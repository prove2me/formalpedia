-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3208
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:10.713448+00:00
-- url     : https://prove2.me/submissions/033ce530-2bcf-4c63-906b-119c42061bdf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 576798561 ≤ n < 576978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 576799811 1250 576798561 576798571
    0x302160e04050604170c120703030c021c050d090537051b01210618060605120903040e010803070b1806160e04060914130804090c0c0c030b150306 64
    0x703408107859039500c40071805e80d140303152030404800740600e030100c1400f800310b41d44e18400a80b40d96950342c440e14000c1c0940d10303a0a540001d54000c40c006001d0007410900c01c042c40005c51800507501c51941250f03070004c00c01c8250240142c0f042d51160303000c203031001c9a54001030003440440d4004408205100e400b507240900009c06913044403032003020016280e09a002c6031901410048001c4c502d111000060000c00c1c400d8158268942c182000450580d0418120743d80000400f40040c5052001c0a09944140310300405d0321075024000030b24130202401a200900840300300603901d03581d9201c0099503038001075030680301d9054000200b00038200d50200304a144111101a015940e5402946480c06c401ea00380001402008003240390030341e88038170541014145843d03000921000081d004245640000d009000103513408000c140443c0340b20042e01c040307481c100e10116151429010880d11020f610b4001042502442c40101c204281140506d105800b00240d00940011942c10540d4403103003a20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 576801061 1250 576799811 576799813
    0x150203040504061e1e05090a1514030a080318010c050c0d02060712020304050f0f030a030501080a032001060906030b04030810050f010507050c031c1205010311010e0414040302160e0405 81
    0x10080280f4044035000e03800417910716801c2001d0a55900105440100c00c660501c14956103c4a039140c004c46810114058042c450840148400c0f120102c1d07910044104080c101140200c002002c00980e001110721140c9590000d002e080f10140000e07082c0d4000b0008542240030784800382c480b0b0f501c0081c205104003003694818043c100d80388981c0b402548050416102d43c051185c5008c108401009102c000d005914011a501e10103000001e045481c10307004940c075030704042007030800300f40d02c404913528400ba40f41054114040d100d4501d40101041d501083c0000d0400c0c400205000c0b0298280b480b0354002d403100c035042e560303100207107005c40b13042c1c01400e82c0000c03408910300d03071948954090070150b48164202e441031050200044d2810030b14401c034026000c0c5000754404040d502c03601040440441c05024429541555034442003803491a102904021454540e915143d445801c02c20301a50603e0040c02c031030425050007500e840c8540c60303030045d40c400c00c0b10004440c44e8108116100700e41082c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 576802311 1250 576801061 576801119
    0x3023003070f0e150d0606170402060a110f03271e06040905040f050c030d0804061107120f18081902040905100605040c03090218060102030415020304050406 69
    0x440603906003400d11032800c100f1011500007005919a011000510002034401c07684540e000001c40090380d0240d000721003004001c03401009035444240c5c8440d085581100c8042c2c0741c860380310080b92461540c1100c55210321030a107510b41c25160200081100b4035a0316500c0710303003503400c10303d1102c4207555000e25504100c41102902d079100c2c1c205415000000002c016034907080d07590240b0b80c00d0300da0a43e001c3c2c3c2d0080e184292141000010002c2108030719054010700010f18428501400c480c0c00144040c12003034660505081c1c3c00300308000c030f588960303010b921911010807610000b403400c1006c08400021800c84500b20b40c3d044003115591080b54501d00007000e15898606620007500c075149000c9800503207450792080010000d009500c0070098075000003582a20740307800c01059804000b03802003418502a501c2c1c0158860307010080d00043d03003081245072602c1e2200100e1540c0300703640c01840c2c00e94411058011455001c0014070444008550038040c003a01c50180e410352405814502c2c00f661726003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 576803561 1250 576802311 576802321
    0x3040f11100c230d0305041e0516081501030b102402010c0809030703110102070f0506041101031401030807020111010f0603050c060a0e011116141c0c12081603023003 73
    0xa400c055030051007600007071238001075451034030984c46a2503c02c968a80240d403510081c005445404002801e000e401405c1414584a18000305401800050a12007094000810380c0101c00040300c01084411041107400c0c83d0079000d040c6d0704c0104c001040055003004020310700d281c400c92100307006500c1d42c0c02071460070a50390b6055070f400042441c502d4942d502400b81c6030101d0b146501c0c4c40e2036140620061301003488e00b4034026480141ca0001a814907181c20525940034410314980740c15668010042503440d00d250005030307044020880d041282d0360034000c0f0212200308075009031003100e10900c01c0710b20340d40403242001b005005004180300003460740003410060398810036404080301e001c1019104501c0440701c1d410703185c030000d8019500450758421030704098108400000c0b54455442044602910242d5030428101340038402c1c00e01c0008160b1011041c00101811607000010014a883e115060b918001c0d40760040d00351071385500b14110040000d0000311880340c2e1080e01901000c28515030ba8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 576804811 1250 576803561 576803567
    0x11031b06091003060b0705070f0803070309063e0d0509060d0b1206010306023115050408011b080c160312021b0c1002010204030803040f11100c230d 65
    0x482c482c01410181c488500180a200c0f200080003d42d0060015001d200d0400c40c0c010b07010304042d44003070140d034030402ca0200031a600c800403205503209840d02a44600070094010070030703d00d8001d441410301c1a501c44880b0040d40101c0d0b05030001d030580030340c0c15001505209a90a016080e49160004070800c6010280c0445512119002000800d2019031540126005181000c241c200300e40159000840c0c2910306c1e8103244003440780f40c001040c0210f510480ba51a00da0010500c07800d0010380c3c41226034821140604181e8020342600c6008025841d41018100360798401c0c45045e0011400b40408290010900c50894100c1d0b001c0d0300340ca926041240c0d80c21601035008070405101c1541c2403000b84400c81c0141d03203881205407404024222100f4000c10070203600074005003030703056a01c1040100300061801003a294429080380d507110201070203052406881d00c1e441c440329403103030311100c1112810342c101d8860120523014014100503002000c02c41c10303035040318403420941030340700d0050b084007684 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 576806061 1250 576804811 576804829
    0x308040c080f0703050d1701051c050610030515010b0a08190903090504060603090f0b06062710020105160305040c0504020427021309020310171f0b010c020d110d11031b0609 76
    0x40d200d12b0350b40036162903848890a0440c19110340b42c0184400314200148801000405101e103200f82d0b50010303a51421004601c0c91007140c102d038040c020200c0015000503c43d54620054804210062200680501d4002d1100342a4003446204918005000c0303282403203442a07900301580400781242688440d1548555008010000750b8080000c10100c01c0d0110507000041842d18085c0900419000c0300d01005014207207203070713240c046a25000c2001041c1d02902c0c080c4000440c64140014541c035036040880c500d282c50340100c0d81084c000100090040103452190310b0000300c2440160341010300c80401d00a910600d818054032441000082c0142d203c0e030b41c0190b42064510044141d443d940704010501149075600380c1d80c41e42c110107400b00b60811100113816110811030010005914040300290003515a10b10190198154114980c00c100d00d6070074050f888400145242c00c0480a031406452140804106600034000d10b61640d800c6002d04035560220301c8000d00c00390074005030b4414403200784 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 576807311 1250 576806061 576806089
    0x7031407050303160f060609050405060601020c062d0a0509090a020f0414041401091b08091209032a0f01021605040f06031a07020105010509040f0308040c080f0703050d170105 77
    0x2407185c0751000580c042c4102002015609408a19884c0030700f403460404800501a90554220300701c04011681c509007125039108010745589041c50201d504560707001e2078002141e95a01000921000f80c03a0050044c00300700c4400c403070040c1349030740c0c18030408141c0c000e1048030488400c0901040c40b000e1554020011049006000040d1100250f0114030500c2000e0340201c80c1666149080d80c0150160100c100784211542007030382c0941072600a160f5240740810070343d94083c20200d00303000195824030054101e56025002402c452600442d080006428125070030301c655001d4800741825400482c904007910035100d1044501441c050911004e001d81300040d840315036407014048006103108002210798420251007603c0c03481d0015002c0d00715031040c3c01032031040c001d1008003c0014190a00c1c6481e0303d9061521011640713442c03802003240750194202240c540a45440302800140019082c411680204103c44850f8032600c0c0c15031703a504007002c5001d0b81010f490300500c114184144107012107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 576808561 1250 576807311 576807323
    0xa080d020f070510050910090b060f0609100f0f031b0804050705120102071502040e0a091a010b072604090e030c0303040f1b050f12070302120703140705030316 70
    0x82c00700d60303c0c182443d407002900b030400d503620401e103c00c0403404c1000a000c4112042d0402900840e0384442c40070030300041039a84680d15080d0481e115841d40403d0712003811001c1d00f50111000c0303640c00900399401c120707600740016030182c0452291a109004241409260700078038403001201c108101c55481c001482038465101d09440010310b034850201403d044c2c3c0024000603241c403a0740c60581e10130b01002d550f55030020700502c820b12021014001540d0825034040c0e0000d190045031520b501d007070301044005003480e02c501c40009048240c4c440103155540c800c0080b800031301000302d0400d4170440d00f140740c200030b01c03428401031101c0038065006030a0310a0030400c403070800205860052466004031003c0721000a240150700812107180c80d03449039510019100300c00c450804000c5070302e0034110101d181c80345004180e009880d200500c03008001e15006030210f50480340c4682d44640d42d100c54032088400380ca01c5218030082c4000410f401090725001405586000e10312042c0c054100c2c8110000d4840e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 576809811 1250 576808561 576808567
    0xc130905100e01080d0311040305072102060f1b1501060f030905010606090501110f3d0c110c0f010c05031606060e0c120402060f071b0806090a080d020f 67
    0x10b12801c22080c5000700b800d0401081c0940581d00000d0030b403107224a44070701d086400e00c0140000386021900320107507114a40d00106011143c44907280400304102c0281d041440007070103c1550400320010800054084104440e00f01c05000e000e1f1b44803101e180e01c214511900c1c0040c03154a1241500510304070f220728010850b0307802d0340c69590071900c10754001008905601020003e07960000a00d104400d5000b01900200c000e0000d02a21800c250707501500741c104084194140b02074010b044009401034101660002e800052070f17100410540080710007103007514a0a0381500c0300025250010311010f8180d01004460000540d1204000e650840c0c1600003400b00b01d036000c0103084490328003805140c0102d8800e203441ca04031001e120103089102661000c1004d00c0456100d050201d4015a0503115166114180c5020082900880200030f0009400c0c034010072090b000078816a082e1000e150548100391129121150368640d050300091907000c080c8603441403640710768090301d4140e1240e004186 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 576811061 1250 576809811 576809819
    0x1050a0e0a1415040807180207060c090315060f090c09031407030201031104080307020d0822030b0603030309060c03091e010e0f0c03030904050615030c0c060c13090510 74
    0x10524402d4108111192102440d100e00e45091050032032507100403e0400e1400741030500340b60b2242414000e154aa0704442d5440d2460582541102d00c1140c000b00c003089541c00708032004001c407055110990f0940d03103662a4945140481c42800200c0d9181006040f8442c039180c1d17198044c01c05602c1c080140400f02d600040030404107040000c3c0400144041d141e10360442c80094116041c0c035040ca0340c040000d000920220300000121151580c040740c220192034418584807a05229800c5e400141c1600791510040a5500303410030310580e0300c01d0141e00c20030340c1e400d03050550300e000403140002c8550190b0042184880c0c100b005581100101c0c0035140300503620b41c070030441082e001e0840c2a0682d91100c2c20611a0424040606030b049044003a001c81d0300001c2c0000d5480c0102075206100d41e5913840414607581d903040c10801010381005041da00d92a002d50b010710302d074201039101c2e0f83e01d0042c880081e4a5001d06c1c0c04580341d0b4011201042d680500f8071b241c4e0001803200400c00901407107441c002007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 576812311 1250 576811061 576811069
    0x60a080d0507050616090e0a110a051309020f04051909060b2203050d0f02100509160602010533120c0307050f091b040306060e040308131101050a0e 65
    0x180241007516665568401440e00c82d02e00360780101241c5442080304a40c0d126954440d002d04116003804084800945803200004020921030845d80002c4d000000d0040b80c01d5005806880442403001f441594150380e000c0f0081039114410400c00030721070400c000c0c0120f2030503640f4280300c104120500c424154403107004508640d1590854600c40502241404104103d10007070b020800d0340c0300034002e1192440d80c030700f95a01d5a000c802c50900c104050804c008a200b080540142c84243c1000d001c0c5040002ea45500d580c00e840b5140b4080e04c1d28000862018014002c00c0d00808d4800181503007074506103607412401d4004800f140d00d00c109018011003076950340c0d8019180391282009012210300310f40405d8548803803540302c076008081c00e5100301d1b00d60b992186400c0d80400740302e107030301c0c024240d094241e85c46209582006101d10701c0d04001140c3e006046c40c84a11691081c0c40d22909034460303000300f9420030360300c800042980101c8140c0c400c555105d000a4001606641440c1c004041c8002c001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 576813561 1250 576812311 576812323
    0x20313080f09040516021005060102010f1109012d2a06151a030606071103030c010501080d0302190e0109050a120b070f0503041106040b180a2408060a08 67
    0x14107004038011032640014540fa10038280c000c14501084030100c102410044c1d16203100c0303103014840710381d0740f000162a03900039000780081c4080d82c90f041003802c0c0c4114620b00d0340d0700040d04050009001004a407000d1034000880150141100c40e60700351101e19030401c031101d540092134100da13418050258406160542000903959205842c00b107a85002c42803001407440d15031f84000308414000000045411089080320b4120780142c60065580c1f10900348803010f11400d100c50b80d0184000260110016410360000e41a68541c03000d941c4032200c0c2030340440c140c0c0200b415094500d0181410528118042c0468501012041c10004101542c460003d10220b28070780c0300141a40301d0704084000c22285908842d4068507034280b2640400441c0710080840c08010001411841e0b0034406003096500c40091303400801c1f44442207641e50980c0760704030034084501c4c04a94000c1c0c840301e030042105000c0d0300c3c4005102991200100c045102e6040490b1502800307051150090704140b00480c8004052080c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 576814811 1250 576813561 576813577
    0x110405010e0c070f2f0102011112130c080d0e01020d050318011407050a14040b03010e0702030702031911121213030f06060515030108100f020c0706020706090e1902031308 75
    0x5c80c420581d804002d00180441203043c26046904d0075080071031074400601501c0e1000881100c0f00540c0e41d5035400c24103c0e9003410b0001e4544400040d00041a1071b0018001044980d0f5984140984080000581e40c1b1403140541202040090000452983c00410680c225040c1c020010503110002907141010100680f070300310004400140740300031035070001c8840d0128070840200910301b510382120341010340418002c11080d06001c0b00811002c2d8801c0007994080c50b0001c054a40903116030601080107028170300c0481c0d044d0344d8101c01d00072a24041c200d42000d060318001601d07910b210846400b41707940c402d90304013004109009020000c10f039203048000686200e43e030300042082c10715040240140c440c91a181d4070210400041c4482c1e20b002c0b400d20000e030820140800c134840c50b0090308001c1d0103202079035220b5102d200c03c00140983d000918004403000782e20307030a02c3e5903103c091104d0828412507041c01c079004a9141d90403181d480e50300550f4000d00034a600640c0317090307641c4d420085602c2100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 576816061 1250 576814811 576814853
    0xc0602030406020d1e030209060d0f06140d03120b0d0804080109110a060909020d110304060c0f020a05190201020a02060f03060a231009090c02010603110405010e0c070f 74
    0x3001d1001580422824403004e2050901944051120600071034a2003030542e800d08050700480e050000741c58201c140c40c0070200340c00050000448140b10a402001c05114109650040e8050300c101800c0c400e0745040e080b50117035600350011070011a44000391000640e900c1d0000c0050200601041082d00a003014125000010410940c2810a01c3c081840c03111002c1c400d07810300d0010032005030060131400403500c042c0000744e00e80c005c40c1420002400e845ca0301c081c106c4c200004200c20801d81d40d1005641c1103868407080c90781006210100d90701c1c3e00c8800002e2055201c003040780a490410303c0400c4070207105204540d1111029404100650030a04c60840601d50100600005207000010764003d49807440c074481d103002010300d2080440400c0d0240c1c5004000c000d200806080c402c030306100143c8030201050140c200a044024024240fa105c06d0702c1c1100d060442021a1420b405014120340002001c007001d6228086a038541d030b8031082d000c9600355040c102c5c800000d01d0070300d0000f01060080c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 576817311 1250 576816061 576816067
    0x31204030609060518060a0c091203050a11010519020702040f0c020703060c050a0903032706111203010308071e0204090b090c032d0708010515011202120114030a0c060203 75
    0x72030f0000a50794007401700040304012a04064240c2c20000340b0a600018002010071100d600c000196500100341d0001440303c00e903058143c082c550424011f05a14249994410300c03187d01501e05401c0b5071040d104003009070700b210301d0b20f0040b80494004d0460240010320001c0c0c00d05084c4c181000b1143c0000c904409600f03d1130040050081510420130301d0340550500920345000c44000901203070003400010300388606e050450340070089582101240007400d508440342d260b04da460103003d030003101c04000103920441045084030034003078080d02e041ba41c0c424282824150165150400080700004004050060603045800340e41d5501501c000cac43e02481e100c1c0103038140b43d40c541e42818004d20195010398005081504408001010706050043e1920751030046001c95540ca428030310a507001311415801e02e410b00c43c803455025803101401c50240c803010000a0702060010507401200000f09100201900401051511a0411800c000001c0a8401506095031004400901a00b00340c005038008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 576818561 1250 576817311 576817313
    0x1803030c050d020c1503130f031d0d050a0b04050a0606030c03060b01020c0f041802030f0601080c0d050a060c0908150402010201050c2b0207080408030c0d0e0915031204030609 77
    0x140040b901d40c41140c405007460b41c803400b001c983e80f01e03900079903c1480d020000004800c0b0751458440c3e60700691052407846c41003602d04000742200002e08284115040140c120449407411000007026107a00101800350402261a540203001d4000c02c20340301d41c00b80411610018045228071030146128258400c9042e095041000403590340b0682c5034195400415030507100d503655080d603411008102c4022036440c0c81c00440c200d010a095000179014810180080c1d11854042600c6060318021400c440280c00d03400304005000e00c0681e0040c20325003000c5c0517100070171050741106d07840c0841400c2c000411035851294900d004000d00310380e00315210440c103000031503034207005264200020b40d01550401848002188282c016112501888100d548141c800184590191a80c040c0c00a00741c075100c0d640c1d0801d0a4995000090304580c500a102c8020015402079180c04400007001d0a401d2140da00c03012498101046076801907458412503400c0c042c2c0000d010000c00186100d07071404200340c412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 576819811 1250 576818561 576818563
    0x4091e0507060f030501140f220b09060319080c01090f030e031005090c011d060424030507050a110c1005040f0b0304030807080a140c19031505040b011803030c05 71
    0x40c020340c41018281790041051400009282840180440d911803004441100185003044030102061800000c1151036a00141662021100301029500941d4039550b0904140d12403070810348038868041d10703036154004600204081d01d01d080c0c080000181080c49901d03800d60292800c2e60440004500010b5801e040c00c080c0036880c51411042c40c01e02642c00c0102405807a0f1311210102070400c42c10020804400b09140004e440020000c0c3c405550f8030741351900c426490101050405044980c94800ca50281c824810944030340c410785e455604007240d07504203c843c0d8403c20801d01c1c1c0303803059006810040e5a60181010041015115160b846150000f8007000304219448403890b00000e008101c0030a0b0046026688107082c1c0c900031105035034404046000b07250700003861541e1002c85003001103407074208000b0302d001d81420345981058425190200c0940340e01030b0300038548100340c842c05c00c454101034024001011050502c0c007212440900c1c0d00c40c0d040303455441500010040c40410040c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 576821061 1250 576819811 576819827
    0x90b03010507050f0a050906031f0e0c090409080702090a05070906030b0a03030806060f0412030e10140309030d1e060b040b070b10080a03031a1e04091e050706 70
    0x41900244610b1a081601030300c98003e0b42e1040ca40c40d01d0001d101e100061040084418105005140507103c1c00e00000c241d5000555151500b04032081c281d0100d10f04a041c0c001c41c3c032900042a00c01e00c1e004000c0d00307110141c840d05004a03903107d028806240160350b100f1006110f561241000103035450141001081c40c0c200b0b500540501d0b10700000d2181a4a9411300d40050300d416080c0391300c50b9200c000c04551988140082c05010010116010501c82c1c038520b2624403982c000c1d03507507618520b810300c1040340c00000011858081058800045a01004032001c0c503402501b0074142d074144100c4401584c02d417815803840040100c100f240f140f495a090f445020b0240125020003070a00b802d01c118007076140304042e0701a04140c0b0714030001c0c0d0407003091a0510301400c02c11050320142122860098040c2a802031000c0f00e01c01c1d140707440002410074462030312403045101c000300c0010f0103400901c030080071034441c2581c00c03121055080324194610100007041034407420003412070700c0c900311001b09221 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 576822311 1250 576821061 576821081
    0x10c1d0d02090406050c0f0c0a02010e090105030309010809011b02060f0a0501031e0204230403110c0a03061107050f15010602151f1511070801091e11061309 69
    0x1810303024400c09a2910304020754416401000001c0b140ca84a19506403070141d02e0701d0107074114000400011201020982840c0107100380ca850300c22035100410401140d00034007074585c041e40180306050b100d41c468034070305801601010000407208130042e049030080801001403000b43e803120080c401d92400b02d0859980c0603400301020003155055a50312403402d680c5410350051440c0c050b81550a5556070750180700c00c001d0b26181c800198180c84000381d10040115400ea010810b680712140e2401000324110030041001465145118215501e00c0010120391040b54800c80c828882d910000d00100655411043c3c04c0d802805124a5030000d200c400702e05820040441d00007104041401d01c030340c06036036084aa404c0030345800c1e0010f8064030300401e00d2503114011040d281001c500f0919004101d0700032001031142517688164483e8003041c01c1e1404140c0c014500701e2502c0c03000c4050300180c0503110500c5d00c12001a1105041c0e0300c00160582c200302101100190004401c00813a4010300c60b4000b41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 576823561 1250 576822311 576822319
    0x2a0b061509010c030923041811010c060209060a0c0210110607050c0a1a070e0307030b06090405100f020d05010e060f04050702010b0d0501060504050c07171308010c1d 73
    0x108054080ca422103006954825041c007000d1029481094010982e203c041d01135120940032014400d0038500b8078102c04c1c0c9599014505d44075480c0d0780b00e4502c421149400703801c003041d034078082d442e6001110310b916804820365000343d0a00ca000f50729a2504002c003007008496440e002a2030307803401040b0603021025041030602008000b80300c0c0141000c01d2055101d8450305025480b1142280401d00b421b81100b40145441c41403104900030440d0004103034024032a80d550710703500e50f4030380044c99507640540c0009840d89031003400140180c60001c4249034801c0c40f076802c0c1c50f01004000c1c485810303100990340380079000b500407a00d080040003e01c5202e0040c03401c1e00351442c1504200001c1070a0a00b0000c0c1280940d131a6400180f5080c000d400c1594042c602401104605009040807802403640340180c0340b140b424500420132444092040d00c4207981c004801c82010240c006c3d410405030702c030383c4216654100300c15001031107c0c3c00b88103158000045803590401c2d182020a18003c0341d48902005c1d02c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 576824811 1250 576823561 576823579
    0x5030106120b28020c0f070602070e0c0f090303030405070303080c18041a030a0b041b181a09131b140405060f030303070c03030e0a030c11012a0b06 65
    0x1090b00d02d51915080032520404207440303501450076800440d901800100050300010350200002000150107a04280d00d5094540381c903201c2004a0f1107000900c1208045660f01002c51816411300c0010100d1482c25a8614504400580880e085410485080d102600005070810a050704002c4136540030155420a62515a123800d00954240c0d02208890140380d4980800c0d5440e41d00c2000102031000080485014803440c0c138021781c0c101802c440031254000440c03c04100301d5485204041920010400c2d401710740341c202484402007180001b03005016841c0c151401d05501d03003007480c034060750344034491043d442c00c203040040c40ca07601020010784c0548019820841e42c50113090041c0034070b40803100407504d40c0301c00c00015081c1c0c1050000c1a81804000140a207041e0050a0340107211311a03101400056072000350346440d5801c0000c00b501280404030f80c080058042144a0610301d014100840c1c5140d403500002e601c40c0440c80d0120a54907010603c0041c0070709000750315881141141c641c06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 576826061 1250 576824811 576824813
    0x90f11030408090a0e1501031a0f090c1908010602250909210807091508061011070b040915030804032301020d0f11090a140a09150503010612 62
    0x41a220040000d8800c0b8004205030076181e9400a440c1e00410380045244658180038076080081a910b81c1801e011901d00035261400c5500402e0b009080c08004040ca020380c1d4500341806003184009240e4642c1d0742c010840081c02d01c071205100320781d80d62195280c0f0010360400c500a0b1400303d0818089603007510301c202000401035050b80042c152500700c4000329402d09107140400c1031982070a0f014583c162288d02240000e0342c030100c52407156805942d034200c1655034502c450700c41c0c540720024000241e800c00001e006400c040001d0707020f0024600d081c0784c10900d400d12040c01d05d43c10340c00c00f4403100e400141c204011441c07070041d2111001c00d071054100292940d500c545c828400c51000602e58801c000f00454642e80440010309000040c9000395641c01c00708889100401000344420746c800e140c40025008540c02d1f0003960213010000e84060b01b880e040400300002140d5842000750300c501c002c400480e49000501804001c20503040c40c11100c2410700081600703540346038000301080081e01c0c02601c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 576827311 1250 576826061 576826091
    0x3070c140a0c21050304120c0e0903120c040302040c08011511060615070f08040503010f0c0c02042a03052509060302070203102f0c031b160f090f 64
    0x603080b202c03c000980c10b210f00d07907038800520060500d005005404086000200c50384d0400d00305801a2041e00380c104c0c0f8588510408a10380f000355140402d40c0c0c024480f424172851850501500b1002c80c500c0e0078101580c1c1c4d030000e801d546821450000280c8183c004124440b090f800c08500c4907950b09140044402d18952241d40d40001030000d0320035003424242040324007a0380126080031342c02046030185401c1c60304050f50a903209120b00d070701075031030241d00c07600e00c00142c4910030070341000366601e1000103030316000c00016040a4070500a00c001c04610084000c0580740507007515a05528003103154a032601484840740004281c40e51000c0011480b008003590200da0b080c29a08030f424010b03101d02c024000709280c00743c081c45040500c0d14061018992108180d00b00040000c220310b02c80101b00e22411041560142809a0402d03510501085000300700800b10008046490012280036042c18151300c83c401c19294012502a03d840714140120b51081c010302022040403681400700001d400030403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 576828561 1250 576827311 576827333
    0x1508010f0e061e0c0c060f0702160e0604091401061e0503070b030c03091c03060314010902090109110d1a0a0e0105061804200d06140d141203070c140a 66
    0x101440b01c03080000a120001c01e80e00717950b5042c0d1110102e55007032401e480740d01c81012003640c021000d03200343e1880402040342070a02809a90780d034055600c460300c07607030240000340c41d1b812004c40d80f042080034007440703d0300d091290a0080c0f00c50841000d5611403400c089002d0039085d00024066000404103020b45e0600f03808a98200c85195581e070f07583d030b5512640f103040580014038854000300820b10a40c0380d650541000301603c2c010300b002c80ba10000c036a032190072100315075802900700e07042800411101d000c42e80b009100e0a12654298600070303242e00c06208941c4080303030b449412000d95202005038100002ca84018002a00d90450254101130001d5010f000780c52902011050350480540340f0307152034000105540e15820000005941c0c04a44401500038000c824403103454000001100310405006440905026101121001d035980f180302c07400203132807581d520724807400b94000f60091210005610415140d034408054252034501100a44203100700d980349680010302c414041004084e203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 576829811 1250 576828561 576828601
    0x1809011a04060f03021507050d091701050f010308090102010917031617061926010b030d20070f031118062d03031305040b0303190e041508010f0e06 65
    0x80840d0001525082803607c60f40d0b000410038020708101c0c1070f80c680c2101444c41030b500d580003507900c19074a041000f422100121107076031030f0b400701500402c04030340c01c0da00400070882c061002040c540c1603500d4440701c01403044030034452030000108011702c610050f40021030441c0b00d0300d011b041440454403d0016410003514482c820310305400240c1000382291201c074000c01019440900d010180c03d010b4400141034541c9107250b50034130460441c1450003141c40e05070340715070351958a540b603140384c0e4003080d5449042140c00350b441000808141904d6070400800114030620602e4403d0110313100b80001c10a00c81444064840208144801d5640f6000f40d105551007014941000c140f444410281c80c44039100a00d4043c0000070305280d50028010002d415501c00b5141407000705070810926a0380c0c4075580c07160103054203c41030101e02c00d11072034030300c00412401400030800c01800e820014031a8807a0f40103500580d0358142c020700301c2c280341c018040014440c40c09001140303001c03802c007070260008280c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 576831061 1250 576829811 576829819
    0x90303121a0418060506030115170c0301150f0503011806020c0a1b05030105160507080c120d1407110714011e031e0e030901030207021809011a04060f0302 68
    0x10004492000c070440c46202501c00900500c040c101410030a941014000b205403006800c000025002d410140200441c1c155400b00841c01e052030003280100441098021491a01a0103440ca907190b609004407401610a40c1000b25200d00e800d0358107641200a1f13200341d00990514020b800c01c58428410303080c041d500010096521046501c4144c1407030318422009091540c10314a4602d50300c0001901015940309800800480d20307249481522894207004250005008002d041d00080c0b804010302800340c0d03102c0481d038500c030b400c02820111350400310001d40714558490814400059820010703030040004e0401d001c0c4000414101c50325105540100b03204103081613040121640b10340c0303042c44900d50b80e81194082890148006000c1d103007120301c141c1d81103074240800324078004604c44d8484000210000718a070250040049d8041e4224035400d80e8000103407040048035040810380d0034424131641000140718070f0707000e1200b00e0300d49d10501da00d0b0049203011030a0000700d9010844209481d0111 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 576832311 1250 576831061 576831071
    0xa081b191101050106031e050c03040f020d120507110f032a060d0905060906090318060c061009050a0b090105091b0a0302030f070e100c060e121909030312 68
    0x5540d800708051400310550b01c0d00c0000034086502d41c1c40f41000f41110007400047c0c540d041d81140548605540c090444082000810001042c080e0030b88030a601c080e00600c40046541c45000428000c100c1348404503800045003010840d05c1102840031a03001c60317000c1014180080030076510b070708a1146016030400c00d0f00c03103150207440c41450408640000c00c0c04d9610001c03800c1482c06040003d034225014801c10b408504039040201702240300c0e2a0800c020b40c20020704010821505c0841351801d5003041007048403812820040c0701c25440ba005007549000340e04e243c401542d04071440202038071407140c504012004c15640d200300c400e0442c1d41c2140c81c00302c1519480305c12207100c4000714190f00302400001d00e07036000e1a01500698469000c2c251100c16590319010305440c07010280c001d25a0021050307089402d0036006490031401c103401903000203180b0031100800b91918100702c082c0c21980e039010071500301d03502c4400d050f28a01005881d042e250146190782c06401c00080308450340c0c04a03124 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 576833561 1250 576832311 576832357
    0xe0609070207122105091507020f1807090803031605030912071203110405060306040f1b0207080717060105100c0c0b1210061e03090204110a081b 64
    0x200640341c041d0440340034070f80b0610440d2415030240e525515000c0f04810001492144081c000c200b40c80d00f030700e4060f1001d07107102035160440390a0303441034100301c4c2c1c4100601402c2d60240c664441c0c02c1940179082140030110306000c8400b601c1d0b000c00307611500300d6a00420070030100110982800c102003240d414890707100d0303d61039003550600240421300700300281e0106000047c0607541b90103c7c401c4405480130031401104154280705403080c0c0c080c164016404001003816401e0641c81006081e0400c0c40014440406050b0ba24030030f0103103485980164080f03401408450700600039180100380344030307191086803008001d403a1600c10501c00c044c0304d20068454803040701e000340218280c65070b1100c500c41c0f000303486100c1c00a4a81043c10380d5007201c40d01da40041d141c14088101d450588501d911003020362009189461200e400da00c0c800310030580c690200c0340c0162202c2c06880c0d07176000c1411804c0c0c1c0b983d20761000200100b0004188500303002d40b01c203620308130068082c211007117058280c1c4000b20740004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 576834811 1250 576833561 576833563
    0x120c01111212100807081509030706140a0b0301090f03080705161505130b040b130203100b1f0c260c0c19060504260601140a060305010e06090702 64
    0x111124038104580050100e48660391194960700c160303d00800c1082070f68880c03000e6507617040709004101a80d0f00c030100c0d201078080c02c0c104c0207501c0741030b0501702c0f40f52000030340ea88001d5070080c02003100307456140800d00038442d0b0705001d584180c080650082091103080d44504900706e40204011b82400803c0780030034050b83c480c20032602c00c090b417044140303a0400c15291186640300c2c40050303000c1c901e02c1c250100c0e00303030f0300e9403040680e2464000e1b2548849885c0c54503005000c2c84090070142d00301c40194004c1005840a020200e012890710500140316040c16043c403625005003110701ca1405030800102c000140c0000f400001e40b13421420202d240c4102683c0e146000f0303042c1e5135410010502241e81c0d903000c0000204101c2d21036050700c80070443c0b030342c1d080c000300c010301c45025440200d0030500c418410003007040313440900d01d03007600000300300100c0101203181408401c0c3c014001d84144000b0000b41070901c18041c100810207464100040e43c50f24080d01010080680b10910902c409808965142c0c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 576836061 1250 576834811 576834823
    0x80a0c020307050a050706080f07020d1206170109050d0314010909030e0607390501050d150807060e03070f0308090a051e0108151f0201060e01030b09010b120c0111 72
    0x10b4480f0440d2085406030915559500403441004000340034a0006510b19400041c01401942250010102c1c0c81c00e4000c1960300d2100e1030925441036940d0100041c1c51480307100785120701444200005003103000e6042c120f040c0340c0d440030928281420801c60700c0c2c91784c51fa00500c80c1102d200c880c0000327403600103180c21100b10405905181e40000041084020b102d15080b9a6800450803e10200d0540049002c0e070b14030703403004407080303480c0c038906501f04042d5024100504c520110100005030307031703540e214a18160007102d81106c108c547c811942401865080760700c41080071406c0f00281805803514000d08852901804000d190100104c1c18203900e441c0c0307000090203040014040c2a02e170b458403081d580a03042000c1c02c580000e6604000c075180310441084a21404005008950794101200d0400c01c400ca002d411881150350320b08000410304004c00da1280a50311611340342549080100c070b941e09445c041c1c200d0710700c6019400d041c0b003c1104000f0303c0d00203814080c246201c4e4030b81109410782c1020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 576837311 1250 576836061 576836063
    0xb0a0f0e0a062d0b07120f08190b010c02040f0e120c2a10030e0d080405071509030803010b0a09060512040605060a0503030304120f0c080f3601140a080a0c020307 71
    0x104c045152001c014000c0d03480b104004065990b01c9402c00040340c11500f90360261480b014480000a1900f00d945581c2c001c1c0500c41e00606000042009607070105088451000241c14007550700c3c1103800c1224810301805c55403841d45245c075420442c0180145884407140191135108664020015a0504601c000b402e81c00c10010192440e0189951f4050060148000300302c17058022200d001c4809806100d0384e03400340d45c10100074000c0317034201390a00710410440304040c4180480400c001000600c03444c001d40c060700700c1c10300301904ea007901c00303015094855030b030041410304c03600b070088400f00464201584c1d40a07800502c0070a85407100004642c2a102c150030580c0c06000000802050000e100301074000032445a6a404901e400c0702403c50344010380da0700040104204121103400085031202801c03c001d151440070182808009a22500000e121070170b5208821070070000c8559a003020b075007100400e80e0f548051800004480090096a008041e030714000d903519210402940f0130000e0342e00c0300e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 576838561 1250 576837311 576837329
    0x4140a031a012607051e060d060e0601052104030311070503180f061b07090e0a020102060a0203070903081c0c090e0a11030604020306040b0a0f0e0a062d 67
    0x4a95141e00a14400d0001d0040340080b401c0c0c04000c100b0720180c04548820030000030701619401d4241003c20850003003c07405d00c100d040c00712140e2051640c8080091030f0130719520200141c000d18100050351090002840c107414404240000d28030840404000603001508041c642260382c1c4514043d401004058501440502e003c182d4000300704002000703280c0b0104103a0700d4503502e1148001c20881006045001e80c10000511910000030105502c80341e000030402c013a02c0126880d12050000c50f003c001454005502000d040019940c042c0700c030b950001cac00d60304207614625041c00064403a600714480107222840000c2c00d8071030364000c0c04007094160071030003042c0300d0184000d00040000304a0301030313418100c6810b4003141d030180780362082d221607050125000b4250f03500c18080000a410091045400c2510b440c0001e50350359500305400050801d0407111700c40c050a010340c907449914000c1400d490305161880a00140e0000e044c5140c0041801180e03402281c01004140c1495a2513842f44001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 576839811 1250 576838561 576838583
    0x90201081f0801061e0b09010c02090c07020301050a0914060412050f070c0609170303040c030b0613051602010c0c050604020427030905040e160b1809150a15020304140a03 75
    0x1c01144507417040720309142d404e50501e80c00e403a614100c581c0d2144c409094003059544504000504140300850b900254040c0031908004d1203801190944004075800320119540c0c2c0f40d040f040148030700c0414140c004400c0144507500d05a84c0d0a4920740d42040c8400c10321002241c4141d0401e0f4074021241c5859120940480085c1d40d400050200500c6015401c0040c0007501c072581010400801c0c1d0303119a406c1540e40380c03010700d192140641c6460142041c6e030406400002541d516016024003270043e005e181c286d0014240c0d902c40203085585105440e800c20800502040100d0300001d122078100d60120383c0001d26003000d0310807038954a480c0d011800400c050301c44c030200b0f044c0c00c201c0000807548142ca0510a10a1880c4e180351602d60502824420148070041803001d000203401418081c03000b40709010302000c10b040020031001040f074504020a16408100c00c03141408410900140801541c4101a00d4128406511307802107029000702d0b96851990110160380e45058400110340211843c06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 576841061 1250 576839811 576839819
    0x13030602032e0303020606030f061504020f0c0a0c0512070506130509090303090714013207060e07060302042d030b0a0f06050306010b040b16060213030510090201081f080106 76
    0x260301c2e10910042c1c01502888002030100d04021440c0c0c4000d048031303000707420755a07901110880051803803100d0b03c0e04241d081c800c590301101e040d4010310007119054002d2507100d00da441c0150b54004560000f81c0030310592002c4d500280400502c00050300c07012100c49445000c2002c1c0c2c5040c0d000d1903032001c3d034000c400c4414840300ca580440158000d03050032090741c80712034842c4800d500b440000460b103400240c2400b0040c1c1c80b140404546803020101302d51100501d50a2001009683c000074020349625a0701d8043c052284000c01c1005d0040c041c0e0f04042d41090b140410368410040c66508182c0e54140c02905802c051000154140c040c5a1001c0e15030160f040160001c402411a001c45640d514035204001c20036290000e650340c1202c8881c6a40f6103050b040842121716600100301c012121a4120140000140c2900280c0003200e03c4005280071107155040076032070203032200203141c03c6510b0510000c0250342e010780081d030300c000c0010411a1464401e608003103640010340c4410810352909038041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 576842311 1250 576841061 576841141
    0x9020a0e0403020f0d082205030406050c010b030106120b0a0b03011404110a050f01031e060b0703090b0307090504020c0309030f0d0906170106030c02031c020a080c1303060203 77
    0xd80901e01036800c942d200c9010f21051551040a46109404a1403400001e20070184100080c0914038040006032a8406281d8455141d504140c1015010500111b210321045101b440b440d01c10318003c6009100e1907140203490080f00c2001d80000c0e240480400c0062076401180c0c20a40e045070000d0300070064600c404116098504069404070f0702d5100500c0c4400e258035103140c1036415140c005004250090055006500402c400c1401042c1c440001d4962060713a0703800d102e00e070014a6503011043d0780c2c1004d0318004243c017105402208440b2800d20600c0510303548145440300b0350344182c0e00181e65810000185145004602030300383c0c10720400000290081d4049002c805100094507003490603a215103040c3c460100762003500d00c1c40c21400b00104246407198009441401c514010350b407801c2c15000421200b0380d854007001c0340294000603144d40c56648484841e600542d808041410059070419500c2030340c519210203461144c021020801f00c24440c07144070160401c2c841c40c800c04496440c0c0340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 576843561 1250 576842311 576842339
    0x11a09190c11060405061005040902010801090509210a2c061605101509181514010623030106171009020c0c03010c050702060a03051314100f06050a1809020a 69
    0xa0b181e000040d070340000c3e227081a0007a250f01c280c1c16154044182e0900740d8020040c8401450ba00d030380c1c82001640506942e03c0050440401c41516102d0350380c0c41c50807806844c0b001c181518030800a82210802c0e091519404012110310040341c81656034202a01c0d00380c13a03500011400392440c0500c6400c00c48261041e03002c110a9103420b1107032011180c0e40c0b9001c10840d008003901100380c800c904075800010b2075000584100c86240b0341c000803c01c14110950a206109800c41e1010407501050720501421141400c0d520070100122907145606041c0010040003030980205c00040c081c1e0040f8105151111303008000c1c0030321517000c41d125005c0e816041d0742d0b00300345408180a0f51805c60080c0e00d140c0b151007100e05c425000b9008626211440c0000c8008040040101038022944003c0000080311040384044c00c9001000a0000510703480d800c6045075810742200318828988001000241c0f0380c1142c1c1c0302110303801d00c0038100e8880684031920140c041c00341c00a601201c05280440e18004c00151 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 576844811 1250 576843561 576843571
    0x81201090911060a0e04021c0207080c06010915050603191107030809120f0f120403080a0c08010e1902041d011d060609120f0609011a09190c1106040506 67
    0x900c2d103840e402c0c000c071845440591000548405505601d50820350010450401528a078007038454440b1000000c981000c01c080f6400d070303000038840000210400c080c0f8013622080d04100301d010709415011045070032502c2124010000800003070000d4030103d00c0c2018442140100f4008000545031921203940210401c40c040f4601c00003181600b040064441e2400c98402c68561070082e54202e2070f103154120500a03c04d40c0720405c0300c4031210500da83c0c032a01940c802d440b5030441e81030200e0400141d641100d030071b00c10441440e004114087d8000c10725508894025040030082d901c035a12a800380c03240350410601003c0c280d054511b90092101d045040311210030b50850090064504281040b406541841d071000d000d2014401c1c51400341e00c041c079402401c50466061103544180e1506103c01201d0b01d203c540d660b41e40980740c1121070005603150010031104a20340c0c1c580035182c420050340000c10512400d40c1c4032a40c034611030107809081400000142140e0003403509240607550340c10101d030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 576846061 1250 576844811 576844823
    0x80c01051f080303010b030703020705120a09050a150c03030b030a1a0403110601080c1e130501050306070525020f06190320120c04051503011a0403050a0f0812010909 73
    0x500800d003c07041d03905840c9896011442c2d0346449008a010b500000710a4900d0b009500c0100c550300c036608020110207605450351051180f9003420031500c412070340c1c404031511040c1c0364040c190035407010740810503030350609002503071620a8001c05d2130580624001412030001480ca0542d6030740a91006115510981d209580340d025190950340b02c03c020700c250078103580036840302d0742daa18140140050031111056405014194600040d00d0354540c4011600450f5903400103100c0741c00e06020050784041c150a26a1800402c4030741301e1600f6103614003a84800b03140d8082c0608540c2e800003c034400d60300081001d5102c03800303042c0604424200894001c0481e1a20007104c0148a410640c5612070050316042400c04071000309a10107594001c007040c0d000300e0204004140c40d500c2c640030881e1101103407440380d100e604260406403100302d03104c1e230026105402e01c0204002400040c14024a42c1c0c89420440d642403140380014280c043e070800004104a004004260145154808040a4001c503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 576847311 1250 576846061 576846121
    0xd0806030601210b04030315060309020a151211040504020a1d030a0f110d020a12020a1e0324020a2f03090f060706090b18070b0a0c080c0105 62
    0x5410b08004001c0e0620300d00c00542509a04010940030344605900500034240488d00918070010050518941e4028402103550750341c4540960424414900240030031200184400140000141400300c001a01084050300c403640481d14468800c1503400404000c0e105540340c8902d05401b60842249460715007031480450384070f130076034540041c03003144090f005152103020088075118072991100b0400040c3c0c000d40044000c90058982240c403d004001006201002294034810004007103e998000c07401018694001c0c49124181d484000840350b20030051000c131081e40d00515881c8100341b0110342403074808981c07984d03c0f5801500c0d50040d103803098603a040341000b19492817aa000e180042a81c50390003030000d2150346c01c2c00c00040c0e0b03c0403001060b481c00d2446c00d5450500341c03110054112600b055820502501d02d40c1c0e806402c03012000c0340e01500c81c0740d0403e07141010038040d4184040070040c4944407182400f18200480b84001d44040082c030051401da0182508680c00c0c0011146018070b40c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 576848561 1250 576847311 576847319
    0x1806041a042c0601050a170a0204170a02060a0804150e0604020a0803070c050f010c08070c0e0618040f0204021210030b150f21150604060b040b12090c030d0806030601 73
    0x2e41854090400304070300c0d1019a03e4801c01118160044c0c010401800f0000c1081c08a40d09403860583c0702d900104005a901c600300402250385000c902c03c040c0740c41d40100708400045c0e0700d0800780d03401c0b01600c1c5802052a540c40c01c1418a6040c1210a00b41c028501054440418800308101e03104900a54903050101c5c0c0c0c8401c1507035648200007006c0c1c1040d0b52010240070500c2c110603842010319051518001d084016168480c0076481080300303c402d4082104100240c1d41d40004883d80072204503061190109070700107601c0c000b040104020202081200007008543d5298141d038440c4604094035604c0e0302c2c2480c0d440c10000c01d1404203032508001310300050301c800303071090910b10030f9034010f803003000c1c0701401006000000601c408145d101d00d529070507107000c2003001c01c100c3c0b03441800001c00411701e00f4031400384403c40c2e0f00341d003156001c8827040000b800f1780748660040720900c90502107010f00580d05c4c2c0004908008200520503454056079102500180d0b0095896000f50012400d8a4030f0b40d9031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 576849811 1250 576848561 576848609
    0x7050f06130b061003112101050109052101090c06020c0108061f030b13090b01030b1b0a0e0316080c04110a1b030e04050412080a0c051806041a04 64
    0x34000d03008014800b004001512401c03c90b403c07040e207025604001c40c0c00d140ca0b01c000b006d1a00001c004503044080c5a101846108090901d9401403100f8203000061a00342000302d101e01c01c100c840c040e422119001c1c82d4824410940c804050700e07410440485002d40c450381c0081d21004040c510740e0000e0034800c085141441c040106205a43d51403d208464400144094000c4c00c410340c0c6156004181d00541c0300584440c2c000c2480306032182c803d0410769070541c50954810340010303148001c886001140c5400c3c11a005048841c020428284100c1d5051001c00091402039002c0b96441c0d0100030351000107500400042c50561b03007404982c103120304d0ba100b009105035030085034588000200310000031400091540c02d02118640a403524101c1042d5040105098a00a550440351230a9a058844000354425102900060503075428080180040310040c401e00940c0d01c0c0c0354490003041a014019500d1000300c600500c42c0c800310140c80c1e5000b041d0701100e60030600c20141180f40c0304103406402c0e04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 576851061 1250 576849811 576849841
    0x1091e0b1f14030903030601110f190f140102030610030213090c0507080406080a0c0305060d021908060901020307090807060212090402070b09250803220b07050f06 72
    0x805480d06403007103140c91a260001190700d0400d81840114090302e941ea01510006622030501c0500542d40d074204100014800354007e056030200e600804400c100002010440a40040d0030352140d880400c494140981d180c104407800800d0a041e903542c40c2134144064000d5441341c881141d01c201140b01264065090b4480e0884016503002c8144060141340e500c0d030700c0520f0b001c10340d10300103041036020364801c0c10303a41c010b4002e140030800f07034006c00a11544034020701c0b041000d10319040c4410300341031011415a00610701c3c000c2c400c00030040c0102e04600c0d540e904d03600034060b0000310f401d0b40c02d000a0b107500030350050300c00c000050001c00e00444c481000049980c200d81c0107500411604d43c1d2000700030303001d40181c0c1c4101c0d4000d03000c218003070205942c401413500421442d8082d0140d01011150180c2d07039a2032070703280010207155000401080d8030220942c1c10b1094803c858660310701d451200c03461a03031890b82280118050102e0107a042c011f0004000c00410a5031003107815503242e8103600f0300081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 576852311 1250 576851061 576851081
    0x1050f0a0e10050d050309090606040b0307030b0f130506130509060117030f180a08070b0d0e0f150106090e06092d0c0c100902180702070b0301091e 65
    0x8140100200084028000066030010110200c040d0182e1200c00248140104404c1070712241c5c008142c407011460048412070304400102ca0702d9180501d018409195800005c06070010f15507641a5501315480e4065910301c04a0014054105080014002801014261040e40c000d4010054043c9410a10300c9018054032152340100030030785ca016208080e01d4240c1c255180791340024081c800404041d60090301815450b001d5100c0e159001c44180b2030300c2d40d21a80310400c2588002000c00400341840119146813074041c4010480d40307040000140f500901001c405000c0c030500d12000e002800381d8145034140e0f031181da43d5035005966103186080211050b605d07250720004083c045001022000d8010002d640c0a0200c018201c1902440615a05048a80c1104910002241000c054007880403c09805912008212280041c1c000c00d2002040024200c4803440980218116034001c1104030010110282c841d5582e40c1c58103403540c00340c841001c85d6840c031081d014100d01804060701607100a6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 576853561 1250 576852311 576852319
    0x30303040503120709031a3916080703030c170f0114031c02010b0a1d071110020315010314090c1e06030103050a020909061306020304060f0905010c0801050f 69
    0x8454162075000c0050f101510035800d01c4080c01e0000001050481c140304684102241c0c080700f8500320240b0610a041100d0300c050f04000440144000645082e82810043d016005107881724100c005500d9000100c11020b40102d502003504010540e05030440407000c038481d92183c032400d00d15480107845103c2a580014426080d10040c4002c07092607003011490207004040321800c0501d01410020100c80140400c0140d4440c64640e011381400c00c00080144000c40203541d02c000d44184520f07e43e0b6020b4100403c20480c0141c010504e01c08006454140020100031903036400c003886401d014500300c0e09094003007400c0440420340c035030f08945500e2040080e40c004e8041c2d410f2007001c03c59056203199025580c0402c2c01001c030740b982c80700c2000e14003a51180e4020102d10745180100400540b00411015403070b1311020810031019202210050a2640f0a80240e1a0303100c51815070060040403c402c11000e10305141c51050000540000600b4803c50310756402507620358081c4410200f00050140e04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 576854811 1250 576853561 576853567
    0x3010f0204300b0705180607060e0601080d050415020705030304180b06070816080d090f061401050102190503090418140303061809010b0607051516120207151e0506030303040503 78
    0x1150098004160328900c16144003807006c039810004034a80c10090081c3c581c141c0d607501f00041c40b142000024050716221000b00380c0006013020052040c0b25034000ca1510b4140d00e00516440c42c02003100700007501d1700405036038030b59403126071281403d0700c41c2c0110b0050070b08003040e886041c01d1640c1115943e03604211428500f03299950045a410483d0000b1106440200032007110110a8030400703c4240c811201c2c1001d003d143e0030403000340d5140300f000c146009a6280104a00d0303070001000039a40d00205101d40e0724601d80c0c100507042d1f0054030382c002d03041820044003a051044980001c28814031413501c0108500c4243c6100d503030707400100c4890703800c41c11500e40c0043c3c5061400c50a179209176806d002103a0f607140c0c0004a1540e401c42d6000303d801da403000320302d81c071042402c0d03851030ba2154034004082107064841000915414483e1035282c0511b03400141d071814440c80c24440b12160010000900c80505040c81120a10308502c8101940501d05800714080e0301c0c011045038025034004c001182 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 576856061 1250 576854811 576854821
    0x40b22110103020a1808070602100c231309020a110109030504050d02030a14240c0906070501021b030405030d020a020a1a0c060a05010314060403140903010f0204300b 73
    0x2c003d6000340001801c0c0203c541005802107012940c0394042c124041c05040158944100686043c020f61035514496080014015045510038440c1c41c1d10070600c07200c00035140100001309160b200e00341c0076401c4101c7c0d051021036801c40c150001c0c451805107a0384c043d88200d00c54100b41c02c841c0c000d600200017030420801000036240400c55005000d00040685d049240c03290f441c41155504800640c40640281980c11440c8c40c0c11090403010031044a181451071500d1161012a44503903224075115507030102e00f047c24482c0950644404a01c0e0f846040300b0807500c41011642c81d045445020b01c01d10614a402900d0f0b0300c003252170356a095024140b0704070142401c03450303181044042108a000f900610000b1504c0100308135060084166200001e940d5045041c905500c064500e0381d1600343d40302c3d6040c0b02c002a0b0000c0c0c2d4088081030103110645820300d81c000203016000400c8030820847c004140400d0081300c8100102a0780d101c1810b03900058116051032141340000c040c0500015070000000b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 576857311 1250 576856061 576856067
    0x50f06030102131a0d020d090c0f1203030c053121140f060705040e0609070c030c021203040608010f120302120306030a08040b121803090409080d05040b221101 70
    0x565800d0800c1c0f014102028890854100c4e0001c444811f0071076203480c0740344180007812742480003034580c41d43c0b0300b6600c43c00c00f40243c0255185100050805980390805400140b049080d00c1442203d80658000f1040703100460102c40d1101c154610401100c1200003610b0003101c100c00035429992011161454181c0c0707940081100c10318a008850141e03802c1d0303034040c501c103000d11807140f4815110a6111800d15051801c00100109000d005103000d5041c00601c0e03030402040d141c034030f50518180803920f1680c400701e41d4a851546402100b488041008900300303811200d198141c0d08171101804085079201042413501024050160140c0c00c4500b41d030111891240c000c40d4400805811100d04011603a18411141e000740e000000a94001c00c003582c4480101c401c942d04140382160000724105143d0040f0303103e01c1303201d106910895580500500b080080c17030556030501100c1e0401c000342d00d0141010007a140c030850745201220607082c60483c07100300040d0356090392a004070b9400c0910703100d54015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 576858561 1250 576857311 576857339
    0x40b012a05010e0a050c1918060503010608030c010e0d0503012904060509010e04050c091909020a0c05070e0903030c0d0207060c0e030d03020f0f09061b01050f0603010213 75
    0x100103081008860500440c50034081d119200c04444000d010045071428444d08110f180301c95184580000d500d104803d0350070311086020b5400310340358040c075a090f00841d0001000150b01c0190194207010001400e48004005040c003048104004c0c4080f0040c07001441d00e0702031402a0202040c4240010311140300b8009040e0003011440c80c05502c0070329143e8814a03681c016038844000204002140701031540e000c031412800c1e91043e182403060b0f00300700c45500454066503000c80c0c0240c1180061112000e8420070100003010581c008546d9104900c03001004414411015980c0f131188140002e802103410b01018401c020040c0950300b076417210421003040754072010888030000e809204000118034140b083d0103020915480340c1076903455a40600d41080b0301a5072300400c1c144140580e911860201c0202e030003022404199540d1b8135041307000030703005001d18a22502c00d000302c944200303c11481580040c0c0605801e0a8003280c070340c3c80204040c241d11421151558905400c0c000300301d0800f1117412 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 576859811 1250 576858561 576858617
    0x1803050c210403140c0109052412040606080d0e01030903260703062702030618010801020c1903020d0e0f1504150311040e06010c08040305010209030c040b01 69
    0x5460501825407500e9400c08000380604512220002d0200308000e1024213803852805843c0207020760b032442c500083c00c042010320070107000745200c004030008040303004002d020340c95022910721340701c4400c908510402d010840d8100c031118501040840e910070b001400000400c84d076600e40301c00031000e00044022b0419a0400c4060084843c1090b800120030f4590280030b030040110209a4a03101d24010262692903004a06001958800c100c450100045040e10860446000741e900d03103500c40070800044401c602d000c0003403106800411003207019001000222851802c40b04102221001c3c2e456078010000001e0160b8013030001080100d01660711a0b1000301c1c01482544000c048102148600180c001303621001140058140840030685d03034008545c0e41c940c6000c02080348a40a210003074405c1d4014250400102800038006a20451a5008095221125503103c0c0d40d6481d0040c040d401ca28402c904c03901810b00f0300071081c10984622080c21005941d40d609807030420704000d11502d203d41b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 576861061 1250 576859811 576859813
    0x90a0e070f0b07110913060e07050316030311030310090b12010c0c03031401030b0711010e010612020108060118060c02010315060c050d020102120c030601110109081c1803050c 77
    0x20980e6054090310010015190b090383d6403070451406150951030100e2041c4a90a0f05041c011103a00c94041101215441000002e00b5100d0440c00ca10b050900d034415a814415920410822400ca40b42541142d200352601c0c40804001d41184e5100d00044a0046990013208010491510b058010404070346011700004103542c8a40031036429507119840c101c000c80c2d075240c498010541d040c4034000e255070882c405001107504565440ba00f10b00050405010408207070b4560450602c20751014100d00c210070020022169a04148100e01ea03c0c071070160b0208441c0c00000b1070035405109111038409042e1740d40001c680c101003050f80c0c0a504e04a090703041654403070071988000c0c2c0b490040c0e000b502080d1250303502d45440c4d141c402e01e000c012070261811a401030040f10b1841411586c0c150308103807202d6034944c40740d40301001200c0350410504c04102a41c00d00600905008803207006060203100d1041400303081800b00c0461054800d1040c9012a0aa030a044880428400e402034894000020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 576862311 1250 576861061 576861073
    0x702060904090c06030204140d0512210f010f0e060a03030f020c12010621030c02010813080a0f020c0a03150510030807030207150c120c031e0507140102030402090a0e 73
    0x6142c0c83d01d4410240c00070008282d00040030300002c0010300b40700404c001c00722086464181160303581e6448042c1c0c1c1505107130214000c2000d4901c0500f070040d0f41000b4060844217001c0c0e160076407001d10080020702c1505142c59071044017140060410501c5481254007400040c105851954219000407503241e203001103014034415080b0075039034809090034000c00d40001040040c24500000440c90840016052100c1010000703000a81c0121a0070f4199409080000095540341092513441000c800020300340000003502c0b104d450780042d844044000c0070b40c21100095081000e0241d4145180000381c02e980d0460723809418800c42c0d81003240c0c44451506070320100750f50384c3d4944c2510b40101360203c0250700126014000342458a2141302c030149145800c07550034020361600440300665a064101b000210b1880c4400c1c14050079429035044000c0e2462418a01281d40c02011600f2441003200c81c20b101480c480d904003814026a170045800402802c51030321040c3d0f03c20000d100c41c03110041d19008131 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 576863561 1250 576862311 576862313
    0x140d09030c0b0c04051f090509040b100501090f0e09030d0606050d0f06050f010516020a090b01080901111b0f070308030f09061b0d15060e24070206090409 68
    0x14098420114481c0d2182010594586840450550010090541014180f00401041c3d44403c0d061340d80c0c00600c0403050100c0200c003000c03114402e460f0010f42d0003000d41401c0c84104070702c0000c3d240c86540c8203080c512541c0d8455004440340b807114400c040c5447e000c2d000c148040b04510740360340d4000343da44007221b10380700d101031440054802d60380c0901c01044001c610080144064012017940c0d000141d4100004d6082c100012154089a50414100306000c2074010010582000080030982c005001d0307422659a94041e00280c403000d03100e80e0004400070701049416a0500031190f02070760403101241080d5421100e544501c0765141c08650a00c903004075a01c2440c01400b0a4004c0c602444d19243d0b24038283c02d445a034040042c1030821a680054200700c46c415200910360910b41c20404400e80c1c030f1880d00c0003403018100b065801d200c0d8616507640003841d0361300540350b900081c000355040d00c5460180c0c0480c0e041c00c1410849004c3c07a0008101d141d005141840007040d4207c40140002050703801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 576864811 1250 576863561 576863587
    0x31e0f181501061106010b03160311130f09110c0a031404090f02030a060510020d1d040e0331062d030e0705060901020a140f1b09060405060102030a14 66
    0xc00e0340f08901082c03a080320202d000205020440c007400301d650f180c81c07941c18002c1880c1181000140e20ba42016900c2e0034080400d0058011902d09031502ca1403580c9083e25218810210074031849003c01c031500e81090a241c1c280408240c400c1d40041102820020629171400c4d200f00328a900c00c0d102c810710801010901d44d116104500300000b020500584a2400b040100102c0300c40da001715119080d20000e0003001c036030003d0a80003080f00c914090f00c0000c8107031401380c4865a4040342541c042e06052612881030000406080ca0075581e03802d14103c0c1410007084242d0210b1301b40c0400c0d0b10250b80009020090140940078001380004030340d22610000c0c54100c00b00310000002d00400243c440c0d003500181a001c0240c80090101150070601d4420f41c10300207540c071414030100400d440a004001500c030042440b02590140da01c806482c480109101305821400d01120041e10490712000804d4aa0a05101e11442038006030000e52500c07407000030035503443c2e00400007030041c8101040702040301e81c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 576866061 1250 576864811 576864853
    0x3011806030213090221100b01020f1b09010603140109020a0c080c0c090609070504180b1f111501050108060a051507050618120a050c060c031e0f18 65
    0x564807200040702c52542c410004101c1c46d008207040051a60307101c5901c02d400c08540c2c440040c5040c8000202c400c0c4410050341020201503141209016000304c0d5044024020140141ea075021940c44440741e07240d180550451705440c2400090074048401400100320340c0d402803600d0190ba0038003158005881c1c1e60007032154007041c40c0341a01d0304903200d200718cd800d01700c02c45508600c040300c03402c0c3c0d24504003000614600071449159031059584020f64003110090384800c0b44860043d0509042c00d01001403217242d003c20f9495540045d480e400940103400010649103030307c850b1014000403d03481d00c0c5c011600c600000c1c280c517034082e040328000641030b40d581488040041c81400b509171600030760300b046820100000c00041420300741c044a4691a44e01041c80310391204402102d648070030304100101c890740900302010f02e403441603c06002d01c104205000e10f104000402300d2550740445101c44440104040c2c3c2c2005107080760901180d003103c411290765420f4607003441103482c42200007008202e140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 576867311 1250 576866061 576866089
    0x120a09030813030b0f150f0a051021062405130321081005220c20011e0b040f090b09010516050405100516060e0d090506030118060302 59
    0xd10800003c20070040e510070442d0b803121101c1c8441015240030121054109188204248034103240c0c51050306035901d040410010380405805c02d80c1105c501c0d60090300034a5100d011200803070101d5202520700b4001e0080e0401d481c44c1011682544003044980e8038210f0781030717410505001051104d80d41d0503481c80755840085000d030340204441044007552120031440302c1440d10800420344100801c03c0f5840420308110b440c162201080f1400e0794001c004c1a2012600c203120180c20b114491f80c1d8030350710500032440c2c070b010700400b20000310800c5a51402c8640000100b00c611a04004c9400014aa0707405001150005480840c0e880c0c000d540d4030f030480c1c00c0d4000894480794480f003070041c041400d00c9030940c4042200d01074071840c81000760280c00350080b8418144511810070006007510700c14800d988100703600c040311500f01c507401e180080280c507050501d00368610414210320412441015030404484028010a1035a420400e0010f5518400010b035000e90740c03036103400030060f280c000091000c7c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 576868561 1250 576867311 576867337
    0x2240d0c0302042d09061d070212030411010f110c04050403030e100f0b101409040209090c0a3b0402040b07080409061406030f040201141603030605040e120a090308 72
    0xe44c1c4d01d8210700f4125900b90024410103150400902c02c40b000e06251110b01c0500d8429480d00307665101e400c0b440e050400320f5110781404007005000800200900e500310101d4241c840f810072084031481180e030010031800032120382c4e104038030301c2c01541819030080b90002e0080c9004a445511030808178984014034124240050783d40c1e12011b0380c3c1040d442445000d62003181d100301c8401600400400c4040400c0b0b8240c16003200181400c020b0340d459040b80c03109900602807452502c0c6c05003404d006a0000310422001c0f03495210800e004060340c0354986034020844140b24021084e42c8860401091009082604103a0801010034a00440c03009800018865002c059a4505041a44081d00d030180d0010040300804070b000029903030303034005990f400f619611162b50160f80c5c50004946c0d070541d007001003004003400540250881143c1d121161800d000351814000d40b0b545030b051004039800a86160b0060300103d014440b8121850000c00d03000c0c01d40e03e040707505c142d00d0f0b403641d000340d9120f0145003100e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 576869811 1250 576868561 576868619
    0x15050a0338041d0309061606050c0c010c0e09191d0f070603050424092a270207080f030709050a09051b131206050402240d0c030204 58
    0x41c41c2502856040d2510a10401c4210300c408607a0303a0313a4080c580e1124440e000200c0d510310f0314a00c100340714500c603802c61818070803410800194076179644a580c030b0392000d50902400620312400703100052100a00030700040810f5a44141041982000c201c8800d151500c415044d4000c40b204a102c3c084c0304011800b6020505010241038601411940a02c0a043c01d01c010000403a00740840050103001c80070b4500c410304040c0c1403482c002c10451600600c03542c04284124204180c0c0000c0b10141d00f4002100046180c445248409441000075011045c64101240d11b2801d0180d4010307006080c4149565070038580081c901418030f400c00c03514200064040d2200b0000762400c6081c401c014403041c6010071203420f02041840702210218090740b13003440001403001208405080d1180140b0b81c1ca1070422908801e0301c1d214003d08000d581c1a40700e03c3c81c0311603840c801d2014000100c0e40b5804200540d2410071204500d00c054021200c41109140c5d09100c00a201320b1441d0704040807440e04400841 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 576871061 1250 576869811 576869921
    0x60f0503070609081b041e060303030b06070506040f020402070c1202040609021602010311190c0204110405010c03082502011508160501030b0a1706090715050a03 71
    0x4a850407561042d000c01442c3c1008000e044401300380369441e40e0b80c00c61902c0d145090880400c000d04801c070100740700d0502070b0202160340d031075907030124054a1081e0340900c102100c82003044945d0040c0e00001d4402d401c0b003000b00340042c010354401c00140d4805800581420500c0d1640f00b07100359254440806081e850303006d1011441e240c4120030241c540b5030307011414920720001100b6034900e0403200a043c16681e029441da41340183c42519180942130320903000c100f090074801044800d0f030510032805a42812140c031003c08070001034501761081a910411840b0712901c04490410340039114810120f0a07190700c00c1a5610003066805001c0660004100c0300c8520004040c040015404550250040b0142c0e803509850200640c045820034039020800b0143e00000914021a640c0000402c84100500000b4a80c0104d1410300c036101e8a801d039502180d81b100202d4003e01180885000a0810040a0303009802503101070700540840c01541440340c01d2482007100c0408024120700703804542c40c8940 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 576872311 1250 576871061 576871063
    0x6030b0126030a080112020427031101090b0c0d060f1d0901060509070302180a090c120504020105031303023a05070206030106030c111501030c0501180b0f0904060f0503 74
    0x1118941c45100114030306240b420380140548818000c0010070142d0000b00343c15980c80d0b811010303038038a090095201c0b18900c50351441c131101c40d011045001c0f1300010111b81d13518074103114410a080d000351582d1015540c1250320400307588040c078090803440d0b40d060b003c0342c544081000f1001518410031510116103070115103006400c0001c10600301030f81010800e101a0b15041d132041e030020147c1c14090303101e4842d041c5140300003e40c2520960082441400022800b60b542c00064004007262580003200950081c0300054600443e00640030503020004201401c0411001240940c003034810349411060101c05400c10350511041141454221410315a0b841808001e004008200d82042403506996601203061400144076403001e0640c1ca040c1960358501540ca01e031a1a200d10040e10b045540341d14011008540a0106403100b0420900126055000b1301030341e0844012580c51241e1940b0b00700c01c0c0c52855100c14542d0884e80403c1c81451171070744480c02880c01803d02000da03001018284030902d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 576873561 1250 576872311 576872369
    0x30f1f0b0306251b32191703240a0503060a0203090f120403110f010c020f030321060906100804060b0f150a030e030c0c01080a06030b01 60
    0x4188aa0410001e10003684080034020814940e02c2c0c949504900316074006a03058000304c6101041c140b030045440d020000c61030400c099580340c2d0b42d1048426140008000007005040030009070941c0460618213211040900b00071140348604152001c504800003180282c1e0010303140c03526400c2100d0240e1700083c440c2403c1c0510301406880215089141000007640c84502030401c0340e01c00e81c00808101e10070420f000414600010908580d00444001c100c0d0419a00034802600e108d0804080b80041d8545100680d89490050f0350f171a40c401115000c0007110625403c40c1d07a40b511007080000340a210b05000c0c15880300310070500072010316000082c000e001000070310040c41004511609a0b083d40c1080358250029001031000449070f1320180814007205110040942c4810807002001da608911401007282e00041e030780c140004402d256180e0f0b5240165803c0032a181c207c03410b1460954410095564007a43e2500040b5078140d40307440e0304c9000582078001c01c00703030032800c0100d00d42c0340c0e040c80706 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 576874811 1250 576873561 576873581
    0x2402030402210705060c0111040605180406050a0620060a09060509160e070201020d02030f1608010b04060513051305010f1418042906012318030f1f 65
    0x555411807100000c6545982e075074028184100008505156150b06c01d5000004c1c0041e4180c549544a8840102a180e50810300380741208102111060013241840e01524044810240082c681c6604251003600c00c0c9171104c0c3c1c1003240764604071030002004400c111a0f8017414445000103001305180c1407600c1030b103000514031051139014855a09052100b004440104e41a2250305002502e820b18105d01910518110208250000c400e010802400300600c1e80500c900c0003410710480c04d0054140c440300024410b00c00c0c501c0091104209843c040d80040c040c070491100e00041441d285c4000840c1e08555440c0c07004000e41d6400180516090300030128050050301a00101800c070500020300e04100d0113a080840d40140b20204040018140340c4038440300040c62140b180c0c40e194403896150040480d00140050419640710521010341e41c00403000203400341070107203010507546080e120304800040c00b030703011320034149180103061060100c80c00b03502c034064109000c608001d038040d06980504071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 576876061 1250 576874811 576874849
    0xf0201150e010b0a020f01020a031407030c021f06030b010b07060e06091011070602071a0601030915200f090f011b020409110406080708010507020601050d0b042402030402 75
    0x1018058034070500700c41030440d02c0c030a4419a94601c0d40c54202d082203000180d07104158000300b2240b00d100d405410540c403225035400d510185980b118021000e40304490f00403030150b0884203102d5500c4800c802d0800ba0783c0901c600105406075207039581072054100b640488441c1c41e0201da41e10030800240503c5059005690040c9020708000b56915100e403107000d001d8115a0b07841120b220f2403403500e0309603030321a508110304546031102810451010b248023015402c08034070360800654903601131310940d5401a0054180c01c034010f10780c035148005001e4019640200b0ba01c0074805c2e000424032070300504109509202168480c4c0d603110038004101d60980b50541070080101400301c4102071080c8000b00160101d801040441c590305200d10200e0000c01e00503040307400c10b0310104114200056010031035010034005c0200d555180c40c03c0340c680d50280103455010012a0b42000400c02c43c12640d074000c6d0103021198200c0c40a04100c07804440b0359030801002c030340c0200403c015403502410207144544929 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 576877311 1250 576876061 576876101
    0x18050c09011223010b040615030b100903080309210c06280b13060803040f090b030a2402040e180a0302031b07030c09141819030215070f0201 62
    0x203a2200f400d000d1103115900c030010742c240070940312403094001031030070100039008101d602d848480759880c40f11206156000301e42001b08050703282c1006800c00c0c00044040c1d03241807241c4c1c10342d40d030b0030107940c4050150700540c421040341c056000c156691040f0410341103100148e03a001c0800c1c0d0f0f241002d40083c1040c201c0a13040716a80110302950812210003900135000203030300180d174070001c0c103192041d40c4103d0070f540c0303003a0000c40d4806000000704140c44160102081107644d400032130064070044042d25400d5082056071034002a4a42c8440d2000420b00360011170606026140f60700720380055100c900312101c0700e000e000c04501c54040900c0b2141400c00601190156510065924410b8004c00800081011030b07082d40d0f8042401030034040d650100c0b049601950300c0d100500500650314100102145d82000701c1c03024140070410441c0c200340140035107404c001c2d8805110b050940075401382d055029271144610b0803040cd2407160f10488807602c0300d806041288200a00b1512401c1d14100a91821 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 576878561 1250 576877311 576877313
    0x709031401110d05131b080c0a15050307140c0102040608010e0601020a29040b0702010606050a020d120b030307150b0d0c0302092508041209052218050c090112 70
    0x4501101c0b40f0320014880441c0f40e0302e07075103c074151030010341d6400b4212001c60324003000040c2c52000c51004592045049501038540030041084010040c42a0700078083e840700140942d0703010740c003c2c0d640300740b181c100801e0600380803004100a5011882a9800f0b0b540003409124403a082912140500455a10f240c450721340b540c0080c1d40c8401180c805403907204a00c216103600c0542034010307a01494001550409401c040c507004018204c141d41150140d400e040012035103511500aa0390040059401000400c2885200344d0b0007404e0212400d0b54180c0f00c40542c1c80c162410401441014415000c0c0c040581c19500d09204681d03110b10300034803c040140381e210201d00106001d00503250126641422a1100000321a0282600091485040e48041840240707a08010035a100c0e5019481c041e10301c401e610421a410900ea006450b440101ca40d041200d21680f00404d202000d088407000403001903640b400e0700c085182c024100c541e0780c000c400c00c40741c504000100c60300404980b0f203580707400704031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 576879811 1250 576878561 576878591
    0x9120a0e10170a0b03120c0708010608031314150f0d060603360b07020a1a010e0a150306020310180605030d12061a19080f06010c06060308030709031401 67
    0x24002110f11500d5503402c40d00c0c0c0d90b00340413a003d2441c100e0101d035a1030015600f034984440300d52248182c1c035413801c0f90000f9030040110490700020088404103504508101051004025005021340c1101d41380e04a0103161000314020190050f1b8076401e0b40d1500c000b8000c020960344d56400107030030582048194140c41c1115445c52144e03071550030b5840030305204c2d069a04000442c81c400900303021b4100c03081c058500e402290711b607080381c0246a40c60b0300038040ca103000c85503a0300380704486550440070001003000205910400c1d540319070a000c0350160380d1303036100c01050703070029111460040d400e000c1c108810895140000044e46030030030144081071074000081d85403014100e4882c14440f00042c010070100d90f030352250000c0c01b4100200600300c007101c54403960f260807a4925201103071690440c1540c02c0d0064011600c80c040b50100b00c1c0d500d075103010044132480e040a00803640583c40300c10101c0010b542001840c410501e5580e070346517051560a1800800801500c507802c1e1b03916210040c00c9c0360f40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 576881061 1250 576879811 576879857
    0x7140708030a05060f0a090222030b040227010942050312030f0414010905060403110627010f05190b0a060e06090a0e040f0309080c060405040509120a0e10 68
    0x1f08001c001604e0b6604414914807103c0c00c2c84044080d40c8000314040100b10603640341600031070003950500544040b00400c8080c072400031000c0070900c044d040041005a00710780240c218107540c0b0005001540c084140c444072540c81c0316041880144081c05040c00c00c140b0029071000745000c5008220b0714484c10007415086c400030b00541540c072081c0c0001401e00880001002a0210140081000c45203034200651505400d50f01100000c09015010302403540c009181e50041c0740d110f040400b00100103460407030412001c045400555298808001410500d02c500c0b841040c41803a020b40d4284454030b00800c1314095590346100c0c5104d0103007400082e40c011104d5104040941d8103540e20a40100050601d01051303211500c1c0f980d0b020100001c010554082180d860310a1301c1d00004a41c90780340050b1100b09500f0f029801280c2844100441e1800c0e070007064208400d802a10003040c000c810b07486840e032122054501040d1701400109050500b6040001100d002d4605201c2d150392114090203011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 576882311 1250 576881061 576881069
    0x60105190b070615180f0b0904120c060b06280201020f04060c0314070f06051005060f070c150801080708011401090f0b0307140f0409031707140708030a05060f0a 71
    0x42d070307940280c2c003040ca0003003508005081002c58031710310980c10301c40307400182c050013000c1c0602c80c0c1000e0a182103402e041d46031501541e400384036a9245c494080080f5103000700000f0075100583c5410242107140c80b01d030010110b0394810803038083c0326400c44605d403071854200118001160700c100710103c2002076800c1540c0650f2114a003407402c03040d030b50030700320b90780c003000407901c24408070000b00c40080103c0700200390621440b503a400c3c000c50b035034008041c0c03903681c5520489800a00c10400706a02034601c1d8010700c45a8829248401c02a40f100c522800301c51810010301c002c500444014418800100f288100408000d0700a20030401d40440c2555072400605c1482441030300e40440c400c0c281700680044142d11350113022154215074500002c42225130b900c0802c0c1c06065601d5101c2d11a003083d000705909244c01da2941408007070361a140d9070100000600c9441003040341e120480c0311031007900c0100b00990050341043c1d10307400c003070095604403035010740342502ca08045210408a5124801450122 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 576883561 1250 576882311 576882323
    0x5040302090408070204020a0503060405160909020703090e0c030f0a0218060702010c050609030d0b0117060d1a0a15090c0207061d04050c1315050706020327060105190b07 75
    0x103840e43d240112403406140c400075071041c0041900d90000b580840510301c80c120448051101c0c1c0c03103540d0200e604d02400b0205c14000340b0f038014113001d148800d03002409a01e100303107401c00c4e006540f08105001d110094481c442646800014080c03208012083c26400044070401146400e10721142803d01c030301280790a0340510004101d01042d603001340606902c0355042002d4a1503850524511a120381c0b140081c00a401e00d84204458030303502c516100fa0550500f2985903c20307407940002c103d001401134101b202c01880c4031400311b41c0c0040341c030315250045096180c0420346900318402e5058111036500000e606a103000e9500003001e0380024414100d84550401c1500800669000b0b140030018087e102d030454100410700a1906102d07000b0001007081c070098a080c1c94036201000104c04210f000e172400688288410004501a0786c010764204130100c01480d20350220581501c1a244080c0b50340b1002d411103c010010381c103000b03000c0c29079100015030324820941040f203091100e0040b41005006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 576884811 1250 576883561 576883579
    0xe120f0a0c14010e01060f0602030a1d15070b071b120c020126040605070201020a3c03020309010506040528111603110a0f031101110408070501020c030d05040302 71
    0xd002d0807011646407011000002d1001c0080306407014080d01302c0c0c0c0310701d4101d10802c601c00505140301006843c002129684c555200a150302d11440304019182504d071b500c0140480104c0d004c2a844000341200d51040780441020f1400c000c1c041c1c404000242c04085800040c1d6040300000c21010390b0000080090603c20705a083d03900040303908102040049800c0118002d5a84062005403e01841944682800c0c0700c1030380c40c0a412401d07070159202ca00c010904403042c800d8141c0507101c0c4000c9a0018040000c00341e030042e29014041240071200c0c2c404694004184980304401303000c1d50394420760a90b014071a034200b1030424403030190800e021030078602c041c501407080c2c21210381280454a94035070b012603c4c0c8141c003090380000d11605104401103400d4085000400c000481d9501c0440d800100d0b9803940405a1415180d01004105d001d89070f560b40c00d1211011a00040584040c00b501e0004200290821002a10742041c4158032880ba81c040103000144562020444058a6064940d051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 576886061 1250 576884811 576884813
    0xa060c08070c1e03061505090c0a021002030a0204080d03110d0e01021b2529091909060b090904081b0a0b041a040201080109020c07050409060e120f0a0c 67
    0xc4410590300003400f9240310610050200c0e203150612020b0740d00030101044401403099030448005114400c007900500340b03400264402e0300e001c014000090307441c01910b910011081c280401c0b640216080303a0419400314007030104540030404071004c80d00f50f08041200c2192603241014a00541160300035075a103520030300c411108290140d4500401d901c0c40005201c0a82414544544285c0d1642020005250048413211582c21060080720401d5014028090f003040f00e82c13007000c10b041c03108a842c132010800c10000da00c0301d1120501000c0034407504045203003444402c40c16a0465404080c2162090004014070b660f682940b81d007150340b2216080c2d96080e2038504001d106940c019a40150081c15111000d108a00341014403561141d080d4195150103d01c000b0180b440035a0081d00198519006202d0300b9040c0c0d000f00f0400942001f1680d4590b519400981550009a0121441500c41c0d11503e1400c0e002c00030189903d41360344025050500c203480f28652401458591810408450300d060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 576887311 1250 576886061 576886073
    0xc05011d060f07080f031515040b071416080706110c1003060b07030e0405010b0a1709010e0f2107031e0302041205010b3a110307060216050a060c0807 66
    0x80443d6403156190b038449098418031203864104a0b9105102c0f8400b0030340c200d103442e04200320710541c0500303c2a1b0782064145030f9200081d0700151300c21108211074025003000d200082090700c3c124204224180c05190520070907a0510780c41e030740110305100155440b0b900880012606082c007200135a2000030a80c420501200038041c01c1c1d000581560002034040285a40408900342c50b40040d241402a6680c41850f85000d1080c075002c480010b48103840980c00806502266811003c1e080000c0b8100c00c401074400e08280c2c1c00385003081d00da40607a10b0452502c2c0d140e0b04490400401100c141d0500d030640e20081c1070000018120031040000750300c00d400d83c038080e40c141c40142881c500409106031651420034000d01e40b02e20a00e00c6a1040c0d030070b94200c1080f2070001070f040401c41800b43c80112040705500c21200440800321505080c0c003411920b140c4040100d2401855a079005084225012002c100a4911b54000a0040803220011302006804c070407005402c651008089564141c142000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 576888561 1250 576887311 576887317
    0x903070e04020d0812011a0306061605070b0d0c030b0a060801121e12021501050609060705010f09060204031403070b07050c0a020d03030c0e0607050712020d0b07020a0c05011d060f 79
    0x103041c80da0109417000c445002084450680360016840c0310105900c8038104e0080c0004c60716030340e008108000c100c01502c0420300000b0005d100782c04941e030254403003410741c0160300900b181846060381d549480d61041d6150044a006200c00d650070180c40f030400c0f000a2411a050060b401d03104d244464110400c403042540700c0418100c1c0c1e080310f21140103450285465200e40c8403000062060300340940740b0956080c11103040300c0008019a240c031765039206100e0079801807407064130103540c1d034107107581091458081c070044c0b1441110010781e15400c0d80303807071591610300308020802d5034418070a0300e00084041440035000171207420301755203a1700c59680f0700703180c1003104d20005d401160101c105400c058042e0007003080071449849c0c0c0b29806182c0302c01c0c09401e00400d030020301682c0c0441010840c0c80561600307105014005031840b0203402c002c0e1101c0690f0708083d0790000060340b14044500601c02c10989030b9018020900e0080f056003000340c1034130f01e1400142000c80c400c0c03000207520341440e4100022 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 576889811 1250 576888561 576888563
    0x7050a050105090309090c0c0d031d07030804030b0906040f060b270a050106050702010e0907020102070816051005130605090c04060323030405060d09030314150111030903070e04020d 80
    0x92002c0e1500c08001e6403282c03c1050800d024600c854040750680c1c040f5010b540d40d185007100244105080301008402800c5c80c411510083e030710000040d888440144003010145018078000c590700d81c0795140003000b0550042907141c1c5500301c6418040015400c581080c400798001c000422003e00040c005207000417001031140b00c55403d400d00d220303034101c0b0354034040c4107010741d0f4820000d40e80e0341e00c0142c66034416424000d0001e10321244203070300d0713142004c00a6000561440014200903441d40e032103070145d225010f52003181580359031403000c12400308680030611303812030b4040c000c1d0300f45245006c0c040911458000c0c1132035214030001d811400c0800c480780000d0401081408403650b00d0515018402e5040c0340100290f07420b540f54001140c000045804450340541581e1400c100c1000c203d000707000685d411010192980d0480340c40b459001c040324041c07410201360303038003081081c07001401d6103070003910740821900140710341c10710b99130f0204043c2c0880346c00b40e03180c2d44030b6540c52001860b01214100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 576891061 1250 576889811 576889813
    0xf04030509131b030605010e010c06050c04120f0c05010216030b04140303100e0c0304021807050d0f0606121a060c0f030301080a030809210a1b031206050910050607050a05 75
    0xc0e42030003100204010003000f0226031000c002445e01c910045843c40f08041e4950301060581c62410000f0f1042e60045a00c01c0e0800417050030302d41ca4012a0b14041030040d070a840000280001070140441400c03d1001820240001d286d01c002814000155042d5444043c2c21001110006001c0c00146c4c5034290468903400181d036601d18040f0100140d84445001d4208148100400280f18150240c120303801560000cac00d030300b80b007110300020b15200140104132904000051114081c244c287d80a403184001c01010007061440c100503009125005c241c441da080c450501c20940c026100e141c001140c0c1d2a000d43e0f2041c1d599000c21080d910344071411000646520001000182c44a00410104d491340d10075035a10041e074896180f00781d80c60001544032442c4011359130314281c1e281000d0f401000c00c2c51241c00d0042c007110802503005a01e480e01002900480c1403424400918807030b600c51840a04001c4039003110324100100b41e1a0000d001d8000c01380034800c005144400e014040080303240d90741d4058 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 576892311 1250 576891061 576891071
    0x702012c1504061d0a200307150c1406040213020306040204050a09140606131202120f150901060e2a0a0f0806100f0810171b04050f0403050913 63
    0x21800c5001001c40d407410b0248400c0d1603400181444d404251403444942041011449805441ca660400780b88201c04581c5485444000200544a8130345230300d0703001030368481d601448520305104c80500d502c036035107800035001f0004110050740c07140c0c90307000745070f41201300180c5980d103010104000b4811608110f174040029400091030382c0c0690818070911031450304543d11501c480b414002c1a001300071818542c42c420080c284500d46c6c000004230075080c0010282040d0303c440d0843d250070101094903051540d00054400851a00d12030302003a00415044020420f0901d404124014000064005007485100103016610751800078000012100341c180c1d45070751604414009444900c0740c801050101c0c00c0c1c60700203400c6291035019030888001350748400c0685814110304035080b44000304005c00d1415001e0300070134017401046640c0f20402070700c402440f1000c0c040c988000c401c05030403070443c4101d0400c0c0c10890b1b49003501004075000341d41410403940358030000001845d0b0b5030408440180140c43c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 576893561 1250 576892311 576892313
    0x1b0c010627060506040e2a030f10080d1404031a040605060405242209050f1b010f0302120705090f040902100f0c0501051006080702012c1504 62
    0xa21845030001c1070803a681d46991075084a400a40e00c1c284942540040140b00c01c0010000340104980c1c00000c600903840741c00c140002d50480c1c4035610004140c20240801045409000d8054641e0406141091042100e10344112161ba070000e0586900c1040701d8a04d03008178100c8900b060f60091680007025000b90700c0c80000c02d1100500441b400d880c001e0810f804100281080d11400f400740d81400d92420032511072220a2403201050007051b900140c0641c8420b507645211810540800e2003008042000c079410305216181c8100300403450065045007542141100208150904526007801d0003c0e0345031409600398024080d401d1000c4801c0341c103c0400540b01d034090000c00c85020125403041283c10002c0034001150034105000790042c000400d000c6c00c0e54085e69081640c42c0700c5280c15404400503548050966070191184c2c01c0400b119901417000741c0d0001300e8290b002d207041c80200704070350510903500c1d0310500d07510038191110200d120009810350240420f00b058840d01d540507001e070520f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 576894811 1250 576893561 576893579
    0x405250510020a1704082a090901020309011116021909050a0b011b030c1707050307060501141c02091b1305210303040825060207020108010e09061b0c0106 68
    0x101c10b030850310820216918502c403404c031010b44042d10b41d038100404010602c100b40002e200c900c540509141b40e1080d00c8038600da66800e0003640719080003800903840c4d05124900d1825a55407170369014140500f441428071010703800b40ca0000c61901110010042102e108100206507c980c0094800c00d00f070100700300344c4070441e030402d014900f82039898003140c00c0030030040c000081d03074110f004002800c0780c50303070341c000c60080030f041020740c8045092185400a10381d50649960700000048640d50b80b2000104156081d00304580080441a00c08a0358000a40300c4111130710036003a0001d110b4450400400d015500c80a541c406803071308c2e40001a5240655822501b5101c01449038600c5420010b07609060025400c0460074286030700d400460541e100c03565013581603007200c0c9080c140482e602024402c803580f068048102140150f10050380d82c01d450000404000050b0803040180c00118240003e5005c0003c903560312001076001000b000114811071030480c41540100e00c995828001c2c00704820b20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 576896061 1250 576894811 576894823
    0x3140309030706050313030305090c0a0623030423031201260706090623040e0726060409030c0209090c040501081203011e03151d06040525051002 64
    0x303800c50403240070540e01e5500300d40e28442100e1940d11041101504000a8081c2d00a140c011400301e007a02d000c07140f1b12012070268551a8040e0001552842c00361504401c0507500c400f04117086103505d495072405844a40030501301000368401c1a10060010100b480b00784180c90070131034011205011560b4500e03011007124500562110209000203400903090000240002140d070141c4450102500d8401c0c155400700c480c4143d6247c0c803562040d0080b240030001c000700040c004c1008400c015061002000348090803007140900802040140003080039144000254005000c0760041401004e0b0300d0210b4a10006000081d000741441003440a503072000319844118030400d90f0700f084142e0303a0b040e41c0c507542c40d003036401d421403200104014418000303000441c44603070150200442c503c541e680c0d1122506603607070a6880b032030356454140312f41d40010014140000702c0c50a000300081e08258072440d07250341c1d40190190345c18055181e000c8103084907442010041c0002840c20b081180c0c00840a03455003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 576897311 1250 576896061 576896077
    0x9020706020d0b010807022104082b09060824031c12061410050c030315150901141b01060803030708070f0e19090f0b040606091d070504031403 63
    0x3e0508a10010710b51158040e548600b0490340200000e0155031085040f811407401601410390080001003400c10007003184000c4142070801052203550016214180c0c600010b0142c420805911000c00c01e07140d0209100360082441032484800752041c4140106445800891a404d4000c21a01c0341007103c100000b040494219254050319641c0001c40c1000ca03580b60240000006c403c010300080c40c202510b4500004000c8d00f480b9143c41c620088481c40d582044030414411282d41d900343c1080e041121080c84100d165070040b5061011404c0064070308491101c42c03901d520004101101d0241c032692051100485100007049000c0d15141c41030740b130b6803040b140c52012910401c04105440e2291050083d04103065403002c051030a0030080080070b1824064580e07003201440404508107829110b190142405803c0c00078860104005210603039080303a1140c01401404441000329481e80824145102c050b0a03500340b5555401c1070030f1340d5900071604054001e49a1080800710050008000c000d45 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 576898561 1250 576897311 576897337
    0x603020a0f0b1206190e0717070503130804051002060a0501080f060a0e01090b010b0901170c0703030b03070806040b011802070f510603020a0315060902070602 70
    0x2058490400740441080381c8144101c144080120400000302030f050a60030102c01001e100701e1790311320103400314208055001742c6a0444008240f00080340c0110307598241504241802410b40782070b40c0044d00c5030100400c040e103030980307c076006010071560b502201e01416005050196078a401c0c940255541e4089540103209423401c0004203107036000080e203004103003920b00207103134a60303607441b00c50b020304001c0031400041e40d00c58012100046400c41c01c10301801095903510740b181c207081d0004001e89010348010402418900a02481e590110100e584c00f035010b04000c69880905000f203860040c540e80319202c0b9000320003e01c8100061525124100c461104100d0b0704204103005000491166000083c160007450000900141c6002c09100c1c0810140717072034207000e41111000b0110710700c07940c0700e200a00550001c00c0741d43c8410300e201710a4102c4801d800300aa14159030100700d08061501000c1c024510000c51501c141800703820450103420a40e00a540700d040c20302d4114060b4200083c2d965031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 576899811 1250 576898561 576898579
    0x70302060310081e1207060213060f030b0a081c050c0607030504021813030311070210030c020127060504081e0711030c2b020402030c12090a1a06010509040c03060302 73
    0xc0c40f4034607404c61000c02200006800109a504013609140d40012011a1026024054412600c030190140402407034203841e01d890074901c0080040c00c5a40e000804ca100c0c03050b001c002e00c002903001440c103405410500500d100d0320482c5209490b54001e100400001d0301c604030802c41e04a1b45900f010b401039100b91510341042e245100c0b00c240c24101200c10f01c03c06000c010b040c00209100360131104042055a8001d4980000d6401044410600894020100761180b900700134040d424825003501204505014050500e40560000701c6800502d020b81340a803900d02150a00084404440c1c001d84d0040550741100740702040f141542d00041c80603aa032000048110a581c1004940001c180c040184a03001104960044103003042035402c1a05038400301562000045e00c4510066015070b481c000303048c0d10748031240d840900c017034801072107035065030441616030000680303503200010740380b5161418840d16962500100d42d03038015070302e260b075025040c040045202c1c3d805074030000603603000380e0300110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 576901061 1250 576899811 576899833
    0x103022809062d0903140114060d08070821010f050301290d0309050d030801030c0602010b060d020306030c0d2003010b011d060702040e06150103050c04030303090507030206031008 79
    0x24103400e000f28041407111090140d58290340d5031a148000784030306007443c0e07840541341d44485d280012504050450303070f90b40d81071030462644a03034810f9501c0141142c0300d000c018004ea941c26010700510100806520001c14604c1014100000404030014078000100d6a982d5508040490141d1441894001d52800010812b030b06494580e40b00c0710800ca542402e64100681c0a0000c01c0240d00401d6080040e103000104080c0d4401c0d0b2410201130083d519000c1550541c14540e004800c250311945c1960b2511030400b004e9128102501c0300e41d601c00c04011f0310780d0386440101e424855040f02095102403210004000c00088880c5c03422590811a56005442c00110a0500301c54081c5010b0303000c10716080d035091841c0070614290344640c0025003a00e0078041e5a1b808102910025030701c03044c0c03d81220b020044246042c6c4502c0c00f0b1803201b41f90900990804507407000851007180405002c0546602c82081400f0040000000031035028144544d00d00e01342c0468901c012007802045040d004440b0796213 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 576902311 1250 576901061 576901067
    0x8070809030717030402041116060b0603010609171c030903021b0f130b0405042a030b0f1e15030c010c0b0a0518070f051302070b0114010302280906 65
    0x1044150301150b210559000c0c0070380400d0f280c0004004030b9019460340c0d0002444464400038102c4050808410f620300720182c9000c0003900c0742e120016005d02000e10040103103941c03110070101241c411480c4036480524100e55181843c030362044038031103803d0a0080e0403500f40d050340038082450290303094426954031481010b6202d80c40c4203403964000c0d004013407280c141c6049a400c4500000c64900090203260b1000810280d0700c0071142640d0b00340c20060103842518004800354260242c80e10180e12040c11955140b910f120041e0581c7c9022500c40001044c00542d001c0c644948801c1c0700d40d03e501071401e04e80300c1001c0314005501d0b074042d01078103011080c1540500b58050109620011080b4544d44142c00710340100401082c4d145d40198050300c11760120000d05c001c070054050200c0e442d1090303041c903041c49100c521058100c10303503d10400c64000850401e00305581075885011100341d50360b800500480180c041c0d000c501c0c003902d04840750543c0314540901c05501165240c2c07110481e20755501c8040d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 576903561 1250 576902311 576902317
    0xb06040b01091701090f12080106050c060714040506030a0605121908030a0603120f03061a0d0902060d0f020c1504120e13091112030c100506040b040203070807080903 73
    0xca40452003007103051010b02811641d070350340014468000201d60050352100c000c1a20320310350a8840c0110501103001496104032044e0141c402402e101e03150420311100d05603034020003000c43d001c001412002a10f203400c0301044900030a0000e240d2034481c1042e00b03080004241611910703110384d46500340b840300c052002c182840340c0e4440360201790a490740c0d9129401a03520013013908254541d50316011000803c0744100c22454041542c1e2100340c080301d1540a021556a1782111100346807200341d60040700f80050413110100741e00c1802250240c103900c0481c0260260680c0000541d0501c0c207440d48101c071950140c29643e95800c111a01c003038060081c449010000d603405081140c11000314400c543c0100002c001e01c1c0030192503481c03800d0a2201020490340d000d141101e0390317481d9500b510761341c1c6801205514668113800281d171400511a604030343d9420980300c0360001c1c549501c00518166515402403880740c001400541d0b492411080082c007500048410a003c20311040c04a80c06840c00415 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 576904811 1250 576903561 576903581
    0x903150b1f05070311030f0408060f15152109031c14060d240905010c1403010612020c0f060412030207110402071506090614010302070507170a05070803070b0604 71
    0x9294588100c3e9181204c0d55000c49034180300724030040003031645641d1200018001000164040d05080c10310325400c4030311250240c0002094008502030b485240e495082e0341807146110130702a80d450440d04080d20318550748926400d0a02100010065003020110003000d8408009149066410141c1c000c80200d607166074895801c5502200050480e050644580d000b0a00403039416808008007844041e03460054000900b003682c0326110b007810070030709000d00d00d01e602c180c2c1042800d0050724060703d295070005204020812001d98501e001c090035583c1114070051000d030603100c100302c003410380ca41d1300c0034251401c50b80000d90304200c80c81280301c0d2003070701c81c01d56100c0c21440e40f045010381000081c0d00b00742025201c0c081a4200352401c40303460300c201e40c000d2280c0840800c005250031447c0c8214081210784605050040118400148003c510001034811415031401400c0049544501e40280681c0050442c8108000800c040c0030010107000120b101d0390f400320366a40e030f50f4240004da941e2014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 576906061 1250 576904811 576904817
    0x61e04051908030106200c06070f0602040306150503061b03070e031014010b04030804060305040c091401061101090f020d11060417070f1d1f030606050f0a080d08070903150b1f 77
    0x101080c7c5a192403030081c100e1501a80759405212419100c2000700d03481f41e48121019540e072482c600c40c8601c090807450051070118064501482c0c40b8400404541d44460300b0b0440b43d000000041c07003031b03024800701540d441d070103012100c186803890484c80c01491082110003e0074403c41c00040c40c200305008490640380e00c07510789820107151501c10f801800021380300700c6e20340c1d0030b110020030500581d21071240c0c0710160651b2028035515200000d40108075005100c8c10f6070341040b00130004a414018419245513040c2d03805901d010301410701802c40081c18207904da0190000800080395840744c0b584110605201050fa19240e40d903561404d41d031203151166045d0f0034640d190155003a8000c005040d480440c03007011070a441005001a0540342c1180c00896415640710018003950400d10141941c440d0b0903144141928104034815550760030ba215080d04021408001070b08a52080c410700000b990f0041e00100d082c066104800c024002c58402c0c3d0f4000c402c1740701600803141c41c4032000f94429103140c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 576907311 1250 576906061 576906073
    0xd0e010b0a290a030b0909100c02010203010f05130e010c020f0c1c060e1e0d0e0406290f03071e03090809010513030203030703090611061e0405190803010620 69
    0x1d801802640c0101c0f00c40d80034035555041c44012510ba480c44540300f80c01c83e00140c6003011080041e1401c1b00d148000000440e80f0610052007040f0900182e1002ea450450b40e0b4811102004801c001074090254110011f5003001c10400d0f01e0f47e0002070b280381d160001c50a950007001d4440501211000c50089911072001d034a1285000c54000d90000c50707001140416180009528001d08505024013145142142c0c460000040300c0c1c2d42c81405010300060494003031080900d4050015100a20250080340d1403e0103941460711035001d50848014811905046031603241004000c0c1c07140f0300c040a2a08160383c42050605072510030f21458071800d40c0640c015060008043c0110f54075006951800ca2144051b071000c000b5a42c104050202d940c40396035100c41c01810f01390002d003c0003080c400c406860b8000d000780180c2066600d0501c11003d41c00700d1240445d5540c2c03d040303241c10080000d41010585484601061298150043d41039036416140c40c0001c8501c0f2038841011030800b000068a60086 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 576908561 1250 576907311 576907379
    0x16080c060901051b0919290306062203060906050106030c03020c0d0e030708070312020f0304060c060c03180c1a04030b01050628020309030c01030e06070809030d0e010b0a 75
    0x115015100f5210301400401030030702041c041c030f2009142504402d100001030f6016801646a680035014075188180300c490239070402001181160264103d1444a03420365000502429442c41c0d4001c0216044002400015801c0c00c141c00104001e001c0c202c0080e00740302040070b40500034000c80d0441411980101080403610f00200c2d00100881211a40360040d000006040041000391703002a42c0140e1a0700102004200080d10304045c1414042035601f00b84010007403150040502d1149079008040480c0d41201d018084004000e021040b070015800401e890062024aa80440070740381d9441219400036152400511980641d00c802044554458018813480c00e080019020480041c1640c0c12049200401a18184410f00c4c0c042c005a0000ca444800c5140400c070300008501d0a0a0402c0140112507009854503002013503a01442030f103601065502c50b0800c201d03022a000c91808200a8040d80c1c1924081c1c01441400c9124a03121003000c140c00c021282c0070704000100b0381c0002c2c9000c502e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 576909811 1250 576908561 576908611
    0x112020d05100c110106052409041808070317010b040b0c120c1b103006060e24121510080910060f17010216080c06090105 54
    0xc4800201c1d401c2c05440301d0a0b038082c900340210310307400c940c1c0e407900c01141c03a42da45a142110350550020384525212000f10030740146442c1120007070805c1310f00b110303a298842800300d000f81ca240c00350003a00c6151811408184503100024200d0144203a881c0b400c0f901c0c01c205125411042030050400d500d90410042102014180c02024031502d20000d03143d0754010f4011b203a0b0f4540001c40c0c400000c0e009000c0c0d01070844208104d24048403400c80b8406072401101d00020000b8900469102c020342251000115400c1c1003103030600c5030a040e4400344032861b2148001000495001030a90003041d0a84403003005003e45114443c500104002113030800309d60381c0000c0301e200300c05000209440006882c0ca00c540d01e501c0a48115568117403a40071182c108408240e24000300444020481807038840180f000402004400003200c400071454403ca003a0811003500a1140e00c050f098443c5d12038800204209903040904400300614050300d5596861040305400c1ea001141c0c56011010602c40030049010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 576911061 1250 576909811 576909829
    0x1b1b060503180601150f14030c04050108090a050c0f030c0901080f160e0718080a0b01031203090c0b0319020d0b010f111002070606050303030403170618060607080906070602070201090e011202 84
    0x84916001040282020403151382d0340c4159210ba2032280300180500c053358001c00c8094004160500402c0c42c541c5548901d0b803100394243d4024403c218814800802c0d9904000c0d1b0010108000d04070203103075a4848060380e8584500d4800c50070f1b0300441c010014003030021007030a004c07035814054031401c07a5a000c008581d4840281c4da10380d02a502c000001c11386480130003a030301d0300e10310502540810b94118200000c1a18243c41a40d08040c00c00c601c220000d03010100640c01c4444420025071207171212a00c10b0340103480da0084407600c92000c42da60070383d98803c1c1c001c601051800c0c5c8501d00042c00140302180e1000005a00e1080c0d0b80c01048031f0301e150f1a075507008203c07280c0514400a8516242c82c0000d041d6841501c00f9000140c2d18403507965022a80c1512903041030301209c41c0e00840300c8298409175104002403080d40309031300c045259414418a1002c5820201d001401e40fa81da89892610f00001d400901007640025020000800c1c9a581d2165441c1a0755500c91514110b103142e078200403070b80f1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 576912311 1250 576911061 576911087
    0x60509180a061a0304030e0d05191e06150506040308030c0705070302060c2b0c1103010906060329151e09010b04050f0906011b1b06050318060115 64
    0x96600c0c000000c501800c0c2c2004246083c0320111560f490038141001881440003a2900780300325084200480004c0b0300194601820b02c017000403c001c21071508041011403101c04002d5001c0b201300c0c407040100301c0980e000d178184016130f52034001020b4407041445100c0c0078030b0100900084c810804540007410480103003908610450480f8035482e180c0d40824415008030b603516a0990020315000c8202c051119450000342da03a00c084003a03000c040710010a50049882d014045038140112586980c170203405c5114000c0e003040d8148401581d80c034001d4058649a051403000800070a40201080362629050b070081000c40711042000c80c900c0300704409103001e00400c003540c404202c40d4007080c5e12080d124034000c0c0040d11801e0340366407504043c8a100c09007407041e030348a40091000c10142c3c0c0c1c0c11800030341c00141c5800d05140110902e292401d00b1801c0345144c20b026051088001034403075409001140724880440416915403607190609036900c40c00e0003042a5084029082d00d00d01d0f2107225402454 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 576913561 1250 576912311 576912331
    0x801150215092e0f090507121b0f08060906011d0c0c0d0f030b06030103120309020d080409050a06080a0f03030c0e0d050f0c06070305030a090c090203090d020706050918 74
    0xc010000fa00c1e01084034214400d2500540c45002c6500034001c0c4036114010000c3c01c07050051128954031079031141c0003130150708501006004024180701a96034545100d5201e200e82c0d500e11516480b1400100b0b50305e1180003000c0c89403800040089401150b0310b0704803500b160800588040003081d0048011000b81102c04d01603080c0b00400b02c0f200d0801c0040342541485c0c998160042c0c8040e801000d9070703070400b80640030341020001000013500d8440000c2c3d11a002d07281c00500c080480c80010b1980344a0180038045c0c140205c2c0101384100d00303a0006028050940c070822841303946200194840100e0340c4043d058030706c041002400b2030b00941020b10b4180603440c4c0414100036410009070503c02c5080180d840d98024906001591420003409581103000c031342c0d0038240385440d60300230f0803448020300d00c401c500d0700c0e40604000c120f6001c401e98080c101c40b820640d180e241011805a892681b030104000501c604000000e903240500103c0e070b003140300940030084022480450100b0144040c00110403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 576914811 1250 576913561 576913573
    0x90515040c0f1a071a0f060109090c020c060903010b063601020307030e0102010e0708070e070206060607110301060308030a0e01060e0105060f16020904140708011e090c0321080115021509 82
    0xb12441e036180319218403030320071321b1000f00c2c20004001414001c040e08098091031501d02030441980d000907140340510011a0700035511110400403c1c050700c403000810390408800716058041d0302e1840d40d8609244010303a42c00d10000781c84004210a180805151400368004000c12800320f446001041d0027075806000106100c0c14004026207001400d03441841e1a4002c803c080c00701c101107a01c290313080340c86803005019500385030b4001091441b5400005000d2840f0140e0048076032400e401c03980c000e5400c54103d680301e00e0b00301100360181c9440c0c049049107520300400070480c2e24000d694981038800243c401803c010810b800c410643e030003101c501c1c91602515804000590750000c02521031880b40400300075a40f065405207141c5130071a0405c2c14141d0510500640342c11142d004035105403451680400c0c00c00036400c0000888801d0b030030182400d40a4407414407050404030509813241880d1740ca40c03800c0da0362504030b05444140300500c1c030b0050300039080d603d902080c40d078410344d004443d00d025214 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 576916061 1250 576914811 576914843
    0x1f05270106031d0c0f09091c1e080f06010e0a08030a1715030c280305010c110601030f3f0801050904020a090f090515040c0f1a07 57
    0x42811000d03444000040d072505400494242c1101d100d038102c20845000380140c0e6034600000d45984c210180e40e6020708071050019000400802544041090003024202e0f9510140001400700c010318001c1541621a0010b050001d407040041c10320580c502d00ca609042e490f440c00444036245203440080c1d0000001c2ca01080c1060140000c01d41a220390700c4001c2d046125034158051072a0042140000102c4020036400b141c8000c42d0300003100f501141c243d07d00b44900d00c01c0012007100043c0000080a0b40710000c000c200c4150303c2094081d50640b10030880d08001d5498a5840000340030041284d901c240e0400d00140c80e0003000b030150511400c00a087d1030000034100031031100046014108a500c0324600e0110782c008c81c8281c0540702c1a142901c130740c0742640125250b0707801d903c42c6101c10799848404000c1203d440c1c0c41541c090b03600c00700743e0b2680c0f2612041c07803000340320544081d03070100b95030700c4002118281030030240d0880f6450300326810202215450782c02a900040340c2a0340c96585415200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 576917311 1250 576916061 576916129
    0x30f1e02060f34031b0903030c02281a0405010207120507080312060a0f06021b1203070510061202010912021516151104050f0d0b090f061f05 62
    0xb86100f00c40105400003980703c02819604021060303a03041e00c01d40c2e034480c400c542c00000641540d4140c14002400d494510114211074032009407074454045c89101c1400c4604654001400c2f202c101001e080c40080d20880350b204c500c00c900c5124056030100c2c4080011210b030764500364400d4000e00c195003109948819131401d591201100426480e1810100050303850710f600c42c1ea026000340d800c2810028200940a5502d506820245511a4156129511a5407180c420940a4088806a0f43c81d4a450301c3c05c2d42d0349900c01c100d01c04a040c00c181000c12142c03080d180ca0051075030141d44007881c1600d44480507003001803421003a03030811003000001c0f950150103002080003000c208070103400e20762030781000e804050043d00645070f40760900c000c851000c0310750403e403420b6910454004030340b0400f810018210b0303901c0c003100030b280d082c010703007003081011010500644e0b52070038500b66000d59458600840c91070107508201e074000c00c070f411030901040c208400000301c60844502e8a0100362540740e055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 576918561 1250 576917311 576917371
    0xc0f0c08010c0c15050103020f011d0a2606060904080c0106270c0806090c16060507050307020d0e030706081503300f0702010e010219030f1e02060f 65
    0x50030100b00002c55490070401c07011641268040f40110070001035040d980017274045202d041e11903040020030414017002031580c1d201c3d00d45440e40103140d488071940c1c4dc1201044403004941c82510210800f054031b403100700c0894030030301c1520002e10540d89075032250341d520084d0b000010307195200c3d0341e1003401050101300781d084490042c103010b640011004d0180002c0d4140ca40541d40d600801c0405010322216849044d0b020b5086008568020307201c01200b08502110010303500c014040500b043d081c4011180c200000b1030240d1100c0c0c0c250745101840d103100391000034440503050340541c800a070402015110300c4505400080c101d60fa4100b100b0130b0343c0040e2601a4840c50f0410030304104043e40902018104181860400011668142542e901c519040c602404e01c0c068140030311000450000d038401e015000d1f64005030300c4e82001c214410f08000780441031b420711304c20218101c2e0418172145005c854a000b00f0070070aa004217001c1d07440400e5401c0d42e40c4013030300d05122510038000b001c81890007c610 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 576919811 1250 576918561 576918581
    0x2a030708100306051312020309030d050c010f0908040f060219060b01110a03170601090501020304050d03181d0a020906030a0b0102031c02030a0510030201171009181a070c0f0c0801 79
    0x13020170020203403c0003000c031204d2148110941d8020444200305440c0400c07400c03816030280c1409500d40b41428040e5014010004410140d0351906106000f0022400041c2051320503268061064a0301d5982c00c0c0c1c1d0700e802420119507580b0400100038001021a00201d40103c010700d80203c501c02d2504200b46800f488a00482c0840d09507442c546d9643d5814441550000007442c100c21503526100020b501ea200b2070113118000d031070000000c0241400742003069102e0002080310031400750f0b10011050311030b101401140f1000815408aa030041f414004c0d0762001c503009090a1440d12030020341c80061015079241819404144281e085407441003101141e036480031900944d032403030448141c0c01150002080000c0368400c02500b40050b0340d000170311540102d15101485002d0300ca80701c100400504079400b81042605000c90100c441c45c1c1024094141d82c031401302c3e1811391040c0e082001444a00312110400aa03400590101040d80c074400014014010704070342d400e25848108840c00d4509040c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 576921061 1250 576919811 576919831
    0xa060207061409012003041403040f18090221010b03060a060f0503030f07080f130b09010201230601031d060f09190308070c0201050c010c02062a03070810030605 71
    0x50600801c600090500d60b011004500802200140094107410045c050220400d500801300015003000071816500a600300d05c44112034645507104051700101c6d0b018028000300d003028042070103001c101405507400e5aa8010715404140401c1050502c6040788004070310150b40d00c601c0c84000b0707a1800c0c0b02d03603801042d8101000c2003031800c1031555100301100e5403140f80254020030141c181c01e4076001c19074900a60050b50aa42ca005100c414076050140901c03010207a8416080040c15030b1501c0c0044c00c3e03400c002e8000b44044480611004110720009015803003100b43d030350000707501d503200398030003104031489030480410030030480481407600e40d044403280c0343c01c40c0c08024402e03114802c0001220388100c20522100c00f58490760000c1080c10090031007820310004081c4d94003168000d8042e6100388120ba0020040c9166540000b59595415140d15500350b00305010700300c0c0c03214018124000241c10094051450f01c0b468412038002a00a00400041200940201c0000c0c6540140d07802501011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 576922311 1250 576921061 576921071
    0x90f0f1c02100606200a02091f081207140f0c0111070b0414013b12030c0709050a0c08011505040f0e010e10081b120f030d1103060a030b04050a06020706 67
    0x241d01402c503503a117a08402203a5214080c004016a512200c0b01da012125a10720307032444041400445a048540d0042d48050040703a050078801c02682000d081303194082c480d90702c0ca0f00004660182c6514455140c09a030b50042110403400b94056426020b01120b860304039400c1d9647c41c1c10003038581c0c008d600b00108407040e0007071300b000c9580d0091018204500c0c20a0505806e004a039814041d184a000308407008141544800a150340741a00b110203951000252580d5007141081c0b070b6204d4005024a88a151600021521070211882240040002c0c0e0700c428405900f8005005458403220b803680c81040070403c80800c500b8007100d08840109142d500c101000c0d4140510100e0110000f420440443c29810007080585070015003000d2800003142c5a0710f0100b45c034004540441200c0024100510800e408680c1c0713820000018074031021502820804691031042d040424802079400540c402c921080c20b201140280b0100c80d00301e84034800f201c5002040e503480f034040c1d0308414400e4591607074034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 576923561 1250 576922311 576922337
    0x6040902060706090c15090e1612050c1b0a031404080a1506030c030507080111070c05010813060e0a030905030a03051b0705090403030921020d05090406030209040b090f0f1c02100606 80
    0x32003180c0d07009130f003648a0301c00c09c80480c0ea0041c18890381400003441d0359120404070343c20181c4101140d418074008504031014003a094840e0343e4426120000300c000034110100c555603181c000c0140d1341503406240144c10341298688806c11540f0561500807081d640d1a40004001516190954015803041700641b0310300d0b00d04030b4100d084960b200040c1004c140708004010020746c1042e00007050b203600b42000c504a80340d09101c0c00d050303407032903d009240e50f01c0c0c007500f1100303940d00040310007019209941c0da98007161101c0a15407116003441008001c5801404403401c0c0c0c0311413126010000030b9807011645140d60700d0002070030700c030010f640550119507205400c200340003419900800f50944032800030403001c0b40180c000c1d41c4a022010840c00c04c40049040007507507690740c00c00e400841d0000d000c200c4508180c00c2041c2100000d1b10b10003040d100c1c80000032149900421a0310200070b284000d08050000c0c0300150784d0780000320684a0850145080121485800e0b00c00c04d000b4110f00e6448400401c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 576924811 1250 576923561 576923579
    0x21f020f070e010f090c0201291e030a0b06013c02011b03020313020d0803010501020610141302041d07020c0607020d140c060c03090906040902060706090c1509 70
    0x2500403245007103100b030050202c0d500d401ca0310022606100400503410302141422401016000c10050740305040b00400c500740449800c5100502c00f044940009001755500000c00019441c078680390142c02207134020740407403c850300c0709130300c2a01810b15006440341c40b4546aa40848070740c1d903d0103005a900d4600a0300d059000480d0075101c540000c000d04101d1504112030a03d203120a0400c040c2c00200041c290341c1c4003000d00d070a0950260036002d0040b041d26100050b03820900070140140b00f10b40008008498806a00c02115241c5001c508180c0443c130030f00c071800c0a412030a144940e001c1100103140790707228800120410f031418000c4410b0a001ca002414040ba8000d520702c905404d10080015903540803110880e107a01036903c00c6da000c0b0541625061840c1c880086511000101c0e400c0f42c000404030003000090f0040314218038a54404ac1004229080500040c0d041070060208100090700303030340940e41d03d6006100c02982540c0c0c802001c00e100803c9007810001901284041001c028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 576926061 1250 576924811 576924823
    0x2090f030f070e01170a0b0a0b04020d021809060619031d0f100203010807051908070e0411041e0207060f0626010b090c07060f0c0809060a0522021f020f 67
    0x21140040d40801000842156441b101a44041d00304136139800030404a0101c0d0b44880c600c03035406041552102c4c103c1100000075040144e09040742c0300301d031450404a260402c03035544038042c014607a03810110b2120301c60b8120030741e50350040d051542d14900c41112040c000c00040800d50a000200322225000e082141030544c030045920440e8014401885400780100c0d505007560740560783c6507400c0486e4100d9034841a0b15a100020601565001040c03407208441403600c12030040c03c10800e02034062042c8411a0f842001034000303401c041c400250501c215400a00a55004802c003081003001014030f00c0441e21143d019144004503124882c54004a40403180e41112180c4e008101229442010541400004001c10400300b80010b07000100440b5030711803003070444405002c026041c00610054440e250542d03408000e840f4900018009410601500d48608e1002c0c21040c10f03031405010000b0020700b000001c0f03911607014824452452550b29541440c0000e50b0300a11504241c805e0b130300e003048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 576927311 1250 576926061 576926069
    0x160b0d1406011e02031902030a0212040e070c08070204050c09100206010e04290a020301030c0512070e10030f08070b06010c0804050120010c020109060c2102090f030f070e01 76
    0x2058840410403aaa044184540c0c03140e03069240c80c15102220b0750481c15840361aa80d890b401056007681e250091f800030180c000d80c45103408580c2d00448014041d420360065205445004c0d070796400044c101c0341720b020402c5113207108155003402c101d032030350008042e5241200e48540805002c01c00780868030380b82a10034018500b44c0054442c950410784c40c0d80444500a10107000340a08840c0c1154803102c01c4445184030220540305200d40c1005c1040340c000c0c0d4001c0c40182c42000c049039000c42c030f510b843c01180000c442d070740008051701450129544400400249469211101a000000403404000a400716248991025039640d41e1034030f402100100054142810804070301402400910110111820348100b42081500914022000c0300c04c100c042c6500102c07542040303000b20415805400c12154544105402e00c1503644c5800b01301c808080c3c03866040480c965050810100d540030307600a024620026003002000030040012920b4007103400d091b80c2c00350b48080c030100880043c41c0c0c4030074090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 576928561 1250 576927311 576927341
    0x320030327060f090904140a0c0303090611030a2709020409060801060602100e07241e09230612010e06060304020607031d030d0315050d020d14160b0d 66
    0x11181e0380c1e00001040c012034000e41c2c01740701c00c5000300c1d0a10a24680c0400c00703184460844010039000d01e00119070022512045002c18503403240400c88034040d800c0c140050144000842c100300c4480300440f00484001500c0b81c850904070010a01c1c84903800e0340001070701d050a0056552450b0000c588100c45140d032064a16901d80300090205a5012074103a1160f6032400010410000e94021941044640d03400991b0040055102d613015843c0303800c003041c12010a843c0e04440c1c0d0220601150203d10040e40308000803040041480b1610484501c0d155a1003500107998403504e4840214805600a60a2194031078051004100c50350140800d1a8804000d60308a130441c101680400c420340a4014000c052201400401c450746440100350311910030000c003152000100d80001500900d11180f580c2a0842502c10204460a1415a0a1200781d024200528101194480b0505030003682400342c01ca01811840221002c1500700c584040d000d0f11905660724120504990f0484242c95056540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 576929811 1250 576928561 576928567
    0x1205010602010b36100902030412031409070b0a020a05011802150a0c0f211e18090c020f0a0c1503050403120b1809030304021513032003032706 63
    0xd220f09890050303550300c813540703c85a03880e166454500803000803a0001e03011144088104001e01550901c03500d00c501085c0c504114603002400c5040600d24100c03624002948400f401300085090361008199803820781c415190b2000711542d40380d0035140003400c080d00c1c0320b0080ea903510035841c103030380c0e039580245080202038a0408030344030290401d246040c1c083e001c5840303d1216010310060141c842070310360070f41600500007001c105016002080611b000030044050b488503258070b84c09124150b14045482c41c940c1c2489160803282c070701805404a0080860003040100001490100110b400151142c9138442c07007a41840300c04180040c6002e84c050030142040140400301c1e411041c8034030301281900c008214403410a01149490001e401d001c94001051020045503200110186001e01d100312100d00109059140b4210240941c83d25104a11202c0c0d00400000344070108240c500c0d000c410401c0080704495000a040da000182d4090656420f0004185440340702c59410703d4240c01210500c0c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 576931061 1250 576929811 576929869
    0x2070807030b1501030b1306230d02060a0201270b0f1611240103110a05031216020d031d0103020c0717070e091605030c0f040b011205010602010b 64
    0x100b050005010242c040d01034501e014182c0c0d1203038000c40c014580180c01c0d50b02c1000002440c01c000c0541d889201c00b202c500803108280c2ca0b02c035114a0b507004030007c12410804850303408100942e480382110300c0566503aa085c02908030000220301240820441c01c92101180703a08105241a400428058003400003d041100ea141aa1142e14015038189842c0010207000441203107000b02021180e40359000140c800300d12501c8410700f15060724410884551031214210a1050384003003405016416003000c102942e101d10110040e2002041200000440c0d21881d0040391400600d004190002540d1040140ca0741c10001c9107150201000c1ca001c40c42e042c40400300540740c252a01030003406440c1c0d0601c01040082c2049000c0c0a003040cae60707000c049410044606981d8000c1c509900040c1c80400a000940d0704d401700304503400c004c014015003071140e013002c10031000b0864001411305102118034011070000ca603124407400317010a5000000c41c2403072442000404680d0f4452100407402e1051902 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 576932311 1250 576931061 576931073
    0xc100b0a12150c05120103150e0f010e071a09150d05130201020c011d0d0512030a020405010914060301030807051c031505030606060a0e1c030306051c020a06080711030c0106060207080703 82
    0x25044a400c014450308c4c020f0b0320001131002c0c040c003095180d20744c400c80b414040400e0040d448085500002821a10740f150755420602c1c814111036680c042e01c1c4010f00c10f211450501519a071101440a1013192415940c16030100c00c071402981c0384140002070550b841c0865804000d104000e60007401c10208204000d140c105484402c94a22800381207912007000c01c000c42042007180813000c0d07044090701e900c0c00021200c0250410720949000600511002914000480c20700d1030108004c1e101074516801e40d110020141d0101d40121600d00c01c0d0000c0b10750580080d0a245c02c1c0b01a00e940116900d590b1001e032800385c5807640c1007584250445414801547d5658048884150341c80c1003020515081c2000207211041a2501105a403000c1071803c080583c540e10107002e03240d0031580220003803401d022103a2080081c51000303400640d40501407060600690b803065218140e49840300241507050304c0141143c204001d58840751791211820b01642e901880303d00b0280032414014040070b032960b00c0d0070b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 576933561 1250 576932311 576932347
    0x60509061e011101020c01060308120f0702190c0b18030706030b091305010e03070b100906180504150f0204050a0812032410050a140c100b0a12150c05 66
    0x140c14010b4243c500d86008200303405072100e4000c1c100c02040740300d607641401590340d0704c203c03060f006030700c11480060352080e10082c40e90301031260795004000d460014100c440600d260100c09480040150400165204d015001800c1c0c034401522100c0700c812840080c1440e040c0d858003c0418942008103101454030f65900d555404421240400d42d0700c1c0c010304101d401851800c0d07a015640c000040c480c1c0500043c04003660080203480c9420545503601c00498040713840a00403004912156602d0906888440d006160010701a103040744088410790300540445110100d03e400d000d4001c03074100903d10300b07090410000c161003c060121811810080e040500c00245044422851240c2665050004960100c844400501000c8150803c42006006a0041d010ba1000148448e40e07200300c076001042900d0780c050f407602c0244145c10f1441c22078409081868800342c0c100d88800e50014105012443c4000403500400c1e4054503a10305a44100565020030010700a104040086091250a500b05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 576934811 1250 576933561 576933619
    0xd0f021204061d0a050f0607061b050a020c0307150503180609010f0534140d050411030f0706050903030702030a1406130f14030d062402010e120a02071806050906 71
    0x1f0b140c0d07102ca041c50203000419031102c2c29681070320080e03040f0a41a410030000c05100003103408440400891104141d541c482d680106000d04007000ca0340d120041c041d02c00355400013807e411301d42c403c00c141c3d01007520b4518102d07116400345c2c2d11040346a60803001c6124168001040d0002002c010155070035200c100d6011410351448040040f0340c4041e82c2d8414001c042d140c00f075480b02c1e9551540320685440c090001902d04cd10358500c0200848034500c2e001500e0400840140b01a0400038036080c4142c2d91500a07000842e014081000b032407005a80c01c0c00f402049a02c10b4804da070180d44c0030b0750a1031501c24014100b8620b01303104035009020070780e0207000d07081030f40e13009036a84000c0040101c83d0f801d500070580080941c609000c0b000c151806411403103a80290f4148498895442d202c4c4102d09903114100080340a811085031103094010001c0100000c090a0044070340307880d41c0301c08001c1c5159101580e41019552694203000341c2ca48003e02d07070b80000c01151249500ca900744040c1112807a0301c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 576936061 1250 576934811 576934819
    0xb0c030f0702010908060c0315010c110f180a0207030806030303040807110a031e020405330d0f03030218060910081f080604230d0f021204061d0a050f 66
    0x141d0701d0110381c420604400581520700a0f500c080c208075405d401d00d80c0080c0c8070310b580401203412034101940300e2810042a1900042c0802e001004a03007031001010300c00000c01d03040342032100c1d06101e110150087c079000700d044160050303840c0301500300107000910142050384650401c00600c0041442c40f4103039604c4076000200044c2089425000641c51569a0700c01084031241b0003043e110500125002c620450007920144950b0f81c9400f11040451800045080a841441e40130710b0403a00c1445844049040902400301d0031000d600d51440d0800d082d401140085d030006000600c0c2c440312040072400302025a10035080141120005540c03400000c480f004026504c400520b4110081004041c1c000281400042068039010301d617440c0c0e40120380545480f07090701e8a05069015881108102d100001c0284c1042622032004681c00c6c950707004044114032660383c89500c0c844c0304400420003030240340c03980040641c00d400004056131091543c10310405913060704020544a140d040680410215 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 576937311 1250 576936061 576936067
    0x71203061205010b030f07051c020607021503040c05090f0a0e0a020604060201060806010f0b0313111e01020c0d0c0521070f031b08030f181f090b0c030f 67
    0x110085004054903444452040024911141800303010351000b800c481e0268240e03250f003003c0e081800e58a003690701c92079820107004548400483d90346d074072515802d80b00038040b5107411001c1e0001401d945140700040f0440100105000820110342c3c504001402e041c0d400c0d400300e141c95152840045401050699001d803240c42400c12508144402c040c4960b00a040da1703101c80d01c400e4024001c01c1e680c029804540300d4500040384050b440b08041c42152039040042d80386941d400c00d00000015103c40c1140c8940691406108a50f180e01035419150a80c803010a02901c9410009141105040069000321646181400821900d020800581c5c0e42658243c820341a4540b4001c120700209007800450b005031a004651404034050784401c59008081c200154020300405d40401d506030b200300440c41d8420080f400079421440c2c01307130000c8000c40c80405810141c80010840303184041400a094900071444800c0b65030700f00c481107028081c40c11009007802c0c9807000c060f950341310f00e943c00341e18101c000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 576938561 1250 576937311 576937343
    0xc070807020f030d1812200a330503160305060102031b010501090506030d0f200a0c0503010f150e091e060106030c03090803131e03020c03010e01060b07 67
    0xc40310b420444900a82194035040c2c0000d0003c180809901c041c114005414200141440d001c0001e80040c5810149500341d1107000600403c0d80820350794200d403c40000c8600180480d480f0100030b10012842c456030f0401c0c007801060058006101d010078082c84002c2c02401040c01c030140c00d0342051845e03400c000889880e00b0006070b195029250b20860550603143c000081c20034190005412210415000d10107500c401c410551515100d0320000c00041c480c281501c0418840c924a69090318400c5000d05040c118072820360500344100400c0c0c1d00c003448042c04000038142485038802c100311914041103460765032960a00010000c4c411074421400482c04078243d180180070865a41d20401910204501d080c580340d42c848100344282c1c0040780c50b00ca0b518100030b00078001ca8041a42c0030121034519590714046c400d4000c498102601c0902004041214405803010030420190082c1c00a0240d0b0450808160954240e24030182c826410303c1001c11681061609840304640e01200d41c0804ca210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 576939811 1250 576938561 576938569
    0x121c0309033903090f06080702120d06090f1a01050c0a060f0e190b0c0301150f030603151409031204080f12070c0308100812090a05130506030d03050c07080702 70
    0x203020b942080e40042ca2081804040c2c20442003012075540100f0071109903513402040d21251400c99008000d44c015922028410580d0001419000040e010009110362250054800c61b40104540348006e5a02d40d140415128141110a00c00c4003d02c0c1541c980416400844e03128100707000c0040c841070720707001c0302030006a442e0403c400150800c01214102030f0f103240d24048826040500356494661032002c600400e2a00044a05943c1c040103400c46508402004035a42c3c2c0b001c000e6041056960305c40030000582076031580614020700b2102244031900040c00040d90b600140860603a0b6004100c942e8904070704d0034610b64040c1d00319048546910452042d56410300c01d030103242c3d400d03075044070030007400035004100e620761207010303aa03840025642c00c1c0c007298100d820f82c0122440b584c403200c8402d1440c12500000e248455025018030211551640420503800487c1003244d1038176201c8040241d1750a040000f072080b91854035007407105040076004500d552082c9500035080715000641034041d51a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 576941061 1250 576939811 576939887
    0x201091404061d01030c090903080114190f050a05041407053a0b04020a020a321e06040c0501050310081c0206060d021807030b121c030903 61
    0x100b40a181c0302442e00e009070000ba0f030042404101c070161402c3c013004c01d441407203200751540d03103915840d250200d03424190030046480c2d581c07400c2da038002407180c0f16940300940020f801e0000d022035040380c1a05820441003100c0c081068210714019841c018604041d684480c0c0c0d190340044843c10700c203a0328030440e081001d910107401400c2c000e00c0d0b00c4031005c03000c902d0a0942c109140013007100410038005408100000c0c0c0c4a0485103900680c480040c030750119080782c0744001250940000c45801103d2075040c0079207400800a150b41913000102e5036880054810f09074002100810080c0c815460103640f040c3c000318803805200d041020100014551702c0f601c001e500003501031841190f081c1d180c1402000d03000749800ca5004014052040411a282440d00460748120b41c010b05100030b01f1100844400300c000f00a0945041685810007041d00c0c0c1c0340d180312050740e050f140300980344c0500b4908104149042c10708543d810545054920400710394015980902c02c1034401c2820228003c132900308040b40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 576942311 1250 576941061 576941069
    0x80c1212030601090506160b06011b0201030b040e0a06060e0603061006031104180b1207080c0f130c0203041e060804032d05040e0627040f12031a030a020109140406 72
    0x560005a0720400744401d14072447c8140310b900c4c05140359542e0030045a440000c0302da90070221600c0300c10680150f01942111494030000b4200203960308041e641d142c648402c6181c1500d0749651000e00b84603401034140d9044e03020301c082d030040c8101e051081440790072422510490082541d40e00001440d0a408000c07140241004100800d280c182503000744018a101e075002c511a858010f00c409500c0b00c042050000c8818440240c107100c5d079114144182d4182e0000050f0b072240c0e0300b00c12001e00308618451450120450780c003e540300c030309040205e071030700115440030b0901c0309100c40100728140d44a002c855203d13a146c54803c0c0b034880c0c6a80b19142c904289920303101d0850741003101e00504c682c1300000e0700440b201401d007030a45466400a02a244990112040161208040b405404440440c4643d08188501020480000651615405800240080d4001070f4986e40e00309000321941c0074951244404801600041a0640c00a82031840502c100556540b50038089131076642d896100303034024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 576943561 1250 576942311 576942319
    0x31815040f0f1e03080301150e0402030f16030605030a0201050a05120c180906030307110a0b03071206091406092715010605040e040f06020c0a0507080c12120306010905 74
    0x19603181c600c0c085050b4841d02450070303042e5804000d85800c419150221046030307001900c180c5140d00301400300c4240d04210107401c1c07e01440c896040040c1c1c8841c07004511490301c040300c541a9043c00d6540c86640e0f0b081020440415082903801c0c0055900825031980307050b0309003049955040301003000e9820f0700a166103a03c413160401c04020004001d04000c0100700080805001c0400501e400c001d48604245c030071940590090181c1c0c80060b000c1d44880b10034650050011a02654401007816a90b000b101c14000051000300d0603003911009026010152450b0303042440b81c041040c80c0720796180402842c2d10b10034400140403c100814008403000701e10010201d01100700c003100e6040c3c2d90b0303c0d034441640c0b02e20f9074a6000018000d10900984080d219541840b01c5151540d40f5480740c8002000300076200568200480201142c08001356070095200c2c2010f03054403071030701c005242840c0003022824010b4108090240700380341d000c00c2c5e101d0480d1910b070310f1540301d17162880102d8210380c80760401500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 576944811 1250 576943561 576943589
    0x30a0803041e120507240506091b1b0c09010303020a02040623091807030809030f06010608010603020702061c09050d090506090103050411030a14010606020d09140415121403181504 79
    0x2031221b94100611800080c1d51407440d40c1c84007200c95504c0851105101071450003803104040010211440005406205003107461f01c0c0030600000fa0002420303441240981c0c400d40303207034045041600848004001e100000fa16024031840140d000001140c0414410020b41c400a04250161781012100702d04c81801ca4280030303101e1500c140940c3c003242d2028820b109155480a940c10009522410b0340d005584106140e440c2c0031040d000fa41200e00100e84c04402444504640e80650b00c6242c3c028140a20205400303445080082c2021124410002003201d1761b1000c2c8456140e500c220340e4181b0081c41c001a00c2c0d07440d400d0255010300326507134490381750092440c1d500910074911001c1807a94441d000810107695542c0d420307030b0780300030600d00000400d0500c0310820684071803000380381c611240a0400700300c0401e000c0e940b11030070056401401f107020b0440c0e8040c040c803000900b01383d0080c510200861505034040d5507580342607a01e5038100e2081030b2000c03041d80d040500301c0c1039500510740e41040d0a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 576946061 1250 576944811 576944873
    0xf0606030914070609030320060f071707020d0e030a0203030a18060e131d0633090c0702010c1b3809030705030a0803041e120507 57
    0x14001809080d82d40c0300039005941494400801c00508540c1191142d0f0f50341072031580d0903200c108107200101c8251130700c400d24519101041c4220340c407071981019000c1981ca04880702810500c01103140441c2140e440d0304111000b6000518503c103040c0c6400c04403a000d40300d00000e4a044070f0400000d405000c042a608082c40e040150010040980c1c04280503040d101c14044641c02d18840c00310768090142e2040356100252035000720b1800c01c0e0450082800440124800c0c50305d0810380e80700a400c07030491545450000f410240111850340c00400b0450010280c00241c0388100280c10560015030000e070740e204580c090341040400d00d9103d0040c002e00c98240c5055250b161140c860410b84498110034185c5500d0b40c0c01d481b6426030407880b03007c92200e03000c142d0305a041e00100412905482041e0000c555a5130030801d051200e032242c00e02e15a2441c0502c0e046004807020402549a415418112000600109420712035001545801a03c400882c00c1c4a2580b808002e0380e42c40f0b9881e0744040328 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 576947311 1250 576946061 576946067
    0x1002032712010f05041e03050d0207080405030604050d030e010e07170109051506030114010e070c020a050a0b0418050403020304060507080d02030a020c120316030e0f15011a04030b041101030f0606 86
    0x50701c614006c01c00c0302110120303da01e01480080c802c000070006681004000341d0800c89078003401ca02400766060608064866020a1400d4000d5a00742e445901901d034200d1116814041c40043d14180310081c0000340b03062071050340e103007018082c003c3d0203280d250140380c403041c00350b00030880f098000040300e0140b102040000b04020301562450b0003942028015011121b46400030350480d0440c804c40261660360714011502c0c801000012a40f207940b002000690381c1c0c03401a400d010709580840656503a1618022203074507076018240c6510181003104020100b500401941c048078a1810196581d00452a00010368868042120000f40c4080300b0302c1090409540500300d1170490781d04031014014102040c0c0900d0008645400d400001c2c4591468602c0c8240c02180e803d1108408642040380c01d000c3d00c50401510720050101100800300420029190070f803500c0125500d110310b00d01d0039080d51100000354000034005044600d00100e15030b40c2e17902c03e900c540040719160508215242d1590001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 576948561 1250 576947311 576947321
    0xa0e0c1f0c390501020a08030103020906120f01020d0509070305060705071505100602060603011a0f0303120a1413020a150c140102040510050405061209030c0303070e1002032712010f 80
    0x180300120102000300b00c135400050365441107078000000c5c42c05c40e8a142d081120040700100b8047e0442d520080b9032621540030440c945c4004d90b02d400158031882c00c1d41d5084225800144404e00c00d034410b9000304080350005c10f43c01d03000740692034800d40c4c9044074189254114480880079130010b24010400000760620b2084000740d078925030035110681c588c802014280c0303a040c8a901d1100345800401002c902d4901a8800e50001c060140c0707013030400c4010344249a507001c039140c0c5203a544507410a4000d034800703c070140e0311181002c6450004a40394020441130b00c000d000f0407119070758000c0c0303070701d00f09000d0402c2003c119841102900c0d00890101c4d0680030750000c1c0308441c01440d2000074086814060000d0310b080d074801401c00c81c200301100c03c1c042c014100240221780c0c140410081820685400d000070f501c40c0b9140e884021150140c0014406840e41b0384407a0740840d08140804458081c4403c4186084010300c0c42000891000b80b000800b000e00c8045041c0c9290718041404a100d507694200d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 576949811 1250 576948561 576948653
    0x50a0c030204060902030f01090f1107110a171002070c120516081b040b04021c020a021207020319020609041a04051608010b0f0706050a0e0c1f0c 64
    0x82030200741c0d40c442c401310980c0029152005003903241c60050100c0400c640c00700030100a455030205400101202c410441d900c056003d441620304e401348403019040803403445000300341083d03118600042031003400352582524001c81c004960005029030134011088c030824003804006543c0b0842c04511320303006554444644c0000c1d110b44403500c00041c0001c022640402d4004141c0a002203052030508000c001c0a0040c03c0f136a00c9582400000c80030410048042242e40c0003400040e521002c00d08043d24100540c500030301590020004040162408540b0100c0034401140e90a410110391001410314082d4190301138115103800c41d0381c3c040c0d58200072041400e0704d0030769080200b600c070000254820200d150307440001c101198010865510b400005010b5500300c400c0c003a00f0641039640312400e488054512000564031285000c0144d00288001c15101d201142e4407001000040c1400e041c0d2000040d5110622040b403040d2000d01014000300008020030044031080b00507140d00a4603200c80140c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 576951061 1250 576949811 576949819
    0x301060203092d09181207060506090105010c0204180b070302090f06030408031f090c110c2e020a020301151a1804020d2414030601050a050913050a0c0302 68
    0x2d40c11480382e41028481d1042e40c207094800010f501d1410070310108600c003404c131400c038000d5045001c1d03030b13004140411150309011000940d40d942d441d04203002651300107801148100e42c42801009a6a080041c00115136030548001c1040c865904c2c41d00703a1000322500103045a242401000002a8160b00400404400312124038191034800c0901c542800704440080075882c0420100d007840b64800840e8400308010000c00500a03201d4100710155030030820040c01242c8030190121900a0038403090314015001c1d200c0102c50181400403064807150b0700030712074440e84440e540d0f20072940700b171001d4030010703070090028041144512a03241c0148017a01c500c56140d10300c0c0c2000900000c0e190101c9024801207030b99522402c804104200c0254000ea00900a0a035113413200c4203040850103c0146d8868040d80c0a4091403a00340080090300440030303060f100760000001408030303070341d407a4448055450030b0340c41aa2035525841440000c120703012018000c1e04c01c0010303850400170f8040348401924402d075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 576952311 1250 576951061 576951079
    0xd0308090120030604052d15061305150d09080d050609132414070f0903050307060f060819051603021011011508061608040203060403050708040b030106020309 70
    0x1103030b206540310304000012502d00d003c10120307209240030740100c3c2c3c000c15240704034401440d15003810681d00f0944007924800c58620b0080201c807103d403810a605104040d51050720302003948400318902c20140c09150300c1500c9014090500703208520540d0460b0032440c10070481012a81884900b9400010300110f4480c20000020858141055043c0c041c0c0b80305940580741902c555075206031220f4621050088204d2000030000014240c0501654100303030320f000501e207080214004104041d003101d40c8041c4105039000b000010b00c00002c07610303015000344002901e0031105030390748050541035005525030311841c001c45400b02040120804400e20840444658001021100c6d2120f0b03064400030303500c030105125114107180a00c99501000c1c4228000290f00c40d41940403842801c0240c0006103168005410001546298200d604000380c45041c80e501e140341903400a42c1d2034100500040030040c0100d2030504100c8d01130306403000350000c0045a5285c1d0384501d002541e83e0010407005218401e05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 576953561 1250 576952311 576952331
    0x11030a170c0a1b050102190512060a050d06020d020405101805040b090a020c0a0804090c02210316020f03070f02210709090302030d0c02030423031f0b0d03080901 71
    0x200c01c41c2c004a51a07290703901c0c2040d40301c4083c0c2003031503d410190b43c655004c000280c0c0412044400c0c01918041d034a40a03200c56154a07152150782c00180801d005601d111000d212036602c145903105415070080000d80d883e0400e03000c1c10068080c590269400500b0042c044001640207000c0a440f91585005850540e0f035400800c01030320079038496a41c118040c4001b0401070030b040c1d0000c010302c2d481c60040342c448440c169294065648207034131065000703030f0b502035210310b040d4140040d101c100102008a000440e0031030410061740f1001c1c3c980c0540c81c0c1d10f24004030809000b4030500180e41800c80c1a2502d55100e4200942c000450b441c0c228451000311020010705015458142c90051000001301041c1d400d0840403001068481000e07001d500c814080d9170412519401400c003550701541c082c60710340340b91407000300d6003800083c1c0141c0d08881c0d500500065840000e82010700090056175070a1060380304507400000c0403e4950281c02181d92511102403680040743c1783e00030508007008011900d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 576954811 1250 576953561 576953581
    0x703170a0905060f0c0d1a0a180609050c03070c0309080a03051b1f18080d0903020c010f020c06031003060c0801061119020609120703380406090311030a17 68
    0xc100c5840350245c01c14070511542c0c0409900c15041035051505c802a0314904800090841c0090381c055041d00d0b115585096040c0e0090141500404480d9001e00c10703410f00b241c42603607500004000340b041000c03180c44402458443d4210f08018044242640e241c00500d04009020360312070b040a10090500e076507402062800010814a04d401c012051500f518105061a0240c10404800550740664541d1003002c10314007001400400e140e21400102200d8518000c0c1c1000ea4a0407220f051042049560106580101d1040219401110640d541e956101c100d103400b40201d820140159182c045404000d07a04100024140c81c682c2c1c982000041c1003001d0300307a495100b4041518203205010f0031600600780b07103000d4500d5200c000d200c80b00400040f140a2b00e41141680b0a07207003c03504c0005203040f48003050b03c002c2e0301880f501c42c408802401c0022425020f9001e000200403c2d620fa0400041c188104648031501100c0c0e41034071396840c0c20401c010140b45071141c0d104507403c0c90b24082034810f40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 576956061 1250 576954811 576954841
    0x8093706050705100b121002070b0a051003030e2707270e060f030a230703020609010c050a060c021006080309010c03110111041d130206030c0703170a090506 69
    0x150103001407180d0300d0030030748510180865a1069400c5171b02d00c0307903880010000f4003101c090800c000b4001a200e1606007818030183c40301030190b007011031900e41880081d1f40b405840006a03a094246440a4907075940410044e07103545c2c45141c9002e00c2e2800c1d00312040741a010803800303081c40c3e0313845004032140740700200c80d10880c010310f80c0f010301d01c244800c0001e0b182c07100151754020801004040005100e04c0401c0c00d00d00c20980460300112005c130324a17031500d2542503041d0103004100c0101100c1e821580456014811200c0e42414450f0f03031002d8508004040100148180d40a00107014000070407501941c0e40a550840720402c3c0d04096001c201410000240d0b00c1340d0b801650340c0005032001c2e4a05560280d904c2c0d0070000d26540310101ca943c51804c400040c001845680c180303514404040389800014607002e8aa203801c0d51058800d00003503070312041501e40289a881030180d4400e010710b03050744c030850242048030010f01544204a01d4030000e40c030840c0c0040c021400c0da903090b0741e45c03890984584 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 576957311 1250 576956061 576956063
    0x100509071416031101020a020610090209010c020405041103100b030d2606010215010f05010e060a0f0e0a050904050a11010813030309060e060a0b04060605090a03080937060507 77
    0x1030500038804803110340402d201106001c0e0030070f6220741400385402400d9034010401d01c400b681c00b103028804401100111031000701400c080445c00c0c41d00d808002403948000c100041e20442c0c898002c00c05200c5480346002044000030304403806d483c0035040712400380c9102d20002d84230380640e001100603603000302e401881403d01e0901d0522480004c1c140910146000b4107004c0c1148500c1c290200c0c0421700b410a54041c00c82d0480b0070700001e14040c00101002c862604440c0541030a000311003509400025642c07a94100f4204002200003070340114280c00015805240d1001c01d1400780700900001041002a842c0505906031628124400545000c10141c1c0c5080010981d80000b0780441d10a6100b0701c4c1c414807923103010400c01615003005180c00c00540700401180d5941900d104d0526052003003030005c2010781007140c00c0c01e41000000700b525045201c050480480024100080d55440184d4040085410111052003407007198143e000703802e0f10310707030002a103030508045107850144044d1800d01d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 576958561 1250 576957311 576957347
    0x216050d201203041103070e160f0f0807182603040b0a0e0d14160602071202060702040b06040e01090b060319090303060e0c0c190221030403080310050907 68
    0x418540035803100c5a91004000b602d414041c80c002251790b40c3c040c0007420052144150340c195505102c401d5500f0b150018001c00305112941407496451034100307042c1140390f51a4200140d103907907844410384041504025541000a50b004046011007401e003102005402100d40c1403d088a40c0201650300c0c810b502840842c0074003441030b540c1301403064010300c908403000340a4400440c01580c440040c030200f0720702c81da02c5070003100c2014402c8450325408002040c80e44010284586021100b0442c0c0007400741c082d016000009210056454503000034142c41c5029100603030300d5982c0c80c0c5618182c8001c0c00307125501400c10202400900d02001500c0c0101d5412042920361505280040c0007407103e0030045060580310b000000d240740750154140d1181c94400480750b900d081302c0c020181000207a11030074800c101208003440240c2c80d8915101480700f410aa130b0410203d42110061650103039900040807468008100301c62001d8030712040041311415612030350140c903000070554041203005108411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 576959811 1250 576958561 576958573
    0x1706030706092c040303020a021b0114072a030c0f060f03090204090c061806020114010317120a0b0111031c020306060403170306091806190216050d20 66
    0x41210342d0b42a2400303c1c686a1aa08400f8010030301c0450700340e000c80742600400c1d0f0108650b40b44070b405200701d41c20040c0004003a01c030b000c41c160002c0d001148070705600c138000c0c0003c1004810028000140c800185060030440034010f060325100903501c509020881e0302c0d040c0941d001600d0002c2070000001c0d5003807a201e19600d01150340c01100200785c0c0d1034069901075150200413000c42c40310a040c4001c0c1400d039036a1000503071100c040310b078408a1603000c40c0840e07250400c480e0101c0e0b4000d080c54150f03a030141a1505c2103400000010b0140564500c00c25403106100c00e114a103065907001c030400700c40c01e807078010000711a030020f5a103c1c0181d0b44043e5030002102941c022444460b4021503009000500302d9050039102e895031070b05080d0268506c524044000144041ca151541c840d0b50311841041c190710744400c1130503d550312401d010748401b21040a0b4481d03504454016010341c0e6054a00861a468105407400e00e103a5813480d20340c4600129060150301207840c41c40c01c010b0054a0710380c0d002061 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 576961061 1250 576959811 576959819
    0x3506060904060b0d0b0420132309060406061a0306040e07080d030207050f19080306150309030a030510061d1810060e030a0b0a0e0703060c170603070609 67
    0x10800d801842116219920803400009980300a0310b4800c0700e0040107a43c100740f6061810212461560082900e51010103005150340d0342d40b042050400c0005004c0800c030403a00e68004180031020306013070140100b00c0010002241130024016100d203001e0313807081c4245580e40c03000d4414201421100340002e00104005401400c0607084911200603a40488501e070380d5501e0240c0c10420100c49003400683c0024098080c84010480f40103410704100280c1507013044601c3d044661024a00000d00400c400303c0050001c0d030302c41c040701d048a400c980c5d540f507482c44c0c4245003d48941c040710805001c40c4c0340c8004603034102880864081500c9941d12200c2041120111506119815200d00d030f42c00300345500f4500b0190044920f0790700600f407024050303800030300308080030300301c0085820518000d40c8034050000c08515040c3c91f95400c00c1805d40e0006088510307101940c20b014083d007000c0c04440c101004d680c004c42e800700d030054141d150702181c0c0145860b410101602c0350351034411500020702052080c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 576962311 1250 576961061 576961069
    0x50c0c041a01050313080408010903021b0603040219030204060603051e0c0301060c080c0d36031101030902091501140c030706020f0c010e07030c0605092b020604350606 74
    0x160010701003110b00d1120401c0b59110140c071f51141d00864180c0e511891168200360b01042201c0b20002c5811509006205040c04104280001000a8407070b04002600210300015440ca02c80615000f034410b001d41030f21024040c002d001c082d209e45841c008180c210000c040e1f0348081d035a004151280e8154a56440d01d00100c40c6c000c00108180c0c1c0e60f4a0800c084043c0f050100b001c036000c000d6640b030b21920001c081c002204004049a0707485200d0103040c07885401130949030f8406003600c1d0300180300000310030740c00700490050240c40390082d0032250300320a000c011601c0f040c54881c812026620840d4030f961006540d0714a01441184183d40c1c2d00c28031070000025800d4000d040d041004140722070420b00480b03002400e583c3c500258a40a80110506000748610401c05101524480c10020302d4603c0000c08280e0031512482c0c0500c050403681d007180d0001201d02c0b51090071640080c42507444589421960794540400805800081c00a40c00e07849101e00d81400c0346440e20705040079203100d913660b030140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 576963561 1250 576962311 576962317
    0x5010303410c06040c03030212030c0d0c030b13090b090c090a0504050c060a080910091509050718020405090105090906070c080405090403110120090d1110050c0c041a0105 75
    0x442820308040c000289030502c01c10402d80728501444190a10701d185040c0a41042518500740c800701408008100d840800801281c211281c145400a40c0d40c9946000320000c0900100403640681c02070035960304942c2d40e810640301503005070844031030750705c2e4802d1076542c5040b8040400c4e0091090b0740010000c1081d94090759009020b00141c500c01c06809002900c5544a090001c0c0441d131600103001100c44100103d007420194104208049400c0d43c8a0b010f41c010f81812866082d81c03540284010028180030b03050003400800d02c030040b000c80b002c102070080e402502902d400b82c11000000a0a440d0404520380240c018a024080b20342302c0620880301c0d140c0511065032030714420000003810341c81e640320403440f40c1d000ba540e0f4500714034030b044503900b9164110354084101903405c0b0010707070003031028040f240044000c480c44400003041d407400008a804805030030703600050b1002e00007450b0340c02400404440c8007e8098420340c03003401d0204405c0344c0403c2c0f190307500c0d280d008401203d10750207a001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 576964811 1250 576963561 576963677
    0x709061404090608031b061504020717190305060928020405090a0501091805060a0b040b12030306190e07080402060d0606021f1b2a0605010303 63
    0x282803400c0d407104942025102e40740d04c610201d510002d208400108055400460b121080015200d2400c100038480c200414030034005201d0740d07000805101300080f08035080c58a40c50303244943c1d00c0361940000103221108411036100800d007800002350907464105030151090001034802088443e02e891800710364020100c9a19000342e080001040035a60441428131440604c2030106441d81800e00400c19260f03000400b56014019445250000300081041c50340304a4078003000030a00384013000580a007080076601500680c40800c404124107011005512412050b10456103400000800c0c11101045208140d44101c10002007002144520744464120740000e00c0c2c07034180b07111a800b040842d10706a120b24007507400300444881c0381000400003800c00d034009500300040384201e00700c1d041c08043c1c002c241c0d04004c90b007030110100410070711282008201440c11005101c041c3c1c9040001004203000580102d03400069928491114854940410184940b0a144603244000d80341c141d8401e082 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 576966061 1250 576964811 576964847
    0x1608070c09063209040b0915040f030f08070c030c03030605040f0b0f0117310c0f090c3906020d0c0e18060a09020307120b0108070906 59
    0x3100040702011405654041c080040c0b60803150b07408904841840c01d40e41036050000103189000464a5a4601041d64032a800c601d00401a540300010b280c2029040c0709521540d582c09828401400441100241018829240c00701d40c0224000c05440400040f10303040000b40e0501e401c140000e1042d5040007400d40f107400c001c2001a150380001d0251522080c8541c4d0b0140d03034a604890364a00060400e610742ea003801c01100b000303031101c0d44e076403131800050040b030030980c21740030207030f50400341151022007080b00d8451008824003510700b6020759a42071240c04000712184c8008624140240300310a8101420345454440701860b041070106072070208202c002c09160800800d640d507510011a000d40c620421005a4440c51940b4040072214103880c108108a01c44009c01042e0f03c031010b444a2098400c0e00704200d40d5201000243e100d18150880d8907064000310901c02410b410451145003028644404d100140c1c83c54011504240704440c0d1400003002c03048200000b50040c4148003141080312 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 576967311 1250 576966061 576966083
    0x16030203090a061211210907120305040f0b041d0702010f0c050a0305180d0507050109060204120308060d030e010c0c0b07051f0207080403080918011410020102160807 73
    0x180000d40c2c01d5071940e0140000c500740c20340742c91400701c4c90320458901d0300b01d64944c2400d0a800c869a4101d024540c4000050925040089504c18070100320100003440c3c001d8031030122510624000380b4981080c418087e500400c110080f81c80f611540a075016030310b038000d00403017944e8034070455612444040c2000003955030307480c1c500c905d07078006005e100c0c0c84100c0d0ba124150748076540c8900a04441009241000c40e0034054042480c00700003241d1038a0002c55880d1240d00c4d00e04508000b40180001c000007800d8510010340051036000c958080e00107180680c0761010290b60712020b00c020b00c04000c10040010f0806031100e0141d6002b2080306a40078001c1055a11460b141c074990341710766102c580262456481002840508410614807202441c4000010750402e01a507440d034101d80210b02004040c8000856119099224200000ea400e5411700540846580d18005090b44610f50a54a80605003034610846218014001c445104071000413071000c05a10f0340301c19091b0341214000b01c0f208070508c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 576968561 1250 576967311 576967327
    0xb0304022806020304140f0319031b0c030c06030e0c0108090a02040f02120105030a150c030e06070804050c03010902180705190206100909080313060b130b03070503070b16030203 78
    0x601c1e0200500b400350011940d650410f600050620f03244000648600b900700c007141c2c2c80e901e000c51034600c0380301e00840d039540d43c02040c41c041d0b45c0621000d040c5031540c505215074400380218200074000300d0380190640c40c452034540c1000c400f0f03942c1c1103407144055031100c400d42c4469440f40400540c82511002a510b0048860b4005420360b8107401c4000c1401d40c000c03c05100890104258500601040380102600b6405948946078111020084c20f041c0e960f480306400b80780d0080e0050540d6401d40000d0f15032074600183c002d80b14501c00d560a5036140300d0043c800159081c1481004c100c1ca0300101810740302c2030300072036804080000070304220400000b0b008482d140c4c40b8180141600c911550060440d91070b0029040903041d11907804488414203050104001c20500c0c022244c000c604c03051415800806e60a110014010040c40350f170300000d83c01981e8915003803943c011717100c02500b242034400702551070007015581c5805010b1002e1164040180301103033030250051202080c42401074038281104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 576969811 1250 576968561 576968629
    0x5160f051c020a170901090308090d06090f03090b09030304031112240f2e030203030c070504050609100612181103060f010b040b0c0c04050a020715060b030402 70
    0x929144000b59000e00406010406141445460314044015071030801900b40b000030302642140c800a4446280091048420303100d9a044082c0307290002c50034450302c0032034982448003604402c0f013540020800f400100301289441d0485074281c00040041d03007480e0071a1117081d1458060b440761640301003055086d245d601024003642c5800080551500070b600740e002500882000001c1c400a404400c1c20100301c0200c0405030b44d1600e15801c800c0440c42031050703015070303100100c0580020b503242c80045258941c41400083c2401a160259424046a00c860701401001c85080c3c80380414051000c0c01032125a02c141103003403903075180c044c000c903c10000d07a0105424a0758542c0039201c1103500a43d01806040c1040b00030f4224402c0c840019483d0315086a401c424000ca0041029031100041d00e2030851008110144c40204020801c00080c00d0060355a0000c0d40b2024040390582c40f114110000040b00d4802d12045a00d0b0b0034509107160f075182d0070000c20b143d4011140c1c016403110602c0004400d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 576971061 1250 576969811 576969853
    0x6130314010c08010e0903070f0201200717010e0d03110f03130605220b0702070f0806100509040f030503190516110c061902010204050d0503041505160f05 68
    0x500000030b040200c2c00c07001859614140c1013045411040300031b11181d810000112003103243c000300400008840e030b10040307a08014003200b034600003070035070101255420081803000c00c40e040c040300035060320180122207007a01e12159805040344c1054408420b141e0103500b10038842c240a200c3c1a2402103000d0310f424050304280ca03c01500da0002503120200002841403540100341c001a120f05602040790030030081c0303071800004185441c3e850210344814001c2121b0300240104001c007000c3c0700d13214000c4580c0d071102241c21616035040e0203400034650900340150350240da0001070488910000d41c40580f02d59101401d096100020310201124461071449032074003510070711040d920304901e4900d005200420b00300e84484190465219442aa5229070407034004141111800b1008490030406900901030750f4480c1e85c020a4030f5051004008020009100780c601030340843d0702050940c00129290302400304210401172500848001017141c41140001d103c1c8101e045a820700c284d4040365090b15 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 576972311 1250 576971061 576971093
    0x10b031b0f0306010201050a06030506040f0813080109170c06010603090f020405010e0703050a29030109170403141b010c050c031002040e0c0a0c14010b0904030527060405061303 78
    0x107802000344401c030740e0f0a0080f10341082a040f814840d4505584446803280340161000749007201d10f00001007046012004d8465400c00c88100c0d92804e039550641030f0103040d03160001c461103030004505200c0303081000156040b80c0c6a03e40101926802c0c000141c0082030f880b602618540102240d5100594a0340a414045d004903602805141008080034090ba1030140c603501402d414038911300d82c240d41d0402c1004d074005002c2118101c20015001007801400c2040e000f078100400e03800d1001500070400c00030030403248194070b00f501c2c40902c2c490181c0c0f51a104207046508102e161450004d075881560701d050301d2030142041e81d504034200000207140112840c0d0000d40340780c01080c1004590150b04c605944010342e9271030381d07140040c0050014151840003030300411820b040030b01903e4800d000d500030034402c04080c0c244100e500b4141405070158020b900120006006500030800d002103d0017502000240640414180b500b401c081061640000c511111030078450540040403e5003501d03854801c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 576973561 1250 576972311 576972337
    0x3030f030402120f16080d0903050c060a180e06011b030936060810020c070e090a060f14091507110c04110c1603032f0a06050a0c1403010b031b 63
    0x15850f0607800c03407d194802c1c00000610144103020400301e100800e80201d02402204c2e81e994580c00400141da5281010004550307c104d00000410800d460f21003250290b03c090306c501840a001f400c1361000d6000c03070680100007404c5507000b0840d4030301d2035181c140359100c0c03040c1e032002c03090302c500038035820b15196500081c2a58580d282080850b90600001d2501003803018154605542c1107403859540c40a8801c030340a003a0145c0014407401d0051080341e81c0c2c5a88550b091084580409100000d0000c4030b650055412500c00071031100c1e1400583d81a580a440c2e1030a00303180e40c1c141e001d44801c101007a154245014a8403050740c1c2e40e942e40304880128140c10a40c0d030b01c1c1d0142e0359000f0724010305040c140e918201c1c0040c0600110390800070700481524004a00450b0300320001d024614041c4600301c07c1080e21036003070050104291a0483c40c4640d45890080000d0342d680d01c400c8400700c411400790100c00c0803c00050011580c604011540015a0b000c1c1a0300d04001c0214036401c0d034041e210510103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 576974811 1250 576973561 576973603
    0x50d030b060d0e0c0f012a020a050a0801060e0105040507020d0f051b070801050703020a021002090616030c0209060102010c0c02091503070b030a1a01090b0d200405010e03030f030402120f 82
    0x502c3c0f90918281104001c20302c1c0c0303000180320500c01c0c4420b50792241c40c107c031900340114030032007107580f820750039000b600c03014000c0119543d891451501810441c050f03821340342c4c140c900104490815109440c41400c0756401840c01011341801a948483c0e00c035803260804c0810048000e1401c04804084d43e081300180040100c1490303c00e11600b1248090326600416004008108600d0380c0001c1244480341c101500503503902e8003034009803c0703209040d42c0c40c440305045000300d0145508240c1c400ea25030f009461200b02c1e9a00c101c0128221500420707080c1c04503854201c5a03015042400d00180e00640443c2c1c1a55000c0d0f500c0d00103454142e01358400040c4040000c104201c0c0d42c005e000b030401c44008030000100e0305072003d0010b00b44041e00d01402542d050082141c031006407194000c11051000d000d02c1e6140e280d03500b40c508000340d00034001c0ca4086060024100304a0600000b142d03100c950301402d0340d0550b142d5a00b00103c01072841c0800416102d03a90507000004070501c040014516618098a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 576976061 1250 576974811 576974833
    0x6050114131b08090a0c060503041a0601050d1109041803020708070f06030203090c0a06020c0328140a080c0115060c030c080c160806071704050d030b060d0e 69
    0xc001d0030928403035900e03035003460244205040c9990381c0e5180c81c0480e083c4040c40c0d03030b03910340c05900d03003500f210000c1c00e0316204000028146810100442c0558042d81094000e80f240070b91041891400351107140c0010002c103e242e01e043d0f0158000c01d58605503070110703481c00c403421001405546d48000c4015000d5920000c210416404100c002c0081c90100040d1001a140c000c444001c108a40301b140d0602d07030004002902580c0a2140d1400c00400405901c00241c9440c03000f96540c0c1d0000c4128081d205100824a031080b05001ca46e9218002c0e1281d49003440d103695565004080b0101300c1040d621480700034038005801240686152010310300001440c0c0c40c14038900114134500d03808481441b09803641c1c400402c0d8480c00302d814081d082100c183d0f40f61003000000d440c08502c404103a03400c21010702c0c042202030010901c0b41c040c40407603450380e010100403416a0b250f103d041e40e00826036804540c1c0c0a2503140650015102000700510b014100b003100c03541041600c0c595502d1014642002020344 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 576977311 1250 576976061 576976069
    0x4020d0e0606042d09081603020d030f2c03120703090203010b10021506030c0a0b0705011a011e02010f060305011401080d05070b0c0c01020c10111e0307090306050114 73
    0x14029440013042e8290407072104901d0000f803c000d0341c000501c0e903d40b4040300a1046080848605c0140384108240d500c505040085d110f0300e500101c0c1c00020305254202000b6a018007401600e40c0c02c0091030000c020030046284007001c00e080d18410180428880b0701009038140481600c12080b588000c41d445c40f0728410542187d541d22403142c0301e041e071400900101f0340d00064074900321284d0100c00d11503440b400f00180c5000102040c266201900b0364001c01d00880c41c0000c0d20005124200a0182407220781c0e0703940700303c0c0c1d500d01c02d1400519201c1e0100761200d801844ea07000c0c2081400000f48184902049000b81c4803641c0043d00d50f60b4481e040001e4120030300b1a2140100a0200503106040006c500101148500240a86800c001a0115800e2030075101100d20284504c1c0085590381e20440c10592034000005085d4a01460300b58107807245200e400c2243d4909012407080220b04540f403440002d6a0806014030302004098040400014030038840c00c2e0180442100e0303800304400d010100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 576978417 1106 576977311 576977321
    0x2040b1b0f031605071415030c040801050a0606080708010e0115090b2802030901120c0c060f0510060e03150603190308060f011e080604020d0e060604 66
    0x51949200c1c010075003262403203001076905866a9203941090482d25406e10380d00221300d4549001000784590095512110001d5840e061a4030b845583c1d084881c1112400c2d000f03a0744510070301c41c0070741240d80700780d0004071032420202d00d60400a01214110042c480c0440740081041c0840030140203d070290b002d0500b0302c0c031080e00c904c0e08a03c202aa511000e00001a41c0e0981c008074007500d01c0481110300c550812703110074440c078001d10303444001013000e007041100f04100d1148035030000c0ca07a4080c00e44c04207981d200100f181e007044004103100100581c403040509c140041115610323240461800b4498003103a01031860381c0d54010210341050640007583e034583c13449811040415400040302e43c01450242e602c400380301050b50054600a644080940c02c2505141d401c011591040508650000010780050700340410580c01005a50645568a115800c81d00400281c1c5c101407180d = true := by decide +kernel

theorem cover : BRFrame.Cov 576798561 576978417 := by
  have h0 := BRFrame.cov_init 576798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 576798561 ≤ n) (h2 : n < 576978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
