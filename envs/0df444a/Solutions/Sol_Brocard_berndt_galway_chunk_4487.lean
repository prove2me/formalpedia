-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4487
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:46:50.321725+00:00
-- url     : https://prove2.me/submissions/ceeab976-89f9-496c-9437-a3704fdc2694

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 806834532 ≤ n < 807014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 806835782 1250 806834532 806834593
    0x405150c1603150b061308030c070506130303210203040f170f1209031303050a0b0112080708130f0f0603050906010f18060b1308060a0e0c01030b03 65
    0x903030300c41000d5007080510101560040400c03081d600d141c1d80d42c51242412450480301c0c0380c0761030720203040c3e80f592000e60b140c003981d403805d8041a0b9680ca01468032588a103010400074084c4d203001242905041048036100f05c0c5112054401d1440e545040f03a41c0d00c014001b00f00702403070400400c42180b4440c0051800f0700d01905440b0841650b0303107000c4005d90059203020000c0a800d000800c109041c94040d02e5034841c040614945a54a086e54079095106000014103041000b0401206200c030019030143d00740e1049401511076602e811a04051150415000b492150100100c000140e8024098440d45110706001c02c48035440303c1d01412804000d8207d014082c1d032208040200940c14059640c000c43c0081c0900b40f6541065240b03c91225140188440030200080040904d84a90700c1107000307242003003949456660101103201413400500c14003c8a11405001c00c00307048951284858a0800a004085282d10b0340019409081e28100955050180c2a5030341902815803000009d20007a00c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 806837032 1250 806835782 806835787
    0x11040e0105030606011d040e030403080d0b10050f0a1d09090102030714071101180e070207051206130b0a021c0912020706020703060207230708190b011505040515 71
    0x1d042c10b14007040141941c0c1005202d50f660302601080d100c6010043d02c1c1903401050641521420728512721541e1300050152070005040f00341e102156200d504030b600110f88512040d40c00e1101101c160159404c1070014500800c450000a4000c01d8010241809855400300501007e800105416011240c42c041d41c0d400008010310f0b9580000003240c0c11800c507980b603080c01c0707854072024860415030070702d18103200131000f4040710361902c07905c00070003042507010a070400d16081100035140c2d13102e441920b0285540300700b035118529003c40c071a031090a00e950f40c1c440f201c0303264442001400c2d0280542354810ba0803c2402a08180007000a41c0031140c0c40010aa45181e85003401c1414500012981150860b82c02482208c2d4003069200c1101d17003201025031200624140b500c00646207a0050000138408a60145408030129003801124030b004240c0d0319016289803140c002c14890351005000d000c0d00d0740140030700ca550b84500120401d0903c1e0040c2480d445901060410f429000761a403250400b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 806838282 1250 806837032 806837039
    0xb040e100b0103021c0c14040324050903090f0f030d0305100506030103020d11010e09161403010b09060d2003040b0a18060c03200c010b040c0e090a11040e01 69
    0xe5001d991596003080c64110325084c5d0102030a45900d8212003180101c54441c855140000d10900000300c54101e2420789981d601c1c6d0381d1800481421103120028195501c0070401d1903e03040a00c25607100c0c00b1084055841c0c10b403010200a9000110200c1c0c0d0b07404002175850b211a40c03000c001164a4032220344001031203081121aa410300b11107035000600c0780380308200500068aa40200c880e41c1130340804030384002c40c60640161886c1000b52801c40e007105150017000551400c0e0100d101e9072500d99190000200050016400c95100074000e8803c00002002510294108000200311119110760001009224110341c44004400b504c00b2000c4c4400c007100748000e10200200058201030364071010850b051080b82402c080c5042c110303015109a5071b07401d4503003085000b5040003550395404440b80c081c0464001c8a080703540c0000c40e0040f410b603e08003030014142040d100d00154102c0c80d8584105170600300b0b04116920000400d4000d540b500d80310040203511a40025002a20402c01d910416605 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 806839532 1250 806838282 806838313
    0x51e0609030f04121a070e130c20010f0f02090109080c030601030605090c090a0c0e030a080d050702030c100605040b040515060f250605090a0b07120b040e 68
    0x90002003181c0c00401140603205200c4088804455a980544c41d450500e1309044402c3c200644e0000c5450f040b50040081d0254005484410f0300f10449480e0306116095821000f122030050124000c074a8034680c400d80c0645c004900c541c132001182c00843d12259035000341040d604641c1d0031420b8660007041d4203180f50780150008000e401810010b20301c41f02a1000640d442c1d406110140109940e10041004503009200480c440c51000c0c003400940d0030700020682c02800041108070006003644003e00d03040c0b40100c2c442c40300c20b401400310743c2000c80d1402c5600c000d0801078807003405d5100400031000b000c1d03410300495989010740c000c00a20749182009000030344038103040303441c440c5181c0710412002002041e840c651044080c2c44d07154450041c4900e1501510900848042500d078084811310700c4c00c00800e1900e006ea02c140403e010307980710b0344145640d82400c14030090807101d410b40041d4482d440f416085003460311901000c12a505814041401c80380b00703030740f200380030380240f5030040f40d440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 806840782 1250 806839532 806839543
    0x60d0602070b0105011709120730030b220c0504080703050d08013003050405040f2019031503021203030709050109080c0d0501021e0a021b09010e090a051e 68
    0x541068800b00306203071101e003248d01c460005078020341c02040811008203114524400b124011422000160307129078650100354940b40c02c1400d000024100400000c00e8240103071800b002c02d1010b501c03001100d045a504002400040d42e52004215081c000040c0c00941000000011802400908079180740d504008000810507000512104558040140301c42100000c59202030303880414004102d0051504a03001d104540c05a54060304108404001100c6c0c0e90001c44030701c40e010020300d40c14140401d41440c81c003440004402083d00804010200c80c081c0e00582011045038240780581f40cac6a60025800c900c01000c402003940c008010080c0349078000303202401400007400c4c00b1040a1500348805d964400216a5901440201c610041040340940549091100c000d1016400f254141008419604841203200041c402e02d02205d045010100200e0070a0102920b5070711607a080a040c040e1a01010301141d03990301c2000c03003101c00b14005010b0f41079142d104144107800b00003804001807524 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 806842032 1250 806840782 806840807
    0x3062a0301060903081e030a0e0f0a0b0106050318060c03061212040b0c011b02150f0c04120201110a0c08010606080108300a08071403130b060d0602070b010501 70
    0x80404000501500b508a52110120f80e840707170506a8410020644400104422103003005075400802400031420403030300811001d6045504465404440c03140c02540e80102c1c2c0f80190400c0300480040c000c051080d0010360340003003040906e1801e070b040c81d0a40c0c0e1501c14129100c0e10f40103404028042980740c55011035450800d0741c00201002c14086140030450300c42c52241c6c19225030001250b000404c002e4020121140540d0881455100b8850000c1c0d150702c800400d00c3d551603d400005190a28151101d43c050300303107045a5800d0905015000f00d10034801d0380180e052010031005090b0406042002150051081f803c903d4090f1400580b203081d1200e581251050000010062001c02ca001428140c40d80e940040407170781060b04800d200003610110a9541c060314000b0714001c0c442d8102d01582d01904695036244401d800c070401c001c4090000741d4441c03c0c0403200310b04403400324445607a004c0d00120001d040800c0c098081c1c2c0c4400882c1d0040720708640030740c0306e43e004201542e049441f51810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 806843282 1250 806842032 806842111
    0x20a0b03060102062e080601030210140403020103110708030a0605130b061c0e0304171b0d060b0102120d0f11030709211a151c0209060f0306 62
    0x25800d0220000c4d480316002014662034589a0064024030740340f203100e0211780003191902030340310f64996245a49030042400164014001c4000300164248580c1e889004044282d4040b810982140c1c0114041d02080c074040031120020b11031040802d02440082d4099202c5003030016a0758980350501c50b251822220303851103940b81008080031601c40701d08442d001c450410080f003240c04041c500c030004002d0306855a03054070001c40d002c58550203240f4540c0c00a0040030480e00d00d0307464945030b101b014040f9540c05030000d00000101000640740d810424254905005442c01908203c1c4e588a41d500165034203106140c443c010f4460102e21841400d123070a04900b8894550704d88840b019280b440070382b05800c00d00944507040344507030f12048070190384c059110340107a1041154560341d0720500c10035907803030700d0a1101c885128030a19203821400480c144043c0c440c0904001502040a0f8041c0244159002074003094083c80d00d030303401d00c042807080c641000610700c00c58140003c0718003801a40012142d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 806844532 1250 806843282 806843287
    0x1d0f0c07020109170a060b100203070f080408060106020609070509041a0a060e07020705090f06092205060c0a030c0c210306030210020f0607090e041103011d07060f08040c060302090a0f0f03020a0b 86
    0x203149a01000329031105404c02703031000e800d40c0c1c28900341e3700502c90ba612142e51405550000b24607143d002c5001b900850790501210307800c0b070311352040200100d41038030014082b40d0711107206241d000e0a48a001c0e8840089480051041e9681d0740e0766844540c1140c0030300058101d040c05001514003c51402d40104404811000e1440e040003c02d00600c40540403085580601c203c0012a140c07485014180d594020207031707042810543c2d031100054216544420119082401d440691032081c48009411500b20b2201c4031080c585103465040701c94250030301d00c201911a1004405a12070010800718002c4942c000d02c01411000710950600501800140401c4403030380301003200001ea011040d80241c0c003c0102e2021001c0351000a0061180909003e00b684590214548200d40481c846c011550075483d1038140a5295400310b8500000b180c005006d47d0240b1824440f203403081e80501188030000c0e20805007542c0312403d0039944020f0b9803200200c1c41d6403640030710850410512400c020b00720086940d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 806845782 1250 806844532 806844559
    0x3607060203040807050402281e1d19030813030b0c04181112090a110f01121a0a0306060503191109040204060506131d0f0c07020109170a060b 62
    0x15290501303440b4140c4129008034000307001c3e12096041004d100281072a0b9103405000c218050200d490349140d08001c109150300d41d940c8940244e0007200034042d10f008040e4102038901c00c0041c040c03a0b4942000c010a9204404000a140b12004000c00d4681d01301001110740b9501d800e600c01d0200812105407044140700070010f20810200394140c1c0340030031a0214041031061809581d901444007110512240003080c0241d01d040800e044400d10300500c90030030340c1c9420380c0c02d0010101c64091107600042c000c40540c4051185a40703c00704a00d0000c0840d05410440000558884001e070010355041d40d50b03060801c180d2030f003001b5a260f40840070b49440054200341d10766035015481c0c840d8807030040c1c0394800000c1c11075423158019000352000400d66074448516100e00f2216040c0e60044d8000701c0c20a24000b250804d140709810700c40c000d0210403100c5690350720220129030f00b00c0c08049052105054009c0f94000100201d04107101091000346032045c000d080800540d00103400403801182c0031030004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 806847032 1250 806845782 806845799
    0x15071515060305040501020910120f060f1205120a020d2d03020c0703080d0c0305101a1e16110d12140d020316140906030609360706020304 61
    0x110884500d07082c00101540d860030700354060311622203a150312500c0400480707941c0d508003000d50b51032074240c101003080c0d02007200d925040340d4040c059245c0700c5030700450400a4054650688150b90320500940ba55408500d201944030713004500e11704096000840ea00302c8595010070400150582c0d056400410110080e41c60405d1006400f00c800b05500040d0039443c60608104d108003c3da489121036a455540c05031180003061080300403000a800c1030081080300c1c01030032200342070354a2a20505820100c01d04c02260b10380c0711071114100c03085c1c2014006a1a400b41c0c000d400b41200c420400702d2251186c1c5031551b0000d51441202c0d10950f864111000450307021a01c0c50741d41140d5040504904000c2c550602003070080394001104140008100110442c0d04100c90fa480300054480180c0040c0c000e4569080f402a8012181c10520920004400e0303d080350503e908800030414840003e441c2d51008150195081440440c84001c0210312100c00002c00ca0320740180058409941005d0901c402c6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 806848282 1250 806847032 806847071
    0x30617032b1d0102030a0c0203040f0b071b03060b3f15150906030307031b11062701030c02060612031308010621020319060b150715 58
    0x1524a60405095200303081e0340540d000b00351071a200c5058504000e5041c010030701139032003120002c529908100c801d48286000006441c10384900301072080d05242401400381d0544c01458040d00d1112020305400016410442241d0107140200e40118040d58600b0500c10032031241c0e1554040002c41c0040e10b00649045015034003400040314940600c40c410142c0686072a0420344140911180c81f000d1140180c01c81c0e401500078181940d005449944190816403070380150030019000c1000001ca040364038103100c98420065119000303900c0c10203501c0f004502283c20a040c0c82d22200c090400710103801a0082400001070000d00c1d00740b00140340c041000b51140c0f0050480e6000d1345a072440d08000c0300c01481034528060a80ca180c1c10300541da440c00d42e020f0b000f11310030078504503032001c80e070242d00140052040c10b03036401400504004007200070f644000075003100b0589146641784000ea60560380d001101f1194014503d4054880b0f60600f00803140c3c0740c041040300d100c10300d00b88800c0e51010030481d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 806849532 1250 806848282 806848327
    0x60f0b0604180c020f12040e010611060705090a120302030304051006050303040e0606071b0e011508160c050105130209180604121b32100902030c1003061703 69
    0x4020501102c03440d400c4c1d00d0816050590460350154201404400e55558058030880b11881c0c1c1d8400b007a41c3e101007e07500b6120b400c0c210503d54114800003040c0a00030001890b10b00710103002c480c07001e941c7e007a1205c0340048000040700160000014401440020012403400980b540002c00c8107a1a02000982d2407017180304074a42c01e4a000009405a42c560301a580519001815814800401410401c45e9289070140302102c10009001043c2514580702021580e0350a895240d46502e542010b4811102c9001c003840070411030503a40c000140c8203001c0e65020b8203c10310b6044140600344104918144010302d07028000f0340144040b40c80800c002062501301d9002600501049038616088038640b801c19140d0390b02c03881e502140420403401e81001d803803030703224555a544040b0018190710021801a0810704541e4056a04214040680c0e4080103505200030110350341b0fa103846001c9002c80c07074082c041d00c0200e41c0d01c0b2000c01901004030012030410300403d001d9480c004200010800340e40c3d401c00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 806850782 1250 806849532 806849579
    0xb1509010e03031b070302120c03030a082503060501090803120c130b03070e10021605100201060f09050403030b01020303040507090f020409090f0507051207030825060f0b0604 77
    0x5460341c2d10b0500403100038445a0350810329140b2040710580d9148000c0c4012405449210034018480f04003003020001d10070020003862510421007400c444155019102062884001d1000c1a4806141130480124151a24042041480c090014121000550100429800800088011914003c2d060f9480315852181e907445541011000c010240700c0d4000c800010130000902c0360b225005040c08492070400ca07003903811084002402c0383c41e04091800c1a0070f1b26010710081c8400c0ca48090308400708103c3d44000100b680e550310b48014560107951007031a80c2c540e51010b2005240d41406083d5844c102800250300e141002c0d41c40e242c6c0c0d0080d600c40c1ca040c19541b0382c1503e0071004950100d81c020301440c40180b0043c0a141080700741090008011203491040e1b85c8002402c0c14100c0170140c81150020181841601d1915030030f48a030301080c0800f00b805048100c882c405e6000218002c003490082500045104020500b201100e015000741440b6040a1204018070600041240e10340090748 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 806852032 1250 806850782 806850797
    0x1051c061d06040501060302071a07020c03071202130c051210050405010e0618011404090501060e04030f092102041a03010218090a02090f010507030216090f0b150901 73
    0x28040010161500401a040c2081e8850880c4810341c5541da401107400b1942084140d82c0c459041d002c030710820200078055114614051800035504840301d511080f5401540c0d1101c8100c80000d0902c4132581042040d051040c04070030560404041d442c0750300c03440c480c040058640d558005403583c001c5106440c0c0a07401070000414260f1004941e400401000d81700784a1035841d260304110b00c050440d22035005901103040c0850480700c1900460499020805201560400b90306000183c40b503090151115929114002070301c2802588080c42107009584d8448003a141500080083c42a5440100c03840d4400d4a0740300842c04e002071005400e541250b0004840c03210f0b0045440c1011a060314960652000c1a102d01c41c540100709003034103000c122125401581c131001c5420490040c0313410260014a40c0c41c08078003950040009180041c0280100c3d282c40f1a07948030203e4006058203d000502d8035250307a480308003240e0103070941a0104645500b0f51030f031290b00d400400d00030952605c2c1000b400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 806853282 1250 806852032 806852077
    0xe090604230105040b060108090c06030a09030509060d02041d0906010e1315051b070b010911040f03030c2001020a0210051303050a0b06090c040306110c030304050f1207020105 77
    0xd26140c000c000094100900c4249013904100c41d40e20000c8a015010a00c100300140c0c0040000c1150039445900405150450719554040d600504180e02d04070305001080001c61096981d407805418006507070000960360300c1c10240c8424008805c0b0040c1c9503043c0890061008a100c041031680c1902c6004249880903540c128010a05050458010303059120907507107080d00c00c00d19080b841c400c40d00140d107161040903e40d80c0600c2ea00c985840030b130080c400c210041c4130311402ca80103c41d5440443c40f10310b081070340712094a120b2000d41e038403c5020032010701c040400c025031140c3d48030109918800080c100516403002039150248400002e2086802e03d1941c1d00146c0102c0558108500c0c0343c51207144030f41c5038540710f0b9444170008001c0c0c9542e10b40b0b0000460301c0c90001801c0b80300b540002081030401d840e5560300c0018203000310200c0009903060180310460b2104002961085000b40c005001d0000340b01c441c0c1e810422182c89880d40320108100020160360008112003d20101240d1006a941c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 806854532 1250 806853282 806853323
    0x12170901030f0c1d0a060519090305060f150609180c040801090c03060e0304080d12141e0603120909090a05031c0b030607090302040e1e0d090e090604 66
    0x10b0342c070350462a1803820314041052944100100121075580104030003412504040281040040c460100000c00810210303500301e0005080300c0c0000003d050900110b0f80300e40e2494140300b41100c2d0084200d07605010032030402c0301b0400f1200c10142c29500c0518220800d00440c0702c8414201440501c001a400882d01d0f0003581400c850040151400030042c0c0d21316450011401e01e90b9200548900d402c0021030070b080e035004030407071342199642d5005040b04910f8071800d6455030b085668a40046540b44c000d03000c040445882a4840c43e10000c0600416000c001300c0240400041e0469000364070450904070782b05182c204480400c40122110882070ba94883c03520715010078004010807500020031301481415403d03180c2c42d4580400c82013172041280703c50a040da60882190390310000740442d0800c0025081075400b098032101900140c980071261030305c6180315880c445040c41741584c0007040e8808500d41c00f840c000080d000022440b6000d051090041d07a4071107002d40060710b040384d081003c01d030101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 806855782 1250 806854532 806854541
    0x1603080a0e100e1c02150c100501050a051302040905010b220501050f1c020a0c0201020601090b030a0f030318030e13091115070516030201140309060c0a032a03061217090103 76
    0x7940100481d0b4a80480d0b880403200347c1005035501510720403022042c6080d080b41c024541a00c5010744908440342c1707000d003080507500b5800007a0170700507802c000c007042200300c1d0302070740d03018112420403103540b00d085058061260451600d0380c84000c100c4082400240c1e13204080b1051055807070034494544012507542621035070190b005800d418400a500f071902034000c114080440c0c001d809564150b81d0b9070001c2c800740c2d20740c0d83d5800d526400c007220305000a0349424030800054040e01c1c00041021559603501960350601600340c000c200c42c0200304031546056210010f0740366004a040c001d0b080140d80c0e040c403082c000c041d410702c11002d019810203070780154001e955043d600b06040700c4045002117000380d00e07004113001c00d81c00501c990741c0315007940341d4041c1103e001c0d2001000405107607542140103007168004460500c10151030f45410300b088000e1440c0161010350038240100990003000014080b1002a0301c15041d8070310441c01c140208400701c21102c076824810072801d0b035902401c1c004800030b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 806857032 1250 806855782 806855839
    0x405070b0c0f0a05060a240303030c0512040c05150a050f09060f04060903230c040905071d0a0b09040f0f0204020702090a0b010807031802121603080a0e100e 69
    0x2803140c3c08901091003400541c0600880d5000f104110701d00c02619a0b080b40c0c0d4040e400d5107600c0c0110141040024840e60182380c0c0c001c0986091030510f40782ea20707442880d401c103a900f42e8200b440719909020383d00d80000c43c6040100304181e4076240080d080d9000d0080d010344405c819194001007061000d90f1244412602101240940b46070303201c1c0c6418024100d60300c3ca02080d41c119070302070080580e02c00c00004c19058000c0b444014a50354061404000260a04100c22101070196103400035843e000440d0702801d410352044462528604500070408540c451258030b44548911000d101c08140c50228524030b03240c0103481880900c8850011501900c240d82c8001c4d000020807040203d82c030f8051340310107180c41c001d03640c100d80d03522102021130948a01032074103500400010304a50051074040e8203050414490000e980d10006490404101500194400e0358107000001c2c0600803140c0c0103007038045401045640080d40307014018000c04003510020b210b805124040e100200b200341140341300a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 806858282 1250 806857032 806857063
    0xc0d0f051611030c15150d03120e1216150605060a08070e031c031514120f0328180311010c050f0c0117060310020f0f031e0f0405070b0c 60
    0x340003844c5c2c814800e0260469061505044044030020149485040e41181a8140e80c0d0441450b000a071260001c01401407031a0781ea10a40c032a80300d082003002d0180c0202000201d80710658002070800c2c0c6d0031603801c003d030ba07a505458045d080c41180c3d28030307059071303030711159482c003c0d07543d5554180c191009210590740c254503201c0c0d01c02550780000d011024010400c03081d5000d0210400031080640c01100c0d90150120a420f8001c541459045c5000240307a82c0000e6030494a403164002c01c140d080d03610514030b2900c1c011704445020904000148210840165881c003102055a000d0303e81e08c8070645400024100d01c5000206036203a0b02c50b502d2070030756a4203c02a100700c1c1c8001c000c1c095480f84041152400300740328081e04581c2c48146c07551320340710382c0f80940501200c102046226000354410382030688000020303c40030080c006090003940c03090300300304040300745102c0f890070b0b0b0041c0e59030003445498820541c82c20800001d1020030342d00d080700c4015111a0320b0b00c1c5203900d16400e211907868441003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 806859532 1250 806858282 806858293
    0x3070c0507030f29011a0904110c0105180a03030b0d21031d0a08030a060e0903030709090506060d1a030f25060503070f0311030c0d0f051611030c 64
    0x500201c0f5030200140b51051104c0c0030403060041d8002c00c64064480041e5403601c00b00010480500d1080315210b1410b08860041c1c0342c1528000000c00321400d0607010f408421010072650751414007442950382110415100d070f1210400c44220f140c0d100361182c0e00604068541d8800380d056203421489058140d800740700880c07454090250400c40a50080c0c200c0006401c051030000c2c5e0011464914407203074408009440155095180d01056920260070261010f036141000221150343c2c004143c0640c020b0005550b803420301030b400514a89203a00250034003031130305d41404081e0b60703140103c86460922000200341d070074084801c0c81130307006000d82d000d4050148003075800c1c080070041001e003038014091703001d86d0740b00d400000ca01c030b8041d1032802250003086c0e041000c10342940c092051085001e0080c034001c143d1001c0951030b40030a8105640c0101c1c86813020030404a8060580030780c962600c55804200090f01c0e00c43da6118121218403a8042403191b044540c20301d541c0d080c41101d5610b1000411a803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 806860782 1250 806859532 806859539
    0x8130506030a0e060711120f0d060f060e06132922080a0b0403080a060f090504050d080f0114030c0a0e09060a0212010918020d03021b0a03021503070c0507 68
    0x1400f8200c60843d420702c0d8000c1500195140b030056840003000c00d04203004000c0400c9460302c800644c2d002490b01140d030141400045103141c80e40c01000050b000b54054980a1403901c00040d01128502800c240315000500c404503165442862000440d0b030542c81802214100414a0005040711003091200640019145002d14040000806107244c0d00ea00c1c00312980d51540129110b0000c040c000342044400d002203408288550358403900003900810000c1e0456907807000c40010f08090b0f01c4620965180c00402c014000301b444100c41704500ca08040c0128904005004282c0805000d80740010f107400c1f40111564a00304108030842070040c0454800c540c51b04418100280c1c100c4500c1e950b07104440c0000e02c000749030700070f440c040da0103411000e4180e403c141e4064040c00420f1403040c00010240c074100056641c4c82c2d0100d604074082d802416090341149400600850100d00060051818140c1000140c070303a401d104a0998505082a88039114910304482c009030391300300600300d4444d0542c0807 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 806862032 1250 806860782 806860801
    0x170103030915080f0606130b071b06050702010f030c020a0204181101050c0307030c1103010f050702010f1103150a0807080312070306060c17041e0f120f0813050603 72
    0x40280c515484180d80d1280201d10b08035080c04007207400c240c0b83c001c1d41c00411a00e0400c0c401401e58a81d40c900c60030481d5840e200001400e821020b4140c503040c0403404030302c103040c0c1540409406410f0620b0801c3c641140c80e000a403e180e10984503100b05640c80d1070445019100340a001581d80d4010402e00c01c4071a032100305d010280c0040026900710503284401c2c0c4d00e03907001c0c2c07040f504c0c20080c0c04051030401045403010703242e0258402d0309032003034000e09240010f00c1d9001e05c41c0350107041c178405001815080c1080700900b19003410800c0303480b591400d10080081a24001901d911604c01d980400f4640d014402040c01c0c51070f40c0e40f20806501c5101d501240d203900c040b0140196500322500c981481e0341d0b00000b10260380640c450307000130030300521050004c11038002201c051480d48150f42894a80d070b540104407015070307024840e51080784809045c000e501d0a1001040140141e030a049491440c07503d480001c0095100024481e0704001001d81c2c481c1401c0030404d0080400400c0d060704c81c900341c07180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 806863282 1250 806862032 806862047
    0xd0c020304090c090609171c1d0108010b04030602031b13090b0a0f05090a151d10030803060d11040204030312050a09050601050d0309090603050f0d0504150f17010303 73
    0x6110b0094284400d050038039128508580446000d81d03030380d030202480c2c58880c10400c0b840d15103611070f5004030b03401c5d02c030003014140c0c41094050255861001c505038102618020a464103800d42c10001c0b044010000324801c541a581038942000f8016a41e8032003031001203005100c4c4c6107480f414a404140701201c1c0055856400c103d4000380001e0144075010801c01c00554454003481540420f40d03003060050741401c0c2a20380d8003104d040342c00601c0011b5402420010203040c4d0001180744000300c10407000c41710016a154000d100502e203aa034281c00c5230f0310081d1900004201c41c0c016030969004000340201e103480700d80d44150141c421940c843d01c0e402c008202603200c119032a011070808010602030029842589030850300301010b000103074288801c200c04803601e04001d404000702c0c00001304540ca0b02e44900700c0118810360040040035045202d0340d08110400c048a8140070082c002002000d000032000d0340c400c00f091908044030300440f035003030306e080d10054050380701040c4401c008020150004030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 806864532 1250 806863282 806863289
    0x30207080f16060f05090d0606081207080a030c14030c030a110909010911070606080109021207031e08190c11060a05040905040f0512070308160509010c080d0c020304 73
    0x64824040312032040c5569190050941410050480c404101d03403440703004e10308528400e616046291000c01400504540141d01d410360319141c1d43c00c0308000a82003080b0b004140e012981e14241000e4090f20b51000318003e450007142816200c5a2049240388500d00602d44c40a039000c1e00f03902d908028507440000d8001703c50004a0a01c0d00d0801091b0711030341825194640801031041039283c0c207111400b00a8070861401c01d003d100144034680000b1014050080038114000c000a00406107004021004d650785144409581040e50280f0103d0601c000c00d081e05144000600114405403821400f188960044441065100e480b480860b0354408100310300035000c0c0e110085696030342010081c4600c0395161190210714108410840c0c0e600741c4d04481da10030700513500d10400706180d4854a080c6a2142c0c040907000c0000184402055040079000e03400c032202c40c004485440341810060b080340301e4440194188800340d2281e01c01c022404046500c64013400c1020301400c02c1e2160080d40d40c0e0001d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 806865782 1250 806864532 806864549
    0x2f010e010b180a18020d032604020321090a06110c0f0607060b0d0204090b040309090507051c1401080d0809070303050405041a032d01050624041509050321030c210103030207 76
    0x182d0340143d140c01000740b805142c0060240455803181201150120b5070302142c002c20a4cc00d00019002d5916402600001d0146440781c0701c1004402c0300690405a2444256100d1903900f007510382030361140c034140c80c00c583c0e2141c00020307251409800985081c410000082d44070342003015a20801442d0f810040c00b0b00d1013920350383d01c1c50340c035508040140c500071a100b0001a805102c480441c070985101d1000c94411020009400c5d8541581c000704190240c01440059021410f0600c2255225820b0781e403211340039018100103800c594008010744603511400d841030751580690852001010304448200b98000c04a4151040c11100944000d203100004d04541c80044030301d50f00103070107001e12071284000514125041c10903600d1180d9084084444d101085803d100120300c1c101a100110010142e5441c0c4a21242c5008201442c0416020f030782000c40c04031035840c0c040d118190301a03d8212048580f042c0d11880603504d1500380d03d01801803546046003100000052503000300741d800643e032008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 806867032 1250 806865782 806865827
    0x32503080a14130809060409020901090f0e01030209182b0914010f090e0f1b1215150f09030601061d012f010e010b180a18020d03 57
    0x880c0840212188810001e942c008079500140c0710811106640d03001c41c1c4100b40d924104494100424910780040d0400045d07a81e0000707505559681141ca0349008149540d102c800c0c16040080740003103e90103200090140074108045050074448012084259104d90220364030302c81449001500781c0140d6003c0100d094100140d2804d031403060352403900351513151640724400c0c4250300c011610203942c05800c60401a5225011502e40c1c0000c40e6580681580c040700740060030428903a002020b489941d06002400400c101c1040b03900301410207601c4280da114400e50245c0030301c003256403051201c00d51802d4281c00102c440181d0343d45c80c050b020020080c0c080b950b00781e0320303201c054a11411200500c1c80c140240d07400c0340f500c1d600c43e10b000b102844104000c5c194034103520500100034141032204400c641d450700d01e4014801c03004d100700c2c00305038000c9682c01c50b07000b03c1e8015480003141c00385c0118042a1903a102800c440c0804620980c607507405004a039400c1003e060041c07a004802d000c12020b000304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 806868282 1250 806867032 806867041
    0x5040c090906090209031b12030a020f062512020d02130f05060901051215090103050a20010c110414011e240818030d1a03010c05120903250308 63
    0x9520944001d4172000c2c0c014001202c0070035a0115030010f0140ca0b9620554600000c401ca44c000e0000e008120059001080d00c0e08411040360f003010030040c10084003c01000b911030103980d80e48104d0807082c4541c00c20305060740d04400110b001e485804510320001d800001c942000b03241d9005039000322000d000105500c103841d41c0410405100310045140041e82c03d010500d0600d00180f507090300700301c600ca4482c596210328008200010806d80c400c1d21113403c008400b0f01440301b0062810703140b003000203d0381c1c50020500300192001c0100c9601420300190b041d18105507072255032010035030303810702c1000100960f52484510300582a0001560440f1450100095403100d0f000c00b4203404030b1612450b078511003481d03a045854a100610758020645007008460b40b072101403000b040c030381c1400032003c0f0726005243c1036482c034510f0010f02940241e1506100e4007659600c0b00585000c006640203e200b5078442040b002e00d90302541d400040820f80009054240d0f034100300604192601c02d0311440e8581c1e68 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 806869532 1250 806868282 806868299
    0xe090411180c0c1c0207180605130606030c08010f060507030c0503040b04050307060e0102100902030a3c0b010902370e010302280507170408010e190305090a05040c090906 75
    0x1132107101e0141c1d20a40d8184042094000325541134030f030600000441c140e80c1c0c000100f40403a01a106000180d842c0024000d03258540180c0b5020f44080c1441040c5501d404019912413200b88211010031401103070100030144074030044100700fa004011a07031519202e40c802d10b230710b40c00380c401c0038800d10a850b0001501d80c0540c10b0070300041016005002c4502c0c580d40100301400f04114101d074180a0040e1031400501503072a04042061004841e40b071620017200152080c1080c04881c1e0240003c1c51345400000701c84040d12415110700000150b1610703494994040e84242002401064891481c2c0142000b42181c0710b280d581c40d12503981c0109940860015002c901c80e8150b0103480440c0440168110002085000141f600300d150041c680421034503044030604e22001c0d40d00704e10800080800c4a03420901401e42d51940c3e520240400c07090013002d07484082c5903580004c040c0180444c0e1068180d4452141d440145806001400039144102d4000c200382c50b2405044d14051030468042003504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 806870782 1250 806869532 806869573
    0x10051507150605360403090e13030e030111070212150c030406152405130e06030c040e0d030506031f140a020901090918080f0301060f0e090411180c0c 66
    0x10050303d80f0281d2601250500100301c03c014002e80c18082c00032000500d89803080c2300b540c820016042000c04147e03541c41e008100c841c0d40e0b803045110b0307810400c4035150081c07203030b0440c0d81d200da0449040302d07845200c0140d80d0a1030074010a4140d41041c0c0010015801d2145004600c29803003002d0400140b00d80c1c509091007908180108400c601c04040740c8000400c1c962140d0400c2049410580e0a003441a080a1019485500300c2003e002100b0706224150600300600e00031200100d90034442d45040c0011165505556510001090303203410100d500754405100d42e52070b882001c412000d2880441049402074481d00c0780d0401c19690140c0020041401807080c0c405050050b0354a11405207080100d0300642030180091604c56460900c1e04001000c240040504504074070380342d80c5035031410001614440ba0504801c050201121807000282d503850506a40181d000c0c44061400316010701080440c140e0398140582c18000c0800d04c41000d00d050094038991902030101c414056880d0801640e41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 806872032 1250 806870782 806870839
    0x118060c0519050306041e020c01061a0a1b0203071d060306100603090809060a030903080c03100306020f16050106080705033f0d0504150510051507150605 68
    0x84403491208110a03c102e00542d0000710003080410200a02c10035182031400d00b00c01001c04940c00108900c50b48001e0144400a1030750688131171000c6404440c080151281400605c10000c498024640400d07000c0c980d1040103070082c0444a0395030700c2c0e0841c9a00500c1c054000c0350030074042c0300055058a00080c0c00d030700c1005900405440246007240170303005030403801c0c01150303845410701c0002041d4650b14040c02c02100c42d55008654043d032410058081c0d2000b60003c0d80340c000400c100b0080704620308044045a03403151005a4031b8103004810501c038041c1d071012040e01003081c0c0d00d03c0c00340301054000382d00741c1d8120019652029a41c07401c05545111b40568032400c101c4c04a0040340c2000c200c1c050901c80790082000300980c1e040001c40034455072003061000e01071541c882c144818003100d021408642d01a900c0100802e0900c6021040200028480e0520540c0a01d0804001500f440300380c0b01400e50100080b05000001c8094034094001801410b005613201410a01c0206503065081d861 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 806873282 1250 806872032 806872057
    0x23070e01080702011805030904050c030c090f0f06180a150212070501060b0a0c0b060604060c121202070506042001120c0509150d0b0102011118120118060c05 69
    0x215280400544000740000c25000555580f44140301d01ea02c0b5850324440580e2083c0082c40d40c5903002810002219405000104032080a1040003030f1040380c48115000b00000325015541c140b0144000340755080c41c205031a8104d500800d040c026011b800b4019410400d0071203140c21125103d02c2015556240502128010ba00098201d480d0040020003084214000c0002052046c3c88900c8601942d018040040010b03101d40360340390a0101510785c141d00078908550b0a0b18240c40d02c48000c0401c420110094200b4101c4201c501f001070068080c40700240003890190748841043c00d2207600c07803400310740986100d110340c02441820100b22040000e1041c050319444640c101c10400640140394144000342404020810240c3c681d880180300d07100041c131a60001daaa0390086003907029903c0e25440e15055a041500700204403c1400036511480012440e41040804400c0060001841020954810b52a101c1d440c00c0d060300c0300d04000747c6170b80140e01c103000c48002030200711482c0c1301709080051b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 806874532 1250 806873282 806873297
    0xa06140d021507060c0c030e182404110903120301050a030b090c091003140c031f0225050601120206160516060e0f06030c0301150c0b0702012307 64
    0x10701d4122400b500b1061455100e03814040e40d90340303070021140341c08015008601484008010185d1000c0c60582940c803d50708240305680310a041848007102600ba803507001c0358183d0040c214000780382c5580f074030740004005202e039030003c40c10000302d40c0c803001035140603014074140c0381c80c0e140703040c001c0760f041b0340024010704280d07444c648441290803c0542443c01ba230003004901b030720359658600030701d000f81c03204200e980308a07196240c120301e0503002c40c24801d01c1d60400c0d400f888555501003000800300580c07003903003415200440c41c0360009121710345807a000355040585200b203401c41c80c141404424824022030b11030f42d8803003001e400e020500303c500960141f02080900d03504900c5a82041d4018820000c41d03140403100316814115601c540c128500048034658880c400d4030b00038a015001038001d5a40e94030b103051014040780b591205000d08910704109140361400da41c42010b10403001038000b01a48014100305000070b0103012500d45000c00310300880243d00400b554444003030700940c0d080d29400c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 806875782 1250 806874532 806874559
    0x30106021b060316020723090609130210020a020a0306060303080c030c0f07062703080601030b1804140a0602031005060a0e0d110a060207090c09031e06020d060602060a0614 76
    0x103900748000d00051300f1400340540000e4110304045461012a0b1404c10038a60900050248211828010322241c443c842030307030a00c0019101d41c491f00c079031950142c414001038060030b2026450140c0c0b0301c07002900902c942000109010103944480f0603070740300c0e036038507100350f1107030140c00e03100e800183d07601e40007408100440240e03401e10358000c0c0601071080101243c5008a081c01c00000080444d0081c0f003544c05445510800d607001000d6580486d0909041080820682c003103044d503622191350685454804020800f07001c50f0350310204458084104440700b4101514213072000c0d400546568101350b18482010410780781a2090b0b58842c1c0c0c640e44d402020151302010001c03550640d910981e40c940020482900c561035074000140a01400d400400d2502c1c64043c2c44011140418520010401c00d0007007800020440c1c030601c441c81d400b48110300b4103100c25061040080c845c402c030840f66907103084000640766030086022031142c184d004d003c00641da80c49100807001e6194440041e4448850032000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 806877032 1250 806875782 806875801
    0x6090a0509010b0d050d02010509071a070203010f0c110607050405060f130b040b181e2b0b182803030e010204080a0212010603080403030e030c0306010b030106021b0603 74
    0x141ea01c01d04910001c00d060710002c01103135082801000c240da0781d400504821103659024024542c02414480c000c0c0040340c0340c10f0068100404441807184d184a0006108080d550250013000c0d03504413100041020b403402d039a003d422103100b444500158060b000014100034081c2056508540000d480d440c90a03c10400d0f0b4181980054014031080300d1005000c81c040310800c0181000d0604403c025035124030b04e588c580c43e4005510084c5102d504c02c202c01c1d01b0384148800303840104000c2540d02071540074042906040d520700080c3c8032102801c81c01c401c0c6051052490419015030300d20400000300c61059144207850741d451201e4004000c041c0310b00d034800720b103040302004a414060700e400070b05007034142c071003a09980c0198402c0c0f42c2c1d94044000340042d0720304045440300d0f1041040080105624641d51101540a18403000c2c0074450851f01d0001d103070310180030419143d0741c000c0c10f8a0403903842d40d03a50403091b0800c0c0a4000144101803080700d000c0301001807401e41c10700040c001800c581c1ca10240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 806878282 1250 806877032 806877041
    0x150e01030203070b18090612060a1d0601030f02010302030601200a0308060103050708070e030f0106090606030c020307110105030c250302010f0606021e070b12090c0f01050d0b060c0a0b0405070e06090a 88
    0x494208c860003090407104001441140c1c0200600d0781e002c40e0702403600b4410240c4000c8001d045009401a0004000040361440c2e20100e00c6d03820300b07000d6101da44000040c3c41c03804240c000d1159800b00034400c1995490301040c000f118610945072901c890700e45030011011900116101c1d400318404101288d40309004035021908001300030120740700442c01003072030760956901e079201180080e01d814082c4100c0350940180b0482c00d52a10095003045400d07141c9401003030700c1d08039060500100101098024203020100e80b48804140b0395800b04400c1c002c1c03510140c1c610120164010b52801088c060125003501400c4110748180d0b0042c5800021414409a80c8441d00d42c0980507110701900010340c1300d0507202810001c40e10740c4001c1c03028a008a207031400d00c03403500719244c400d19081038001d10583e0080252014044819400500d2041007004194180715020710780c00b080c401c040b046010003c0490703059106521034002d45243d982d035129004c075540720a450040e03000074110006007031945c46500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 806879532 1250 806878282 806878291
    0x50721120e0904060911062106060306130506040b0409051c030b061803031201031a01061403010e040c170d110312070807030605041d01050f06130b0103150e01030203070b1809 77
    0x31440c015007514002426544c0040d09880d40a80b0b03445690403c0701c0d048c0d45655020005032845442d40c500200052102207028a078400f40313691320008240303a034a40da40603c50981c0c01420401c201c102c0d0381020350341c842c2900c112800c440c045503024083c0070b12a0107a1604124040c1c9180d043c2540e00b8042048070300e2240765160148410301005042801c8150798a00960140d503c00700c50f848217055285903010140c10500622400d80b601450085580048904442c0451800f420a4480b407400c1e062035178003a03002c412800f0030181e0480041e080440d0750b151070009903c0b08030a0384988441c40c0c0e2280a03034030820200300c2c0d50b840000c54940c09200400d40c007429074030f0001002da0b20b40780050304a4050540711042201c0000050040200910505410101280c1125136a241c040c00007196112920051419540c465001c100f080e4007941210208480344c2e007008407140e4940104c414102c8007440300340d01c02e20901c0d80c0010701c1c030740500480354000d0703400d000d615000c2041410300104500242 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 806880782 1250 806879532 806879543
    0x141003020d020f0304021c02010c1403090a140a141c0201110607020a1e050705060f1e030403170106090e0c0705010e0c0f01090605090409050721120e09040609 70
    0x12162008001c00e100401c415410021a281c40b03040c140140606004d50104d2802d01c13480c4010040d016070b80010040700c18650164112920040040c410b40c00c6004080340190011400040800d40c01880140c0c403006000903100d003450140d41c1c041c1d2030140102e00070201c0d00035a01e515101c5000c907520320580100740c0103050450001c000804094900300c1c0c21648800103030400c40100c01008120007070a0403514001043e0701031b407640d54a48a4030f5020354441d00e48031b20340000d2403074004681c0e44141c407590744040d882c0030030420b1a8080c10ba032561040340e040b00001c201849100607011400348060584104e40c1c3c0b1006000c0c1011451a25a00040c180b41e048003030034040d8000113502401010080340b01c68018002c51244d0000b80050402140b01c1e1605011003184140f00540c1d01c08143d54291a048a012a111900381081d508100444c2c1100000d85410000a80c4280a840b004100c00d482411440351201ca21502103c500304001c001c41da0110b80300d030220b404102581c00030880c01e07001380d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 806882032 1250 806880782 806880787
    0x1e120f12050c220608072c041b03050907080303070f030207060603080c0a17041d250923010e0420181203090d080c0f07030309140102010614100302 65
    0x40891000c1903c21a821855100540b4018842283d00c07018003a0031000f41c1c00c00480b0319000a007061095010071040c7c41f400c0b03200a540030000d80d283e400043c010200615005001800e110300100506011181240c0a1081c100c00098960000003124810b200b10703915000807140009045010390300204c01601c1503a1101c5010000c2035014004240715116000104411002031510140568107280c40002c2001c06110412940700c05005441166100c011002040c1d61520001d08100040c8200c1c103148060b1100d544404680203041d000a44080d18400c0a0700c0340c507079040c0044020360001d114002881c444a00d17a186c20300d900303c004030204942c0d2600d5130000d1a00142e029410048604440400e4040302c1c001c45d08000891001410901c40130f50301c3c004a2402003a2080030184006280000000b2403c015003014010100f00c4002c0034295500c00c0d5490600034400b42c103501881c0c8800c42c03030001e22501580148100c000310784190300c4454940c0803010401000c0a0501d14000038980c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 806883282 1250 806882032 806882047
    0x31608070602030a0c111605010c03120510030b090a020d0f06090b0907150e03060c0c03040f0902070b07031404080c07050901030f0606120c03080d0204031e120f12050c 74
    0x1d40c0065481804000000120071400100051814003601c941d41a20782210002e0090340545043d07910980d002820078060000da41c0c60f040f02c21035403101040486510304014000078aa944014800711f078091400400140c41d0704900945581c40300c3c0e070080d44510a581c1c40030000e105925120451400350b100002d61400a8446100d0403004481c102481d4002840900960101700d80b102101c450034034013800304554000c0440d40d281c4010b02456248100031401080c981c008104440240c00e0901e04001141d030350300a6840030750016501124032120880005040071301c280b04120120500d801540c4158445440769002030380614994600d9000b00d80b008274807901d9020140c3c0c02103218196407030340603046d41010801c0f101aa0480c695095404e400c1501050b0b9207070703c22082c1d98011184950700c9403100c21980091046604c000e191004015100c0049659202c0110449008155090040c2044802114030421031500304010a03005460300005040b107900c10390f881711040d000e1a180009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 806884532 1250 806883282 806883293
    0x30121080d0509061806011202040b030f07050f0405060d020f4c0203042106060e09071502030f090a0515070c0f050604090504062901090b030903160807 67
    0x241001e4120075101c0c0c0a200f4044820062280d0000c41c052400d0f903422081000d1540f0f42e401132107510020007000591105641c0d80f03901600c00410700800301c61381060564031081d1641d0b0f2a2252a100d26a2503410010a0900780103940c0300e018001c0801d20403190b13583c00c04c8403880c24140f6641e0040410500301c0620581030100406428448100d60700300380325507507540100b40784c4441c400d282c00c1800c914450009d0b000426181900c41c1c210008101c448134910f1402d019002010142042c1c0c2046000203400240403941c40c000c2080c5030954441681b518641314130300282084a50059200700000d62503181104003074042958000c3c642c0e80c400790350344000b801c0003001070090740c100f0200081352001c020101a8100041c00b05c0f84200d040c583c980000211140950f00c166414240c403800000c04002069100483e40400050f10b07440d0760b5540c2c1c000c88581030101c0381e150302285e0303c0000400c14240d01001c1d01d1040215000031442c150701040e00c2e1880309044002141c17000350034044003000a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 806885782 1250 806884532 806884537
    0x90c06123702040305010b030f0a0b07120c031a100f0309110d060e1b0d060e0f0d0e15030c0304060e0703140c100e010c08160609080a02061b03012108 66
    0x1c90804003585660450800a08607401e0310915482a40038000c80e13880d00b007000c90081c1d5400d070007802c1d0541903518500290340001c83c08055020051801603522040358255002d0700032032441c10590400c100700701040c001c00310090a00140403a8a110407407541a100b904020718542c400d0110380a464903c90100d000e441d00d440045402d15121070307580180320000c10044440b46061402060000d03140300c040341440007088009031a19803907125400c00b101080101c00780d0000044129217207001202c0000340107a90b8490307118401d100c1c5200030b80c0c0c00001c0390140c0e0700400c0d403005a1440c60b202e644d121401040c115109003180e00034000000301240350040c0d0303004400c05a401425000300031008004440c0c0c05074600205100342b600c0d114100f41d900c050b0307100c005540b08400c0c03544c03106850400310b9069100c0b200104031904080c062402c2280b1f03032019090134043c83d000c44045482c0c0401444001100e4100c0c461500000e000410410100400721516803600c1a4804580c41d07154480100c280d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 806887032 1250 806885782 806885881
    0x30e060a110c070e040b06060f120a060314070e0a0e122b06090b0901080a1518051c140a05070f0605010b0c070801020f18030c0604060206090c0612 65
    0x440130000c00c0b003400380b4411242ea003c0e5040303c80701c0c942500c1314003050040c090310102a145080b51740008103004800d502000145800c0700100005103618000159521010700aa501d11103035480499400d203242d001d03044050040c02e015000507031035440c48000540040c0c0324012a2160304215400c025191551580c6007014118040381c06418411a1010b0310000780446010b6407180c801002803000c04600003d405030310419000306212703a5030814000e014800c0350107190404c1c081e9080d0400200080d1401c0c50004091500c21049200f0420340301034030803d502d0009620b0810038902c013a40700310001c011321481010380d500b400f00103440d070a044500036002031015a41c0000c0c02482c2400030043c0c4401407103898000e5160500e00c0c92462000e001d145025040c07401921140071540c0d90900100540e00301c05841075031a25900c2c07100035030701c8005440468441c0520241042d450800108894400e0745101e102e0306603866010130300e08401d0b80c0c0d170700c404031001414007209680394030b1065a0030074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 806888282 1250 806887032 806887049
    0x10f02031003061a01050304060b0d060203131b0605120c040e0c041e0b090f0f1e1806010504030b06040e0d0315120b0103170f07030915030e060a110c07 67
    0x80c00e056141c003e003241d12036051007580c1040400b9010050780e01600701d950155200a000c07503512810303000b1810948040368006c0405002008000244898001014101d401b03903104030010f405c0c111101035000124068000064810003984010b800e0720758070035411402008400c2d01e403a55505d00d00d045041e0982d400208a18001740c01c005040000c401d10b41080700d1000301c0d54201d440e2080c10011ba20400c980c8500801203030140b04440e1356090241c030121040a0030a031402c03000c0c0c405203030b0340c1004020500e00c9621000b080540201c144c0c00128460038060b19040d01c3c140c19511003080004004040e1756010380c803210780c10b45101c0144101201d1801949000c2001001d000c0b01c1201ea0340d01741c10070f81c03000700764000c90300101d83c00074511030440c0c1d08a24074078802c82c804c504a40b01c03841007190b05c0008040000c1c12400301640240003204840c0f0303240c04071510144a000c11070568080700c507400080d40c4514017048941c0142d41c4141e00740c5101c440b034a460300140780d00407400e148041c0e115070007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 806889532 1250 806888282 806888311
    0xf160c0506012408060d060b010309060914120c0a08030406061d04050d0c1e0204090c0806010e061f080903090307061e020a0302060705070c050901090209030c03010e0703030c0203010f0203 83
    0x641514a00d182c03d901030090801c00901c1c901100030610400300da00300a80fa554440a11514690003540314081e01c0b500b10f001400442d640d4203041200c04522049501507108288444400751001820340f5a42c112200162900e0300070740d100c5c2d0b00a9040030b44103030b5549035a0000059640d011600d03052328101045030850141c40c15080c860305102918807400c080c4091005010001189502150b4541c1c2e41078201740014005400403400900c048240103007506a07004011441c0c100001d83c02d41254003030b0310f1005072a51044180056201c2035400490050452810300c0000d900174031030198400c03246802c03241486a031100080c030f00b1501d40d2202c004603800c555000c088142d42c4180004000301c41c0020262201e0700d0740d00030360f1030900170074140400c90041100d00411420400e9007000700030050900b100e5503100c200c204029880740d12001e219100b0f1000c206290304041c01131a6000c0000c1c0090400e16281d5103080d01d4000d0b041e20100d07810b544e5651064152001c52014500030003610035440d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 806890782 1250 806889532 806889569
    0xf14090604111e242a012007030e04051005011403090d120f06060914150910050705010504140f06220f0b070518090f160c050601 57
    0x103114240064000c2c0a0310440c0000c1500082c90b00c40424005411344e010b00f00c460700d805030f000b40d01e03040d031503c2e030040c1d000011040084102c80c60409182c90316425002c100d21542c502c500e0807580402440e511041c42c2c100303c169410b40040103031144a0280c00d1481030020a100043c003240c0c42140c0c0d60346204c444080920195900c010b000c0c081c110085001e43c90340c00d14480896841d0007401c076601c01c125495000340c4030901150423140489064010500010341c80d00c030040c080c00202d00800310b40048055030700d0580d00e03041810301981038610f03204a00d090268014014202040040300301400401c10034000062000d2240740d204500811080c40710b449016003450419903240300d024085ea001030184602c5401002420840c030b03010b0109000a4086841d0288021800700c034051724101c400810040301903000801071502c41048611030740748030351807001c10429100030780d21105851441c0c00014103044441102c40540d0110b410314120409180e80d9007494118260421440f1100242d0310b038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 806892032 1250 806890782 806890793
    0x60d0606091a040305060a05270a030f0302091f05070c090905190b070c030e09040515100305060105040f0b0d03030c12180f060e01060b030412080c0d0f14090604 71
    0x385490101c000c02c2e2506185403902c03580c8207400350604050030754076804648000c803415041405240c04084044032010030381004c80e104c00002c1010380200fa05106040c1c8c1c0d441c400d00c211038035100020070b11101d5480561842d0b0405072590910010700c5030410400f40861094101d0b4002481e03c04004140c4000b2450a00c0c10484544d03220084400c004a40380001500204070302e904c040b05181c180c8414202c0c0c01c0840b100e41d808205140c00ac00c044003444280400410348840d0351801c11910015074948107001f54810b1401d203c080d006800410046c003e51511303810001c214401b1140c00b0602c41020000128154010f050440100e41ea90101900d06d03a0000c040300c0d80c001480c01e04100106410058103840818000004c00152504514000704203469200960164111000b00601c940750b2030594840d50060b20f0a40d14a200501d11a41040c4180c0b112481958a0184107040c41c24602020024040120308840d109444800c040391042e804800a4442d0510800425107414281402d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 806893282 1250 806892032 806892059
    0x9030332090f100f0f0b0a090f2a02010506030f101a0301021207030c1b1202010e030d090b0f2203020307020303211005150a090909050f0f011802010e060d060609 71
    0xc00b4200d0708140b034044407a03441140e032800b2545d036204045a102082c1c50460018661540c501110ae12010b0b0700216a141072401e040f40d00b44960000c00030754580fa41010303614610012040000d074030074004a0a0003c56070068480c032140c03482418000d9040c0d0001a0030383c0c1100c4030f08101685104100507a01e941801868004009030070290450030281d000c1400c3c101e11208060248420740c40300c1d04015101b540a90010710400040e00d4591400321841c074080c282c1e000050b9110039095020a802c914180e01c0c03a40180400343c080360340c2c6582c91628401801500100b40d007580000e12484015071070510007810503502c1041da443c0c0d03c0154008010b004c0c040900030414510032a42d09226640f03a02800100b0b08001c8c801281d110f03c0d4801c0111510075894128842c49824141c940381004000200010b07420030002c1641c20f0381201a524034200c0307000c203800c3c40c0354041e842c030178901550190140c0d050803d009400310345006d0280d4250001d9407142c0e4866000500b081404020040c0d10b40c50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 806894532 1250 806893282 806893301
    0x190b0310061d0904031b0b150108270a1a0613090302151305010f090b0c0a1d042c0f0313050405181009030332090f100f 53
    0x200ba040c800381d0203039038080030400d55031164000c0c44010041000d041c0180001c0444600d04191540100b0303d03494071020502c025281f030b0f049a84441c1300880e030f560040c940d0324030990703119071440c081c4142010035894010030003a5950a074019060a840410410f603511080061032108507089800d0030028009070b0400c084c1034070751aa2405c103208001a80c00b0940464018907514500382c2500c6d10626090001c01c1d0740030091280d072030410792109408d060341001c1101c07800fa01c14071245035180030500b509441000c000200003101107510008180c40c03400c00300b030419409400001c0040d0101803224400d80c80c5c807030309000c0d0744454900710002d000400003c00c2140130403014508040d442d1203808040700d52801010310954440001800303140a4089a010022040c2c0c1116100342e400309007040140007051003980002d080040c0006918004008003030002d200c001080e4035040510307440307182c0348005440b0f0f17001c40c020305601e101d1541042103444541c0c68030000010722140d503016607008880d040d81 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 806895782 1250 806894532 806894537
    0x30201180320010504120b06040b09010b0a030f0f05040302010504170a020c121219081b030f0604091b09060e0f01120503040503030a090905091515190b031006 70
    0x90600004091514802c0b000c003205410340c030080c1e03079280180c8a9000b1904034a0607519903001c0e4005004150174080c0c05840706440c10019411a5014042100000d000351042d0a030104441c95000b03202e540020500c80807141e0008004050b41c08000c140c0d80180c5080c0c0060b91504144810b01c01040070356050381641146003840c006030038030040e444007100410284580c0035a14001c5804070b007400701c031004840c500c0d0016a50b03009400f80344140605022104001a8503c000a0300c000018180c04060203800f9000740c01d42e600d10105083c811801041e482e04191a800c1220018901004a4884004001040000a040100c80e43c220340e415406618606101400e00648101c060403071415170303154484010b000039070b90500c1495072045038010364140c400064820740146d4031010b07401c1035600150081c880b603110b89640702e80d0b490400c000f05961540c54004601002c0d0b0750781401c0300240e0040c04102d9802e180000c541d0400e40e2a92000e4658a0300200b00007600b082a07403203001410590 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 806897032 1250 806895782 806895827
    0x212070f0e0a090b0109030206040b040f0f05010c0b2805090c0913030e030f1b0a090207021027091416020a12030b03060403181422020708070c030201 66
    0x11000800151051142c4202c060313995003c990b29074410405100a5600a080c045d62943c0e03940e510250307503016101c3c01c0c1541c3d20346103001c21050b42e03d000314003c59905035a15000d01c40c00d51103038080804080e10084642d40102088600380d504170075180204103402000060a281404485080c8402040098481e8840e20708102c406e401c483c1c2000700c00c03074051500810842581c00801d24002c0842141d1000e0311031560300c1ea01070305444104107203845041e200701c9001c581d0b60305164240d004040c3c0003076004008102c02c0929900c10b0450322540c24901c52000440319410500f0900b00c041508111901a00c401003020b01e6a1a590000c0d0071003007982c120880c51030716800094039010501401080c100320900d01c034040d02d02c00d8000720400c000003000c1d11928181407801810b0600106908042c00f651700200260384c15540d40090740003075025201e201c81c0e8284404001065441c4031444074019800c0c010180420307400c001500c14207101d0b00c40f0f0703001c403410b41c00090704060041007100162050b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 806898282 1250 806897032 806897057
    0xc0906090605120412020c13200a02100b06251b1d090703021221040501050a03090c080102220b0405061c0e030c0304032a031e060212070f 61
    0x150818103501607009600e851201017015000c905010340380b01d6040e44100702e1060902221300903840b080c6440c030360140455080c1c0b100c15501019000c0c84c208000582c01144418090080c1d980104c510480c005140500c0d140300844804545442c504100407261200c5100008015400035445211340140141040031480c5c80380d60140c2039460413040050102c0f41c03000c00c141c12020007940b00a5a8000c0140e003500c240414803540d1002d01d625480d81d07038a000c106201c1000c21800c2118142ca5060f075801c4e00c1c168041c00d01b54040d201d9070004494011409400052800c020710103000c500c0c120460b001401000e075040084090095001701560600800003000305980cbc1100b22480b201d0041004042d0442c20342015000340480041ca002c0f501000601403040704003c0018401e807481140001f051016407030303980103250046455040968100541132010600c01e100035030201c9105131500300d21303110b640d44840590f04801c0c11656104040000e10040d10703040b00800940700c903146007c8184004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 806899532 1250 806898282 806898307
    0x30a0e0f1c0819170f010f0b0c071a07150605060406080c0702100e312705150105030109020a030b07030209040e060402090112030206070305190c0906090605 69
    0x1000e048410070101e034001000700401c262100e5410200c4003242104441c040078080301d9024031201c0780104a02e00081003c80303c14001416118038001c2d20015500385180031072594881c4c46000074a22035140300191036502a0480e054440502d5403150f00c5100c98a00442030082001d0300440e1a800c0c0075083c4460740700d04c030540302103400b20f140c88151511141e413000914801d40c14041d41100c62804140001d079000501c00704188030031f5881c040c8a01031103501d5100340d950800140c0c20410f82101500c00c042007030f044181840c484100c0186220910300444c0d030407040b00f00085a0b2600101070f2104160502c2d082d150061205800a1100f004076500284240c07205c1d000050a0010050228020790310075415101c1140d03010700200f10580f42d044500b551440210307400c03407003a64141d0001c12800c61540ca03e10005038160020985515a41416009018018036869203035000104e0100b140515015203446840c80fa21002034035800c100c0020881c6003150000030a0007400c000e0042e4009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 806900782 1250 806899532 806899549
    0x14010206160806130f05150609031b0f0d0f020301050c0405130e07050a120204110c12092e110304050a030803040206040e090d0206060118060e010e040e030a0e0f 71
    0x407500d060862556101c0c0011840c0b452840030190f100c1c81d00017041010001d03540106d0003101c106002d24070781c807030100c1044011b2141c0d1340c4858141e0003840949041501000c0d850044d60001802170200320101c0010903929a45800d056800c407100e15510070550400b8400c6507040400440da8078030b418107103400b00d243c0304100c419070b8003901e035200170b0032510710010311041024100040018407625604c58000042c00c0c0842d07030980c0f003a46091804101c0030b80a0080315207152018010b440c80d01c0c0b8190141d031039504103624032604190640100f0b03119016007007003400c600b40802200307194003520081c000e00a40740d00c4204800c561003007005000e15031ba2051004220b0703a22400556680e40d031440868424043d0303501007412031500e0700a1000060f0003003035030742002525601300c503820759a10004450800f20045070441c0d10820300c07401d200483c41564003500508040c14402002c0c0381810202e0f045030255050880c180d040070802070b640650040202e4000d03241110180601e201080020b1200b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 806902032 1250 806900782 806900821
    0x271505130813030507060e0103180b040f0606030501020703050307030c0e030c150c0111040312050a1407050114070e0a050111060c0c160305070504050a2a14040f14010206 75
    0x10400b00b52050040400c1d0b2046014550041c25038665681da01d5018000c8400b00441c140031900b040405002948e048085246036508100440c4051302d85403144015941c0000058030456207030700c400f0010517001d00040403c03174420f944050f90b0b07141035040103084450404d040010016043c1d5240403946c0c0014008680d0a0101c4000001c612040d03603000700b61044041e04e940c1ca5080040000e29030300c7c09400707802103e0040021500c4030080c44030460300da10505510002145278400140c80396011407000c1c10b4120310810000503414402518565240c800b00d5002001580c200260607403810400010bd00034132003030814005000c01c00060b19201c98004240301034144000c6004846001c00b000010f528089a15a65a203aa02c2c2d0510741d032129510700444c0c0c026400d03c004541b80c1c04c8284502c191120340400806840071b60b12001c184041000c810041c00c01181025042d20160f408000307000915440103c952070600e0a0900311384080c55036040d6065412007001c202f042c0c041041d801c2c014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 806903282 1250 806902032 806902043
    0x111c0e040207051b0405010e0c0406120b03150a06150e1e090709320103050a111201150f020303071b081902070816050d020427150513 59
    0x400a4500490300901031803102420784c1c410741c1c0f55508245401194211203550a60301803003540e0b02c0d0f07500106a40403c3c0c5090303002007000c10042001c0c510400b858103000c0c042c039134085410100400002d1505001d522401c0110499170107000607840c0900c10300c0014160b0002c5014240720140010f42015015a035640c000d01400e00c01c3d8002040034078045500181c020040c401a041c00038009020b041c036030040103d480130220b42d5020043c0290960342143000728080a0440a030210011005014083c1225144584550b014440c6001d00c902030302d520000351104003034030340c503240d18500400c012880c14002d024144192550231903000c0101c0340d1081c600d0900d80d4070b101038402103400103030b011900980401e5002c695051035000900281c1c0c0c00c1c4403903900310344900c2d40740c52405480703000240c20001c91b440c90714820000340c180281c80314046800104001000d40076440060141c1d1640085040140440f261240800c04181640b1800c011081c60801081c9060302c10000c14084213180a0035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 806904532 1250 806903282 806903297
    0xb0a0f18060e2106150f06030106260c090306011d0417040302040f090224030106030f091b05100e090601051605010f0b13090c0506031e0f0601111c 65
    0x8940b00c0110382d00100710f01c0400b40c11900751102e84541c903003409035040c203030302d072403128903d640c51410800014141d5401400240307143d2034250140d500c14002148180c160100c41c100a148425041c0c0142c4107800513004960760b0807000c8200342c14090140c000d401011303007002d203074000e45c0703140c1c0015a40f00e070b40251600500000e02004030071b18041c583c4020b40c040d0070f24020040e4070030301e41c00881145100b610081455580800b51400d031020900c060fa005400600040000a00c00d070041e02c1d20102028000031001c143d510342c8031801d400807825a41295074004100514200b160ba26025190700b8540303244050240000200010f1029003440d0410801040c4a0200d00070030031480180d60703000008002010301c40c00fa5901030081305000d00e00c6101c51585514545886010320019182c1c00f00c00010094140020840d260b0405007080c030a0344084840d42c40003108949a40380241d850720001c82480ca03044000504014201502880e580c20030021000c100700c0c60100c40322214904c0c2011003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 806905782 1250 806904532 806904557
    0x427092a15051e1c1a1f03090b010b0307090f150503060a050418060f02070201170414030705062202010203160303020d060b0309010b0405010302031c180b0a0f1806 72
    0x40020400c025000780c5910000b41c0b450040300a840f14211066098000d0042d4151041d00c40c1e44884850206500305444000e1200c2400304000020000c42e090b04000608c4003c030388407048904001d0b00860814080007040c071410a8203c1c1e0150001e0083d030b950541128104115858444210030000e4213000c00407000c9a6680d80b020b0721400074182c0a0f208000791544040c43c8005d2280c6030b1020799281d8600b07013151407400c405000b01d42d90b46806848030890314101a691400c2031300300600a8072215900324003c000b5140520003040703071a000c2c41c000d0141c2c2c00c240151003100420302c410b2044105039454400011313600841a540c4a10410424100c0e41c111030409601078451b20032510845498007901040e0600e170040a9802040c0c001e0080100c3e5501e0310601046440a01010754154800440494030300c0c0010501c01083e101803621601e50003168010211010207a04425050703040421401c0e045070780815800c0b41c907006498150950018280c0c510402d60702c2d4040c0c0020049080c0c0c620 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 806907032 1250 806905782 806905807
    0xe070e09120309010c08010b04270b030a140708031c020a020a06020f0d0506090103170c0c10080441030403080c011d030f0427092a1505 60
    0x740a07040840181c182d0701d142040b0603500030a5803000001c003107000d4074004129004420207540a13640398480c1d200c071031015141390b507060184004980d44800d807115075000c910780301800700d0140d03140f2868840002c0e103003003101a03007081142d4125080c01d5106008100803181c000b5003010b041c2d540c82c60b0050380c07050007400882c1071520440029110720300014941140c640c0e14001444844040c202c100700c0d42d1140010006010001e100c068040489004000090100800104602002030048400d9a059440030450500b41d418155011804807020081440042c800c7c034216411a08103620942c04a00c0d40c0032128541e0034240040c0c2c2c030400d1000411401c0030002c80e0003440d000180c00b521044040c0b41c17580039001c40c110b02094042c46070f01e03418403d04000140c4040045005c000b074202400d06600b450403400f03400828101d8001d018010a915107644501d83e00d4074024a0000e004986891603400403503008000040c05c1114441c080110b002141210b1083c141513151190343c0d0702402050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 806908282 1250 806907032 806907043
    0x30306010c020102011401081c0804110127090c17060109061d041509060f0e01050402030402061c0e0d050a0c0803070c0c0e091207020306040201180f1205060a0e070e09 74
    0x21074000304201c0041428072300040e081210130756040380f0544500c0d040104803961181690000c00b000c40f0000100351a40c0961003c08401890588540020050107a16a40d4601550200c01c8060766110201c1c000ca82c880f08c1c8034084900b82200d01c015040c1600002c10200c840e1140d641080400340115100a0742044140c40800e0b005000f80000d0b624080f00303801f100158810307500d0481c40d02c2000a0700082a509003405c0b5654144c9031020740e0728000501010f9800240201e0388203508011500895800c040c0c070005038110204001642c07555455042d280c80c07019241e040c140b200a120401c1032a43c04850a041e40c0d620042a903184c1c1c541c0001035850000c28074004201c10080900440c0342e0740c1d020445032003448000100e4481c4110002e0303421040c811410301030740603000000010007550003000c2d0011091401c2c0c0002402c982d030b4840007101066681c2201240c209034112510906c0020089d03250040c9982c1340411640c40324001040d507802044c4201b590000c1c40b0400240c0403e4103008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 806909532 1250 806908282 806908301
    0x60e1009060213140105040b0c0c150712030213330225060e1009080d0210110c071e0510050a180b0409091502070c0305070e09030306010c02010201 65
    0x281804240c0451070848041d4001d00c40303c1c0d10321198808000f41401690a00c1e80303c544040e1141c0d481c2504080c42c0011942c4055a00d401c03d2150054001c999250b21210781e01030100c40601584800051502a01202d109c0110608050050110030040d440004912044a4544240b4204810030008100604028614201c901c1c0000184288055000300d04102d00d01c007050070000700c00c00b405a0701090170360300340211b40000c0c010580c19582e50500511021400004c0d050000005c0e503184483e6181100c1c07a901880181c0001d00032041c01782903070081c82c8045803444c5004c3d040003440340503260394965a103d0b4076280b02c0b0216804002508480910000d85000750000c085520000c1010702140e0110240341c00140d074840d203150b0a01d644c4440f18056544d4407052a1500c1c0c03803c01c070100a41822402512400690001e40241c0c182500c014441d007441244041d24107450340c00c0944c10181d641e40261070051000003048240c00011048035030005090801780d00034690703800100c0c01001c0182 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 806910782 1250 806909532 806909563
    0x5010e2a100e01110106030c1d01170a02280f090621060203070507081218010203041109060102120d06080c010207060f1803060507081f03171e0f04060815060304060e 73
    0x3000070840c0a000c9c4045030048a0006100145982e200450800d0501c1d444254600d82c022103c05001864130044220040203141d401c400e031911100c08088184c41ca0b0f0f403101404040d486020041c200c114091300d0010070175030f0701b480004005071040940c40b80e1030003001085594004005040c0e40d000e02c0941d01c55540040d00301e0344a581c00080000941c0f401c1e0713400100d0300110b101a112070300c014003c50344240d61151918504807800014414220000360015055010701000b44401c1c803600400341c0702201c01c00c0e0340490311919010002d410b04407548032441c1150005101440041e410117000c084081880c0350810002c1492034802e040d80a603600010411401c00050110701c0d58845c0310603020308030811201490740c140c2002e00c8015015440020016210480c5000022212802802c040c0340c2040300981ca0b5065190401c0b01c17544412802d4814920103d0288555980301d004543d1003001c50504410059500002500c5400000e1004020300d898556417000240d0030310075440e81d4400300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 806912032 1250 806910782 806910803
    0x216080c03030108060f01030f060c03020d090b150d0c120305040512030d0b09070e0405060307090912020f010204140d05010615050403050606062505010e2a100e0111010603 76
    0x1140e61203030310a1003041140d101d050f010621600308841180e04032980210031140c3d16125aa500c009800f01003001000e140e030074001d0b00354000060088a0500c0d1196154144510b42030364441c100da600c224030f0b54014100720048000280000c075025040d0b4125040c0c61040760080c2c03604070b03440d201d43e801a80d0881d5140c2400241c00c0703c008050203203601010014000090000207000300c000044030154005840c4510401860500707030f22294002c1c4000e0241c03542903403110500c1c000d40d80441422100340044801034100c10342d040c040c00c200c15800000a600d014038212145240b41030280040e482a4003907050141001400d500c1f64004018081d80848601504007001d003064100e80b009031034900400c00020058a40f41d07003241c3c1d000000f55955000b08501003c0c0c0c07945462624008c545540da02d44140005003000c120303c08000c002c00c04802c03d082c1c4054140c440a04a13902d50a008032803100c0f84246068101c1d407136000610082c40d002c1021008074414501410803584050712100c5403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 806913282 1250 806912032 806912047
    0x5060907180515040501081f09110d020315120109200d06062301050712050f04030606030b07030e0c0901150e061902010b09010e011a0c1501030c05060f0d021608 71
    0x40d0241046417000d8035400c5d1a965101c52000964916000b4003460030000c0c0d0003848030544c82e900c581c90140c80040c0b014100510800414120b900a031125090170110180b0946d581c9800002e07031003041401c03802801020001d50720000b0049a98500d8015071018030600340b66902d1300b680000405400c507005018003591840304141c08040c0d24121001005103400d4840603500800482d111158842e584410604030540300325600c3d080000b4103211031004210020100e1074a0003010702443c02100c031941c0c00d00b002e420280841d000003540322402d03003110510781d4041e0303122589141102d56200b81c014120418520450b44404a219440d601c240041000900b0204000c0d40803d41c580540003002988811000c00c100c0c3c07102441034403401c0d54054010b00055420031020320149504807652420103130710303c82c501e042155101803040e1403000351b0300410a000900d5060340051600742c610520741400e40881d20ba0b42d2040302d9640445540020304100d06000c1c00c43d810703412039003021f4110b0711190b6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 806914532 1250 806913282 806913319
    0xb12030715091e0b09120d050a020403020d08040f0f0b070b0406020d140a0608030c1c05070602040e1b031e060f060a02160e070906111e0f10050609071805 68
    0x80f640c0d400c0e50340c2200c4a0014030600400941c03143c500c601da032101818180c1c0e0700068406060010810030700e15801b4400080181c4561001d1507070548075941c09078540d4208480002c02905961110040d080015400c2000810302c1d01140c49082d002200c0e092030381e59070708100010b0b200303110141e0b1071240b40001a00320310141020241c010383c28000d051120603642c01c2c07010364034011440703003595a80020056000c002101c09500c01408510b091107805c14100e503c0c0c03603003283c1207684049440d107100010864a101c07429100307100402c441e80503505605242040804c610009451075009014200c003041413a9210500e0001210006000c0c80e40c0301c2010743c00135140e00b0001e0540303e00503903c0d240401d21340c80d5440d42c1d030710030403043d5140296a0b2400e0170444001c0710200b02c2d400d0754095060366501002c2880d0340390001c400300000501b00540403061052826441c1c1f01010320182c80d00b82800740d56030341c000e01940c122200b45032800010960821001d80d45442da4030490384040d04510104d2640f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 806915782 1250 806914532 806914583
    0x31209030b0129040302030d0c0501200d0b090114041a030a110112140627010602010c020d020303011412030d15030c120b040b07030605060d0905010b1203071509 71
    0xb65021075030f440744618070381030390310300683c04000d601d5003040e07201302d404c80d03c600c034000c02060080303002280d1512408681c3d9203040b24000290380a1170006500807900d4407502400a020000b544d40c84440c1d8075100800407201d0030700d00e0070380c4161344400d4001c00b210f80050800e00c41d00c1d002000c2d540484401d151400c45103900c078800d42d020811040c1389041484591181881d03206400240242c65600c2000708100018454610306e18403244c202140d0813801c0350800e40e406170905030000682002c04080103413a14001c84034000456008000500442e0241500c0343da1440095071f403900360700b90000035035085020b105800e0303140342c3c0307031807884040007007111109000c81e80203070f40f1012119180e400f10040b43d4094800a4002c180da07038003090000b4a51841c080d440303411352a00240071070703c039000250a9405421210210764441d203050701880310130b129800d021501110b107800b55500e152070b00c5031207000300c40024003103100d01807000c00701e501035030000c0c021154400000071103140c1c1a00f8041c502c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 806917032 1250 806915782 806915819
    0x6050c031b0321010f0e10090c0f1e0903060b010504120602210402030307030807020f1905010b0d03020a12020c0402070501140106030203060a1e03020d05061816031209030b01 77
    0x214100c01c003080e04030300040f02d590503142c9008182800b1030030440104181040075141600000880301c000403000c0640c450200005601d94031003102406141e8020107a0410104000845401c01d40c210b442642062000c011640e0241c40480c9407904d44005070350038020380d4400180c0e40800030b2017030200881c0b031303009141e40450300d20842c110300f15200035a0a00c0c0001c40c0d000350075902c00c2100313602103405041100e62004c0180704071140030004000c400e04120681a0f4107644c6250094000100310081c06074138071036401995414070202040d28020b681c0c4020001c050602c0f60401c45000c003451092044251002010b803040d586e841c0286451402458420503900007030384154004182c491090084074050a401860140450f00307140c42d18040380001c2c60360a480c0d20b40f8800000042e29142e140011140c00703100504a01c1c9003090700078011310b12078040c42040c2d8104d030702105154042541d619060720f070004e040380c44149025400f0303207411f03500b03030405491071031100e00000c1c69000c0010b4030b4122 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 806918282 1250 806917032 806917057
    0x53903090307120315330c110d02030309010807030b0d030908060f01030c2c1e0708062101020c15060109053a121d12060106050c031b03 60
    0x100000150480407a0200c134000c0410000c040c2e0100b10841e02c80781010040e0082103081c00c5140c000d02d81001c00001048031038008602e852407194140142415414929042920308030402720007540082d1312442004c00050502c44081c010842c03561007075002c20b92a600203484140d440c002d42c200a40400c01511803040140b26040004801c642d40110355030403680d0021008108905044240d5081901ba4800d082c843e4109400400c201c4d40c035074100707401420600c0c0240741c0d0800083c6011000c11313004004000b881000018001507403290301e5a010f881380c0820704440443d810b002051b0180c820b2290b8907106204892101001c43c40c5c101c40030f40074072001d03210030f2481550351060100d031035803880c800e42807040301c001522541042d44024a00d45807070003640c050b00000c2035450349110803500c014000003035100344800200c1100e01111612001e0200c4915412090070a041581d6107c140a20810410081040c1031040000c0003071f01c2210b406050340f131240f0011030040342d5490300500c54004a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 806919532 1250 806918282 806918303
    0x40c0906060c121706060a0e0a030b1807030b0c0d18030906030b030a110d0203031b03031909080a030e0f1f0b01090b0301060f0c02060d020a0f03053903090307 70
    0x9403140140c00c40b001107190404c40142aa481c1001c10030340d50050740300c05003405143c1d03140700455911401d44002851190f403540d4030728204125000c401c00303150382804070141d1110300240f02242250340102d0b4031140e0305001e0b59965480444a60290100d05607101ca4268500c103040205070f048112182665015981042101d42d41c07000c041e0703180d08541e80607010f0651405810201d0030312808005982e400601100c2c54840c0307100f41019500019140d18095410100038016250440e10660115885020060204501c02c2d1504c1000b84205091401030550340c04041e00c0c10501400444e250290724000d1303a80301700e025515107030342461100080302e04a241c030a03080e101c1d41c01030300c3ca4819211505901402c42c0e003401c001755032001b1401c081c00b0511642046c2c0a0040e40c91130010030300c1c0400c5030707400f40e21045644409031418241c41c4400041c91f00748030030008001d400b4810265445070716018001074841c2d8a5074480360b11800c40560522240000c1001070b541c800100400d0200d01c194070a08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 806920782 1250 806919532 806919563
    0x90c082e0605092e0c140607090e070305041505040c0504050c040603060803072411071101080a0b060a0f18090605030610060203120702031615061205060f040c0906060c 74
    0x110210402c518803c0308000e40f404d0862940b0511210240303a200c2d65614101100c9680300d1483c3c620225400c0001a1100344140024401c08240c2034101c007081c2410f1002e81426914241d11441a022004400740d0b140d00040500030040662402090007400400250403c40003d00ca181e0041c003550b0046814404000f074000c4002089603003080d0000000c0480791150b0040c02c0d0ec1d840d40958900e031207521554440b48001c4c07040d000341021803040c0e00c031f464802400e40003d8400c40d0014900000c07a40341010034010b070345998084452603552403400e55194003084e4000e5809855004108600d540662004034200300c85900c104261107045084480b1940c4000302d100301810a400b498006810a203d01d044002113a0021604210540190303801c14031212000101100314100c1078070b28220000514044001d0344c881d501c0174010003032070030307100782026240d550343c90b000a4140543c4803d403000080c1030000c5501c603203002d4070030132105125495803003200409142c440002079035220b140c9807204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 806922032 1250 806920782 806920819
    0x2040f1d060402060d0209010908060a1d010506010f0e0a1206051510022104081c1d032505031204080c09063d021006090c082e060509 59
    0x241d100ba9802800146020301d0520400c010390080c2840786d0502204c1000860804e40c1806024070550b170b1350b140013421910802d16503150702c000c9204e5607040e902d082c09000059070300444010680300343c0d0402210700c5040d103020901c244115031042d0903030f8030a04840000c005481d0005c1c0e0161041e08000030300440030380f0030080c89040940e407010150303019071001c0054034116400d4100c03016444180a0a05544002481c2400203043d07a80c0c29504041982d00501d51f0007002d0f01041c1000846a01c2e1005142c8011a03a9080940e694841d0315040440c070f2201001004565805004081c090318980410900c0c1d441d9143c0203409071075405d001e9004c41010900b81885083d07c114001400030040d6000b041800d6110522001100384c00214084101040c0280c80748103418049558010202c0d1840c80c40780000b103600ba41c000c0104a0706060415000704d91100c035180d00b08240e02d0406030364122880c4820a01954080d00103884901100c00107400794001015048050064681840182c10b04000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 806923282 1250 806922032 806922043
    0x50106170c0a1e0314010212150a0317090a0308190e06030f1302060c0a140f0c01110c03060a0b09100501140a020709050f01060906030204060206061002010902040f1d 73
    0x80741c020004071000c103d00c1024281182d007804103600348101c0191a92500c051070300024100b09820fa4001403030154030400032020035400f00301170b444d41940f4403003100000c00d03403030b01440080d16400c0340425120216170420b00300e5000074001010b11800c3d5550f450704c00950f400c400d6003024842014550001114016440844610b070300500ca6459035071081c034010030422015005102103100c1d1602d110058540b1801014290035220040c54440040d20304003083c0303040c1d000c010070307113070031880d9020300050001620f40340702c6078242464243c51070a0040e1503d02454401801d5041c441e407402c2c00400040341d8480500790700c0654042c0d4003941c03004000c4a00c849a0321400340021420164031034070f9a8000040c0c8034011242c8140c9031080e5840440c481a50016124540e0101009004004271034100b2502c000410701e50809600b094030f440000f070740396100100f019005210003802000414400e41c05030100c1e0764003c20820420160750081300090115000d00800746648025091824030000394 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 806924532 1250 806923282 806923303
    0x1061d0109090c12060806012d09090218041a060105090312130302090f010602011803091418130309090608030d18022e0e06220b040305010617 63
    0x1946a51646004500790043c03003141050700c200403070008010618407460045000800c3e40400400c11035052400c0c4801551002d401c000c60010348000d504184601904044200e8808a40019061905002094002030b03807041c40030071141100304100c108101101c0c2514060300700811801d003a91200c006480c98860858a1645607201c05540c0200c04e07412801041c040702d0101d8600391255895000c01d010076010b86003d405494550300500c01150309109030006140c40c1c43c1d0400000c41a0348010741821824002c2c14904e441d01c50031000d1944070b40c84c0816080503c42c094201501d450041740020500100f000c400192a200c0e0000712412580a140c080c3e5411201442ca04142001100c0c024400c030480a065082c0041c2c0400142c0d1300d020030f550b1802c1d2a0500311a00141103402500c04083c042070380418807032041c44011f8151165825203142d107000f41ca600043c001022000f480ba1102076000340c0c0c00d4400040c005c0204001034000e04200d60840042d02e40c3e04510071403140c0c1310160000b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 806925782 1250 806924532 806924537
    0x1206070201140f1503031605060f060105121302060909070e0f0109080d050706142d04080d02030603070e16080919080d0608120c060601111c02121201061d01 69
    0x1408290040c4c448044081c00b40d800608503450803568060640d081c005031001900c00350400f000700441c00e000094001d900c20000d180c0341d072030310039030891428a002028001d4100008072200c100c085440d001c040b41d1850400810000180c60081c10041014118854440c002d03052031f0041c0ca0389500600001080d44c010402074070755265441400c403141d400c2440251503140c2c5413421024100c0f840d07860b1070301503450340c880b60b4503503059190320b1050a0703c00e0303100030921020b00d0b007004089659402552941b4070341e4000541d807a240d002c0040c4c0344c2240d0740c00422041c50341009100415420b252104e01d194801d48030b809440c2e5902500701c0d150300d1000c500c8035620141045100c0000c01034001800310540c0703000006000c6403100c1e502880c060121104865007440005c2103100000e0800c49964032800074130b030985550403840d445a40341c007040c804000b01074202c034403250782c1503000b801490481c0c0d0505145940341c5210302d400082202c420300c0b6290200f404440d5100314000340703905801b5401d01c182c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 806927032 1250 806925782 806925811
    0x1e0303011217030f070f0507050c011d0909011a0901080c0f180f070314070f03020f040e1302010917060c0a0314100906060e0a0306020a03020405120607020114 70
    0x5291901000555504440c0c1d4000700c0300304a150080340014600444911030068000d00d45018050b0040d46c0850082040c00000e000707500009900240240c9480030a10380102007041c00002542d2102d801d90542d81e000400380308015119005504c880180c81010b800306503001a083c05000c0c0340d290a008480341074102e5100e1056030300b0480c8200c0000d0b44041c0c004012446440b503020218481a1400c0d40c0e941440d50a010803541c0c036004071030842e1540c5c1303150003103824008009041c6486480003042403603000701c0c020012030f00c2041a28014222580111441c2c506140d000101c140340700c00490106112010200325070003e001c01550145000b0001c00b200d03100c2d8600e04810340c04c191004410140c8400c6081041008090824026062424803594031410280100b080c2d0301581c002e90100300d250002d0303000540c0c40c081070408881e0842ca005a88550301c1104a020303110326000190044030158000c4180c01000070094400d01142c3d008000111804a83c028003020607103980c602d49448 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 806928282 1250 806927032 806927039
    0x70f030c030f0813120c051005030a0902060408070e0402150a02030304030e2106160212040501030e0304030204060308070b06040209010806010e2101150509060105070803130c03141e030301 83
    0x700d4815011550180800a08104c0442842500204039030480b950203243e41030b102e003c02a0084c04a0041c040449003042a0382603124000c00328000203095a440e580c50310240800d5403203a600f2603000c1c1c1814001d841d03909481d2101c1001d43c03007080e6001c038051014000e00040e40b00b501800c6e40d0b8903140c940d01452861f1a141c0b0700712142c08000c12020b034040080c0035041c807141c4940541d003100c00c000c1b00c040d288514003004541200700800c01ca040030354021804880d0003040c480d00b111b06494003400c00080101c0c040d42040d10314045e640000390090f213000e5000c000c1c41045c00c050b21000d4400c0d807003070031559288028401039011328140b65010804040c0491070542c0241074a12000b5805883d850709080d0007400302103040c0e43c0c9140045e00383d5403225003000341384180720030358094841500c03489480d007890b038002016407040e00f602a100000100204640e49031014400c1c00300c40c3c100340e04080950f26802c0400702c80701c40d20141c5140744500000390240c2d0151442c202810810030000d10f0444e8078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 806929532 1250 806928282 806928293
    0x1124042111012d030603120e0102330f0603101803030905030d060b090102010b0405010810021e04060306061215030219030203060a02030a0605030604210509030a06050702070f030c03 80
    0x19a03542041c59114901c03a00c07101040c3d01800084a0510740d540820803a1640c1407850500b6403030003071030003044800c2440d00c0013a6000a015500260b0014800300d021120410f90042c05103000500c0080c400800c0a0104d903104052082d4050481203060f20110401c2404840407030740a10280070500032003a60080100c3e0095102e031600d68014030590385469021a0303070000311141600b01c440040c8021840c2c2500796424032a0206090003500c0c1084254107018003155151440c0c0240d04d5510340001e0700031602c10100c0130b0301b41c08443c0a80303400c3c1c0341c6880d20b0000e400342005008481c0001c0c0c0c03001c01c03040442c1070350050b8000c110b0a84421f1908074115000c0c0303d41c0d64801c3d10803104128110750000b006071010003880d807285400070390068882c02d00e0b002c41020f40c1c4841e80010f200c0d500000a02010607183e59070031152a0070400e500c10460400e031401e4400e406010744555050203107920340014022181c1049100310103a9082d034080130b845443c501c04811450001600501012006000162 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 806930782 1250 806929532 806929547
    0x3142409011a0711131a1e040216051b0118061b0c1802030402150301061b020109180504141c08220c03060f020313112404211101 57
    0x10701510304a00302c80120b40108170521000901d00088070380c0c0e100058544101500b00541c18842124a810294410000c0106d00d408a890ba907215645c0060202c11701034000d54501121a070060940f9020001d21100c07800c24042011101d010801c1d00300183c440f61030381c1d007204095582035200e800745c052a042e40b107108190b10040445400c801050017040c3e04803900068065040c200f6005640d910f010f00c1130040cad501241400c514070403400d20041c072401c0e03000600c1c2c03114804606103541c0e0840785030004a0b02e070b00540c0e01c01181d039041c2003a00e00000300150000340c030940c01900382e42c0f0024403a0800690b076000e4200400e507485199241c0d5900940b20391012a001107508a4982586514580000801031800011100c0c2c000114007001080f0607400365608007803520700b0441c214945240040c070b4041210304014400b015450b008019a0340c0c1c404100302050310440151181000ba4140d117010b94800e014030744240203c19140039042695541032a40541d0043d9200c044441010042d01c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 806932032 1250 806930782 806930797
    0x150106030515151308250b0c07030314070204020712022b120b150a0813150c120903022d030d1509020a02010c090915051003142409011a 60
    0x10213084c0002803a6003080010801c099543c0c16644038404034500103a0414085a00190b024082441790300c00610000c01d5000407030750581400705000c034014150300418030440e00020760191011402c0014481060b00c074541d14800ea4003141c0e4080707040c81c17060540f00d42d5602c40c0c0011a41e0301150660841c0700d81252040c2e140d04200c0480e031060158001103421017907031344030042d4036404521183c0f2294080f6081d908204408001c0c80030641d1b41d2075518064001e65010000d854030b03000340d40c02c814460409145105400c401c100908210382c60001d4494501c0480c030708020b07035140e28290140c800c10a10707c18840c07060000b54a010b00101c01e10003d0300d00301610a1020120600c0050b5404090000306036092080d40000392403000c0100240c1948031a4002104191038858954103a400c1d122142007903c008807440191450340c2d00c42203002d00f42100c0c1010716002024284110a961030704205150421030000c440403184c40c00030b21400342824440da40c2d407840e001410034190501c030401400c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 806933282 1250 806932032 806932057
    0x61409030c130902040e2401080c06090d080a12110f07060b03011d070e0c041805040c0504060b040e090d051905070b0403020f1209030d03020d060815010603051515 72
    0xa14499000501162039134803002d03060390007500c110f03081c071102c2e621540d840380c00c1c041f905004d55041c220442d56035405800030034052440003504130104d60354001207a070031320343c00904242c2e00c404103000200140b5500403144c03081401c03c3c1d0f000208060300c001381e80007540a00b4403a41001e540d5201d40b0040c01003940d00d990155a00d0500c82c0f4a66004c4d403001c600b884540b40103103142031a00c2032602d10304100a011400340f10050000344003000382080c0d0350b14811685200450075440304c0c20100c004100365801554010302e410310018a8006e504098402c44107000300c40c00540d40ca10000c507840c1d445803239041c00040c0e803c100c16052036482c0480d02e0a01c2545103000c500344040b940d036060301d123842510150003503441035400040b810720030040b0b40240e406059240b03003806184008290b841182c0c6c102c0805068011446d442d40221640c0140c2c020b0441c00100d403518504080c2c04601940217004003400070303003880300003024a00d844040c009000d90181c640f418134180111209003d400100e411b072007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 806934532 1250 806933282 806933291
    0x20c1002090a08071d0f0f160306050603010801330b03040302070504020d02091e01140d0e070312140f120703090f0605090f0f0c0108042a061409030c13 67
    0x1008803041140074060310b5445c64000d281071407010b200c0c00e03600004004419595490701040100c1807440d0b0318981005040b180c03844024550801600074085680102d6089103000c00005803036401500710302c1c000c0c180000001c00741c100d010b54510000d82c0c10001d520350400e000070b0820020f41148001c6500030302910549240769240c00c0002c050380d004888c5c0880e02500450700840a2030100005040502a0070031000303030010800000e044012030303945200142d4000700301058280141e40000110441000c2941c13100c83d140e10344400f6030b130012651000010418461f0742d2162000c001281d10b154400c0c3c07007942c2089442c80c04e42245010040100c405c240d00d540303d000024240d060b009400310301c2010003207032500c1c112640b20302d4010281002c0c00f4682c131100f00c04240040c082200f01e644502842e14000c51382d83c60904e51a0800000c0e2881041c0740030042001d1404004a500c4040d61640e90303a4004203081e1010440881c00350381e105542c160040d0f0300b041d190f80b5252a0304d4888420348032020a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 806935782 1250 806934532 806934539
    0xa0c020d06020d02180102010209010e040b0120011a061e1c05090d0e0d0f0b042609010f030c0503070f112a0a06020d08090111040801021804020c1002090a 68
    0x90903a0890340d50792000d20780101d0b2060240808894504040f0300071f1000310300340b00c0400c000074488404001e405004507a584415450350b442410580c019036100c1c00411001034000840c68000e02c0045c651108d40304940a0301c2140d4642102110704000f4480c058030b0180c2c50030144200b281d07000720101841d0b01d840f82c0c83c0000c450302500860b0b22500c11903002d040e5100444c00054a240380d442071035445100c01060040001d10840031011115030062003a00c800d903a1898207405c1d182540d18410204104403254000000c2d0010052420f920f0a0780c03480c8142d480200180e0655106001200100f0400e000081d18039210710480b02011145280410410101c0170040b4100708580943e60fa24022400c0b0705241c400841c100e00300c03007100c06d0b56010143c5140220003512880117a100004002c88500031603000c800035000318840741d10940700e1036078807907440c0d000c68001d6100c00202c00605460b000903a65a24151080d0340301502110080e05810f500908410001e505c5064490b078021480040070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 806937032 1250 806935782 806935793
    0x305031b070f0b0702030105090303190203340f0c0c031101091a220f120809040203070e030c040911013b09150a06120905161a0f0a0c020d 61
    0x2d10003406240b10181c2d4403801c0d40140b509607840240420000d0307000300280002510344041074202044424401600c0c1d458820050301054001900c851031403074030b180b04a06601c010031841c41a500703242c58000901c01c602000f602c00f8084000090f1195800071780c20404140509450001c2440514241ca005e5403201705a88140d240301c074100c400840302007004840300c0340030f40c0c030800104651801c0d0b46107640341041d082c1c1e40c0c41e500d000304403841c080000c0070707001c00120300c040d10003401c0b0040040d51245007001d0300400f040e101c1901180700e0b108810040400742414490004080d8000d20795900c600c0040c4010748000034510a0f400607203010b40318100c1403100c001c00c01d01d0300741600e0b803c1040e0211180100043c0160182290b0361342441c0c0c0043c40d034690340c0c1000b10700480312582082114558000c0441c3c0c000c03d04c050014215001d2102c014507840c4039000064140c5001c2418600034080107001440d09004140400b51000070030030662180364002c4580e02c2c1d03001c0c0f004100b011010a95a40d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 806938282 1250 806937032 806937059
    0x319090f2d080c010e07030f080a050f222112090314150601090b090d1e0317100509010b030406060f06230309060a0504060b1008060307050a0305031b07 67
    0xc0c0c0300e41034046800d83c2590b0003030107544000200c038401805ca00341140ca41d601480d41c401c500900c40e290008140c00d03028054001d88440700482094141c0b14000c0c01e100600f0314078840010203c400621501090703240e001101102c400340f1103403030300c0911700c016541c404007807000417400d070140a2210340c0000083d40b201c081074401c0c40100c0c040c03c0c9034003011a020000c01c001904881c144280f05e101800303c800320b14195074180d4421100d015681d00d19040411000c050700c1c0e480b803401c4280303005c0030081c903401690841203200c00001a0000395144a503034580e01426000d400d5110000c2030040005014420146030010301414000500e44d69541004a54141542c014000314102d249a12401075908a0010440b10511512450340c50070114850b15280000c015030811a0b880020ae41840700660140e01d50040207481d40713083c6c03101c2503009459180210355084c468800d8900100d070904044080004a961210056003005050306041244201501c01034a45102c1c40c0000515417140c90388 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 806939532 1250 806938282 806938373
    0x501063e0a150608031e3f0708010b04030204110c0f240f0106030e0f0d0e0a050303120c0d02091c03081008100c0909110319090f 57
    0x198041400b2180300d0707825600ca40e84442c4840e00280720006000040b03d1144000c0c0c07402c071041d0b0b5621244c60b400c40340e000c014445480d11012141010307209003001e80300002c0a41104661108155036180011103120801b4010802034039014002000142041e0f0800da104400c0c01d00841d0030b140041c04850718160b600322950140398400f0401141c01e003005003d050601d4100c0d80d20150794a02148582441c90307041c0b080108156540c2c1010070079030402d014892038004003800352a449140ca540061894041c054003e02ca000820f0300000c252a000048408210b00c8082e1840156129a0f001001e900700e07181c074880303680d02007000e020700b680c90985401d42240c899018508402c4079090080c000007004101003142c4d44682e1060041800008040d202c09002c107a0202c0d10301f140a030201c6400702980d1000a100d400d00c0104140100b0702d001070361003603c07107030f81c840750410221a05400b92480c003140644010383c070304ce41c0404540c119056400302c00c84481911a180c01e8001c20720303120200c050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 806940782 1250 806939532 806939543
    0x504110f0423011505190f0e0a0b04081009020d0f02060c012903030a0c02060f0d181a040308040b0417070b2403030d051b0c010905010501063e0a 64
    0x20010722480c4460f1000f21510003080c038080d41040036480e86580d06c4850755000e0b4040c021070f24011117102d807040780d81401658000d028980101c0d501d410320200e5800070b00800409000343d07d12586d10751818846c051245800900b858000d404948038851002c008000c1a41c00ca401007141380c400e11400d000b48a41d0501d820101500045811112210140c104000c0c3d8030a410400200070300319403202c18000000d40454030180d4807100d200070300104c0d1241504040101d4100352113000c4c9010b50b0301905e501d050081c140c2100c1400810034a421b000f0003160001d010586000c04034011031000248160700c60302c10b00c4804855194282018210b402020040301d213246608108003d008030480e514694103050114a0b54000399140001c1c0c507030042c443d50103a40c82da2140003c6c0303071120300d0b8981a80c1842c120b0b0190b50f5002d15110142c064000c81c641502c5075800c010001407501c1c8101c2d6140081c4c0300c0d89601d030030009201c10004204000450880030400c0700001003240120051062074402031141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 806942032 1250 806940782 806940851
    0x20a031104050f0103050a020114190e030c12100b0307090501080a030e030c06090105070606090e03030405011a0901060309032f010f020307140c0f06010608070806040504110f04 78
    0x1a00308415500003c2c03860401c014002c0040000510014805140c01e80c2401d107100d040ea54000c4a00160080310343e2881d8004130502d1449490303800940082e0921815016959118102403d1240c0311044d8103141c800b641c086101040801c00b80e0340304102c1160000c003503c10340d642d14140241907680a070881001600000703c01c0c1d00701500038540c1c00c052341060340980701c800e1108000607602e001d00661a41030100010700c95003003224940c00100a0103065a04016021056690030794941084601721020341c038000c40ca52042c0004620f9031f9071910024406203040e070070303c5800c03000f604800c4002c4040c4072320b4502d203d140e041e22030500001d52601400d18030140749405606800e464203ca040c8036a1403041040c00f150960125000a40c04941d068403a40c5825084009281a61b9200070310100d000d22000460a01c0d44000441c1c00b0705050b58410925848070130412088903025a0000c05415a0056421090410030704020b501a801800062100c0d1348e490824880d000181c0d440c01c0399100b4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 806943282 1250 806942032 806942063
    0x11070506190f0201060803030a0902040b09010f0e0a020c060103030c020d0b0f061903020a17070e01032306060906101101052d0705070206070c0302190302040b0111060c0a020a020a03 80
    0x850038540807802c01c1c0c8024440c0a2410705110303124880a49070070b20468880a40740c080d519182c001d40782c602c80140c401b003040c1d03a44202c002070f4000c99026041603900710030301142ea8403c003402a94213000c03170388028000992941d1743c280c5945840f410300726001142c07030311044041030554540500c06c0240c10300b040e440c1d00d0030004100f00102d50542071009034144c1e07070307081c005a11344071100c00568660440c0741d540300705007801141c9400c1141e4803031200d0048407400881080300703240ca24910064011015405683c901c80c0d004e4644208803800ca0b041015400040c9036071904a9034072505ea00d040c20000000c0b0700c982e03500782c00e444044812500391100349951140041c2e00031a0311410303541ca0204424141010100141203104a0502a00c1440042000b105000010302d081c07005503801032514050303c40c001d401c00200c01c2c0a00c400d03841903103003460013106540103604000381c400b204000761060f42d44147c0c51070415044120703100d08610a66000c900140c6074084600007440c0a4907007115034255 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 806944532 1250 806943282 806943287
    0xa1401050414010b0a1b11241e0c0f0c0307091b0c24050a0509030301050609130908040b033c040510290904121107050619 54
    0x41a0300035030280d4a0550070514803101e030180346044d00c5903001e01d642d40d02c0c684402128068600e51541001c030001c006d5440c2013252011002095900c1604e10301c10055503141c0c9540007042200341d1210030002080070300c52003440c10f4055003c0c40d2600f601c580c1422901c8000380d14040800740b446015030711007141d41c00d8a150802a010091042280a000e2400503050303504c0c20154494a55081c8210141624104910003002c0f0800c019119168662800350040041c042d000076561981e01d186000c011030b01c080300100c1101c1c1660805090545402c841009220940d00d141d0460340c07001c0d03614440080000c0400005100030b08000c1c0c10f0303039100e003000c504400d02c440754443d0004203e8605000d091080c2410300c1d4216411161840011940d90b8a00b003460030501000d44850304d0501c0c100c10150403201c11825040b40c00502101074038000228000d1100d10041a40c01400c20f40704450100000c600c03480c030f0303410103048100c00d8814103542c52001c941e09070001c00c2c0400500040000580c1e0781e0340e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 806945782 1250 806944532 806944571
    0x60e010c031103070e0d140d091706060a060507050a02040606110706110601540501030f020609030f06151804031202220905060108071701060f1103030a 67
    0x141c1c44480518508003200d001e0320b102c0740943c17a1401000794060381010300158510019400c0007075000d03a241071381d44a00c010220f03c8a8090680030f50910400c1c111444030005003075115035400b038002070743d41d41000c0c41900c141e002300400700d0b5144948102d640058580740100402806552a803a05200290a2050070140c00f0380080f0304108400c0c0700034022900000302a8119005500302c04d0305803400c500451181104542d88000c54138810113038100c5040c00d040d80c1501d40801050450803c07450000d50000e8481c00c1c400600030b403200300454400b610b030440040a2000300181207482e9001100b02c071904040d411110100d000b16405200106400e01c004503c1e0090000342e620004d6142594019080c245078007111004164040b0b041e650030b160300c4072120584d400c081640b000041e6920312503405440c3c01ca42880c00500481e021601c5076020b10b0b015001d480030340048480302da080c0700c403c0f0b03039110b400300d0880d042091848011703001040034801140519902000440d00355240b03203145400d030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 806947032 1250 806945782 806945801
    0x80a030e0a05060406050a02090409050c1002010605010203070602132c01090e2d0312011e060f0c050c04060e040201110d0c260c030d061a0405040506010c060e010c03 73
    0xe40044070a20005080440c4981e4484d50003240062162140f0b00184000d00401005540103407a010030201072000000da610440d03d0203c4600c174107003104140c100c0c00c0c0c800612413103025900922003000050300a4002c2d15145602d43d0304080c46640e40c14804a08050030900300390100c0b1064051603c046130000c40c1e41c05010700200c20300c14940505403455803040c0740650400744050004181480032a42c0c0100f5011047c5031080765120540a00d040040303a20a00c5100d0340040c08121602d210b003807000e60307031080b11400d844420002c05881c0094541c580d1080003280d0038020031040305103540da42c3c402d14014101ca940f940c0014502440050001c05112440040590295110000c0660b220071000a041e90003803103c0f0003546041e10f500d04a01004d042d001c8400e00210700c8410400c800406400310300c0b8100804e224a40c1da0308110780c42911b00300c4291000030400c20050000317050540005070484010325181e80b14040c3e80c0ca60b4000c441c000c10608410717035103d0113400a125414000d0700c458 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 806948282 1250 806947032 806947061
    0x250807120c050609031204060210060909051207060209060f040602240c0a0203090405040f020102210a05160f12030606030b1e0d05330f18010207050109080a03 70
    0x214440381ca90401104542c840c01d4450702c1c0000c1c0740680d039201400060900480f11400b00d0715552900d00294a50241441501140b403070a40005600c0560703000c0e02d00b00742e4102d0701a0106a241c2000801154440513003660610340030003100f2a075448840080584812440020342c9890422100a04100402014440180b507150b044c219404c402a40381d90800c40d0421802e80c0c40c145a0001d0b403c0d030040700041a4498505000c00003400f942000000303015201340d0944031000034207000100c901c8009a00050651814080c500155005000400490804000306068804640d0300e6944003542100c0c202c0e40d04e4031024503000006e42602600000e444141014088006604041003148070401c65003d0910301042c3d90650b0794a80c1101702100344e80050076a68004040c068450501d52151202c008442402803038040ea080d1064100340901100400007546444105c01132011989003002888103542c20011140028000d20031002c465128482894840c210000060200c0b2140340700e60b2203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 806949532 1250 806948282 806948309
    0x7080f01081c0f0c151b020318040504020145030302030906030606040b03040b160e090f07091203080f06010905031c0504051305060301050a0c090b0309250807 70
    0x12401803aa560307490b044224940b44840c04100c1404541d0b40c1100d0501130022040d00070030a825210a800004001458004420300c2c2462118100c0e0b40341320f08401e03c200c40319030704881c0030580b5042e003242d42c02a005240c1045034a041c0308062001000d079000b807492252004501200060b0380004600041040105003170304a451500c1c00307512441203402c010710840000000070042d6a9040aa4004d090013116a07030710381c03425280c8241201010742d501c01d5041507951007890301e1440b0305801c8007510030241200001d03031100c0070350581510018020f0303010700c1040700000c02c01001010060300b00c03900079034030307040c035400c0c02000d403408182c01802190401501000c2440107860004214a441d07d076101542d1449042c3e185c12038583c061130b040340e0740c86143d21701c4020458040790403480c0a8071045008000c11346410507a082102d1b84407115001080c0100d40070094800e4000c0036533405a81c030003e0320781209442c0d5491451022030000c40d4003130074288000380500e030300400c4440c0c0a0044e40000341c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 806950782 1250 806949532 806949553
    0x3030a0614010903020d081603110c0301020301050a12140111040f050909060708090109120804110d0b19020706050406060f0b0301030c171603121107140d051507080f0108 75
    0x201042241c1c00040e0003481c14070340d01c6c0301700800e0700f040f146600c498a1094840502c60f00d03004050f40c8000d00d10348424440c00010b02d000303180c103208032412140000c1c40c101c00103103460802c40307408841c008103440b10020310b464540ea0300005e010301c010424510f0303440365545050650105200119400a6008031413080821000701e02c00030b4095040300c01c03401c04a07455540d10201d54050300c0800c400070000c034007180011031300c1c40d04502d91901451013501c80103041c841d18010f00a20903282c080c044c00283c0c0c608081004240410712100d02c140c200d04000d49021035a072160b0080e580d040c0c0e81203403501d550340f500300410000d00358200e002d055641401481c6500d103880751201400b2070301601006402c0b0020440403814100695407221a80e000000d10080e0b0700e04000c0505550451a40301040854010210100c40482c00b1410b44500b04a5070050301c108609100308180304201c106c601d40704041d000e180d003001c07040c801e5204424940e502c006601c0e1070000270611080c10307801100c0c2640440c40c0403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 806952032 1250 806950782 806950787
    0x160509030a030c020a0b0a030510140120011514121204050f0f030109051b0406270204031b14040203010608040209430c02030604110402090405070203030a061401 71
    0xc0141900b51900e40b40c2d6500d58000142052400c0e0f100c03c810090001b4000360081d0035800140c810320a846c1c4920400b0381d0b91800c0100b07002610300d4280000e0205120030414211040511402e0700303444000240206141e44000004a141d0403200a030b0100b80300034041840c0c2201c0c9921111302100181602074102c44400600780540d021b16803040520f015140720030707151038581f16560000100248142d418500380103031a580700401e0300d0010f0682d110009650300306801044102e5000e007410b400d9400029103036640100750f906084a9030340d000c120001c0426a04459007210310341e00704000607003600d020030b2841e40300c80d046040b0b07005600500040121075001180309c0d600c01c0c3c066803c0300c01f40e6250003100b60384417440c24409031090448a80c45032840101d8a06201400e00786003044c080759490241501d055a480310000d46c5507004800140c000342814068121000e070103007001d81020141400582079400131603076140168808402c03c54500e40300d01030000140782c2c40390324403550300b00d88000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 806953282 1250 806952032 806952043
    0xc1e090a05091c03051510050a030f150305060109270b061f0f020f030c280209010306022809061b061d10060e1605120a020316050903 59
    0x240d001580ea8030005600c0500500c6001100d40000c001d00310643c683c840c01034000c007416241014030051507050802181448894051002180e40351142000c0650300700320301800001c1c20410a103500c410350702c608090640b0400c0046c44c03003100036100c00c0d03041005407412030314440e00104c04082c0024611090b5101410000e02161300081c03504510765581d008a1104c81e02c03142c0070143c49901015580031507510214000040b9204d60a46070070018121003140d59026102001c04903070001d484946c0c1c1600c81071014010105d071034080c0d4000070200e0300040c212410036441603490319000180c01c204140032804a4982600e4014413050202020b040201b42e520140101024400b0250121000c2449d8a50410030036510190a0020283c0301c110941d014521030308260991180c41010300c0ca0021500aa00544505000782d16543d0743c0c020384c04896a2402d41c2ca0403e0140810414030008501c0300781e107116201c00d00026039030b0b0411481d0080d820040103000c0c030800c0004c0c800441c5659001c00c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 806954532 1250 806953282 806953291
    0x3031e070302190e031e0106090b04090b06091b0708041701020705070317091201090215041d0a06150e01140a020606060c03040b030415060e070c02130b03010603050c1e09 75
    0x40c84d08040d602000030a24244c15004043e40401c5228071541000e08150072031010784000080600c0ad03908840c0c24002035030b003041d0006084800400000f11a810416000b48d032050320b429a0240e00820401080d01c150b1014005544040c00024103103c0103050441c08020750700c11000031450082030341c8540d51994210b00008050a00300041d2181442c0c0440075150f072000b004142008400c03040c14a60300034040381c03204900584508010b0140724002e501900d0403550400038101072903a0740c0d428100b500d10000c29016905944510100b020071035103641500200a5441c1c0ac64041807880001d007606005120344210381e00d007085801c211603030220301c190b04031340291034141d11620720800507411405107400095506102102300070501100e900380410303800411008102070303030b00c0d0071041c0045e501c00c031074150120303040c142c1e02001801c00049c190169179032a040016601c024000003400c3d14019407080d44c45600440303001300d075494480c9040703400c00706452421281c03c120b00081b490a680c01403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 806955782 1250 806954532 806954537
    0x30f0c0409060801060504050105010c170a02010f0515120106060e06090d0f051b030c01080f060a09180201020709020408060115051312200108160306030503031e07030219 75
    0x82460246040240c0e009001d0142003400a81d0700c1e604040e008041c0da01c01d0506c620300700000021994003a902844000d0340101820305100c3c5503805101503a403180f90385104665032003503205420042403045600404500d0f0524411a01703043c00c025040c011101001000d915044080007840c0d0031002012001e9400e40e101ca0b00c40b040c803000240d1b5055074850203040d1200403940003042040100d1440e12410540c100365454a284506141e9070301e41e000d036814041040807001c501000a000c0201d60b00210040021600c01c2c0c03544981e078251980040041c141d140302005c0f1808640c1c0500010001c0c0500141c218209441c21820715603410307042c441d22030100e201c100343c8040a4410700489041c139500c00042c480d0381c0ea41d59901c1841c1401d001d42514492140c0b42041c82c1071180980c0c20594160580d20392500380c0fa035484550503000b0a180c01000c0c16a144400000501d0074009180b00790a19010a000c030682a090482c00f8034008001008162041124141c0342c1c2614012a03a81807031403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 806957032 1250 806955782 806955811
    0x40804080105061f0e0a090606080106020d05070203120d0209040911030c0f09070806131505011403070f140408060a0209180c0d090606180c020c031207080d202d03 72
    0xb90049406e088958009002e07403402c0400215207182c1203a901812990203a0888002c2012150701302c42c140207100000390f160f044421085100082d0001500a11400201c0149041030703000c0007500b11070700c00c0c0c0c04031645010724016604a00d13052084240e03001e810b94043c1d441c560f54400003200640d00401d0201030280303000105031075480c0c12625103260614280c041241e4605080e4489854429103c1e0b180062094802c0001d540903007002d4a00425250312132503100c2e08128000d445d80002100300c0e855100e014000010902020402613009101128006a07a99521414401d0511480303a40096102ca69010b020308403400408440c1340c24610180011321030344034a44003010f42181e6100c15200e081d0b0402045120900342e000a00c9074095808031050a0f0b01001499203032418070b1030140a048003030051f400810340c139800801c034881d020040068040b0712203140d20307070001000f4107203140524080b40c00051210400c510544507509242e50104111000d8420103032840001c003052900c0846 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 806958282 1250 806957032 806957057
    0x140a020315061201182c010f02042601060b0d0c0e090f0a2403060905074e03121517100c02070302010804050a020603040804080105061f 60
    0x240720441049000422841e91040e80d41d82110032a4003e0246845421504031007510a007880e1140c6414280d11416800c1100a82071600700140c500300342c3c1403915500c0c1e030415828181c980c80200007400c0b40c9494072000c2c00700307041070701e5800000c00b0071001e60343c1c54120240014a51001034503246100769078041030f001d0424008031258440041e040b07400184034810302071460500000e4600c1800400e000304455680300d5580d9002c2c0d03540c2c941006044110740b8081c4003188564028627070b41c9001c0c00403140c8480e80d524030815520888190081c07010000034030b120a0405d100c141414680362030038001070384214080b28603170528200800a050104000c440b01c22401590400510120721020102090b030341c2d01c212003114880441111a00c5c007548103c0c040300041071280003c2c604c91507004056150550f070044d10007800242040c0d8452041018150045c1d075040d0046202d0380c4206c003400d48a03850000c020b400c1d6200503000c2171080281004070b41c0d0b05483c070108645002024640644000300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 806959532 1250 806958282 806958301
    0x4170a24090501181a06100f0201020705030c0304080712030f0815030d02100f14040b1f141206040b191d072c071404210204050109140a0203 62
    0x20640402002d075401c100040c07141d007400034141e104050003000844001001d0800c0200000011200d0310343c0700da08202508402032060b0320200020b81d25000041c5002016225140f4503002204441c640f0382c800242840102d606201642c000c2c0901505600c208249650140550f405020500108446e0f080010901118064982d40c0d4100c0501a510708041082c80251286114092000264104100b07640e0b90701907407090300105927510741040c0300d9855a42c0d8004280300701521050719802151001d45140101c2d00f6641c0051042000c0e02c4104214407003400701030000f440d2580c105030031040800020074840c0085544c08003c881ca02e5013614900e5150030002e09208070054100e030700d00308080700c4410780001e103a0162810301c102c3c0500d00310304c0051001c24015504041c28101c0e00300000c140418000e0956100507d800c036031842c1025200c140c504160034050a04c3e01228014a81c05015802d00d40309042c05441540c5040c080a40c5524030203681c440040c20003c401039000001904810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 806960782 1250 806959532 806959541
    0x3060406050d0605072c0d050c1005040305010c0f020a1101050c03040303030b040e1c0302070203120703050a08010e09070605031504050915090307030c030e0d1704170a24 75
    0x1d0700500d500c94022442c205070b0000c01044a094021a814840c950120404180480c0c3d48509940c61110f80d074001100344080042c03c058100d64030300c02c9a14850243e91000117243d01c2c1151661015183d51131800c00e0b80c00e495a19422800b4020700c0403000d00115404a001a030071030304001c1448140c02d4450040f90503100b0500c03020030303500000c140401010383c590484d954100e4102e0701441801100d04400391211000e0040109841c050480640d8590098000e040042c0c0001e041d035042c20300a9054044992001c40120000303040003d40801b51500020304902411a10f2801d540a2034040c0e0401d64a40381d83c0100707000d000c0702200158000103042019080020081d2092240e4104814204e6441c00c0b40302c2120021381d800742c0080c0f4064000400c1d1286d09070190b9800039203a141d5101a40d05424411070140c004082d10080004140c1d410030030402c108801080640d0b5510342480400382a583c1200e1040c00c1d00000101710104010483c0c091120301403403403d15481c00f403c0d14820052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 806962032 1250 806960782 806960789
    0xc1707020a080f091e100813020603010311011107050105030106030e07090e03070b01120b010905130204090b07171b0913090c030b0c120a020f0c1c2003030a0203060406 74
    0x75000001c94605020b2024040c040c0381000313641700803549096410b10840003c400b200e09400c031500c0c20a441a0358820321606030061844081e0b40780c08403a940100718950310903001556800840c00700c4000950303100c02c3c0c6003482c0c11030f180a4610785041000084c5140f0040c8103610401d606d554001d200741c58103001007401050446d104114541012100d103031684c000b1041543c001024100000f02201d00e10548050541e00c1846007401380c0c2041c1c20b01c00204005404c0000b9914103040c91801612140300c1c0b000514007a1150304400e2909140003400c521010302d40c071010310295001d10142c1c502c0c2040000080c0c201001c11a1500c4000c408244510051641e8400b000e0400403070300b05002ca50b0088000340c0303018140a030a66525101160a540304452060714400a5140094a07480580d806050101c2c0c402e00d8940c40c140c507081c1150314180c3c1e103140b0840784644d0080a941c0d403507089a4242c459000e03505080501a9002400545a00004041c0c4180d00d800000285440d0344e117034404800f5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 806963282 1250 806962032 806962043
    0x504111302131d09120304080d06030f0c050a17030909071b06090c0b072a270515030a030f20010b0a0801290d060e1b040c1707020a 58
    0x841d5a1010f07032503078980462003040c080b03440040c00f154429001240a01d040341c002e644e040d1450f2119a6240d030b0301d80c40102802e00b00d40d902d8001200041c074016800d031a080c019414540c28600f8101000030b6105ca41c1e02c81c03034030046d5a512511410740080250741c40900c0803038220f046039a03215010750b00d0126400c131103100144030500344001c11903542e00181302c5501070041d00c003440e80c4441402d40c0901c1404000740101361340300240090311800f1200760300d40040310140f4422032a580c02502c0700c40c50403550362150640314130b401076005000d00c0c030a547c1c0c88150010900442c0700454042901e45021007400b41c200700c140080054441d0140310010a8041034070178506c07100400301c80040c001c0401051b070503c500d41058001654090501441d1034101003201c00041000901d543c00440311410108030b034110003440044004200d55120385120b003007400d406012482c000d00c108d9500d012510851910551501444d02103241d404501d00d2611801250b0590054882c540d0607813408440c80c0c0010314 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 806964532 1250 806963282 806963317
    0x7050a1202100b090c0304030215011401020c0904020f211f14040c0b1b07090b190b0403020405040f05070f1401090305060a090c08070909030e040504111302 69
    0x20419120102400e0396415800d54694801071503004041e00d280c400c401c4e90182c1c01a01041003060380034021a081071007801164104951054800700740700d801d0340220740b20000c20384d8200d240c2d41c0500101303681c0722013110814514541680040d004140950301d56010768031078044c501c00542550429111a070b504400c940f110917950340a2120707003d01a402c1e5840328203100d068403a40c076001c4103042c00342d0303841207942141500f0305528070069044020320b60711380741d04030070403083c8041d0512400000c4c050300a00880d04101200901507080b00144a415144441d10420042651a50207440c203684e8101c402090300d0b00c813424058440a0300a4018206001d2604002213003030311251408205d461007582d0384000320641d0019641e500e03441c40003400740d030800b000042e400c1e1000e51201c1001c9125210f000368060f280c65405241c80b5507a041030b03003030300d40d42c108a00070705070029195080110121014000d515055031940641d0425204c082d00a0079805490310100301c00e5016a510002030a102b40b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 806965782 1250 806964532 806964553
    0x90308031311090411360412080112020f01031d071502150402330a2010050604020f0a0e100e0d11030a121d03190b04080705 55
    0x1d1901a1508100d810002c074100c00c900c641001a02c151003240c1000a5007845241981131158016103401800186203584401017582080d02001d032442c04002010b240303017441d2514103420303140050007507042401225401001f01c1040c100c400d40d865581130f65008480e10740e8800682c09041d5104a00d43c00c180d0074188046100c5c80003408034110b076400d80e42056034240a601c02d98550a400001c459020a135400040c0036080101c1c1d03c4e25034200d215100300c540c2602c0b560034903a0424801d9040340050000440e40782c540c4e80a944031400d5041c40000710500842c01d035010350b4450500072034400203515603000410035681d0380d059442040140395210380e0740c09841c000801e00011503922502c20025000d189016903c84c1804c14404880504a03424290003503c8501070640340310602d690502c80e2300c7e8020f00080c02c08200c0c480956542c1c4407031142c00b11400c1d03c00e12a42c1d00c0e10541c3e000794044000746a400b000e040c081030a03660400ca01078002d07200c07814100354911400c90090918440c002c02c0d81c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 806967032 1250 806965782 806965801
    0x2705010603021c0c17060d061404112e1e0207031e020d08031506130e070f081b040909050c09090304060801211703100801052509030803 60
    0xb003640c0403a0743c001401d000c0420052500300c5414660f43c01c001401c400f20f9a02106803100801d801100c010442c0b0640b00082e039443c016581c8070740100103075102000600003004045103000070398082c00c4400781e00e00844580414510402203083d52403e20380c0c103184071140c50040024011040d0100c03000ca200004001d006580c80c03140344030440e410344d11a19a080c20301820a1111210b80e401000300c42e011549440c3c1516682000e44002d88000b81203c2032441035031400010154590421015980a0b26010070f009080100074600402d000301c01c5410204260700400666005488848101c8920160586800701c2d014540003d50201d260019620a1010010b2007030903140cac04481444460352081c990503203d0103140f241901080d8158014030401c613030b07003041d09441014074240040001e000e0711000100408a4000b584051002041c0403d1418501030360002d855044028840ca043c100c0da456031403080015030035002c0d2410130003400460720600b030550003140c01803c0030380c40b402d120040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 806968282 1250 806967032 806967037
    0x20d050d0e0405100b070203070b071b0909050d081506070c0510020a0305190e0301090b0406150303091505070b0c0a0329040b0310020a1808060c04270501060302 71
    0x15680401e07003400000d1a00e1900d4060f0a00ca01051010307411024540351444003140c02c6000102d0307050260f44004100c078010303a0701809100d4060015000f481400c2420f01c5a14400d98002d001603a0500b1391500105000084d60300b582100b42c40c1540b1980d5808202001d4514100c280c9075100c2c2e40010080c041c04440e14225094980c1100c10400d00e007126402680d0b2141411070050115109100b40600c0c000c0303144920385000114205010800d11304c40010382103485012044030910f40381c00521041c0600c6200c1c0105d2452001c0c40e00d148241940c40240181c01c0d01d2003601d00c03c0c6000d10606026a1064060706c0810b40d1150010358107040644100085401c031440f11000a85402c0c844119110f401c00c03500c021040c021008400201d02c5400d00001c1d00302030050755054803640c3c0c0740340302c403425510062101300c0c059035426000e144042c204e109810310760b61041c1044d0b40f14034103020040c0240c00468046a010b031406e20701c030b003560091200a002c007200803041d500d41752070000614560540c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 806969532 1250 806968282 806968303
    0x3040f020d0201120c110124090c0c02060403030c05012d0509011b020d080f070f2318010e0307051c0309030c0605030a0e01060806060d03030207080f130f0b03040303020304030c020d05 81
    0x20b01201d400d400c1e118070f00c0700000a0414400b1031410082100279826400440400620314010110103001d4002c100c0ea60320030390013103001415032012401407010070300c1750007562011641045e0007410344114441115444035034a0380010b54800100e90200c03003d511a10f80e064488186241c001007a880207034403201525000c030302040740d000005008180d42c0b90043d1040d001a11411810390180c0380807a15291055560500f03403660b80b0b280c100d8030500f00302170284040da1008060490f01454001050f40303000d40340c5140a688038070000d104903550781e050680303050240b0489510641040c00c00b2107494071140e001400d0100c3c228004034615500c407005501c01c120300441403003001074500056080f00c032107224020040c0c20000c082080d9251800100f50040d000349400742c10018076840d14071095010b50880d081c80c14001800d03994008000ca2840300038000c040c4c0c9001460f207060120080346c80300600003800c041d0f0020014041501648080c03400c141c0250542c02190340c0b91074900d03540e51900c0e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 806970782 1250 806969532 806969567
    0x30030a1103120106080c0909041416051c15060e010303111507050f1b030304020307061416060603080703181a04170c060d2003040f020d0201120c 64
    0x4801290544000045070982d0a400714048410303841c00e14119110403001d0701c0c40446000c108000490341d40e40350b1303407a070240d0700036014001018446a0007501c0d001c245010204c00440b1240204043d50ba0b9080c1034148882d80c5070410b000000501c0c26001082c480d0905908051403c4400300303841d410a11000e042c0d0707105c2d8031030100e03e10101c1c641d03554410f0703d01d0808030088041c90000d1101031241020300494409c03072000f1b904003603070b610846200c2e14201005d8219640040108001d41c901002540000c0c0204c1c00e14120b0039038684000c0c461032003946c00c00b8050042444c0c10300c08010b5141d204800a5170458401c9840b0001850001c000d84500220044505030310080030942d085043d22990141d0060b8070007514003071a00414002581605101035081d0046509064280d00ca038001001c030810700d10f100040e0400c8031030042d02d1860702d5000d42c03800c081c1c09004000000d20001c940103d03c0790112810f868105079440101c1d071030356008042e42140343c1464105809160040c0e0524080e00252 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 806972032 1250 806970782 806970797
    0x1d0f060a050a1103150f03030a020a0b0f09071e0e090c04050105040c0e091503071203270303053414031213062021060105040530030a 59
    0x14100540d00200f9032600d41400c1040403418180040040c445603c0000e4108484101004002030560700490301040c0544c1001c510b036000c10025803c01c0d9401210344140f20483e0800e11252a51078400380510f5106250174008024103004500b240c100410386507e00c030f0280c2c1f404040c1e1b1900c17480540043d601540c102400410079103802e00075456194143d50b1202c1402e507026042000d404c4000c3c15140400c0c105981e4a0030301c0c0c60502004c0c0c00707000710301120f003207000c02c40c130b030007402c1c242616042900d5116400c3c0d20801c000000400030216034051411584464030386202640b040d41c4a5400c410743e03000f2a005407441003c2e4442e10007090b000d900480080c0e0460100c2c0354480c480c11851f0002215680002460400500d0109024a02032070700001d8214141a0801c1000c440211000c249500424505503030000c10001d081403a041400103a11402d14500280c914044c0703002c1c00d84541704291500e100d80744c140d480301001c0101c0140004440000309a010b80341d5003d03044200005880 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 806973282 1250 806972032 806972041
    0x20a05010c120c141614240705090d02090403050c06070807020d02060903040e091c1805030c03061611061306060614040306111224221d0f060a05 64
    0x1607482640f035144110701d8246400000034126017400003594048900c0324041c01d1844400c0c83c1040300c80040d001c106520400784011340d2000f80440802010501080010400d5443c0303600c9403540e5801041e8107030382e80185600c0310320341644c26008042100585100340b40800c00800c0e44106154003802c0c994007500c00c0043c400074100d888107002c84002e180c0d80e10401080081140980c100d5511070300c0b4030190303801c4c11000140d842c005600600314000080515103410643c0704800c0200e4000c000c200e0042c007040742c0c000007107078450500603c405142e010018400000d603008402006c1808210340586200e460410580181d140d07010320299003142c5040e40100f2082d01580105010102619090781828a140c1e1200043c04880c8856010b4003018030000c4801b42d030040020f8022004c1543e03881c941000101c1d01d02c100409013900e00d00c2141200f420032080318105500b800c071800e407010003040011103c540880e8081402001c1c072100d2281d1000c500f001c200c0820103501580ca48101030009456 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 806974532 1250 806973282 806973287
    0x31a030a0b01150201060b0a020105013b070e1011010c08101a1c02071209050d0803060316081b0a06090e040f06050108030c060f1312020a05010c120c 66
    0x8521000800e000003040050040c5007043d000d21401d007030948004130f1019241d64994002d40c000d44402c0000d41e44510050242807100713460b8400c1e1464444401d01245c0c1030b80008010400405201100300328604082608a80328061802a00c0784c0903107035005510450b0401010300c4003a841c4403480d546010940e01c111846404200d00490386640e079140141e051000305d2651883c410144044085c1c00c101c040440001c0b0740c802416824602001601e40c4502d003003102025050444035420087e034590b042c48070381d444100032000c02d504408115100e550341c401080c07030300740c050183c01d20485040b0307030002c0c51600000d04c101518000d0032160791a0703011501845286100b6015000c003003146108188081a5108005a4854052008110300514139111002103460070f81280145070400a01900c0c18501008265080350081001905078a441c110042c00e607000402e00401c80c80e0b601407800c01440c4200000d0051680060003002502c14444024029101d0100701d000940d0510304024005030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 806975782 1250 806974532 806974543
    0x605070b0901050106020a020909071d0105030d02010627090c15021b0901031415011e06170105042f040302041a030d120f0905030a1403190203071e031a03 68
    0x5c00b90780090186890540c20008010310060540c07145100300c18001400980705200540c900c00400404c80c410b505000900d801c140c4441541c0e8207581c1000420055181d2000040c028801080b08a1042c0d410011450000c0c10240c100503001c03a01ca40404a4880e4a9050b880f4070048184c08a45441c5044ae0b0284041c281141341287d016540100410106070f0100b40310815002110a4540300c0e0301035051054208020381082d850302500c07211071200d0800d443e0210700031345420306200c10411071004003800701000500546000c0c0e034441045240340c01d6008100b81821942c00e02816a04100040358001d03600240b01c00c2c0e128a090407000b015410660b8850044100c1c050090031a4011501095420014800024200c0380e41c0d1900c0307580c9156079109155070a481303000615640c0c0d18103103000b0b1810b480b0110424014204200b0712800a440e4002010036440c98075001d6180e548000d41600e042c0b880c042000304a04480b51300520840e859407009845120070501120640341d0360b02855901e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 806977032 1250 806975782 806975789
    0x20d0804091401062a050114190213171f0f05070e1320040603020d0608030903031207120204031209140105161b0e1005010c08030402040b01030906060605070b09010501 74
    0x1918440c9802c1d200112020042000c448400200780081800d039280350848030100b0404d01c1c02c410040910104002c00080020004144031040d8140001c590240c0bc04014134410707950822074034140d10072100c00034403c104172000c0f0f01400d0b85982d048800c04070094100328a0012629107400c6c000340c0c045000d1075503144c4810303020308160fa40c3c0740340840740c8004005c03008028080190000c0700041100300314006001405169901580f6030300ca2007522025102c0d07580111190790010700000040d628000166106040d0404003d00c258550b640107950350700d10014054000c0307000103008400e122104800921024003550f540c5251561828111050501e0b180b9280c0080c01c2000b424080000ca1a14040524000ca0b0354440358001c29041880c81400c642c0294413044403d81008540c2c950040150001d0a0a0074205615051035a409159110040c0001c2c0b286a4880445003580d110f58040424258466020008e40b51600409030054004880031949a14104002049558103000f0366048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 806978282 1250 806977032 806977037
    0x13090216052a0f041d0102090a091109060a09050d060e1614100e0d0302151015031109040f02030114180117031201030b2706160c020d080409140106 65
    0xb241c60010010f079428014842c42d403080e00c60050101d11010100c02d0944444000e00040e514000b02092020040440d0f0025001030300d4043d600c400010280100c0314003490484149542d01c440100036034041d00c2c181c1155411a0000034034070100b09030381e8045107549480c64100c681248c100745c1c07000082000d03801030708000090081d450865042c60080072003c004a401d001c070b6603001c4000802d134004000c0d07909800685c0700c040301c0707400c94038640f8220742c103d08490040d904079410681a0948c56802c0108041016501d026804d0000d101d0700c25a0b81d9400d00070401d006401c4800c40c080b001c1d40003801071007100c000480000c080d528024403010810b01c104015421a6031038460801c5d5400d0030301c0c00dd00344c01c0c0410804410002e84180d1035038003841c41031400c034145045c140780401011895180301c4084c4001c410031040e4291001404a60058a002141c484510344c540111400300c03a42d24001c0d00b1464140b089010040c1072805001500c864003010800c2c0308200310140c81c00f240030f11030b4801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 806979532 1250 806978282 806978353
    0x10306290a092106110a17040f050627070f1404021b070801110c19030e030708010f0c0c0f0605131505180102041a1309021605 56
    0x802016000038040c8070364541001240d240c2d0700d068016840e05404402401d12402c0154401008528814403880081883d444d0341070508003180607041482a54490030901000700004040261a290132010306a0140503183d03503081c06050104083c4408602d41a02c10425078440e01218001a0074811222501d4980500518142403e2030041241d441150400d40070401c002a40c802c01084000d5034500100404d90f681c508454a404c485020b010b1702c5201004002000610900040019015038086065417014240f0315041d116014030921454040c01407940c0020b2040041d8003102c03140b0040807040c800c00305900000c8806c00043d45c0000c100607109400e580c04100e03680c0c400d9034030059094501d810f65080e41c56120b09001d5650600d21201d0326403080200c03a10100f403da0308140031000c000c0d400c0c07071b04103c503001001c52401603c00c40d4a83c08a0310122070300c09424010020701040350110740c0c400b000d0b00f4203444907050080c140c51605c10002c40e051844041c8801144484c000b806422 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 806980782 1250 806979532 806979599
    0x60f0106231308011e0b0103021206040b030a0615060908031306050a0e0616030314040b1b090a0305010507141927060806011214070c020d0506010b0702010306 70
    0x101d908000440b003070840c4410008910b6240034800c2d2407150010303000c10700d040074001400c142551020740c03043d4105401840485c40c0c0405a455494000d00100c80100e04c40c0c0c48800802d00d801d0148501401c440d041c400f0541c1d0911900c3c0081094521a69404400c2c503200c038402e40e0349116803030407000c60041c40c2c00d082140c036101d400a401c1c429160319001700090a0500010801c5d004000101d0084009280803c01c1541511885c200705040d200298040e1400b40c40d000000000200428402c450100c03643da4262118011150400001070603102e8190312400d06c1e500801e0120b401102050b4030300f841403622003005084c3c44190042c0d00103255a041b108600b1117500c4c18035030184048102c92000008841c6100c10403202404140d0b070742c4c1006180c000c0006221240070201000c4a134034241d04a61921140003900d0340c04903060804010700c54003807002c2402e171522103c02503e01d0080000201700c2d100720400804180d03000b41d030240b00c19030b1511101c210428000b000100c2031f104104055 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 806982032 1250 806980782 806980847
    0x3050d05070201022112220303050c070804090c02010b090411041a040e01240303080606030606070b09030c0c06180f0a170307050115031203150f0305060f0106 70
    0x140041441813064440702e54180c00350090902c08590804004000403a50034001441010315070b40c07045c40c4014829120b96000544040c2004440c0c01404241c0c0340c0d00006e080c690711404171125613902208080e0398507030f01c181e01001480152208c00040d400d180d800c032620320b0b2642c2c40600568010078210005a059020000100068624411000c445112045555545100b055010480c0000104400d502d001d07140c0e00c0f52040c07410900c40701d44c00c0039060021076480b421003030b80400240d803601d950351101c20000f40180034280c00280844c1160307041084100e4003101800100b840001243c0c940448041000614011044100340008040c5100c1c03c0e540340400600081403c080c1540c6041611643d80011034919000409000d500028802d4100300c002d214014103c148641b43d0341c03100b8115561181d03400d04c0381a00354101629160002060015290700c50b0003071080744617060340c0d556240781c0300d605d90304110f4500384801d44030030001407003074050090040000090341e04084164202c0002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 806983282 1250 806982032 806982037
    0x20105030f100302040f1506020304062705060a020f070b0910121e14100308090d0501020408070924181802030f1515030c0d0303140106180b0403050d05 67
    0x2060852840c1c0071001001d070b05c40744102100c03c00444800f29000b4a800c00001d000034499100e501158000c00c0100034103940300c5804800140b650020240c1d68078014020901c0884035081240d00000004d10308507255000541d45583ca9408010340d100300d5074600d40419140942244507070031550b4544440201c1348a240b02910428002c540010300c2e0100c0200c0080c100b0340808250700107641d0b0000c410b20385802a110a40c4040c1c003503a04160b0f107082d50f403008540d0048142e0030b401241c40a9089040100a4040d24003528580080715003180e030b10400170025101100719030854131034010b4494000005100104191840820111118041c0480880061800340b064441c05d50704082198016501030000d0000e480402004010054134164481e00b082e2015086614a50301100ca50800d0303280400d20008014080340c03044c81c4403a150805034090701a0462070501e00700340200120382c641d00300f13210f0044590042c40b031a038a42d80b5004115000c0c8110b0201602c1c0c0d5015207501690140715000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 806984532 1250 806983282 806983291
    0x305060303072a0905090d0305101805010905060f03070312050f070c090c05162402030f071b03020309130b0a18230f0702030412050307050706020703020105030f 71
    0x1241e14007a0355403940000d5200c2c3c0700ea009200c400e01c1007910802d9854540c00c0000d0001c896042103142080401940c0e2450103072480c10903d034440001502c1542d11208000082c44400301030483d039007801038000020882401240760b1281350174040f912608101d41c592040e503c014000789201803d54588a082c1040c20300d000003006402c001e0000040b0550001d45801e510540c01260000d04110b00e1401f030312120200794040200a00c1850381c080607425812111640002d0342c44c4900740c81241090b4425045030132908802d00000034040d090461020180c82000c02d580c03125041d03400b032130255090700764080c005401a841809024190302e40a00c492100d1140c100300065a68084404110001c0c2250321000350501034805030009450b0034051452445019060301c60008526503511100240161500c280105103030b000882180c001c00881f0080c00340402030702d008614900e082c5640e80c2c42504111542d014030317100080e40500000d00d00e0240c0b58161102d90550b60f56180e095007840f001030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 806985782 1250 806984532 806984539
    0x609070b0a17250306030204050a0b030d0507021f0f090b0301081e190506011e0506040311281a0301060c030f02160605031e06210c120607090f0303090303030506 71
    0x3d0b40519604001004180303103620580340400ca091650041004884009248450090401c9003c008075607000c40d415140b00c0803030400c203880343d50500100d11282c01c0c2c600d0403070b4420104021151841c1c0c2002400c85030f10344507078034900050f440c2d882c3e11030540000e100d0200c480d131051300703000c040c000f44a01c00c982e20181c4508480b00c00340c0c0d001104076000300c440010f84168102c80300501c00101c101c01510b0b103005600d003402c40414174220110b01c0a100303520000d03020f10045203058690f5a50340e040694005c003990444c580c1044102220440281c40740304594000c1c040003951201c070304103001600d040b580c19841d980c04020b180c0d2000c0c0c551045080e264001c5001d4580c0350405928014007034005403c0da541c66035100e1808001401103841c01105820410100400f0886140c2c4d600c040a1000c010309504001e100300c1c011411850020983c4940c0c0d44402107030f0740b94800d0040050301c04e01c0380280740c0e1148600ba40d05e003140c058100c403a00001c3c1c00144000ca0900109009402c5103402502c080d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 806987032 1250 806985782 806985811
    0x10090c061d0d0812090109051504021809030316080f011a0f0c062d04110a170c03070e040b04021512070c0303050702011518090f050609070b0a17 64
    0x203400044410280c03901c1210840404030741c022095020a103545d40c055030401c02000903c6864481543e10b000950001350b005400400040071520350000200c080c1c441402d407480981001202103403641c00458450031100082c0300d0341e20a843c451240075001d91054107014030741c1d90070320540e41c003140a82c0d01881804982006404440300c3d8110050101280c09070140c041814080f2034080c0100c002d1b030a9104540040000709142070300d403040300343c100ea4002c0e20300b0700222030400441d0f80c1f5041c0d0740c030403071010440c2036183c40901404107a80424017030840c01d03a010707a07442d00c0c0704100904040d10b01a198115041c00034006040c6200c1c07004505182c1d900072814481045083c464000d411a101f0001408140c020000c264040c0130301c980108043c002440130050014400c0244c456604c503041c0c0c6600b4041007528260b0700707079000e1002203401c518000b0701d22400d07007825a900c85c8180d890307010702d1180d2800050590318002c29036a500c00e05e075882d00380b98400000e001040070703000b800c3c3c0f103048400c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 806988282 1250 806987032 806987087
    0x130209010e0405150a0e240601030b0301060b070309182a2003070215030106020c1e04020f1c060e071215061106010b0a140a120609060810090c06 64
    0x4d5051920a802404011030041c0303000004904002d4440d850b0004501c0a0f9000c05140210b0404998091800e1800080c40820744001034050011603102e02c5440d5400101d01003815031000d001c00649a0042c01e811581548500400803240188803241048108400607903072011aa2044002c8c0707a01442d01000002d81c0400540300f42d0410740051020380c0c0002541000c600300120294245201d0000300390466143c030401070741742d540701d5180314460791015000400031800c45c56130800c0c004010f8011501c078000448800314503440786a101c9010a1080c00340480181680110400c0da5100c000700b00c030341e484104044e140c424801c00250340b0b4036206d00c4141500c0745c20030345280040000d99036101c2c0308508100c1d207508103001078000111610701007142c0c3c840640c0001e18400d511101c00070031940c03441c804100f1921484e41700d401c501c60b58201880040e944046422050594840c0703000da03032405240451910844441100043c80040403010421003280608403081c140c1ca5641121907000c50f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 806989532 1250 806988282 806988313
    0x50f0d090b16031409190c08070e2505040e0604140c0a260408071e151112010e0702071701020301080105070f0804061104030f03030c0305130209010e0405 68
    0x4032401c190881c05920800b10035a030501a210108203801100906405d000c072080d03494071048449a50010b0b95014032608004648545100404500d07090300c11035a101c00c2c0302c2c440010160792802e03035402e22540000c1e25140a40b583c1d40d0246079510303514070341454910101390b0540000c107031540c050303035a404100c0c00f0200380d001544142d0b0403100076955151800e4010345207002c5407148074104542040000c120082004505422a4014800d19100d400c145010301100c0f4903509508158901070800004009480000b11354003c87e1035814006c40303c0c0c1c18050b0a0354014a080021080c01c0c0703000401076006c0c0c1807103941e007022080c816105a2a1110301420710f071a909040080140e6002004004015080c41826080b501c81e00c2c0501c00341540c0e02c0002e0079405c01810240600e07903980d119444a01c0c070f000443d401141c4c0183d0b120300d0051541030140091400349500301c042402c22000888001e22021400b03101a401001e05455034200312140c4070301100284100c455210341e50700280c034101d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 806990782 1250 806989532 806989553
    0x9121e090d0c03020111010b01080a0e0c0a060203040911180103360b010501080702120a171f06020105010f180b060c0a0c050d0c031407090608250501050f0d09 70
    0x5004100e8407102c40e19500c001025603103401c02c00c107020b07490402000303140d030707407003503c41d1341000030302070003054800c00d011070a1f060030021405c4641c0800b41200000740e440d0044050000c945034000c00300a071188100480c01b06100d000002d4022416580c03014000c0e600940c0000900449050100080503114841c6818aa4440c45200503458801141c0c4100f06a10880a01400702840c0100e003905081002943e0303052043e2482c1c2c4203c10108000c40306034803c542c0d84414216840c02660300341802d2a039980034200c1c0360448c6801d000c01d4a4003007001801401118102c58114504c0420286003a140c43e000c025089001400f0644030162641d45640c0d99001d00003820000010300fa0a8400b46400d0502e03240540c84140034854085109012416441c2c1d520304480e00015500b42c000d446000e00740c140030345600210704080c079143e40402c82800c00140c050700e240390120341c00c0d050442000e140002c202c0c1c41c0314060010b0020050408860070041c0070340441100081c0c00b2480984543d1140c0c0d41d103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 806992032 1250 806990782 806990809
    0x100501051b0f0f011802030a031b0c090516030c0210020a02030d0f0b01110d050306040506030a1211010606050301050a0311132d0b0a051c08030115020609121e09 71
    0x5911030b603111840c83c0c0080c03240508014080c60703408072000d902e80c086901c6d400600ca010b024008070380d40b117081105486029009842e0301c080c101400503264072080e00100829a48040d41e1003191031010b028501a205d02c842c00d00345074005101401c200744a80c0c02a604c1400b20f4400c5000a1104240c030003098003c801c8085018100410506800ea00040c507500c03c0101c3c4e568141c2c0000c4582650580040403070360444825100454146ea030000840c0c580201c06400400500c120007114150b5035100340120320800b0001c0082c0041580c0c0d210448190000703000705644510001d800f080050660a0780b0400400c002d0080b201110f4018038a4040380d02c40401c03161000c142c4070f10b24080c801a030003500050202004200100840000802c844c01040d014a90091120f0f0414944054201003c1c2d02217540c407000040e503075a1149030f51a003601d51000008058416031001c00d10615012036290b007503260541303000b400c101003000305080402c590030000b00d0030303101003001e64000d8881c01d102007801f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 806993282 1250 806992032 806992063
    0xd020918010e030a11120a05070609150b03060a11090d02030a080310061206031505090c040915050f06100e0609060d0c08010801150b1b030a110114100501051b 70
    0x700c1003c01d074080d102c244441c20950031904400d04480070003003100c0644d0400c87c120319119403101d503140340c0000205255000540b010119080741e55054100c1c1d0005603a0030010b4041e0307080e944964540200f41e03000c100078901340722000c0c0034805035030500503942221607000404079101017825454009090f0310965083c004001248400e11001d500b054103000c500807500f070104a603d00e5903c5078510307500100c00d410030054441004c40c01060b020030441400c8000240100302c4400e0341e11305920814448240d1180c003509010000310b502031816503182c03080d100034000f400406115842200e4201c4905200c81c0c0c04503040c000c120702a12054041d2400c0407150360001082c0300c68200181c00001c050f40440701da03a04101c80369001d03191b5001200f040b00c136a02001a201c00e16000b4107110138403824401c1090f0b200209904030f4990b4014014070388080207030020410004901c0d441c42924104031548103000e1400703d005c0199510450050034106194048804650b0b250b104090500d42d018440c00070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 806994532 1250 806993282 806993287
    0x61203050304140705090c0304111009030c050a0e0f040c0308181c031d01090302130516030504020a14221b0305040c09090c090507050301030606050f0d020918010e03 73
    0x1000480d5544142c411001c3c401000258075000c000380d00680018003030031911501101207801c000b40036080624101000b0441d5007034101c0780c44010400071030b03440155085041c42c81d000525007040b400150584028550402c0c484e070342c884005032581c1000e48103c1c3c64840d000c0000000c604280050001c3c11a52818076100040b0b9501b00318049200400c0a01c030240c20050ba100001c1c0c00845821221b881103409418826600c4016510b0b40c480d80d10180d040f001881c0030141c103550a60085d44921044107000b00c464209100c228203e0705c04a038004d4100441d0744040c4a0303802c403c81c1903450240700501c05140114800310a0801d420140ca0703a0000799110110743c2d00400b42c2d105403a1a2a400e850200071a140503110b14003088d80318440d801c03159a440c803203002400424446100a0544205c0510144c2403901c001401503009210a44445240c406c0c0441e01e03180c01c3c4036441b4038042c005c1200c441300700c0c0384d02003200d0001c1c003500d290445c0600c00e90a810b0040c0038001c0b4003079050a40042d58 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 806995782 1250 806994532 806994541
    0x1050408030a031508030c0a021017010b041a04210804050d05060406052415070506090d0206070306030f1106040f090608062203140f03150a06180b0705010612030503 73
    0x45104c10b55402003102c64105004284d010741c1c0015451178499011130790503003041440d5005441d11400c0f00015411140c100c4000b280f81a80307240104121158898944400440e5168041180c01640104180030034098030300c1c40b144590b041381c9103803280603100207450503a89000060021044010071510703a00048200f00a01100b881f48507488004480041683c8a60207400100c8611440f0502d01c10050400100840d8207603e003510b05055001d021940241040007200b80d80f40600c0902800600c15000040c00a6110303000384e4045952004e940c0036074138803135662443e0a00800442d1900004140000a21204050800d00051401401c0010443e08003141682844d03801042401c0104a401c0700504842c01002c62700d2101d0b41514003248085100321070ba540c1c510501820156060020080c420f00103905003080e141090100c41c01000d00740e540d041600c0c0c40504009007100d103046803204100c40a2158010001e0900c1040002002c0b074640814120b1300741c100505400081c000310400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 806997032 1250 806995782 806995811
    0x110f030304030308190c41030c07050a0c150906080103080d0902031e0606060306090c0d090203160602061807140307050303040e0103020a140915011e050d06091104120201050408030a03 81
    0xc200c03aa00c00ca4001c01800c5081051002c0080d0660307010047c00c0d00000046580045000340c400b002c3d840000c1e1240cad03080324100110180068003810040d4040303c0c040212082c040c80891044401503103400f4000d030310f144c441c140c094014000010006442d102a90f0040e038042c0a0a80e0f45602d580b0a03c00b103c3d5801c039000c2c0740c108014001c40c0503400030400d0003041d9440c3c80d00719500003000707586545d6400311403016201500c008e040003501440780c4c0000210028100b08800151040b540c21101c241d594800101e290b110020014031464000031010720904041c0c2002c010001b0001d41202e0321940e40b40007180c5564020781c00510900e03404001402180381c031803c540c004000100349071080000c02c80000701c8003c0c000c1e00b51215a01519001109a4000c2106485010b1584101140051090b070301410680c4030014031050309281007008540d051141c460b9100c4481c43c0c2e040d280c10036050055010001c0c0e9080c8099040c00424403000a20007070820050100c4e081035070300410410040c0c043c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 806998282 1250 806997032 806997077
    0x3070207080a170901200a06180b041e0803040b090712210c021e010e0d11190b0c100b15031f0504020406020109110f030304030308190c 60
    0x1a50241c102a0035038000c00d580040303140c1030f0748402000581e02c0300c0f00b80041c0d03041d2a40c09404028406403030f01101800348080340c02040c00b030107828203000404060702031702c03091059100020280360f003600200700451070010905181220a070401021940c803510303510460341013220704a0700644642c04100325040280303c07110003082c45c095042072401d066550505208580c07000201804c011a10189006204a040843e00d6401400800c0364034141500700c0b88252203001154089540301c0c2840c659403c010004200d000e403c2400200e0b4202c6e808100b00019411045c0c0c044400c0d0480c0e030200f0b02002040091118101080003000d0406640d4a18019a400b030a0443d11968490070508074074000c0c0c84c01c503903118201e031440301780c00c0051003140301420039103800268101e80302060100e8615015071241000c0da0042c00c4c8928501d81d03001c2040b0000d4000c50b015501038100780010400a4003500d105034100d140d102d44001c10800140e805c408031001e400d90640020240c030351680c00a48503861 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 806999532 1250 806998282 806998289
    0x1091106040608071803140105100f0f14031c020f060702030f0a05070c17010b12012f160b0402100201050105030705060a090f0b13062d03090c060503070207 69
    0x34410304061800c94050302c40d0000400d40c0d018000c900790301c13002502c50304540c10046d41c0c1c0b1400c003c40b51800c007440f45000f8901100c6113480b02804a20104600e150964004125140c4072803581c08541001c84803500b000b948080b4603003500c00d08014644c0d070000c0b10003104050f07120340c0c01403142a440503142858000050410070a6402c2040454000916641142d80540660030321555038101072134100280820799010f910304807444203081d80d0b551010740000003070920449003004601800010310342290405a500311054809180400c0800c4000e00840b440c00fa01440440c00c0c12200103040c20b6581205d070303044504041d003000300310851402d410a8141e03185144000c00084d0705100110b0340d03401150007124850f5102140031040c56100b801000e001c8c003240d02044400594030400c4d0038007504130308400742c612840c042e008954103100f030f01d00c407072652007500d031031808800c07020910529810650180d100709602c403c814070102e0980440b0740d004001d0355860a0303803803a0100000b41003428540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 807000782 1250 806999532 806999539
    0x408150c13051c02040906020d0b0a080616231b0303090706110a1a0a0b03060c030c09120d08040210030e0705040c051201080d03181509050309030f010911 68
    0x1041d90000d5030074601c07105581050740e602c448054082000d184108920000039070003030030034170b940c005c20505402808600c07038084000c3c40542d035182c04011100c18580508070036688010001400c602080004000042060504128501c1c001800030481c488030000d04850a000007111311071140300c009040414010320f03003d11b0850801a6101da02c6101901c41e4000304903000c1c42c0e44148541c02d102900020340c4c0f0031a5080400503034240c200d48003074200c1f1110400c914190038180b95083c0456828452a00003a040d0b195071355059080010360090780d1040e0704100c0080d0b40b01040741d01007001c0050800f4584850926240901c100440c00c20003203410001c16080143c01c07040c51000182d0201030360011600841d003040d00711012101e03401448014403240c1070290002507e610041910b601e20200c550b0140002003003038000d1151024088001060341d60200e4003680c9040c02075000c02c101601c00c8003545c1c58160340500180c6006400303a1400480d075583c1366140704000f5900b4050000910a5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 807002032 1250 807000782 807000787
    0x20316030b04020d030212071406010801020408120d06030b071d120a1509020a030b07020f030325020a0203010510080f07060c030f090503031201180e10020703050f0408150c 76
    0x55480300d01007500604004d000d00c01c074150a1081500902a6600400315407101c5501c031641c0341007000a1341d02c103940909450060704004291050103001302e40036911094001e00b003880c507005903082554040004541200e0f61400c0100000304442d103801d0240b07580741d403219a1241d04248016500054456041c4601c81c41190031000c010080b5191410517005000411644d11041d900c5020f00400c0000962141d50b4200c048100b000080e5110300911180c1d0840720101c0c00c441c04195030b884240c91912440e020580d00b00c00084c0c1c20b4048101441c41c920580c0d0900e11954003081c01d549094400c810f40b150400c00500c18000100b28510402c07484000070800c1511385034000c1e00310030220002038100100c44140d01000e83c06051500010400a8103c81e555500c50307036016111002170240c4940140c9001501c0c42c03072440c03805400400907000002c0c08441c211001300500a40c00b1941c11002c0c01001e000e070f0405c0c0300c049006000241f06480107032115811100068004203801011a164250107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 807003282 1250 807002032 807002039
    0x20a08090c10030c0c12050a020f150c07051e070612060e13050f060103050d0806031f0e0120070302061e06040c0504031506050306090f12030a061a0403020316 70
    0x192040080d40025038180003982200807034048800c03149070117000e05031080c0344640c401142c1e8400c004054203445542680c5a5813000c44440d03440c0c03814902181036440c507240100344014485e00003445218411000c403410480f103480007074040e840ca000709204581109000b040100c0c0c1240802c0700003400030404002c810300704122183d500201501040c0704d803604010401c204041000020081000319007125550760303491030540e0b034840c03009070207100249060001c0f609504002440400f43c9d0400041004a0355041c2c420030010010750752004500d640b180c10441c1003901c40104031000288010703c180d60744086081c082d1610740003420750001c05103040000d0558010040700c0c0c40d04010201d802050000f9808130440c0c01c0d0065404c0a001001054425900f41e500c941c040c000b1240160261840b60f44c950083c5a110506444010000e8210740c1801c2c54250107980116400201c00c4d40c00100d06032503809090650311140c14807030b41c0c084001000d201390b181c10400341c2100040c19130448225070a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 807004532 1250 807003282 807003289
    0xe01140105010306081213050a090c1b031b050321040b100e0c0a090f090b030c120d0c140a1406091609020d110d020d050606090a050118090f020a08090c 67
    0x60310742c6d810200100100301405441c44a011940080500a141d22401611848813100502d621070000780468bc1c0c01c55003003a898803170003102540300d816448201c0c0300198640c0c0800c40d2006101c045445000400c0120b11200c0500050403410708244072075407407031516240082c2d9410b0040c10707000b00740f03110395410042c0000700070640703500500d0f0001045e114003e11009a80c440c07c035400041e244522044c0c0820b004150350320542c02140102e085503c0c02181c2800d01c40f26944e562a0b000d0a50491001d44129a015400340b050b6544522208298030003803503003c86c10075405031000c41e56846254200380002400b0072685404c00005005001c03c4102c0d1745680c100f50200b442410749207a0086110703803015203a5801100d000b00d010100a03511a01d414842009500c003400440080c0c1c60040840c040d41040c1054503100000038080d051110b040000640c1d0360aa05400800322041c1410046202e6003036004484025918090140e10740f54000d078060801d80d402031500500b0340c41456190306565 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 807005782 1250 807004532 807004543
    0x170609070821070606170c01140a03090f0c06271d07110604031107090b06031513020a050a1e17090115080a020a0b040b19120e0114010501030608 64
    0x120381c0c0c0030614560704282480c49a03402464000340089141102c00a0080106e1900080742c152080a40d1150540700c0300641d014000400c02000415050000c0a81e280c060b9010321885070150316240d508024503036a001500a00d9001500001c8401c411804420381c0e112440b014949015030b844000307030415008001284444664010064024000c100d40c18001c6c2c0448a03a140c8050a0714258640390070080c002031410540c0380072070301c40d260000460b41c0403032140042003000202100d1464560b1084161081000789255510040d05071032008001c515100030090130356907459031502e441450b100a0910300300c0001c134040c0d24440480301c2c1034140d400ba484041905001c09000343d81e40b90032451a0041c01c03841d2250b4081c1c1c80041000c00d030540d002030918013040c4219005812662192280803450103240b040d440f61010512080c184202c5258880d0019a168034010880e508607080e00c42c250b607104d0801e950165036501072400089848202075002d408282010310030a4a0000382c169101c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 807007032 1250 807005782 807005803
    0x50105010f0501170405101e1d07060908060411040b0a03030e04050115080610090503030c07080606010c050d03050606130e06040c14070303050411040e0d0e01030606091412071706090708 82
    0x1242d648501c4074400d006501e4411b02c2050080d810014444c40d810050030858510380d15003a2031140c422b000440f40d20801a0200f070f2030100d80940b0031070301d65649044070343c0c2210094683c01522105406444e0b280e6030b501304011402541c40e601003103028000c2c8401c40c2c0040e0424040941e038a41004a01c3c0c3c2c000c010140c0101081e29003041002001e03008490720b0303040c1c0d0400303036043c0000103800f16038a80004802d41500d080406448207600c0d480700640c0d0901d013403100140140c00c455074030040203000394011640240050250351624108404070a5041c00c02c1d003145200400600901600381000e106d00900000b503800d00007016181c84c29420464002c40c2c000400300350b240c5001600700002201c010001c00c001501c20b004403908400308a4803803444002d0240041d1003041e0050036503119020b10301c00c44031192035260300242414040f050361100d1950b003035003200e5100440862000104040c0c401421008540c124160422000c039092a00c0682101181d61040609108071071000c501414007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 807008282 1250 807007032 807007063
    0x1e0902120403110d08070e0f1e0901050a120f03090503060717090c0901090c0c0204140405160e0f07030b030f0705010f03110a081f03050c1302120c0307030207050105010f0501170405 80
    0x1040d414070009040040401c2603550004012007445060274240110104850011100740303080b80c1c0c85c0c8061140d11240e521070260541d201d14100d00200f1800320000d06014002c0c81c00d265100e0f00e800c0404d18041d070555407a0001a0314068001080c0018081c5d6500303d00c5000141c08450340202c001085024103005103c5001d13640d40051080d24060a0f1010304954040c0080c09400c1c04052181400c0700200c405a4490140264500c403c4191942c81801d4076001064903217152602404820000401042138042c540c0e07600000115507020800b44030654155401049014200030004110140701c401800c1458200440922500340002c01c1d0b030441421840c1c0410716990320464030010b4819260107140090f4240d03c0442440030124081e44d0041080e541b00c5050001101c0800c01c81c824580c040440546600104a508c0031a00095821014620f80034bc14680076848840c2111401e038012126480554020400344d42c01244907042c3c440c400481e15014a002e0f1100c0761a000c407001d22a01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 807009532 1250 807008282 807008297
    0xf0e010c021003020d0f02040806060a06020a03031d0a0b0a060609050112020a0311030f0109050f1e190c0e040606050405010504120f0c030308090c09101e0902120403110d0807 77
    0x442d03c2c0b182d07050350125815040140000b070280b20641c40250b206005214007400740714005100c5083c0340c2400780484440381c2c0180842009918100c00818685800c004803088200196902e54030800100000600407000b805660406560610496095510003c140443d00e801041540c0c0c0000407245801c0110a0260380e89610001c12801844800700301c0d585141d010052144540f05a00c1c058143c46001d5004c0040d5140e040314034180d41021520300403503951303618100c140283c1c2a42d2070b540100410313805c00310380b060a4000c0410380b595445030a00007068088000c440d49403d001d110001c10440c03d007a07103040e04150008005105901030308020800040001c070400082440c004440ea800c4008803403810b07200c1c603006020b805c0544a03e8842e01c208280c0d400e040ca48504614010072500e503c4d4400989401001d83da40c002060206210700303519000000c0501b40c500040c414212414042a444e180500d4040c1c0b18041814559500751f00441c6210f4040340c0005505801448900705040e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 807010782 1250 807009532 807009559
    0x903040e09010f150e0a02072a170d03110405030706050313080a082a09040b03010b060a0f020601060305040c0e0c2217010506031209270103030f0e010c02 68
    0x1800340c81a24020741c0c0f554900300003801035800e05a4007400380c9152a1503400681c641c104a101030780108100649a200d003035110441030006010341082e003e0181c0c40d600380030b95a880c1c482c0c4868141408074001a0400505d01030302c81e0b4584030708100c1e900411252810241003c1c04030380d4400c09070040d101403010020104240b0303c04e21280222140e40900f20655138a00314100070100c41d41600e65886008a07551000300821804162160045450f0207050501d40b8800c100030140211282d50381c1c041d5079940b804009601c031000104055040c544907580c45501740740b0b0007480d000c8140d211100705880c0006200c0082c801f0306604c4d0841c1c20b643d48840c56601c85101c440c2c082d100d14601e4500d4010f540e10100b644000c510030103400c88000c40001c440c1e8034402c1e0320321400d85108507079482c0c0c15080440c0001c128807260000d0044d00c0b102600c906042d554200d080000e800a04080690070a8401c004008140d0311410741000c0700304a2030080c40c07041000001900918228100910860790400c40c0c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 807012032 1250 807010782 807010801
    0x5010c0306050315040b0c2203200d050a08090105070f08040509010e0c03070c02120f1b030f0601150905090702012004050f0f0301110d060302030c010e15090d0b010303030e06010e0903040e 83
    0x62309030004a80200c05907645840c1001d910722006c003d41442c1c41d2628050249842d1380c0041007150080040c10414603071359103004103648100c648034184541404a00081585007140e00c0c1400d20481c46150f030341d4248001c200801c0016440040d405003540f0800502410603000d0f2a00314055003010007100c103c51001440da125044c4c0c0401e1540b0581a6440b207400380065110030317003500310904580c95130490080c192680d40d04c2c00603074010f6001c07200400420b00c502c001c6001524075860006c8200f5181c00002d10a14401d95504c00142c2d16070058540e001f1000c44981d070040d105c100d03103d2409140401088101000030986407207062075140304c8a60b618290000080c8840214a507581c071100c1148980003000c483c00309a009100b880304042ca0765026058150000c4170052000d0b0a001018580900303980c0580241500080d40e40d60110001d81000d0140e40a14840c1d00d0100340500c00c5601103180c10750580c0300c02c02544803007083c010412000b108035010703070b1300c0f088000c110ba80c1d8500301c1c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 807013282 1250 807012032 807012067
    0x1b060c1605010902150703090609060518040e16140a031104021b0304080a0b0a060b03180a06060f091a212a031c14070f05010c0306050315040b0c 64
    0x84d40110006405c902078403511401003040611a03100d6111150702e40a00300e584007c1c0d80915400b04004000c49021600807850f6004030ba5401040071850048407040c1d00c1c18201c090440d032031441690a01840b0018040095599040c1e040d110003d09610b107413220740e103048800f00f0881c040c9600140814400201c01d50844480f40b9580440303546030368a040c010f640303520341d010035900d140303006010803112410341c000d003001c5130482c00c402401c5840d4810f50019040c0750500c55136a0703100c1c441d801030014482d03009501c024100000700c0c00342d0300d02c1c2c0324521050700e0008104490402042c250101035070f03141400e0741c0711104288511140b109a1030201d0303140c42200b2050b03c265000320b020351030103241c3c2081d04107442041079003501d4021510302486c1c0d101a0b241a0207001180d0400d00141030004104050410702d405a04c1e120800207003522a9403c61b5501100100002c0d00c0720010b00580c28100003c03120007404454a81840c07619848110300504090000000b480000400c1a101900e0a00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 807014388 1106 807013282 807013301
    0x2072316140a0501181d01050108150d030e010509060f031608162d031d0c01050f090402091c0b06040c02061303051e1b060c160501 58
    0x541781041c800940c14042c2c4540f0340001074100c900d80c10040311101550f035403002941401c00051610340021b04500031842d10503080545074580c2c0742c030030304440e8041c40c00305048141000121254450400c40c0d590100000c00d0000c420101c500082d402004021707506115800d0740c0c20256440541103031101c0c101c5d54902c24030b6001d503000b40e078003900102c510041c02403500000d0004a518501c072a5540001a985003180350f50b21407540c44008541c41c0e13010080c00c1d80080400000c10724880c9440c04a1108800b04120805403150b806480240c00014542045401150488252080c10000c107417141e126110110f0502c0c00c0c18410400f0903c80755024022030b0f0b652400ca500100c00c0032604a04001007004844111007800320320303051801144c07108940d00d00300915407030140c172143c15503503695411130b07801d0060b9902c900c01210b5070080c904203002c00e09106030901d01e004152100 = true := by decide +kernel

theorem cover : BRFrame.Cov 806834532 807014388 := by
  have h0 := BRFrame.cov_init 806834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 806834532 ≤ n) (h2 : n < 807014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
