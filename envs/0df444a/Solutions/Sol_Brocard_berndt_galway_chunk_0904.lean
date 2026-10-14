-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0904
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:39:01.011114+00:00
-- url     : https://prove2.me/submissions/aec34e78-5384-4386-8f44-50f1fbec137d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 162410071 ≤ n < 162589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 162411321 1250 162410071 162410089
    0x70605180a05070f120213090206071b0e13030f08060402130b0c010b01050301030b010311061c06030b060103150512011503031d06041401030f1808030118060602060117070302 77
    0x8961507040300f041007280120300c592020240c4580740090500c0ca0760360303001400310300c0c404d03104102c0d15407a40780e001d06540e070700029160745541000201846400005032003000ba8528010040901e0440e400300e0410a0301c0c4058401181d0316803a40d054034520b01c4425a40340400800f802c0d406602085003041103c0340600850007002d111805907103c1d0800b044030703130940f01c5c440251030400800303000401c0810300c2d03255000d04481e00304a07190400810100410954842d400010103050040c12115030002e1503680140f080320700038440b0750741c151134150046041d40c0405500750010002c40a05002c40d03d041e40c2410300c1c400001d0000503100b4581c041c084860f031841e50040d008241c946054850302040960061502c0d201107580c2c40c5003070b040080740c5003811807040000f410140da030105206030075a50351100c64050102c08015080200620f44019994401d01910500c24100d900b1041c505065000d1141580c00503005004c117a0b09144119070458400d1001c0d20451084000c00005621040b45d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 162412571 1250 162411321 162411323
    0x10b0d0c140d030507080c07170d080121110604080a03050d0f140403050714010510090b090106080129030112111f0507020301110406050901020d0c0305070605180a 72
    0xa100316452800c4070700020300701c98038a0035014140c0c1004290001c3e0f03121007128206580290495181e404900c2494542000d42d0412070345d131030000c01c11100d5160700041905624120359070340d04c003580e243d8110960201d4003603803400c00c4200300b0000600140c01c6200f045002c00002c2c181d03034105959044140e00c2d14006079015000302c0ca0010f1101c1e02c03aa224050101c3e4041b41540a20180c10801018a14010024006400c020003c1102d1f4100318015410b107610541c414020b105034148904039104010003441031207416441c0108040b141d04001e074140d0704960154070b81c01e045a00e030203030303d0f02080300d401c01c0b002d0182d1060b2102020007039414040d5000e03281d04020300006543c030b40b07400e502c1a560001070030300c01d0f841d8040100280c10140d00c80c00c10314003e441c00c591101178a20119014150512903034001c0e0324080ba02007041c0380c2c04005403690400981c2244c0003014800002d0714a010f102e8406800141c0170400701010038080c0d0007a94108400502d600201025041c54034142108a44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 162413821 1250 162412571 162412583
    0x3070503030f09060915040b22080d0c080f15010203070c081c03020712050c0f0307060504021f0909020708210403030e0c03031b01150608061504050102031803010b0d 73
    0x5003c0958010402c0f141c2c8500400014a609290243c4240d4080d60080004000301010b00004850803040c20150304046164640c1c400000c3c52443e100085800216942e1121894040c2115156206500540c060710719840c4169040d1606502c2110340080e2190660551004002103400140c004c1528401841120040d0422034540e01c50110b14504003070030704003010f0043c0000c2000c201d5a14814911401c941401c80d503d02148407820304011406409410310b000200b50101840b00d29048248594401c90381244806502000c84030070380064840c54000401e004414400006158010031190740511000c5091000039076096030000345601100800c01000c4040c001090741502030042108040c2001d0115001c01c40f02190384d0f8000c403d180d1588100310f00c15000038540030341c08050682c50034080e2400301d945540c2e0242403041c098402c14001d10515039851062166401540c055500580c00341d842d00402000580c42d100d0441d04c5a80c0c1950b80d1006151165190020540342503c949 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 162415071 1250 162413821 162413851
    0xb010903151506030e03161104090b0a150e240d060c110c100503040c03050d0c0312183c0303150602070e09150a060509100b030c0c0307050303 63
    0x466240003040c22a409241890700b010000001700e0400f106442440300034041402e10103c2e40c1c00d20841d014040d5166603005481c0014820a01034228250707840b40b1071001c020700c00031078a01c0030300c0098a06407151006c0c0b08096000700e00d44120b0302d01030724981ca001c80500543c20031840000390a41d64026021205940e49032031485c420f07900a0440e054200308600600700c3ca000d120042085590070102d90010000c0c0000040c08101140c40803a01850b044030484030443c506000103004109030200aa01107080140400d45001c2d45010381e143c040bd49188602400d032069840f203a40c41035aa80f9403035404005480e0f443c511801800368145003c40303005003640880141005412a04000003040d4000c40c1088248901034000840000311001ca5000880d00c2d9180c0e1507460a00d0b21948000b550365444100340142d08202d5005101038400446000c422034070b400c1e41048400c2c5191089029124003400010003428019002e44951860742003a81e244c1101c40c1c0d1010306543c42204c200181019403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 162416321 1250 162415071 162415091
    0x306140108060604140a02090105070501060e18030304031d0102030c06070906110f0604030c05070e0c030711010506030714060f03010f030606080d0c0b0a0b0306160f0f0504090b01090315 82
    0x80100d0b94110744140e03410085800c0d04200c000700500d00400c003000703e82d000142c41400e07901c070368100d896054102000b0402c050302d400c14100408401d50b604083c814020b0440300c1c24207004403c4034040c56164860300c00780440e03214440c800703000c8400c1050540c0000d012880c0000b0040c459079202e40700d66650402907a0821102400085a4108174202d030f50044610142d030b5400080c24941150b01030904c0d00e001c0d04540350852405103140c20010360004040280b143c03400c0301d14050340c06405079480d2110b15803c00314403242241c0c030880e229a0705900421003080f01800c3c1c85100703110288040d0580e880c000c0f00011501131640285e00000f00d007404804108280246441440040c25440001c0c00800d1840325005010025800010300940d600c540800c805050591000724208bc0290958809140c40b24001d01000002d4400c0e41c08125100c141c2c40d1010b10072004c0803c6011261501e03820282014107001c010440d481c822814800142008400f1802c0301c440780ca070105600d00c0205040d000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 162417571 1250 162416321 162416323
    0x60b0a09060608041b0b041706070309031d030102040807081c030c020307171303120807020c030723030304080a06060801050106080115090302040c03090c0e010302061b01060306140108 81
    0x5602225000e032801005000c140d500060140d00550043c03058840540080001d01040e0415444040c4000001400107059140c6504501c2d05402610545d0800e594202d015403c0da9a0024010f00041c020306003000f0030048012003841e1071038082c000605003500c1d211241e150a01c15000802c180d40415001280345003509401d00f020f81c118038041c0017200c1030150181d564011042c2c02401d84629144c03d810b1322411505a070b0f8180e102d5000c00d8801a0b0b01e00b4140d198005003480207000506403400146d50070b0000030318410980000c0c0c0103145481c50010650003402d0080503074480e035442440c04503455581007019101600030480940001519031410300122082603009068903410a0010019a40c2021215045030401400038101c101c8050040f901405941c00c000d43c0b0500e020320604246a0541c080402c3d24840c020103140e030358942051200c85082480002c0d4402010041e168425002d000615440700c902e900106103107450b80c2d1070300c050300c07080340e003842c11b50031802c00400c51028 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 162418821 1250 162417571 162417589
    0x4030f0c1e210b1512120a140d1a0108060405040c23040c2c0307050d020607120806180112060e0703080a0302130504051b0f0403020a24110d03051012060b 68
    0xd0345402429001b40240c5ca10819028a01950040c00310030301c20044d1107000042162080c000c00c410030000080400c1200d030081e03865103102400a41d14400148041c282886817074092900b2000e844100f624100865042c440010206444d200c42081d0100c02c50302c4600955160100d0354540c0e001c681c590082c4009040c0504852415010030155584a2520b0101c0e000c1d064400c29038400d0002c1b0024004207185100e003042c02008180b4005482a040746d20582090280c0c204445917030100d1880514891084820b0040c90308001d03520340e601c0e00250251340644180403c1c0da0a5540940d03803929200503941000c905600813a800161000c4040c2500d500c1c000036000440d01004a814015081840c504c02c5030914245030b00000382d06114000c1d0705094070015a402401618000c0e25000400c60040c0244103681e01e8a0307401d04596800350107008885001820180101111400b51400b2400380c030000d0801c442c508001d0001003425817200d1541c41c00075000b2480895681b90707007400d00c000d0342 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 162420071 1250 162418821 162418849
    0xd0608010b011e140c06100602010e0a0b0f041e06020d14070503180709060f1706071d0f04020309030702011d101206080304030f0c1e210b15 62
    0x4071440b505a55040700d5103800ca40c100b1084d181500081c8411407182d03240c3c1c0f2650403a0b04562088004000d00201407109200a07074030707554001e201c3c001c2a044901d03a01c551940d4020046d0042200045c81104080242a40640210481151441008110805c00d0540d48007680d82e1600010010420541409403085c03812528880030054608014024424040980782100303469281d2240d03101040304102200150210341010822141c2c1c0b66002044d500280c41500d12887c12101990740c20072020402c3d5118403c80d40380c0d1500407042ca00c0956140d100514825408000d42c80c0344c621903161440a1481680c0d550300550ba681400d0002420b000181c5201300311a10a4400a41107500c030714807a1480c00031542080c03011b0841c60400c0c1c501400e032641000ca981d1101050000c14041000e02008105000d00748003a2100d0315062a0120031810314800b01012100c2507003003021140c0040513218061800054801c0e0030f259917a94003010b00141e482a46512142140d407210f45010311000c03a2071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 162421321 1250 162420071 162420077
    0x51005180901120b06040b09100801150e0105130f06030b1f080c0d050c0d1b090203010506091003140a05010906060e03070e040201020a08031f05240a12020d0608010b01 74
    0x35031501c1c4401242003da514000c00140c1300e140400c40d035840e560040204502c000388919800d28025041c032454a0491241041542c20004822400d110828101d000c1d0342000111403d243c2c00d1405015091100d8034000c0c41d02a07a52410354003c008900c6008007440c482d00459043d130800a03680c070f41c81191808103266035411035000b0404000001424840c0081c00e9841501064550a206040910401d00c10341c01107480c02580b03040040103481d294140d05055030900350545c540d618002203000034003403503400c85020813000c00726141003002010b07a101c0515001c01d03600c44210700d038191820305640c00c1c0f0450ba140d900502180a01d0301511001d48110714112045000b0700c0c001070740e60801440340208003900000810b0541e44240500e40300107800115060b5241490f01410140d00e1103c80704801c50f0919040201d014501070074070380380c41405002442d0030b01c00803543c6030f16182d0019411070184883c50324180841c810500282154000e0400e0014a0382c0c0341c09415070a44100410b01810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 162422571 1250 162421321 162421339
    0x40c180902011d0d0605090a020d1506080f03120a0209130603030e040209010c06050a0b060a020c030d0e090f180d0203040f14060d090602071a090c150a0804080405100518 75
    0x6a444840584c0300c542c0d0417900100e001d8031824003181c1030125045029400900346580081803103080803100c89044144002005584e03039446c00203450701d10740350901840e03400400102d105d80700511440ca40142c05248014503040711500080c0089031643c08540d000c58540c0810402c0c113410100828486805036801d40c0341881c0080002c200200720036004082680d41ca01154000d401507106022600c405007402d0b90381d24108102a41c1d4000b195481c46c42445401280d40d07101c0d1240b07005269500c00070b00290801c0c0ca803415096183c483c001d01c1881d03202503807a100002d4401c01c0142072160302854020310790300ca080503901084206c2c40c0e0003910381945a03c07a50a0301c0e880d80030840761001c05100d4001200c0c40b091030b0110180c49001c0d0050014104120078071141c0302440c0282d40240c000c44c1c2200c4603040c0381404d100000000001800e0b0b425028400d6610300c034000d800b82a40140300701580c40c60503840790009810078501810f45000101c3c0498040060440c02002035042c80301144d025070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 162423821 1250 162422571 162422627
    0x30b21060a052217040b0301140d02060d090614071d040b06070206130915050108150307090b01020309060301080618010e030406200a03030c0201150e010509040c18090201 75
    0x20610a4094059408528088210070b10980d0ba0013080442c1c5650480765540740d8450340b05030703180c1003809001d030b1600aa00800801c3e03e4821803212000e9409040c0c18201030110803200c0c000c010040c015901c80e501c0b210703024003480c10400c8041c403413040d03070712411a00d0486030780c905840700e01480b02030300440c541141e00d01c8599602c81500c4080b681103c2c117640da01052a4182005041507021840706401c0c2181624070b4600100e50405070303802070b0791f07109007560340d4001c4201410f04400041d400d0340001c0e400303001b400402d40104d58405018011071346040d00c40c001241c40f65100340e110040941016042c42205402d105913242c0105420000b07000010303901407038544900c910b11450b014802c05c4040c00c200c40500300402c20501c0b6154090300e8050300c031401c0140c040e01504502c40015440c009082e4034810a00c645402511112550b0182c1c0340e080c9011301105481c080c0082c2c88c140d0305034200150f4039042460203800420b0000011441c002113100241207041e18a90455064100f045142 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 162425071 1250 162423821 162423841
    0x6020615090408030a020c0304080d170601050915090a03021806031c0f20010c03060e0a1505060c010e1603020a0902040305060a0b0a0f03030215160f050901030b21060a05 75
    0x42e1300302172040401651480038003d214618450390f400041c0901528218039619a0044007003075841030040178010303e6917130301c80c0115021b1049501407039011580c140c0034004e14520001800c002d0350081c064214568990300018080400c102d8114110200c0004208042c242070000030120b0400c41107840784c00b4242000608a02c0c0c44110180c20400d1110408620460a9008480c11604800200f00300b51400500501400160041400c1d8600610100e1482e130000c0c843d59000040e08480c6030307400d03030030041000360990042150030b881d99260001001c40e0701042c004141c0351640d50101403d5580b0f10301c18800030400c107500c015881032061000f0004508041455039120b0310051000484c0c070b5429002900040c456085030004c050035503004420950005250104c0c41420f5995400955400b034441001c600d010b460309000844610443c401140150302034083c68605040c041518091440803450f03800001008410034024a1611040120706020868000c81c2c000c00520891400200358 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 162426321 1250 162425071 162425077
    0xb040627060f080d0c170c01020d0b01021603060207290403080609040803040b101a0405031006050f060d0605180106080906091c05070506090c0a0806070e061b0706020615090408 78
    0x905000b0251181410441c3e42070906e2200e500000d1590340b01c98500d01514000c3d000308402101040c90590405040d60001594811902188a80008050a5682b4070000c0c0d08221341c00c84484034080030402c0540d00a20042d4480c00110402c040d0500e01400c004240d0748000c1d200c1c5029070701398400e00000c5010002126400340c0c00c42c0059085464071208480651019070001c118134040e10700014020143c40c0042c401c4550403000c4410706000c100710f070021118103204030356011500102e007880b2810100094400190451000200ca0707907034501180040003090203460f00d050844006110580e0042c2e070450304a0164401402c6a2800107103141d600c42400d101b000d6448420b82a6400003407046080b1480c96521000b91070f0f680c102680c011750303110306400050b03100e07800290740402c5610000605502c500196609c0a40c4601d041061104070f83c04008628443c0a070795031504010b0341c0400c0305034003c0400c1d07801030025192031103000004409201d921445a01c101041c40007003001c020a07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 162427571 1250 162426321 162426343
    0x140703080420030f06090d050906040915150302090411070b01060503130515010e07050a0f080604022106090108150a0e0a0b0708091c050d0b040627060f08 68
    0x1510700c065400102c48441d088140e0100e0354580b00d00c01403000402e502242c8140112001d008441c445603800c01c0940d40c03405060705454108000b800104030f22045a00070550b0400720380610394019407142c564107150030405150700082900000c082e541814284954050b0b0600501844e080c00e0050b6101c296000c4103201d41d10800401101103042110710071448803100d94000103c0e8880070068004102000003441641036040d04003000074912401601100d40303c1002e44d984c0c00540b4030043c010b07200d100002d003149030800d5003401101a02d03109580c2807000c458403804019500c1c90701e1000c00c255020142c0003501c2c281c01031100c40c21003030034000f146904050711520200704132090441851501001c0c4c030018007001652801e0151075170700800403038000ca165000741d59002101030682d01340f800040241f6800900100046a010110385d407110a02d181e0013807000c07452a50300c04820488030007000340b100100e6128000050006038901c282d034010854150720910b20f5141400300f5403030314000c01d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 162428821 1250 162427571 162427583
    0x150f130b0901110705010e0c010f0203030703051e0a020909060a080c01050913060b0403030e011b080c0a0602040b0a110f0d08090a0204050103061e060312050a05040f03121407030804 80
    0x864000070081d00030810341090480ba140e150055420858041c000b46e206040c200e0140c56054200b5500c80c1d0354070451007403e500154610307190903500b1401414002c0011445c08000981401c0c41404983d00d0381c00781080e400c2c05a00d0b584078004004049401914203031040e084008200701d000008104050064007d08055840e04001000304040ca03504403030000c191890000040391507070912010300140d034040e41d0340810350000e007001556010840c801d41c0050f206400b0550700014071080007800e081c0a600c06440b40d2881941e6018203a0708103810040c1d01c1d640208030f00d1a503c0d0b00018000ca03002031340d4001d1811038507140b034035911004030f41c2c0c20b10304001c0030400080084600b0030202100c41d5024208111030b41e541e04003000203106101c0300604603401900201c46460312805120b0507a6000300c60302e0300300000e00c0720945455218514074000c2c007009000014403000f05890610041d4010610720004207074201008201000461014812240c24060100400d9008103c25031185c4e01ca1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 162430071 1250 162428821 162428843
    0x7030807020a2301020c031b060f040803040b070210050108070512070e0a09020a0b0c0a021c0b07120f090c0302030729090a2102040c0e030a060207020f030708150f13 73
    0x402840c01780c81611581d422900c000640c10101020440c101d054685500d81560f40c50780f110b01100070701031415500940301d5402031006c100440d98044800f500071200b80120782d405404440c1c103e0959109901220700307908894400c00071803c108400b02048201640900845400d011460700007030405003208280e1595120b030f0104548510717510301d002e8511a080355031074500d614540390703a40a020b03208a0140428581031540f400c1c0030000003814640c001a00100c0d42d5800004540c1e459031151803083e032603250f01441003025158817864200038003801c880c1c84468150300500d0f00d000c66030703441030308000815400000300300c2c030565807040e0342c80b800801c0541d9034041000054081c880303070b0003003000e910f104480c42d031441c4840f2039a0050103100340d80602201d501150192001500044081d800d500310a03941030004040358010b000305031004201d8a242c2681002103850710b01c0c20f8000c0301c5194007010800a4560001c90304039807100c17050b0924002e42c0780ca0030340c03c19940e404070f000401e0340ca241 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 162431321 1250 162430071 162430133
    0x6010c0b040b041704090507091202010806090604060f030614070c0b0115120e0303070306080105060f01180305010e0a05070807060f03051008030c030d0f02040506091e060a0507030807020a 83
    0x403031424844800209030706500c4170b881c1d40c601c9004001c20368123180481d0303048000082000c1030003800e089064058590fa4040d40c1c1d81014080c5540c00201019400359a64802260203c1c0000d1030802850045000040840e0036460000607480050410020b100d07201d2903050004150b4040541915806c0c1c98404032080c401d60203444050141401640150038010501c00c003881c000050351045615a5050200580c1d03900c60364200c802c01d548040c0c02004451900ca419401600e80700500b0b46450020300985a076a210b083c00c5031410300030f0403040d03005064182c0a0003410042c0c0800351400d100a421124685000904500074000310708007455190000103d114410072b001e0030041401c04240c950300c200c0d0b860010384075446005002c8c6124900a80301007c4001031080d20280c0300064041440c100c180c408212640c0101c440c0e160201c102411240c103e0b03250325001e80b10300742281d00c806888542626024000d40e400401801c11580207040c3d0002050380c084c408203d2402c0054019180a28 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 162432571 1250 162431321 162431333
    0x2010b04020d050403020c0a0b030115050403080a0801031a010b0d09050a060c08010602100e06010306020f0d1a0901150f26010b0c0c03061302010e040204050405100e06010c0b040b04 80
    0x10a04000303a1003031020907801c8a40c41250011803145200707909580c0150b85090400400703074202d02803000071407030610050000182c0c01e40e80403132a40c6141062401c2940d0799072140c046902c01030551000030000001042045141011440a4012084081201d42c1401c507003040b1800741d6240d540d852501c9045c900140041401411440d6420420070700c0b00c03440c01840905026401c0c851031005200c2d800e01030140f0b07021807069208114030f0b90042c1a03180d286d5101c40300a50400701c03880520b580104440c044a103c0b0f8030594074489c1075862111507240c4c2403810451400d005030f0000201c80b802025000750305a210031020640d080c5820308000c4030b50b0100c40c0207405c6800400040507500720a0010888050007405070818440100032202101103200506d0740701d54069440d620f0032400140220015030181d9070408038040054001400c0c2035840c070010701640c10a0313420f106c1018484800380242a90888503c0d48800c080c2446c404c0500c40c1d560301c1182240040000d0152074071a00440c0c20004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 162433821 1250 162432571 162432581
    0x19080a0519020a031e0c0b04031707030c0207050103020f1c02090409080702040c09050d170f0313061a0a03110f090408030901060f05060703031d010c050406090b0c1c0201 75
    0x78100c90440402004070801070340d100c9140300c0607000310315100a40b4408040300c2072000402005d9544880c10a98195503842111202a100310b0a200c0c0c00407038100601034112456101c1d90403580e0200f164a1143c002a04019050700100c1c109401045003804803d00042224810082100c0f450462a940d100d14002409514500e603030040c20032199109001000c0c01400ca09802102c0c104000548860144d65002845c8105074208013a2044500441c0341c200a686850080e143c3c040d02d01071010074030b0441503104039072289441000200c07540502a80d445014000b0450401c10551b022602d000141c02e140d0368400101440c0d0346500780e045a0f00c0e11614228504009840017941e401c01c0d10340710000340c00850344100d00d907103080d0b000201292003034881c804803003019140354580452510700f00c001c1c10a41050b04030000e405003120b0030f4080d091045210910140d5626610345044c0b010003440c1c80110346c001d00b8594800e1001000102d070105948851803500124450b0700004c0c0002079016007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 162435071 1250 162433821 162433837
    0xf020f0709061e0302010806010507050a05011407081506030c16020303040303210207080d09060e071701060801060b0405040c0c0b040c0e0f0702061b0417100e19080a05 74
    0x1006940002a0214098010320140c80c8200e1241d030800300da6070f9002c5000081403101a000424030341c0490142d5003d50028000c56002d0360a40e0103a81403600d40d5802e481a0310100e50304412442c04120340d80f0b0748910242d030000801e20a210107202008001051030102a00c44003c0d14000900040c160390301c1006c0c2401280e014081c1d9464035a68100074010302c81c0205036209108040c10090010701140c4200c030005075002c140c083c2008980510b51340200151201150f0150342c810f107103594100c1c02c100e07103c0201140d200e012461601070700d11078290f44403640800c4417030703041031414003802050200755000e4407000c1e60005500c1101c02401c0301e01440c000e03800342841c240e490074030040c00f10b660603e5040d030700351001e81069a00c0340c40b201600840c003140d4600041c0c12400104803001c00c00f0701c1e0f6020380b080a00c440c9052075202e04004000741030703032181035103a98000f40c49014429494028040f403040c0042c042d00103101c42c5142d80e40030007a09140140f4000f000610b015509000c0c0050360003070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 162436321 1250 162435071 162435073
    0x9060409140a060803070302070b0306060702040e010c090503071805091204030606090b010c0803132a05180105090a110f0d0203190b060405090a02210115020d0503070f020f 76
    0x100190080c40941c1e40103070380480350182403200104200c003001089414207603060303004104880c94440c0c032100c0ca030005440035921000402514001d69120701410158010510002842c43c00701a009080e420055100a020303230401c9170100720207030340d40c5044800c00011160104040c0c0d5015106400c1c42500c500a2a524002003000700c144007280d4400d80c00c2d500c6030101000744c1d01070440151280035050f60001d0600d44100300282e0071100c24070788001c0c200d1089901c82c20840d5110000301c2e0052810700c0c0e50a10248046040106281814501440104006107480154107010200c1e03d99200208800c00e2143c41c2d80700076503a01c401030210340940c0302c003409050301c845040319444007941c002c0d13404200b95201c11400c000c0400c2c40c0d1081d41c5070484001d05051600d4505030902110520080030407042a50a000f0b203130ba0084041c00b480449196070350f03a4007103503040c252076208102c90725441800b154004843c802e855900322049907042021390a000380d0f440301c101c00481c42d240741c04842d1718407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 162437571 1250 162436321 162436331
    0x3150406030f030f1404120309150c0614090a0209180a0311010c03050108030a0c0c12050a051b010801060e030307020a0305010b03010b060c0703080318010c05030402090f090c010509060409 83
    0x80c02040d00c00c0c106468070030390b26081c134101c0302e900407124080b07859004092541c040004003d10488481c00700301162103803e0400c01c02d40e40b501c222010395145101030000ca151246100104400c511481410036607208030040765003010107400750380d200c0c50200240201100349c08100048000c02c80c606414410804607510b0300d81350302e0020440031448240c502c456081000104515009005140c10b0301c24110045003800c400b1720342140c492122103401c0d01d06011080001c18480102e00d289940503008200825580b01103140491400303d5940d001342040d41100558042603034030141c46411100149400c0b20994013540029085114000001b0b40c0070648150000070044190890b2200600850003000800d4001c02442038034418802c0c40a05900310100520011722450007445e00040c0c1c03001c100400301035607460b1070700310f45202d0483c1000c140c2c044204011407a00920323031544000e000d80b11066074101411072a642d5104281402d061080104000d034464803600c00f9100207054610003840 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 162438821 1250 162437571 162437573
    0x70c030317010e13020405070306090608030c1c080103020609150c070509071407140c100e0a0605040335070605060a060504080d05030405030405090c0a08060f10050315040603 77
    0x19010400350749081403003140002560b00d1010651a01c034030700100c002c0298020950801c00185030041008003410b55038000440c0d282c40b284036010141106000a60361401c030850040d1070110001944150f08444c41d040d40401a031091700241100d0341500c41603100c200c1480010500007040040f500a0540400c24071040f80700000d95004803882903c0092658a0f10350041310417100f01d04004420440420422000624844218400300810410f603020114818005a070034180311003010002000484a41314500d010b40e1000300802c0e040c24204c0c84d051030b687d10380381c03003a48060050f4803002d1400341000c000c0400c02040c28102503020005551010f2b07d181080061005a80d680c1c06a40c603141c0c041400c3e0b0290703080760151a02400148114002c0c3d0034100c0c0c0d55440204200c0309800280400101d5450f251220342c02000e015000c6a100c2100207402460400014980b038030800520030340300c100d43c58035812146c0c08041480e000f0399a98074012002c0d9a02400c0c541d56402500e0260004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 162440071 1250 162438821 162438827
    0x110307270b030705010c0312140c0a020105101802030405121b06090105070903141009060605010e0d030516020d051005011503061d0a1508030409110708040e0903070c0303 75
    0x14222100c200410a041e0100309160b620fa03482d000c1d2030701241c1c0740c4c10780e040800d00451104110b010700481c0468111040005445a09010344458003904404160130a0f12030b02802002d0344501d0400d03581d081d20f440c00f0f825003901a008180700b102941c1c008041018050b0900c0502c1540009071429681e650001c505000c03d21500029240306000700f0000c1040a003060280601990319981d51042003800c549640855040200490307000d0722404501d800e02101602407401800c2c06024000303145490140050044140d404c184c0d4481e03000010b1000020b500802030308d6480102503050010b01f1514408504404204000540503203d404000300c4179002c5034203c503043e90b50b1f111988030110100d850580603140c06009065886031100c0d50748040c0c1c040e404041d80c2c4032402c80c0340414041e200d130785100c03114189034200c0c504a8100140a00080c3c4450148075400000240c000740b400c0d8082d16104103138020b034001d1440854505001c100f080504005442c0895080090b00994990341e00c0c0203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 162441321 1250 162440071 162440129
    0x20604122001051005130204030f1112151e100603020d090602040e041109010f0501030f110721021501260f010b01080c03010501050a0e01031d0a0203060906090703110307 75
    0x20031b00c10081071201b03540c03041c2c45000f0342d01201d9001e440104610b6280d5500c44004550704441c3d42c0041035681c003078040d0302080168841104110440e4101420040d41c040749200b400003440662100d6041030042c0c840c030b00b180840846209242c0141c072032a84021280c090702d49101d002e44014004103000c19100c80c9d451003580103d10841404008800ca00300784108950240705007107411007400e03010003079540640c1140f02c42101c04140000c01300c03215030007440700d9000003400f503440b0882241e01c06d142540d840414404c0001030b000404c0603a1007501c1c000107051050040c140c0c3d882d01980f00200911700b802d503101945040405960818844034682402060b84845150010340342d0380c0400c0c24140e1103005c0724103079030060f95001d190020844041e40d494904081050402d0f69035811070020712139581c590b4400e00e0302017000d4041ca07410380c010107240103400351410300560400340a02449007000070358030040325441a4111804c206250010b802c110407984680d105030300702925102400c0d520090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 162442571 1250 162441321 162441329
    0x828110f040e010909050304030813090204081b01030e0705011b0f03020615010f0c03051317030a17100620030d02071e031d0a03020a080307120206041220010510 71
    0x10314902d41e030340c3e00c00384810340d14891005045900100410b01c00308a04c1002040340f0a1070380c0c40c00e0072141da62106c4030100e03800341e4845410744e040301e103a5044040300d102040a080000b441c05102c0180d02d40440f584404151086138180050740360020744007002d030030800c0081600070b4460036840b0340c1d506029446100803a5508600c01143e05e10b9032880d8010880341c0f6040c05988d50b0102114055602a0350952102c5000d14507001c0c2c42c0000114890071240c641040c01c0c030340000d0354907042d88000c083d01450740c14000c0c0c87ca00703815004006660002e4100d10701110960719000a02c440d8140310824403400345580342d203280c000081c8030241406141c000f040304c0c601c14004049400345a140010501002200040016410300d05c03d0402409011401041e0b0744000d02e1500c601c0e940c0e5000078030402c0c02d5480305035113030004214502405100c0c2105001c82c05240003900c2603140543d90000c00040070f640c42c4040c0101100b0042d6040c070790030000c2e11841e41400007004541458507842e07040a0283c85 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 162443821 1250 162442571 162442589
    0x31208040203210d0507110a060b040f05131101050f071109060607150506041e090b0c07121209051504060c03020f0306040e030705060408030f070828110f04 69
    0x1490543c00d5241c2d400115080c0503401c440713041450056a403005042c01070082e00810140200c8030110400074491000428801c10000411016410512058444407840440b03a03520304000c01c82c00b10011a200342030158490085200c1050400040e00d483c002c000d160666004003003400c0c0204800600301a481020884440001b5551141006114858400000d0904e1006465981174070f550b604890780056000700040380352403d4058240a00b0700a83c54031401988641c08182403000070060643c02440c60740030540350000940303600d0200315414446400f008801100c10690110592003d001c00d60300c541075610703140e10f1180382c0c0c070305890035101035407120b14040704034580030701a20803101d0a09071060382904650318441000020120301e0f0f40b48e111030100300004400680c0c18080f40388035500c02c0c03503c26101d0425600200e41c1c04001400035090020900a0045d60700075040c440c808002000d403d0080203480c0d070302400280520030003221b0586000b0481c40d4405100c43c02a0003902c081310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 162445071 1250 162443821 162443833
    0x31b0f1211120c01030c020309030a05030301090b0307080a08030a02040504020d020901031b020a02010e042310060e060315031203130b0901050c04180e07090e0d17011707031208040203 81
    0x2010040704507442c0326080e60651080800746a594083d801101e21820f1500541c3d050001407808642071000015088400340c00c00030042c41040312610424003200000d9004111003410520a0303541d403200c0401c05061408080000341c4110502e40481d400307400701410544d03d4060502e08903000e90072600c00207010a090036507802600b561000e40c02c6007149254006c240c101c2d81ca8006440c3c0f40d00402c1081d41064407036511050040ca140c10a00250716000e0010b5403030f28003a170500040917000e401c21010080500c03000311090755001e0540350029400035007260080d03c501d0000340390248000d4441d9000d4004400c101d20041c10100e5500703660300505204040d0f98800c2081030888404480c150407039070040c0b005224140400c64201040b00518800048404000c004185402182e500480403d40c4800504108134003c1c42105280034481c00d011039580c1540c44c203020003003414001c400d03042d284038507a1040703804200304000003150002c0c4402002c1c3c0100d00c00030a40441110107074004d201744 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 162446321 1250 162445071 162445103
    0x5040b1b16090c030b090601030b06071b0f060f080109020f0c0601090606110613080a110106080303010f0608070e04020a0302040e04060203060a12080a050a1709150105010507020109031b0f12 84
    0x617000311011107000402c80390a079641c400054000b4600405c10310340101041c8989000940c0b117441502480f85489030004c441c0c1e20b06607000d060744030b1941001d41006000100c140007950803010803415070381075000250301c80c01e188c2034030300383d90140c411048517a108420002441482541c000c8044d641076507a6112a40110060559181e900703132a25034070322074411030700d401040644000e003003441c40720f190099145041010b0242035a94580090109810000040282c8a00b40d03883c0d500810007828420f10515080001410408014424500441d00015180ca17540d06c079904032000352400d0309440e5041d00307150034880e0007074204503400b40c0100410305020841000f8100140e50140c1e0054000b407130314030594400c4400b40c02421014040c050480b40000404050340c0480b48204a001d0041000000094004680c1c0301c0c10303444141030003010024030b000350b6400403200007640d80000701c400310001804910764500c0c5c0c81360f11003411210f80c120042040b000c0e10018200315401440155041c0d564 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 162447571 1250 162446321 162446327
    0x1504110405060316090f090c020615030d12020c010c03050603010c05030603030703110106050d06020a0305010f05030d050c15042603010e04020904150e0a0507120305040b1b16090c 79
    0xe5009480c2c0c00b0005000040403040304060700141d5100c18a090303080c540d5151003102600b000d07030b000512031944a91110004c00e03410042c1650001a400c003000b003900300400031a490b102540e9206003004002c8541c0d0500703a01ca50103c410403042c1d50003c10413182c10840c001d0041c0400d44c0d6186c0300f5402e00c100450b443e031041066a0040e0801406186880140d58056516a0f102008030b6850354896500103070950f203c2d44441c451a008402c0540d6404540c500103040b07032030580040085d07000c2d9003018801c07601c0000d601d0b00c11220504011760b031503074450003003452310489603d00c0d1401100710f800c010410014198071160140961221103004900c46d800d1000c90000340a035203c0c0e00707034140018000d4900004540d402601940483d801002d40d4070994042e039010010300c109551042a400b4100101001500c0041c8280c010460015682e6900202076120342c1c80b80c604c2c0c00c038011400348428015543c80074805600c1c8411203000302c50360711128000b00110b10032031214a2600f28500c1e06180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 162448821 1250 162447571 162447577
    0xa14010f0602060105130603020631210606170d080106030608060c0d09052b1106181219030c030209100809010603021e091308161a150411 61
    0x5560300586201d0303080105000403861b03402c10f0741544548408000015031035502c001c00b00c015000d0410020540c0c100080b064811121207160070a4600d10410400300c00107007900c0e0422007200444002550450034200e018108980007113180d41d44842680300340c11400640d580c0d4100445c2c0b2614580c1c1e03030316a81982150003034400c20b92160442c4002440d00e04010340100301d502c9401e580050030041c3c9850300c5140017010f0740103c4040040003180c0191010300344590300794401ea85400b41030502003ca40c5070700c403500a002c4c00850240c60240215116041c007244045861007203425890b450264000f0100909101d425070110b03107400301c1c0d261254824001c4a10340100680034012148680804450551004000c800d0035542c40e040070006a40e40c03501280c81c0c0d940d482c0030484148521007000320400e805000ba200c4d03080b945410780000390402c4255100154542c100141c0d585c881d003028102403580d8542200102d0607041000700b4296006030000801401391400c00c600e4502d0789840c03801d84 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 162450071 1250 162448821 162448829
    0x203060f06041a1b0f0708010b0a03050a0b06030c150304060b04060323030f16120804030c0b0a020f0d150e06220617211306110f060a14010f 62
    0x1211603c040c8201c1c8680c0c00080c1201c0711650784c0080346041920906080c80c04c80710303050040b5004004100081c400c00d01441c500d000d403c9495011043c82c598030390760b58485200004040c03900d20b1000605903170301800800f103503090280c000280c800c0000000c40240d0b004480c2210458038016125425040621591060b00d9106c248160b01e401403000b41c0c0b03021b581c1c01441b540c05220401543d843c1c1690302002d00ae00d031142203115861020140340400101ea803007144031003003201690403c404240c2c13000958480f00c0e0415031142d40d5844a407050340283c4558020900b84c0c000c0025900c64008071984684c0e10041d000c203003880700b15200c1000146030b1006450703483d03101030700c5442555000d10301c1d41845105140c0d588001070240d950402280b050600c009950801e4101100040c940c00c10980200e81c2100103003407a87c90208082203008585c0c82c2802000100a0078071414140c480e001c10900b140e9100b460101e413443d103000848100904011035401c048012560000110503414124a02c1a6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 162451321 1250 162450071 162450089
    0x3061009060e130807020a0906060c05010e01050c041208040e0117011802010f0f030603050607030e0607050702010512090102120405010b0f030c030a14030d090c060306120b1501050705010f0203060f0604 89
    0x42c50300f6840391081a000791800b6644031808100c0050395142c01d20511b0000c04284d280c400001800741060380c00c66001000745150303079046c20104079410240104440550b00e50341480c40f120030351414141c5440c040d03604140c011040c000300121711032500d00c0f001c0d40d02107040c2000b402440c42500103401c03e480001002070103d46030300d00d0304d40b816000e94160740d50010507150000da4655662543c9140403015900070707000c81c1c1e4400c607035110818240306142c1d0005860420a10748240c40d0300080c01351142c03044210b04280348a0114010b40c03001c1d01102c3c40102d4445800038a030425040060080408400c0540700300d400840100381d5007004591040002001405816240e503940c44400c0c042d102111902c549010130020142048001c1c450a51414054505008aa0f0605002504540d4141c0150380e08182c9000c100f40080d100c00240c0f03601000703280f04103203a01318220058800340540030700142a07500304013840718000a240c0c05181b080742e0454041854062100600000c1d1042d80101001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 162452571 1250 162451321 162451351
    0x602010b0d0b0a14150301180503090907090e070905041a0901050411041706060a120b180102091e09150a27051303090f0803180402040503061009060e 66
    0x85200300755010b5001c550f02001103000211100c410301c40740e10896206903003000b1003140007072505007481a80b0141d114800644ea4082190325910380d00c1c040c03594114410900c1000050840d0b101c0d06006004160160100c0d1050905e590090005405401103e002d686002240c94445070340310035044030031401070220b400b940d00b0003082c00003600c46001c0310810314008000c0000c21041501407003507042c903104058141070400701c041007034441c3d0f143e000f045811042c40c10780d404941035110268010742074501c03e56000d41c0d081351181c0079018944110758007006540000d0710b4503410020b200400c0c0c1003200c0303090a0b540d42003000d140d0b150421840035000b044808082c041d804810240d0052011104041544131051500c59070075200102c540d0103400c42e40f6801e8038100364114a00002501818450a9005007480402030f52805111070003000b50042544079003443d125a41100d02600016007a620a4507040ca0619414000780c4540c00e40c003440c080700080d50390f9900000500070392030b6a0290315 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 162453821 1250 162452571 162452573
    0x2120a05060c040b07080c2508060f0403050901030209010e09010803041707030f150906090f060c020c1f1202030109060503241314010519240e070504090e06010504060602010b0d 78
    0x1459000742e80303825140d03c91889202034105a23201c007890034508081100f018142003130700b860705140e809803e280c01103c055042c0400a0781200c10b4820041080ca00182c542110000480b81781c2c600702025608014213034004182da000120007042034400b265055442003114501c065521011403101404540901d81d00400140400e039404540e54440030b0003040d600c0c2030303403200406c80d5482041101e4401b140da41c02410498903000304e070f15401690001d0416032005178041903210780a401380c3d825030000403600051180c05400200c8940d00034100c119120340e1920b80041c014503590183c14400d104001428800321021a580031100411100c801901c0d01c40514051030040250300c200c6a040040e010990100000d2080e81d204a04010580d0040600410090111508403a503214130003d110110b003000d24010441204940403403840110640d290384084883d400b9a8011844050400044000204000a02505032902101e0810200b903550409074220b6800c5a49181c00c03030b20000ca240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 162455071 1250 162453821 162453833
    0x60306150f3f030a0f121505040e0109110402131a0a0915050703050f04051f0e0123030a0905070906031e1e080c12071b0e0109110702120a05060c040b07 67
    0x200c4059890b01b0300e0102107505488000903500003001c850b10f003007030024013049189810301a180f141a690f0008100740401919400001505e64004501550b0000340c00000007003064072460091601c03908a0521b0f15607070450300d030a580311a0400d0b0004403a51008a141180c1ca0340c11107000c40c4c1c580320030f80f9105496605450603042000098800107060000103400d889242c1c00200c0c40200d448025106000c0101c050500407140b80c11a04010703401d80c00c1800c4100580c0c01c600ca40021840c025100e50b24000c8480140c0540c00d0b0040107030164410000300d140190f040001688c1c800c0c5403105a2404001806269500100c0094801c1c0f03080d00d92070506103001c40181100354010340030585041c624440c42458041142d89404e0380340000030f296002d0000206031405400c031590b070703901259840c2641d000b0f0000b4060041c8400301d55100e400002200070f040484841035406001075241d103414141003034440c80f0803c010343d2540210070000706a480404100c0c0c0c00c0c0c07000d40c124103003070403659107501d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 162456321 1250 162455071 162455087
    0x20a020604060b030a08040602150106030c05090603090109060905031206061602041e1a031903140a0c0f11090901050126010e030c060103120305060306150f3f030a 72
    0xb0f540c15004001c0301001040c1140002c0000d000036800811260302c1002c08903452090507070025081518080042507465440000c0b03615121046075600e49a03101c4800c3d550040c05040402001240303807408a0b003c00401101801c0d183c410905070703c0042d40d170340040c4980c5104441900f0481d102c500c03000d0005240c030ba48600c40326140c1300c0341c1010250b000038181c1c3c122203030760328221042c02805000c1c800700d28040040c10408102d112801003d83c2503968080d08906c01c102852150550105800d0202031003944400e840d25040300c10090344010340c1c103080c06980b0740140e500340a0070031103000402c801c10500455040f906460007812002480007a4a21518802d400c500304e82d540f91131000060700d90400140a245034070130064070389940345203490b6554101c0400c0d0001410704207420860a03030303400f25a030b560008050340b2a00d141d0060300001038942c1c2100c01881d034000c00d060000809144000d21070004402d445140071100402e2525001c1140200c00c03403064503504c20032405c04040d01c100d03c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 162457571 1250 162456321 162456341
    0x1305033414150d091b05180c0901021204030b010518100504020a0c0f0c05011b0305030a0902060906071a0606040506032e030506040210030b0303030403030c0909110702090a020a02060406 82
    0x1d07803d00c60f1516107001a0f40f00040203a580f1210610210391140c9140301c500004c003400c032082c086030f101c1e401d140788003070303070000c24800c1074000115a0180d183d00903c4406030000f101c0009075074444e20b0b886c0c0b10515420a00441d0301a452000f08a031119180b0f1103101d0103103440305c0441010710714040401c0040d5002115040c1040307051160400000c80c281d203146240351180750302c1c00e00c0d14240310006005551100b4003d105c00504038401000c05c0c4c00604517a0081505040854103003500d0020030f22a200307810110780c110b000091404180100310002804050114000170750903214401081201d01507401901e50001c0108040b81900c1001c01c040842c42074043c11100c0045050414807804e440c80340c2c0143c070300350001c00400c021032900c6100d50801003200c0c201080190700c0d141c0840d5880c00300800007000d05031390304c030b074420325501541810000300617038441032020012a8480000a07041083c2c00c90040d0780d0780700070880507a42e034025201d500b0b080f41e008001c25070f902d450742c0b0082d0103d00d40d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 162458821 1250 162457571 162457609
    0x1050c0c15041a03240a09050403020309120d0e030c060913090b010303020304080f060f040308041403031614030603030304080f04080d0f0f0309080f1305033414 71
    0x4400100390b40c01c44010354000c01001c002036101d05d015010144421281040d44034038074045a040300550761144014802d4030813054001519070f80703074a016803a520844400c20350220030303020102c440401c0001c8561b02c42602d03541d0072003151510024103a541560414440e0703c95003e0203044220700300381c1c81c80c0482400341c19000c140604c0300d0b1243c002481e0203070001d0300183c00c0007d080c0401e000c204501000c09659400803c01c0f0b20300307400803d0b045400035100404004180c0041024005070303004601d81c898410b03060ba83e59092007180d1859009001414801241580b03007694400c04104094a10403a00500910724598a80e9140c000da07034086260030a00300350031f0202054400c010003d903d650703034064a1f0000c00400c00100503014100c1300c480e11040608080040e00010a01c0302500d20916112081c1600c03100c811542139846801c9401076501031007000c1104513560814161140401d00262410f01610884540d007002c01510340108540e0905224000c0306508210000b010f804080c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 162460071 1250 162458821 162458827
    0x41802071709090f040b1602030d05011e0b0408060705030702070806090a0c081912050c120904060b03072f011d2e0218060f0403060b01050c0c15 64
    0xd92414501601110381001c08031001c1212101410f04140c0203410500221908406140c940d841d0448030f80010246d401002c0c4d41070a0600060080080c2c0f9130700c0b4000707075060025684800441241c0325059001e0058908070202c0096802103045c204c0d8150344d114401341429944900741600e203640060000030852080d4400040c4007901031080c80e0107000c00b0405010804411300302240e00450b5504200013980002d0103110502a45245d040d0589030300c0203040c03009010713140c402e89950103001c90140140c02880da20104104030728009100d04042110108070050b128001e0301140e001c01c88220b0007040d5a06902c09040e105242603440090003021420000c000ca40543ea080d84c501c1401900080d241d070241e607101c22001d00015400e100080030340c40a207038048106200744041041d1240c04e655001443c0300b84142c00c13030410400040090920b0341c0e14100c1c4c221207483e950080c84140c400c40e2409101c04201c0d8805d030f04071000c442d981801080080700900410503140940d0807806e030303420010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 162461321 1250 162460071 162460073
    0x1202072309070e0607060e0601061b061a0a0602010501031703100b031003080a0804061b0c02120a02030f06180105190509100c0c0605060406030f17040902070b1e010b04180207 77
    0x680700800d401803143c0c40110b0802c80c200d281f54074040040e040b0070107001c43c6010504540000c03002d20300d14280c1140002c2240c3c03100c207500000790031090203015007020b407026000ca079003501504003d04072840f074000964440111401d00e0242d00082e40c00b25040c94140038204641040f00d1302450b0080d40f0000b9541c405a40c0c1e42c0c0d0600154458142640481c0c481020001800054881c40280310340c034844206820301d80c3c5100500369203400e070300244a625442040b0020b9681000703c3c3d036040358003074101c490a071400ba2199a85400440720240061080e034a0b10001c058180110b074021a0103011b0240c06840d031440301000fa110041007200f407480b4200e405010350080b1f018024a4820940301c102071410b4500300802503440c000c1c0a036004031300703040081000660380b0000741d2145400008444140e01542d819140902c2140e010541003800841d80100744000b40802a0050a40f031182d2507100e00d211200000801c0d09210700c9100702001c1c00704011403017a49141c000f020100200061400502d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 162462571 1250 162461321 162461329
    0x81012121116150206010e180a06051003140706020a11040902030a210201020f090111070b0d06050a080c090708091e100b120a02011d0d1202072309070e 67
    0x3410010b4001c1031402c03a040191089140c100c0018840340d1025001640c14101041e40c2514090100000080391015000b8a00405d05c010b0001581c000c905001c3d50811504882e51010a40010703604071480d00020303000c11000007989821903030150054100110303140c803a0718880c00c003048140d801607206c08510006a0b01840340840c0c00c0e215076290f201c91000c41001e0b40954800601c0c0e90700703580c41044155900b1401c0d8094403111502440c11072040810b4448081c04c2c0f8205510048024001140c40c442ca042c5580000090711001d540b0208c0d501d0b42c500f4015031705c889186580d0307040300803440400c10651255000d20b034800001c00440340764400183d900d90007205501403207081e41c0c2002c104c1585900c018041c3c210369100c1126018840d4848141d06034941e00342200003414030080c00314020f001114040145004040100742040035a01c1707003001c000d040741022400006004419000c58882c41180f500c1c80303500c51035041c40001e409a10140080840701601560900c00308100e480150b580d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 162463821 1250 162462571 162462583
    0x60801020304030c03020c0307080a0b060102070b1b0114040f17190512090c03030f031e09030c070b041a0906040905040f06060501020309060a1206090e030a0810121211 74
    0x103ca562002c041d80c1960070b0090074a854201c0c06842030708a05000c104041c000031b0006011a00b20350f000c80c650f00c0700030043c2d01e0714000754844064510b020071880101c00181c003c081944002c10024002519041a544450601110010003004500e80c090002c651410074011020005000c1b41d4540814545802003e9a07124081c03400500c000603400e084e010441d1400b50440d000070700406500040c2000a512070050190303690951a020000600b80312154490084803c0445102c060301d007407600382c96859520500211280d417046010004682d81944101d908030383e400b03480703034811001e00301e41d0080d03591244040c1c0c4ea0000d0180030100e01c07039903280301e40c030b00540c0305440000d182d104900c3d000c0c027555806d600c114150740051081c001262602e02c12502c58510902d4030394064141c0d00c03880e0000348007940290007a03c0c5041a81582c40074000010f100d00d41158440c42c0d050380d00c6611807441e40c1c0050103100b013104030245102000603410082c1c00541903d070b08094144907040c0091914200c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 162465071 1250 162463821 162463823
    0x30e100f0605130c0c031815050c06150306070c05010b100302070212030a0f12091406070e040203100e07120908032d1f1205060106030501120c0b0a03060801020304 72
    0x90380e9400100b01038500f04a07040d61143e080b0307a042c000d620354240080c101840c0c6801c0501448164441c0b510742200c40c0d81d281000d0204e08404c412008030414004000350040721400d404c41c414400440c890f24900c0f2400400d08200178001c112030b580d0020202e80030780c07506d82d003200d080d92903001d0400143d561005007410070040360340c01600c0d0036603401003000c4150b41050240994000300100282d1640c0003010f8001c414603810102c51030307580080110b00400001d0300141c124801c40860780005180070840038040d40090f56402900790f040e900700b008922081d175900355441c608620402c5a605032000c01684001c40341840b00000f6042c40003070050310000c42d030481e4404c1c400000c00102108003178071910761500c016001504e500780c0119592a03060040e1118042e40810200702402c801c0b824002c401415a803031a103550700b40039190281e518a000e004030000702742000004240c191440e40c00058054000030a10304551811041d0b06a60344032800c2001016203685002c548060b09000840c012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 162466321 1250 162465071 162465101
    0x20f060c03040e0108031e0301080c04110702040f1508010b0105070f08120903040e10030803040f080c030a08041101020c06031f0504111801030e0a0803090c09040317010b0316030e10 80
    0x582e80407540403900a512400103502560230300041c08489400207840080e48001d03100012141030690400c01030b4055074a009501a00f0421120010941c5410910002c240c244038010300e1034880c1003032400c0e140202c866900044050103c00d0100703c020701c031344540340e000e00c00281c68040c1e035060a40849004070780080b2030b5400010200f060094080d1900e600200c071303840c0361f06080d003541d542d00705620001e03002800704502c9289034424403070103070101c07500da1400c241203075034406441c03030090410842210305135004040f11000d01043e50007c5061001d451004160b146035030703500075031b1240940c440090790320b01040500c0045420b8a95100d54035180214180994840c820b000c541c41c14141140381843c1003504141c1d80c0660081c0c00a0454013180d0b0200a42d612075940e54802ca141c00c044a01c03003944503000c0c07400e100a15070014011441c0c01000a10710055a0f01d80d08140694401948d0348141c100065400c0301280740720303602c40d071881d030f0810701a40d11004a848240095683c8030f10782d6118 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 162467571 1250 162466321 162466327
    0x306060d1e1a0708280209040f0c1110090b040f1106040303030212130c05010c110402040e160e0901120302100903120606020c0d230d020a11030109020f060c03040e010803 75
    0x600c0307400040a45e07104001402c800d204412040300c01c0035000381c41e2a840402c54000c500395010b45c0da1a0002c000448202a04005401031b0703d030002c202003055015050a40280c1000202c421028040d9000c1c00390400380c072560581303e996406900c9404110141c2d50301180d802d0200083d543d003030040c002140281e0300503845d181c0d009214510244003400c1c0000c170384078100ad038100051040910300220b44090801361041c03141400d058013899018040150b0082c80080c0100d441c64403902058000e400b40400b00c01d00010305501a00d074505004101e59100400c00c1c010004110030503000c0d804c40c1d1203481600c5440300f8040d00380d42a546032000c101c02140c114030300c40d20200b00c3c41c0700328030040c03c0341e02c01000005082d1010a4603482c1c1c488010b084d070810070310740ca000c0d481c03e6801240803110490444c3d151044455000307403240d05445044614a00c401002e0b01c107481c05020704074051343c000b088465410180020094254070003884000302e400248400180750030b8407110035009203032410246039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 162468821 1250 162467571 162467581
    0x6040b07030501171005090f0703060207030f090f12240504021f090e07110f07030314090f0904140106060e0a0509010806010905040302070e010306090b060306060d1e1a 74
    0x142c801c142c00124200503d150a040c0d80080001c40f101c8404041d00300241c0c9803554803a0506180e1081c52002951192001c00000c00c070310760f401040302034065500c82812080002080301c0d1202d03d80310306460a19040c80610400e01c80b41002c080c018829000750b8001888180511755500226018030100f541e118204020341c10b15000c2c007032654417541c40303424003800f040001414103040c3c0c1c014800d61141c1d503c0060000d0380241c0c0780100300c3c1e41d0441200c911100203176469981c6c6400b0302040b40011252502e42c5044d469440030381d048000014000b6840ca40c241080c051940c800500aa854038201c801c0b8203080e110a00c1218041c10a079610310220680c1c1c10f0902c100d0f040994049401410054010071506102154190541c0d0a440000c82c0e2038986050032460144603400c100b0f030140e281d1000008020456001c03080c0e507407003500b04030b000341d50700e00405440741412240035170070400c4290070790002042c00c064036041d200a8180085c00700d00b581c4818a440c04010503211080c00b409007400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 162470071 1250 162468821 162468827
    0x6061f0e041a130c14030406091406040302010c020703021503061306080703060e0a0809011412010611190803060d03090902070b0f0a090f02060307051209010f0e0102090a0303110f06040b07 83
    0x42c02c501c0040343c0a200d02400060000d0141c01040a070000040000c40454100700d4260050308250703404c80303110718058004001a03600c420341507404402541c071b040b1518900782d0012441404803030b001441c0c07820810b140d095050042d8802001903034444920b09058002c144c0c244500c00c05404000b0040c030b0f03070500b18503000c2c04641d82c0c0448212035074803005081c03000480e40001ca400c403000a10b40340710480103400e1161841c1c003c00d0100c10788004200d0001c14015441100c119044c0700c0202201d1600e81c034000d2103400024014006000890200009181d50406d4240681d42c14405c0c0b501d807000f95a00c01090f81244c01c20300c02203960902c0e001c18003061a29243d03846400c607040800c06c2080e41c98981d600840388040c510300900030300b804800281000c1c000d20550b1b14000340000003030f00034904040e0144c02414620981e0501e00c2c41c01d40b02d41d4842c02c0500c25150400c00140844a44608588050781d8000341c00d06554001d00c2180c00003150800248003550003a40f150054070721038140601d001d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 162471321 1250 162470071 162470089
    0x1020d050306060304021c080703030f063f0501020c0102040e07090e060f01031407020a1b0b0d0510051017010902070f02010c0c05030708160806061f0e041a 69
    0x22404000d0140705114240d503d43c821a0740055045400d4400c0100701c504401c001646960094440580861044181909604010f4100396407400030800103456054101c110700a0199042210030060340c40101c0b110b004492101e1840c642c451145007a0b103582c6c8090981c0d1100c1408842c6940108080101c02488001c2503042029402c2003c1c199050021102060300700400084c820b0309200c003840d100764000d0b0b0020300c0c4803482c020b4285480c80c3c10300c80a5520501c40d00110f459880103110368100c1180300b460a42034402402d4030504c8d05041c0c030320600c0503082c0501112450140c80390009a542d94100c1c2d86050b00d030607903d0700000110a910019072400b01680301e00e02d401e004014904c0000c10740c050021f80b01da42420909041c80c45420002c140d2081504103a826105401c030203d610500040c0044900c032101e40ea103400036440f1030302c0c1a210441a03d0b0580c02603024048000010003011490002c50001d04d840017118007448001070a988002c5032240d1603131802030201900d403d082c1e0072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 162472571 1250 162471321 162471343
    0x30c0f01060605041805040c1206090201090e061c15090c0e06101b110307080c120304080a081b0607030221012d0504110a0801080106031106070318090b0102 69
    0x25084c04d02d80240c0304542111482c045134032960701c0b400107040048412800015040c2140141103d61007450200c004042e155420b9002c212200b40c00202146c414000718418103015020030024508044c4c140362064030800202c41d040c2049200800015a43c41001c0c03207580503101c1c00c20b5103490010620b1a800000e40340c68020242e5881040021b6007003481c08041b50008044100442024100b012441000344110341c1e260103090800503440400041c800242d4030200e4040d4505d0040b400d01640d603204520508020341c10152a0340c0100341c0d42005044480c080d40a80c00b0000340303248009003408412100311011030382c04107100c0c1c90541c42407484104000c0780200c1d0b038043c0d410038100c003095090055040b980c00d00101d016610070303500c01c102a8000d060181052004202000c00308200d90002c003a01d900040c4440000140004140581c200f20792300041d21140c854214000e000c4a9408150b00b50309120b580414179010034641c00181c0014426a000015182003801c002404d15000c110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 162473821 1250 162472571 162472577
    0x1504050a0522290f0c040b030f0a09020a06030c021006030b060607031b051b010314180f030301030803060f030a0c03030318051905060a02130510090b03040602031e040f0308090708030c0f010606 85
    0x4070a20004891408494004038807a427440c06507901c110502015002c1803034000d41012074200e001481c650140c00860180380303690280c8007400c46041025007164000d02c0042e05501c5c501c408a030b03440c142400181180e80c024940240310300c02840c0e00302c0402d0307909842154954010600c0101c0100c9142c206c40415500746414450801030090004540d003000c2c15208284010200e600010340042060302103442e08079051700e0300ca69407401c1032031854000700e55150003001202082c00783c5140c0840c1034610940d004513092403190464404800826a141030001c0842c0d405240e2004900c042001c070440704854064108400e28a103070007030420b070780904000c10719401400801e0681c00308100f0700003a00d4050740e034140220a02081210100380e03550020202650001c2400248081b9030001e510504000056031035050303880d024a10448006ca0780940301c0c1050141040000e4400c1441940000340a02100c601e643c84411450450303002000200c001da011001c0591940c00071b00400c070042401d41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 162475071 1250 162473821 162473827
    0x3031d03090405060a09060e06030d05040b0a0305041b0b0a030b04021602091308130609080c0607030c0c0315020d05100303090611151504050a0522290f0c 68
    0x14412503900d0207480085841540c46200280d1241c60748030540340205800303103060003c41e5071102c109140040035901c0034000d00590441100007406030303084034101c0340d0780b06003945401081c1000724014500a00105e44504006820030700310684c0e0301c454000752851181c182d0359401143c0002c1e0444409480d4a8040d900500c541d01e035620059800c0b0b102280c05840c0100380c1d40c0c0d03071815104183c0d8110070040041c000428560401c101c038806071310680f03401d9103a54505a417505001e541c0ca0911a0805910110030000003002a2080c410b00e20418031890507005150303100e60390783c42c5c0c6c000ca1040180e511036010a014100014a025558008541040709198a820354900410482ca24010001803003054009220441c3e0104003035035a29108a071640010309144410314007001214404903c114108000f04110900b07c1c805da40c01034041c0800f00000100040802c4070032200500c0985100d5000130558000100c242c041202d101c00385c0da00c19111707281c920b41c0100150005021001175403418 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 162476321 1250 162475071 162475121
    0x8060415090c2c090a060b030a0903110f0607090b03061c0309082d010203131403090405041a010f030b06060d1e0f0612030c02040504020f120a0303 65
    0x40094a440d070740d0100c1d80b014890416a15420603002c01410b24400c1099803050b001c400b90a4420340340304981460b060f80310549450160748a80c044d0700d9000c40d00300013080d40740708154400d1a81c684241003c0d0000440c0090031401c241c81c0d440ea04441e17801c03d000308031840da4041700040c00703440ca40758090304504016020808a101d200c81200d41c0001d80e40c425001c0c14080e0032031100800481e012240189205031042c0030b000c0000d04540e84160950750280103410041c025284280240359044003a040c042d2211003507130300c1c0500c0f0090940070400c6102c0d411784890291921445c047c0c1480e00c42503401c13407580004900e05902213040801102003c1c0300051240019136040f80013103031800e8850301b0901d600c030000c000303040403003070250280b203010040340a0701e130001d07a40a02d092804000103540c82400405810701c0040c01030021340c650350341500515282c4d004036003081c00541804800552a0082400d08481c501c07201c1140c0d0003c00e80f20101545401001408140030160000072000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 162477571 1250 162476321 162476351
    0x30b010f030911100c0b0a09020102011407020a1101030e0706030506030d0203040f1a040b03090a030806040606050a0503090c0301060b0403060606050414060a030b0310200a020303010e15060a0e01080604 89
    0x2d04500240b080c080b104c800b12206119405500e480c2d908040000ba5600384509441c00400710400224090750a0040c4010742c0e12000410900c940300540160034500866900c0358521240752002a040c195116450100c022040080c58041d1501d03890005050400c903040620306000c0c03107207032400c551041005000903000c0d900c498046441e070410300c411500703040c10b010506018540090b0001c407400700c208610490002140155140a52181c0500e0b80b034060038071040c1c0301709025440c04914104003181e65548a6001943d000c1401c00c1a16400d01c10300c4006402d561241e4440c0743e6910380442c040c004c0c890b1502c2048024001030528070f14140c600340a002c401008070f12054480c0da0041002040305020381c0103040304c0c4400809549e241d8080648100003071801c0c0182d02800ca10703054460303401c031406604a900d039210316002036086a280c450304502c1c03c02d000345a4070322620f07042440b005a0700c5a00c0030300344685040d00c80050072594100010300c50f00700103010310f100b5402c010240c01030440d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 162478821 1250 162477571 162477593
    0x1303140109121b020310020901030506040603030e06280206010312020304080a0f02040f150f140d0b06150d05010e0f060f0103050903040f0f03110603041109040c15030b010f0309 78
    0x81c0505040e8440c0c1d410411146603e800f500b8040e4040c040c0207045840d022003139004107940503007603c0410903a00d0f0a401d0208450f100e0000901040c0203d024441a10342640900b031050410710702c00c108414429180328510302202807040243c0d01031700050040003e29842034200500070301c019801c00d0b181030344c4180d9600d00b40b0006005940041014001c1d529660068028900d138200c05012043c0c144000c001d07001802d00c0740c0100131090000100d03041d608407040680300130f0300810140703455406131924429a5170107000b81b64000b0401949280c2815848040e0a8031700814100207010340c03504c2c00302c103e11107008006808400b2100100300d0a581d40d8540b01300da1034001c3ca0009010f9503504043e925501c5140c002c1032441000301c40001d4001f001e40c40803000d50f03205c0da2a42c203104490310144001800151001058800d47c800c01007880d04000b0032455000380601101c050060b514194900c000d191a40c3c3c0000080e11a0400f400550f00007100c400004583c0c9810048500151100c51b40a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 162480071 1250 162478821 162478853
    0x50f04230a1b1e0528030f0612060e010204030203060106050a080709081504140a2405040206030c090a09020f13050102030307020706231902250902031b1303140109 72
    0x30030020f0100c44258443e00c1580d500c1d035107101c5540342d4001c4c0d101e00c0003082a40030b02a58006402c000b844070303a40c8114010f0504a03200810000c0c004040d86e80c031007015101440380c0c2c03c8907640c240800800f42c4d074204400e03802070045071030b2241d83d0a000a001041d503a0000c1145062110700a0204a00702d00050100d10340a0300d20508840c0d40c545103020640104010388691141c40b560301e400c01404969122081880d103520702402038039046255540696074111006580200148000341000c26006c0c000d0480900007040c3c0076901c0d4480b8401000ca8102c4004185150000306201007204007000000c4041c0009000450851400c902d0003990303807100c1c1c081c0078200100c204040d01c90680e42d5950f04108142d042400f0348454010608811410600100000501ca03490030b0b40c865000440714030b140a4060141d80c0720050512805030b010703600284c0104040b070b02e20000e42d0104070012002d04030801200c0503480c2c0d09480c5042508940102d2244001142d00d803000395400540f4401c3c0d42c03e120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 162481321 1250 162480071 162480107
    0x10090b2b0201090503010e0f010f1505011809020307120b030a08030a090c0b03010e09120304051009082101140108130b060d05060406050f07030c09050f04230a1b 71
    0x86581480101c1e2400c6813540126095030030b0418040b910900850303640c135a03410120003040318100004060054507026202c030404d44000c03540038082d95100349414800d0200508507891580e903103030000d20482c0d20031a903100c005503107140002e00403c007034080e803101884120001c0040922a40750f0b003010f484080c00c20f19825699103241c508001c034000c2c0000c0208216a500340d00c03584d481d18152000903040b2040d40560056150050f0010030b508162401160040000d04c0c01c8581d404a8a0003821a00401d4070281001d00805150703040c000041003e804040e800140c042d4501801403181039058880e8506201c0f2040c05c000c02108000886601e554000c281d858043d101c0c00040b4408070307c00c51001c0e043c0d003d200100014092207811160041081d451160141c1c0c2d01e400c400c50840d001011404c000944109003040347d40707001e607060500c8060042c0b00040c480100801d070056043c82d120041e0070101c0b4041040f02c0600e60784602c192461061040340e04102d000b500c001c111803503c18114100b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 162482571 1250 162481321 162481399
    0x201080114040f0212060a08120a080a1e06050a0801090819110a050a111023040b0a090503010c1106010e070c06050703050f0105041a060304081210090b 67
    0x580c2d030711504400c0d01807030105400c5694000501510201040c12a0480e0003101b10344000074074080d002440e2950b90148141040c2451401c07e0700320380480001d4042e4803100d8591014400000b141c1080f2090055101000140c1c14580020f028800034203502c4400c49924214901e804078840004031444028005d403604011007071f90320140e079240301802d208085841485c19040c104040010740b50729aa001b2001d040b140d140a000300714001c4c50705010309001455844583e0065100050401140c1040000440c03e050315500300c81d80c103400800c2d101000a48280d02080141820311501021100924001d45020301c0300c1e00036aa6500180304211030300103c1d4000401e0742e0f00c1208001e00d02c45e4001002e004904010100a01418040d47c0082c406000000002200d24183c45010380c2c1d540002880c040301c5141c0b50405c115508020816980240d04000440c4140900e0b03029a01c00e10043d5800c0022034249040002107501d00035100e4060b224450130f4442110800503d045015072201003010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 162483821 1250 162482571 162482609
    0x301080a0201050705121209070806010605121503030a020102120f10060c03030204050a03080715151a0408070617090a02010c0f0602070b040c050102010b03160e07090e01060c020a0e0402010801 85
    0x106d041c802180090003110041840580d40441c1c0459601911902003203c0c0a0382d00c0f285000e0f242d034000e01c2000c0c00714004200303c684070280c26205990011f02d50000d82c407104400000300e070441e07001c2841e140060f540080c60317010034920080e00c0c94001020303c1403044503282040d0000d40309207460140a003400080c44040c81094440d030101c030007610015100352107166407440c0c6048150004c480480e50150b007540310180740f603045e00c01e20701c13200351007904c0308503d601e00019501c1408100041110120040001254040040010800074542555441c2c015071410101094000c00540380321b5a64002402d40f401603a401010845036a400445c1521354180c24540f61b8000d101780c0344000c08403403c075010081401080c410701e004036182030300244020701589042540340d00700807402c0c00004400c3c00c000d00000e5011000c0990114960405000790303600c40020204183c403d1f8080400968208503002c118200303410014002c00c0c0060010341e85051981c006000814140a0501d40c13461245c0082c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 162485071 1250 162483821 162483823
    0x40504021b010606210c0c0605100b070b090708030333030a11041109030a15090b0a0507140406080f04060f06080a021908031e04050411090a06050301080a0201050705 73
    0x106a41d4101c0000304907840d91348402a214001c00a040102841d50041000008045008060041c41d10f550780080d400c40640c1c03040004d02c0060301c02a900c9494880c04100908200024000740f8003c14642d15a03190a9030740500d444941e421070f04294009009011030207892440c0f100305000d41003001d4103121f4040e2094115902110b00715549807198035002810b2110144080c14400000e80c0c0c01c0c046002c2c00c0300d194013140303e10300c145a0180e00c11803000c004a0481221655403181140700410b002010352100301c0103c1040e910007860b140e0301c0062040c01a00f2000c412210103038900c41ca41060315118000d807040c04020318024500b00b803071000034100704aa50107503000329400c1c00d08000868544a409541d01400c80c0124016a0214841904a140801141c04581c000c800951030150404050300d09207145420400b03180000384804540c07555540100e07120f00c0640ca00e81c03900c59126500704914030400e036001405004c070400040c8003440009c40c0104400e902820070740d545000902c0c01c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 162486321 1250 162485071 162485107
    0xc0303190507060b1f030b01110d110c0d080d050f06010c030c051f0c0305011211101205070e03010c080f0c0f12070302040807060f0807140c07060806100e0604050402 73
    0x1140d44250f509a4601005e1810302e030740407941c2c4280d44c01f00000c1c00d1a400545401440c2280e0320350a520000f5041d050500c00c0c00c0d1040707181980301c144c5411400100115003100c14082040701c000a010a00da00020b8143c0305030b640c071410112000401e4200306002030a8803070b10701c80103003c0240c1c0042003414040d080108480341d9000103d8490306078059101c41000303201001d0303a500000d040c80000206115070203c40401c480c0c00c500752540f0303400c6440403c03240041c1403004100380301c1040c080d0b2058021324031170b00f4031480403500e80e07400c480a4042094215500c03120014103000c0a8020310030340400c4040c405038032001180c4140d95549000820090070300420010b0708004030703074000b0040d50f968950003800c02c40741c04208584c1002d44841090b9444030704150742000180d1024001490a03100f41c101704203581310340c0c202520f411196004035052103400e42005c00854030801c117010642c00c104018420b114142c3c68194840861a0000b03441d07842240300b154442c40d0040341034403c1e05a10982 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 162487571 1250 162486321 162486341
    0x302030c1506011409090109020a110111030a0c0302070b0601080703090f1118010e07140d020d06051201060810020702030106080706020f0723010309110315090c030319050706 77
    0x4950082607090140280807a040b100c107070001e005019910480c2c0050010f40e11440401410b4000036824890103400942205002c001000702004441c0c01200d8284200183c2071411440c0b55507903c0c00080310019501c131041d04108141c410403451000c1000903c210b908446e0900e4a0b03026a00d130454114083c00e2410b0380504120b035030b8600e41040100300c08913060b5081007514a0345040f8188107062004081c00d100702c803442c0305484006852940b0801c00f01c1c0c0601c1d841181e090410690403044400c0340c112104030610381d0b556150502c200c0c40c06408403010740e000360000f8441035041140b01d5868002034140d540c90660089611002c40d60b00b03401000280107084102c440c01555194000d54420308455284524058078401190782c106881907447d419002c007a1880030200309100440c01407441c081c2c00e82e104040b1000501d01e0740c1d014403460138800e1580119102a0034010070031400c2c02c1ca0011a280b083d4410882c500784107806000310f9800d00b902e8103250740c032803c440c28110081d21425072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 162488821 1250 162487571 162487573
    0x110a03082a180306190504230c0406140a090b040f050c120a0203010302010e090405070b03090d2a022e08070f021b060d02160809030f03070b130302030c 67
    0x4422079500501602030403084180c04081c9607920407800515448040550b02c0039048524451030032003004480d081035412511904401041d590303030b40c1d10144040c50a503420b054581201d0000401481d081c001c5202401035010307162403d006080001e501c6250511820044a8960001c0d240a50b01d07071740940c0001001e0340050000f803800000b0b00d410f80d8490101009011200e402148241c400362099905a90f0b041c0c450303044040c1100c042022500000b00212181c1c840c602d000700d181d41003040610700903c1c9003c000c0c07810340c00c0401d02034220642c801404424503d4440c91450000e1b02072124500742d50181da046a03030030005c8110101c514540400700d28101a1031180c010b11903802407841d0b20608070b40e0f540c030a0442c5112000c80c1c40d200b68020307054144a80324030b9180d41f450700c400117201980c004400103181202c202d007105015803800406944201d00421808980d0a0501004462091080203549080350a645103a0b02d510044c10f11092118130300c4281c400c040c000c208688103604048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 162490071 1250 162488821 162488881
    0xb0f0402071110090b0a050304081b07140108150603041b080304170a0201081506040f03050a0203060702120304110111151b07020d0b060411040f08010c110a0308 71
    0x414601e425403085000e03039015007903824103d4801886070410740d0548008000756868078921110032074041e0409002612209820008025003c030340301d000d24001d0003000060007015151960b40c010102c0304141440c14015000c04004180c2409440c0c00c03c050b0b8210b420503200e45403420a02c06c0c03480003022404504d104508046442d010020190040351740d81c0e46541210098002c8894450398103e0000780400c44080c081030041c0010a41c0042040b005032141e03003400c0c0c0e1807030149241101584261010303040600b103801507003000e01403103901c0302c0c844c0000c00e0741801400c00e1100c0b501c001040034104a07140c044560f550f0303100da41101556401d1000301e134880a1480060121403a050714807112000e180c8080f050b6980481d01558806c0340c00510322144000d10741ca8141d00c9880041009038042d5845980e03480094810000d08058a1642e1900700e405007000845421502c0300000c02080c4060b8440880c202400040c0c80c00c0c00ca60b051500d00031036251002e07107200401c045488203421141c41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 162491321 1250 162490071 162490073
    0x1a030706050d1b0512190f050414010504020108180a080c010e0705040b012a0204050c070c050901030b010501030f0e0607020d02160509010320060310080105090d05030106030b0f040207 81
    0x10001900440c0ea500c4400c00075825030003401c0080b4422110b030760340802c40c01d200d00c1d244541190001030f1b1004440c1d0092043c201000342d1034080320216030b041d442c0b4a56540c2403005111190000c481d2180321000200214100f640020b415000000e014a002c80e91014081400c00c0e4284200540641d0080c0000c3c1c0780c0c141c102d40d250292108589019291082d0680025a8640f034000d0941080b810703100c1c42405002c1071100402203003041007086003103110810358801078a031482010300c035101000c0829125030161034003001d4640700303510241c4140c07140d030018000304013098100d0741121000d090000f074240c5052117a1340605a8404145018010700302040301080d008a2112008125039080e1070200a040405a450303c3d09409580e0b0401b03020b01c014800a41c040b04502512511100280a50340c004000203c90350301c1100c0341510319004180800a034042400740c0c0307030406040c03009481a030354100700c000d2079400140300b400d041648500514455844c0d40724459550080900255590300c02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 162492571 1250 162491321 162491327
    0xd05030d0c0e12160501050c0f06070f12060302030309090604140106020601050411040b070609050703081c06080c09071b0503030f070206010e041523040b01030c05120606041a030706 80
    0x90001d0324091003118405100541c1c002c141c94220640134200d500601d030500c401181c26130400f4210029030b00c00d540803450b19000c208220341c400c0742e0303e030355140170310440c030340c0043c0401041d00f03080024030308008061005a4002c020344421580640b00070b42d80f5920880024040d150f809280641d21b1120000820760960200d6250706813417054030240082200000d6400c0188654030400416007418800903000036041d80004906902070411540340030f80700d403100102681f10112030802038400701840c1d404d42d22240503107001003a01c00302421101544401164001c0c100030030b10300401c8100114602280f90850302d03802c2d00c03500503040b42c0e20ba1070b100c2c0030120441c2080e0f40003405072144034000649405041010b900c15907010060039550440181c003c805080441800ca081c2081411900120759444e0704051086006012140700c1d540341d42014600e001e5250046030103201030342401c41d081800001c0035074104030b00780c40000d40c203012080d01a0390700140c0000541c0c9405a8280050756585c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 162493821 1250 162492571 162492587
    0x6070c0e070507050a080f0403080d0902010f0309051b03011d03090a15140a03110a0c02040f2f040302030d080708100317031315020403030215010807050d05030d0c 72
    0x190510984a00703459964056a1034010b140b0001e00a6000c0c41d84c4900058460f405800d43d008907100e820f080c2600d0344d85800c0140c1040381e21b50380903546c911108003550391012103043c114500342010040140746498503502c0746103200290700e880d003e5003031840b0309441c00d510900c2c25040c000c0c4104105596088042c0d01ca600c00f0342100d100750213100010a040b4070310030200700c03005d07820f84500030107100800c0f5074100c40c1c0102035108203241d80e440011040002c00781c002c11448a46664002e41010749104101c102c620305105001c0ada49031100d061342e02d02c1003d2100e106c5400920300d410400e860410440741d680310b65000290940a04031142100d02d801050b4280030301900c1e116055595200303480c00d00c1c00266031102900d800c40442c98106000e0044004640003c40700085a00c0d12000da01d030450741c48803100080c10841c1d400a01002419814000342c0100001a52181d0b401c0d4540059940d03212b840740141841034943c400e03500e08000003042114544511232209000f106c074804c4000d48440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 162495071 1250 162493821 162493829
    0x60315100504090609062402190803070f090503030904110403060609020306090c03071d0d12080907090501080c044701020604120f0509040204030521040803120403050906070c 77
    0x3d003070820118121500f8000c01d81591340300c0d01c8520a40854400034487c00740601d01010640c0201581c0d281074040c2000d4403109540102d540b01d03075a0900c800002d0941030030341151001c001c5489001e000f10366011040b1802c0c0042100c0200340001c2d00301c000707440741c4220384c0f005006a160010018500007181c015501c50354040781d600105503241c43c03080319184012610480051030700032105d41500904050b0458031030000d884203030503d803603584e540030792482980d020000c80c06a001b04241c042d020400314010f09502c28043c000365260050050f03440741c10080c000c0c8074944441d40010b0070706442130242c003025070610b0b22514840324011b40c604200c1c01131503840020850089501d045500029a490081e0781c400c00c4101d0045071010101e480b003059883c000c0030002c041081d49440c2e0345a001920145003e0000b0f81004030003d0258030100880d04a208010b41e01400b0403c10074102005071142c02a0424405500c2e503a14a0304407002d115010480d41c0c841404517003c000c1c07040d02a4003805903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 162496321 1250 162495071 162495089
    0x9080609070617070206010902030a0f09050a1401090503071221060e01050f130c030e010f02040504050106170103081c060308031b0408031c15080f06070f0905060315100504 76
    0x16070303c051941d41001046030a1009603002100421021090368001c40c2d00580120000031802c07994a1301e0b03410360b031160350203035419440420124140304409500c402d0010096008018540c255698503803a80603080c0c01030b140305400700f4a42400ea0040903a400f040e102040c003440c03280b01648070364004007502d015a1241c0c11120001003018140710114840f036210040c4800140c0d141045410040c0030382000f000109078030340345508a5034009001d4803120005e101c43c0540c913070742088103002c01c5400503401141040a107031409541d809003801c44a065903045107103a5607072024010441c0000007105a4004400c0c501180007040c894241c000d50b026484403036a008a000f00402d54a01034041c0f4001d1204642041060b0b0121481c6e0001d61aa000248100400c0d007203c40440026404900d52008096400c01545450305c200240101c551011244c203043d0380003020303c10010000410790107001e00a21300080414800013105005d0110410300400c00078030032041e860300401c1c0360010300c40e43c208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 162497571 1250 162496321 162496337
    0xc060c03030e01050712020901090b034201050a1718010c080411010f090905160206180604030e13090507140a0311010c140703201e01050901090806090706 68
    0x401601809a18000c500b146da483c1607000c49001020002c0d07121039809030612807800e800003000d800e080d010714403d698407081c0c4078961148112525000e565007640000c1511a00681004103024080c49001300038203281c810385903103181d8026924440c122401d00840e01070300d41005810b08031440c0c045007240840e0000e00a0504042c400d407003218045e50b000704815180c0b110320b00d40e944074104c2e5105130182440c1030142207503181002d01c1161020b490a007052003054040d4208a038042020a800141171143d8049a415a281280c4c41c0d0030b01070402401c01441c901403001c1a91024010028061603600401c0441d017076241c2199218100c3c815101c4c0c1d030383c4402c0140c400d0f1421403415411250401088440060000300444020505407003c036040c2032090708083d45c10401f0085900a54411280c8000d414140c16000c12400d25003112540b040340c640410720846802c5454000e41d821080c20015103a00a4400580e020141c9401c00d00c260700c03c4004204402c14000b6540049030707a03c1e215410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 162498821 1250 162497571 162497591
    0xf0c090c0210020d0609050c0903010b06030403120f0e0f0607080907050d170f041509050d05031c0f600b070f0b0c0c100e0102070c060c0303 62
    0x816580140322100c0581c202202002e4003503441e0300100415a9400c000140446c1c41315042c40c11290240c440102d40701010490a1290400b441120440c42d01100c4860540c03410f80d030005d02c25032950340d98203481c1d03071584519604404541c010400802c0d46a0580e0910301e8488a41c030341d5070318122000c00c0060382c404c011402c1124041801d01c00d94401406101192400f92151901c2240d44010219004000c02104811240380001703800500380320750f4802c29005401e60700416060b0a90003203441200350f1800c10000510000485071580034900300c0b83d600d003580c40318200050640e1613001d0281400d221100500d0146c18074001d144c08044000f002160681e013000c500f46102c403041d5910380065a010310a44480385440c84180140d100e01a000002c0c1c0b5220611416080f1840854040244054280412201c90309083d4090001c0c0200e42c00c112a011826550300d400710420001c29585a080d000503d60a404030740784250010f840b000a180e513903d0041c4032004681040e0b00007071900d0411a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 162500071 1250 162498821 162498839
    0x4030b060a060801060e0f0a050a03081c0615121509140903121b0c070b03090f0a020303031501030204050a0e04170a020705150c010501060f03150302060304080c070f030f0c 76
    0x41c1a80c100d0364840301a1080c6e40140f10b113140040903015841084001300080750740c2d410201c0409144501c1a00341c0b80c8914001d502c3d82c0b0000c9403420521107041c0b04003400780350143c009a0034044c1140c50011960702040160f2001400d903031080351071403450301074080b4804d040354000d030610030196520317660a030341e0380803200c1c1d281d0040e050f0084045643e440440da011110787d1020f0100f46a4801c214600301e013500e003407031170a20164880c0303040a2010041080c58081841801d03446805100a0100802a13500080d1684001010070b0f04011001076504041d901c41d5050706c001e014058019110a601e806500700391640c115400c41d86c0c0d0382c05290381900c208210065400e01c2e09160001c060003410601017000501200b11001c3da103460901184030200000d00480d03008006075221038500c042808002025642d01c01c88400013040034810420040c0c4880045035442900007203e01d8613420b10100e003a0409100d94007a20420000c0b01c030200501c0201030895107a1840744460480b0031f5600d11000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 162501321 1250 162500071 162500087
    0x3002040f1217030402030316050a02041409070306020a030b030f0a1e0c181b030e0c0d030207090e010608030a02030405040b0a06020a0b07021e06010f1406030a0f1104030b060a06 78
    0x2c10b09022615035030a98840080a15001031006043e203040160181400c20000042d00c0d09035902c0c1d010b40c0c2c40206500f01032003500c180480b0071203154a07a11b80f201e900c551301c0580c0c2c48000c10040e80042e01060b00d511071740c0801c3c50420b0040950310406116480b0343c0e80e4154031901a142c0540f90328a01c240140303650b005a0700d0340d6210000c0e0742041d00d0300d0760640350500e04550014540d0344a9402400840505014201d1240c09450004403540d5041d000307450007400c0381c5403500444020036230102090300000d43c9401c440b001800401d094105114450140c134442e806030f0030503c0080392100a994000c0064000d66000740d030200640c441007010000d024041d03110748005600003814010100e18503404142d407004007401250031040b1004d08041040e402e00c240c03c0103542000d0014017440550000310001001415480c41e50212444000f885030700c4060982150b1179651142041c02280c01d030010280d4120340038100c1d8596a0340e04000070f9245044907080c7c802e103c1050040344a0703000b0140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 162502571 1250 162501321 162501323
    0x11407081e0709051c0512030601020304050f1302070302031c0c0f0c030c020a0815060a050f0d0524041214180409050d02010e190f033002040f12 64
    0x40d210081c400a103020790468060042000c20144020100341d0745c6540381504d07041c100c000840d041c100d001d030914070300345004e180108000780c0080082c030801daa4008242c8054580c120745181d844000c580020300210302040304440c050740042014000d03d6008800341c1110904001919118080301d01d4010484480b559560081800d00c0c0c201d4407490310034003021490728401d05100800803000d40002d00341c41e08541c03080405501486101c00c0c070340c41070340c0401d820205c1610b10440381403c01d03001231003040d403054095004000681b424000e00c84200406600d4042217901c000b0f0443d5080d88590f071340b02c2c00710780c160361740301c41031000349449440381e424802d5100b4202c60700c50070940320204044c540218811800d46c09600c8150300c001185040c80911112071302c80d000040c02c0070388601800c1c1041d42c1441c040410803081c1026102051480008442c2c265061620f80e0704110003960b030b1400d1903500b15455030000d0343d017581da80c020901e680c0140309450480c003d140d5110b60720f00ca820f00307441c50108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 162503821 1250 162502571 162502591
    0xb07020d03030b03010b0a030b060406051c030e01050706050403020705010e0603070929030a060e0108300403140c010923060703030902060d02030610030209030303070c0c051201140708 81
    0x110034030210740300358424404640010000f190541d000000280b0a85035a041501e000c412441072050506d054490307000100701c10307203c00100000c541400101c0c10155040a41400000b81c1d140c1814ae01c207000f1208107903442070302003206041c1401c00a5640301130f4012240820702c00703640c9104601e0402c042d24030611240d500c245d2804e0400c4c0002141200c00042025907101c54120040c0c4040860099403144800050003d00e1610302043c0c408081c0303060b0b000c1d500c590002260301c842084400c143e952680704001d4020815001c03611030702c0701d80c4515032024140108910003241080ca02288100884400340c1c4c0d454a101d0b201c2040b450b80040400c0401501118810034400f9420140007514066000c1c0c1000518140103402140c42540b200d00144a0294000100507451400d1a114620500503180850820320f0090109a0f6480068103070411320003030402c0b030820007204c1c24001020f41409407810300361644020016020705030050546080c24045000240c10324400c1c80202e100d400707912 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 162505071 1250 162503821 162503839
    0x40f0315020c1e030409020a17060105092805040903020a0515070f0c020d0b07020f210a08060a03050d030b090f070e01080c04080604080901030e0a0221010b1801050306010b0702 78
    0x2d20610f0140559800c0302e6000d000500c4002041540e51001c0c0c040c81c40c3c40e48410401c4611101c031103070b00130130040c8028103100d0184801e00342901e82a02c800303403880c041407030441081603e003650741960016a00c4903a01604044030202050b5022a580c0b0099201310100c1d8003621a0f441c0154102404469060000c0d1120040b800710074840d00d48040000c2c0054000440d0341c856460362071075900219400d070096841400e40b0320b0740c030b04104035542c1980c1ca800c240c20907003084d640e0040814414074414134100f00c0903a000c2030325070341e481c0484001564803000b1070341d44050f01440a8042c140a0406610034007910340010f00d0300360101c0d403a501c0b94580b562240c01002c1002c0064815000141a00340104814400411912410020715024900a140391616401c0810004007660850982003540340c010710b52140c01a10f07031001c0001c1002d80903c3e03400c0d03c00301e844c8109005082e070f2444580d1240d904288122503004000005040e44d1095094841603a02c2d0003e10005200d171902c02134100b8802 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 162506321 1250 162505071 162505093
    0x30209150f030a0c05010206070503040b01060e13050106020d200a120c050706080402101d01030e010e120d0605030f0a030302070215121006090305070506090312040f0315020c 77
    0x6454400d00041006144540c036080d070310082440d081422204a8140d0f45058041c8981c1d0b80400240b40d01c210070346001031443c9000d80d9030944ad8031040c4030704c400303000300130241c0300482d5035844040d400c1c0000d4690401443d81d442000940c0c89408a410402158140c0803201d1480501360440650800e180010704001a2a41c3d9280b51400c15403c0201000402d120450000e0420f10050000340142c0e95854030504080c010000640101c40100f02802104815050004000460241a880b003400c6c001902c5003400041405042d2568102c400f82c06004d49402000103408040c01d00c8182c0010300304031050f241d80a1590350544a000b13195650302040c0c004000034482e030018001144054030f2030f41c9400c03601c1c00071a9550442c12610901525020404c4514414403416a00410551610000d044c0c41e40e19800d80f43d13401030241c24007919001404c038100b0b0310308004503580c8905540c9000e56a43c2e276030b86616122403141c00300300e41b04039500c4140041c2400c10b000341c42d14100380304003901c54a504 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 162507571 1250 162506321 162506341
    0x30d0816050c07060207080606040501030f020d051c030e15190230092806200c10060504200d06180b181b0a09230f0406030209 56
    0x15491210400c0000c1142c035041040c14451040203040607002426002c0c1401c2c50030b401e00d4001482d6501a5107000700401c00315101e00c0325451001e40640f50f807011907059040a42c14504142040050036007030811490405906511030403000908400361640422402d00300004440e06a0350101294191441521400d2042d4018401c0c44100f91820720120110820310041c80f0340c0e1041c0007a01c0c4071304010003d07240018004d48000c01e00e40906441c9000b8043d071581c900d504000c5000d03107a07680d00e4030790034000c0c242c519041d540000c520300031980361500e4110180c9d82d00d90000f484116079042c40f0000400d400e042c09403540c0180c048500c95080340071520104e2054001800644000342c44450010356042c00702034040b01c00c0c80e07026000c209003404e14244900c4001803071030051101444810003690404107214115140c0303107440941e6450030300c50012110883c154003c0b071344a200500070701049120b03400d00c04500c0c07041510803405820800041204446e4544000b83d0481d00c1c00d000684481c003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 162508821 1250 162507571 162507601
    0x4050c10020304030c26060106120c0903020910030210080c1801030b0d0804080d090b180324180a0c0b090d081c0615020705040515031f0605030d08 65
    0x250300e1044a042c0340d6a500c6002d09a04c0d03692040d00c40c1c400700b411840740c0e00c000c10780800000c1901c0006085a5141c84c100405003841a5078070001650303a6006010481c2c0301d007070340200954006103d002c0381c0c1481e03d1903417441c002d0b6100c00c0344a4080e100040c040c080c0030305213082c818549400d0740c1d42014000208820242e52042010f8105695a2400c55195680f00c4110b0003072401120060b8969040c08580c070b1a0141c076040312428494034072001c2124802030b40848400c00b00d00f001081200c903084000c01d2614003825600240c544405e000407940c203050302c041c1351065540020711689440746c850740d00e840304c0329828082d1141d00d455800344503041081c00101040d0f0f40260201401e082592a040c4181d088500402d880001541c1c00302002c00d003d0003924054082c80302c4004400f0200c1d040a0341c0c0d440c1911889000d580c032080040c61000218021a2600c1c0000d025118003c003081d03819003549095040320380140e407404c9030103d05400c00091109580941c0e84403007203a0b4440d000b144d88510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 162510071 1250 162508821 162508849
    0x901020610080d230d06050f04020c0a15060506030901021903050f0720030c0a05070509060904110f130c090803040602150a20040306062310030b030f070315020304050c 74
    0x105580400c1d84452413684020b1404419855001880508020401100c0b03003e4048440c862030060080d40341103240031521510199000850140310f00c820301208024000f143d20541c0c2c0818044204081103c041d00149003122905130742d030407465480340b000e6007107400603580001d0030030307a48000402c00c5024a6255060700580c80b511000c404508200d1031855000ca0040d2000350071403480303001040410820400984000ca40d010310600d4a480410168403000300702038603008048204040301d407a070425031622644060080074011002100c1540a01030803190382c000590b200b0000142e0083c044203580958516501500740d07070811003200060160b02508804002c0d03564074207a00141e01c01c520051201d1a1020317156201e0785142007400448d251940303c03861840b044049180c0e2110070f59441e0070848400c5800f4031412546d135000720000c01c0c56810070364140c41800c0e03021400781000514001228070581070030800744c00d28600d1400f0380c0020717a0b00801079442074102942e0b502d06811400412 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 162511321 1250 162510071 162510107
    0x60f020c0405070c051515100c0b010e09160e0c0703030e0f15070306060f0c0f0b04061a030c06030406090f0b0708011404090b0106030f06030803010305030901020610080d 75
    0x20400e1080028100e510549080d00404c503022800000c2000c2400030801109201c0000c20040c980020042d10007a58056050310070748864455160f0b49014050100aa5410000c407880d1580c50745048070b00d00340c050310308140d6031048540303954988806e00400400d50704801074921040d00c40c080c1070184c940200408130280b503110049010445030070001c46920000890043c014840c01c140031306e040043c044c05440030107040c0702d000e002d11900850030300c1c22403002e460860100da0850034002d5445110318001010313013200209100502680f83c1012100e01d0100c0ba482e94580344070002c140d51501103c4125810082c02d20001c2d0100ea5160300418500d8040c1e0010841940c0f140c0da0051518000c484001c040b68460005102c00d143c0411040c5400e44162810840e641d016101c450080c10305204010030181c6404d1664511030664001000a43d0301224850712540c584c84c169850760451511a4014412700300069000402014410f00700c2d240100070300380034030f40003004641c40070010102c8001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 162512571 1250 162511321 162511333
    0x31e1303080c0a030f08010e270d030e0106140a170a0f0b01090c05070b180106090908120c1c0507140409050415020a0215090a05031c0f0203070504060f02 68
    0x201c0c0d6800300610038a480c510282002060510740501048014461801080070800040c00021010520705030840801c22410888140041110145001d84190035550b4001c0041c0d43d080250140c0003120704404010080c0300301030f20b039030a92088aa2090b007259224941540400420030f106503544280207121040e41c0420030140c560005008100d1b00445c0e040740000300400030312040d8401c10b86416214130386140b51404c6a1101192440040c01d0102005504891583c0401003540690001c00c1c04150900420106040c00e5040c1e42221003c0c44881c04200005003604546404403079803448204080c0184081240b8000002d140007025176080c0031600c410311420b440c103a40904010314524601060b90700d060311340302003544076007040c150f43e00d0f00500607442c515401050752154400d00048110055568881052428980000140144c000025169140e0728080b045d515819135040f828007541441c200a2002c91208071207200024805020601c07c00f480382c0d00c02520035400c0e1040f550 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 162513821 1250 162512571 162512573
    0x2040f15032001080103110906030703021003140a05060105070f050c04020f0a03180503030115090e0702010e1b010e0402030705070c090b1309050706080c0705030a1d03031e1303 78
    0x150200d42600240d600340d8030140c091070b0072104078122001c030010a10300030002c3c0d450750b0340759421035110241152140380d0b0000064540c4d2410000752001703540040801e00c0200729420064014035000c031390010030301d00c2d1000180c1440c07070b1030149500602040e0f4425182c24081d480b044002d0011010480c4d050088400070603a40d9198009440703d04030f40301c1030aaa030f41442c403015080710340b000250104441041e81d00b4000c0350020013501d044070018104400c01500c83c00084941000c680c02c400845036815050200b141e07815400b40114070f81d034400f00e4110101008082c0540801000b03041d0001c3d6000c4420045410250041c6801c100d540c20010704108065542448206403500480e420075a1013070082e50b58a08803081d401001c1d4402420844a103c41d1501520f40c141c5004d404280f101400105007500b846408454000c0c0c6c0140c1a640c07143d4020000410724815140da4114104195140007803d10700482110300840c0e18811301c3c2c1c0030740d1400c891001c0035009044111142e20214038000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 162515071 1250 162513821 162513851
    0x1050402030a03181509050108070c0c1403030903010e060103030207050d21050c10050901110f070204020f091008040b070305010602060a0e0709090c0302041406010206130f0606060f1d0d02040f 85
    0x5405600303501c400c6d5a1a06281c0010040712004100340c0030130400314011400304040700c08400641d01e4240400d04c0e40801000803900d54452040801c1d015880c2a40803a009080820190b041c0d038030a60944a481d80c5da1000c0010000d54000c000d418800d0407500035001118801203060318a00500b051803c0c00000165039052a020004015000ba1201c042082c40c110a1040411180084810f03500b171111140e490409401862002809641c0c00030ba1440d0301d1854400303030341d03056030f005001c100512458240141070718010f8504440f81c6860102141043d4001c1c02001d06070351080d8011b1810380d64900c0ea6a025003102c0c0d1070103240340500c0001103000d1607207000b40c82045004d58480360905196205000c2107504862003240120015028480d07641c0c3d001c1803050f040070f10100c4030003104015040c4482111042100140300d50328040d03001800c3c60700200c21a0322240c0646a22003040707560303041546800c8100f00c88541c050340b0b1800010052819500c0551000204800003a415405100b10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 162516321 1250 162515071 162515099
    0xa020d1d1006060906020d030f020d051e0c090915010e04020a02030a08090d0c0f03170411010f081b1b06010603021b070803041a12010e0603010605010201050402030a0318 75
    0x10300010740022601410320049402018010501c600e461606070389404c0303000351698200590030301015147d146c822145030305a0141c480340008250100141e040808002c004414070340005100711401400280120b202042903232001030b00030b48500c000d0740e10720307110306c0c80c140800c5070080c14030500d0314041c8100d03220b82c80607010102180d0021035a904030380d90042c01c1c0030700082442000b940074482c00758085078000d0350f04001035401181c1500e140460700c0c05036501c01e55800c0c00c0c528172186000700000e102c00010303545441d40c070030307202c00d120000011401c44400c0021500c0112981542c0c9004030702c541a280113080403196180c1181c03480032490515401d041c001e9001a0001e81c01040f41910502c00c2110700014060740f6004000d418a04880180c880c01144514404414000416102054000c0c1161903035100004000e041c3e68460300800318203070081d16440d0180d864140b01180d40d50051150380d014a0f002030062118030000d1350101c0d0b140040c4c420040301c00b482d0300f01c00210700b2000810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 162517571 1250 162516321 162516371
    0x90402160b0c04090b0a0506070b0702071d04030801090e0606090c1204110f06040f15120207050d0809010e030909090705031e0d140712050f0d020318150a020d 70
    0x201070394413484c0c696484103841d0003241c4180314200984040001d941e4483c2103600c0c8030740c8038908801c140c0ea42d41050f4240a102e40c40128440707100b04e0342c035660000b0003140510552003038075400a40d0f41c803000348004546050090000301e82c406404035642d482c0c98031003583e01c07030b248481e078a00e003210031003082180f990280c0f002c651542d1340e802c0c03c078094545088481816401a210039003003502d840c1c1220003c01c842c1c81008d4010801841e0181401d204507109010403501c042c1c10341d680e01052030801c1e81c5900c054102d00014400f0b00200b00a00018090b0f0600c0c0e2039407800550071b0000400811141c0200500036465034400c0000004840c1c500340468501d807690300c4d10444000c00d0681d202c5007040b110172120f000308181710003140009040700d03041d20b14040e0030203407080b01c402c401d4000f83e13038030f1003104c00c0800c07403081c04110700b101c542c0e107900158425005e001d803140c248821a0901640d4000c044003174203040d40444001605c47d600caa014064980c940d890124500300300c0c1e200401a81c00d6080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 162518821 1250 162517571 162517591
    0x62a0327060516050903031917150f0105040f06031508010e06070f0203070209010e060301110c01020414030a0c120809101706010f0f0311131412010908090402160b 72
    0x800c03c02901c82d422981e0901848904089107415042c038002522440b540c80c8210880e0a08500d0300b0b00c8074031841d0200f2024004080c01c141c18241411703080075071144640380a11a64120907084840e5110340300380c800315036500410814160a00e1400c2e0302401c0300125011480c046280001200c61007402403035403c0e0341da40301804040c03c0844004001a141d10500c2e015588108071180040c1c40300308840341100c1d0100500c0c040790b2900300009014020036070004200c0c000200c2d102d280d00310194001e0044483c6022201ca0b008000c00501d500d840328601e0242100740601c000b000a41c0350801494a0544600c01c454641481e100014601f2440c1254107400101c541a5070140000d4403a8415000038003401c109c141e0342c0401e10010314400c030702ca42031f9003019202c03455011808101c905a5600c683c060144c203184e142c481446401c0b041218041d02d104034410320740503c10305010310841e1551600440c000380b41032500e900f030101030b6210909800b030360a0328484c0c10300800d000305075141c01400068 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 162520071 1250 162518821 162518831
    0x8061603150f06180308030604051f0e01080c09090c010503070c1e150902030a08090f0405090a0c300c0510080f0a021219090f030903062a032706 64
    0x3d6401840130305078000318120240d4807401800850503d0090b01e6003c0000c5a01042030f9444003e0070000101e2001c1401c080d84a501010841041d06d1240034182c40c5a001250801c030004800c01c04452402d4401c03500c140c10000b00b01090794800e000456001005080c140a0280d0b15611105252680d030014004480b06070240007c0200403a0075010141010405114444e07140d0002070310303280d50b00c6004081c1000003035042129154142e82c10b400f42001042001145043d0254a464094180d4100c40c00f407050303d004600324103440150b45282c1400300000503c01115000e80301407082d401c43c02e44503000c58110014030380d6641080005144420340d82d8246a00304039808040090f400346c092035a82d4014082d911007543c0007400781e984070411115549122405003221801040d0386840a4003607400c1c400c0300020302d9000076003902168464003040016100c41c00c8a0f40219011992810002013001030b0064080c0c441e40005481d442940481d4a64603052515000701180c0f5680480c2c080d5258 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 162521321 1250 162520071 162520079
    0x191b030c030309080105242e020c091008071401020703120c03180b070f0c050303072108040b011211060a021e0102031b0a0c0203030f07061508061603150f 68
    0xa00450740c01400c1404107c3c10300005032071184000d41e900c450305024059011455a40c0d4480b805c141141c22001c100003044540f1060b4002d45611410102c0c60240101d00045214000e4031131507003003120380d181d014000705800e004d00c9440c9a1a1b00321824110301c00c2c0c00c1c021001c203650f0f0361031020034840394031001460500742c0380140035a150003624400d0454150010018550143c040300d00c1135a000340f98400c1c000c901c4c90701082090b0240c200c03a806100200d50007040004070711401c507507228500249850b40812440441c1d48140440f00141808070a100401580c144003c0c80301070385c0e2040d0480c40c05d0301c0000340810303410f400880a40005034480314500d0581c1d40c40003282030380180c02d50029440c620700300b50f410352103080c0d03480c00041c0c903c0c000664084491044070301c030107a554010240d80d80e1700b91280c513050740d68005550980300107180c1880306880b01044e20030a001c4500c9100507100a59400148070100f201c2c44800d40c05054994450420041524130000d0243c0a19590a00e10b1030070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 162522571 1250 162521321 162521323
    0x100c030807030507050315040603081909090c05043008040f080105060f12030d02030a0207060e0f0c06220315060b031e0a02040b13090e191b030c03030908 68
    0x20151400c4245850f1005100e000c6910404030382e44901c01017030806255104d0800310300244141d5002411070100402c040304103440c43d5404036640076441c0d40708500c83e620303140c00d07808a4075240075280c08a082000100b050a1100340d200d83c0d840c107020405443c4103200c0000c03042c240401c020880e5003980009051020080041c0064081c3c04c2450080080e0301d0f2001c04180001100a0301f544600c0c0e464a404411100030401c80d08002c280c0070041d9107030b0030840c01060103504020000c44001e8145040d000800c0b00c001801064510403000504900803c48248042075021402800d02201c000046145c507100909441e4011480360510b4487d400b114a02072040310311507002020010000c00900c6501022510f600303d00f52645007042c41c85e504c41c8080d91000748207e0340210a403034004108040190301107649c000894100090a004840170598242d85814902420025100d10901c0540118980c0d42642c9001c0886100440b4008d860352920520301c80c0c02e070700031000103406000c28404450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 162523821 1250 162522571 162522587
    0x501050f090f0613080c0709020a02150c0a031a100e0f0d050307150f2301091e02160501110406031802130b0a170705010801050d0507060c050309100c03 67
    0x2a070010301080d07070304911040c0c0c8801000e030210707a0040c03030500c58409101d01700f411070f0f0080b449502200c4003584e8a524003c0a904044041c1d005806042c00003030300f890000140078805d41748050820f140481c2c01c0000d070003c0c02c2c149211070b050b0840c3d400024907a03c1d05684200c0f800707003688500001ea241501002501c07182c0218190103180850394600000300d000007a60f032401d42c03242800315281d0b0740601c940014218110b03d103500c02d050501141042c0740d03c4402c150018842c0c4101c40d856030b00d403c2141e050b1515140030036149440b4650200e941401940a4503103510802d01c85840a001500d80c00c0c01d458514075540b0700000002403c0210b103405218070300c012402e40c03081301444a103d0300040d0072182c0c07a41400741e0203a01c4010480c403594480311240041c2860601403107100e221281c007603030b9981181c042e13580428240000895030b480c0c00d040c103d200035448402800717950b003004001ca4400500103411610380c44140907580069842a840d5012001140d441e1502c0198a0078024403406c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 162525071 1250 162523821 162523831
    0x30603061b020706050c0f01060e070f0206060109050607060207060f05220209041119060305180105060a03021014160c12120807050c0303010e16110303061903020301090501050f 78
    0x19401e01c50500303594012400ca412a8581d04000380c56101002d41c5074208000c07400410281e510b03001001c5503c003589640366000e000282d0380e200d815143c0a405998400040d10854007180e02d807482041140b03042801880864841d4a01508044450303480307906030f51080d002c422403143c503402008400980d48586076850005034140c40040c00494010a602c1c400282016050403c1c040c9910055100e4440401140070340e0380441365050f98414006008207004d0302d03090241540d01c1c00f1100c42c01c905011b000e01036200149849600f0303156908101580383d481c2201e0b030078030035160700f2101c10106080244c5090043c020f02c42c4e0620784245045111040c03140c0120300e41071003442348500410b51081401c0703108030840c18056120348400c0c00640c0d0b140a000c51021080c400000081100000d1100603402a040e100c1c520809030074a000c15540710800044840c00340d401800010294580306801c00c0d014040f6519454443e62640c01003425a0324000c0c05846680d118014410441d00c5080c1030346d480 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 162526321 1250 162525071 162525101
    0x12090c0303030f0c030411060a030f0e0c1c060e0a051c051c111e040302090609011503021c1d0c0a050f01050708090907081f0b03012102030d03060306 66
    0x600d030070000941459409400444d031510007200140c02c008140300a00c03008840104075030348980036080001c010300340030050240c1980c10029001c0c552140004c454061441c01801b0f814140c15001ca0488448155002030b100d44ad251020141032100034850301031f40c40d004002501d04049100d5006000c2c601420f0280300f004001c0015485100642c81881409102c14501103075581118203030313600301d000311030070200300d13201c081e40c0980c1c800c54010041003207078030a0301c0091903561007504008006009201710b04440080d000c0b000c80c2644280e004007144443c0342c980350f40340608070607444c0443d020319176a000310700524204175401100030000d14a06c0003046900000c0302d800c06005c20b0f0b41405110015050042c0825010300b0007107813009407624140064100500740ca0f0045008003100b100341ea01c0d000c201e61081c6400c03942c284090300e00003500c590000041ca103034a45813000c851040307800707441c584080001080c41c00580e410b020080300c1c60540c1c4c0d40170400609604221080700c040042c91074034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 162527571 1250 162526321 162526327
    0xf040c0519081605090102070b0406050c070e011208070317070801030311010b010f03090c030b040b0610020a0209040201080c090d050607120b090126101b08060a03121412090c0303 79
    0x1034001541c01410f18280501d071058035452160010307860088590804e030600303e0003081c00302d034441d84200030700f4486d100c001c01c840d0f9032aa26016141505c1d000e02640b01081c1c00700e04020042200000101060f138400d19108008c0743c0000c44401c070f0030006442c1c282c00100d8080c010028035a0201d081c06000c1286002040840da94400281281e5140004041855214034204d010b2200100780e50000315007149418665250500d0202859101240e5440c4502e1485100d4032401e840003c1c0d4922869000c0e041815a860341d40040d2010b040082c840c1c2841e150801c92032039a901c910f03103a0380d64184030b680241500d00f041c2d038000c3d1080ca1644414040645070001001007541e981401c54115040003116000c1500c2c0c03468503550101d201740300f0a0b5071344a180300f480341c0d20f040c50b40000c0202048080201d0b007501403107400c550074039090392415884444403809001240d90515107c0e1803640506001e1908001e8015007a196000340e50424440000c0e00304201c54800c05100390b03814402c0441c05185 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 162528821 1250 162527571 162527581
    0x1031a0619030b0901021b070303030606020312060609060d0c081611070905090a08070804050427032001090318050d03020712020d020a1e0b09010c030309020f040c051908 75
    0x1080c0e12440c400074200714041008200302d41300a5040310070590113010b050b03000e0b13059034043d113554140e103101c101c00281c607120b0b00043d81c0388080241c401003100c04090f94065118842008004c5d0001e80c145588440c0130030181c1c0788110b0a1150700303501031240c0c0341c0f000c5d5403404242c4070001d404100c480f84144100301000c0161490046070320820780e00715600001700350712004000c51030001d81140040800c000040d420040c0480240134000700c03a400c43d400d222840c000d01d50034000d08081c4404d40008604000c031100040d015007402105061142c40c45420340740311203001820b44008030360030750101d501c1d42945182c690031076281d1409414103481c0c1182c0c0420343d5400942d240c100c0c1c4110600164030ba81054215074407229400340c810340060072907820035150f0f0700d4101071400004d1804081070141000050145000051300d00d554016160001c5a2000780c034240e01820030000103d91059611508515560301c2c0c0c1306010060f401a518241c40e1444196405007003000151644180708100b4100300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 162530071 1250 162528821 162528859
    0xb13090c111204080a0605220302060f06030703020a0e04031815091706040f051f0c020606010e1e0411030411120303272e0c05090a0b1b010501031a06 66
    0x3110a0b68071080003e056513230355581075000c2c0e403080b200941513002415003005140e4009500b034002c903003008001231a900c0782c03020507581c0d00e01440000e40050a104007007100008030361149030302074042d04058608000386150074620f0310094004121100d4200c0864200d503510844080c05002c40ca04039020149440580310b0b503910008000905000c00341d90990f040010030320030140e81078039480500d034202c86645041c0020b4690568000010304c506400505258460410141da1030390180c41c5203040101c00d00349050518041c04201d40054840070756420b1b404507100218402c501038088031905080d24410424210200f40602d45942e0051041c88007010502c940f40d0101c03180c6d4601145481444030000d4102010f00075112500090260030496102024078001c180c040361361401c210300c11103000150b90300c1c090450300341d030440e0664600b0700054440740e00502c10b20414045102c241c80c20203170b0040c2529001d030022542a00d040b021000d101100a40c1907411120481c0c040c20b94907184500c03c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 162531321 1250 162530071 162530083
    0x20c0c090a0225020901030f0812090705041103061f030608031804181518080c1b100512180607020c011d0904020f0f0a0b040e070e03070b13090c11120408 68
    0x2818501220720348d0003c01400004541e200f82102c1c0c1c182880c0d10300b150b291500d038941c034880c40b809942020001003c1d40d400c6812248105401405070307403640c9210b100b9511846564803814145a950007003c00c491000f040a481c13654004841d00402403181e106100640c1c0c040d100f0010545003801e51800066110884a403018a80c580002109030700507061407005944510058420310000a8034901d11401040104c04080d0411035802c641c402801845241d8103e4907640d00010b40902034003036080b040f940303180e40001003410802901d007040503000c0e00384681541c401c00076900554400d4140d5802c0002d0600000c2150181c01c2c8501d001e4020500074503000700003d00c1943c5181507034000d5507480c080e03040ea54001030b10804c00c080d2594a074800170b40c010300595030340f5441d0000180c6030328071415014030700260145c0a00310b0b46141c070200e0300321a00724010401d446500d940021501c0c03600361080740240304c13141d9141020080c0300850310307080042130303081040004000c0105005215000440e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 162532571 1250 162531321 162531323
    0x20706050a02010b0a0305010504060b1507060b030709020c03040f050607170a0903170c10021602090a090611030115020c030c01140d05011401080106080702070603020c0c090a022502090103 83
    0x204581c0c540c402841240144105040c030b40e4040650a03004c01880f0f01540710a00c01c07407060100b0032a03d403180080080d00c05032041058000441041500c0000c2d4040e000f85036240300280844160035140e400e2a41a40c201140e26225a400441c0070071803030070b201380440c1c001e01c0c05403461403500f180e940351401000410b08580f413004400180640459110312003401c020b51300142c60480c0c891030480c10400942c81411101e003140316011a64906020500c03c0715606034800c0c0050000500603030a100d0342038070080000459940d9014a04007150b00c1c3e0007140700b40503002180564070f604008a110064652000ba01e08644c00050445040e803000604001240d50909101501c09a04000890b00748203201400c040541004000550820b002c1c036101c0d6801002d89500507240c0c0c07100022104682e04841c1d08005900c034240400099000707170f0083c402c860245098918483c02e81011a07600101502c6841e24035500203100c2c030303c4c81d1000c441850600b882880f80c07101c440e0310707800080c070101040c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 162533821 1250 162532571 162532577
    0x90c1e03030d020a02031b0715030e030403391508040b0703020d090807050a0b06030d1b0305090918060108120405120a0203060f0103120801060210050702120d090c05030706020706 79
    0x143c44e142c4030300070015202800e2916108601c0c4030307071243c1200d480300d00c0c0340b0507200d00340c07184448915524000e00511b5400044e501c011820240341d42c9560100ca07100d40700c51a4010800301d04121450800c1602d081c400c50075580d0500c04a25024900e014840340080c4002000440d40a000000302c0072034010360040300314030740540c6032107001e4104c0c40180302000000b02135900020f0082c040003400300310705041c6401500400b0141d0b0381c43c0149078507001d1101032100002c4084171b40444202c01400480704540c000d140507030030130380340c0310100d00040001d03200b02c41d00045a04030b13102680010400036015000b1040a000440142040504107004274080e6512405010303004aa90036400c01c070802c0d895070010101c4185080a0403030102202c000c0c0070a407640801d07000c1c8a4041c5014200c154120781c06035005104005152060354020a809041e0500714001d008600e001d40184078040c201004c0e504400286070324183ca08116000c019a0040340640c0091342c0801010380c0214405081341c255007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 162535071 1250 162533821 162533827
    0x102100c0f030b0f040c09080106140303040605030a110f03180d0f080a200d0c0c02060301050d0c050402190908010504030203041206020f04030f02010f08040209061c0803090c1e03030d02 82
    0x103070000385401c0c40504c5035500107182a1144050a504c44140401c55010b003008221160315400201e41d00c5c00d82013140d0341c00d0352041104208284c4104011580b1841000c800140c6050b042440c0c002d0354071040a40c0c0180ca008000c0c0329400da4041c3c5601641c0c403407100140206c85002c0030250800d42d4405615080c0103481e0009420404203411158584015514040020301800f800c0302950304000100c420249c68241e400241c94041e2501c6aa03080c0c006002504681c0382c5001c0180951801c101103c108820300d0000600d82ca80e4005426400d042080145038003421a01c0142884810b610114a0343c0c180801c0c44013098010044078141d44190352820305016140c14480f01a1044240c0070344900800035000042c40fa80c80d00300300c070151003680c850100e1501480219500c2c141034402940c0b000c400c5010809602d8864100b01d1812100052203085d1030003500c43c0e0340e154000319000708650700b0007100da0120746821584200407180c6103007215901c0c011800441c1ea240111401e01844540c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 162536321 1250 162535071 162535091
    0x30905010b060304050d02070b0418022104030806011101060e010b0306120a030f080f071d0a0504060932040f1e06060602010b030d050f09061303110102100c0f03 71
    0x290041c0148100141c40140e90b8201461300640d40c1302c1d00e66100005000301000401d040c00042d00f250112a09040200144c0c007620b140580250701003035982c01418883d08503840c5400480507035600c070354044c1d1600051494040e00141c41c03500e45442e4414942d04d054000c0c000419014611815142000e491689958580020908102c1007800302072052140106030780405034401c11104004009907034410482e11040000406181c081e40c00d04007203840203010200440b200f40c8a40e0300070300e00900d6505141d5440c00458115a91a0441941c407130711802c10a0102140c624040058030740e002c405888100c503107807010b607811406080282007010f5510140103100d800407544011010130740c0d410340d00c802d99241000040001d4030400000d9403d0074403882e050f24000c1288000208140c0f109850055034610421740b942c070203906150b0200040c00260700c41da281a0381000034503c9100020300d190700e46000a40b620214014020f042420100f001142c185d1121604481c02084c1c14042000d20700c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 162537571 1250 162536321 162536323
    0x640060501030b1e12160303030c030501050d020d1b0605030907080601060f081b0a081006021207060518013e0d05040309030209090d08010e0f07140415111e0c01030905 74
    0x800c024030480c5105070080c4054006c0880e03440e00480384680ca00300080d50f20601c045c0c007956401d102d034992007088403a231000542014112007a856100c1d07514040003903440300040d620703180c1726007025000407004800c0140310642001640301800c1418000c18403517162120060001c208036403400c04208004002c00c103070220001007a111466072a0b015500c80703030001001030900c503049078121801c1e4040d407400a0321174000706d00084d1040300e40d07112501e440c00589441340507080c0603201c1d9940007402c246009140c1000c0c460200c801201ca481d10801651603028039010b114078124507940820b03c51b030340d0000c4c100000d04640080c3d0144802080e6075407203040030b5408041d10340c0060b4000c401c0908111105602043c0d1602072801511000350381d90700c0e0006c109140c60700b15603030000300350840c0c080754540d4025113170504c03020106a605071405071203400c14000c0d2000921040042142240f581000c194140501c1980d15440c54005c1100e50701600100d59030181c2681c82c1d8180744d0b0751401c402c18000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 162538821 1250 162537571 162537589
    0x71221090801090602070b0a0b01080c0903030403020a06080f010b03010b0415020f070b030105120c0d03110a0c031a010b0304111003090804081b030f060640060501030b1e 75
    0x1445070000c21098409050020107944106003c42e840380ca1600064110102d520802249050603503456220b42c4d5189041c05156100c4208154148070900c40040140d170740003c80d2024014540d40d0312001e0901c02c86455a001c01a00141000da40520040c04690520001e490882d0301004100203140c4443e48140d041560307018000144d4058080082038402d607400c0114102c1d08107840042c0900145e440d11a1a1003805024030350040d001c42a20000ca8400d01d105003030800b030481a140030203525070722080440502d5108403220540301d60850141c02100c007032540103044101d180d0f403441c07038a6520401041108146c01e0f20481074030244025a078884e80c0420505580301d040d0a541e01d03124024696500c9482c4021a8100d148102c184194140440c01c80352860001d0014041501c440c0100003c100104204c00000e08400c0007044040140d1400d07100d0b590324101c0384a49602d07501507030500345d03143e07904070324107242c10102c6000691312842c1e00d4152001c035006510806e00149000144081 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 162540071 1250 162538821 162538829
    0x80402060f0c010c0e0f0402070804030803040804050303070501050f070906020a022107030804080106091e0e0a080d150e07020a2a030b01060206131104050411060d06030507122109 79
    0xf41c81d103a040c0954941040e40241251011250480381300d140c0000c020591180c400c006201c2e000512003000040ca0410107144c1042c8101a020b0501d40c50b140404e1941d0015801035a80703a46440a01601c00888021980c104000e4078282c3c2409040c1400607540f5104020024000c9203401c90700c0382980207004014804184081c02c0d940c069650381000c90003a0006e019a01c01035180813000907258589104040c0d1070035055601c5c01400d0050301c0f00200809101c4a0b02c9464060310300050001a203d4004003002c0305403020000d50605400b4842400d40941c2e003004035104003a10502441d06c0d00050300c059003036440b07541c6055001c1c07101d60040c12105401c881c100c14000d01c0c41b02204118900090b18140c9041d54200c0e10030b941c0d07074100807100a024140103000340101208a0810781040d80101d1f43c0300303004800f072008c14014070703011448aa1150382043c00c160381d2404c1c180104440bc0c08400f00400c4049184066910b494039060806040644e4602c00c07006040b4400ea24203006100301d600030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 162541321 1250 162540071 162540073
    0x806090a061a090312180112060308070f110405010302010e0f010c05030d063f0f1506090b0603090303070f090801020a030606030c021f02210a0c08060907080402060f0c 74
    0x5002510074480d90350700035a18103440382c00f034121040741003142d14056403061b049041020560b94050001940c4640c8031012100301d40d901c656012000c980030b43d00030601a072060407420390703003040ca041035013100c0303d4511001d107c0c0f403c1000410140c0e80c04a02c039003c460003100c09180103224a0010780b549500d201c0b004015010100341c0340344454440c1e003d80100c44e45042c41172000c2401099446202c9030f9084810500ca504880c029005041610307805d504d00d00c0f4110038107003440d11b41c40785131400075070002c860b03040c40c2c940c2c00a001051130340c080d450f00c0b942e09070754072411801d0075400551a030000400d41c500300094417404290141c03040f92014010100c80c0000c640e19500e850b80103020304950b0240b200480c0c10803441e1031042d44001290801d440305141e0103103a504044c50600042c1d8011082c0319103d0f40200e01d211003a012031003c450141c0c0c81218001340802e10f035079000d071500388020240342c41490301200700100c094101407401c2d4016812038040b035980003000380b042010300a90000c140e031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 162542571 1250 162541321 162541349
    0x10209010e13022106040506011b03050d020c010207050106210c030204110403080d09020a05060901020a121202040b04050405010b03010807060c05120403060b01020f28020a0305250905070806090a06 87
    0x141d02007481116006a00c00c6c0c82c240302c21341e078020044d81c0da4104c850488911038644241140801d01c99070160505513110f01000d131a040c0511541c3d820781c0c00c10a801d403416556000100044006101240c981034070200e040034034801d103030304c5202d103850840c4000380c0543e40710907281d150780a1034000c0b00d000c1c2d544251081c1c1c44403000311401004000100b8100d002d0070407120003180b41d14059055984c807001c164000c1c2204119641c0e0b10960b0b020900c10301081c0040031340200044002e034000751014020340c001903500e591410041205694069200461070349003040140003114000c9528010340d409801c01c0128002103103010703485c0030344901d0b4450909070040b0700841004090b4011000700c1600b41d00715090f400a0140c1c0e2a1960f00143c2c1e01a101d0342c400c01004103d5940103001d4190034001004206416500c2c3c42c0c65003001402e01071440304520341c1c06203d04d29214a1002006408400000c214074038000c80d0140000c030014048902c180d9110b0b001680c003030615000341014203071640400b81 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 162543821 1250 162542571 162542617
    0x12020f061b010b011b0206090102010632060403080f07150f05010303030b101b05030d090b1009020a0c03031a040908030105030f03132c090a1202010209010e1302 71
    0xc01ea040741c41d64400303508080d030040a0f90b100d54014603031601409007501c181c990950800c110359111090f0181036540310314000658265030314500d0300402009a030040000e401c071204030441d40b009a0307030302e2180b14180401d20114420b2015280c0f21040400c0a80e81c840e400c1c1000302114500040c46884c003800d18800040d0020543c000038100c901c40c1c0c9081c0b060300740400411540e0b581426046001a041402031020004e1410841038480c0c000e0050701c1c42c00112000c418180c071180707401640d0000c40342c001e210307000d130866090b98000c0c8000c240460030040c401c94007c00b4020010400307030405451b0100611005604a080402c0a20003802088030f4401032030b04c0034040d0801d2042a100e40260002104002d102204031926544c05081240c4c180e070074050a800410380440004c070700341c80c001c0c003888c4504e1001034505001b00140c9000b050280698070700049412071000401d004c69005000715943c41c2d0b00b1652080c04428111141403280c00b10b440404001e004084010b08044d61000401c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 162545071 1250 162543821 162543847
    0xc0a110106030c030c0803070213020f0903060f0402030c031203070327060603031412180a12020a052116060b1c15020c1203040203010920010207061812020f06 70
    0x204682c1305e600341000d1596034412040c5c0f280511440a900f0442c140c801a44004003a801052109000d04140d420441c501c80401d25001b01220803104583c250301c24441580303000c0150080d9244210001d210002995050f040b41e4000606010203058903826148a5041c125602119034000d002542401d0b11a074100880a0f00403440182c012681c40c40d41904801510700442d84078043c3d000d861000ea44a4400d081e900c5044140d07040315500604c6141c80000350031609003029024264001d02c1030b04041e0401505244054a0141e060701c0189140c414541e1004151031280c03100d02c040340f800026501300200509040840281c0c04010f030004251400e45040d90640a070b0b0050840307160141c01c40f27442d60124420401002d5003a8460008204d044410600450703002d40702800104110601d5030791005811000c0c509140300c1705009444003407659041040380300920044c6000445142003508810140c0c4a034021040e0032003071a41e9a0007591203042c40c029000101808103581d40340390013510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 162546321 1250 162545071 162545093
    0x20d0308070e1c020904020607021207080601060c15050702160b13080c060702061b0307080c010b0f100e030a08030c090307062a051011030907080a0b0c0a11010603 72
    0x10030540b103603400761414445101402902c240c1e0105121407010303001c210444100420480c0d1100d810001c007030058503810340e000203e15144000f80b201500f040409401c000e016003020701000a842000302c040b40090240d08a26414603900041584a9007801c07410901c8008110010405102c2e00288400c8406c0040503c1d0340030f00c00e00440241c86040054848100c1c0441d540e10240034803560b409490500c0c01044a900319030780828111408200e428110703040309005842c01d0b10301054a00f100c0d0421300031410801c4007200d852080d180480000f415031281d07103100004006031b140b07600300f07103844c00c200d068021600113036450707224540b61028010700d602403141c0501901460314009442e6004410900c403a10302080010060b107030007080c0800300c43c40aa020f8540d0301c070301d1105484600c014810240700520800005c0d40d2464006400c0d0703d860b00781c0e8406101e82e841901c012000c41c98a24005401c18400b082a50342d640c05030104079100613021040c1e0880d13510b016400002c1100e04012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 162547571 1250 162546321 162546331
    0x1b0115060f080105060301061103070c03030206040201120902130e010b040603230d0207050603060117090a0615030b0a09081201080a03080a0b010509040c120f050405010f1e0e0a020d0308 82
    0x55107155020408044544600070311516030820300078001806a82d0280e64034008406a40003241d00b8143d032500c030145601005d51064015030008020307c001d550380039081301c0c0100010f980a001c2c0308115408036200003481c0e0310040419546400d04185001c003908a000042d0008005000c0185c503400d20307281e840b0251500108822180d13036909008400800c5428004500c2e8015141440c50581801004e62005141c141003221f42c4414058800640322814010b038015401003215050340e00e4024210b50203180c6d45e0300c0d004448802000000d601602d910f0780480554004100b0010a241c252104d001c2c41c81d113039844069140c0080b50088000690612050299403001c8054a440000c10100d0703c075052001d0010b042048510014241074002180304005440c0802d90214001102c0d4200c44404541d800f0040d210014070041c46400d0080c240010b00981080120181640011112000151075200e0075501d503181407a8060040c003810284640151003503a031901e140c5002085c440040354 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 162548821 1250 162547571 162547577
    0x51807031503200301140f190203011e0b09220207080403120e010e01080f04050a080309030a030b060a0e1207030611030403030f09081617180a0b070c0b1b011506 71
    0xc43c00068074050094a0801c040410380c000701d17454040c2d42985010780102180600003480c8174240b142c0b80c881c4015802130210281e602d0880054003915005010b41340d0040c0ea0041c014480c184096440c218001699201c0c144107044014650300352001038045c0c0c8a000c0e0041c00c001c1000410301c40e241c1d10103000f0405070355400600403500300c0103413101207076841440d000500c4d6000213405803071812481508540544200e4212910a54907510607900484402c10f90381c20214000d094940c05000b41038a440c0103d5506007441301c0000024015201c4c4591203102e00c03011906859480014007020015540041e024010048001300c9003405600c1a03904a00091604d9035066008000c2c1c80748003441c61b80700d8039852504030a120b10380f44410b00034101740c030100c80c4100110009c2070008020460f031038044001740000c0e4540c10400c81c0300015030703001c840c02000800c1000005562036480000341c0310703c445020345030039400518560283c42942c03894031a61034921400031080b15616150700701c900640e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 162550071 1250 162548821 162548873
    0x3050d05030f07030b1810051819240e040311030910030c09090608060f09150705280806030705060406051c090b040822051807031503 59
    0x50044456200c229207001c40b0040c1500800c100a01c2074008018840c0028455400c1d03402d1600f000b03000d514103541c104c03e40b9a0525081003181070442000280c08110303104104c041c03070003020b074081032a00407020120440d42c80302c2c68081d00104039541c030b017005908030740704180c2520741c88010510b44090b038060380031a00d0800005075190002048544d42d40c0043c000030850020014184c1c060039050500b101481400c0d480482c40c50580c1c41a44010007940e00100308c582841c1001d20341d14140136010140c0c0703401101d607000d0070004c04980030390009000d180995a507150091588480105c002641d51603040d21440c9548643d8441003031402064224280c030600341c3d50750704128240c070581c45070b41c000c0741091001042c02524204942c401c108454004502d10b5000e035170350020040211400c480d49440418401011403824881038482d02d4540d400321005401e1100060014150a804440d01036004000900440c841c0c0c00c00e91103003069031000000d484e01c2c2c1c6884440c40c030002c15030a0982d00c1c6a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 162551321 1250 162550071 162550093
    0x50d09080c4e34060c0206040b0a020f0106060305070903030c30080601020703020a181407050915030103031e1b06020403140601030b0106030b03010b040f060305 71
    0x40c0490352040d4a1008204082c600c184407030354442901403400c2165105034556941c0540104003211039a900840c0c00382003038500612070300c0c02500c40e8864050200d4100c4541d044680710301c01411041d1041e60420f440c640b4201d00c00200c0c60f1049810003500000b022585000c3c5075000074116450252650081c090580c403100c0c21000c581b0111074000c0003401c00901000424026400d0118040c002c6101f410040d501c0420000240c018070300750101c0745030075103079090910740c0800750a030400c209101511281c0d1941e00080d40145172805a01c1144522030302c8092004c0c07481c4c1c0080ca203004144040001c3e407400036000b90031600481c912038001d0440040018080850b402107a050300d605440725880c09114040084205403800d0040d41408018500e042c03102c044d05030000c03540c0d80f00d541d000d60b50303600394980000780c0001c1019403019030740503030300500008d11074900c46415a10700d0b140001e0301500285c0080d0140a4080d04950401c0c0307404070054140d40c2d107030403c13001d46c0d02810072a1011002c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 162552571 1250 162551321 162551329
    0x212010e0708040c06050d06050a15120b01021005220c0504140108060106030c02030c0106030b042001170a090f0c0608010b1903091703130506060105070807110607050d09080c 77
    0x440f002410707208001e409002c02805480a842982c244c990001620750b11100820800159508403140c0520b4000791000040d9100c40d010160584c4d00383c0502c0254008070010799500b240c6100c0c1006e603500c41d0000790745450480078400203049589200030154005003404001c002c2a030043c039024900341168210b10400f01402c4504171490b000c02084c880e071900324218001d060380d0345004118042044801c4240009018640c0618003c0f1100007d90516242409070400c1d45441102075250310f0303000c1100c40e80c02581410469940404003403003540d60002c100c1c000c0004ca40000e0101c0e03242c032182c406002100e0301580984401e92119500d90340c903200701018170700440134098600401c1d440418100c0307110b60000700445108400000140240d81030080c8690170449480302c402e103a4802240910400300a2103400210a09001c4c0c41d20706d00b900c0c2c1c81103034801c000018100c128403007015048d545907081103800503a041000d56928090b2803200034035280d81e42c421031904c0d00c5410740d004030a2030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 162553821 1250 162552571 162552587
    0x2030a0504031b020a0513150b03010503010c08011202280b0c01050901060308160602090607031809200915071b15050403030e040e070f09050f040b07050d0f0212010e07 74
    0x42c0051168400a00d00f03410404d0302d02082402c80001f81d100d00400d0b850340c2c449009840640b8000c81d0b1151a5130402040c1030840710040c0c4201c0401c0482001088000c80c0001d02201154055410911403403842c07503804036640c1d000d08400300320003445100046007800f03a8094294122030764028030044e01c51960241c2a1809404007416000080000720707410220820105005031003500003500f04010180043e44031380001d102680896070450341d00a034031141c094908090007011004000c0e0500050b110741c01a505404512804100080e001c181641c0380502003208002c40c452480d034810092601c0d504c5410000100d601c008a5200701003940d0401c000445520703199550740c1410f080c6107032812a070166100c4000d0750481c2d42c915100c10701c85001d004900150110032820903005240850103002c80304001c0c100c00390440f0010030b00001408210320b00f41c020364503241403a20b07003c0e082d0f050b0000300900300c180d9040d81d10000d039000e10280e000d090a030495112116440c0c0656840d40d003954494 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 162555071 1250 162553821 162553823
    0x240e0409050309090a090618020306070206150105090109030602040b090a060e06030a1d0d18050f06070201030903021f051605070f230105010b130f030b0601080408070602030a0504031b 81
    0x90802d01400d80f203410700b02030141e0b1001134040b012a0140240e02ea5804540e15030002c1041404214104003d60400f0000e040d0010100d00c001d1a0f00d01c3c2409038801a001450070580c100200000e52031180d1381300d025414003443d000303070085540799925018003256910140c44280211201c1000203031050082c065a8105500500b410b45169694008100207085460a049012040e00e903d0300a910b401c21604110020780d07254030407420580d80c0743c925225a42d900c021303c18240c5503404021602c071a02580c00c2a070342800c000c10440790b1443d050b42050300141d501030010803408a1804030a00381e400060080c825100044040c2e011180e040360380d03104826025048540c00b40d000360018844005145000e0203110300d00198141e0b0200e207500b540c07c00c5e40324041c04580819010200e0049140b0340c001400c45004400140789150f079040c100c2e1100801d40d506000b0080001002e011100c011168103550002e4210366038a0300300030100c001d000a45003540010003480c001d04e80045403140c081612 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 162556321 1250 162555071 162555073
    0x4120c0b13030b130b2e0f1503110703051305040203070813020a1703210405060a0f091208100f0b0d020c0f01060324060b03060607020a240e040905 65
    0x254103503182d04102120241210a0b0b41e04c07910001404034949051140c003d8959501c05400304280b8032400e500300110700c4d1440ca800710040300c10001c1c2c020715400042110948550a0444440c850b415001444a05184400040c00080703050403d40d006000301014507170b5500c0100150388035400d000803800201d0314000030074ad24002094030030305110420f24009100801580c100d94032040c4880520011310202c11309070b40040750840d021040042c00c14040d2015402c00c418502d06501e0300e541e5440040c150700203041c2d0307030344c42d5802503141d64209012042e0022800390384500190001840b21034125002040e600a180c800301e0440050341c00340e002c8842e96003015040c40884640c030b500940c031001c0648107502c079081c005c2c1c800e0700c400c3c015240154003d403040000c0f011954030358165000781c1410522034034901382c002c1c40b03580d00240903207801400c02e44959403188002e10200b45080c0135a0004640c2c1003101c905880038104040703005142da141da50340c54106d06a968180407c0c1c60313007200000c00d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 162557571 1250 162556321 162556357
    0x50706021f09050a17130e0708040312060b28090312050a0504090608010209030607031b0806062205010e030f0a022e0203030403170601020607050d090804120c0b 71
    0x4005540d400c500c800c10b0044044e2120b0300c1c030942e10503031790721068698a09080400b00c0c5407080c0a0342030710314000030030851103001c02d2450690001024400000d000030709201004000c0000c1c0d1020ba48403101902902d888140c3d1b5002c0048240740c4003610810366103418009400c08501031340f04201c1501101d500c20740752184030003011002c0c0c4890304403086040401ca400d100000345100c0a00428004022203000165205006028103003014001400f82e01030500b8001c00c44410b1402c4001011044203618001c01c2c2a01c41400050366031241d0076404c1491098411303110fa505181c0f900100c100c07142601d170410041010750a154880805450410703107138000e20040400b504018038000001c07081c6014440c0e580c116041c10b5a452a034000c40c4800503800481004101a044941c622a802c40980600c40300d150600000355104401002d180803c2004607201208506980040880c03c4c0d000c140d040e00e40c2c0d01c0b41c0c06883d5a0081e854207880c01c004c80080041e8000b02d500031592190316000031505c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 162558821 1250 162557571 162557623
    0x1c0b090a0902092a031006030b0105070308190212070e030c0a030b010308030702210a020c0103020c030a110c0307030f0c0603021c0e03160807020108010806070e040908090d0503040305070602 84
    0x282e001c9011141c010901d1803280070034070040384d800642c0324002854120b400c0604102004007100c4440c00e506d41801360410034200404c2c1c02100712a07020b1011441c41e2100c0d545080d0b000041c5c01508842000c5290740424000316a8001030f98442040d01a030881d40c4510714101004488215880042d00d88600c2c0401400402c4074000219400402030048400d1509034403200c51403180014007030401e4081c0410040080b0f54140990a10088240381c1541032543c0e5071507031502c0c3c0c03080000328402c1c0285410306118910050003800301c003a2000b001d44d81d055a0300c0c01c040c17800b01071451041326a0520004040707091400f0384255800b504006107070314401031100b00d12400030610307410200b06610044c4000f003544800344d28011452031296080b2521018244005001300d441030b0845007180e004031041003042e661000340c0c4d440280c0c04032004240d100c80350030003440074030568202640140d00090000e09100300080200201c0e40318904941890755242001c0361030310f00080c0c001030700f0002c650b1020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 162560071 1250 162558821 162558841
    0x100b0f060c0a0c0303090801050a0618051906091508011a1c08030103030e0906010e13090c0f080303061903020a0b0703170708060112020c0303040204050c1c0b090a090209 75
    0x3403141e0031404491896042c0c0c1c441100300103082e4030407000500c00c084140f00b2140203004203034006030511001c0c0718090030180d007203a49a013007080240b81c03166542d0000d00d00c01b030030002c20381c1118201c1004000140c1c8034018040038213504040a5003500e8400f200081c00c0c01d052040c60441102c00c00d810100700b00d094204001c1e200d0564401b03403810005110000440c0c04200118020b42c0f007500c400d907410141c5801e2240c09100140894144480300b410500c0c6516601000a1490942d00c000a6a0091407030022a4804039800403ca0700540c907001291103040040198050b440441d00180055803034024580e040000b800000c0d04220000c2003002071034424005030a083e80700313042509038070f803070110700c1d104c0c84c40212401e0300002c008105021455800030380ba840042c114a10642c42e1841100c0c0103507070bc0c4030282c0020f0140f90740b000095205610030059900b07a030405601034911042403130344032014049110b1224410a0000045811030807035104060a40d9400707000361441c2e0752121407075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 162561321 1250 162560071 162560077
    0x90b010c02130b131e0c08040302150a090f05060618010308070210030207060905011a030304141c02090c070b060a03030806010c0203190302031b0309031c2a05100b0f06 74
    0x4140c0040c407130054100c0c0c1920b54020304507004c88070240d841c0c54204c2c41740501d05a402d91141c1009204661090001180e8040b404241d00d030382a8000c541c4540315002200b000703040340000648058064842007003000b02c00b040045c0a45801c17a03218401c03050401e80250902d47c2840028000c0404100722401824050421000301049080050a1004c81c1d114001901c04c2042c04031100e9564642d4181841011485540204402d80046040034203010814040c8038503500964403070101f2401e1560402c1d0300b90566100c456000c0c2c040340039802c00803680302080e04400d40440e000c4098000107501d50401240703200841e901680c840c1e04a868401c019200d0800001007640c040c0144015048400c3c3c134005242c00c039510960040d65581d40c0c0d040b4030348c2d10384441c2040345102c0c2c2040004428650740041c1600d0705009811402441c1481c0100544440b4103110404e4603203490f04c1d440c00e412222581c0c244084a02030300c00d44005d0000c01c9080004c441c81d400000364410241201540181003410113 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 162562571 1250 162561321 162561341
    0x1226280203040f0902071208220f02150a080114010c020112110c0705010212120103030f02010f051003030e04060e011208130e1e0c030f0a020d060609090b010c0213 72
    0x680c0d2800f0389580c96100140c80c903400c00540d0030f40000340c0e44104200707000032070910101072078003000b1400c1403860420700145541d40504031800d1201000140f02603c40d880140d158014003000c485d0304c1c1c52100c22895080004008003244000f00001101c1e80e001c000e001c4c00042c141d4840b80e514140390700544070040404441800c8503925009444540072000c000c103030b8982808003c09095140c01d00081c0341510111300c0415121081c44855401c0090048643c15a40c5c541001500380da01e6000403801080c0041001794418108014480040c2c0360809a03000c1c3d074045d41c0e503442058410b00034842511514810940131107061001003040f4820b4500c2c100d000c52041908520301820300510541d103c45030742003030401c4452030b41444042c2d03660008401c02248845284049031611180041c1c80380401071100360040743c8000028205040d81d411110103451403c010018071342c903618010b03e50013807070084880191505e1010021580552840c4003c6540101400007020301a000c81001e0403031428 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 162563821 1250 162562571 162562573
    0xf12020a0201020c0d0801230907030902060f040f03020a05180a05130203060f062403010b071505070206160302090603060f0d020310090c090c0206180712262802 71
    0x2022030040c04042c03003102e41c01705850340d5902c0694104003080c203082c20220705401c00004803c50654043e220b2030075450b8031412500300000e0844690011039100d102c0c1440181e08660001408180e8105a0040c4400e40e80240c907074002650302d035024003807007203038016130842030b20043e80015801c441c1c190000d40e480348000c404800c0b5002144c0c0824a001020380e9041030b590f02600401c80d031800e1444429080210000390916165400302420040d84810f0248070390007000084c080d018001400c003180294401440100820310f81010025200e2a0549040400082c240d43c41c14905101c2c3c025528410f9000b0801e80c51a200d4104128141c0c60321008160414480800c1c480969402d0200740010781c030007400441c0a441342d00c0d10300700c01c00c8150000c1c0995860000013410140c0d000942030f50010880c60b4a808803c0d001c64030500c0c28000b07520a030a82d00c101c005c1c000c2004209c4028140300015600d00303041340c04031060040d00f640a600703032500e94039104a09038488201483e0f0f50001c04100b0780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 162565071 1250 162563821 162563827
    0x90402120d030617010b011205150a170c1f050c1c080103050c0d0c0b1803011109010201061a0901050711031c120603020f04150e040308060306070f12020a020102 71
    0x100c403a60070050071080d608040b80e03564108103d0848045140c0003901c41060081020340b600d0f1001030140f00c44000088000307581d680000b454600441d81507565440f004088a20721030340ca00542240c4e441b500d00408581c011400b1960807410000b40c2e01900c0c040b5800c060000d498004401c076515040300350303a80018814002c900044214000007242092843e40e2194115811800d141b46441444001e40f8003800100e0300c0080032501c0300000b5400e445140030500d03540c650b200c00200f103ea1382c5109807603040d481d000340340b000c05c42042d00a248404081c0c009208e03403613940c42d6010030b1202000464000303800c10007070100c0e650320810081c03e02a00c50b0407100c2c010020300000ca4648540318100c800307a1207010400f100496004071030328010400c0500b0900c01d0b2030075540440e114001d02070b100741c029501c1c1c8a402d1171214600888101420001614100d980b03050b0400600a580070b6070200d00034016000400e003254070581004108880c1780e2510718042c0752464000000f94800b071142000c43d5424 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 162566321 1250 162565071 162565099
    0xd090f18090b04030e0909150708060609040614010315080307110105220303030e010e0a02040e01093908030f0d14091e190b0406090b040507030b130302060402090402 73
    0x82c41070900540c0607649004e90f4880c0b00b0140082008080c042ca141940140a001c110b12500d20780e40c1d41c44403180c5001d441070f8503002c021440d01c1c0600700c215a807040c10200c0101c6d070006854404c00341c40c0300981c1e042c01701050f0451f211400802c94010301c08950010071812000c035411070914040303030740185005458090f04580c0004004030300307012940c0441c2044010014140d150003004100c030030010003002040d880980d120b640706c28641000f401140c40d00340045031078002b948404103040d04080c074080d0032502c03200c10016219112001080c0006503500012580c00d401c0c4582050302c0e5000001c618000002c0100030041d0072400701181050780341c02e108606031054154060085400304018460b56000c0b484a0650388440403040c2265803060381d1494500c415a0075041c01e06420844606503900e83d03040c490086d2182c0d80000d060501007000340f0080220014204080780d01800900c002c5031914405240c041c03c0385a070140069210a01040140c074109403041c4d00b00344020010ba4070b003024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 162567571 1250 162566321 162566333
    0x60604031502030108010506010302090123040918151e020f04051810051c020d060605040207050f0d031109061b1002131502060c031008070311030d090f1809 69
    0x203608001005542c000c40104803859090117090382040302403d0542c10b16140b400000c0004441d170a4510303d08500811745a03544050348211005000310703100a00c040411030120000030341d201c035411101c02e401d0403802940c1e11500e101d50940364503a494043c01c0c90003011800801b941065081007584c038400c0100003403d54516942181031a012038109032a031400005030040c0b21155404603002e4039144118540784807d83d006841843e40c1100ca0078112112070400b0001481c0c25040356411502c002030a00621400090704095030741c960003101d189842c0e00000310309030b8400c041c2d0080500e00c180f000b1865450018040d1044a081c0150345a03081502c10742c5034079000e446402130307118070782c0019190110392402003887c019200c00591007441400342580203555050003400040c0304400800031920b5a140c1000b0000100f80f207404071503000d6168104094202450412a4403038801c0450402c1c140b406286080210380490101000c020300c3c0183d0060034280c3d0721091151295204080800101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 162568821 1250 162567571 162567593
    0x111220e0103060902040e0d050405100203070b0705130f0807180b0a0e060406170a02120a1b0e01050d020d031427100206040c031b0312020c01030b0d0510020306060403 74
    0x1000b00c001080c04d11301d50042c0b10803915004820090740e004901408800c0e600141150300320342c02610024607512444204070308600880000a088202842c18050403540c014003404003103080385894009255a4070090031180401e210320a0250404a42040040c03403460a0b1901c035000300d1400f2815156120002c0d442d11a140c0214900c035440d80305200682c145071007108013401161089412203003208510715611103120300020300c10a0840000c010418040c0b180c4408154440703004140074101982c0780542c1c2c83c0c83d01441c0d400d900c40d04000031785444e14030a4140074235009020700300c0800707044d20101d480c041410218100d90b02d0800403145000d140881c0f001d4100310200132220184201c20030051071003410380b40e080465104500740404108034460107011642d20a07d82641500c031122000d524842d20350000c0d10040301030304030060300ca80104069840400903641003109014850030018120080d0501130803503440200800c0001806500543d005400101003e0803c0d5803565401d030551 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 162570071 1250 162568821 162568823
    0x1413030b19021603090605070201051b030c03280804030507030c06020405060f04140904080d0902030a02090a0905061803070311011b02030408070f1401050304060f0c031a030111220e0103 82
    0x1c040c0f001e00d8040c143c2c084c100001401c107e1802c40d1900742c080c0c000030654020701003110302c8100182004a070034003007042100d504842d408184d07074a41c0484c1200b15140c1688200c50701c0c540081541c0c1d4011207214060040c03041da071607240c0900f000f240352030442d000070302c0d01000c40b00d050382008085210360702d000242210500c481c410554544c20800b13100c4c200c80545030114002d42002c13040c080002e02110540708070b0480b1220004480c0c10a000103807502e080000040d4126803841d06220308a2600e400040010340240c04441041c1c0750720146582081c054450302129400034001213002902c1026a5010f95014400109a007152403c0351014020303142d10010250740005400c0014607010320040000749120b41102c0280340c64148900e40d960b0070620032904101001002a003004015489011005002c403410030020038003201c040c0051a115135490003002d03400440342d10a14050188032003c5070060355860900120410195607418849120390010070604004102000b01c41900c9000b1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 162571321 1250 162570071 162570097
    0x80115090807080a0204110901020d180e0103060516021b13060b19020f0c0a0303051c0504110f0409020a060305060a03060903020d090b0901090608070c0b0c03071413030b1902 77
    0xb021303403040000b1142c030078a4269610500344860181603801240d1001c5d090041c2c14441c00080e14502e500082c000b554108038820440b6600200030700046a000c584031f480604a400084030001c00140d80d0380300201c0c0b03410800e4203528401c100e00d080040c000341e1003004640021407059100c0c144580c107500100032040482c4014001c05070b586504000301946c051001c00944410001a008103600c180b6030300024050107000a12039511000c804205014155406000c00540c18a441c0140f003854807204150b100b500c1450104e00145454482c080310f04d94010052540746103030440035800b9140052420398030000303030300d80000462003a0003241c0149229601800710a004000058682140c039005044078600074007500b44181d0300202c4c258296165401c140e0503580d40e41340d00703c80000c10803000030156245a0184200107003000043c50203921aa01e480441c04542b03021000c2c01d004041424903801030001d000c101048038642d0b0b050b040303c08180007422800c0490f91420507684800840840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 162572571 1250 162571321 162571333
    0x3060c09050114030f07140c0729120402010207150806030115050d061e06030f05010515090408030c130e15032d0304050409080a1b0308011509080708 66
    0x1829034819a800e000e00340034200310581002840c2c4580d002d000040080d159020342c2c0002c43c000b240141c00352038618800b401d6050b41c2c0c0d40501506031b260900c6104403200c0039150310406000700344142e140701d42103030075031304550402c030403464242d9101c0360162050f4154014178401080c0d40301d06c0c6110002045d0780e91104109410200241800c6400c00802d03644007c1443c2e9050100b40d0361161030621316900316502150302601140540e0211041c2180841850314203803001040101444905815a000b48020043ca50b201c0e4588031181d003802800590100500c0c001500140c0010091500b0006e24140c2da030500c1900120f4130800714041d04858000e0303406c070341005000c0403045001d0710005015800361a03100b003010170119030130794991514001203e092204140c0440704005842c003c080081040c440c01d0280d0411400d2075000b00d26940020b0310040b001c1103400e910440301c2c484a90b050343e500e04168608a43c4036595810200d1040800034540d0001402810070080c090160040b50701401d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 162573821 1250 162572571 162572591
    0xf15022d040515031503031902120711010c05010f050f04140a11040c0509040207060506010f02030a090b0d090219150e0f10020703151d190201110304090203010306 72
    0x2000215810009a48100401c41882291209240c00c00045003016036603440c1e45134040180300410a080c41107400d440046042d29a02668130003511508540f5025505000c2d130348952a101d5100d140d1f405848500c0304404490301d544038800c003101c814069000000e41c0d080c0000240c06450045c0c0f4241d5092031454148414052803100035100095100000c150f100019a10f6014000c00c0803c0030380f246139a82400c01ea43c600980444100000081086544001e91b150004c02000162000343c0011030514103a24030394000000c5584440c0c070354696400715440c0602a4a05a00480c02460926100c01400d00180c90f0408400510561030025080c03040c02e081d5905030400481209604001c0c150fa60b4560750303103034110421030b920029074500003461a400340a81c5005140d60006050100c0da00300c45100d90096401040c0d030035640c40c405406511031582c096a0b850700c1e41a402185c503400c008010041d8000d51016072541000c009603401c095a03000700d10200e8109074000d03a0340c07503144d1140e81 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 162575071 1250 162573821 162573877
    0x30902090903070b0604020a17100e130b04080306061b06010503062a0307020f0d020c030c040c053403090f050d0302060103060207060617030c010e190f1502 69
    0x6036011412400450030815581c03901c00c071501d00175112a014a07400202d401c2100d01c260740100c000380d01c080917804142010142807104440d2486448803d000010210300780300100580c081c50f040e0403022000098036591034800300c80d8000b0f045107074484010040b24200c0c11441c400301c08040c0d00180580015071400041c1424040000e0140c080156800844807990b84807940a940000b041003115460b6070303d52005034a46a1081014080c0c0c1c4660714444a031240c1c002081e10b66640150159074500c80c1410910046c5c030b2243c4000340104809108610341d44650003981e403140b14a102802c130b24001c4c40b1000c0b46408a00341810340009600d8601404810a50708245e4004e2000ba540d455040d00b054400079266501808010300782500040d9100038003400360400c4020b450380c02d1040104d00c4c400c10150f5502e034040d03031711641c01c0d5080592542901002042503495008070340e060b68548101a5140402c0f507901c000212640c08100b040e80c0005440351011381035005c00d514410585003901113201e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 162576321 1250 162575071 162575089
    0xc14060403030b0102010501051005030a06050d080a031a0904032d09060206090c090103150b130209030c090601090605070302070f090204061d0a030605091005040818030a21050d020a030902 83
    0xa913040d681400c2c0100281d4070750090301011000c00e45440b0351a41c44030032080018003040d45c85103510680c0c9440050a220981c0002c099156240c1c50400c506840046003500c1d00c822207070280c0c1d000c041c00f8001000300307002d041703041c22100007544900314980340c41c4d41c0c03800d1000c0080c809200140d19a10300b4814241c04100240d00210910001c200300002080094020441400010700718204854951640030068221166441d0000d004200c1e0201081c03a0b18025005104600d2091143d4a651042c0e42084401e09018170810b950b20b103000c604004090300e8540c020b45c4101c08500c80c3e9000001c28201c00ca00203000340c0f070381c00409039545140c01001816003400510700d03910f400034001e802d0f4240e07448003102e1040703070790090340032500f42e450410090810001c0300760360b54014100000c000402c42014000c00716104039000c00d00202038090181a0760303006800f002001407000780710700720112002c040d4090b140707031440c90b1152800030203035800d5082c4c0c0c020f000300201290311641c6000c21403500640d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 162577571 1250 162576321 162576341
    0x5100806060904030f020a1502070309170a061107060e0703020111030c1c05040503010203090a02040501081b06090a080f10050717070c020103060902210c03040b0403030c0c1406040303 81
    0x101464106400040c81046019000401713000c62100b031340150342d000703010451040790419a001ca0301c03001122001d0196021203c2100050301e00240807514407845071440c5000f8002c00020902220b40380d40d01c2000b007240e44010118420b00740500b6001407910300400c1405403030300d07010303045540c07840c800901000510222811140c005000402c840c000c002100e0803088030140c2900d0000ca200760042c0d0702403080350421a0194000000c220b2110000203100c6ca1041c03007a01e042056a0741c030446a07840760b81d48100c215076441c4045e034402d028904840a040c0361800109002240341d550040745140082807c54202a50000b10071082c0201c5284203c90b0721440c1c604080f061203155184806802500130000001d00c444440c140c400d69100c2da1050014005a00d0210742d261f640c0300911146420700419a8604100100021010141745081da130181d42d010103007800383d460307540e0168050100015902c081019004a0301d01041d42d5188285445000401074502401c041c140101036803c0a40b03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 162578821 1250 162577571 162577573
    0x4061206200d0b010c0821011512020304080c011e0b01020c0a06260705090f03010902010212030c070c06031416050405010309050102090904050309090f063006070201051008 76
    0xd40106008a4030040340c082c40403404000440309441d10050b9109000350401500404002c100c140300048600304100c810b81085c88031381c02c82ea0303030b8080c20200e1011214821001030803d08809000c0001c2d500519002446456110b080010b00c032509400c41d9442103801d04079002040465072015918400c0b070205d00303001e1010300810450312020403401d007164414003040062051201d100100c0a82e049010310003080403580480c100302c00c0043c0f2a8100402d05481030b02241031280f0340e442c052140d21070380303503040e0040c020781410a440f0303144a400003014004002c00402640e0005800c503000b000c05000b01d92000902ca9403000205915501c0062a00644021800c0f584800d190040d082d641101c2091901107400251441e010b0302901a1414850b0820031220a02c001c111001c0050000000c0c141c0b80110a83e135000910110a041901c0d201d801ca0840424400740401c03100007041d10140d6408084101456101c1ca20b10703280c01161000d0040c0d43d2a002d2221000c4120350400003408014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 162580071 1250 162578821 162578861
    0x311419090206070b0705280e06030405070b1b010603081e030601080a020309032a010c0807050412030e1003050109060f051509010207050a030303090605070c240b04061206 75
    0x7501003181e40c810180040d03c02c081d1a070008541920540842d44074860b10310000c0282412080021000100c5007241c501145503180340b0710590404130309591049404c500240005851b1054481850740420300030101a1005824480209801d010312002144600031003a0396180b024401c141d25134100280418040c030030020300c031b030503079005030300640000390740f20300580d00d4541400903491481500c07603100558040c10210b458000550555102e0103504400900c955080a00225480601107da110102d0303005c4c03006001c10302c009610150b01512900304101940303161170000e621102401c040310006603e50005000c10705141c01844020300040404145640c00c08000600701c1c200081c42540041000c07d5401c22603100304091002000045d041c405495100e0034000c01034019520300f91340700f0b030a000200301a24030941d500501700d500300c41a8010a403114004001c0400c607220442c09250f10760641c0d941c2681d5910a850040448030075440d010703c490714044007034403079601103083e0500341c071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 162581321 1250 162580071 162580073
    0xf1509030f030315150207182a020a150f0c0e0117270a120f0807230301081005060904230a0510060302190531141909 52
    0x4421101c403075641800c02103100c252aa11080d1100c125510850900c0d480f01498030000380c01084c5842510480f40004000010340c1d00ca080c103803201c0d0715009002c0c01844800c100303a0300c08100054031141c003610640701546520349030800d030800c04807a80b50685954842c00601340c0c580348901410206031307040c4100c9030040c81300042e0500c08013807840c04031030a84400140e9031450041d054012440c2d040008070000051004203640c401640f44104c0342c0d0001030101182c030601603001a004031b02c8a5a03102581e680e00318048030b0581c812040d0300d202c40045c82080400c0c2c01c184010b103019001100007000218152202c801c183e8070090b00c031078041c0410034107000c0491111707290400b1099072922011003409a4100080ca04503018901408a0040802e04150f10b9015044502124002c4030b58483c0780b401034220302050041485002d5102d502d041d401d506004050781c1900300c00065080c810707241c2400143c520150384011800d03100c200d0752034041100041031210190f06181c01000d0401c139244171 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 162582571 1250 162581321 162581333
    0x1b011b0308060d0f050607052d040b0c0a12110709020c030306010302090d0b010b120610022a060d0606080709060c0615120c180e0a02040c0203040509010f150903 71
    0x16003001d000704032a83c04503041c00345901c80f031000b50b0360002c201c50381443c110100a00a4004155400021440500442c201d00c07501414580d0f1000700032106181901e401c3c8418400d42c405114600380c1c2c044c080c40c06002c9a02c0c01d0068050035403175265442e100c10009940c41c00c2030440d412494009105010304038170140c1c000196580682d0030f081c0140d0310450304002940781d840d1701c00020a0384404800200c3c0307130300e02c0cac10280c58a16514140d450443c0c07510002c018035080400300c86001039200000d0003e0121030150303945400030b04a800700441c0000702022035145d13880000052641c0b41c8070b8508200c0c0c140e01450a9502c1185841c0440e0400e06050300203007038008035880584041e071504100400c540b442d044002c020401c664105000280c186090303003206d8044c1c443c07111048120720510300d9000392405404441d01c01040540300c00f00c035940c02c000040882c036030608111300c4144408034194542c0c0640c075010f0001e100c8810001480c20051600003803480d03555008115481d4410400124 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 162583821 1250 162582571 162582587
    0x108060a030c15090807080106060906080910050406020913021801020c0303030f091618050105060306060f0f120403020a0b0114061813020d020706060f050f0d03030b031b011b03 78
    0x110081da007075849083c03c022600d040c030030342203902940640e500c0002c0700e00c4158456800c4038081d403185000a9035880d019298070104644c0d80c4411342100620521401c481d60129a02504c6480c00509011401002c1008418501e44102c40540d001030203d108542c444050a4890300920041c2400700d400e0003c6070f201e000151a01704221000000f01d0502d000500400c3d4007041c125111121480d921200400241081604280c1c3d55107070500208090600300112071040308050842e82c6001411003402866030700140c1c3c0710300c1a07801400032010403000b1a64490203035000c1d900610b2035440c1c90600741c91154041c1c0c0120307441c80800c2c0044000c0d031200d1003038803245d242000e1414070300102080440c42d103c88403400d9440c11880000da11280d414194041d2080a0086000b0412161960f181c4070307000d0010b001d529400130203800c0d24030207443c3c241d9811003014402d00d00030a03010802000309182400c184600c9401034200d89a5850310f5900c5802480f00101854040c4c550300b1040c0c8000c5d00b410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 162585071 1250 162583821 162583829
    0x80703121107081207060c0801050f060c010b0a0311030f0a020904030e0409020a06030c09081f0c12020403060b12060f0612120f0301150908030901050a09030f0c050108060a030c 78
    0x401d4600d240c511468003400800010715040066500750b20a000c02d00d01d66520441003205c6040c6031000c100040c9210342000c505a540140019400100c10070400805401218501c086036407541c480043c80c0d00c0b4000050000c0d845000311644001c0040109414028641040b1203d41d00c034015903005a924624031035045501401c201340010740c03a9021501601400e00702a4015460303900014005034107500c42200f2645594800c401d03580c13924000d9071100c10034800c80d0500d01303081204a580012f07a44c404900c0140c0f90600852403182691100184e821550040d42d0b215952844240c80303083c21500d208404040e4005010b05162503006260340210140c03200f80111343c0142016482903040081441500d0305400b00c030740302c4034400c0700814030350301c240111f08d00c80d0340440150410500501f1114241c0345100082c0d41000d000c2c03801101c054101040002c06c0004800000010941413029400c889000b580040c0045003810005401c086028146900980440c502040800c211103200c10981d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 162586321 1250 162585071 162585077
    0x270307120c05040b060c010c0806091003030c06020d021309090308010f061205040503090303072a0308030703111c050406110903030a0e040902040608060103150c05031602100606050901080108070312 87
    0x80000703503012404031b020b02c12403c000d541c641407003103e60540003c40107105c2c800845034944169038080000f80001c43c07a21004010606801800d00096000e80181c40361810940005040a0b01c00403140700c3d1801d2b65005540301d43c0e0340c04683e030a040d404a82e1601502c07a0744c580c05250b501d00740300244521180a803101e030702986d600c0403400f0081c0c00c1c0100e408928008040700c7e1200715030304004461800c1a01060f03840a1241c41c00e1116540300c1d2107100449400016050441c4d894407010b0b005042244112105142c0410030310f5503080038404542450081240c1c0019503141c03501c0c1010884600d4050f1200701c59051050501c2c65600108590300c4100c103151004c8250801004980a8108040002c0d8010304028021654850015006040701e003d208007046400c0e05820341c0c002c40e40941c00540000758100001505081d600e80c03094209111032045076892110704600808588a503000540040c3c0700040c042615030b4402d40d0203000d8030894019080131842c6640c0c2c00c2d1943c080040035014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 162587571 1250 162586321 162586331
    0x60907050a020f07090204090f05060603160e03030406030f24060e040605060c060708010608040507060e060d09030207051306080a110a030503041203030f0c021e03270307120c0504 79
    0x502e10030f12481c801a04101c044898294881600d179001e07400500800c6030042c50404005041c5007680105030155401070081403854540c2940401024000301d4000244080001d00c81c505407403c00041009040950300001c505d211900c1c00c0d416200f034440b5036491500c1c40200c04055100c500c000f0011102981031507d11901c0e4840400c01510b140e82c40355503c0080810029000d280201d1001d2044000c1d60b030b00221680c03240b00540750880c05032805880343d4044c841c2440b245002d1401e001c0441300007031455040001f001c6080050b039190307600c100c00503002072504001e18149100c00c05e000e24080362080c0451820665007599801d80c00c04054103c7c4601c04044456465000010b00515004010760380d44617150401c0c0c0b01d200100b10340c2200000c0c9443c5d802d844080d01c510480d0349140031355004e0007517141111003560b80740b2202c00003800140003c001d801c0b094081c9601080c4241c3e0003c001d006002000d100700b40c01d01c80c0c00d43c4604120304459008000196015902350140d40c01207900180b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 162588821 1250 162587571 162587587
    0xc020c1002070f0305070e061005030103060f061707150f0c08030a06051f020741060d0905060604050103240609020a020619060b0405040519090b0109050c0306090705 73
    0x4a491081c2d07203c003a4400028101006101010640c0782c00da03401744826800f03e48518041c0b01079134810540c2100010424001840002c45a030860901c540d104080801c0c3c4645031108000d2412203c0030340407a40c0d0100d9006c00003184d6031803902c0000407080c14950032100c0e12030b43c0900300c0c02c0c150000070540580000040c00c0502c159001e200545405482c10351070000001180c00e024681c0103100000d403040c00000645445a181c0c4540c0d011306101c802158000440c94100341c150522607600020116003441c019140c460301c1c041d001481c20f100012840c0089070030800e090220180c1101d006a09210051001c00c0c5441e042d901c2c10000c540c041c0340c7c032111209041004248a400c003140840c00001c0404050354000394850045090b041c5a51501c0303100b0381171100301c0c1e50511640302c0c0c84c01c00f404208143d19041d80300c0c0b03a005508a013103c6842e003140c2d000000b1203d02da00210762580d0928014448903e03584540b42e072080b408800c803450340c00c048000440e02000244101c042150001c0c1110b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 162589928 1107 162588821 162588823
    0x303050a1503020904020424050f191203050909010b0406030e070f05041a03010e01020703080a0e060c070503190305090d0203030f060613210b06040c020c1002 70
    0x240c0c042c5568280000c030300005006070f80c080d0b038803025030700040c10700f00f0354074552140d490008a4013070920301040b014091070300c0d1150141340090700f44c69604810300204402e0720384403420f1243e20701c0c1d01d2904549030b01c100400303143c0021110b00009070b40d0001c00c0140c0190b905a4609111400c0920056a45c489940c4250a0f00d0380500c0e60400c254285a0700c6007842c203210200303507411412031030080380c09c4d1100700c000000141c1d8002410802c4c181d0040351030b40c001c61750003000c3c441d0f2098560480c0e6210130180c90280207110000301c060420400b0000c41e83c1302e170050882c002404a11983c00b50040c82c044500d01d110f402907040580c902840030080f20b10461038245040342e5900c50105001701030b0002c000440203801d85480c08242c100c2e04201c480c1410146180c0e100081c480c501c2c2070802c1d0a4090f20381401340b0308042e91480340703030380104070b01c04031117001d60381c40842c01d017000012 = true := by decide +kernel

theorem cover : BRFrame.Cov 162410071 162589928 := by
  have h0 := BRFrame.cov_init 162410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 162410071 ≤ n) (h2 : n < 162589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
