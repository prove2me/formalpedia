-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0915
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:55:31.844168+00:00
-- url     : https://prove2.me/submissions/d625ef69-c16a-4cf7-b750-5461473772c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 164388489 ≤ n < 164568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 164389739 1250 164388489 164388491
    0xc031503120301030f110303090607030c0f0c080709050912071101032013080102030705070b0915010303030f05070c020f0d020102010f06120302150c030a0b0613030b06130603051207080706 83
    0x1441014008180c3c0c1d1401642c50000001b0030720281900ea01c100c03900f150704038070308200070000640f02d102d42c088032030b005604018035814155501c0e4450303000f540c03014426510281c420710080c695442059006408000201120354581c00780c1201c601031789401804100c0003844e030307603481e034060380003003107800d042281100302c0310820703101e04090740c0004501c01101004540089001841403003101d00414940e21100c0c1400a144d5a580e00707d000107180e09001c1c0107582d0420425480210118040c40c03081d00d001c02c01c0c00a94521500300e0324020100d0080160a40b506400358544804d03041c0c904806070307400301070070f89580010b0780034000301c2c2c0e0701c0800e80e80341c41000140c0070302c4150400300b01880ba030300b038680403403500e901807091150550700d55a9842d02007022403e840c1141e44042c0d1141805000c60703090002c40c1101c4a41c61095520036507039031030050708100741842e001060740c00b000c2020f80704215041c00d40c1c8071180e80e4504d101e5403441098000510209104038041681c1035507500000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 164390989 1250 164389739 164389741
    0x408030624031e010803120402060705010207030804020f0405070e040e010212040507080c010c031202030406060b120a1b020601031203110d060e010902180405070509041802090c030c0315031203 85
    0x464614207038412105040c019400d1407031040540007090740f4904944440005608200540007002d60b0480080d20486c5c0c003140400c55400000c03030078009002c00340e010341c80e075440a1615005100a6002c4580706900c542d1400040085454000280c0c401c203060a0780c00003000c0a41a501500a1150050b20a42180d03603c1c1040200301e0005030700415980303240151351002105400668500305500300050103d03031040900844005290b01459000340a54404035102e0b0380c0d1011140c031640287c120b100703290080c2081255015450080822506a03400901c404804904d030094980768103000042c008011111880095031090700130207256580d06890b00d584200c2c401d820401040309215030881c00c204c042c000100f0492610070380303e01030700c2280108032300c42000081000030f1000800c101c0500c003050005010300d45546c400c00881c00d40501400501ca0304c42e004100380c0307003002420401c1d0f80d0b5041003003000501000e000d50b500007010f40307030031030018004000007400d20440d04403001001c00040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 164392239 1250 164390989 164391049
    0x402090d2103020301061d030c1c1103070518090703020916021b0a06121d03180d0f020d0804030615090b0a0303050415030605030a03050a020607050304050604080306 73
    0x100076520500c4036210503806011041c01a800da02003486043c001c6840000780300400d05413120048980600107090f01c005c9400d030400140302002008010301003914825880c4104900454045840241240141032607031404000030107aa000711440052540c07a2800304000b01c1f130400400c030140d64010a08541854076403100340040c1da100c500c03100180702e10300b14440034464400c3d00034004c030f1005d0060101c05043c40401d0b1224101450713540c95090703581d03480003900b021015592170b218040402540c0d981c10004110600c000d84801d07140d10800d00d520144002031185400105d0b00d641c141c42420b0103d80d2400c00b90980d004540c8003900d42ca083c00508280c0a610750504010780ba80c0000c200304804005092101702100d03400010046a802c110500412030680e031020728610301031402003200c0f80c8036030205c1d05040d9031800850120b00040f0700380c001075405122080c2e100c003440c038080e400d40c0f41035100c2d5a03803000c01070300260894400001242142e201c012035030041c8942001655400c110403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 164393489 1250 164392239 164392253
    0x604050d14010f02190311040603050415051603060608013005030a18060203030405070b0d02040b040b0901080130020105120f06010e03070303090e060f09040804240507030e0402090d 80
    0x1425a216201c851600000c22880c028447c1080e003003001810075080070b0410f00160010840540305036400e0181105200041c9482c5c025907204401c03a4140504e400301800000d0107568464101c4401c1c49909401440001e40301420105440032001800307504025451441351403441741200070b4014000000c3c41e05140b074104520408481260681c541c0055840301c08a8a034041079074010b00c81d03046414100001c1c1080005004020101c1000500d82030707441350703003204603400780e0300c0034440d0100802c54410560b0010344039401041c2070510101e0303042c0d8083c3c113640c2c3c02106204141080c803440f040107055911a0741650501811000c4810650034a1003080440e808211401c03400518000000d403114100407506800312541900da0850541c02e2210440c1d491800a000e5030704044012204c100c1d5580b40d49545000394024112242c0d1039042400c20a8031207203040303911a124560701800180c081d40003080762095900741c42c0079408a8080000a4040d10514422540c45444d0b180424140290 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 164394739 1250 164393489 164393497
    0x12a05030d140f06010c0f060e0f01050a050a15030605040323091e03031b0f0102040e0702060108070b180f3a0c0506070c0801060f03120c020604050d14010f02 70
    0x30b0316044101030340c0b00312032000554822110030703000401d17840002c8002a8500480b2100f2841980301041d00c0f042c06806e036181003a8609a40d01982d100c0040c4407500e00b00384200b03604240c0309ca2090000b850210a481d005010510005200e56582c000140038107214a03d01c500700c000c40c0400c2e041c4030200d01c1c1040382c25002107409503c1030010100e10303064001c03050142c92061360098083e40c105600c4040c81140c5415a1074180c200e4082c0c1c42c580c980c251402c5c8010301c003411a0b410301070403a04000b10001d1411205802c00196544000024014500c1c0d040075a407000c104501c40300314030001c50022903c42a200100750381c010201c8411983d0000039843e601c84004401440c0198400c4501030b0707507104920703094001c0c0c9001c450441c03d10550601500074a08a406a90f00303041450780d4143d03050031141158001080210050000d20810400b21080412074285142080c40c411003a0000790720f074859442814030503038241200341d003082403010b410504004944001c01001014140c054041c2d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 164395989 1250 164394739 164394761
    0x80703030e0703150b030f010c020d0f050310030803061f05030a150e0708041a010e0402010801080d02060a0203090a1704050910030302120702040902041d010c0905012a05030d 77
    0x2040406107440e40e4000920202101d40003031300c0c84048050414000020022245140c0e0140102104091009824029001480803580c0101900d00680301c0c01407100d41c0d04d01c40c0b8001c00000700240060900745058010541c0d8001030455540d03100d039000034031203c6d00143c0300d180c10a1203c542040e4190004043c61040c11110000d00040c000c0d03a00d10305940318603004102100382030001240d261445403000640c02849803400c4039140c0100000c00100c004264842c400c1079890108000865a10503646030041046e24000d15a041da11900a5218040107005c00c46269004c00050f40300300f010000c0414081c0c110f014260722021401090040740d1003402114081c208840c00700c2d4640303860f07400e000200c03901607000d4901842c0718290200540d01415080c1c0c2c0c0262507400c02d60150f6158410b00e00040001c4401c00c0922202010090175907094a2007403090080d030890402c1941d13008151020004030070f0001123904401c201208000195000c00a8018480400c4000c414012035200c41450310b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 164397239 1250 164395989 164395991
    0x120607030603060c0306061e02071e03020f010318021005090622170a0f1a01080109051c0c08130b030c070507080303040f020f120303070309020111061510110a08070303 74
    0x41c44c2d0b6a4150155001440342d800001c408030002000340c1840c0b03000303e1a602481c8196000b183e0f81d0302c00d13555011200300005180e049085c90800840c501500b00c400c500d030007820140300b1608044180040c3c0e01c031031000a801340615948a5007914494021218958001405d03203440d103005d070b2900c00b040c81c05a00e18100022401d080803031a03850416508003070004550050071170080c43d41d1060400006020100da0041c0c480c40000c1100350340f1000c0d103000e8240c4c4400000d4441070b50500d02d1905004010f04924006a0888001d10750b80c440720f41d800075900220330580d20080c0c0c4c00a080c1e140307a641d110601d551004000e004184d010207009090a0b400344003261000707138079035203420b80702d00c0181e40c02004414010104801404c1240390080085002402c070010786004109542c2103510440700800020341da80c80120441d07070802109200b04107494010051868181c01d040c80041200c0b640070b01c1070b02c1e030380c0302035011503c0345036409000064002a1000510141b50556641d04848401c0b4042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 164398489 1250 164397239 164397251
    0x20a030603020f0d0210141611090a05090304060e120304080c12011505040c0c0506070f1403060907050f040f080d0f080702100b0402040801150302040501060801080604030e12060703060306 83
    0x44e29000301d902c40126001012042c2121400009a4103410400b00c851064201070203d2641c411f0491620340c2c80600655001004480b1a0b00f08461044002c0005600900d4034040c0030019000105850990b002810900c0000c800070300003880010030003a84d58468400000d020460b0b140219a0b08141002500c403070346011700d640d1046082e5004100241620f5950311410000c41c500345c0c000c12541515030805140d54115a10394505081c01187e200005c215421322600c48690b0051b80c144003485100016400c5003405000100320b450081c22450401174081020b0310b802200340215030042020a400d5480c00380c0e2880d2072500c80d6100c900c69000305010300f0038100030301d000d445502d1150400d0790203081d003051390103244401001c407083e140360003550074840803074880c00034424425041117407600d41701d4807441c0d0710400040c0c42c0140c105004000703411004000f103580000d032040e04a60b040c1400550222802c000c0b4540c51009403c20040b80300380b038144220543c040d030000c0152400383c0014042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 164399739 1250 164398489 164398519
    0xe010209031e06060f010c0803090f06010504020906030103060c11030a0906020123130c0914090d02070503071703070803160f230319110a020c0316180f020a03060302 73
    0x101c20b82c0c0c20319410345400000c0054240e140c41d03e613001d4010300505182c925a0b01c2e9132103200442d0030440301c284460380484100300e03905208004c1c980c0101000c48080d45440b5188003c02c1150006200082645446002d102d603014005c1d80e01c2240c148006044a440743d200800003031103200c5d940b0812000d54605041140ca0004e074003c1c1c401c920070000c40c00c626039150410002c48078401210152104203040001003500c9d8464001e200d00d00b03001245407001c90404000850510b085105003806542c08010304010715100499180301300c42c0c0c0340960100c0401103005990075446102e02c010304142c40002040101000f00d200e010083c1043d0380d4a40a000300c040054481f5441e000c1c1600d0444600344540948880c0c2070700855002c803001c40c240d41140d52080484080c1c2d41e04526505048002140a4050a5040000c0c0c0c1c003100080307008150050010902c98000030b601e014a800415620b0010426108030340c020f141848442a0b08643e1079244000040003040c40f40030072446111808400c0c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 164400989 1250 164399739 164399773
    0xa050303040c05040515010507020d050f01090318030506070f030209090f070e0a08071401020a0615080d050412031202070209010303080a0b0306040803070c0c030c0e04060b030f0c010f0e040e01020903 88
    0x4c82010f03010406c503258244140151215000940220703403084840b42c58200044090100060101000c030010030321810601d00070b821408a000392148604850600f003000c50000240079810501604040108800f4480110064440d40c1c0074a50002071032400d206400844d50403c40c0304007060f42d20030400010b01c1082004090f800c0c884d41c85198003010301484501c100f80e181103402d2505004a4070101c4480d5030b001d0580d0b440c450201c1d50403003020030802085605111102000031940390651900341040009800603007034800180030081480d1a40c602c0710710703590444100e030b600280003849039030756454001c0401350308a40110880d030410a10b0b0405050005500c1c2c09183d100101609603640d62034103c0f080c1150920960309a0454500027000ca9100400d00d4060402803036020241c2c036003401c040b0b040c2d525848242c1d0003607200501c008200000855001825403091800d5440e20040c05800c80d410f4070422046c6900030724200c101c09030920158010035011200307905950784424140d143e11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 164402239 1250 164400989 164400991
    0xf0f020a050601050603060103060302150712050403030206190609140a0c0203040b0f0d0b0a0905220b04061a04060906050f0d02060d0504060f1b030605030c010c03030e0304080a050303040c050405 86
    0x401d10350002005100030b03c1c0c8100030355071011043c540003e00d181e817900080c00036100e60248002101001802d2401c0c0101610140300600c1d050074454641440d41d0703002980c07000010204813051550184d1030050252a422050041402290a02c10810080b8000e045010140c802c4010315103019224041c007400071069070212039070300d80f1032414641e07a841c54060f180d02204580300c00a580356203c0c0d00e1699580c42807030140246520020307030380c5402c0c103c000c1030500151078003180c1c6588034602000510702e895540e0340070394000780c041140c40c081100681a41c0c8581981a801401c04c20046500909a4000d000300da100325031002c1c4040c2c00b00c042c042403c0900d038003c4d42054080000380411241d03604940d4101d4403981c3c00041c180c0e0100d010400712603086c2c54000500da90a6105040e41e5814060b82001d4030307046000d804030120710400030300000d18003500103041c0354480e8040a280c810500541e0002c2c4850340c161000d00525140c01d5840340d10480b401c40394802081004070700c900700b038400c807 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 164403489 1250 164402239 164402243
    0x31e012a081602190213060609030b0c030103020915041b1215060e0607080d020f0403140f0d0c030c0209010308210c0406030b1314010f060201020705060115050c0d0f0f020a 76
    0x42c000c000c44c000b6003144a880590700c142e810525245440b440c0074424405c03d8002c0c0700b140d0300c00820a0551a105100c0700d005404605080003d20050025030740708414640c0002d41c60307211807072800030000414003800381c160484000800c40c10142c992240c200c54a01c0c070b5008031090400045e008032603004100d907014040c020010360350480d41519400d204009151a5006c0d0610b5424041000b101c0d00581c2c0c0071602505178200d02150030401c21400c003180a0307000701d58401a01400710344412007640c1c0d941c940b00341000c00c508084032600f418040d07002d40030065006844c0e28030644c1c40c0e0901020b0f41d4440680e000b002a2103290828011086040c114082c0f2060592240307014074004045000d0200d101d042503002071031031400e480010144c820091180c88202c036402d00e40d07240802e0b1642c8000a40e1200096900401c10a00000c801140301419603800c00d20426002c50b6a4000300c643e4020311482c0c00c1503114605018a40b95004810305610300b56035699451100f00180049840e0714120f840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 164404739 1250 164403489 164403493
    0x10216080a02100c0c08010f0e1c0e0a0512030304110a03030c1b080a0507091104030b22080304050703060c0f0f0e01052104051b031e012a081602 64
    0x341030014600220020103810a520740710030b000c3c044d600c42c1c1e56080d50940c0542d406a54800c005c40700e4158034001c030b9074440d40d40e0b0041d24845445814843c01c0c07003140d10031a003c200a810350032015a03111030070b58000d080c1c0544041e1070031040d0700080e99681e03c107440c1a62080b0103400c6281c4645003109505081e44c0e4181e8800c140e52480303694030011215100445250008481d40120b4403540c100054021140105c008000803807811404904903181c0b0802a6024041001b0510200e008100d015801000d11480e014115158030506103a44880f050001c0c00c0940003c140814403100251603402e0740c0c0200000c1040039203443c000e55800c030b114008407020840c181080d1080c00c0c01405400303414103043c10720500c1d0455459202150008900381002410014010b2200f48102000003000a0b290424a80d88210702100060b6903a50440c01403050441820707031580d141c05083d041024040d4901c0d82d2441c8101015618941c0003042e00403000018404c0c1d4000b0b9886541569900603d05450b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 164405989 1250 164404739 164404753
    0xb2106030c030709021612020313090b0d1103070302030102030705070c0617070c0c26070806130b040510020d0c03050708070504050d170304030806130e1005040f020a0602030901021608 81
    0x198000386d004600c0642d80c0c22130024503c80820721115404000c801c00b40d0107182c0e00d641440e40c00c1400308042d0461010503103001482c02403503c8540d4841041e982007140c2420400007040001d01e0640705401c025010350002c070178001029080409861030341d04c41c81d03c0441c9030b510780c00216005910062038203450422140401c000b58003515010b1040d43c00b0301c910503d86030720b0380451030314514002c3d02250342040c0307000c2e0300d59010424041c50007e0400c030760142905080022100c2c100442c003600181c9000b4084010030108181001900f201c030503010f1095455041c101d40400c01049102e2030000402d0034000012507032880b50f40701c54442e40d82912502e0a00e401d00c0e050001d101e51248080f614010350304d144202203001d010183d0b118502c2665100400d140040910100b65141c0d855044ca050920382c90394400800484c000b45105d040c400001040e40d1241403c1c269429950000b03900031244141c045802680070004003080380c0b0a0b001c40c1c048604000302085066094130a181440c0c0160b2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 164407239 1250 164405989 164405999
    0x90302100504140a030e030d0309050705041e06032009060d121b11041b0f1206090e010506030c0105070b0406020702010e090901050f0714030f060a0b2106030c0307 72
    0x2500071900b0a00603008003215981801c0f000c0d15015180205802041040540320100d20b020440034200345000d00e410711190007950380d01940c0f60040c0c010f40e4070a030f4440300500b9907640c10b8111a151020341c50810b100d1340d6540e0414000c210021000c0500b83c06910b19400c5a42c10121102130080101920f00d004110310f5403240300b0a070701d828029404000031151850a245422207698200c0750280386910000c180840c00c01c41100c40c20501101e0461611000800303103504070091401c60343c0344e410b10708455420160040c00800961b041480d10030719100c2c0540844030158030031403144d04103400301c52031001080c0c01940c040c05102c40c002d009012280001c0e0005000c0d0b005000c1c954410305000028520b420001500d14900b1a1962401d0b0340d1107041103915040c140e6141e40095950034081901540e0701e9400c1024407004001c01590b5100a01140b601e40707500004030010000e60501e02c0d2100c035114201c1e0200c10907084141042a14a8007207030301c502e004230304001a01e4005004010041ca42 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 164408489 1250 164407239 164407241
    0x140a09020309061803090301020406090e0109110f090103060f08010c031a0d0204020c0106030b24010f092c15130204080c09180303070507051507021f1b0c0210020109030210 76
    0x4c2d066070811400700381310141c1e403620240040d00242c9941d4070b0f1103220702c0c1890480300541e0740580c880d00139a42040e0031504a00302c080111052903184200071540d031807400005a003d40000e5002418118100400003105c4806600105045410366800d21004d202070ba0034440781c040c00d038043c55101c5a1003000d680103282c00c2e030040c145840d2030700011500030360b242c60740c0446c0c0d0803c0380d41040707480c8814420845148228410500301c082420540b169030050303100107150010b140640c09a2407c00388003030406800e4244200f00203040f2107605c001c9403824901400e038180c040401c0f01d00941103400302007a1a5039500a03a0700740e804000041024211900030000607490103001000040c03c000746080843e00240000c40c8141000d85900d940c41101785050341c60020740d01452100442880d00784100990f000c60403110656005000310551442685000020304050000e2044c1000304901300050756003041c50b681d14035000b105d55000001038140d0aa00340e442080005005030002425025481c1c61 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 164409739 1250 164408489 164408521
    0x17010c08060919270507120c030809040e0a1b0501020c060a080606070606030614010b0c0a0303050901150801060806010e04050c10030905010e1510030308060f040207020a140a0902030906 82
    0x3010001c2132a0050345600c49481d02c450b41c4054081e070807071807208144107042110300020071403031000c6440d070502c0c1c1e11a000d04140c1070000031b009180004040e00c0c1940da5403c54a441d201441c1036680c03004007451300d8070027201d9114825003076540d40c81c4002010f40c00422503003070707150740580711503d0100c2d807000459030501c0c000c14050740043c0038807102000c245148100400345202e2800010301301100d84003980d41e000140d1201e01c0c42441041141c1a510001c02d80032051941030601081d5a1242050103000d000d01c259600c0269410110006590005400610031036400c001036840fa0f0342c80f4100004001c108840280599000340504401401d10602c1d22183c029207140020f000e40159a56a00b03450316000d8034400c0e5480700708810080192000c00e9600711022500a01000b4030310b0b0f03000380c04060002d103202d218241c0c08e0071106241e103e580441c0c0f0280c2c8c0c000c06143e00305441d82c1c0e000c0c40c1d01c2112003500d0b0141c0440680803603840782c01d2003142d0007245034600400040c1d5170401d4002000340713 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 164410989 1250 164409739 164409781
    0x120e0306062b1a102310030c091d0414060705162f040605120d050708210415050402090f0403030906020f0c0c031612140717010c080609 60
    0x100030b1401e8121400c0c0b007a8503d001d514084044000c040c03400910302c052030400c1e05c0380380350701c000004504003a540344645004580380c1c41c207010a905000440030b5500040d65071004030340902c4420407074030055140d41003600c20351044650b82c1c1401625020710341d440308200e0320301e8045007003006080c041e0003880203814500e922070380e481c1c0070150302d50382c2c0c440400c1341d50280752016801381c40381c0c0541860b1500894010340300686200d00552003e5692503a0381c001c1010000902c40000386090500c40303140100c56400d4191003100343e400e51200781d16801c0d010103c0741607500c174040c0700b00724046551500502e801240c00820410160311820507002190700041c100f2400e1541d1829034100240060020b445080c0400202c0398894142c04055410000c441c2c1000d8031030380000c0e4402c40c40b0788a40c1919015540c80ca840340025807207034503120305c0e80303e0070b545c46d0b225074840e80c60b0018000c42c080c07001d01500c191040c024000300300458425680b0440c01c1d0f803401d6120020000003010f1007032030701920003190 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 164412239 1250 164410989 164411003
    0x90c0405060703030606030b09061f02071a3402040c050903010f150801020415030c020a1e0c0509060d030311072001110f060121120e0306062b 63
    0x2554900c00180a5803000c0c00c218042921a2410424180c062107010044041910142c2841c5400000110443e038801c00d40102800c01100d125000f0344200404800b41150b6588004d1000381d0032500d0205400c844a9120145c0c034440754510048144405680383c0200803d031840300000d1a42040098440b454140301040024014104503680c00d0088000d0320180c1c0e500090140150480c451500d40c254100d22440da00401080110100400b40341e503150790b0f0f610b00000e8807040f007082281171203000d24015085085604044503c07440f10a800c058030782c4210291000e8a90f0381c014003e0208084801c541e0148901e87d0b50408a40260030200b80a404038a0851404000c0c1e84d5440d6a8020540d5210041c100480e20070070b41d581184401080086400c010b00e00c800072a50401e81c0c5440500505032040b1030048144c950307801ea28458003926500a01c608110004003000510b510644503103076100e482060082012070801c000c0d031426054070035814440c0d181000e00540c910b8444c00b40c0450b106 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 164413489 1250 164412239 164412247
    0xc1e050103021813060608060301020c0309041a0a0f090b010e0d23100203041505012301090b0406030203190b01020307060b03070302120d1101052707090203091501080105010302010e090c 82
    0x80e548130390740d500029940060020344a03042000051518070002c01003406603104000803407242d8000015a03800f1013080703070042070002943d00c0040482c2d06c04401c894100c0300d019408120b828420b01c1c404d0030749565400030000c078407160004494403c06c100c02c4039009030702c200422010a01c00b030078031071195950000e48403803502d00c070f8619480d0000ca140c2440400d030340807041c442004103552034403281d0200d0f10410311503035060030301c003032041000215059202c40401c805403039943d00070440c510040c003496400546441d51548060702070760085881c1c604081c0b66180c1d000c0f40d4081403003040f00d60181a4021414034219550f010000c04590313880300d900d48074417040000140d440794240d266801c00f041c0a0a58010f00000c0548800030b400d01c0712200d40d041000304410840200881c2c0000501c040341154000c0004608a0400740c0c0c0303400031100280008200860302c000090800c0e2007000d00c01026802c0d03a40e54004900b260400c1c04020300050f1101a41e0030703146090211a90032018502c0003900e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 164414739 1250 164413489 164413537
    0x40506071b03020303040902040614191d0603040b01051305040809060a1404091e060303170601111203090d020f060606090118060305220f060509010608070b03040c1e05010302 77
    0x5d03540140c0e02c4031a800b034000400340401d80d40828440c80307401c80341108a080002101241d140f0503640400d020070020001c10030701c150749605070310b6056224042c0402e82d43c0d06160030020010602406154000c0741c2c0c000c8021540140352003a140b02d2070b0003007103850400100c24200405644002018002c0042500148180c082071400800c0101581380b40020344d8040d48811022841c9080850100c0030302d00041000460b40001c02090940c010000000690381c031600162445050b0304d070f180c445840b035102694998140e01c07009501403000d020888074850784510082769500f008503040c10240e00800c2c041002d50818101800080c0014185440c41903d46080c0003900500d90703028000090300c0d10240010f1101d41046104809518120500c5100c00c4d51215850390224860081032981e03120002940d00c4401c0d4080b202419a0005549886039103241c4000c3e82c3e0015202602c8940c0c8001c0009070801400d20039411204101c09000041031400c40150000d400450300c841c1054042025401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 164415989 1250 164414739 164414743
    0xf010c080c030c06180601120f120207050112020a0207053304060e0a03020d020f060c030f0702090f1b2208011a030c0a181b1106060105040506071b030203 68
    0x14070903540d00065441d0044103a9080c5404009801c03038003252070078400e41c0511600811010306440742030030710740345404a234503105044100c5038401410b400000600b002c00240d0100b200c000b2900f09a030303007045485010b03112004910804003880c0141e403080200b004a800e0080c0b0100400200c1c000888a00c8103040303405c2044202c02c0822406a90700190511080e50086606031070310350240c51014029086030b01003000d0f078001d8500640315240c200c042070710590754402103991454203c1c055944036024905c980101d50000c81c0e04078411150034000445c0c44e040b030362200340f0422440c1d12403030460b00414554480d6034040038034110091182c410110320035000014880042c40d6040001810b00e012803043e207606541005424424bc003c040700c00155a524600e00c81a901c000748440b014403911101c0100400713200c0c02841c04103400c04da6001e29160052200400c0c50200015120644d94110045035a4403890246079400b00003072140c20081803c5840c030000071300909070007810031600c0340c0000e8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 164417239 1250 164415989 164415997
    0x1020d0c080103120302120711070503070807030314160f0510110307020d09080309060a031b0905090108371a0a0c030501140f01120203041505150904020f010c08 71
    0x10302061801004004110420711080d5104d06249411424100303041208490001d000e01100104101840300c3d26401105000440c0104070080480320b10903a1002c0c1c0c40d448641e584425030100b41001d02c072000181110040301d04100f2100800b8081495655400784142621282950385115011100000300894419104102142c00c1c026417240f520300e00080c58020466544010041c4590042001781400070944685580c01c0700c8031754503040c1464040340202090301a2814040101c5040001b40c0d422000c80415510300b5602403030160b80700d146807235803042c0d001e4254240c4c640344248212803111000c070ba039903050010032621684107100d888514125004d006001850840c1009021180a45108801c0003032000c0c1010302a0358074041400205510788800940203070f19407290313a06280c0c843c00640c0d2a03560440380c21526803c26003441c0000c1005101c3c400340d40c034a03040109a000f9844100015030303e42c0140315101c02c1c1d803107034244a04c0c41401c1c284035042c01101010800028031380d60140c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 164418489 1250 164417239 164417261
    0x2100b0a0909150213090e010e0c13022a0f06010e07050d0209061804061502060610020106180e061324060810020304170702090c0f0904020d020a03200d050901020d 72
    0x1505c07241c10148040f00321003003e000413800d6071500d0315590341e071800412150398850080f900b800b50203200074845000b91081e000c500c402c400f4846900f16600e80c050010102d00d204400c111010b0450240c40d0a646174800c0c0203490001c18070a00262000e803056004280e0160180809403c5c03030500300120300182c20030030030103418a40d07541600725a41401d2046000400440c403180c40c0b040c1a039000a900c990000d00f0716801501c0c26030300041c10b14001d4200e140208010003c00c50403c00c0d204100008003800f860034891409010301150740d0100000d000c002c013540001d0210716160310100010801e03400042104c0380162038590000701100305004041401c0090710015a40380342515200302c4039107a042c840f1480002c2400b01001585441c55055400a07902050700e0740c0759049940954103001d18a140c661144c00018031010b02c1c0e1321030300500000d01d85074900748201d0003426030240320688061120540c44100380810340e0701c180240c0241d504000700e100014a41003000010400741c4a446c090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 164419739 1250 164418489 164418517
    0x8120c100609020918100b071a07020f06010b0405090a0903110105070507150606020312070c12110f21070c050402041511030304080324041b02100b0a09091502 70
    0x5403a03082003468104880c032001140170070780c50070300c24801c0f00100902640340402c40114001c02041a9094480e99408030345c08844228900030034001e65035803a42102a00e54011000005080c0c42c8030026075042d20301c000c01c180920f50341ca21501004001d2240140d080148a08e85002441403e208041c000c1183d03556041c0c0d12829401d141007521044650000240e19040b01008856808426aa50350010b00c2014980340c0302c46900700c4455642203005424000806148115550450540d140d0780b11070b08282d40c0044104814186ca030309001020000e08c0412a0010118216400082a00c144180d040001e102c0e2280b000c5001c980194100034600651140100c8465800c03100c1080214003a100451a40c0340c15a244410b600000e04030004c0d04045c0c03260309001e42440d090000710410003910400c60380c009208503d0442515040712005405000d00081c0c42940a000342c04c04400c0182c00d0b00121440c00d860308004018440c030136101e0440c0c1c0e0501c1c400e150241c0c0010906100f0b0424 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 164420989 1250 164419739 164419747
    0x21908090f07050d0f0f0512030f0a0e0c270406060302040b060304170d110703020601050a081615020109050a0605040b070801150806030c030106060809060105090108120c10060902 79
    0x100080c9071540c516154142644110010440f9603a4035513406252940320302c8440140b0402e1070a000d2260203404000e000c6e000c7c4030001140c1c3e03030840010310b10404841100362a075403910035421040340c2d0b0391103058401c1c2c4c001c200b4242090078501c0e9445d00d14016001d003200d0030304404170510343c5100250350489040d600c5840c20020352801c0d016002401100722103051a5007032594480001e000b2099490510141c042441c40042c400340d449002102c68201d541035a407901860029150b1f0424040d16100d601111b0021441c003200184c0d04c01c4844245a0940f8481d080540e0085c1c0c03101040700c198215921081e01030b00040082c44107440e1507104400104e128102450b04c0c40070840000c0c4a50104408200100440b01c1048222503940c0d1641c107009015444040100e82070a940421a9030103600384640080c50390350240c2c14a00c600b15000584041e83d0304c030003c100e04508281305110155001c02d010941c2c00800100901a04400a048444001101c0440000c0e00c1e29030b0b0007083c029034041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 164422239 1250 164420989 164421001
    0xa020c040c1e170702011803110a020d230c031b0f030a03021c1812020406032108150306040b090a021003060602012d0c050c010e0106031208070905010f0201021908 72
    0xf04007038008240303000a1000750500b01409001c209088000340070000350f4150020b1030750042c481c140030703142c0103070409404d00719034100705c0c40d0303480f02c20400c41648210314401c0b201e46030046804000102e00a0282495031000000808091640158a1790146810080c01e101d42d0b8100300034902140310f82c01400e5100c00c80c1c44c0340600070769003c1e801c800341704400fa5842c02d6104094660380544a240000c541000101d001190050150b034100401103c00c82ea502d828180d0014500c01a10905503180340c40307541d0390294120700e0b21005d08420742641c008004100001d070080400381c0c0c8002680c003101d207044440d07000910b44402401c03564010940e54802401000e0b4217010b0781d001c40c0800b2820443c44a03030120400126081400003100700caa07220303802c21202c1d12880403a24604907a000900020b49030200c3c440c02041130b444220340888042e00305814150003a19440e01ca8041600c807010a5407914006613424565802030400b195030810101c1040348001d02d00b02d001030390503981d200491900d6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 164423489 1250 164422239 164422277
    0x20c0708190203190c0e07050c060709050a0801150308030403020f010f0c030b01050703090308030c130b0d06060801030804060c08070f030206040b0a021e07080906070b06040506060a020c040c1e 85
    0x3890104032062990b0313103d0041351083c4490000c071010700c07001c4074455540340c10031a0a40180c03c640d403260701803401400700c0e42e5071024034034095030b90886410080701d03903034000f035800c88407c54088071110100fa0130800c00b02d055000034652050003401a2010b261400502a00710b409200841c3c01060f41d0700c0d01d0001f09640341c071620b10840400c1c2401440c104154401800055903032100406030940000000c07070410720740040c0c0d55a600c4003c0350341c41517601c0f00e00748902c0b41c20480700d03511100d10348807000035090f1154904c14102c0b60441d459502e01070402c00100c030502d0703041c00c055a0040c0104401c800043c41561580001c40c000d9000d03011a0500f442c01e0840c0c8030014100d104c5041c018040b034154450541ca1501c485840024155a60805480c145206004e010f4106601c4032003c034103101408882150340d881283c040394100002d40e9003100b0082030780104907071040140d0014141c07507000c0c00c06601c40d00410840e03060981e546240120450348025540d04200000b9542034810303d42d101d01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 164424739 1250 164423489 164423503
    0x6170c040c170a06080106361803080901050609010f1203020118140705010513051c02030115170a11010507020a050907030e120405181806010f0314070f050103020c0708190203 77
    0x2c128000923900090345045208680446c03550140e055450b11644845505c000c1d00c030248090240d45480c0c0c0b904026000b0142116404815401c00b80040c5061038003c091606813040220500380301c0e800e1444d41510f522440008070250340d41d4100c1c0d00d0001e0080407000e03041e18880c801c980800306d0080900d030705203600b030ba0040d410301405000d8000034500c10403548003075500960b40d520b40b416001a1a000703401030024084d406510340b03042c0d60854005006400300b030310050303140000d1002c0408902d90b6161102140501300c0702ca0001c000040d17601c100010020710f0700040c0180c008a40310380000f41d02c00301c00e4680b82c0229903108071689041d60140a1b60a1988400e130079141458900f5010075000d0900448134144c2d03428007000039108003415242c01c5040000e42c030485109613140d103585c800e41c01c5d0501085e80e2a1107100800400644c0008403030043c1d0300400e070310b10ac020386060300540103500901640c01907405880408074520000b00b005440e0101141c5c0c283e181c20007140149810110303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 164425989 1250 164424739 164424749
    0xa081c0c050d090f170c1207080d0f020d1109010e0a03050607030504050312040c0302010806062805071b0501030506090903030c0a0915090906170c040c170a06080106 73
    0x420320080c106800c1d0444280c401c55000c80c400402d1001191501c1c02c00e410308820002c0000002a210301e00e100d40c84000307414220100004c0380c045010103091100f460044000081c0920f02c10003106410000940019146079001900942440f40061060741542e5115003c020038002c0802c51111301e40c3e2103000d040c1e0404083e40e00100071400c5031569a155000146403805054403003001c102000000c104440302c0c076004120205545c1004c0c640601d0720701c007911041e03000030208404901503190007000c540f100c1d400c0d000043c1d102281d9021142c0a2140203442c0e80c244903050007000c000c070f036140441d04692944c0420054001d428100054201d400145c0740c24081d1107000100100d20500004a9401070301da02c00c0c003502c0301d20b40c41e400c4855640603002200b0080c21240912500c1e0307000a15601620041e440c2880074540f01d10300c400072f20b540000b01c25800e0b844140140120b06003039100c840041d00520b450080492400440e980d0808292060002c29682d84010818044213204140187c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 164427239 1250 164425989 164425991
    0x1805033421260402060708130e01051c0b04080409140907080706090b07021c050d02010b0f221d0609070902030402091906030c060c060501080c01080c0a110a081c 71
    0x406000010914030b040b01003001c0381400301d4400306065586040591704103030707808840c072956260b280304261610069803040d5a04400b4540022900c0c6c68449000a1203041d00c10401c489098940c880c1c86c08520040d000b915404c80800021031051180d0180d102c1400d50a11600c10314248211070500c0d10306264802c2c52250860078081c050158440d5101f822a030340300c0130040d1200703624000200494008040060300b04009101c40e4100070b000700b84140450a982c00130070680b5040c005200328058000c0450750b0000301c114050701c02070100c03150b0000400340241d000030501d84003641a4204000164444540c0d4010810005010010481c80001d09518402581903040ca5400b0031103403480070304415144d4006d0411034903444019401900119040f8803100450380c0c0e100c40113080c1202d60075055503110f050200100d00d1100014450708020380c11b03501c0000303c1e40e8510030708940d44c00ca040000c0810090025003540b2604c03c105000e9068001c0c64070360b541325903000c5220001d9034071401c0c03a4403076 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 164428489 1250 164427239 164427257
    0xf0602030c040501090e04031e03020c030d050a05131104021804051017070f0b0306030c03010903080a1410120206040305120301170d0207050118050603040c0503011805033421 77
    0x2031707844908038070b20714001c010311940c120b803209c800e602078081c0e07078160241440089100c014402c000d400142c028040848208040d40fa0301c42c0210003100f034800d01414076480c0322588945801c0690081c00082d01000c1c0218500d803205000400391513044d110101d0208448105024a08010041d000901e5090008241c4240750152400f1801c41502c11240c0c050300100001c0d2041c1c5003804420401e02000300200001002803801808003201038544106451400045000a030000340e406402060511050f00416103051080ba14030910b400c0200e030481414040040001c3e01044942c5000c1c0d010002d00d500c0e581400002d0b42d4000d100545504a07038442c001d10701800c0c1c1c0110340300040d20300a00c1c00c0d00c1480c0c840d603d10001c3e88a1a4001c40d0000340002c200b00a11500d0389400080c1d0b08110020b0054211209260300f00c42d185410182c12a0010810f142402d49135045c0e5007115500c44103003804040c0d1054194a640a1069003541c601441e0310043c02c0701402d550030a541401d26041034421 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 164429739 1250 164428489 164428493
    0x1050a0906120b0d050c09330f040f060608060d0302030715020f040810150620010e0d02010911030102041523030103030e040506010306080d0c06020c031606050603010b0f04090f0602030c040501090e04 88
    0x11840c0070741d10091012008c600070741141d44900d054031803a103002800c14000c050b102224000208034511456000601c41c601007500c40c43c0c0340c00100728240e015030041d810070500d034540040d40001050f5201089608001c4003401a141e40b015000a0450401611a03080901e0740388094a00d54100d103031140840e0310046c849160402e820101200101050701c4a41b92146403890060044030100d81c014443c020000651a50541220840703512510058500c58060000d2500741c1c0075078040c0c03070440c1a403003114020b030902c140780b4140c01d80c50014400a41035001030081c8902e52003078109500040502c0201082d80c1412300819800078020f2808120203031401b8045034076009c502c0f1130704040042e00d00c1c252003070018a4058821441d4032105690b0340c0c03c8400016440ea0718005001c50344d46060a002911914040c81100300003403000c0c2c0231500c0074003000200002000301c200300302c6101e80c20b001d40201241240c0b02540c410044100099030740e5003807800160021003581d0100202c50302d02410440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 164430989 1250 164429739 164429791
    0x70207090902090f0603100246050a020a0f06050f06090103030f050a0504091109090106170402061c091410060b07020d0c030503030a091101050a0906120b0d050c09 72
    0x260003c0080a41141341c3c80f0180002d0034040d081241c1d42505001180091642c130100000c1100301e8240c50280c003044806461900d2400802c6002c0c1c014006030110a1000501400007080f4650561056400310300746039540c002041c075200815030380c0c0c41e83d42c410040f145000c0742d41d0a40000382190750200c1e40d89181d0300241034000700700344e9208020021404802150103075098401030302c10030300180005c21300d00340c11500341c0c0c10940916202d040724100010b0201c0c00f0381c1c2e01d4089011130701c80403032f200e5445400340070b0f0550041e400b10700d145a00f01040c1840380134511842c1e503003510489070304000c802d0400300d65143c0f140d4080c00c088128a004820015007407107000b01c41c800b0341e042d900c0b0f0b04082d20b90704101e0003441d166072010f8003030300000007000091003159000b071240520650007128401010710044a060207822801404504406801d0002c540510301018800d1581880414482084070102d1000350f150352045415912000b000301c0b0301e103801480c80f0340c0842e82e14804c200c80e12144600324 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 164432239 1250 164430989 164430991
    0xe091b0303091f050f0414191d060a0905090a0c0f0e04020f060c060a02131418180109030504140402160b130f140105060a12060f060306060b0307020709090209 70
    0x4481e42d0340c0d83e10040c1e080c4d0090040e0782c1c140300c2158800b61181c0c1d0300c12000000743c0703000c444180324039800440c54410a11200080703050f59406c0540401c290704c0e5102d40a99000c001e401701e0760100308120300080410b404c0c0135191107024044083e102d001e5891070600e4950f6400e4026001600c00283d06200000c40e05030300b250f02980483d00190f10903910004a0240d104000c20700740d030741c0240310820030300036010b4008190441a1a41c0041102c1c0c0c1c0d01d516003c80000c0342d41441d0701050044104007032a0711040b211340c0040c09141130400001c40c0f00489421645541c904401081c00440c04101c14244040c400300703058015281546840c40c1c0300e0011070340030903070200204101e5152000c207440d40f0f80d22010b0060150300400590000743c0380d003030458124038203001e4403107070351709081c0002d0031818208142c20441c2c0c3c01c03071035021815559541e654064844041c40544051741c1e6000040400c1c1d250240300010401c581040d603880c104428000c3c1040700c190171800001d81065000f40058441c0c03401c0d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 164433489 1250 164432239 164432269
    0x41401050706091403070b01050402120a09050f062d0c0a0c0809210d090503031602040e03030a091a0402150a020a140f010609050c040e04020a0e091b030309 69
    0x80e03689148502c1d048004150302400985928507a02119081c0e94001000340b01c001e014003a083c42e940e90701d400b040f0a03440b885141c201d00155020100b1940e5600e900018203451103001076a2a0040c16040a450300c0300407681ea2a81c280001304103505500400344a0171515034441040400b8640000c0d150a01d104484d101000c0045401d458003d00c03040720242c6000100c0184502100060342020303184076041e00540c44082d004901050062600035840802100c1c4094055401c10174801400440c0300d9400c40166005519207410111465003440114800c0c0c20f030010001e01300119007401c126140244002c0704c40d00c44410244030143e52501d000604041d040072500d03581b90340c020002c038100300d80c4102c010924038580e103510341d4904c0c000c10200b0701c56604070002c00400703659010510a450023039510382c8410310f040100b4003072890705003481039020b8000b5002c1641c4583d9002c1e80a00b0f08401c444a8a9030307004a034000c000610b0a1700c0d10030b4407140882c021801c00c140b01000030300c0008101c1c1c2c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 164434739 1250 164433489 164433497
    0x1503011a0721020a0221061b0c15090607080f0103060f0e0f0705150702010c1103070812040608011212120608010e030d050105040908070602030a02070816050f0102041401 75
    0x52030704206802c1c1201c9410880c1d8486050800034182020b5501c44818800b00c0c0f040c04140c0d04c450034042c4002e1005034900409006040544892404010110a00700c00001d03000c81000701460519003000031741e642d072030150019403681c07400004882c20300308050022810040c401040c068a146108807541c1500d82100700080c0d4050641c50303d0300104007818030140130780208285c0300c813040700200340e040413034005650900000020201c424000d20034030350024003040e540e20709580403941241d0401500c1e00b000d8103e0344169211039840345001840134140034020750008062180c180d100c1000341c01020510240d201442040c3e840405080031076603050108000b555620140c1c0420703400100080c2030600080082c002001040364481d4800b50b41c000c8601d08180001541c3d040a1140030034040d00701c02c00c20304120340d03959048040c2d0300203001601140d40074040140813650900c024820440d01902110000415140107410010f0049010f215a407050008100d0b001c910f00584040260034070f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 164435989 1250 164434739 164434747
    0xc0b06060c0d142517030910020906040803040e100801050c070605040c150f18060207030312200405010813030e0d08070c06030606120c09090b011b03030b1503011a 72
    0x7082001401360601c6000d46402003031981e001d000180c00494003450051603404950100d44000440d648070540e10701e0181d1380b0480564031040256030107420444001481203180540d0340e924581303941c015400442e402c60820051100b0180ba4003030b404010034004000b07000c00e00d0403150207400e40c01507000c046c01003605e81c0000b80801100c0c40f02c60f4050720b900003ca0000d90200e00d4010484888402128041a01b45204180c00217038144030000b110241e0f030003040b40034259501140c942440207040c1c001291500d4041c0c01e07a07400c20301e0070660191200300a0b0384451500000600c0c20708003901c03442e604540d810042d0046940240d0500c0007000a6410240500e00c6180c0411544a041b40180482d001740e000810b0117989a080301c012a101580e5032540446a035800108460091503c8804203c440d842040314081c103801180440105051020314084902c00060040154040440c0002c2d51403c0820a914010104480d52408003541c141551b0511200c0703503040d031003020101202d0034086 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 164437239 1250 164435989 164436017
    0x10090204150902180d08040512120a0f0912020d1121010603110a120314070210030f0510080a02090a021603080103051e0c01080a0204050307060c0b06060c0d 69
    0x90003101c4010426610407080c0c5a03200c0902000b07401c88110210b049001c1c1c407101d2464985000320102264000444900c1c181c41c0c2020800a0455020150030324000c0b45c00401690303188030060000c906451f283d0340e102a1806000525140140d08403e510f454a090b4a9001d601d0301010031045992042006075025012400a8408840340c0e9813250003001d04681c18080100c1900104100c9114007089900741c812181004059070850080f99010603507480e250020910600c00d51380c0f098142c040c00c5142c00019000b0581134006955600e000c83d4549902d004404080d20909900c000120b1110003401d060481c200d46505041300c019100b4800740300402c42069042e03048a1a40d000710000b500c0c06001c031b10300508881000d100c181c4660044031141511442000f4174900200901000b0300740500c0c1040040d9549000900440305140c0e0910010491b501d00700300c1d401c06070440d501c0780c1201d105036107480f44482da00201800d0007003a007440102030301c450004e02d030480b040c01c42c00c2c0140500c2c00c0e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 164438489 1250 164437239 164437241
    0x70f0c030e0a0b07110d02010503040308040f080d02030412020d090603020c010204090212160f050a030c020c030618010f0b0f0108072c13050103020306191401060509120703020310090204 82
    0x1074020950720459000000411041150003090303a18070609402404010034405c00000d541c0f00340010703010500800000b000a4407402c50710741d02601c207070014408980c45071520700d20b94010f5200e800d80c0031390000900c000c2c007003104141501e0b04500c3c80148420080d140c0c00800401051240c03600307240e00441c0c9403d803c00c0c00c0d01030b00c1c09004800f01c219207484001103504400c0c45c00b42c40700440c0380c0500036a0a81e0718400d8400e08010010350304c940f440c01c201030714200d00910010355000114000c54039040308030b41d03003401000e0084070305043c03046002c1a03100306542180d0500c0d0450000900e0200303a603c260f2240781d5002c01010342402c04950980d0707005015501c0c0b16000e51740e1401d504601401c250110b1481c06144a05001611680075114004909804640c001c1c040030354190b000e0f030300041c07109080c1c0c0d540500c041e1200034089400300801d08141007824003038000d40301107000801c4070040381c2410200d075204c03c3c05174401400207503c0c41e00800d072a5840800311414240e16081c004080d5211 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 164439739 1250 164438489 164438507
    0x1031508060a0b0a06050a08130201021c030c030c080f1f09060e0f0705090a0506090310090606060807020303040c06030c0302090907030b15070b0f060f0307060e090f070f0c03 77
    0x100300a59401d0b291600440e4001e00206000c680700300001e1101080041c8140107560410820351280b003040e88801420003000203c0d004103e0451103890300b1601d44445003c110038047c1115140130841102c2c81e800030702036851480700b0310104140501042142e04c210300100b82c002c44401c0560680404000c840b0b042c4a100703420500700c0c0d50030040005507001c1d1507140b8501c40c00304003015008548903c0785c101d40b944514a841c0d6445041c01406101500d03000d40140100e02004045aa40307034007107a050710036640c24010030b40f400707640d0310400c100ea95004801d803544064944041c51961400e81e8900e0f051303042070b0141c40101a80c510503421124040ea04a030b05031040100204254601904002c0280c240c0c240750901440140555520800944007a54041c0b07a0140c0e0310170b04c80d5500240321203600001000c03507900a4206900890a80301071011002828440e0f868030340c80c0041c0c9051002d1124007410b1503000e1b4042200704030403903602c007507481d40400b0350340b4040200600c00d050495905c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 164440989 1250 164439739 164439749
    0x503180106030519060b0d02060904240b041401080603030a03050403050d1b110f0307020d0f0b0c07060c0810031202251d090c090c070501020304141614010315 70
    0x218940700013100c5501d542d000740d8030501c51072041c40b140a11000f03100c0796640d0060001d40100c402e008802291405800280c083c10003e202d60396205110300c2e1902070071f44d00b80d000f0050000001024060724a92180c90040400c00382046807a900f814004640d491083d10b0041c010981e481011034101845101203420402103100284610340b100980c803041703401c07040e0189000c43c103409520510000b0100e00400080400400785040030f01e99001d1008500c50914210f07a0310003100340c2c09000070444c4941900408411034030584a11607850f01404841e11020ba060510040c10304001e84d42c0c001c56039000a072588000b41c100d0b04108084180e241405d1740d15015a61003a552000911160007501001120500d501c0d0901003c821301000e062090140c4004040780c11001e20344001c1d0802019003900104140443c500d0038a254840d1401c903001500d089070210700946160754a02400c000f41c0586958503c19007a800c1d1400d0800c0c41c600486411140c1416111003681e51910b800e04c0240c0011f02c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 164442239 1250 164440989 164440993
    0x30709030f031e1709070b1e0d140103021302360d111005040f0905060607060216140610170c09010f05091f030f1718040f0b0105031801060305 63
    0x1101880d001e001004100007164141c0d40b01d0000501110002400c2411500385010481c90032800c01300007490186908c02c0b40f41d0850081026081e950594861000030040100100a195041d0300c10080d03a21411107030400e24138010b01103c142c0c88401d4107043d42c019640380c1c030540b50301d0301d090f585800803da0740c40300390f44020b0f0034202105015840180c0d01040004448130940d0811689094600740140d00410755529058001880024490360041d034116100904490403e503803070340c583d0141d07402070400501e00b808002150782000010180f101d104540348014004604d04141d0a501915071485640c181048000c54100079080601c84890001d40141890140e581c5400d030f00340d20411079114103400f031b000a030b0000c2c210159030b020111704078400300b201d90549451502d6409040d01c20741c0059641c0201c11500308c00040e04500100458200c3c010020f100d9030390103040204032840c0128000859040422007a001ea0384003040300d44c0b00300f042c069082c03454040329940c0e00400403508020014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 164443489 1250 164442239 164442287
    0x100b010905061617120a0c17010b0c010f0c121512032c030d050307051c0903020706140a05030c1b16080c0a0315110f04060801050303030709030f03 65
    0x500700c1032104807030301ca00a422000121341d03d4200d426041c0300301d000070503880d00210003003140440290000d03549034802d86001c40d61155002003601100b0800e80c0703ca440c0b8140050340700c0d0400c1c428080c0d4401c81c01c04201c01c010303984604101034058280408a034226030342d0360800c0c0030a01074044281e409004110108901c09020b440c0191151540e61b004104400f0310181c03e601c040012640b002427420060058070380d42001c00d000f603030240c001410000900906019209100d0781c85032030800001107400340400c00c030050342006414045290010020031000c4071242286035200c0782150003102c0507240c5142d880ea14481030842d14003440b00c000ea030480c0072180f456000200000d459607410514901d0136004c0b40d540180b10350707401748044265089001c980b8100089918030305801c40740c044038140820308022501c3da0000d5a800040591050000810305000e03030380e8007076681805400300394019480d50601e641c001d0312020203444020080740d0001d076400c04045c0b09000549104049400c0744042d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 164444739 1250 164443489 164443507
    0x31b0406050406021b030a02091302060304030e010e0109140d02040e0106030c2d05041e05090601060315050913030c080f0415020a02090c0930070f08100b01090506 72
    0x120b038054410031005114548008a02c1200d01c12440d4880000030010400c260b015400d024030780100501d00c40845904812407009030321440c4c0150f00c40e501c20b071707242da07290f2181c40000740006805560840c1000003001050144001c80d21251000c0641123f0380d4a040d94144006000303800e02a501c08115400e06034000100681c01462a0980300ea80c05103500c01f505454044012451540d0703201c020002100e8201715900f4260320089010f00c0345c0c10000925080b0710716101c142c54090b100350324030b5130260004210856042c410340507518010300144041c0c40c50440002c0921402400600f03400b900c1014078001c060140c50fa480f00150300c280382c0340c5c49002000b48000702e41c01c180b042580b030450b8454501c2400e44080b65004996600415070909629000385425841d04424070032904280b0710b00100b40740418034002d00c01000b42420145501c040508134560a0070240d902011940c0444801440384900104038031905482100000481484640040340e00441e56849640c00120025110728 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 164445989 1250 164444739 164444747
    0x1513080d0f110f0301231c020102010506030d0e06030c13090c0e0609011d040605150c0c0102010b06121b0301080a0b0f011206090503040510020304030b070c0b0c031b0406 75
    0x4289002020020034200c08040e01d5a07101e0f8414072042400104018404403060801500d05129020200380c150305215020806200c4001a4050138400403001c80003190782c24000c2030b42c4540c050b00a000e500f04101406042050582801c521036074010002584104c020403d81c1e819a101055020000344e940a001d00204407084042000130618420f80c8001d041c41030449070030440c10380d90940c4141041c400060209015805240e10a0322810700161b983d44501d1515a090714030440c0c00d60761552000c1003454922464001c0d415139040000c401d100b550340340140c51034a80000390a002e10b0b074a040b10401d8040c0403050702580660044004520090700043d0041c0c41c5114003c8110541c4800d040104403102c24420841900302194800380020440d40200c000c1a1040d4112410b117900d80700000e01a4603e0960000160300c040340030802c0c844642c82c46c0b0741004d00c03400c2120304845a0380b00c0c0800a50028000b0704040c1001012030500000410ae8a0038408051112610baa44414000b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 164447239 1250 164445989 164446001
    0x102071208160c08030a05061212090f0319021203090306040c050907021501060f02070b070605190207030c021e030604080301060306140f190e0405071d0403021513080d 74
    0x14401c1d190300640700d02c140740607041d810000c5402c0f054013070541d514868404050800103102540000c0c4000c0a0f9112480c20410b918064444107400354030355039510140311550301041591442076003d0300307583c44e0428410b1404041d160301514400806c40000d4034662840c41444500350701445848200002d01006a64280a58608803034418640e12150300032030340c0b03003401c201584a0400d88801088103d001d000681e600314100d00640c1e5499540e80021255508616002e41e04a6101c8080004881207080a82e4103221a5802141440d00305d8400030804401100024010641d21b070b40c1c400422203d9010201700200102181e403180b400d4034080f9540c1d0020312400303001c241400f801040040480303c8100041c0d0001d4203000580040300104a20b400c001e0422052442c05200042660603842400c28480d60080004080003450f20481e80c0c100002e04001040d41e1001c0e03002d100000307602060f80304504080310418030032a1200e0300d40250748070850800400569000446440d200100d800034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 164448489 1250 164447239 164447251
    0xb06130f0501080d0e090c03070c0c0807150c0c0e06030a08030c190c0f02011b050f010b04050a0b0906060a0504380f03061003020c0307030207050a0501050915250501050a0c140703110102071208 85
    0x103100d00ed2100c95059a20080f201c0000700302c3c1c030104100340030000364280e50035809440101240c0b407014554032405850f502c180c0d000001504009809040c00200618100150103607107000c92441509807684045041080c0c4004d04214980c051071000060312900c40d07031302c0354110040d04c0c009040358083ca8000d10a802015003e0f42c1003000003580c0070380511071841d2252020b028207010b50b49220400802d603000302d011805018040c04003007022a2420003c0110728014040404c1c01003041c1c910908115000f0010842640d0401881100c02124400d881d0840010748003401c26002c0030206a0190085a1003a009403201080c00300070f150307001480f0320840390203a41c55400c0e59110700046821f1f00c03801086030381040461040c01000d01c503001c010300500c103001c0c420060306080140e01500308000b40c0c0043d16107a46840500540e070801e440b030040280d4090810001c00300300062648424010803e002c0c00303100212010140868081d012602c5480c0e00c401011951a149034020b0030524060f149 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 164449739 1250 164448489 164448509
    0x105040c080610050105030a150303020a031409011b11060a051806030903090904050c09040609120e13020c030f04030c18110301030b06130f0501080d0e090c03070c0c0807 75
    0x1401440800d0141c003d0031010032226410341408010f4400d5400542640b410965401072854a9400701440d440914469405400411075608000b440850a0384018002010810600c14aa81c2110005104d01040c0540342c00c901f0f1f8608088210724050354555420a10009140311a207521400500241d1b074071000c6110415a900c0c103124590004030b87c1c0c802280d00402055025250190b0241c1d8090310880403240c0c03942c600f9020a5101c00e06807411242c031603d80d000c1300300308030480c80e404a0204003840d09000511840c00041d0007200005078042580e9800121408002d8051007100e00386a400340109955655a180c000c003030340301510800d107517100fa003900c1000d910907900501c190410300346150740c1540d00703649450380c0142016040f107520410070b4504c00c2ea0711915000f440850030451100048642c5411b00660501da9104001810081e11280149a6170744070107590381c0041048924544070703074884c001902c08042801019217001c500d00b20000e0308000c0007886900307841e41105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 164450989 1250 164449739 164449763
    0x1e01120e100e15180304030804120606050103140a2c030406020105010515040b0a121a10110715090807080c010306061e0c0503091306030506100303050a0305040501020417010504 78
    0x1074190700c5080809540d40b600503c40081044140748003032800842d02000c1c1541c0c030b07186da01c3d40d41c1c0c2800c0c3d05c01d5100c0f160106124070540b05111181c815a401404282001d00400681c20080fa1245c00010050301c0126503c54150028042c4e8001200505100c03a620b115440c0c7c113900c803660381e900320b440b9513001982000000304980c100b800341d40c1c002e202480601c03400d15082000c030351a19001102d0100400010000440300400307140540d0051040c0c4062503a15030f5586414006450070811380070f01031001986032078551300c0d400600c00d01105d902c509020f030340c0c140c4041d085504465542c0428401e00c43d06d040842c0c01880030588201038a8241c90801446035a114140c03082702c0349944000012450074052854280104c0c0c59000652050060b01e02d49054280021492010140001c034815515803091040100801c40710703400c000c0504521024500e540da0040c15442200030300c00800d511800407608212b025019940982540f06e0982090130808001c140200000c85080e9446a1401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 164452239 1250 164450989 164451011
    0x120804080d090501020d1d040501090e060601030c0e01081e090303160c2a17010903030e030928030501050c180a0513021e0c060103030206090c1e01120e10 68
    0x94481d10440e00107030080c0c82d46e0782d41030b038065606403a03c12404100d14104c0550f2500c90741c89204260182294110002c0c620390400d003001d20b81701780100118181454549180714060300103091174140102407802c0301c031319690328154042800b581501c00514400d0701c008d00c82a0b1002001452140003076a081500602001d00122030031205900e0103400d0046c0482c050071425080003003188c1a51440c4a8510340c241d5030301c54000c4480300c4c60f060024595540410404059140c02180d1100020381c00541c00d21224a0009440c0740c40540d007001c10481c1005052442100300b10f6072401560010020059850f14940c000d4591b404100348881d0b8104040d0941c030320b0b2400406142c25240080c103a001207007401c3c800c0c01c000350710079050f560f612020000c403403121aa03078000130b108014900e0050a200e514601d80645804e6000c1c00c40b005580003520071110310f88070990103030a0480400c0d001000101c041c00143e41c0c84c0c0102003001e901d03504050482d94000d00004a9200113060f00c902085001404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 164453489 1250 164452239 164452247
    0x306090702070b090103020c01020903120c010b0109050a05040b0d0807030203250312151806080c010c08030a020315120703020111010c1b050124060e0607050d0809010204120804080d 80
    0x5000c0c6a4503d04140b141c952030f940b00742d002d0148550b400340010300d02440500002d141c60100101050003c10020300340134095400e0050420045c000c2c2445c40016040800080a503030150003100d010395611043c06425640e000c01c19032103107812115050352640c450900940b6503024140483c81ca00c050060908601d1010082071420b0b074140e600e00b10042e80d2001200003a21482d00106c120310020200450504100380380f00980c0021340b0341c001904e80c50001c8503400c000100150030305020302220340d580498030781c2c01202d60ac44210800189c1d02c4c0e54840840d000300b16141030b0310b500141000c102680c00c3d44006144001c0e00d000341c9035582e54076031602c0e200d030a0781c13070500c00400020800f010000d941d10a2502100300d0300d12560000c201c050070310022414181100c481002d10b00303110401001066080b1203400c14140c801e0325003e140ca619604c500780d50b60615030b0718004002c4048002540e00c40290306072000343c4007080070443c8a40660901080b980c02c00d0240c01c40c60f0160700300024540d0b0013 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 164454739 1250 164453489 164453503
    0xe06040606050403350d0204030b010f0609090b04140c0307020f0f0a0b0402150c07060801060203040f0302090402010e031006080c2b03210516080708010515070503030103080306090702 81
    0x110044a00c1001c0102e551040303041036a0b1701d8100c07170360604008402240c00c04000342004010901340140c0f5a451800d01903400070b01a40007442c090318215061103a107078000c228005680c40d2900c08a040198480418020045242c149a0490320b00082c805002c0328540114000e240c59802c80740345100620105071108140c011020032540b1003101000060a40e03d80107038003900060240e0111700f1403c03000c1d1302541c4447c0e80790b800c9400c070136024081b8540200055003d40050710055041904141d0039000c1a00b00d800064481d00d800e000003000c5a10904a01002c2d103006001d6600c803040109040000c3c003d14000c08041e070050550b02c0d20a4200319816810032880740444a14401ca840c03e400320085054030160200040801c005007603d100424120310700c01a94400101e82c80c0c002c4902c1540c4110041520400c6100014018101e03071210715141910800c44681c1030091080c080e901c5507100e10807000f005804040700000c02d00541901a40c8030f210f060717070750034025131322204200e8840030707 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 164455989 1250 164454739 164454743
    0xd0e010507030b010816030905190302060108070803030103061a0409080409140609040320010203070806180403020606010806010c05060f1509040c030b040c050d2a081f06030c0e06040606050403 85
    0x284400054600701094007409085c4040341800101200552227080c20410b0441c0c0104c50700c01c448041c5404c242d2b04101007030051010001030714041e8101891340361a8031046c400580040d841e0042801e100001c0c0710603101c516001801000015040e107000600354006100d40301c502894071784400c11130750300f0700c0010703105d42d03001014041240e845580640346800711303c009414680e8400480000314200f44000c41c0111810344038200189031240030044180d080e092845140c8051070148000030340c0019000d50448402d0815007800d40c1c030030700102c480d851102d0000e09a44202c005201e25141c901c251140120000840001d40158032000d0106051041d500107101c00e45861081002c1074101605a030420b1240c016400e5017540ca40000789414a8504c00351295600b0901d0801a220140c901180d21164100440e10261600120903101c00c000302d05802303900309050071451017260380d0b0302c03038009075611601301c0a05030740314910318124500031118103018518000000c035406000d201a90f02f10780d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 164457239 1250 164455989 164455997
    0x5070f0c0605041106121b0703020a2a1d060105070b0c0304061509020c011a011b020301020714030c070602011505010e0a0e010909050105130c0b0f09060d0e010507030b01 75
    0x20300155145001488000e00559607518440c24000440da1001d0080c04c81c200f820000d01e07028100550b80081900708142c3d10140d0030010081e0700700003a0013090070000190000d042c10b200c000d04007200440760b0084250700c440072000840210310708d01c0030b07a600030201d02c00d07020b10520743d07031207031f005403014490004040c0a0030000c600040c500382d402401154000d20aa03008100c03184210700ae1441145103800c040038150f004190605c10010910414090b207004800e49048840322a0010b04001044032203c4031015455a076841952400d404440d00c080d0f10201000004840404040c1c480e003203810a00301d58080d2030000600039205019500c03e5a0700320007040320003490000150350450001b42060740102813000c00143e414003da94060082150000108500d0705501c4c0103400c46100400502050f0801d0140401040c10303034a400d021386110f500f036140d6422440906082c940608140a039201a0020b080040010b0b181c001c075030483c14843c003c0c030050f00e80345415003e440c510f41081e8002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 164458489 1250 164457239 164457257
    0x9220501050c0c1b0102120a021c0809060a0504080307140c032b020a050d020d0b1207090f090b070309020d140a03110114060f060f1b070605030705030a05150d140105070f 75
    0x340703412001001648a5030042b00d02000c039000000030401c0d1507404c6a004a40d2800c20000c11403030500416034440345201c007c110900c1d25a8030940e0032700020f0902d03030400c07220a545014a841d660112410468040d003200d0f02c0c0d0746004000500380955404561140040c1041502000701e24000e542c00d0540316103446003070000280882c0000c3d00100d4100b00110b4503a004039429440d4403c0c40d904036002d01c40508220360800d1025005d4480c159406c3c080c05190035080804500000e9100343c02c1907851074049251200e50001540c421040c080141c250146030584c03085a0b000060f000642502c00e0701c40001643c1d807009110300701e0f4075100c0900000c40380100050a140b510700b010300c408580040005041c00c500d42d0404169400c005501d0031541c038100007008900c0820842c3c5401003220740341192a52400000081142c000504160714264031140400d1400c07000d07003002c0800001c081d040406941030380c00d081184001d2001100655460040401c00c407520582e15546101d102c0d0310f61180c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 164459739 1250 164458489 164458513
    0xf120c030a08060a030f0b0a1104060c06051003150506010810030308040f020a1d0a0b04020304020a1e1a03071715190b040b070b010e040209220501050c0c1b0102 71
    0x10b0600010311039a4801000341000c00001c007510b44070403080f8000c24100030b0f94a000b064240449191781341800c8420300a01c001c1050580c45004088030710790203074004c103050f220481420101c503082c0c4c0004182c210144651070240102d1350000e44a01d400340d0701e003905070706e45807a0740c0340d04080c5000240c0041d103044001000300e0403503078803250344510141c03000300055900d07403001417009140480e556515200750300380441d4008034040ca0303c5d080401c0350114a0350406900184401c03100384102041c1c0c0300784038109048001b030f0030307007000080c03080010741c050741030215444241030b40c41150803c0214040800d00c01040c00814603142c0f043c0d80010101d1400391540301006000520104103041d00c020550001c034440d44c3c4240908010315400c4003082c0c0352101d51601e14000003050308181c0304001660200300142e51a091460f4000e001c0c0b0458034464101e20264003820600b421001d05690708040a00000201c14002003280f00141420780c3d400e210081240406204081d005600503031190b80240303030f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 164460989 1250 164459739 164459747
    0x902040f062706030605010210020f030f040f0804060906170105130237020607050c1c020c0d0b18030f0706020a090807060306090b09070210020c1005090f120c030a 72
    0x800c0100e640401e85205001c0b681c141c1d000c5400303070403c40c0001c0d160b041c02c00003540c0403c002c3c0000c0305043c80560a114107400c3c0c00c0024040242080040d100c1d007030106052204807002800c11503001080f0680d15034507403070043c2c9070682c64807030100081c45072031040400b040070850700340c140c2750002c0c9000c0900c640250b4601c080e40040e0258100d200e60800d0940c214402c0000981102c0350b0751403421030a52360084080e08000380180703804140b100411250703030740c102c0200380342d20140302e0724400d210703940801d00b0124034021800044c150000c021010302424005000400d41c400c24158508450003520360300e0711500c0340034032001031000d024207110281c00249560040c0a41600c0c620b011160036580303103010340c50540d40d03610030004280e840d03d0074460400326000c2c1602145060f107030030902d41068a0002e60716041c81c9206c2d41d1051303020030080ca0080081c8840515aa0021024000c5041c0210243e4070b45100d602c1c400c4180c81540301c215407504442c1c084d0b4036517800b00d40186080c0200c100e400d030307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 164462239 1250 164460989 164461007
    0x3080a021b0105090c010f02280c09050f01080d03020a02030f0706022b05010509070813030915091d0601050d0f11071104150503031c020c071206060902040f06 70
    0x1079506860228031920a500b40b00d03080c0b080d400000100302d4120b8a0001601c1c100c102e2286d4011500034200d102c400c420409000011610551108400c6152904242c44880b20f00d4000004003424441403003d00126035000a0503210f20809031512000e00d040168224480e9428900c0503810600080221906503000b400189001b1303e0054605154405e0100d4820801c080c00c10002903040722001e01c16900380300b142c1c094282920521402d00300000050071031880140818801021104401b00b00351040100b000144800a134080040c2e40003c0c0c05420b4001c80e00a42d010392142401c92001240f2004540c1c1c023817401a1141031070310061800c0c1d0b4014001c0104006500e07610380c18802c2035030040c007000780002030042440c107260030300002c01c202c2652821101010b00320094030050055580c0841180c0707008105500c10142d241070203020034064003420b0285c071200d01420800241c5d01c10540c000ba00044c0c414042082802d4680100008a00860050f81401010410f041c010b10b40207032180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 164463489 1250 164462239 164462257
    0xe0639010510050118030f0c030312090c03111801080d0809010b0a17030408030703050301050316060e1e0a090501030b010611070608090a0209090c030106120b150a0815060f01030903080a02 83
    0x20340c90741516915900c42655443d0811103094400c8c6004000341a40891010314000100a05025030f03001a01c881101e10703594000a00200f07050780444c050750361070144050201180c43e03070842c955a5110341454407004803a0215004c50503031000142c2014040c803c3c507124540040400200f242404000a90307503d410020040520040101091081b810006011aa807190b03641c0756072581000c0030725090048212030b002e0340381c007902d0060100d16003140060000000c1600d908901910f0450b800607081a13040b09140c00000781440441c00704a917800145c1603038010030310507615990701c0c0000c9a44004620a0320795a03002220288501480789081d66004000c400440302d00074943e80019110344400d4a0341c0000d40e2007148401402d0500780100001890032050a9071050465100d14507003c00040040c0c540c0020040c5078010795a401500001501088040b90501e1000400400d80e1110036100c0324883c030400c28241282e58428080e52000d0f0354540e64600050726400803180194000e460300c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 164464739 1250 164463489 164463527
    0x20c100c0c030b10030212012f16050a051515010f09050306070314090c0a050f01140703020c03010b0a031a070e04020f03010e060906100e06390105100501 68
    0x40040414a40c3e10224002c0c0000300421040300c1c650310421403000e02001000850303905241a40345140001e0313030f02a20320304419078108541d05103003d900010f07101c0c0521444c5160940c01044080c0980002c010354450b2266040b0b82d0112104034000400030f0040b200f105c1d10000e02c003015041d552088040c0000f1110904020504036124800a424054100c0e04040000e81c1c51003480c04081038015504d030440070305409845003003918004207110310580d0080714082e6500d844140c402d40d10480c4543c081c0403031041d003a910752810340f4000303443c0c0c034880f100b20b48a9802d15407044110715296840c072046a0b0300c45d07100f0710040b00c84401c800c01c0280c0104410107003c5410620380503030320f07540000c1c180300c0280b400b210396035030415050000c0ca440c06030400740914500e8003004260703150401102043c0d0b82d6800e011455042881c0010914490403081e0300c0905504504050500d5281800c0001d00c101000c01400c0284000c051608079034045910481d512042101007109501489040310310070b0301014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 164465989 1250 164464739 164464763
    0x20310030f0318080604170405010e060f040e07110c01020303061c0515130c14030309011b0804090902040e06040309270c020d0f020a020105030712020c0f010f0c020c100c 75
    0x200412603000b0b9400f20b444e6801440c1007100b00401c50800721403aa490003900c07410b05050100080030300482414003030140358001070174401d00a2900668008010084a042c074500d0700c107500510041d4442490581c511a95000030705640c00031003580c0c4540c50290640b041080303400da884401c6a40114199254090008a4ad482045c40d400e89840707100d502840ca64406850700c0c00c0c6202800383e600685800780741c03401e50503040d5004400c07580c0561007443d0040007422812410141d034940c03940b0041588400040009081c0c490b90042402c544c000c8408001d400c0c041000309071904c02c1110f0050024902990620010801640316115a107900c003910243d900412201c00c1160300c04802d40380540e0103c1e1464015503400340c0856010209403014040031045540080e20902014141c0350a00c20f15050744000746800b68155120020960216038901e40c0c8045068001c1c9081500c2d80709650074881000c3e0a00c0c00041c1d000981d48018082c0f04128098030f4080360707905041c50b0102c81c40043c0c42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 164467239 1250 164465989 164466017
    0x9060904180c080606130509030702090c043605040b0a050c040b12010302040e031215060c010903030c1805030c12150108010608100e0c0409110a06030609050901020310030f03 77
    0xa40e004015243c014010003140c10200304103d81d00192a134a503140034282400c0004022011003030303c0c409a8161001006500c1e890341002050049422942d0403110384115014181075010703810040071240c2c4540081404080922010354600725000313002d174088100400d208210661080d41d210408051240c14582c40f4100440158082a01509400a071300014010b40c50144100021210705100035860003115035110405204018034010210783d040300d4a041035180c0c1000c444e07880d401000208010481c6180c0607000f412003080d01d0380003824800d001000440785c40750101c02e84a00500600c1c0b80564070f81084031240441e0141c00d11802000c081c81c0a010300f440d00765010b00302182c00460142c0c10303c0d40640c0760140c10103800740356034248008420040305c0400c0c40c3c84144419180454810058100310f945a410140c409410140c000f000043d080e5060303001e02c0590760b840805010ba61246500e0500382d01065440f02c00c11001e0560400004017010f04008105200c1d041c0120254a51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 164468489 1250 164467239 164467253
    0x110406051008040b06010302040312050904110408150601020105070507110604031b0815040c050d02011403011d0606131203030b030102040303030b0102010b0102070e0c0c0a06020c03040315020906090418 89
    0x1c0304140020032020000c0c4810407881c00002c952242c070070b19007141064030b10340380c034241d2613655100e01040c0840010802c0d420b48481c1c02c021078800c2001001907032a80d031507403256900c82909030401146012480440e03d150b01c10b0242c00c1c05420169201414030034240c0300c2814144004106075408401040000005284103c51039045410311281c0c042d680d2404a2090801d2004038007007620820507000c100c0003440510951040c0c4e10b040c0c0c4c24006070281e901c01607034440c91141c0d0040c88800d010000240e000058412a0710300342412404045a488800500146004400c1030321400000030006020b01d820108040911030f0281c07401083e112140344c00700e822a405500242c001a86604080001d540c090054075050242031008040141c90b0034039980030171001038212003550500041490520344104412480140c0000c421540c9007100c40325240c1e01d9005100c01c89090300343c6031101079044504e10035030354002005000540344c60003100800c001009013540c40303440368076045a95008240d003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 164469739 1250 164468489 164468509
    0x41d010906140108010605062a1b100c023a0501020a0e0607240b0301140402010f14030c0307091707060315050a0504020c0f0d05040f090507080411040605 68
    0x361400107580b11403192080e80000b0140c10450341a0304201080042d81c840b0012941e49049141684001d0020102e2801810120903c0020341d4443e01c031094030400c0c2c48102c844c0980c402224001d580c1c1100120540d44624a90700282d032040c541d40080c00320070704c440301400803072405440341904013008803148840129082c2d000c2d03c0c0b0f030f9800b295100d4400e4001c5000c000b9110121180e608013031542c0c1d10301c074041c01c0034281014040200d50740e4480400c5513030045080340c2c80060003480003410ba105059080d00b4121b505074000399000340d91038030907806038800d00c0082c0700412400c1e181d5903459010030328640c8043d048004010407001c0008a9180c01590f4000c0407840802901d0342610303180000b0281c8017524144040c0b421450400c22403650ba8005c21801c55005450250312401c80041543c1082e002c116008601c3c01a400d02c555155406030041c81560040156240c1d40d9403074444e4242201d200f1640d42001c900400003007000701d65260004101d04000510120f44543c0702c80c0440c00c2401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 164470989 1250 164469739 164469743
    0xe100501090605040b131113030b040209070804030f08040804030204060806090c0625021908030408010f0b0114031f0f03050f0604080304030c0825120306060905041d0109 75
    0x15958006004949282c0218001030400f00d600b80840d66600300050396501c203050042e400150b5540f411452900b004043c0e0354141144804504881d55030b00b4009600d0b40111001c81c40340d1b0440700040d403124055030106000325016529030a04821668094403001c1001d00103a8a6080074880080181e9550145c4006450024081c04041c2442115a4035200c41240d2091240070140407100007808101d29860b01d041d04141c500303144d21440c2c00480d21040040308100a201c00a40c03000c160890000014011120f07200000c20000340589140800c998112107041d000490941003c04102819005503421107000c8801840c030203140411072002841a42c00030a9050002c2c1041060040602c040901d120000003d0542d07450181d032040401c0c80000e100806010212144d41d05103e440d0080e00c2620701802003605141c09495458034008100704d8049a0702030400344540c054900c0390048900700c03003132901c41c1c5000a040004010260060041c2010164070b02a002d1070901000d02071030380741c40c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 164472239 1250 164470989 164470991
    0x3040305100f05090a080d11071a040b0708160c0203010e0706030c230406050c07080604030306170c0d030305060f0d1b0b0c03040317040801020a081501020a1703040203010e10 77
    0x200300c0c400c25003d968008002040a40001d0b101c000459400b408980146000c80c800080511480030341c642c1c0c1703009107007000e00089100c01d1a00e441010101145000300e02401d010081c507640d040c800c03a07040c04211180308a501e203806007001035038010b960040003d44024004030b0008030130302e006841d100300ba0740031000098403500c1100040780c0140c0e0a0a02a21054140c00c200d87c0074070004940b0321a61080e507041000c0007a03d1a0f03400014403401c00034103141003d0300d1075800c1c1424000d02424042c0109a010031000e00d00100c01040000c0b0048400d5000d01500f000c0c2c0002d880650080030010041d80c1c00c0350b001d81400ca5507a481038503a0b03104903c204810b00300c41c811142c60b01407014094018032494141000b800c00d801000009036002c60b58040c3c0c4d00744141344080c400340010b0003650300614081d03002241f0264280e0b0450380303044c441c80003074000507100c0b0094001240c0d1144c000e03002500900105000c108418100402103070f0281c00640041000c407000070b541807800d0400760183c0051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 164473489 1250 164472239 164472251
    0xf050706020d200909040f020d1407091a010206042406060203030f06030a0f0b13170306010e01020601050a09050a060b03071206080d0806010f02070509150a0801090809120304030510 80
    0x8000303944400c2101c0004071101605080a00001c00c40c0c40030040c1001c1c20b609115040c1c0070455540d00c0c4003009c5294041d031080003212004241a80d202540d00134151024100a0080c0c03084510385601800040140d004100944a0b600d1f00407241407003a010303148446a100c80304086075400d024000040510781e000b15924a09a01030118100001e010b551081c0c120801c09004214041d80007034059800c01151340317154503850400b03034a40c80c81200c020400c0b00c0001070b0708034000c0044061441084281c8030075000c40d680381d00498949009000d083d500401e003010a000c004400da00080e030048030b002d400903a084c0c49048240d030307030f030006c4604900044200c1c00c0404940880d01980c4020070321030005110f0038011041c0903002100050115040181e120303842c80780107108125000003030502601c25000360500608040403050310031640c0e805004460000144008140329020420f03402044007810003080004028003400e90b1214407455205c1448003201046c0180881c1e0f0710314400d001c0010b86 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 164474739 1250 164473489 164473511
    0x80316050c060c0a0b07180f0503060906240f04090c03140a050a030e130603080918011401140706060915121a0915010b03150307150f050706020d 64
    0x250070020400701d80508810b21080c1140000000c4001d80d40798040b500804070b581c0d400301181c11410903821040c0c8001542c1d00011070583e030009020584506400b41c1e4110382d20f4145407903542005039402c0c4a40c140c0c03454403403031400c50b26004240050008001142d0002c1d0500042c090300c0b00804251410011440e0030404c102c40d80c2d5450000c41c01001c007425846210751215070b2940c501038805403e0060040d40080d10b655208607010000380c603000d04009094503810515005c0c2c2199060501a141004c40b603e206480005e124ac1265407d5010340c03a0f001c100c0d001150004d141d00d00c4404880018410180020850f01440c4040c00c0b90001c000345422a14000764070201300c581c40504002d1400c07030039030080342c0c60f480c007074034100c800080300d0f100f03a104d270180a450140c41500c0350040842c1c1c0c0c000030895280d00001140680300050311100d40c9102c2d0000c050b181e0302c45115420721800c0c0d4010032a881c6002d826480d845040a00f4160300344104d0b61a59816680100c5e5401c0c4603035522401800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 164475989 1250 164474739 164474743
    0x120207060606081008030301032301020c070303020c06071e022710140f120c030d0315090b0127170a0203010f0c05070605130503210906070c030509030708031605 71
    0xb500035035000c00c00c152540780ca000280c40c7c1c030040c00040c14007100c0c1040c405501030400034a200710403240c002107559402030b064558a0b40c5040c04210010b000e14401000d5506d020b0342941c0541e034020b02c08140803044404010400303000d549080b40c12290162480d1214005000031000c81250107041e80d40500d8143c0d01d0050741d144a400c078801c2015004111383e9191100c40c3c41401c00d0f2002d50b00703100c169110b541c0084c9808082952a945817040310192087d59901d50000382c0100c51440c400c1000581320341035001542c4000b4070303150001309a00160411301c071028525444c414448144c0000b450340343c1c8a201c20722007208600c41c415500260200046003802d10801801c035014504c104410404410002c000d0310542101400050701c5101140d1600c0803030010000040d0f0000849994500c0d1340900c50700e00100a080c0c4079030404140001d020807201280c1b003072141c003082d40c071036030703500d089580030340f4144c00011030503415110f4114040340081d8100024030020304100c80d80782c0c2c040c030240740043c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 164477239 1250 164475989 164475991
    0x3020c0a0b2403060121060905100b0a050904051f090203063c010b0a0e0603070809070f05010203030c07030c0c0603060807230603071407110901050d0203100b0112020706060608 78
    0x280682d00c44c20040000b140400300d21141410010400d07800d210b140e0428030050142070002500c240291601444c5071144c5901640315007200341e800362100b6585900b080b40b080800c0300c1c054080e41000c42c030380c018031203d4075524092250b0084001058a140d402091501c00c0403940300402072a0340404c0318607a46460b005843c0002100400c0d10070b03100e182107511840e10103110315402048045509001c813406070f5130840311803c0180200e03440340340458001740207541c00e6405464a00804101007402e65036044c1d01800d451068004518640316a020b10351a684203107015810000c250000d0400150040c0060300140b01558010420a0402c0307040c1d400e0403c5a4412200b880032a042d4007445002d081041242c44002c03103007692280c2c0c550809607510074041d801c1003002040000c1901c2007091070035841400020540d0f03c040f15030f0301e840a100c0c51110311030000c2d501d94820000d20080360095008020240010b1501e0049600c06540c1a420b0360801503003101e009458070007d020a2354403170045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 164478489 1250 164477239 164477311
    0xd02071106090f191e0311010512150409060f090308090c18090c0d050307050c06040617060f03010f050405010507080103030807050d1503052109060a03020c0a0b 71
    0x52450032400000203a4800f440c50f01041c094800741070350111a01c0500d048000605205a40da021a1140032090089108034001100c00b1a400c0c0c0205c0c041d544510255050b2001ca46084881a143c1c0408600c01e0b00b40c03400c56a501c01e803507119000004096000702d82c9014050317000490708201a00d00038100e035100806ca812280c1c403074100c600b00c640c0c03200d010546542160a084820380c95501c01d09003001da15004081d08048650000b004111000008011060150b0140d800c1c250400e000c1203a141310301c0c8a1000014221f8076060350384a1401012600a0f1004210302041000900860300750358207080310303040e41e580e90400c00051100038012540c2c41103191030316520b82d40c110754000d403030704202821a02c204800440e403c148089168090716660001c0018600c006680380b90a40d0742d640100080c88214582c800081b070f9640448040d1401c4000041c2420b0600c078001500b100203400001000d40741d03204241a520100799501c1906000314002035803110784405031020b550504099a043d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 164479739 1250 164478489 164478499
    0x603020309330c0f120901090f0506011e0506070201030c02010e1006140904030c0b072706020c040501050f040e0a0c08011b0e010f0305060628020d11030406051b030d020711 76
    0x75000414400c441103c0721410702d0b400540041d162146c0c0b80d401000750a80c0203260038100e00003403060290020782c0a04841941c03c486100300400c01d40300c10040224481d1540190f030900c1040f00560080c1c01010400c400791000103900a07404086500d042011101c6001460b03407210700340704540070800030380941e201c01d84110034035041c695402842c410700719401500d0342c00c103c070104002c14411034000f201403950140f04a000c02007421a041c0c440104d1103050090711078401c01d05d4840c1064090b01e03041b204c0042c8840464280c2c0e405000240400700d080790400c2c0551442e1a00050500942d07a020303040e600d00009000102501034070340c0942071140c49051007246501940580e074441e841ca03440d500c076440d010425855960115840303009040c00f59006251501c40c0e4100710421004003041e2501d01d608440707108040340c500f42c90b000e0544100da01e2a410820007480224028402445148140341c0230750002004425001e0071034008100403111107400280201c140030310102424411031007126 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 164480989 1250 164479739 164479747
    0x40f0b150a0f030f1b15031a09101701020d050c18150702130912020d020106060c03141303051209090a0216060506042304050f030705070603020309330c 67
    0x344c40a0002d034074100142005090300d64040342810502c0305000500070340160360040340000ca0050b004e00000418031041581c2c1a0200312070349040003a10340a00d880c070940c51104c0d410503003150004611003d02540e00c0d9020061110448094480d46104403000107120342c80c2c000c1140c450103440c580104c80b1f80304400144e62030354144140c10864100903411500e0b41164148411846e0181100c1600540600c44c00d10012844540100c0c4810348448140c0c000c221032a2245819200e05040680240024030400810b203102e0100c1c2c00240407209078160000503042c0c0d01d654051809020484000700914003084903400c0742441c440c4075400c4010a542941400b0403008505460340c541ea40250409444e0000b00702c403503e46912100c600d002242100c4040801e902821098607016581103400c1d12548101050807a40401944c000a034814040d010951508204501941018044d44200d0280e0882061540041d0141c0306c1e56810400012890b1001c0304000c03403461100904050302e06038104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 164482239 1250 164480989 164480993
    0x3010c02010c080705070f24050f01150e03160b04030309050109061713020406120b0a0c05121b0a092d050103021614030c160518040f0b150a0f03 64
    0x18a01913010035545020307601c4a185090803400600c1c0c1e140e01074070408404030800e18040c80b04050004241c09402c05000380d4403803001c0d03102c000c2024450110009102d85105045510a18503509100320042c00c5410743d410590015030b101ea95a40b0000f007680000404004041c0c00405000041400f400c101c9688e6141c0200504a04100d80b201c0803c1c40610001800795010710684101c0c141c1c015104000035a21040c0800d01d28142c2e49044d6801d82c01000010a40156800341c032007000d0b8159905400c0541e0612030a02501c4080d012080c88100004801c0da0055048062f1803c40c0103603441a8181c3c3c90400340e10380900704690b503920440d04480200c042d0314080c981540c200c51081c41c0060f901d0b41e0703800510700010700440000303140b455884203001d1081000409483d8074a1420b00360341d04a10610310710310068103144105508000da900c05680c070911140c1e4451350042c06070203c4000c0300c030a42d07641c0310106021070342803d032100611600d00450074416051005429440300045841d0300355 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 164483489 1250 164482239 164482247
    0x1e050325090b0f060c0f01150503070e190e100207050c04050105030303070c0809060702060408070602070e04050705010c031205040f0308060d05100c020307050a05010c120b011e02010b0d05070503010c02010c 91
    0x242610703030040b50300044245191208006c1250b150703200340020031100c51254040d9118141500c11303039200344600c1902003074484105d020039000cde081302100701400c2e5070900c01c020042e102104152a41d4040c88000340c4c1c0003c024001000361510800261118280714001c0200b02c0303e0682120740a80d205004010071142c00c030f90341c240c11035040750440d515158902c0008403a80f0a2450007900a140070a0000340395100142d00420359626409030b5444540b83d16514204180072240500030360f20031113040000b540a52030040605000386005100c019282080070f0954030709070342c120b40c1d00700030341a20010301d603020301c0054001c0030888203035042c411030b17841c1c1e03544c0c41030070a1000c041e9580e102d041c220064020005c80341400d51000079070b21243c903e41007490080c02e10030100c5c6c000c114540c02c95014000d403403040503001241612200d215142c07011b0180c10b10201c0d450329800b9590798034802141540d80e15144002d4500c148000c10032a828a000c3c94251081e010070749003035a04102500d0f40c0d890300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 164484739 1250 164483489 164483509
    0xc0503030612010b0a09020c010509010908071e0618022b02091f0605030a0507050a05070809010309060501090b030f0106030201140307140d021801020a0b011e050325090b 75
    0x41201c984242c0b03182c80b05558010901c0821540c1e04c101d500b80c0c005826440d0f03401030301100325120001c201035a10a031026082c1d500c40d1100800c1c0c2d00c1d003002501c00140611a150584080ca1141084c941c841a80c8540c2210001c0c0a15520151100005811841c1c40c4505003103400c03a0440060702c1c501155121811100410f4009129201d05030005481038030780310b000301002c100031065404181c0c2d03541019185038020381c2d031070340294241800038800700d000751304a41d07101c080d46d0348040c83c203241c41d201c1d00059008031240604050b1a20300e2040410f0503401400e01030140c2034000603038202c01404040c6000741600f4001c1d4542d05000e010800360784c2000e41c1115010401410719500d5840e0507007200c0903508440d002e20081408986030403117058580c0500200c0103140514962411610016a07507075000e00b06c0103003c5500c52005002c04403a01041106034003440254104031600c540c0080d0910305e143d05080746107101c3d2244028100001c840e18001001021b40401041d40290080754007800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 164485989 1250 164484739 164484751
    0x120519150e0a181527020102030301230d0303050a0606090f030201050f0c03030405061b0c0c0112020d090f0209010b040e0f0c1605060103032003031f05130f0c0c050303 74
    0x50f44400c24070565005a018424080d400400d81e9104008160340000428211101c1e04c070364003940348583d02c038041d0049030b4030049805800440c156841c284401940e0307000340300c04000b442c281855a02e441c0d00c51010040240c1c3c808d031804210b91400d4440300c0103e5100b03a001c1070400050b18130030000302d40359011036401e9a40a182042e030b1240c81104454140c80703500e401c104180300c000304120a201001c100039009042d5100400d0380348001580c0201d10b401500d0518000d600200a1490290b0003104c081000e400d84030400b500746030402108004a4190707040943d40328000004090440c03074404c4072140500f84201c5094103244c10070044403a0258003c24003081540c10354081039014191100791040300301060300801784250f0f01e141181d1200420b10080b008203021400381d204c10b2000004e8162035011031401107080d03607500c1c01c88074803420541e8007925502c0344c6000b012a450b00c0d40030b8401d20000c03400381d0214401d50400381c040c0880f0309508029040109a5900500040c1c1c00f00449411003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 164487239 1250 164485989 164485991
    0x403081b0906071a0c0903070b0f1909050a03050c0406060201063002151207050301060c0f02060f0307091802040506090f040b030d0f03051506070b07120519150e0a 72
    0x1405030301c0d011307050b001d141c144203400c03003500350030450141060002400c11035001d6091b1444c0c2070b50340004c52031500520701c2001c2807920030700030400948111000d0032004901d43c030b01a02c54603a1000854094101e0390030503102da40000c458240581818001c0b2401420303144002c102071b925010120040c224542e90110b860900405c90000304d1040103202100d45400500080500d008084030b42034641c4900041c0e6201d04808000581c10360207841a030b8102d645503240d004d4040c079aa43e0300c030000c030400302040364003010902503084aa62004091845058681c0703401000f1424000c000304d0498441000d500d80742d004110030b1041d900d90300282d171680c20040c0c0310300b4408400c04c030024015203013285103240c041c401c400c603100c03500b588100b040d9010303103994034204425141d0310ba0441c4031020755054550040400c00103140004c6101c032020740c0c020f045203084540c07540320003605006e40f0001d4521580c3e02d00902a2600d02001d00d128202a07a462410b18044031072038a00c01081c14000107103110046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 164488489 1250 164487239 164487247
    0x6050703080c130e040302192612010303020f1e0319030f05091b1906111006031a010605030601020a0204110904141602060106021c090302030d080403081b0906 70
    0x3004100c0c0540e0b41030141000f15142154481d400b80751000d00c00c40301178005201d402e61a50400e40402e008108068008550017042c0c140040c01d11040c01e0b194081e480d04603010400c1c4070302c131002009441e010314400c0e1302030301414000c8500c65203010580307080c07030103404561420103100c1d4500104a980340741c40300c0f14070203207801046010f41c000c0c0020100d60402504010070400d04c03003400710303c42e01e81032524510340884110484c04c0c40b1210002c2c13030000c0084400c4807414020300b40035500a84440d1600b03130032560070010401b0030400b52411035004682c0c40ca1401c140c02c03a1010203080301c5025010342d20381241186400380000359144008800a400b82d66525261024402404101d4200b00d5016209001042c611070b00d600c4010342c01c5503c5026560b138606501402d5201144031812601d13070703a00520f0002d803072119a4414060080b460010304c0050f03d4000010784080c0000a0080229100c282d06868a0305026050440c0104038801c0402a030480180c0f003080d002c2038903120903090700d01c1038407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 164489739 1250 164488489 164488501
    0x14120301061d0928020a1209080f0a0306050315070f0e030f010614040b04020304050717010212041101031a0d0303051f0f09290409151e150605070308 66
    0x42d800002d070485811140b41e03401c0084500040450484000c0304081c400d0300c1c1002c0401850890080d844d0950000f401e001400c0800b2074036801c031000450088487c036250550000100c006030b031103865184082510341d20f04020358582400000c0aa1a84e402407403e2441c0122005040003800d801035418407000d032100d1141500d04120840142041da802040500d440303100740d208404402e1440c40c816810a01c504849007000d00030760740140e50040003440400c0c1005041c1607000030005074003515660034040c901a2610700d074900c5004034016051382d070b80c2c030803c0400181650041040200c010701a110b0014071a01c85000c0180f0305900340c40c0c009216240c4110340c0d10540c400d03680445d001c0001c920040341c4602060002c4086a140100401196000d41c0c0400206040050152a8075012841c00500c07410650000c050007441035a000e40410843d03940841103070b10f620409070700c3c0d50510032401c1c1c40044c0f0740b0032200c45400a0340c542044034580100100140300301d4900408101508010601e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 164490989 1250 164489739 164489777
    0x702010b042d0c080c07140601060507030e03060412030207110a0b0a080f010e04020f0102030d11130501020613120903050d0201053103110304031407031412030106 72
    0x38000d00024820300c400012401a104202000300510760440380c08500030200308841d1080030001c20341510f8081190ba164031141a0303582100c2020b654040d03d0055141c1c009005100c01c5003e02250744400c2c1c1c03640c4560800410010713952402500a6019405000c04540340e00c0c00b04041e83e01602d0007694443c0c0c90715000458265189c42c0c180c20050014012a9036440c19014002e11261507582d44403581e2164500c0c0400070003842081ca4a1032468081009030508410300214840180103c1e0314141c44440041d0490f413284034005400d410100c0c00407816900b6044240041c4804d10003007c20341011140c07403e40f90f290640087c42c0c1081c5a64150040d4010243d10004580103819220010000c900184c060130080311a220346d139101c0803170130b054601364a0094013142c0050301c16003500400b0380c7c5c081d2601b40341c41c0d400d0036561000703200020006030606400c0320520b43c1c80003d01100d9141d4a0219003008040000c841550441c1e8602c1d101c070031400043d03030b044407060b2070310f482c41c00500406c100f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 164492239 1250 164490989 164491001
    0x816030b0a0e0114030304060c0305210703050a150e010506030a0b09070201050403090510021c0909020406031a15030c07022229030706030e0f01090302060901060b03040f0b070201 79
    0x1504600c0703804000034060a5503094034100c4061200c084916101081003603181c1c4240e000e280e020815a43d180000302e84210064416490400d00c0c400d0080040c0020344200c5008031b0710b20001948443c20000b26103070900402e01d80110a0001d21091824981008405c1005018103809441c004c000110310030f64503001041030340b01c003405020480c10031681c001e0203050708072130580204001440000d428105a010f405019a107030b8041c14205003903182c4a004403e8902c0d4980410002d12008640c54a6510041c40202840d480009001c03501e1070881c0c0d0a01107000415104844032803024410001100403a40e00c070b10300b110000e542d0038031440020340107200f401c50001d042c0c0303520b189200320070403d9000d41c24113020140004d8020b0034801100a4844449101c00c0d0560002c00d01000b40900a410103400c0141c24410b5030301c038803ca010759a0031580340c0d000c00e500681c046028007545410a1040e41d014260b00566a451403515465646103c02008001080c442543c2c0004050724409e501c49 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 164493489 1250 164492239 164492261
    0x9090c120e0c04141f030c050402030402030106050a06020a1a010e0423100f050603062e0302150301060f0c050c01080712111908040f02011b0f0c06080603010c081603 73
    0x410074038013241003411820004441c03886845c5102c03521174164084158400c4200c030ba001c80d40c170403e03500340030510000c0c1d000507108076015900c075840031640303a4480800001814040c0e00801da6500c080c100801c803030000c807100e02c42440d22100107102403001c0906059010340c10080c100c000746401c034908034031280ca40b400010180120300c0440038946060b0050100b000b86000c0500084c2c60b207c0801d519a0415101c50880503030200d00a640410115455650840c00c00003440300b142c2d0300d80115010321083d01d4401c03256080040180302090b001803159083e03011514210b14210401d680305a41e4150700c2c400c060511501400186404d44a610100400842402c052141c2240e0140503d500d401c0003c0018402907441040c940d005d10071740c075951040340c001c54000390030701141d001550410080200050605c05802c1c417030011505803075140f0b10180c82801600076061406d03000401007280034110030301c81d9041a5600f001154070103280343d0051a2005402c048100981c0c2c158018a825802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 164494739 1250 164493489 164493491
    0x607060507030f1a030615030a060603080703090e0f130c170703060f09080409090303090b04030504030215070b1f0503150402150c031b010b0901080a0309090c120e0c04 74
    0x400070300e07030342c15001141c4000701103d05000703441c0e4034110041191804096581c241c1e0100f070000e401200d03024002c090700c9070007070280c513508448e58480301c00fa0f4200d80c00944020070300150980401d03501043d02c0c0c00514485100c030000e03041c0907500d03040c1d120b0007501020600d110708020200744003a40440f6001400f500642e031566a03011301d03c690b1030b00c18a201c1a0f5a003481c1404000740310340c0034003803502980d901517a241c0c64075051020b48030041c20908015070406954000c011300180300410100c0c040c900030b13210305884e1451841000f8203101301e22580c0300e444206100d1400061154090590000c250801c80010306c02d0381c0002c4100c210b0194403480e0300d48180c07201036094401e0040154000c0303009440e1028840000d114609032840346001400f0140d1003045102071180741c0c3d07000c401710300c02400008150340c00001d0004215040a8200030040d4200c894200c0400d030304003903140001d03d981364060010000044000d0f28010b440c040c085446522000302021001d0103020005180200600c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 164495989 1250 164494739 164494741
    0x11a03240f040501030b1f050105040501050d0e070e0a0b03070e0423060a0207030215090c010c0c0e0a05070e040c090618031a1617010315090c03080315061e0906070605 74
    0x21b1005000c602955480100c0c415505070040404101012905445060f140e640c030380ba00c1c00004407916842a00b0740500c6d182e0702e0810b50b80d011001d100010040c4038411440b00c10381030140b25003049600d11140e1031f02c40c0d4400e00040006840200c03120354455003240319242c0d406804001901d0210f440c4490350414047d803010411140c040d64044c003800d6001c1d0b03007103800c154400500e84150722001e4416000541c041a07110945620800d4a60000b901c103e1140c086955207848011310441c0543d0a0f038009a201d50401c1710381c5070300c010b80742ca00e07410445d41403040d0007039048007a20202990041404000317585400000342d4030506401c0c1d00440d4400c0c0880c240c0204603a2040340f00005581220520411005424105206503c1014012581c0540d52000e904e1981c662425000c0c4c01d07038403116182c0720285c800114009804810045010751202641ca280403500e22622190f2520441c2c07103540e05200c655000405040000700300010800071640c2c1c6c12403200054001d002c0e013030000300080d007444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 164497239 1250 164495989 164495993
    0xd051608030d0b031516050c01020307020307030e010302090a030b10080609010902030d0206090607030203070908030d0b030c15090405090111041e0504020301063002040608011a03240f04050103 85
    0x20070381d5400b6401d00708400d240c1c1da8101a1a41d41e441c00309011468600040f0b0404aa55080d41c6d20120650500360301d403280401800342a82c004690040c0540c001003400c9007450341161024041500c00d28046180881c10f40009070042c046010203081c150790140065904420001c010000e07228000c101c1d5506c1c07820510590180c032081a04900034002d0b40e41504510f1700000d1072500885901025103510740d1941000c400175080207040a04200d18040b000445000a000401d51613a8030703040800c102e2032800c285454500d00840e0980103a0a0040d140c0001c082d09041e51b03646441220049070503200d8586950241284004a1050100001e0b000038102c200c0303040e2a0706031411498030040680c1c0e0744200320490100340b20b2600450f12120b08062000015007117007082c61070044030340480c12100d202c40c104a8016801410104814000520400c400b4400341d200040b0240003151451400000c1001b281c0601c0c030800e214481904015003c5a46624070200000f00c080c208008560b964 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 164498489 1250 164497239 164497243
    0x140a06030b010f1d0d080904150303020d0c060b06030703140f070512040f020a0e070201180f020405040f08030c0c19030509100504030501090b040614071d0d08040b0a09090501080a020d051608 84
    0xd0102a01ca10314000d001c0c9d0510410380104c03001c994054002c1c2040300d003080320a0b145226054402c890156446070307003150076610380014502960b403541c3c0001e1126001070407040c624070094009000216108100000c440e031000c101e4508510b19818403000d51128900044180900b10000b903114580d1403001c6080805c6803816840749003158001d00c031001424181c0140d45210890180c084482805840c1c054242034100030f4000d03200d070344504004480c60301c0342242c41d003003552042d80880002602071070083c3c0400101d00d5003034050020a80c0d0302440c3e54090724910030002498003c1131282d0080c200780e80140241c41c000c6170020028803d202c168039001c017550000300c5044908038036101e20304a1480014035414400c4a450f110101030b0010258510411241100c0b902e602c04a81500480051546000307000208030300a600c03070703c4010401000d40840c83c2c64018688080c9000010040f000e00019000162a019505071210311a2400e10500789900040c0c041c0507105d4840c40000c40441c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 164499739 1250 164498489 164498497
    0x50306041a010605070309090b030a0501090308150f0a211703010501030c0c050c04020903102c0d02190f20040e0d020a08160c140a06030b010f1d0d08 66
    0xc1001c061550f03803100d100380d4040c01101c1000d800901da1006c02d109100040c0c0c401c0d510740d00300508541c003407001da41c3c8042c25540200001c40020f4822014803403c001c8500903910001c10484007001c142c0b100e1404103010101c144100f0440c22280c1010300311043c06100b2101480d41c01100324030000c1c00c04615003107554420310445000070724084013072514920070940d4084441e400700140002145038000c000103500305c0400194107019449486d0381c0150b080c4100c4416050440740201c1711144c9100e00c0900b0180341e4401e40d99500095603d992050b4082070030280032204481e00741980819082c4501c0c0d400701c0c114010300340480c0c001a86d40d01042e0420308402100120b50a1028904001556448480300040d00e409a4014020040000d00000140040d500e8600542c01031803219218070311884c507554088040312801c4240c40e00d10b030030321001d45409042c4609052181c0c490381d200080036000e02c683d003402000600c0d0203907100c15600709a050080300004154850071101401d00003070980c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 164500989 1250 164499739 164499773
    0x90b0a0926030115030e0a031821230a03030c0903080a020f060108120915120c04080f0129032508070e060d03140d02041401020d030618090302010605030604 69
    0x504c001225040381c03080c00755241c040006406809503c0c10b41e54140c4540350008802c00090605240100b909069010030051103028002409907001c4982003c04070700f0503000c040d286030444003c601154400c0000e441d80c8041d811302e4002851050107804072010046a00020302c000c4001500204041c4d0005850203c50801c000340d507100c0c2d90b1403a5881d070320f4440644045030564240541c021500d0140c142510321100c1003039841c0b6004490000c03d110701000c0b14880c588540202e0288106101001902c2d080442c44000b00607042c410340d8105104c16580032001000103101c0306421550310113002028032140030024140c08214400042012214503000700c104921030307180c0000d032181d0005600e5010710f03400303480a0f4590b00103440480f00e02100c1c11101ca1613003000c0025203010382c2075100602c01082c15850100226042c0000242415821090340d030400d41003600510892500c0c000c040d941290f0000300081d5a04540f0b410b901400e00360b8411130740340c003a800410050280145400b44145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 164502239 1250 164500989 164501009
    0x30504030806370b0a0c15050c1806090307030b16050711010513120303090b0604051b0901090305060c070201140c060712020409020a0e090901090b0a09260301 70
    0x1558500500c145034014454907410501c070000510a034042c68a90748806914504074800020f8949001d030784c144c2e1000b40240006803814000c0c40c1801a040b544160a640c00e1000348014100700700d81036554020480305c0d1910120803c00017001d43c0da203108075540c00401805681c100395a0b070505d00c00c003071812212520220041d600a45019108804075000c459000c400802c840e441e0400440762074020f0309024020444124001c07518080f0109052003840c400d640208040c03e045c9004581c046000c2c19450040381032100307002480395212011070300c54100e86901501c880005004075600495035001620305d00801c4c091101200d1540d0007042880c1c003c4c2c964180c81c13008619105228070800448080b9500000b0100f403126100742c10543d0070100e8614054285070f00d511210049030311004016000c035401000d11406404d04151540c0c0c801c8510300200b00880c4640c0342c828046c100107286a031000c0d07440380c4403002c024482c510400c00c8158418441912182c00c0744280d00e50740203001d000010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 164503489 1250 164502239 164502241
    0x1d09010606020c18040524070e0a060c03030b210a02120304050d08131503050a0b060a02151003050105160206090d05071407090e070e010f0f03080a030e0109030305040308 75
    0xd58000158090480070180240d04041a41d8450203e0003402030000c5440d40103074051040f030800c7c92609120440780000c924001c9040c0f0b00400b40168105095440c05511290070400465030409403480110f40c040c20041002d1a004d000282e400302001c8002042c420440b403162035070080000c0c060300701d40c400da4a006072450920744542d030741d000d00d00c03619620003140802400069041c00c013403c0c8180ca11514003034050307142e0703185620b9464040c0310240000d42d1001080003014950090104201c001e903810f0b0b00d0500c40711002505c503400d222b00521500e841c0c001050790035542000f0140219041002041142803c1051100c05882c03001e07030000600c10307000400d85840300421060207141550f204e0528010750b60f9940b0308045101c1d0031700c02c0c80f405988000254244a030103a0034040d013400c406001c40b14100010800d1029041e0002420130301c5401050261005802c0280c003680c1c0c02c03003030f035580f51003200104074003500030741d01d0021030703542043d000c2e004040d0034ae009140200d00c80d440320181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 164504739 1250 164503489 164503499
    0x5060603280b04050f1501080f0a09081c02130806010806070e21060a0c050c0705010e03120720030c01020607052113030f050703050a05030c041d090106 67
    0x614002075403410318030600c07420122000305a0a00d100d01205540780c0c040389807589080068201c070000c5030034040c12441c002c00c00c0b244521158a0301100e880c00d0a2500701800c00101401c10454000c1400000e00d5843e0700000512802e402a02c00e00a0b010070804400d04034000050003942007441c03400d510000c00440404c0f082d801080c480e0684124400501061f0f80e2818100d58801381041819000081c0e43c008045810030240c1110803040354a00a1189040410300801100e14080d8011f04000301400030040718030000c140002103660074600703000c0c500140c07000217003440d0010b21003641c1d01c04005004410032420004000f0607002601440052803141428142c951b440798074032038010f030440c10000d03c40c1409400900515208002d40701c000c3c90f003054901c203410f0000d8410b10416020602c1d29000c05501c070150a03145042454941d0401c0003580c4e0152081c010024120140030300400003842d2510350100703503802050360b03440142800c171132441c089080d01c205503441e01d0390303508000340421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 164505989 1250 164504739 164504749
    0xa0302040f0605012c012001090b0712061d0402012c03120a0c020d0c0503030c060906010f06201515030c09070e040525020304141807050c0c0a06050903010506 70
    0xb2082109a105590207101728004503503040080310644400e0304807a421b0a00000f003403094484c81c0380308001183e40d0b410401d40c060b145981003440c0c03a018a0408105210148540601e02c10718205000c104007192a20310040c2e8501040d410b18440c46d90321202c2d244403a18140b9140e0b44650015001e5503200503e480260700d09202d501c03001004150120350880050510400703402c005401281740070381c144d0710b61b80024250352040440b45415801712040c0b00010354203100180c010000002d015050b10315110010b0281035510440c100f40c2544280e185840260a110018014084181d0030074035240511280018030850035400e03000b032040440505046c140194118004c15540d240c1011105224003004040e14008000100340d10011050140b1400b0340c0111809480d02900172307603116420a0302401e06641d002c0540d502c513031441248030b609140c00c40310003a0002114900141c0d162140c003c52403805603400400c5030000c200d140300240c400d500401400c05604110028003081c0c5038102005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 164507239 1250 164505989 164506037
    0x5031612080f0606070c03080f09041a03070e041b0b0c06090c1f030b09010b0c0609070303080703022203140f070b180307090501080a030f050711040b0a0302040f060501 74
    0x1c090340c050300b40490550319081c1c010b8008148079464100b03040c0d40301e544280701508485044182c05202081400880c5001c0c050143c03031040f000c0300380c80c0e400f251600207a501c02c05803080700311381e0f010f0201140c140704664003414100303e484042030078010b07556180d400d010740c042003640c00c141c010000800c0c4159808600501c0314480104084420140001c0001181ea005401801450794400042d081500d231014014000c01540c0012602e4810501065050041c02406110030b03802c880d90a1001170f07007005013203400c28018600141c4621542e4940100c0190040344800e803081401000010048a40700c4084001c880b101681c07641140c0142c0300b0751726101030047c440405030905c40f82c10428403816004640c450003c00710b5101c150786c0d0344648200c40c001c0e0054000f40c0c20aa00420505030000c0c94030016604610701a440c00080c0c0d01c1c1c80808882d4004500d20464861070809815030b030f085904000746800920400c00943c20038807102c010086882540e0100e4080c0e00482c414084030795a10f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 164508489 1250 164507239 164507251
    0x303030b0f10050a020325120206011a0904090602070b0402190302221103010f030615030206030402040e0c060a170c030408030f06041104080c01030614060418090503161208 76
    0x56080d0305040780c143c1d5160460142e0704114030040c082c4c4010041c1050400d26094090420030f14006581c4c10000355546071440034209640c800001003045280005003151820000441d641d21101e40d00300140190204c00c0014100600100312101440312821044d0f00440c401c5410381007010100204a550031b0281c80003035170004c00c800d1000525103048100c0b0700ca6030f4004900250083c846c1002e07000d580c0081e0401401c003185000b040c020010349116a44500350a0384114407104e1039540024500c0c0300c0200f00a01468482c46055045201000a1000458003e02c019241c07503007164010301c10750310840790051400d101004540c0401414045138003841d0002e80051569035448a0f40e50310308006000180c2285da208568048114210040e102410100010702b42070010b501c001019114036400c54422188480c40054844d580e000899048400300ea4030b00961060030900c62000b8104200e01500f94040041d030300d0003000948c2103959100f845021424a03003c1c9545040312819030442d20 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 164509739 1250 164508489 164508499
    0x50d03050603160e060303070b18010e010b2214012705010501201f0f0506040e071701020708030903030115050708040e090c0a060503090f0c03060a0209150a08010303030b0f 76
    0x50004120f01d1308a00d0740054054101c03890803055035600c11140340304072a410004d10881c0c681030450b81e000e01074040b404041e0002400320515031400503480103005498001f500e20b449a20040f9020680c01c610070914004e00442841c0da0f583d2000c0d056201540801042500755020441e51400644656410b881c410303940d851101a0f01000800403402c0304407034844034481c42c41c03040981404806650043c034030003a400709080010301c090100350760016104600c2182415421408280001080004c0324884007050b09106003402841d4024440c51002603c482e02c004100242400000001c5d07040307a40d0449003888030b4161517400c035420b0107500c400070010346040200300100c10b02c1d5503107140c12411880565008051400c0041c814600a0303001c3e20110b8004420081d0255052007410f4000c10084040d140c0c20491500013900e500000f404120103503070100d9a0758841e01c42d14943d00c20082c5801c00c0316520801130001920050091100307c0001c1e0519001030701c2428131035507070480c824011b05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 164510989 1250 164509739 164509783
    0x1060f0b07080c07031506060f0806090717040f021f090e1005060a03050a0b030f070b18060a021b0f06030a0b01030b06070318080307030503070f0504050409050d03050603 75
    0x40e54900c035600404040e03410010600101c09806824403003003004621548042e010041c2d9001c418040d110030754850410b00119618245160b6040740700b0a81c4180c0c21a251403003940c0e219400d48184026055003c00c4c480b1120400c0100000302d5a0070058500880b0f030311143c90816065510007103240e0866400044400008102d08c0308034038036468100d4051120300d190540c0f20b01c003180094200e112800002034aa005000500301c680c81440006003050300640500c01c0001d1407603903100030900c0381d80c10f201c000007003a002d80b18490b2542400200014a010384c1e800f10440001e640c4c6800c480441e90f1003110310243d814500d0004400005042c001e04050b0941d0788078480c0c14000d006150809041c541c07100c2c07003102681e580c41d008049061098031900540700f0701000c03841c851440c5800c90005a8810814100844e4114003502c5c0d10500d1403402d1580341032401021140c3e40143d40c042900907080a03042020004089a080e031194490380c0d04001907503501c400c2542d02d44243c0d1422200400d408 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 164512239 1250 164510989 164510999
    0x7020310151203030b0d0b06120606030c120708190302010b010302030105010c0201030506030c0a0f060306080a0f02190305100203091c0915030902030f030306030d0302040e0c03070c0c0f0f0801060f 87
    0x801c000510b90700900380000c101c164040440c8400c1420041218840007403402c21001d80780906013500322050b05001419140743c44004a6542c2030041d980078421101d40e6140c29958034104020380241030341030251354050402040700101014961404c401550808440314082e522034800e4038100c540581d1400c0c80315070942c0042d002008080e001c00e42500074081505c1d6a83c480c54001e20003001d441020302089403902a00400f2a103954110707e01c543c01c1003243da408514240c8251000035011101502e4100c3c00340d40e80c4000101980c0000e00c10300030010b1030070030058164007440c494000d041c00c0e601c1000001c155655610307024079903d00408c840785418040306003440c10101d07038520306080c001407454003500007a00d0b1510b000401c64055000108200740f41c1001d11030800841540e040c10740c24141081d204402101004055000413040031000640700b5103e550140c000c9034204a5100300c8941702d1740310407070082903405200e1028840981c005032605052050400300d41f045c0000c070813014180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 164513489 1250 164512239 164512259
    0xa030f0b04091b0e040b06040c020c0406080f0d0207030f0803061c0c090501050f0a03030806030f070306060618081203070e060d050402151c0e0f030c070e100302100e03210702031015 80
    0x402700404500c1030781d140950076100c600c0782c8009010351100400107607138041c080d94500380780e6404244c1150040301d81040084c8060100b107071140d510415140d2255100d101180e190f0324080e1303e4001800d400d0301d8030020f02038007414280c1500c113102000e01c16aa2a038040c0140d06040d420081d402001407101000860311501050b0781149008080d0394884400c1c421680c900740c1c4903001600c4003580c0340010000643c111460f00c41d0000602c0e07588040e0b0346006003160300c40280b180e058010241c0040012421841191003020042008080d00d44030358084612100511049404900800380207640402d400040e00989105001003041e40071400c2c000c44280c0c010380781912090005205003074940c486c5c2e80052001d0061303a85414014246603281503001c0300c01000242203039200740001842440540c584003101c0100c4441030801e50341c9103003000013103441c04c81c081c0e8202041d1040483e00c800700900c08402007800c580200e048440200c9400000022100e1403a4401c03000300c40d1038010002c0800c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 164514739 1250 164513489 164513501
    0x70c0b18010615120f15141c060507080c1309091502030115020706030b0105070204091a090a02120f0c010813081201090e070303050a030f0b04091b0e040b0604 70
    0x1240300046202030707507801c04002001d40c2c4a5078074089102030b100b1190344038203131040341100c4044003c1407210003400d00c0055003d610038001c103500c41c4440c0d8900b04141c0c03100211600c1c1d00f002814210010302d0030b070400c4001018252400400560454080755544250200b91031003003c0700c50100b01d08901d805183c0000700130005080b603440b103510503055443d500b24400b95008002881860070524030300d410003401c02840784c0019060524005800344140d031f200003510718041d8140c400152500c00c0b803e001d001004a00341c01c000300d03000c20003003010400b404503924413a948280c404070040c0424940d029155410044003464070380c40070722001c2c85507125a08090300a422a1000d00c960341d0103403a8079240d0780c012522040040c84441c01001030420500c81c0c0d00c0728aa6a00241c0007050560303a00070803500c07690190300205038440c0c019884441c10b5910000004000074010031821500e49000e48181c040000560b0030000504000101000c81015a6116981c003031920079040e5101c000b000300500c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 164515989 1250 164514739 164514781
    0x1401060519030902040f050f090609030414042c0c1206070c0314030115090801020a12020c0708030304110f061303080d02040305010c020a0c0605040b370503060405070c0b 75
    0x3840f200070720301584440c81680101c0707082d01c0c40800c191520b51089889040082c00020465001e90200414103002100b510150380d10341c1c66031301440642c0c0c0d000a0203400720401628200000c01d0340d08400340c84421515200528840540d40c81d0a00e6200300b0001a8030300540048542050001503140c91141400c600014400d0408110329130b03408415007110b4000f41c118400200e0880c0e0085035180c0c200d41c0400003410610000c0d0300e42600589e000b0000d4010141d00000c0c07580100380c10701d00d0041401000c02038075151003101d48a1801c0d040c62808c024582c03a0700e41c040c0290034a009100c0c20300c070044940b81201101040301040c034581d1441e506512109d1030840c01a401d00010000510a0160072040e0406500516002000f410711950b2684558021000c1c403100f003000b040002200400d603081115816142d8550360100391940f0f1030880c0e010005006041c1160400b00413540100207076000325020b40d4100007590303413103505640d100c000e42c8016103403402c1980040d19100900100646040c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 164517239 1250 164515989 164515991
    0x6092803112d04091b0801050a0203041203110910021c020102040602060f0a020405090a05072a030e0402210106020c0315041113050901020d050a0908120c04120305040801140106051903 81
    0x520350702c500003865400d44a11000c2d2011702c1c41042040000d0003403030380008403c48210704c2d500f060798a280740350492010801c24035440c0c1c4414004950b080091701d51001000d00410800822010000d480310318440607041440c0340b00c880c040f8050320510036102070703541c65001071010781ca91000b9003210080091032035540d1741e0204800b141c41d80b1042c2401e4001c010b020004226420b0554001e4101d001c1d049042d2402004200d54840d40704000764807244054260038900d44e1182040302080180c802c01c0b52030304240c00c400e00e960f65450a407414250495410742e080e9609a0201d030308158580f181c1142d00303039100300044080b1740401c10f08042140e41e001c2c002d001d1441c05018031441c20640340212540d80040e54041101c5943c11094010326130f11020f4080308111090b203650b80c0341003a0180666414901004070001502e4492650850700035106981c03454816494034174000b00580d0160043c081c0c29400c007040481c5001030701300b8480c140d0703006880c0e042c02c002805118041800520688400701 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 164518489 1250 164517239 164517251
    0xb0c0702030109120e090c03010504110f0313021f021c03020909280b0901151218030f030218060903210705060708041106092803112d04 60
    0x1aa030900ca4000c0c3c0c50310a07403440000d006100000780550100c0303c1c01034090b4002e84100207001c0b003c0411281541c1d02101c0014440001d1000b0312860b000740114038064402c000180500002000704040e4001d00c01c8070700588100d4107540300c081d8000c01c0b0088034090390006408254240784500c0648110506140060800f00c408001030403003002913a4500103a52103001020140500034403203160711450302c000740b00ca500c03003201049000030148260100c8000002a14031080d10a00040350a20b040d100305000b50f8003807025132280101424422008140c080a4200019003e8002e40b88607011810a424030002003400340b04050b4030003a923107130b070601410184420314107800407000000642180402d44070b4240c0d290140c54200040c1105080c442c1540401001483c46a200701d9000026509103448602910100e0030f042c022401d040201110031889004407400511141c0c00c0724056024000080d00e513809100e07109952640b201c01d04840d034100060407903c101612012070b000548005aa = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 164519739 1250 164518489 164518493
    0x1180c150c021011010c020c010801230901060503061f020c0f0103200304170301030c060309080706020406020a06060e0c0f1e370c02040b0a0e0c0a0201060e01030209040b0c07 77
    0x20240c0104080c001081e04e07880603c154400034070802058960301e000606a100401c070001e0000d9005218807840040301001c2c1c01602c1407010403403205840d024010340080c0d40c44400c040e000d500110f43c01030007212403415580c40782600703401440a0a04680181c0694400d80052106404440050a060503191a580720454814604404101076024140c0c0c1d246d0505103070110301e4510210081c0040141800180003282c40407028400701c401031704001804900307a1070f1002c240d004018014042c14404900061260b8011071188806c0c0c0c8104000c2140e10b0f1a081000d804041c281e40c01c07106d000c4103105614200102e003004000207120010317030031071007400f21690820360740c8150811000c5060503034107101041c81e03007140e42c2500e0801d640c4580e1000c42e10800140264004440a0304c542c1c0c98546023103807030310f07090102c0c0c02901044005181b170f0310b400c901c403543c1940580004c100545c60904002285068a1802410381e5802441c400b40da071541e85400586d40c1000d0507003440e0740010451840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 164520989 1250 164519739 164519749
    0x90a0804060f170f0c250609060f1a01030216020a0b0901021005010510030b04020706090309080c0a03080a08060a0e0f010f060201050403020703031805060301080a020301180c150c02 80
    0x100511081c1d80700056000c0d0b0b89402082100703201001090180c441e410f01c100007003420455540034043d0b1100f40d4498610500c052042c1d506024800c40c541e05051078030f824000d50350043c0440701e0041c94144008000e407034500c402c0300e2141d4000c5600110200c016030300e5620980041c88a042c103480c0300c0d0600307a61034001803440d0403142e201070100c6c4000680600c0d01d503014090380398000740711801080158940004102c80001d401c90900c0dc059803001030786803d82d116816506e0300e90304602c082140c400a0318014041d03800304e0240107440c0c1328034582103420303203401c4081d030043d00e51184000341803282040303050716509005810300d6403080c0400408211f0728407000f41a8410740c61f41900905951400b10b92012040d0150440c200b10f90414080001003a00044c1050880f43d15190614036440c20424030345600c0141e42290b03078485000000041c540400141a80c0182e00840c000c0140d541840340f800b5954140c11710080c06800d42d41c0301040312040b0142da048001c1c1c6541001c030310703050560f80064 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 164522239 1250 164520989 164520997
    0x50a0302040504050c18030f0c01080c0f0d060807080f0309060d0b06030412030507090509181f0f0c02010203070804060f020f030412090501181403031603020a050d09120b090a08 78
    0x40010952007030480041441001d11403047c0d02038501c0c80e03001c1c00915202e40041000f2810711940001117240c00c094403045504140c00c03115040d48070010743e81e4600203130500d8401d810844c03003607e070f0115450304081810410200440c0096140044220034000b40b07030004041c41da011550345184070042c0d101d907030046103c0c511400c0601c1035411450b602800b06c4202410250400110100c14449916107107141038201c0340410344843c070031081e0383c000d62030b10301081d5900c8201090202408010301322030f044420b03070304001d50701880042013008040f0b00300d00040368001c3c006226035002c42c02140440d0310402400030b042c60054071b0705d80c1c0100c449003035900c1aa000c8891012020201c03e0380c503403085038840648024a4100b58081031440b11856040042c041d015403031000c4108d80e91699020411a00141d1280018540d000010708001e922041c45090551b103a029071640040c06a10589041091392102120050303891165150240058401450100c59125041502c40803842c1030b400381c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 164523489 1250 164522239 164522251
    0x103050303190204060c03030e0a050111040801110a0212070512030408090f030a0305090f010c050d020105071b210302070f08040810230c13080607031a0a0501050a030204050405 78
    0x540e40c9080906850780301d1581800140b101610501090000c2944000c224000a8061a0110b0707034500c098005802d00311047c200030b00e55840c003400385a131070307401700c024100b1107055000821130310031420b02d01c840a100c0e00c40d0450042e0000c030650300c030600005d80075003e514051021604000c00702d4100040c942d205039402e0350030300d001141c0990b60f07150014540120715415000750410100b0380e54040c0850080c01d48203403280fa2005044001c0ea403003046078501494100701107502600c040741001c0d00912090782ca0b400003407140803d00a05c80700410131002100d0b440380b00c0e0054841982100c41300b0000901c1d00c501016006c012040214202d035662040d92405201c20350380e0307240741c020390a190100e00652604568145405640710070446001300b2100780c0d071000c00c0d0046940d881400c8241d0f11408104096a22815001081041e0f00242052195101b602c040000c9075081480e0800700c000d407410340c0d038010590700382801203501c50070140103103032500d090241c04c141d1501700060070386d08220f4075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 164524739 1250 164523489 164523493
    0x1d0907080f060402040c050903060a0506040e100c0905030d05071212020c010e1c0815031504031d0d0203030a11032106030610030b0403051c0c02010509060f01060e0f03010e0303010305 81
    0x20f000952505104500121025041580ca01051030f004262101c0f801000001425900d0707000a149840700d810600b42c9560006c240c0303060480f8490f0b01c400401982580100044000c0e6021800303003000035203001141ca0680301c190414403243c0d150301135a0100f40c000020400041c0844031106000e00140560b10722400011070b084032003001d01840c0c82d0240200700a550220b4010000d5940c005002c135421042e011a41c40c421354a20022914011110381010b400d0181482000207240c3d20079100c2d02c0c1e00000d04859052503841d6001c20148901440000e50305400030800641c1182c0584940d81031030a80406490401585090354a032629014104464580503a41004168074042c0034890b84500e5103004c4416090650b11011125070000b00010103001c00003030b85400350400d401d010740300c1025006040c4100e640e00346009000e048151002245840b40e9070104d03100303510307500440341600c0c03956907000c060313000403001c00412114030083d2070f80655a4205100350a0424001107000c1c0d030040340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 164525989 1250 164524739 164524741
    0xf120c030703050a1e090804052d0f09070c0320010905060c1e0c0a0206040308040e06122a0d1202060a0b030703150e070e0601031103011d0907080f06 66
    0x1405401d50f00003e080245462a1000030070800944158a80d11400da59000280207a1607242c00b09007849103030001503000508802420008100d801084142499018201c0049410300180608840380808036030780705440d00c0c00a0041486103803450740c0103000c1e01d0211110030144c801411140782e5a020310045075101d04074802407040400000d07400c0b1910b0380141e45000c2c1103c04440041d48940c12800c426500010314803060142000b0a0420640007010540d540340d49180c0254564454420341e81c244814100140c0c40345007400c07203051400f08520103020a412021031000c0140303900c06c5864043d50220f203050345140c032050010080340e440381081c1d0340010980407000e4130f0003000800040d43c0303900384070521849031404a0b5600440e540034042880024a4003112009810441040d59252151040014a03052210100c5020f0306003a2000c104003c00801e0700c0f983e92000b4043c030004d6088040c450251421745a031000e0f40600540b0503034560a031103690301410844940d0030801943e220314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 164527239 1250 164525989 164526001
    0x9150c09011b02030303010303030c05040b0a05070b07030218040c03020d0905010e0f070602071401030e150406050604060b070b0402190905010807090911040e0f190b13020102120f120c03 82
    0x20840914030000c58005a00a900960010307079281b02c140001010517480c2c802d0b070980303a07026406803000f5000388081d00da102d2102c03517002892900142800e40740f03110b60b280401c0031107009200f101c1d4001c0740801e00080720203211040c44090080801d01908165007046515114111441042c1005110300004604044100740c8989404200c1d00c80d460142c00011040210640024215084416030704a00070301814400040c3c00400390f24400b020340f8028000c080b500c202144000d68411740c40307410304101e2a1100020702080314458050b00307018540070404500480d115511881d8002d100400c2ca01707040c40034011040303681c000c0b680b0119001c1c0e103810050101c0314060014034003819565500b003150480036141c0141415402c01d040c1d020780d0b56170100d403803522024411407540300b50840c00c68010010052411410304641442550f0f14030840d00400c8110b100c02402c03041d1650140d00618081480103200c8110758000320706030600310000c0200e48259500f6040c040d01c260712b0364a1a981340d19002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 164528489 1250 164527239 164527247
    0x405030601060201050118051b0d0c03060608070903030e040b041517031602190b0a020d021236030732031f020708030108010203040302101103070809150c0901 70
    0x68002d0029a4104401480811450009440304049100000c203a40e10340d105e83c16142c040344003008004080003c0c600c52070785003d42140c454100c96550400200b81c0c0c0c7d00c003c652000f410348400000030310900c410008244907403520380007000010000181048401c00160031034070981d660f0710000c2117031541005142c44121140c0030100300c0c03001840c074242c40c0d607240c2200f8070203001c00240320390320382030341c50414891030400704019003003a45141d6914481c83c00065030720502038120000610606080f0f03003100340c840c07066508595900301240c0142c004441341400848281001c20031b21210b940181d00c0c02c2e07500304901401424505030700740d0000d0813128400702c900c0d08521900c081c000800d6104060b9140001d8042100312a001c1c0c0c06000701e00000740e140a0b22071000d001d801000084000304421206600441c080c07807080c1c084a0841d24402c800906440c0d01d6012050b0360382050001420180c007a082e289c5c0d01c402d5400503200340c09034070821031400d00c005071409020030b00c020170014055604 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 164529739 1250 164528489 164528491
    0x50114090a050f0705060d02031503010908090a05010c080a0e150a0801030c06080405101107050f010e0c0901030b0f190c0f031a03030706090c0e130203060f24010905040c0504050306 80
    0x1180010304104e90900300420b0f00f0b80304024100b01c17916400000180039507015107220700c06448c0100240070401050401040c0b54220700305051082040160000301580124920381c0305503840a5480c1c03c041e40f14000b5507020105545140e0445003aa242c0ca5001702c2c2a0010412001192507845642d41507040032081c6822940050040c001400140300c0451400104c2400701d601c0c0c128041404c16001030710001c80c0c010340d6030060203449000c4010200c1c4406400c0300c407002451800b11510200d1000c07c01c42404400e10001e016014000c02081e0009900c160065002c0a492520a5542080801c01007213514481c110740c0001c81d0351111580007503040c080e008090900e00380e041e40712030b50b01c03000070f46910421500404c02c507a111464003c102408170100002c0060b41090002031811200c2c410001c400d80700e04a2081c0141c80001d22014403800034580107074003640c4283e2003100c0208a0f5411816803007039190500011180000e0155a14002d40243da06a81d441030348882c5000c00341864010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 164530989 1250 164529739 164529763
    0xa0c0504060203091201060b0d1b030b0109060804020109050a0e0f06011422031a0f0903030f0601050d06090f0207020102011a0f150405040204090b030d02060411010c050114090a05 79
    0x4104410003505030b00200392416032108480c4904020310b044a054010182a40f20a02030b0002068a000c80211580f04840e5400884a01b0078071400c0024200c0482e10200095400704204013020b0182070b00c150b102551040c41070420302011602c0d040041e030880c039140e100303640da580c00c0b804100303802045d91815078100c4002c4c02e1000b0b0421a4030b092114138051141245041480501d0151460201000703890055030000b080d40c04031038856000c0d000c01e010840b20b50300d4000c01e48010403695100081201e1140000c81100003440c1c0f9900c0044072103600c0040e83d44541a120b8201280003110b0f03109201c0d4010754400c2c0141d444680d84000390035140e6600c94860810104c3c0301c0c40c80c054940b10400c4681580880300c650034981024400300403405903401c00c94226101040100c1c0c2c0700715640c0b041004a0044088075440582070b202260b503030f402240e000380166940b20382c140d5030303500850350744901d00d11900010410560242c01e071488a00125940d0400390b10060004052000502c81c2801040b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 164532239 1250 164530989 164530997
    0xf03030b1203040b0c03130303080412080103051e012405030d1701090902010507050d090f080307031709010204050414060423010b13210b1302130213120302060a0c 72
    0x100c00e000c10b500e0380a9481030f001020400070302400709410501c11928411108250389030296203c0c14018144e040032a8215500d44040c6203111100380501d0001e4101c9500c800100302c01c038125004510b200d414a410329030599202c0303d40c00901070031404c0d141c210003e108224000350346450304042c5422030042d441402c1c001443c440c4104140d4000303086054030b03a41100416014100d20040b10580708640010306580504010381617072942c00006a02114480840410647c0c4c944418980b648901e01c03005000c036902c0b141200c8800c10a071421b55001c90f0080005003400e40d2038020a09413480710b4141803d0700703410400c0100c145420b2262080e00c80315801c102c80d444000048862922a041c0296048248049030400c090000b02c40c8800183c43c0c4800441f400b5208141210917010009004480c0070081200180380c5002c400c0d480e0488a8000f0060f0809a5144044800070340c040300c0036a0701c1000712007012072402c0080c070011040c24802d0f40100150b140201c8800d04450b90880000200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 164533489 1250 164532239 164532259
    0xd05070209011517040305042405160228031505071b0203120c011d010c0504030b09011404051b0d020a030b150307060f12060e0c030c070b040f03030b 66
    0xd030710794080307803410b44502d03030301c02c00c0795038121803040d034040038007801e0044210036104c100020140d103e400703081120b940b04280406124100f580011034400340900c000007071028440c80d0b04000d084103603540e43c50300180011600c5011086114007600d03076507448220309511044104100442c0c404152860365058404019600b00030000a0042c00b035454200c4420103c22502012b540e0140070518203001501c2d000b5a444140807d0799029003070b4124101400c600004142000350300c107000307141c0f280002d0b664661a080c19540c640240c071070040d000d041c880d940d03050540c020104040042d03020307902580040c200c3d96045c2c04403443d071082084080c0d01642201c0c5030300005884017048801a00d5000000d055161764052a495210000c0504698944500440002d0007504005076648540f407a907a2008141809550f0324203a61591281504642d100300010720914401c0e00510b401684e90b00c100c07458018607490b05801541c09443c00d0300c11402440f00e03041095010310503d030703021400740c802c8982 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 164534739 1250 164533489 164533493
    0xf03102301020c0d0519080d09230706270b0304030c0c09090510020f0c150603010621020d02060d0603031e020f060601180e010b18030f0304050d0804030b04050c030d0507 75
    0x103c400c0000300c4880c4c0400107604104201c401801d45200d1040d5503010840c410032802c00c0750398a800d82d210405010895034220100ae07001007294400d65000d51201c0002e2040882d588a4588600c1d010020704441610b011420f000c43c003004601582c0070765542000042d16080240800925030301c00c500c00b51420300703c00000b8001203036550307045500c5400140c0380c850320b0780f900d519807040220030580b0780600000100317002c02c0c0700d52a9010f1f603010383c003c115040d1030b8203c01030f071026a030000c0d41c10100e4100b401c4005107000110340c454039202421003420f040124a194050300c0083d04100c2c0890715070b0254510a400003401150008040d10003095811030260000b0703161540035002c0c90400100c40b00404d00d60441c0c0a075280140514000103109607554099400240c1004504084d008903101d110f140c5450001240e00c1c591250501442c5000d103490200305c00245014000c0316560014032000020408a03c1010f1003240640090120348179a98105070405005040d80414041e09001000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 164535989 1250 164534739 164534743
    0x2030412030503070c02030a03030504030305090f0a0b07030e07060302030103050c0114070b0a0204051c02040b01020c0a060804050c0405070201090302010b04050118020705030412051606090303050f03102301020c0d05 95
    0x1855a4060500c0b5a41e900d42c00000c0b1190171710140041d40520407148035070101039140d8030552045011359810045070304d07150041501c5181410360328249500c1100044003291076041120741100e080d080005140e40c5540c40142004595440756000ca50302000400501805024022030901c1c01d107031442202052110340d2085005604000c1c20200c440d03800645145026811034000c2c000083c408040b43c82c0c00100010102e000f04802c0340541d00f0305802c5a10707540005800344a1040003071461440e941010002c80300c101d002003058410740305080750a40c81c0c3e02c0e03030711500f801081503138004281950f003424040d003528103103058540520b250100412001c06808041680c00c201c0060250782e82a590034a1490350180d5003250000740d103d400c8520401100140c80b010042d244241c1e01c046607650102030303820040764440035010840402003503407041803400040d5400207203d40e1011446450703084a031040c10702c211140003040260039001d2615a010409c5850300d41c012181d0b030004089580e6841c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 164537239 1250 164535989 164536019
    0x40b040b090406320915090705071209030317010e0604150e010b030f0a0515060901170a0c0908070510030b0a1a030105011205090703110a0b18030607020304 69
    0x40001022072202840c0c1e80302e400ca07100800e40500340c0e94845558400844449074140440420701d01040b02d0302d141c504000008910409449071580480307508041407154000004000c48100302c0c00300a0b40f40001c001c1c0a4121940140b680d62500c110704503d00900140c10413007001c0d079a0b0510400400069504480e0103034030203010b03100451400c0701450303030141145a5812141f049040c03c000804e0b0780c802000a54419010f101105980e5107030500140c00312441a0380305c40e0540e5041d038510382c4e40c4c204100104001501032401e1484000070780c604240400d03059411848080d02da039000c0c59140d07400304160001d014100d000d449124641400103128800c40c1580b070050603180e04030b02d651507440e040440c0092201421040c8440645204403034568424011076001c00c0040b1381c042c0442000e0300c0362922641c1103d0003000070340c2c1952a0800e00041008180c2e51040200b18040387c05042c00d80030342401e1680e4500c0488502c03080e03040500b07003034008001d0b90444d8030602040241c10300c50050300c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 164538489 1250 164537239 164537249
    0x304030606141c080f04170105040314040e041b05040e0f010515090115091206060806010e040803180c1203040311010f020d0e060417150a110906090f0d0318050303040b04 75
    0xc4c2d0740e0303801c81030381d124524040c4d5844541088031400c1c54915206064000f03500c214401c0d5128283d181c044c25500515014900a00424000c4100001c001450103182d00301003005002440392910f5881e0700140c00e568010011031020703080f03010649070b07e4000340102c681040d28071b9124001d01024602003211000b0500c2181e40c01c41245000400080c020b0070124060b2510a904000110395818036801903c01442184170a1080304000180c00c3e2981a03500d003d43da0010480703141d5201d29004a44401302070b01c84205c83c0c001c1c5405914107236074201607240202c0e1880c01850711203107107061080300c2040c1845680e0510221a0055125a40c04180c0d01c0360030000c3e040004002041a0100350540a00d0f00f210101d4100070208049022000502205000e0038850552850b502c000940050f0396590b2140b0b03407500c41c1800249940c0c40c155001d0550088042c102c071003000458070005541d060138050680100722079100c6140b400760385510703200240c03009070020740c82c0518199016015104500c01c2c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 164539739 1250 164538489 164538503
    0xa0f1d0c0603180109030c032a1211250504180803090c090705071506050609040b06390f0a02040515040c020304180612080a110304030606141c 63
    0x80c81c111460f00030885a510b008000700703c181c840e441c0180c60703002d408030306030003107070050a00894100c2c80c002000000391940c481021401c59595a1180d006011402c403020700510403a200c0303881a04011003402041a0042079402e2110344019240403811b5412150245082240009d900c4014061040e440e681c403041c520342e42e5880a004608007040d5280c5c803a40024150107005400e07078404050031070b00c1e000721500c2855000c1413aa0100b1140244a16500258180b0001146160550000c03100c0b50003c0c008624000c40204802d5a5420101c4200401204c03484680b0040c96440c4040500a200300d008002d4082110009036560034000b500a03c160348840014404010704901c05140000240c024001c0d42e036007040194407600a0300841241516000e601d9031000c1c07031401900100c071074041c1c1454400700e15444003a002d900005502e000d0050b504241d8415890400c001c2005601038000041c1c1f0608003c2d85100e203804a031305007840b0f0b0b00100300c00065100c90000002c0310310340c0811 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 164540989 1250 164539739 164539741
    0xf05040503072406030302010b0a0801140a0f020c0616020106050d0804050d11030102030f06040b0f06030c0a05131805071d010e150d05010315090c0905070203040b030a0f1d0c0603 79
    0x154034603ea482d2040c581980c14000004100340e01500185000c0d582120041c103035980f1440c4444c00c035000c0812400c40c0e0222400407400c403001903400382e00c58581c04403001d840c00200071007007071410406480351081001065800c2400590a10822000d003004075500c1d0018451900c0d260740c20300030f038010a482001c80d80019010405208022510018058005d5440e0b2801d06d400103c0e000c0b04071041409241884484112403030b040d0031460050700010070071811500c414042c5162034001400c0c4c4818000100103038902e1703143d18090b410042c4149041d0006420044e08010180c41c006000301c0c051002c09020300c5062444000c00d1100e071002031810300c800c861380380b000502c1100e105203c080d8940c000100414030781000e800c81c42c10382c2d00130f040c4c29035004079044030310040320f51003403010303003000050002840800201e400c0f490708134016204032414152181c43c00345940c3d10a48907e4501c69661000d07045111640c01150a03100441071080160040c070444681c898059185803486010004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 164542239 1250 164540989 164541023
    0x408090102070f060305090d0f1d0a030c0b07060c0203031e0406110d0f0b18161e03050702190206030109020904140a020405090f10031401021b010f0f0504050307 71
    0x82240c00500f40841001c1c8000c4c1c2c1d807080a00102400d0b9000401c41c010340310184a1f05000d140d112000d0803d41c3c0d60f002c548440c8400452250504000603641b1000e0420004040744800804001a140340c46030345a445007945083c20440380c8082c2c00b201503402c00d204100441407100d9801c00840e014189410b0700f9070720f61800c032008005044d1030588001e0007180d5600102130982c814a2a807800cac0f80d0411280300540d040190002e5100034004d02c400c01c0320f001540217907201221040181d81030030521503221040c00755200c8072001c0003e20001a0fa00c1c002c112003643d040100e481140e101242c03110040f0040c1c0c0200380c0720310050061104a50300042e1410186e01d03254041381c0140e200364192620350402ca8103020180d8840d115040c030419801010030040d401c15103400c1d0280c6030000002c080e15265a44102040c4010490700c982c555013030000100e5030000384481c0200481c030000000e90510f04040580440ea8484c0545506920300000c000000f06d00100326090b064202c104451010601 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 164543489 1250 164542239 164542243
    0xb0c06010e0408040e041a0c0a110619020a02070306050403050a0e060a08070f051b06060907140301120201050c1c020f070315090204060b0403060902090c090d0609020310110715140408090102 84
    0x20040d034150850351101003020100c0b200015000010260b55400302b040078680348036a44003c180e500c40c0c8503040001580c0003000056000305482d4400e0700544d6885956500d9400403504119010307404284c00044461846500200004002c0d0f400c4a030303e81000d1030020003c1000f0b00c004c0110050180210b01107112a00070b00c140c8a11140d000114107d104110900e2502c3e01030540703100c3e000e002c034000420007082c010a11040c80c520640511803e5170300c0c10a80710040d00082c5000d038144a02000030281242d0b051020b60b0301186e540d0390808886155001c001d180409001000c1c01a422070340f0301b0b10005050000d0031041d1140e0200200b680886400014001c0800341e00151050b07500203000420003006030080b180003802100c6c1c000550395a83d40d408000e114042d2036991000c3c4803540c5500050b1164071543d241740c0003030100d6a425250114007021100f429021160b82d800c045003040c108841e0140111003110001410b20503c03440400304044401d02900040080c00c012403054a41d91007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 164544739 1250 164543489 164543513
    0xc0503031c0c030b03030708030a0605060d05040201110105150904020609060403030206071803030f20070b0c0105090f0a14031315030b040c0806061c060b0c06010e0408040e04 77
    0x4080d295210418102152010076420315884828101004210298040c0c03040711a02180a00914a0980e85540709a2140e000030407950860750b9420b8041b03030544408014214115161000092a042900005d000118520000840d0380e04110030004080025221000d40035000d07604e16000c4d403110720018525009160201e41c0001d40402c002081c5640011070300d02030785054640c41100f0303103e041b160104801ea03000240c040741c5803842114a180c4502c0080681c09001000c05002c0e6072440e00160a00d82aa40141050480802c007084500703401e03c10f45030008d03c2d400003019680481018036132101d0805401402c00c800010809101007001c2c4200c580800a80c5900403800e501c9449400e195000e400b43d01e0000b03440c06410780101d08186c441c500c148071140c2c451078841d80e00c0c2d134100000c5501a20717804125101d091402034828800c1c0c0a1400a0004458141e444001902d007051038100164040c4001140c03041c00c6c0000310316101e0464080d289d000b00c510203107a0b1682040301000c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 164545989 1250 164544739 164544749
    0x6060904240b0909072d060e0609121b0d0b062106070807111501090b0a030605040605040b061c0602130e160906090602031918090203040b16020a020d0c 67
    0x4803c040207140307800400c191043c1e52031504040d0003000054080c602d0002074040c601112042c4800c20710081d400341d4a01181d0b01c500821140c40c2c0880140490800aa49070341e0110542c1f05034600907980e10740b007da404001d40183c940100e800081e846602140740090320365401410107180000d614007414528000303d208110481c0c03a241007855000744091411100741000881e0000b0200c041d66010a100c5101d4a00202d1200c03940d007442210001020224112a4481c40314800000080c00c86d01660740320301d014000009003803a00f41000d1001d0240240480e02c5103088030100411201e80780052000150060801a1100b086544100e0500584d81080104002c0c4008019102c08012100c126044081d550b154080341d4440084e101201940600030168105004c01100a81640100c0d0760700d002d640b400f0208182c24114004081c1d000d0b130045000c8540000800048c000070b2031042340c000c81444a40e0240c0e000b0391000075124500d1800091040f605114142d060001d0814600050a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 164547239 1250 164545989 164545999
    0x14010e19111203040306050a050408031f08010911090c07050a080a0c08070503090114030601020706050f0415080106030c0503040305030a0203060a08011e1a01020703081e130806060904240b 83
    0x40e44095643d03280c0041c072044400b0b40c1802c00007000c0b240c1f903010302c40c026640079500500356210350f003002000100409094a811f000800000703450b8000b409900c2400340101c00c19016a01640305201800c40700402d890908002000b1040001c0c2000030002c20494024004a8807403511010403650600500b401500c60200816424113101012004144454098840c103404410b410f50201890108540003400360b04484001c000040c02040100003c0e0591a181840c140c1c07205030800c400c0300c1074404c800000c0c50140040c80410741501c40c80c5030030110750030f081d0f00b985020b503030090040c07100806840c80250044040340154407139a9141020b0304566000384991030480d22b20b000510080d5030040031442c20501448040008840c40c00c04070041039020b4422142191944102c6074070044d1715804562811003c2081c1003c030002030f041204004c04101150352510300b44501d42075004d00001d03c00e1120300c0a100c000340d1010300c482c1c1030005a4444110000d101000d4500070050910104c0e00300b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 164548489 1250 164547239 164547259
    0x110c031e100f02090f0406050913060b040c09081207080901050a020109020a060206060a0f050d020f210616080f1603060506030f0906070503070e040b041805010914010e1911 76
    0x112529401800690780103a070044166101402004242c4031580b10303058021240354007040039082b0610401d030f005030140c000400c1c6012000c0c0450120354808001c2ca0005c0c22241c801e22000e1800d1200c190f80c6c440084403103040c03c4442e11111020f01c909410039043c4040028000c040d03500030b4000c1c41180e60028242030415907070b5800070351111000c03146a03100c1d492a102c0810a410084240706c1a620050503c03151809580d0a0040c41c00d0f04001007507002042e009104170b00300f40116000c00340907000b07001c2c09450901994017802c000c2c0b000061018001c8110401c0985003c4020702c540c44001422007140440b150481030b40200b20541140f50494000420054a5060f48900e81c1c01012600201c58841d694000100c80c0350000b52a040001400055851031500c1c0c1900020480301c0000c00000751301c86041001404000c10400440f041e944900142042c0401c90230b802601003400002071044414030f02101c0d403100c4440c1840c0ca80c1c51110400c02080c04004002c01b460440003401c0d000380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 164549739 1250 164548489 164548511
    0x3031501030c1b0b06030606101403060117040302011a0901060c02150d11090a06020609120310050a06031b08060a091a0d2a0f0e070201090b0c0a110c031e10 69
    0xc1c1303000315001402845580045491030030040d00c4a5800700306036880b030380c0b03541550166904a03840075003954108001c2104203203007002445041c5000d2403085c0c0001682c0c0482c00b1014100c500a9543c0510640042c80104851500444800d98840d0704452030004c66003090640300c1d9601601c0340403144645441c5241e120361007482e00030004440103c4003103d00a94078203080340c0d6000115a4099150099154036081d4050307103000e1500039030f220b4003c0340090744920200340031101f00d5109000203600c0700c6803d240c50018042d44403e84105241840791840c00c4000b00320340031000d00c41e0703459050340e030f250704a400c200300500c40304031900040804e00c610f8110300307100c001100e4001c800550342c00c0381d910207040805001418801c9a002e140e61400052500c07401e003940841c01081e020540d500d03080128005103e00e5040d40c0f1030115080e4039070302e900c00c118000b801617448801c4256140d00550320745403144d800141703c1c007006c4c5008980c0e411910b96030081c0c03130600c03d00c0b03d00720304031500341006407030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 164550989 1250 164549739 164549753
    0x105010912260c150f04080910050418020307030f0506100c020301060305120405100e0307060509060d09062301081b01020f030a0804061a0a0524030a050105100203031501030c1b 78
    0x3600009441400c0d0203501c0313178a0401042907082d030700285103510402c0404a0350900000e1200202d9880c00c03c6414281c3e10481d00c00c0002000e513505003030350b40c00420400195054829803200150024080040e071801c20081688004d0302d4050340148800031482c0021035038250040806998400151910f4004e041c000080f00d4100e801450708ca6005000c0026038140305e00c5800c004400018002e04045140c90400c0c0c0b41680100c100d25040b03101003100200c49601c601800c815a881020300043c803803d155845802d8507000044c0880da003405c0310040000440002d070320000d00180360190a050702003140140d14040b000c00c219a02d6001c0481d2070400030b41c1002d10700e840756001d20811b214684803060718071002c00300034092940c402c2501005222900344a05100c4041050103c242c01703070468215500344541040324402d800b42d13141c00061080d800c1010462110000e540025411402d00103510040c860f000c0150b00d0405a4446d0300e14540c500c5886a4040701907446900c0400c400d02d0b090001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 164552239 1250 164550989 164551003
    0x13060801050f09061003080a0309060203090a060f0902030309150702090412031a01020d0818100e0c1005040e22030309020f03160b03180111030f0105010912260c 71
    0x124440c1041d000903c0084010666900c00c44a41d00501c44070342c299601c80c101c035040103408104065442c4140070000380305100540c01000b181000b0702c5590040e142c900e0680c0d041d40e50707503000c01d802c1c9448000162800410b41d545400d0440e070790317a05401c0d61000c04285010f0800007039889103507203083c441400940103407420620400e80c1c0510048500c03602c2000c11406040c0702d240180c0c0300d800780a0819116079000f07900007016004040c0500d40c115002413900759900811103100b5079940510b00303012000c002c1858401c0003038a040080c4594108003038424007036841a01c1e01c0f4602c03178000072015000086044800360f0454100391042182d0304004000b8810008224084c005081802e0300ca45400201102d485070070140701401c1c141081d21100050304040c00303403809601d07445100d07040b1400a024400700d07a082507941c02d4a03403800364041c029401060b4052414042c903508c060180c800390f1503040f010303250040307c0c1d000c0c52800d84442840641c04045a0300001c1004200404828008103200f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 164553489 1250 164552239 164552251
    0x50703030605060a12051e011d090606030d05160503030a0f0f14070c03030905070b030f010b03010b0405010305041e05060105010e01031406220c021c0219111306080105 74
    0x1c2044548480611880d4411301d405000851307401c01400300000100c1d04141d0303021174440d4103220714001c42402a006a142a040060b1802e40a0500c080c90107100d5200c503032100d81e801c004c083d1400d011003c0f1b901c0d0070f224036010080000c0000c0303400c4211403400c00444050342c840104d80c0d40e45403c22420006245608082d04150b00303040461078082c03103074002c0c8200088092440305954030340fa0001d5507201440ea03011003c3c9a00c80070400089001402900b005141e0081d603503030382c0e00d0b100c6002e2103120b0b0140c00118031054140010311402c8441e02c00c0c0c4080e201c0078200010b59484600300038421200d21155281880c602c3c8441104024002c40d10b14101c880c00e0300c42c01c00d12441c440056043c0c4d00600007211030b241d41c4000180c610310b07010304040301007056030a054a07200880e2280b4400c0e62020b031050f01c050fa00c03d12503051041d05409031804072505910103840c1310307803480302d041d8001000600c019000403070503481c42d8203d0b5100d01040035900705840041240c15500c071a018040c100c00c480c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 164554739 1250 164553489 164553491
    0x705031309060e070e0609030c061824070303150b1317120720030607170c0316030507050c100e060f0c0406110c061602090711070e0901091205070303 66
    0x40060b5041c1c0d50400d0a029002c4c54036402a02d644503814800c00d900001006540741c071840d900c02c0702e140c80314802003410b5070340780020012061490381800101000103d00c090030202c1d1700f00301c60203001d07880142c1c0c05039541131030003240580021498506a140c1d540052014000001c0e200c203051150758900004c8603001c181d803420585580c00402e8407035240500c04080070740100300d250b00146103c190442680304518852002d204030101003440d124044540c0340100321010000c0d007286a003000050781c444480181c02d03145103003c100c2d03009201d501c81000010b143d22540030171101ca01030829100d6908507001190010442a0f4081d40a4444244042880d005500c040784e00c81c8c8206044911800001da240e0345030615158080b11b04010162850034140200105d1001e5952203100400072000340341401c6041031114010080c200d20089c3c0010207004031040c0616280741c012402c2c004aa1340035020541c5540c4050080d8003415504100030003c1c103180301e8441085412401a1105d1070017650 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 164555989 1250 164554739 164554751
    0x91c050106060e0d020f04020d1409060a0603080f070c050303030702031e0406051b0c04021201240e0f0a09020f0322030203160204021b0d0e030304050a1a0705031309 73
    0x100c02c0e01c019a641040b02c0d00100c480013000c02500708600b03425001c0101403c0140f80c444000b030380c58101e600560251484180c90014403460600401415400001900c4204141403540d0369140161003102280d400710304011170700e1000e000840304440014600541603e41e031340303042e01c030094903580240d020030203800e130b58404030290107141c40555094610585401d0301e001070001c940109031041030b0356600548140f416010803134480d03002804002222110140d5954106464100340c00c01090b880c00b14180aa415074025640c44408a03074400d02c10b40e106c0d00001b07900d0740402d200c140f40780c012000039400041d54580c25510100114441d01c510303d540200c1c1c030461144000d032a0011b43c4050010385c801d1000080c0b54070381507900c901e202e1008100500e00b1450004801080030030700c1001c0141d4005880304914950014801000f840e000c5002e14035050074200001c52003445401136611000001c40c000c0340c1c41300410300311004a40c115085a48960002c8045200c1850900070100401c3c107081c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 164557239 1250 164555989 164555999
    0x905011b02010e0d11060402010804080c071202090601020c01090504050915040f0606060915030507030e0a0303061415070609060207020a0e040302070e0702030a212309030703020a1106091c050106 86
    0x208a00503405d6650700a82883d85990b00112900303207000d041034807108400c20842481d803208100340300003400c80480b01400819203004000f4412001019141950089241031807181e0340f00c400a81511000c403000205a15005400b5140413214040c00890750002400d20003480211500c90503a20311840080c0070345c41c2c0711101103582e20700b03e10039408a030440c4480a04250701a40107141e20089501c0c0c0080c503200380401e2640b41000700c0d2011303008280e42c4d690600085030a030000d03c40c012004ea501070f0300c80c4c0052900e0307505c921813031401401c5035580e0420401001550b404a84290b500181050326081e10740c3c4491100c4a0250303000c601601ca02140042d010428900c076070b01c40c84060700078608128684038152416011180c20554000c802458240c4100841c8910390a030780c0c4040032030701d001c0710080840c80280f4026103240b41540c800c0c082031000a0780000d151248079130000c022680c0042c0078001c143e540c019007400551103500d50040340c62105096101840e076030b025000911800d50b0354 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 164558489 1250 164557239 164557247
    0xf0f0c120c0c1707031e080a0b1e060708090d05061501020c0604120309030804060512090a0209070c061107080901080a14010b0c03120a0209011103030105130905011b02010e0d 77
    0x140000d20000f4031903209140707000f102016141c82400ba08101440d158440500c00740b0121030f064200c0030034521814006451414032a82d0800c12003602e5114050901000c03103248170203d843c1543c4a20b0001031000100f08076401075400c50000689980754582d86032621a85442049421006240000e000918950310006005070042c101414007842e29041c0b1422410000203000d05500f8070188050010004000200400081000b91764190320341801d007509443c049005065400b0a80c00070307505501581d02c46210642010050624003490b100624000001c1c01100680c000c00d1107000c5900c1050002c00001003920311001d13621540141d0354150701a01f03c429441013021211804d200601c0000c1071540245000032500081341e00340040d641d158055014211215a0704c60780104c0c801aa85d43c1003000c0c141701900d03030400f0710304540c18100031a210245c51900341c04081d84401c04541130110a5001300c500000903004d440c01b42d0b0040380f0282c0603182c200300d003062070712030400b529500d0f40c81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 164559739 1250 164558489 164558507
    0x20f06040c0b28090807080304050a090507022404151b051809090708070b071e030c0b100512030f0403080c2a0103140106120f0f0c120c 60
    0x210a50090794035080105034034542d0003072420107603030800c0240b125105000303800d8400481c3e056543e980b6611810a1505410008541d0241c030b902d41c0180014465956000140400d6030000c01002405580f0400120710f050070b03490555084c13030341407502c012100780a40c0c07110344500d001e8a040344c1041d4414a000f01140c22401c445050000450004440c0602c01c0d4000c01740d44400140c85942682d01308000b0300c62900580f925089580142410006c0308820b110000052100c0d60185040060944039220001001c0f041440e4440c8410083c1c0105130003204c85500681d0082030120640c5080c2c6148020942c09025a0744503901075001340c40303501000011140300c20012050207041510310b42d140c400725046401c07006810b029500000000c80098201c030040440b0500d044200700c805000094205c4817044003500c3c0400d404401800100d400156101c01208803110010302a4146080c20000341221000c044800703040c02c40002030103600000682003010b006a003040002403005e004d443d5110303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 164560989 1250 164559739 164559743
    0x4030b010f12060504060b12100507030b030a12051207030b0a0503070b041202060c0d020703140703030e01050c100203070504031109010609050603040501060506041205160f05040c050d0c0c0201020f0604 89
    0x8042c8405600080c16034201a400c00e2080c0804241c20104c800012900300b1142c12005440d071014031046940c0b034240c052190803803110f0404001390040c42010985810345c1079400f80120350804440321011740325000b00c80c1014012000d507402030801c4c800090242039807158035407240780c80c4c28001c0303039516001c1081c400b2034075020032007490503260058076141e401c885403060381c1c00003041c001d001d01d550f824041000c46001a5010303248607815490100e9000c0c01d07030f03944200540d00c1040113200094000e452500890401d0030000c0e2a1283d500d40e0901d00b2083c040241c26480c00803040c0070100390441e01a000381c07407081032400001e8460b1030a0199000f400d12440380050074084003005541010b100560300719010760004543d0a440b40d01107005a03001d03030f10402540603402c10340310501006010f056400d001074003c0c41070291500085000c03001e02400340c280300326511204002d026018404583c4034501009051128115580000e49007240040040c0c0c050f01404010080e180701c00306030703c3e04c219 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 164562239 1250 164560989 164561009
    0x901020c030c0102210c0f03030402030d0e0f091306060f0f0905240d080403080a26070e03070e13030311030c0d090204060902070b04051009020303030f0a09020603010303020304030b010f 82
    0xc1d42d44400c0321440d21000704030220749904221061b40850b00f80151112540d450004517640d06080c81410703c0d2014410040c4104030407821170001c43d0361866910b0044503400c403880180350301c900d0f100c1c0c0b0f00f401551000402c2c051410b40300164078402500342c20b08556414081d0044241d4641c2d04005845040b10f52000000301e901c0550a20141580760580760312002d0719001450810303070703611501307a0701c650030680b40e1520104003107180c154800c4110060505218110040e60100d443d464003859001d009441800700031a40e000e80e03a00d08000a40042002018648503400c04030713001100f16454810980010341800134a06074140c10204403400380c98000c2c5403038a005901d015800082c058044126030007601c54100003100701032030003c0c042490040c0e184c01c0c4a400d1034900240381842c00d40200c840c03a82850292405030743d0210580707610150301924503d0359503440640100500203208025031100005c00040b09265000002c0c0c8140c900c12082620b1a98880b46140c0c480c81c07991042c3c070340e44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 164563489 1250 164562239 164562253
    0x905010f0c0618120201200a080703050411190801051003170c150c0c0c03070617040804030203070b13060e090c0c0c04020d02090103050a05071b03091a0901020c030c0102 75
    0x9040740e001ca0790a00000030a00d01c80343c4140e03158107414006142e050010b07034540d5901c42a12010354042c10f4131440f0b00b01b210345400791159001d800a800204420107250b61940010107205591b8006180355100502c09249800010410700c0300c00a680281c1c2001c0d03181400290001c652481201e003569086085090000d1605039a001c207584048203d001d0b034050b1030070a0f10106008440513005a402c0c424454442200200c290b1410181500e658403903802410200607240d0880ca4600280c03003c0c500c003040598980c01c10800c5072199600007901403156810004241c681c19000c0e20021710142201c441180d9105401c5604105c1c4800d107560210381e030000300d510b5030084401029005d90200a8440810810001500720b8000d401800071094000904559a6a05106455122480020406c840e060002000709401d6105210030300014030415554149401540c1000040610003014883c02d04403207030050f1150402e00805025228a00d58951103140100b030700b8041c8441a4001d0040b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 164564739 1250 164563489 164563493
    0xc05040b0609150c030d0c1101060e011202010201020f040e01030b09010504021302071a07050406110105010b0a050a05120a0f0506032103060d02060309010501030b0c071203020702010e19060905010f0c 88
    0x400d0030604180283c0842c1004400100c41050018040310041800001542108600050009102600c11561036450540b0500043c80c07010329060640e401644284203c1c40c003440140e00a00c00c02d0152080484007040024000c04440520741c10f1b80d02c5210001e91946078442081d003070b03c1c0b054400039403000304464000742c03500c0d25a01034a5043d01501308245014102100c101c00580107450810000320006030a21825170401916549038010324003c11880d0325010301da1080780500c506543c1000b0b00002c600001901c10350030ba51045205841003400e42c14441c034100028140d009140d28500d0a0030001112460007140001860014124080907461112000711103548010440d44d44154854480c6000d1385400018502c12104580002403a5045041c00210b140000300340010180e8200304030700004558081c0001c080005040140e1900c0c0d580c80140c9091407000c84d40f03504040030090680444203542009401c0b1185a102c800b80142c44000445100054003012804074009002c13102c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 164565989 1250 164564739 164564749
    0xc03010e0f03181503090f0d09060e06030703020f0319200909180106080303040b010e0103030507121205042004021e090a030b07020d0201061e0e09280c05040b0609 72
    0x540c0401050b1403c513048610400c10650001e94940c0601e52200e82203481030365041005403440082401c2a003801c070714165004201c1060861584d0007040d011020074004e600a80503900940b01000603941c40e850403c1941d040b03c1050b0680c034020904080d200554068000c0203020740801054509107070049540900c080d000c0040d015801d03580c100c09200c0c00c5a0707800c2c8100c1d00130307221030b802071941d034181b6051500341240b068219003e102540001080041c0c1c01000b02d480702075006100c04014281c2c01c80c01d940d5a2038164400c0074550034041003004000b01131020880d880600d10303a840784091102c2c24002203000d5000c0e030000740c00ca890341404900080b00c010f01424440103101e00309854596030380200c08101561040c0241e8426502170400940a0190f070015100006400d81468040c100502c030b105407511920b0003a11180010070001da4007440300074540071410340364601e00c007a13400348201c1505c0c002e10f00307407906040484c01160034074180c06404005807004140d503081840d00700801c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 164567239 1250 164565989 164566027
    0x21c050901030c020a080f121014090c250204050a1a12010609020a0801080706030b031203090f16080c030703020325030b0a06031e0b011401020309030105090c03010e0f03 75
    0x8015485452400000115194010800a20540d491980307411605a5074501c00ca070281c00b115601c60003450900038030851003240703425a001100c0be010161203415184810748150003035136990381c900404c9007505100b4044060f0744207100340c9007009142e441108520803503041d484943d0030300c0c044902000561821342d00c5c100f180b45c07500e0000112103680d40400c400700d80c0301004c100041b44640c0c004002e00d0b101846407000800303850038144140407801c000262184500303981240c0c0302074003002040058608019190200081c1d0040300c41040c080107121408040c00d1095040354072030b6117400519801d011480808607940640104805002d14528080303101c0c803c801e038003803992403140020100c3c02000e07520380502e003400000501942541008103010052a04490300303400f0b44081c420000c0c1d5203145444c1114800b1205920282006c40100e0030f5100e50000c596056003840144841200301090042540310218009c0000c40000c0c000c0e00d0315030780c405412403001e810a10141055800101d144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 164568345 1106 164567239 164567261
    0xf0105031e0309010c11100e040f06270e2b030221090c040f0e0610030201050406030209030c04060306020a09062c0d0605090d021c05090103 62
    0x10302d940c2d1140034042410025052401010b000c409020881c800000510301c8045002c80100103024400c8030a8140c0b10714580201c05050300708911800e0300300c854200b8101c040b03a00701c800c6c500141d603a140b000816180c990349800c020030303003c0c444094403c12803140444044104800e4918202c40703221180141481081202910050b80c0000030200700441e159034090344d1040c850504100c80303103034117a800509102060034010fa03d82c02102d004825101200c8142d6141303505106aa80c01d0f200203400700780204402d0101601c62f400420941030050225000d048440c8081005c950403907100b590008d40c04113120701140d50101f600001422585407001c03030418500300c43c030515141300c1c507854078501c010a2000704a440703010319610081e800c01020421031410342580d0b0740740c1100a8008005002c0c964040080704250f69484140d03410313540e151070418001c0c0c1d0044d03000707152900c11 = true := by decide +kernel

theorem cover : BRFrame.Cov 164388489 164568345 := by
  have h0 := BRFrame.cov_init 164388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 164388489 ≤ n) (h2 : n < 164568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
