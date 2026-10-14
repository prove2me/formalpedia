-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0502
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:08:14.544884+00:00
-- url     : https://prove2.me/submissions/2fb77fe7-75d9-4ea7-bb87-52ffc323823d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 90107914 ≤ n < 90287770 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 90109164 1250 90107914 90107929
    0x6020d050c010e151f0f150c02120c0406090e06040807080c030310050f0f01051801030b0315090d0f021e160f061211090d03120903030209101b170702 66
    0x10004031070a018060090711030503441035001701100011445c004506088100e0801c00c01e61241e4450000741c4860565040e1144900e108440d0f8010301c02c1280f5507003141c1c0a60f440d200e00c2c401c01d10036490007500040a00140c8915010100c3c02c4016044560340e41e02c0d02c071141d41200d50255668601040b0b0744001a03030900040d40700d9044424241ca0361030910702404002002c8910160081d1850703a0032060300d0380c000307060f10388030f0042c0351242541c2e201e40d4004034090704c4143e032400c1c1c15118030224000350356800303c29540b040d05028200c3d0060038018000b220303114009041d00c1d02507040356001d41842904540100c0d99130082da011541f05a80c12000c00ca16100146d1104040300402142070100306e82c171181610303140c42082d0341401358040d0380d410180070b8410510001e1007101c64454007010140515500440400d80c92010041c42017a41405801385d0b12280e8441d218004000c1030300720682c0680468141120000c1550403031003410b546505016103510303a044203608c41401103600591b102403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 90110414 1250 90109164 90109183
    0x3030e1f0305041203020306090105040b03010204090204080d020609070b030609071106041506060e010e0603070e280e0f0a050709320103060302030a0b070c140c01080903030106020d050c010e 84
    0x40d4001510300c0d00e41004d44022400741404001c0600400c24000103aa03020080d90650b0411180058a800d4800c0060b00a104943c040c028040c0003040010f070f0410003154015802d0781540130344449036500c12105407540300340c0c040c1d00012207050000c02d0090400c444103a0703100c0c03031509000b81c004034034401c403924100b001c880440d24540f502c0c002048410860180708010b00c80e83c1000d903507800ba540000313048080030500702400790001100003819144a041110f4010501034219600e524003800ca003250001c02005050030001070700c00014007102072280c1e07148107401c1147e5442080d120b481407031010706006003060302000f040f0b4102040f44001d40d92020340c264805402c1089040031400401001c100040b100340c149071402e1810000761300c02041103000e0030340c0020265480d0352504016158803480c6080548031111880c1000402c05000a1000700c0c0202605c94a0241d0780c0c040d1199900c0c4002d00413040103800c0980e8141c030050041000d00b198121090000c0303120610b09501e14a000c0b081e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 90111664 1250 90110414 90110417
    0x3020d080a060e041b0e01050a2702071a090a03050a110703080406050403061512120203070b151e131e15060906021605010f03021e0910020606030703030e1f 69
    0x283c5e4101c1014805a8400c0107108241140c0520743c901b400042c0250002e11910300c0100b0242904a5086c01e06c226030160305601100464031271441d402e00301c0140135050202071528440034041417100030001a045c08060341580d51519200d1000002c80d98000d880302040c806100740781021000a16040160010748031599615031554030b0750829409a40039101d0651072000382d02400d10108031071a80c5040840d800c00044e050301c004032081245184a485c402820000f440700601034103051407401d083d16150103c0b451204c148032500144502e4518812407a803003004c414821261102075004603121411242517040051820f240400035590440b0716400d082c1c002d064140710654000a46c43c01034401032000b48111818a070300c540301d61000d030092906005888000e08402c2d442501151302020b0383c880562000204940b21403525000346065074416507032221840c108a1001403041e00c034040c01801040002c0c80c68400b07403010328807866400d402440101c0c00000c0c41004101040c1111602d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 90112914 1250 90111664 90111683
    0x3060405030904150305030d1e050a1a1c02090a090506090304060305090f071802070203030705070305010501050415090b010e09070c0c05060708030601030e010e01061409011203020d080a060e04 85
    0x42e58100012581e203004040307601e00ca0301e9814804160f0001c2a294030300c200141c001918000025180404107644000112150800c01000074000c0103802c102d15110480c41000000140c0c14100050118a2086160b440720607040300809454441d080c540c0000d01c1e040e0000d0ba400b9140c880c907090140403107800344c203907000080810006a15218042d40b0070022805001c929424890341c40e11180c507403090481a0841e91104500300c241541200c458550040c112aa01c10203403a0a81d00c0709000d10080d500b951800c0d000003901d0400e402002c01c000306450340c064400d810200084004d081854107107041002d00e182e00091501c2e0401c18500490440d110b9441e0040b031480c003c000d4880c603411442c0243c4040c041a80042c10200c02e0341e81014090a010408000001806d801400f005104071038075800c00000003070341900d0f8441034440c045c096403900381981e200c0000c183e4403a0351803402070040e80415400110035115482140c1c0010303002102051803503464200541078101a1815202c1b60302c2c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 90114164 1250 90112914 90112927
    0xa0b16050c0d0503070f050106150804061508030a0513030204092f06030402100c080414030601080106060c0b07050c010c0806040b0307140d0309080601240512070c020f0306040503 79
    0x808102500041600310780d007554104250f0340b41500c07401940320013895408114007000c00c2002c01e402c410054021500222020348180e00020300303e01e01510207440c0e50b89000c2d620700400001c4c3d0050740c1074900a0004614160100e6000c441503408002c0103400b10311a00301c0400141e80758003034880d420340a903200c0001031490000e961913980b0760758814080c0300100c60100c09140c507910260b90b80f09804035042214034078150000d4840030720712100100b82442c0003c000c10100c40b1075141d00507280c001c1d4101d4105a8940304107a003203458601413480401c40008500000511144405e0f034800d0042c0b8005080c40c0d405007031340d400d40c1e2080e80e035040171850a404015840c03c10b80301d500d0001c041200148119031401c1002512120300489460060742087c024900741400bc6038064020b2814200700d9849603542c11110483c1200386150202450038a00c5c841c0820b40b16900740e400f044003d8898407090b49440c031060312000e0fa1a1803c81e0000c0340040b8140982d0b4050241038415800341000d55034452 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 90115414 1250 90114164 90114173
    0x6030209010905060d02060a0201020c0607030c0f020304031a060105071407140d0210050c1e01060e01060203130605070c08010f06030618080409020d02070f050c01030507030605030307110a0b16 85
    0x501608a03000c0d240c508010009030396140c4001406446c3c0680e4100e640c1e540c1254101d01a2060000150343d40c4680d209010046605074014103d5400c03550340c00e2849040c070740e0300300d85a02c00c0e840090101c04400c0740d4042000d4007884078541110301418501e181504950716006d190740c40685511090f0840e034020044914848090760840000300d5900d0102105980040c1c4840b1403c1030040c00c004011601c6d070351500c010091940007606d403504054444c03880340136450181645010342c0e5804450700d000061100d000109945281c0d280103e00c1d0400d9007482c40441c0c05400554007030b940b0804036140000c0d01d4000388961400c03020820301c0496501d0a50404e24252156510300d990782c200c4298400c8080f441c020b0548050700c0307003001c000d641d620304100c0b440d010f4010030a015040c1030320740c14104204900001d1200e1510003c0c0ca0503c0b1955882c1010b0b02203400f50301c14150590010000d402c0024104d1030155140c60707005040e250403540b2070740000b0380d0343c01c0000c80325540d1040d4a8000d0a00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 90116664 1250 90115414 90115429
    0x30f070306050a050601120b0105040b0d05160f020706030c0c06021b060603030a09060c060902100807030506030705090c070507080303181005090a080f0903100903080a090309060c05010b060a03060302 88
    0x1001001c000e110a013000c000017000c1c1000040c8a00c101f0740d48a20010050307120b0f03821580100f03a040300c4035850f10b040c4c0341204000c120a960b20450b22941100b042e007004c0c011400500c95000b1a0081c00b0017a03c1d0080a030b0140020201c50300410140740c000e81c0c0011640e1014110a104980f0003c100c0742d4241070882ca000c00c00303030405100340e01c00d00c991030510b540009010203035046481c00c8d42d2980b1240c034280014011040303000758440c680c4e0700a003283ca40c0c03002041d0302c01c8026603028001507c0300c005040e100c41990244903080b816a800190b9101d40c210008e16219110f03a049541c4155200384281c1150000c0d02d80311203aa09200c64446486410403051460b140e0701c6401304241e00b017000380a03682d4040e400005005040105005c8086400350023580c8010038041d050712004441450200c0091005020440100382d800002c1078100281d4443d00002641c585c5078094458200360060b43c03040790102e800c80d40380d0349a0016000646800c4050a003250703032602c0100708203007144104183c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 90117914 1250 90116664 90116671
    0x30b0a09050d11100c1202070302030a09061407110d050106030b090d03020c0601090c0c050a05070501080a0216020118121101020609120712110d090f12170c010605030f07030605 78
    0x204034049803e034a8021000c5450400e29989110008000705d0304d010a803046201e802e500b050080c4003107a14800d140c1c02000403c4120380c0c6580305014181c890744140c034501201007030302003000014840c4000040f0704054450b400c070001803603a03600354055034425085d02c03040d40080f03466100450034065006410085100e43c0b03900303030506604161341c800e04103599200510948a00340e4440c2104000e01d40549022502c4c0d60304841501d80c0b440d01402c00a580d1501d600c58a40025440300009141d480b1910030340e401c807541c45035200243d865903001142e03041201071440b0076520003400e00152102681c00a42d21042c030401040c0e41d028480400a410030000402101c61600a9017043e4540c95030714044603180c076130140d80c400c000c284e002022030340c8415540c80d440b00e6114424412000a401c4042c660456201184080703400e070b201c0594013201c9130303410740050201c0724550240c89036840707807400b61071881c01e040000100c40d80d440c800203103096501441c480d03068100d41410302c00e1000c070b0b00542d42d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 90119164 1250 90117914 90117917
    0x1b05010605010e0f1e0d1b0e1012030e010302040b0c01090b0603071208030405150a052a04050f030a1e03020d03050c090108040302070503010e030d231807030b0a09050d 74
    0x189084c2001c122039451150408140b00300d03001e00c40000c0c1d0ba032940c2d1030b40c4c0b01c0d8012104000e034030030b00211400c0c2d180050094420000205c1c0010b0040c11070a6017407c00c2d5000d40210702c0d4100034956055441e50320a44d540c506240d000d1102090134030308200078110800c2d5441c00418410f00f1810416008070703010300610300903000710005102e05048452485a25540700c6800c0e80d80b55141c0c20801e00300880080c8400d5080d8001050100c0c640e019005240901f0107612010001603105005401d60140c40c0a074000043d0b05000400c46032400c10361016060300d0180550301c051740d06584104c03c00b000c27810590350750f2805034228401d040e4100820401540309040070040d0382001d41c1e07105000d01440342000c1c108200000011708152090103100000c103000381c000d0201c80200f144654880d004141c0c1000c441340f6002d00300c1200e08a40d0740b2025a941c12003000d04042c0c55400001e10411046c4140c0310f03c0e845442d10020020f6201032041c1c0c880c0c03068410002350100e0302e240142c01e160f0303506034400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 90120414 1250 90119164 90119179
    0x40f0f0614031203070c02092701140a09080d0f091e0312020d0e060708160914270a0b040c05122406030103060c082d071b05010605010e 60
    0x401e251000039800302c14450042e68140c880d0780d5410219114041e5010080d0001c0b0380c1e10a200860b003a01040030001c18105075280c00000d46120818200d41d0390701d2200d1100c2c50408003281c210740540c0c2c000c9483e940101603140c504820783c007070750f001c1c0c9040000b4180015030340d0040800b88812035016080c40441c10400c84030102c215140101440404280c070746240f41e000491229035800c5502c001c881e840c0180584146140910020705048000c881804440b104400e044110341d2045900109403110400540f1000d0314603024401e82d21203005844115002c1100c07400008043c4852041c8205109000402c05160f410706100545682210030300030b008060154440c0c0d85100501240e002d1a04441c0d450301150301e15042c441c0307801c00c0450740e410000010022003480840e0704549180011600c50950540b120040004c2141111b4500b0f020800841c9445100c60000c03d0725a4200c011450b002404c1024040d03181581031039014100c80c90381d929a401c10203960094801010f0410864650 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 90121664 1250 90120414 90120449
    0x61103010503061803030408091c030e04150302091506070507080f0705040608100f15090504050c1203030403050f04090e160e010609030f0c09020c0f070b030402150a0905040f0f06 79
    0x89030b0306e00001d40010314210001c501030100f41c80b1a1004640b0b800000f4019403d196070b4240070700820b90f281c0f5228080e608199a0f00d501e140c02034084000c480c1e001e0009112507030750b110a1088802c11000d09035001404114603000b184c010458400135040074000b410320002c0c01007026260910507403150740a0340c106101001000c2000c1001c4080041a400101e400c000c4500c0000090413800240300d038036811000003007102d48160340028460f6100343d0032241800d4a1000700640003044a000c485241d000b000002c00180c4104042e01c0c100155210060403d501c44004a0075242c1c142d003001d0690740581b0000303405030300d0f40c1d400d00001c00c1041442c81055040c604000d10b0039002e8040940444006040001003040d03a061040003005100d108645420304040d0542d02c40e4a010182c0c80c2c2449640c4010450407c02e40c11680159402401501140758030420a40303e904503c0d40707007003400250300c3c0009098a55006000e04031104480008041c40082242030445800e034124100010300c51101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 90122914 1250 90121664 90121711
    0x30501150503060a0b0418051b071202010e011d011401050102100b03070b0d1407050a0f0804050a0c030b010f0807050a060806060708040915080d09050108070c06110301050306 77
    0x103468102052800740d0740c90340c900d4042091a482603014402604c00003a001810104103810345a4191450300d003404291203c5007215060481d03101501e203c90410040600043d00d0115244003a5036980004200d96202d00c01ca44c0c01c40380100c20324115140800085407000c0428803450750007510803e01c3d41215410000002d40c0d50b51103c01c1d4034515640c4844081255500b00b00010052400b04a11b9030b0b00d400d1030070340307001038800c0b1081d981a001013000460032250080042c0c078000c140c2650352908a0216440864281501130000c1c0c6042c0600302c03000020402c00c0030a54091805881c4480c80303545840c51103020b858181c0e10002103900141c0f414000c2d80e903a00103140c200d4505203498000c50b215480003802c54802c0140081190000280c0010034111a4010b20040100840420502070782c400010b074860b030010403d10001680114180800d41c000e204482e0020241c1c50804254521584da000403144503003c8414120b5004c4010041443c1c100465071b813221fa80c08800080380c103071100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 90124164 1250 90122914 90122939
    0x12010b09010c060609020702030d020a030e01080c071e03080a0905060a1104050604030c03060c0c11040c02010e0111030a0c0e0607060509010209060d0c020d1107030212010f2a030501 80
    0x4002508a00290000c0306038401e038030300041180c011030100804d07a40c54098400075404010304034040d0040241c0d6400e11400811010451500358840012121030540111000c01005101041a440a01110012a400312035054903100343d0f41e002840700c00c0c0b50070060070041000b000c1006441c140040301001820124031290080302040c4c004c10994040b4a1010860040303401c201c0c2c008402081c00021b2021604181088a004240402c038aa4540200700c514a9204034090502c00c004107030360480741010360103001e41141b07502c0005041d880354503450b4250303217840098914038407001c401d210005036148200c001c51002401e040f5003a0181c440440c4403805004009013034955200e000480c40d0000390100c4840c8032000380704a40e6400003080e40c000070310080320307460018440c00581800c03050184d0402141c0d81e03502c100800300c0c81d20315030801c074070703080b11000c00d01c1c0c1552201600c1444c88518001c902d400c010821450a813840c1104030314040103a900901306c10582800010860301c840c484 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 90125414 1250 90124164 90124169
    0x180a0602030412020d050d05031602010b0901030201051c050a02090f06160b10120b041505040305040b09030304050613031a04030909050c130602010b0109080309060307050304140303041112031201 86
    0xb05408144003c0e4000a081d040f1001009803190140c1401101110340c0040118841c07a40c0400400c15521014000c90803603802c8242283c0021110f030042c009507004401503d460052921554145d9541149140a0742d80c07d5820111b410707008158203140d883e084100c45034a6506452090626803200c412400078205108040c1802c0043e00124225080988000c000b030020403481102054bc0d81c50400381c84941240e09644542c2e80324101403550b0302d6405884d00803a0190f0700e541c20942420800c40140c0e1010580b1589803000700400503041d00c0e080e0140a800350400f401010301e0380745040401038103800c682c840e42401086810800001e0b0000525010fa4214000008055454283c0496507110325144800390343c0c4107a0000541640c15000031011030000e0343d07100c0c0038030781d940d150540e280114407210354000024800140c1991003140610390250084441070b80c652840d23800e050541e4401e8805450070030b142c004403c480e04012031901c0d003041c0803000a501e8003650b54030b610180f0f80f060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 90126664 1250 90125414 90125429
    0x1020c0103092006070506040f1203051e0702150a0e0d0804080706020706090803040f03110708030706150515030402030c0a0e040f05010f0f06080601050d08030a0e07120305180a06020304 82
    0x3d03105401da2144070035641150340c0001281c03024102810282d02d00b1422a808441101c0d001e2080300300075110b409000e005007074840540000d000114030065048800070591003c501c034002c2e40c64401c1001035051806803508d07a1002409034140e03050903007410400e1103001c041c411040f051200080e0008110fa0302d5a4114030016110006407408501a145505024101e11000301c284024050070044065140e031080c1c0b01d2101162100320490341f14622482040031582042c040c0601003030158000c0100d40b1001c140346001c050316400040d03d002800009258030440110030801141006c02201c80002c80894000c2d030360764641028180b902100a1006185007060662241040000d4000754a1001022020311000104179a020700a200611070000944203000002425003005c0310182c6555410401e901d10b03680e01c00e4200005040200b02c0c08609110310000002d101d50311440404d0802e1107562003d603580c482803007600c3d0400e000d20002e845140c8441c030407c11160000112030465024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 90127914 1250 90126664 90126713
    0x50c0111090301150e070c0c051503090d0918050a09080f0c01060503120901110a140307170702061e070503071a061206150105090301020c0105091603022407140102040501020c010309 80
    0xc41c540484230b500b040e072215820050b05448460a2410f403c05144503038524401c4131042400a581260744143d644504d00248641e09503000b420341040d00000e9100c80ca1010124441d0303070640d07400350507901035607241103035800204607900e02440030701902004001c110010310180380400701c4815a0302c194030301a8140500d800070070850403000d00a100c000b5030000030403416a1191509179880c2c0d802030400700c902425400600c50f6014101080c1d4682d180c0141c112410000000c03050100000301c400822410817081c802800098010001011039a2180301e0529200d031404407480104103001d04800e00c98180300441c441808000911a5808428106001c401017646801600c0703600ca400906501540005403020349641d054109a0103a403989048400310041a48c41c00c8001c5083d01000b0741c40380a5000c8075008140c480351f180d2a016010140c2490030038141d03185d10481d0a991a00e003101c1e500480c0402c07107582c052086503244c040a0030240507407034407942c54003c181d480c8440030460a00703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 90129164 1250 90127914 90127937
    0x7120605090106300b100507080301030b04020d05010509330a0f020d0608010203010e010501110304050f04270201020706180924030b040204110910030c050c0111090301150e07 77
    0xd00c1400074040d83c020418a6100c00e903003840c0b08000c0e182450800d4050007040ba20a080c3e1b605ca181151a841c2d0030450303c500351390840c1d440c000d82440c0940181e902c60a41200000411001c1c030406006140f000001c2c280c1780895520403503c3d030f1807140d00203400c81c0202a2403450f80c041c050340540c40300eaa40e800280812002c1c48c603800038064540c101064600d03101c00440c200c10154001e605070f4443c14550406681d81c0c2e0f0044881d01001c5158107080d030402c0c80b0400441c1440c00704050301140042002c10b411312581d034490506444800b141070711044503c400010b6580601180c07010301120300d405840c000c020480d00030788802c0c500c03411819a50b101c074800c072103c0204000d00d20005403114202280703a07883c20245a81c02c0291001c0e80f0852a1041c00c018100505003168401c00001d090700001540c1000254010180c00c1a1002070107010010000501030032710030a2020341c10070301c0c146d4a0fa403900f000c0c142103808803407000318608400749007400b0404048240035480f48892500720481007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 90130414 1250 90129164 90129197
    0x7030603120818031c05060301111803070e09010f0605030606030d0e0f0a06020f0106060e1e040b04050a0c030f05070905060c1005070503150a1a090f0307080607120605090106 77
    0x70f03140c0c1c084410b54000410882180c0411240140005650510920840d201c600425080b83c00b01d8400c44aa40b000300140c6070040d003101450000800002d09640c0000e58492410007200c00c01caa0b00c02ca2139540300d072070041070002441004061314064008010500c0d00d0b20100c1e9480140f007991000344140c0d0301c4c9050791940ca400d009040d0f2800031f000301c04042e03622140039507141c0c24920481002e500307188004c18560701c90340d505150303202c0c02000003e0a00b181c1c0080070008085c0c0c1142d51f00181c50300ca07001c0c80c6032600d000300343c000c1115810000e102900001c0090450320001b2107114038034100b0080c0b10100b54408065401c0d907004456103030b030380c0c001203003100d01e055124540039040d1400c040401c90348582242c00345d80314407142d108260561600004200d082070f01c501449440131078296032a40416078010180100040103800b45810640f80c400017450500d159110701c40326406602009412544442c1d1840c400c450000c0a000c03540c10040003410804050003a00c08002c0180d01494070717003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 90131664 1250 90130414 90130441
    0x13151d0402130b070303230405060411030a140d030f1a060f13030302010501062010050705070203030c0a140d0203070b07171003020a06020d020601030f020a0e010e01030506070306031208 82
    0x3c0a503040180c1c0c0d108400e00c4d014028101a0040b060194403000320341c40708010f0049940d2045034084041e010594070b66450300b14100700000360f250144611034507003000803040c8d21002da08505080041c0f07071185400d00e0040a032240c3c20402c403c0f05092821198101c1740c5000004035010b07080343c02c2e540303a24410300b115080c4d0080c40300714540320740c01500010034181c0650086050b98074681d81e07514860040704840042e18030040724480580d001718403110301030f81c0c59407010b0780007882c5140840c41d040b840c0d0006860b64220b6184001c09402031001700e030800103000c0c500300104010001505083c444c010000e900c03801a848e0103064410484002101144141d4030104480031407151800d0f1401c201c0c0a08074003a0300389c0006c0f8000c0c400c40d18045400303800014024040e0215a00825803603085039103100004400c49822608119203c1010030280308502c42c4a001c0c10881401c2881503155090140ca81b16016209409140ca808800c2c8041004c11148070015070b8942400c508540360040300c0b40c0365 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 90132914 1250 90131664 90131669
    0x70b0918040804180b090624040311040e01150b03040305071502030a0e0f33010b030415090c050108090a050f0c0906100e01120b040213151d040213 65
    0x4100a00c01048100200c01020744180c5202c100d2400308210011107071800c80781e2502c1c05e0b13039014001a00280c52441c0c5000440c040740132248003450241d1030700c0d05114264000f034004940c400590010090142058030034620741059210003402080d00800400316502400d010340f607446c2d04004002030a1501910071984010360190400030342869946e581c000a420585150142604112503d555010000342e0648004a84d2016207140408501400d8880d0b060f140300c1401e01d0b10041e6403021612900c0400c40c0285000d0704070541e240b034589804003001e441da9240b1a01c80b464018404041050244007106884080c204412240c80703550b42e4a150015100000f4014421450030440020300454204601c42094643c1382203a21880c04002c40c418034182c0c0800001c107401081083c642c4640031078070100300100c0c8001078a19500e00031805076130203080384690f880301c81041040155a84500944d5000051600000042d0406410480642c16201d0148101d4011070002103440700751501000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 90134164 1250 90132914 90132949
    0x315190b13050f060a08060105040c0e030d090303090807080c010804020409050f0309040b2d0d0b0906010512030307020703083a2706090c0e071d0d0302070b09 70
    0x650089031400704007412049600307920780c00c0500040354040c144400034100b030301c4500c8042d180d01c0c1c1c24030062200501d20256603c0070800c6c46425014035403028003541c1001030031075644469160640c1400340411183e82d201003111b03440030400304920403000c40c0c0d4280080007403030100007a480324000a000b400844034082c1c401d004d40213800c52018800002090300c6d40068038148010b500080c2003246a040c0c20010a40c2120f0403013040c1c1c400a00a82c844450035030060001d0703e03100d02501c45010f0740350200e4211405074016001400340c0d10702003c0341c0216102d040011880d6183c0200c00949501c01c03441300419200d4007040c640340014900c3c400c030b801c4884500b102e00c20001e01000c003103049003040300480906480c202ca8610344d0b03040349018284613102071035040c8181c4440d54400d0700074910090183d800401c13b42005c01d982c3e03001d0304600d029040030360b599114070807040c1204040e200c01a014600c10250000c0c40c90000c3d401086801c2150041e200868075940d100c0049182d42004200c07401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 90135414 1250 90134164 90134179
    0x221010f050a060603020901020c0d0c0e090f16050d0b18030f0d0f050106270b0a020a02040c1d0111030d090c0306060501031a10020708010203130b060315190b 70
    0x30600d0a080e40098400c401e021010f015440e07850381c00760120300c109644140140c012940d4908103003090240540181c0c400d401d200c46059981055070f03004141914401080e80121726021000c0d901080745054410070500301520051401000070a09540c403a002080314009000007501c51646019480c0e000401c00c080c0c981e51502040807000940c0148070f032841c0a450118003586108040c0324640c103070799803500c4a0b0741185030b40b0346010355184400320001c10724407452000700f140c08504026001c4824141c00810815925204000c16901d0200c42401082401c43e0448040c0f80300d24008921094207003008846110800102815882003032000900f06007003a032090100a10110104200c038001e0604100454944004400340c607540405522010001a40c0341c159251125030b150355103445004444640b41da03846c02e2420ba0308100c42c04600d00c08501e2a07a0309201d1220405544a6012400340480342d05a08252041d04400340580310a20f0340c0c5000300310002c07402e80c03110080303000042418 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 90136664 1250 90135414 90135431
    0xf0f02030702010606080906310f06020901030f0516030b06040f0b0a08070f02070b091306061211070206070b06150301030c03030e01020c0a0e09030403080f041d0c07022101 76
    0xc1d0291100307200d52400201b0220014074401004241d0300d014800c0f03009075040004803401140c00801c8400b00349240c0703c28404091000500399602045c1842c42481c0c05600e40081c00000340840b03c0c0034a804281c0c0341428104a9401c090354101c0229800600f0300041544200b00441d0b00c0d070007035802034489175010341004130301c42c01c90a001d009546180d981d11051551a90411280380c0560b9001d207000d41d020b00418402007240303c01802030440054505103480d0790580c1c00320141c1d50243d01c8400400d11020346414020441d000e01100c0480490f04a482c1080a6010917a50b100c0e0b4030018040081201c04107003190344040041d54800c101ca09260b071256102e04260302c01002c2440308a011500c00c5c10507259550020440c11085000104090a202c0c81c000004000d040004c2101070203020030400440000d800d90060712200c250700010f103440b030742045036225607000c0e88401c0c0b07014040000e003048a11312a50382296806035043c0d40d43c001080103101c12908001d0300b9581c1203203075401d20446 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 90137914 1250 90136664 90136667
    0xa150c211e0e07091104080604080717030a0504150b0303032a190206012304051008030f040806060402031009020d02040e040f020906010e030d05030612030a0909050109061203030f0f020307 83
    0x201054510043c001c00c61703840c4413a8000d00a00c01c9100720600b0f9040540003d01080519014140641c040c0c0d03c0e0302100c00c006400203070507a00032104000401c0c0e44c0d40a020500c28401104060641c04680030041c0e1101000025070302d000052451101c40400c003407890703590f048007603400300f0500c0c0810002d444000700d1401c000404d22145a440051250400000b003480c02000100f10349602003118201600d1400144070240400034240251420a11780015251004000601030503400c004a26202c90610b00c009082c20701c0609413501c5680140240950300028030285001c13682c2c00840140c0e07070741e11039040c9400f07400b03260b01c0055441703d04000c000600427400c0074502030500c2221410480d5540000540d04241e019101d242c0640c00510100284c0d0f009800031034210b0001400641400c4005140c07510b554003418000001070f80036903041103100750724080c02e8094211070f00d052004504007442a8030880c034002001d0109a104c0c03241a4880d0641c0d0710000910007508400c0d9628500641c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 90139164 1250 90137914 90137923
    0x60806010305030a1d0607110103060503061005030714010206160c06050403030e0f01090308061915030e070603020702060d0c0e09040b012306040e04050f0a150c211e0e 74
    0x313104046068600c00000801d40036400034403e01c0002c000d2810f0130f450352254401400c9041c102d41c14075070b50b1200481c030780d50104200c80c815800b03000da1261440c04e1006043c2804400d40c400b11194040325035581c2960f03000300c0d00a030300c03d0300c168180981c48004642255940c00440c000b0b00024030b010144802c1c903625800000c0c0c4c40c00001c0c110380c0e9080300034841508990429a001d030001d6070901c0481e007685003120a45800c40482d41d19000440d031601c032000c1903c0c60a07a2100042036803074081c0c807240e40301402840002c04e4182021802d289458000c642c2a11500c070101140365030301c08580381958050000300419940c050a903901c2441c1a19190308605020b010390080300031503119030302d8119400c61034204000806040f95060503d825609241c40d50040e208036154029420060300c1c1d040d04200b58208070b03014819510b02200f00841d91300032a41602c88e6003040151400000d80549111402c0080d813a00c41c000005a5030001182141814550708800740e01e107080c01900140340e5000078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 90140414 1250 90139164 90139177
    0xb07030501061d0a0504020c0705040f050604060f030302060105090c1c1401050307030f080901030b060a020703020f0108070c140f010603051c080105030a0f02060904020d1505060c030d0f06080601030503 89
    0x4540d80030b03160148211800401280100544c054508403081c007141c1481c3e0040c00700705004608954980f0789a40000f41510007688031603060710760f03440c10040c4915141c0500402010b4000940e05000c1c02c54070000c1d100c140500409003e580c0e090007055611404d00100d5119004060385620122500c410040280011012201c82c0720382c1c800000c5a030f0310340410350404403540324591a00c9000700382d031081c0c41030f00102c1c21a4103140e600c041c58601605c1d803000400c03540800d40d01038106181503204024031550101c0090341007101c0e01c020440103941111104180b980c11008001096092440a170324140348011800700d41c0d400c0400000401800040312010203180c1c403008031504c68054000c45255000740b00340365042e03010588001c0400c4c0c0c500002c00c2080d0000e040c1524201030400818241c4c0d101c49026030070150f844001c00d00301f50103d014540501411611a40740c0051040c805940b030191170003502c18245d940e480e0314408400356011600418041e001d55000b9070352800c1060b165003110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 90141664 1250 90140414 90140417
    0x1e03070506010b0c0a060902030307081c0c02010c08040609060902030709060e0108010b0a0608040305120f06030d0c052508060403171e0403030b12070f150203092b0b0703050106 78
    0x4000325150140700d061351800707407040004108401480c0c070b441c000341000d19402c0e41c05001c2044114040b0b1541001424400c2c1c018008005010b4001550011212031655800869140205e4049110741c4809119000741d00600040740c4440e013810910001d0000510081d81803054000000d58110940c0240b82218400400d201c01340ea82c4101c1d003800d81d0b6092050759400800709205002083c007035112550040e0203450200d0800001380c03440e0004031000e80356800407641e4141044400d280400c8103803642400d5280c0b000300b080350360780c4c0e156030303a452014264182c2d5010618082d088115681e410000c00c00c0c0c04c214be1840c05c00e400c0140001c942141c2d00c00429005800040034114514008011001c811603c407049540d03d4608030000c05000d4003550b03102c2c000041c007a000010070032180014024898100064078a404068940283c4041055003907410034003000b100b9548100c658401c40d030b0025014003056588139032003c01015403d00040030f9941c00002e103c152a41a40700038141e4845 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 90142914 1250 90141664 90141673
    0x507030609061d100b070c050a06031406060a020309091005040b010c080a03150503010e010b01021905070b0d0b0a03050604051501082a0402270916111e030705 70
    0x111a081c0080d90701900900107285010240440c0b4a03030980300d01c1d41d000c02628000c0701d00540301c00c007401590340007000039940e000a9000034070551900c480c0010050005080c20450403807011a800c05103600101210b00c650004185007161900034800c64404c00001015154649031801e111040c250301405158040c80c503204030b480031540203034811248290044509810100040707400ca02902e4a12442c0c40b041c00c459000090703503203003402081200c03c1410000724000400e54002881d222a0040d1075000d200e221424402040000c19040d041e50522540346544855524025001d813400e806e0315a081020380300000140440490107a0041c0e110b00c081d61140c0c0c00e0602000034a007000e01500800f504000e4038810036035080f04803000b212841125841c18900d55000250807038200b00180e04264007060321040c2c010458840110030480d0460f41c520707081c00c040c051180745880040c5000203001e100b0550b44d0742c6060401c50441814040281c40c03080008244840c0d4581e0840d040c00c6895108 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 90144164 1250 90142914 90142919
    0x30f05010501120b0a050a180317150d03030207111f020d0503040b130f05121308120304030f030b0301150311090103051924050405160b0a08041a0a05070306 69
    0x1070503c00c01c290160003400c40c920740e071112a078240007824041c202032000c0359500e0b072040c8041981c8410582c01c81c069100c60805901600c240250b0316401015a44182031007541058680d442c08028400c15405290040e207481085c0b41503100b0388000c50986030300001940015441c141402240c02e0400071540c207482c5000e080c1682aa840d0200f5a40108035400c0300700043c2c0524420344040d804140100d00302d902d20301e000d0f1a40750801c00e10040f80b98000000140304080940c41103503900050160308014403102c550070501840c18000544000d04001c1c0320208544021301c41d40022330440720040080107100d094203009061110309120071102180445503150451804440313950480c2d03045001f51100d0144000360400e100035050046440038040c00b42400c2c9841c000e03040c00d480b4642c4c4cc600141c2030421342040c500c0c0c00d8083e103581080c5000f5800a026178000d50050b1101c0400c5c80c1803a0364a5161890010f80c600741c078845011707041001000300800a103035900258082d640d00e890410400b45c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 90145414 1250 90144164 90144179
    0x201090b040f0909030e10020303060109050d02090a020a022104031104050f04032019110306010b220b03070e09060d0c050607060608120c0d030209031b011107030f05010501 76
    0x140d0300c5240005031081c8410041c2e0b060300d401004e00c2d18400c3c6801060050340000040301080d00c4015900141d0021080003c2540c12041040150400b260221f20b0050f0b40e6000030000170740100b8542c1d000d90003183e4000c03c1402045411b95120f810700840fa200c80c0c03242143c080c0b83d0014801640c0300107015070655814107092051a00030402d1000401c02940d80b034a06880d240c0d68542035901200303808240c01c020031018040d400034204419042c400f0841d050410340b000c0e1740c1d0315001c80d200340c001c400100302c0410101c04079491440081c1818071400992886034045100070392004880a40000c20448440e5000980c1380540208030360140e01c03600c42405000070101c4025008206002041050203545048405401c0803031041c0c0010490a446030f83c49030420a44602c0f48a0110001c0740c0030294600134041e01e641350081e03103411411300080c04001b0780e54482c420000c8032080005401d00056910034280c0360f0b00107201c075085a1103140e481c80d0600c2d10002c1c80c034094409501c1c0c20f00108485 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 90146664 1250 90145414 90145417
    0x5070302180f0f210c01110304140613030b0906090115030305160c0815060f010e090402011404060905130606210905010f0e0105060f06030c0a030213030c030201090b 73
    0x6800d00105407408055a041c4415041881480e50f0b200c0b0798940300c088290b95012103035a06100910b010200410700101040ca020310861140b4148004000c0e1509540b10000a403021504030241c1c50000c40291030100d02d1030302c0f520b01071140c441c03c081c60101c00d01588282440c021000e180443d81240d862004a600f200d60701c034802030250044007000c00100f84070390050f0007010140c022001107101640d46900401c042075006020705e801580c1c2804030002ea00101c264019025034181c5219040040020001d901000030f242c860031001001c50150b902c1054200301100949884a540d2501e510024210443c5441824801e0901200e8120070804900619040302d51984850b2403c241c2030010040401001c0603003a5115581c521040c0400c00074054001c111003000800a03807821500d40560035030750000d1440d402a610442c13003a13040d0300c9507400c49a20144001c034198407111000d01c214064443c401d501d8001052141e00402400740c409041800c50b80700340c0310b01c00c12650343c0c3c4081999 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 90147914 1250 90146664 90146677
    0x9051003090b060916030c050f0408070e010902070f08030a09050607030b030f030f0d0507020313030305070308060915150c06100504151208070c08010c03090203070504060305060a0e07050d03020a03020105070302 93
    0xe41119a80003175124020f40006528810303909145081a03915800940c03290425030113004a6481030720208034140112a480740540001071741907162040d503482c3c01e0301c02038240c0401031003104000b0002e194809139600c64004941d00c034051314801d09101800401500460b44254802c0c0141c221100d0140000000c4034550f14005400500309404400b442c1c6c0201402480c0001350300040085031a1000301c8080302002c0c40c401c0d2a6103850326000e040c018010b00e801040640a09804000d029507560780e40c135900202501141c001211000c0110a600140100400b01d0103d10451090051404540142005030340041d80c04100d058410b0400c1c401918541c4141c2601c002c0c4080958085014407000b82074490280d60300e200310036502e100302401c4a03c24070700c250009a403035030480114503007409150010070048505126660568840d581c9800d03000e40304c28889540c64130090034079441031040100038140103000e0740084101c0d05000c1d48440034510120019440c0070001480140070703100f9500c2c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 90149164 1250 90147914 90147931
    0x20d0801030615030b04060219320409140a0f091e020103110c0105070f020c01090b070c0b030c1b06070903031809020c030703021006030b130309051003090b0609 71
    0x2280e480d6031141002003070920840824903203450b01c08004075034032501c00d501441c46460016580d081030107060384840394480b0500100044c48000700004aa14003440104a12131403680d90341540daa903a5070301c60700c03a40c1e014034045400c1230003404a080310054080d108d0081b02805100c04801c0c0503200085401c42e0314002e00d00c140b05031111081c07112101098140c1d070710605002038000d0b0111211185a0001d6504440d103a44070001c00c440035a021400c1c1b070690142d4001440380150400010701140c07441e0103120403644000c1801c00600900002d100c0041c50080d00080d941d00700840f40c000310380e108181c001d410b05050214006400030006000b40f15591640d240c0c00d1003429941c046400340e100c01d14041039045156408110f0000e035100a2000d000b04000540d911181854040c0c01c00e00ea100d030010509141030700410110300c07039401c2280d006460b262704c800c106803249420f035104001d179003001d81c00c4507440103030f0264943c140d403140038003034056046c0b8521035494a081154240d4110390450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 90150414 1250 90149164 90149177
    0x121d0411070803190501030605090c0d03050301060507020a030b0406051b07030503060906120d09080d020105061c020a18020403020405160c060518030310090e03030411060a0909020c150106020d 85
    0x10104400c007000d103801807290340d603803d00f01c2d601204e4081034400c203030021707110240c3d00c200b40719440804210b00c650702d001c00c0c3d07160880c0070038a86000d062408140700b140c0c20f02c0000508503085580700680c50016580c0600606900d040500b02500107003400c407002da0010600312203400f00340c401c0005803030040d94190350302c618541d621018800d0014010b0316080e0482060100c00c00903a06c1070001c00c076500c05940e035600034503150440b003d2400100741e00240569150405101c3c0545030f110710358520f443d02e52404e4001b0f22040c40031650000031f07030303021844d22407880d203100b03240030b44580052040300c2c000c440034807503601d882d45031341c1d4290528190080031502c405500000108540c101a034422481e031821581980540201c6045070300480e1000e800c02680c0100780040714492050724074050f079140065096281668404042500702c00d1268030a04000c124515020310036954640a450f50240940d154118080c0107650350081800c940c8500301250004103200c1e02c0011100402d521603951007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 90151664 1250 90150414 90150427
    0x1805010507020a0503030304110f060a1b02060f0a030b10031109040911030a06020304120c0c0b070c0906230108220206070206030705040303080108031216020109121d0411 75
    0x1034034654007070142280c00210740700001485507000c0c40514490b900500003101d101019908201c814488c026030b0300d00c500414441e032030a1f10f80c4100c030101100c0140e038240290741002d0001400c03600440000038005e45000035025400d07641600807000400b01500c0503400c03523210000036801c2d10060405501000001d02017000b86140542240880e42d005640301c95000d9222070220b818281c1c8000103840840d000018401001003001881228040a1410a400e2842075480c400003805a2107030018241012030700303105110400100100810402c10108403d0380c0e510000c1e0300d001201d004c0c114101c000404901200d500844c1107901c80e061051026500780c1c0106030b0a0704d182c035252010798004100b40219001a140c1c00001e500507801521210f40f514030350303c2c00030074542c0c0581220740250010b01c505034000c040c2c10200e83c0c1010300b003840c481c00791040d100c04a004003007101d0041d01001d034007501003411903007016002c9460841481c43d1240f031003034407040c0030582d590f00001c1000f8074130802c0b10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 90152914 1250 90151664 90151667
    0x70b0705031f060f08010e040b010302101101052d0609070f03110301141002070812030601020f06011e06030e030a1116091a040b0f040c050d05040b010501080601180501 74
    0x9503400318001c003400e101400a146000038a41403038203ca008628950b100c08803081d0403031081c500401c02c50070080300a1900c1d599205240f80c043c0f00c028000d400340f800920180d030084041241d01110b00c0b000f004289070804640b0f00382c240d110b8a2072507185122202500e41110b0361001071140c14040c052003040d8880d40822220412203c20040070103994510090040e40c40350003c5000300b20105c051001201c1020030010608440312056081d91b1050a04100c80355002c1040d00c3c121480142d050746035921140184c1c281600f0a034078807114001d001c000701e140302d80d40d41804c845c50340000c40407090a41707a1000342e00700e403103001042e1199401808454040f61003140900c035080324610507030703425103c42109100300321350340d8008808468542142d804d11004040d805051003400b01c505000384150600030883d0001e840d030030702d4025900c5a0410118602501c00c6401c1c3c06240c0504100c0c1e45040e08103410084020302070a8006011b1202040c601d621501c1e8829099208442c2e044016141000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 90154164 1250 90152914 90152917
    0x323040b09030705030d02031e1005012a12030c020111092b03050702041109060d05070203210402090105030d09180902040603080c070f08070302120f011d070b070b0705 74
    0x140c000e40d440100f0400340007450510180200040c100b102680301c0c1041c040340c2c0701207007881e805541d942c81c98100700300070b082c01c040c0c044044410a0030176921708010704032811900185c1c00804140341c202c03190003504000e0b041a099100c016195020400c0c04c0010000701d00341c40140d5000102c1d228280a80c0daa10304e000019582a540d4000c00c414801040341411a81d04171821421340115102050581c19400c050080740c842a48004000303141c44590800944c46005a400441150b9900c170300142010f4020811030b80140301c8021080e8060494407100100a50216000c900035041c2d035000050f0f40c1030014181c880038500d51211840c441c2407410840e124501500407141d00c5444090200c00358540e031140b00099400350f5140c1c1d589210000403e880c22100345c0c4607101102040e1400c02c520300000c00c150045d02e0381212801d80541da810700d2549000003a11000c07419520740110007020b090003141c00b000141c010b01c107a030046541c0b01c40001caa8001d02c1d0700500080c1c406030009840520400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 90155414 1250 90154164 90154171
    0x1020408072106150315110406030207051216020f03030909041401060b03010f0611060403020316030c0b0c0301050a09020a0e0d051608010609060b07020a0608061503090703030323040b 81
    0x1596619001036603110001a00d080d0388282080084e500310600900664408040418800300c00501441d0a0004160260710440c8901020154041135070410014184404521400503120541c0c440d11000c60000b8009041c1004138801c9503280300c2442c423400c01100303580a02078000d082049580d550b0301e5203070001c15118003400055588480c0400d04030802070240d0f018105071101400c0042c24200c0283c151194024000d1040d0300407001c010000740d00004a820040c220f00000238402e01d00d00d4155003c00d61403c1c002e1441d43c01404102840e44178901460480d0341c01c840c1d214403250b503480c1d81d004901c1110300c500c0c0064284810b210907800d10b000c920300203603c110226040d61081c0c41441440000e1780c0c0250900303945900c01003010b00424020240a04407100026141070010750014102ca8003512602c1c1c14070a0100000f096a0750700d00c04150301400c00512030b6078070b18020440f15180c680c7c80c00f0840c0800c0c503180c51001500c1d440c880c3d000c10101030b8180c0c2007154403203442d03804a000300207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 90156664 1250 90155414 90155459
    0x110306060c030d06030b06090106110d050a090f082b0e0d080408010f05010311030d020312070203070c0b0702010305070e13050603100f1e020a140c0328030506030102040807 76
    0x200110303403c48203148512401540103100480381801e007101002420541030780142c0130056216040182e46001007030444131041281489640c4a120b074070309564015082d0320103504040110000160004045500c40369003108244c0480c40350460f510882800e0b0300714890317034000386103594419441d040c00416281064024403600f81071070ba80d6681a42500d8090841c0c004603912000100104040c1350186010f00008030050005a201c10030300a50b280075005d0700303084000011001ca42514000e1040300d06240d04509013000301c070349400010310b6540c0032a0049000030718040000c0e00052142c042d081c4461001000010220005103412019182c05000c244d40341c00b4002c900c1d46100c0c010f2181611f4841010720100b24640030032000201c101d020082d20154900400151320b5107a407120a00c0c0340d80c404a2011511080d00c0d440c5a49140940b807461440504111300da0701402080c2e141c1c00c050503206541c00d01565564801341800c2c0e008501c20310b0503a0340060b00c24004058000c1c44400e242264 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 90157914 1250 90156664 90156667
    0x8121e0d0209150c0705060a0e0603040c05060c0d02060a02030403090e100e010f081005040804030b0c041e05040e0705030d231b0d02060403081501050706060b03090c04110306060c03 80
    0x700707000200c0030301d42c40203401c2d40fa600010741985001400e0010070010801110180d051a84108018203604804080c46100b01c0c00080050200a402c00480e80038020140c07445450f40c081d0009035917a410000d4100c8054840c03540080c10400450084038400d0754986e8495080d28980146c5903041c017800b50142000e00c0366104041681c06004035003a008003181c02030000590320345074070242005510f034200d28a550401d410000030401400131503007240e42c0040441005d96460b495025240502d810a40c0b103680c400d00561260000c00d004002034030411034040080380540c4084580e10b4400d4464590150041100420054007590164482001516050380c48501014406019501000c03d507000107a000ca6500c500500402c000500481540002c14090a1a84010300303141001000f111110301000902c4030641d110b1400d496499500c04001c0c001e0341e8540441c03a210360400c0b6010a407510543c408c140c1c03245440d00500392010700c03081c0d4441c03450310354030144001c0b0761160145404030300c070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 90159164 1250 90157914 90157927
    0x60309050c1f030b030a1a042102060109060602060412030b0a03020a0b1306050301080601180b03150f0a020f0906090406031a01030b060a180b01110706020708121e0d02 74
    0x100d0402c5403681982c000030364440445403000203000c43c0c001007181c0703000341d220700c20210004408100750041d007407109000900c4c40c1d4407480d10340340000d041c0322014004500707100410809500003814505032002c00c0010b0003c207850f4a0101c2c0d41d5602120003801041c10300012a4055010750310800741d528015003009035445c2c49402050f08000184c0c405a00907100050300340801d06101692000380605d803501c2e51555140c04103c56842c40180a5101d10708600d00aa501d066101d0703019641440000c2c0a50702060050030340509000700c12514600210300050014003400748510031125481d4003121614140a491804e00c0b21680240741c00342e804c0741c0d03207480200c00724030025194407032107000300c242c0a030070b6041d03203401c2c00c2240c03001e444140141c071094000d000340d281c450820f02c0b00314500320b03000540590401c01290240038540400510f401001e0001c50240c1d0701048030400d442c1c80208172401604a040d0302480d61041018031481292110040b00e10b0307040140080132107407402c0501500b80301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 90160414 1250 90159164 90159169
    0xc10030e0d0203070c17030f09010207030204090b0a05010b09181e0f0a06090207020105030f10051309032006010e1308180f0a03120e120703060b01110604020604060309050c 76
    0x441820901002d42d00c0810a0410840d580d4800b901600d0404840c4440302009000d15940780100303168070000b020045001c1100f0703403080055400071a00184240700c100c002e41800e40c00a00f00f500e65001c594101400410540341000072600e83c00e0010300243c0004403202e522410004025090040e22010581010001403105440758080c901d44440a145401c00d14158000c41e0540e07400145558010302c2200007513a0400140d1b5404480030600000c00d0360342580d8031642c418950000c030b83c0094000040c80c0c0b078210a0b840400c48601c02e40318040c0c68070003c08541c1c050000e028600056a0040e4014495140c0c12154a078102159686000c47c07420965188801c81d00301c44018440b000000540c143d41e40740005c01d003515441c0581d10400d6039800c1d52281407000d10800b0080050100c1c56642480584034000441074000c110800c0e0f44040e5203d10b00240a0701051108500085003207001018952020400034090341e80141164070307151408106134040d003a40781c8262200d0251520f56010703038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 90161664 1250 90160414 90160423
    0x40506071509050c01021603020d0605060d050a29040c05120313031b050108070f0503101a031503070e0a051518010e09030a050403170c1905060f06030c10030e 70
    0x20743c450f070060085103040c030000a280c50b50745195124484960001040541c45034122000d2050f0012004035140d5227100c041106418003220007400c520034801d8400c240301c0c0c0030801d02b441001001c000d8070200390035401c07584001001d0701c2c0504000100d1004000300d01e88103802158030003030f9005a0b414aa98151001418142944113542d1007401031120261035a0800d4440064072007420140f000b400c00385c4004103070303000d15200c00d4144100040405c40c04044d00785500000c100d456403529600e243c4410035100d9410035608109011b00713101c42c070003986c035001c645c110584c0c05004458600b43e49045000c405004003400c88642c0001c030403414849034a451800090010303215156062951504848003a1080000d00195980e0000e0210b110040c0d4010201c608482d040190b1004061030581c02400300c0c07090508810a501c074400f4180c00c0700701c070401e20340b200070b010740d0030307280d46541d002982141c800b011038402d87d00d41c024140c012160f240030b542805a040b01450002121020500e2040c0380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 90162914 1250 90161664 90161681
    0x10b041a090f12070302100c0f0f0804052206060306061b020607080c0604021005091509060408010606020a031101020f0706050421031a1918180c1401030b060405060715 74
    0x458100c14414410f50621f8000114800b010b03141000740e21700c140e00c0c0d03034000c96004007006001003a080c40c0c000500c200101590060f001c001d008682800605801e9031041081c1641e5240351800c5c0a00028194024410340307046404540b03690307400395102ca40700d0b08481d0308400d00f264000c3c010300c40c020104a841010703100a0401d000241447d0929004201d0414044860301c4204034041107c4583e584520031f01440c101d0407240b0007903e40d1071600028015018a420441d00c0c0d610384900019071360350000f03c204015001c0d80391400104160b08010303090f4800c540360020225010054400090290341c400b03603000c3d000b1030940f044e14510740700306c449001881115900090300d031100c4030040901c403001d24040e15070407074000303040e01c2c0302c020800c10000342442490000f244407821440d0040d1a03070404950b01030794481102000c0d00310719190007810024001d08281c2020b01504a070954003d105101682c0c0d8001c1800c0d0606251108110036688408822a900f0700b400700c11881c0f15845000310318a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 90164164 1250 90162914 90162949
    0x703030807110318032a011214041a010e01060509010f050904060b22050a062001060810110307020a060f0b030316020f0a06050d0207030306080312010e010b041a090f 73
    0x382c00000c0805c25160052020512039400c2c40041d000c401402003d003240780103542170920501910300751b080300c401400301132503862800f8000c00401c41003000c20783c088400325000340e92040150742c03141c40304810b2400900581010400c108008c1d1300944c002d81800124403068a001031500140e0804202510340a6200c01c030490b40200d5945850840d9400c092070060005016100faa85001c00150b50000e00b4422102841010b0315091400300c1c4031603414100c185008001c0c00b2482e07447ca59a65510b080d06130440c2414034200a511124076801c0071a8007823200355005080070042030f182d44c002051403050605400346d49100061841d24240050300b501d0b600c06103000903504050060000304818200e10070711076118060103120b6580c003d01a1500e40e07041650068403a0f915107403d50080c4482d40040301b0034480031410103000c841036074030703141a01d0b60034419048a9aa4041e1610325000703600800c1140d00700012820350b1000721034007030030541d02c0040110070804d451030081401c88041040361030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 90165414 1250 90164164 90164197
    0x1c112704020f130212010503070801090f060c11070308030105030606011106070f031b03020702040e0703020d0807020d02040f05040201020c100507020d0c0e0c04090c080c03010b0d060902030a06030302011107030207030308071103 100
    0x47c926080c403003000202101c10082c440712026644036080c1c0303260680c0003481d181e51450445403191046080e4200114100101c510164407070605a08c607401c2445054840c1c862a400100c4e02e5204801c2c00c00720380401401440c454507000350681c0c6040720703076020070101555801e07070039070313041c480a500c82070203800751001a6525003500611065075020a101d000c1980280310800068490198018120741c00004d0b06458030554400a0364031005003602940c0300d82000022903240c02e00381c0c011790255100360200c940703001d040c005001802d20500c04090200d038003806031401605007403c1c4100001d00c91042140f09039240e10346078000e00c0007515203003609000480c060010843d148140703034280c1040c2c10565401e20b0007a4030b899043c0703c1400f49050301c02020441180000e81504001d0252441d110155124607004141000600f428807040d4019170038544211980c41e09502200d041d9038055029040e01811134034151849034010b401d07442003100020310400c04840034000740c100c3c07a4800141a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 90166664 1250 90165414 90165419
    0xc150c0c17071a04050102090405010b030604140403050901030e03120106020607110609060601110c1003050a0c0e03030a0804020102070e04060f0b041503030e1c112704020f13021201 80
    0x262008035264140c9a00c00b0032032030003c100b086800d29004440d041600c5810755582c03604d140a4050008241d80150030321001281000d0180040d5100c0e5400f694100200c2e506107160010b100b02c11388000d070110743d0811010703040707500c26042104849004411603141810404980c1c280a109034000c00040c0c0155081c0408650303c04400d02d1001c04103030040030345041c5a5500341e110080640480e060214a0700300745503c030003d000d0600700d030400a0044a101c0080303d03000e009400225003c1006a05e00f601801d03c02c0c1c06517001c03c0c010600540190300741228903200343c94450f00070b0410380c154400c0d1f03040040d2040c40c2c00071b010701c80e500c10240030811542d41c01d003031300a0320307a049070040c41207007001c641c000300d800f90f00d125100b2a6018609441c01c20410340104010303012146541e1b1400882411040c1405082020610400002e0740c4940000070032161524203464910102e81c3e6a40d8503502180261810782c4101c1e11006000f858003a00c00642e0700b083e0708980c00200000080d0702585d004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 90167914 1250 90166664 90166673
    0xb120c1522080f2a010f090b0d0b03160315020c070f08010906060f0302030a020409060e030d150f0302010503240603040303090b010b0c121c06120c12020f010c150c0c 73
    0x1c42c408510b030b0891646a2251308034607081054540790740c0d54104143c041c00281c440384075001020081c2030441d4a6aa120308004d0300c42c0260407440741e00e03400b0780b003180180c1000d6400e807503d42040340e030130010301c0c43e034035540c1f604c85e40195202045d0440588034460011441c101218034041c010a01c0c00c0000500b85548c0c0707401c0c0309540155002240c0054480010405a14045810403880f64100c0d0000b400c081c0c245070001c010260117160b12154403002c540c900c00001158010070413544004440d070040344c4d41d503140b0043e105440c000240002d00c1400401d01013811902c00201146402d2031450042204102080d0f15070800c840039170000382c035403200005214011005d1800342c425801d400d4606450310b0340340d55442d980070184110425000610b00d604040f24410415103007880301e801d1240380d64400c00c041300c08130b004000380c0b03045501e500300098804406244a007a02c1d4060220100c0e062003100541c0c204200883c2521048002c440c54855102140300e11818840c441e2a2024002c000303050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 90169164 1250 90167914 90167923
    0x4090e0c10080a0b0d1205070f060617010518030a110f0307060501050910050f0d02030c0306010806040c14011d060702041407030609050c03040b040f0609060b120c1522080f 76
    0x413114081d82c40c03403c1003800f08a5101104042154608020756543c1180c42c00c03107000c0202c2e11020b01000c0c503100012400007113070303c903880070032041900a12040d04d4002100d03841c1500c00000c0789007603008100e00c288103400340a081e042d03011a0020303110011550102da17421070740180b030101d517010307540c00c01401180b0301030203929082103d40c02c408800320300b0170307010030710340e820700340040d8407440c4902820b004654040003501966500a41a1015540c0d0f81f1141d6544070002d035400c503144249440b02042d400d000d00c0d001130980505948080417007650145805140783c4000b056034020004106030300c0561103501491035400159600e603401d46c0f0740340600400702c2c0c942e030708080101400c0000b48450300d400e0f0070a9a801c00d0b08009a10465101c1c0c3ca02088840034124004001c5420255100d083c028a6806012a10020f03211381e8030700c0c00d10050350790b22100050300050748407a860400d1000c07a4002c002a00407500d482e5001003c94034622001600c030005c03640300d9421940020405c3d40c0003c401e20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 90170414 1250 90169164 90169181
    0x20f12070801150905071403090a0c12020f030609030909040320070306061d0406020d02120a020307170106080406050907080a060e010b04050405060c09060d02160201090e0c04090e0c10080a 83
    0x81c02c100c02d0818281c001c0210047c0400c925007124003001003104030720b06025804140342d001c031030003034030a584081252140142d040241e129510840145110381000305e4480d02c12103070b030b0b0007640c640b0318184200404180e0250040d03081002c0c0c003481a00c0b116002082044034030110b0300800106103185049000d442ca280c000c1d620200c121800d4402011210700d1045d0410f034011405a1912100384c0c0c100c00070b0081091640751344088a0038015008016030055015103501c0ea02d10428031070140000705900000c0c416400028103603000240401d08a034402600421000c09840700ca03643e03980991715240700ca450684000d17903111414203074042c0c00d1094590604c401d0780c05010a162917214981c40e090000c0c070540b18250001100d001e81d603030358011246404259401107449140140d02030700d2080403410708a02007410b6000101d43d030032603104c806106107690441113250500700510b200280405140c800320078442e80c80e0b00c80c0ca6503144040c50b0101103650341e03410311600c1d05608203820740b030810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 90171664 1250 90170414 90170429
    0x120c080420150903010906020f07050f0a020d02131d0706110d0507020105070303180803011d041509020f040203070e0118050108041217040b0603010e0105090703020f1207080115 78
    0x84201c801540701c104034000303410b51801019450b10b28101c00b1901410f0b1404004001e1440002c401d107a1151032800b42940b1360060b000ca4411402442c0440e545100d80d4a002c0d41c08015550403000502e414805d15411500f140700200d4481c00820006200091001041c02036400c039071010710111b07502c070022005020b1240300411100d60084006002da1007840800790400c80300140c803005041c000e411801cac90302c40450705040000b500c0d040a0003690001c0c05500e81c0c0d2410300c40890420080c42401da4000e40d0490550078801c4800c194200040c0380342e400803170700070110000610440e5a648055485030700c0700d8640c000c0280303c20000400e0380d0b002244401c0300148a2009000c0c0780d0780b181041e0788c4194440c22403040c0781103501080cbc844c0d007400320000705070b40035400800c01041241c500990045006800074490f0009141c5064243e0b0812a00560b4541c00309800f000949844a030031224128060401c03c01d00450401c4641050325a13004030802c4c1e03446032401004120324036001c00040115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 90172914 1250 90171664 90171713
    0x9030a03030c0e0114041214031c0e060403080105040c020c03011401091404030c120e0d0606060315121e020a03050c01021c0806010305150301060e06040605040203010e070f120c0804 80
    0x2080390201b4090b50040c1900150481450000c0100c8031819128035401842103d84801c1700321a684035203064500012442414104458402000020018002d60345511500310766800c000c1032000800803000381404610a400b99030a07542c07801e104020041070b030420811030301e40c1440280c0c3c094079a106000064180c201702048003003a80711481d045d18580c05a1994503081440b6401c58100040080050f4000c0c200d281400070440a81d003d20100ca803144c40a000d00030003102c10100e16465842030807090100c510217000003461108100c1e10b40c6a00c0010040011030503000b1071001491900308603041d0380841600c010f20342e0100404c0307c0301c6180850381500400078160040c0021405024103060548074008581043e045180076404c0300700c050020042c0c165141c407040400d581c280d40480c05903240c1070000c40c130317402c0a000b240d058030315041e02000d00e910380b560211100106143d00104100020003890f516210074000d6100404055954400c4c0341041d0505c0300d055582441001d80e00d814 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 90174164 1250 90172914 90172937
    0x3030203030c0306010309080f0304060c0509030d050d06030609080c0c060a050d0b010c02041b08010909050c0d0609081309050a270f051518060108070e06040209030a03030c0e01 78
    0xa001085a0307201e0b95042a0329101c0d120400107a010f06141c036002001c05ca000706110084032414000f86104a000300c100344080c04074480161002d1040100041c2c1507080400503580303050040c4d00030301c180c3c40c500200081c0540c2da81c407440202c9240b880d0440300b007180002d029142c10020418030880510031581c1904c1d1030701011b40541144607a600d00a141c548650080300304e41e020310341012803144c021300b051103e03100103c0307000703070812620b42603a0100e8001e100200d101080f81c420f021100d039004008140d071003208400c10014810450040340e1064035400904005440312000d00f4198803207802d81000705040001220a407600113154418807403070005039001d0380400c01150740828903480c106203826130075802c5c42403021010107805800c9104070f601c04103521085403a1f083c4213540208158003501c045c0200d041c1c49160a105141d55035001038014040036030031503503490b00813400600043c601000341c0080790408594100a03000309986101c109039854010f0b241b031440010910b4801c08125 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 90175414 1250 90174164 90174167
    0x501020f072312010519140103020a2108040605041a0c1c020a06050f01030506010512060f060103020702040f0b09060a1d0702070302090f090d090501020c1e0618030d02070303 77
    0x8040c021002c0251001810481558a840010760b800d041ca01c8001e200c00d1034054108203401d0090a03110300036501c0c0142404603207046205080c1070f664002e12162003646442c010011351400080c0450b044468502d0722000110311000070802080e00b501c0f841c0d1207602d0941060904a00c10040c101158002c000c01d5800203800310b4642e10341200c0220f00b100d02c89204408030310f440000721000341101d281c403051250003600c151416040f28407400440b5150380c1c80b10306124002460055100c03c0340c0c4032034042404401c00d00120350b4031903010b240050418100f40c0000e8103031960040c4410340d5030303a10030000e52a404c00310004c2d5440801034409020080c0f5100d200c044030f1039840e210b40000303000d500c04034440d64424001c8038025070f001800c190309418964001090503c040d80d000105110310138020000038000c0b8100011220305030080d0080d80c41040500c01c241c100e0340210025000d0b110010030050f5074000241c41410115940003c424100c0303802c1c0752800198020140c19503224040800010f07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 90176664 1250 90175414 90175439
    0x1e03080714011508030705010b12030403030e150307030e0d0201020910030213080a0804080606010e010e100908011803141207110109080f031906030201050a141903060501020f07 78
    0x940c0221031041508004004a0050185098806100d1845070f4005940d01001024041950082c4001c0010765581341c03c1140f00ba00404560340c03940c10502c02080403c3c007402140c0c201180140ca0490021850060617100380d008540d580302095488004001100c01040740d4540500e40740000c5282c03a42a1001840b500140d01100003056000500a06e00e1710022303442000400781c800484001c0c0d82c0d649402910b40c3c225014000c65440344400043c1e55620421b1a01c407000810384902100d451003000380107500d20f192004001f4003460f001c00044650091040c0d03011600c40c03a5810300d0924081c50300800c1d11513507a4400194150522640141d522800d259640004c0a0300307001060412615001e0702401c0850b03800780907540003040c42e01401950704011481642203c1152158450750780d00344044508501000e4006642401a4490a80603500c0906102c0d0708a0b5102c1c1840c5200409248034401104000d0003e46c03668001c000950701000a00c1804030058041c011003030a1002e40c0982 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 90177914 1250 90176664 90176677
    0x909030818060606180102070506070605161403060402030402040e0a050105060117040809060c15040c030204050906070c3504150f08060409060906020a031515020a0f051c0201061e0308 81
    0x5017000701c4401105603008001a0008200c00342085840c1c0740f01d424950010308c0c00311148482c0b0103a0010000e851482110140c400000c00490313241542c0705c141c14480290402807003243c10a03a80d070b0081c000f40008000708408244504e001044d11701d00500010031446005a10b00c0d032209510040c032002400700015503881a0b4150f8a160b00e40222889042c41c00c801405882d1030100d210301840b090100b212800401d4030300954080c00301e0b0b1202c81101d0355801c412100d210014079501031450000d01c2c0341c4d00104011004a0b4040720f42e62100800e1188102c5550030b010011000050401c0301614298500515840714148150703ea10100000303000328100401c0107100c0c5640740501c0d0200300d81644a4203101d90090811525802d8848000d802450f00d09144541d038490f0300400140c100d0706568201030040c05601620324103a5030f40d0740804104000300121041d01984010343ca4084020741785070050b000c81e5001180302c901d08400305843005d04c080c0d851201c03c031400030144041211002110362 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 90179164 1250 90177914 90177937
    0xa05040504090f080408060105042316050c07060e030c030a020907080603070308030708101a070308060301140c031905010b0909091501090f0b060307170703060909030818060606 78
    0x50b840d000d850518905208a030008201c110302080c0410110710004266050f80e00a0350100540c0154140d00400322800194131080f080c584000201038030752040c05517001003c9801d0250400c5020f0244070700701a1103400507000070701011301d504242d10301006603c90129050b009803024145030340105403060030080c2150705024150f800b2401c00c0c2c5042005c080110b4020300d915403241030800e001403030f444095070074107100320001c2e44c085201170740c0c00c111240c940d030750102e45c234030340480c5a8040c1c842071001084654955030b00c05441c410301c900c280026120b001c0204120780d80e0310700328041980319085030b0144801c4a1a02005205680300d1004070303420403400301c03074401843d6a0001c69503d448507000140544400350300000505110a402992100e02c03a9031040c0106403000040c03002c0c0b40400c440d220300240003450034500410a5108403038001c51285808108140c075501c1c40001da90b1011004c40009101804003c064501c40200c40030040561024009604040c0005015805410004071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 90180414 1250 90179164 90179171
    0x20a050913050d0e09092a03030d02040803040e01090204080304060c110a0303120e1906020705070e1f06020604030c02090a1d0d180807030b060402070f11010e04020a05040504 77
    0x40411440004221a160b400710403140007030400300c2d00500c40d07a036481445002e84000000b058050030301140400400704140e21100591403d81c0e211600740d10381c02c0b015a014042082007140444e407600052025003402801103507114a080300c02c043c07080050b030045600510522041c04041404412281110b54030300c0d2815009440e403c10601441541c0b074403d13800090310100004164000c03103079401c0508081420008280482c00b2aa1a400102a0500005082c00c914000112aa0701a0004034083ca08513a40c0c55201d1108640c0024156020350810411044c8800e181c82000c4c0ca24014041c2c40c03010f8512070a081d90081c0c100b103800d0310024880d1800d02c0018003000b0881d030204c0d00b0301c8000095070074a0511300c0b40880c7c0f5401ca00311402e0016080240c40304c91840c00c8804d100889425a0062601e540b541d12182918a0090191540260204200d1001c00c0030750110080742030250380c51101404074500051701d10018603542a0145006203d40e035200c039080000e45040303900588011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 90181664 1250 90180414 90180421
    0x70b0a090311150d06061206030201020a120306030b1513060302010c02220903080a0c0201141b090409080a1701052d0d080304060b0d020a060302130f1205010513020a0509 75
    0x55a030940300d641e00482203c002c6004d800d0300c1d10750740200c02154020f1b122540140003124000701520518000640580d110440c120300290581800c4608000c0074500064081d031256600000350fa02614014103580d015195145075180c555290501c22510000c10041c913441c680c00039040c91100038010b0311444203c584080c00480e500001b0a03007219035a41044521a1840c01814950054401c8030318246040449140e0500501c03811800012401203420f26560308290200c401001d0304819540c2c0c1c00c2032042040c2a243c42c01084206441000150b882d203c202070028404889041020100c1c07180c50010000b94441100e0b40c0760041503003508034515010003900528a50341d800061307802292801039681031203184070107103014a00ca00c5003800840901020090f01e4010040d02a42c060010070f4200205030182d401060380e100c90f0f2207066040d9070f40700d070119000d91f0360741d0024141911a09088081003070a10605034800c11140500308440c425070007140c1ca440d480e0044600a14017803012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 90182914 1250 90181664 90181669
    0x6030207060e03030108010603110a060c0b040309030614010315050c03070c03050702030d0903020312070203030a030b040b12010c270603020f070804120c1413051005030a080309070b0a090311 84
    0x82d01e0084090450f40e595a40b0340b02d0318000c1640b0f01c0709540c601c400c2d04524035189050b60b04207088800c0c503602d40c0c40c1450280c852500c5800054001c80501c145441b000001590038080e090310880c0003e42000f070b961660800c821280b400c0303018491131520304002c004400d407022056a800c8000c500d8840e60344903c528081d1543e01c140840039501d031180c1c00203040a1503201a049082c1e03403094041d101d000c1c104075000815070060140080d859041840340c02c0c481d502c268003129501c80010b101203004001000403560590507900e0400c1180d444d4100c10348601d4012030380320125100f1841a5190364601808045801001e000d8001015000111000544102c0058410f21604258101ea4441d03481104004156240200f100c408620801c002103071049c141004038a007402078908030b1490007800381c090003080000e040740301c07420340d10401080070b440c10442400304a00c0342e004035a490030700c0260035252480c0c82c4c0c00018240d104214100307019510145800071641d000c4000c40401e00131000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 90184164 1250 90182914 90182921
    0x31b030109050303090a0c050102120901030f090b180f0705060904020d0b0604090c08010e011d04060612030908010614030a0b07050706020a030b100504050616141c02061e010603020706 81
    0x5020b0001e00c00481402143c0038040340350010309210b0140d40c5100d079950001a40c4800346c0000e0b450070f4503024800d84400754000d4012600f4118155400100c070303400e582e5214602103041c0c490040d0449a05482001020104600500d00321068010305e0980c5c913243c0068960310a101c040c074021600841da240360052203810a10000c03034001c041603110390f2518412001494403011003070001314004000184041007400160584258005642807001d44451608001801410803500c455881310000383c1007000d0054107582c81e22a035921a812850a0791090a5465a8001f26542010381c1e4a6840950300001e2403009680c0c030a911041c25030b10900d00b03880500600c1c038041c1009000044008202d81d156210040c0e01d039080796100140c1015083c00c407054051401041c0d04250b01b080a0700b20107216240c2180e0791407281c81603024054800c4e074070900301081e000c2d00748082c0b040c24410030070058042c80118be2207014030302c0c01000b04000048141300c43d8010704c200c1041c103a000480b5002d2100541 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 90185414 1250 90184164 90184181
    0x12030e030a0c0b0d14010605090402090118171005091c0e030d05030405011404330213030c0b090109051011010507051c0905030328060306020301150c02031b0301 71
    0x1c0302c18019640e400c110940e60041e00001d050380e25007045610540500560181641d130203560b024109640541400000c2d40701c42030490500843e26004103c42811001600142c001440d4240140804104044c60000c80c0c0310b20803030040c01c217800c000401c0d030001140c480c81150310310520304c0c00711800002e849404203248a2505401100744150b540c07504100154000c40c4030b8002000805031a00f6051011803060710000c086040c0b15420220b50949120060b540030742c824040b0b04544803015908049a10a81044501151204041007440340c0c0c0390311200108100d85489141c20407000c0000c00e551030320300403035114013a0550f0245200340f14004002d19111040300070002c5003482d01015106d60084801950390a445162a07a01c50850303024230303554554441c0c011030035038851000d101e28222900011402056070055440b10307903c0d0601070750000318010f100041c1d4a50400c0503024001036002510350a0107072800240005840000345182442d40b810042a00320300048002800341490b030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 90186664 1250 90185414 90185423
    0x50c01051c0903031d0a050c1002150112110a18050705040306020a080a05071b080c0307020d03030507080f06060901080604020f0c1608010c050d050601140313031812030e030a 77
    0x2c02d41c08101030300755000c4418000305207910b1040b0004c600310140e58043d030140050594000d090035500504041c0f42c2c0b5600d0a03103a005032400328800300031190540b00240d21003002428100c80380401d100003210020b07401d12054400840207810030b22460a006400e0f0708461140359030303100080c105d520500c2550091940040e00355030b1400d403000000c280c40000d84e40d204009180001181459004030404800c0641200c00c4420700b080300e0301e903000203030004840000c441c00100034940069a0300c0b408481d20324403a0300d00060758106990014080d500003000762140410079011300c480c2d03903030703c505444018200340380a641656809002c980a8000c1c52001c02c0e1040010440340c80500c00856500c0020b91b6012038040025500c40f5030030700b81c45040e031000700031030b00070090f2217441500b54002c1070380454181000041003103031154528040d8001c8810100315180c40000b0000c140c8e108032442d242c00d03864032480f186642000c900d69070b21560034000800780890980d140407641c90a00c0051080c40c1c02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 90187914 1250 90186664 90186671
    0x6070f0315030b060405090607410c0c010c080706090c03150c080606070804030b07020c0d0c15090503030a03020a0309021906021002030f0609070c05100b1c050c01051c 74
    0x16032810f084292000d03207945114078103050018522040000d15540b00d01d05c1035403030310400b188c00d0307604101040d4078428201e00b6400080000d0751100c03109081c0000d030805013100c81d54480f15034002da800d01e000014130a04218191032403d01080d1800140d920880c0c0041e07000074a05c0ca1032801d1049003001e5400101525100085480ca00b8003580c45494200716603220628a95160010001507126540004007010014042800031684e000f003083d038009800d0046915a64140c40003465801640304111105111087c040c44001c4c1d032a01880d000b5240b40c00d01c02c0039242403034002516400362001801c101075000c02d9004602d88a5017240340790a4000d8000045040007029031041829030f03014003030145c07203158801c5d2840a02442107030b1081644102c00d070f009482d250100f1640322005001d1300f080103e4a00840081a42400f5020a070b407040d590014a102e13a2006015201882c01d6003090003800124000c0702180001c02e604182031003d10344580c3e5081e294002c0c515020310fa122049070300b0706c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 90189164 1250 90187914 90187919
    0x3180305250c0b0912030f0d0c0507030c03080606070614010603050112120c030e100c05060901020a02060109020a05190c03030609020f0d05071101090807170405010206070f0315 78
    0x100803008018006800d031928920340d10603595010450300c0000010038842401c0420403150009102501c01400003c001e00c003100d000c4440d0b41e00d076403c50480c8006200e00011240010f000c14407403c0341c0100181000c0781848404e07200505508400f6102800f444960781c0000c10f03d6569104a81d0115400282040085441103852918200034050710021904d0840085101407402080300d910360350022690f410300c560b80034102c40c0180d40724422014010000d80009655441e04080b2401d0709080c0da030400481d0381410010314202000d080c0c017120f0391041040d0318195501281322030542d8450b96015035a941c114604075418881d00e610960301d200b0f03000c50300200e10303482503814801e90f009540c18008152102d043c4422803150701581407418600b004802000441a00801c0c0d100c80941003903c500041264628207459100c8004c403488500010030784108071801e18241038058001c01c130702d810242000c0010355102000380c114424000f42100d00f0001c58402d070886400c60040040c461a400e9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 90190414 1250 90189164 90189167
    0x30e12100203180303241503010305151f03020f060705010903080f100e060904030e120a02130501150c2f010f0804020114070516080f1b0906060a031803 67
    0x402c181c0b40c10700b42007000540001400e0001064038041c128180c90f555891455400064418440b4240b2642005070760320580001c00c1503d010314021402400039007c50004010000100280100f5585031b41040c82e03080606011003064074011360354140c803241405011000060b4160044d85002896907080c03602000406a000d05214040d9008900703840700d41d15000f24001c00c0f80322501410760041c442c0b0300000c51905e80365010640290080c2407811890000c207002c201d1081c4016071400156000303803801c1046081c03180c2c1da040180c00140082100f54107000d6032012514809245000b040840c3c20080c0a001203d200c0403000b0f1418002c03004901740c8034103000e80d03110b1690081c0340800d42901c51088201d0184d405544030b941e059441900a200c13914141665400c209800d80d81c2d80715928112282060200d07001c0041e0580000a0006440310980c413842d000403004001751522800104a21944414007490742006084401c40d8462103c03c204600908052804446d82c0c0c02000c0c8010625 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 90191664 1250 90190414 90190417
    0x60436020a06020a1203050c09030124060302180120011518020a080a0e0a1b05121603030302030c070b07090e070e030303040807020d02060d060e060907020a030e121002 74
    0x8900c203946250101d0354961040e42c980071640c2025103800d41512010900303510940c044c81d80841079216031410700318550046400c4400c100d2444400c20010b2100e11000151203000200030801882d0561425140f20400c40005100c184250f041c8980105100809440e180421460002070402000300100d03080311111180c1d03241c41000368022803001104845d080900840d0046801601e03080c0c4107440d071305540b10041c0021f0107001d0060069224441c0004c3d00c00a200d0140765a070560030041900f4182001400c01c180c070b0303c80d01594846d01c210030051031001c0342d01d82105e030981001604c0340d5a8544440d0103105801000b0308810203031080281e00c07a0800741c100b0a8481140c4040c400d0380c1e41c05015207840300707200d03c440c5c0d0560041c0000f40015603c04010714001c3d00c090411064030f8581d0f0301103005500511140046c0070b440e076000f4000115100d0195610907c2107483c0340d21400c162501a40b100d004140203010422801e0305082c03141c50700340e0f03001d4000074510112651203d540800c0400ae = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 90192914 1250 90191664 90191771
    0x120a020304032604120212040603020309060603070e0a02071b06030207060c030b010c020603100905010605190203030105060a050c0a0510020c010e0a03050427050106030b030c03010c080604 83
    0x32515042c100e0030301e854210300c0c603c55a0108120100151190307114072001c48402000c910442c4905006203e19004000103000200b441d5140940c40e807e200e030042c1c5c28080014082c0e03000750310007581000200c0030107940c540c00c040d03481001a038800c8182007007130b03000d0750003846842c03000070010001036115071682c01801c21a004410030020341020403000c40695480208640c006a106003002015140010040d50008204190b59450640e12081c0e00b0039210300742d200102103000400c8441455078280031407601516188040c5184d581000c0000d0302074040c0d10904401c000c008561028113100030407024504a401c001100e8900d02ca0010750006540941284c039650350030305098480784d04000540390422581602e45504150a20540400c101c800c403044102030800c4119640c031011861240902a005555020900303000c02e0050501d01803580840381e010780e15044103502c43c150701c8036072103411800480d408101da07844c0d0407003107506810f54103d030002c0e84c508a8a041c822810002c84000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 90194164 1250 90192914 90192917
    0x709080d120506090c03160509030d0305010608070c120f02010f09050105060a0506090915030a12080106090b180f0a0b1201031712272d0703030905120102120a02030403 74
    0x70fa44040600041c00300554101c0a541024804184506400700c8a4003000409140540c104000e51002903c0e181520426402003a43e850041c0301641d44000400d9000c1ca150411011039030305955203546070495100340c601000607110000015038400c0d0468414143c0400040c041d150f11800d1490003043d090740d40e00d10601e0807041c002020b0400350180ca4400034010201a6580e888401d111400c040d442034403030b41070003030b860808002103c007c1502100e00b03030b607618140c1543c100780002d80b580d10035400c4400102800e002c0706884903c000003501602c202581c03941e040388000300200e555040ba0340c01090702e0710008100400300800c06810941203d004020b905410078a03070300180d006200b60342110100d501c0990000703c140e078024520b81315030b0b94600003840d00503460200c150b0400301c000b4118294a80414588007040302c007055600d94002100d4003410078689103640c050a0031205104150040c2d00d60751080302c1e104030a5040e94402d0000901e403001c54a070010341e40000b517108640890 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 90195414 1250 90194164 90194171
    0x40c0b07050c10020708100507030b030307030207051903050c12030c0312150105040b071106040302040203070807080709080a0b15040905070303081b0414040e0124150906080709080d12 81
    0x10f45640c400a44035007256081d5001e00044103d110052000d010014144018151564502c1805460400040c201d481c001c1e405001024240010818500c1c44943e19040003901020305002146003c07400340c04686c021a030003408515910040c80c25130107054078900746d40c0004508a031410004155061252040c044445805500c540055a01c0d0280d8041c61107200000d0000b40002404031680e1811030400500540c181540caa0028044ea84110b40800000d600039091140a40d00038100940081060804038051400d1007020359560b142c000001c3c00a040e110003290034042440005124502c000e44140501c0f001420415034a254605c821030004084000040c1a28042e004034001c070b0160b020303003620301031819800c0d8030183d0541c10465405543c3c0e11204100c03039000d1081d9080140f08001a841c42840c3c201c0420300150790390f000105221031583d80c400204ea00c51083c5050b19100e00704845503850340582140c03243c480e90800022407150b0f0350606034150b000106040c0b4254132030f2061 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 90196664 1250 90195414 90195439
    0x19080f0c040504081b0c0d060f1a0916120501030b0405070e010e0406090201030212040615090b0609010f020a0b09060f010603020a0f111009060902150f0d05040c0b07050c 75
    0x411114102d030003910a1900f4030805410040c07030400e845c00703501c10504807403600100750005121540d80850072079031f0960b00c0d0480140d0780c585004a0b0340c06c0d070105c0c0d030031000d680e400000b00d20142001062604880e079001086415280180c9028079862001c0c6010030066860345460021040d05480c140e03030501c6840710008441201c0748859040c0d646401800310305840b070341e5900e0040d1940c54002c81c10701d5001c0c03213040c4a82c1c1c8120703140c82c800c40c0101e00100e01d01c1c44450899020100d250869001c442c02d03c0c285a00640703c5100722518000c080c6410039107031030002c50403030401075202c2005020601510600c035141c81e0024806000d2522071010400a0340c2c1d500042c0c00f203215141018001c5029104d400380c42d64081c6801c2c11030b95040c1000d8400102c0030b01400c004661100108a42041d55481a1020342c06c040030080c1451446140b01442e0420585000a0b907000303204d8a100740f01e0700c0b040050200070302290441c009040d01d0342c02e16120400e034602652180c81680510340158505402c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 90197914 1250 90196664 90196669
    0xf11070602040305010b120a030e120607021b0105090f09060411120907051e0108040602040f06090305070e060a030807031e0e01031109010f030f090f0c030507060306150305040219080f0c 82
    0x690387e81c12a19401040c41008685e01035481c0c40030151001d80c0000d002c0c54600000009000380e030301c80e1040794003074110941a60003d80c045456400190b04001082c0815070b01ca850b450500390040c401215008003503a42c080000d005003918036a00e400800340820007000300702e880d080090241340b400c0d05560686469005100043d04001d481c010f0301c9000000c0d407112940104942c0b508107000d030801610313194a95040046a80145e440310340000c840440400034401c05103d0203001e04001d51b40541c450a00000044d0308001601000c0c216290000310030003091300400c150b850040300c01b81c0780e0b11954901c07900a4046030300040c2c41c901090510117120314000b0f89038100c3d090040b05844a43c407200c0349890850003001d820202c1c10b40550344d01003020104150045418141c1c3c41420078003100b608514100303040186a0f031046081c1030038180300f4071184115248014013056945070004241d5114000141203404450410102700d45c4c400c0c002c43d5000d008100ea550b9142520121400092072005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 90199164 1250 90197914 90197929
    0x4060b030c13020d0902100509030106090b0a1502030408062401020d02060c161506060906020f0304031121070f0503030f0403030e03031c0501061b0f060f11070602040305010b 77
    0x4046601a02001c002e1810100c00e5028107042055180001483d0a0706c1c1e0104040016500c2001e002c983c002c150324120786000d01404001d00000082403007850401c001003071540500d40512240040c03101c08007400e103842003040e81c0013040204110340302820200101221505050150300b0840c00c1040b00ad2105d50000580c500d50120590007002c050740c0b4035002e1032190b0000d01100c4948110055044003040b030040c2d4080d0701e04d4041d50700003412071412802a000c071390603900000954000c01d0b1082541e020100503281280d07003200000c0000700840c40000c0d048401440a030740c9411601c2ca4100000701c000a0500030340d07400781c101c413007056290802c26690b40240c0e42c503c0b241d04410002400064801c5212030400340001d01200e040c982d03171220181510030315200b00b03255075940740c0c01000102d910480d0b038902e0000d406001001c2000c2900d411082003061000903000e50f0700c48500d40740c06010341e0320500b10700207c484843c0d11004549004000ba610901c0281c4407903003000f4005c291454940c9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 90200414 1250 90199164 90199183
    0x10302070b040623010e0601030e07030c03030810050904060c021209150a050715020c2404110102030d02040909023a02030102070206031f0906140904060b03120304060b03 75
    0xc001d050301d5035556140006000103035007811042c07a8680340c02e40d503903403601c0c1010301a1178a0111034409241c80750005046410403c92030a8503400a001080800d00ca82c1814007a00d0305071800d4046691041051900034509070f01060f01b1400041c2040b05018980e840022088059030a48181d05581c945a208a000301175503d54401200017580d00701240020060503c803555082150400d1004e85403008001c4c0201704040c080b5400007070710b0203150410301041d08495415002c03203485503134058854003043e130010700041010034640c0c1c603125140e000b041602c5000150003400e540c0d403519130100d80041c3c8044d01d022801480d9020341080000510380365008440341e20a89851040c4c0d490b110320845c0f00d205c6c241a60155420009000540c0700c090085210b0f901d05513254a003000074078202e500d1405698070207002549000814400e64140b040d4006a0b44411242d0590319161814000014110091041c1d030500c10300110140900024001e98402c5014100030800d4142600c10f050310390070303841d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 90201664 1250 90200414 90200423
    0x709060503030d0f09050a0312060510050304060203091e0f120903030f07060f02040e0f0708090c010309031106070e0108070e090406020f0904060303031a040b0f121c0306090b01030207 81
    0x91009084000f5142d01020062103111008181d00d141c5888080c101a41141e0a0303001440c1c204104155030b9181c010140182015030382d9003110b124810000b051030001820003010071b500080818640e910070440840b2401d82900c603000000b8121085582e200720a03401d04085000d40102d0348450004142503412001c6c0260185181c000305560307402d04c5038401c8208545642c2d440c2040351603015144041c1000d000d96146038166400c0054ac11001c1c8070b0010039031800c0260141c100300350503c0c00310301403001032000c5c00c011079594001d16007039803000400e03103c241103880790500300b0018507801310030309105440070b89a5410545a811085958590030144c1c95040359145002c240094900d50081421209580d460307410b0a0710704002034203860140d40164002900c4280c06d84040b41070422072041010221f50411402e180039010801c0d1207500d81c002445160119400c928140d1b080c00000451400007540035070002c1d2801014000701001d0203004442884c0c124000c9295000b0320131961707000d422 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 90202914 1250 90201664 90201667
    0x1b0203250206070209040309080f030703090509460b0f030f120a0908010c08060901120f11040905030309071d190c03060b12040b09160e0c090d0f0203070906050303 72
    0x11a000d1000205c4082c00807020048480400625050140460420300c10010051556240e4a040090801005410080c4983c900340c0030b2010301c0d001c110000c0c2520300020300030340340b90b820740b4003c8400131541241c541e45081d801080b100c00c1800d0394004603101400302c60075001c12800303000781030303880d40f4500d00c0c2103582d4843c500c20505100c070a0060080c3d80d015140014145032221101400d480104048401040901c002e110951604400c40d501414500040c4001962581c03101c405103a9540c1c0c2c044c00e41040d241c500e1440e629940c01c0f040328a40c209080ba542c1e424005142e81e51011948525241d0110603140300e518140005070060061903140116001d40585481c1e50000f00301085c14041495911000040d454840c0300c06031005c007243e200041e605203403034240301d01d210303500078400006074104540c45403103841c1080144099031a900d10144040c0e50b19603200100d8402ea1030b646034004e1104021600704104a40043d40c41031080d070980c0e01c0d1541d1140e46c10180c0f03903e070107a983e05420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 90204164 1250 90202914 90202927
    0xf0a0320091003150512010f0b190501080c090d0b0f0a02030c09041e1104050a0837051204030203100b0307060c08130906050a0e01080606090a1b0203250206 69
    0x70913080b1803c540440036944420729682c1c0b001880364040c0404801269440700340344040f014245c42640319410003980c0f00b20403031408120803c04030601d401400c0c1801359110208840c00024410f4a5501c41c0140c2040310100f540d0400c0040808101c3e0029048203814000403102c0e0558002d4038011001403e001d81080d4a04041001030014000c07a09851054050b2250201c180382c0a01040b10082c100000ea5a50802080c001100c60a810110103a801448100c0318000b420030390b9803240140900c252040313040b06900000e0201c180401402500c00e190b40c1070a80161b4000401c00c80e0320071001c4a40c03180d0f20401c0b50091f5120700514984c0354000c000d0410843c0c0c01440604a1203104280382490040c034007034452a00c03051500112007035680ca44084c4005e041690704940542581b151183c07566140860721a50390708024820b5024030303041400304480040a030400c00c0d030404020f5003061004030f080b500039500d82014107800d540c00c41200e05540c80344480c0403000003464011b0207040c940700c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 90205414 1250 90204164 90204167
    0x109020405220e0a03110c0306010f150c0c091a012c0102030705060a06030b011e09180209070c0201180b1b070807030b0a2306040903050f0a03200910 66
    0x41030b074040c141110740c0320900f0300b0f40190203000402d40b89209856800030784c80b120390444e18044410340c420b4003a500110041c847c0c41d4400591404541c0d24071404440e41589150440e035040ca0400f0003001d01c64207640208955842d0b0301300c03043c49451220354594003000400112800d4800d450f5a05200d06c1c01c0104020560864144080041040c0110b928241c3c507692480d18103a411504c1e040e245646403c10300c00c2001d1103500702d0040c012203801410041041c0d902052200780c0344a0f02d24240e5403903014040481359500321242c99600100540a00d140290020b8407400c050b00d001c900040124500209500102090909450714207110038140500c02040440c0c4914288480d0004d1140c0b400010300d9000c20003141001d1481400740a807141020440c81c01510708070400c0c0003680304444091842c40712141c480e2307a8809422900850600700c141400d035110310500003d10001900050980400b9030180c018181d15a440c540e425850803104501d204540201c045c078603840015080d107091620b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 90206664 1250 90205414 90205459
    0x3270427020316030803010503060a0e06130c050d060b030105090d0210020f07020406230a03120c060f02030c0406020f06040f02120309031b040c0207050609012f01140109020405 78
    0x1407014040360141e500248070000450503076807085803898070000c010b02907400c05100007a040784c030300c6605009410007aa20780d40c407080300400320642d410810700e41c5001c3c440207071481d0004040240c007440100d91942010800b0f003402c007118601039030074900415040c4070000341104440d085d5a015140ca80703020000d0001a5006c0810a40c11100c1801010056900c0e446044010100020300c50545841c1c503003001c12180084441a10a030310076641040441c00d001d20580c40c011061815068240262030480014140481f04140b0648007004201d0281c041c0001041a51410780882e07004c000f1400c03d4a5a441044500402c0c80078401c0a0500504203030508041036203400c800d5a00b0035007103070046450039070305c0203c1031101e1040c03800b222640d060502c5180c101031280c2c40609000303030528000c91400d215101d0340ca4104681590214030141c5415103210b9200d429841c114000c0b401226854003a09400103900003801c0c4103000080d4290042c403c590894401904010000b40c00c40d5229904 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 90207914 1250 90206664 90206741
    0x70312030b01050d0c0e011b0b04060e16030b01140603010b09040510090e0c0909030a0f080c070f050703060507050a230c0d081801090b1303020a05032704 68
    0x43c020b007444590395841c802e0040900101040d0394582014944000041440b050800712444030414054a900460500f14205500541101c404501c840c001c0440515113407407101c030f000001c242e00a01004100c84404814103e510340c0d962041b40301c05d808100711b81c601c0b00788a11800650100601101c0e824640c2005501104140900c03030704070b69070020101991000b104011007604151040c56403860100c01c41604804500300850a000a4200143c008041c00301041c0601c0b02150005100900c89000c50f410103174004100002d942043c5401e541d0740301c1901085030074078109070015481d00d03c5a000da400c6c40d2050386d181400800d0700d4481c108849580c1d030740880c0340a0100000e0040102c1001002c3d260815591802e03143d11300354011460100044000200c1641440d40210115540b10340e00c0340c0005500b942c1d244060b90901c1c4c00d91401c1c07403802d0000e140e80000f0800728400284c8003009403500388890008082502514204401c0314110101030680c00b001803620300340303000f021509059 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 90209164 1250 90207914 90207917
    0xc06040b0106170610020307080a05040603060b090306060d060219030f0e01050402150c030f0a020a020a050907020d050d021303150b010f120c09050a09020405180403050f0f091c0203010509070312030b01 89
    0xa044000d03152000e180e8000ac03001004140700240c01c10565a041c840c440091000101490800c4d10710750020380c4030031002d80384d42d1159080a8003001071056a6040b910309800721540c00e01075000e604006000b800b107031700c4840304191912480c071241600c180580d034452070303000700403d100a004e03146007002a0800842030242d072000b4089607110b0342c9003a000b4000005150024182c00802c1c0c4100000380c229a00a140519140001d00c0b405070b40006018104000c50b0a0654481080c415004000d0003841000276210042d20b0001080c020201c204110f5903004150600103000208015190740c0744c0d07a9007000c001070650300b1790b0480321400d42c400f5510b500c46150409003556240c2c00035840e940c294100d8034210b94000f800b0000ca203040740c500304110429012010152401d920064050300400010080b0324800290880141c9548402c40e844100c0041c401d429844d91301900c4280c0c00d8a41400324041c0d803901012401c040000148036003201d034049485946503841144c101d000e002c403020410b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 90210414 1250 90209164 90209167
    0x90d11030d06090501050f01090602121615060512060c160302010e060c030709062a02060c03070b040c091b0302180d050a03030b010f1b170c06040b01061706100203 72
    0x100d140054018040100f80d40503010446504003c03c1214520b5a1030071941800f410034802c00100760082084003140714130034901da40300da036520260840306030580030051a1102c00c041c4c2c003110290a51107241a00c0040d540b404844a160402956a0200361070301c54061800784100d03a403c100d2544c0d8400414428400402c0c8140c4400792149400d105a40e0000c0b03584002c0100580e0079072105107880100090305e085451411042c600f40220b07502d4a1142c0300109407544c0010541d11413408a42d04145882c08036030356403d560409011502d020b5904480c0e0118a800008040c0098000e01d0116010541009100700300c0130001d800961101b41090b1300d10300b4403003402a0701d943e003034003852480e8054009410800b20500d8020101c0d903041c03c400e0705108101161061460b8803480b541d00c284610301030701c248d5518a04181814225142880c903008200150032005040007086460186108216043c140c1e600d8407000e0b9190100451700220090a4800140085c5001d0948441903052401a42d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 90211664 1250 90210414 90210427
    0xc1202010905090703090308070504031e1406191a01050d0e0f01020c1005060319030302070c051203070201020c061c150302040222081218280f0509090d1103 69
    0x10f0504402255490042a554906102030540018045520488034940241351500750743c0c40a041c48070407803458010408143c3c01004001d4090940c0641c0039040c0200ea006251232420002c4e524000c2008021482c100240c0300b031208060801d8000305d440503150380b41481403229001d0700030030f40c1c2461244144180048103511000c28401021140d031780b000075204102c00d90003500d0644002511503800396121456801020842e00c0014410a5062801607520b00340c034208099000ca0903004240c0c440d121004400701d0a0000004142c002d2003078094404070b0914804005071806007072084c564144488148076030400d401c1e4400001d02652890041c1c0c015203980210382207820000d503038000c3c2e5041c4800000c00106c0c8980031030080001c4001842151a0030b03440c01440d00445c003800d008a075400141100039501e85800b094004048c60306000d21906088800107001c01c103214021040000c0036021500741014400c244c826a4090001c0c0000da6962204942c03a4036240743e035560500003031044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 90212914 1250 90211664 90211669
    0x70e060c12040f030308010f05090106050f070c06050a171009090303020c060403050301030c12021507020d050a0c150801080d0809070e0f01060908010209010e0f0109050d0b07020105060a030c1202010905 89
    0xa440a0003d401c1907040c2c1900f14500a00001c0040c1c01800c1d9041505408101507911011103a05582c007a1401c241c44982020307560b491401040c400504422169101051442d03001015001401d5103a9a0202682204110780094001610603d50400040c8002d2200d4520380e08400e003403d110b46001407421203000801800c100d020b44044002071000030040060080404c09440074100c0c41304039070b40d6003010381d0001b40792079203405c00000c0b00e03080400c02605540e5410309905000d60080256021040d1514090410960500490010035001c11026000d40d105500080c1a61660001090f551843c030006442c8454010304042180c46000b41c040f60100c10794203818080c0c1c100e03d54401807541001e5010b07000e9051034202050b143e10600420358503a9000c1a101c80c4000e0540304d07202c10301c40810040340e080100e43c1200d600302011072103c0f802c01103158040c91042c0308590081081e6107038203040206089103031202804510340c101b003c0c4140034046041807442881418086101d5030f03151702 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 90214164 1250 90212914 90212917
    0x6030603240115080f06010c060e0316120e01050909041e03031b03051e090106050d1a010b0304080706180c03050a05100203091011090604080f07080303070e060c12 72
    0x100324003154084004002103072402c0b000f40040009403c01c2412403034405d00c07000712500024003a5041000b0b8417880000c0c008550702a400d440c03100f00980b66107196a83c00030326101c00c0440d0807a2040185d1105203686841a0108041007005945071803410b084002041140310002d00240c80d00603031111510308100f40001a014440e10036140440c45d040f0980b60140400c6116110000303060904e000c10440c400814000700c04c15021a9842002d40c84071154103006080e00d401854111005440c403900b0300c40b07961441c5081c0d00300d0003c12502d036a01c941c0701312014082510020920f030800d01110001400d240c000d0782c8605c4401e4005a04c0202a03150320281e265103034000c1d10203820000100003800001d00001250000c1039009500c0c4d800c3c001d110550b6404480a6001042d81d2200110000c140013000c407540124000c01c00c644480d11880c4450b00c0f030040608a60987c480c0e01c1d40007401103004070a0324840d60098480031003404481062003e5030b48064400c07491405035803001c96036460000c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 90215414 1250 90214164 90214213
    0x41101080c190309021c030906020d02010b130f0e070b13051c02100c020a060c05010f05060a05040b0103020702040e0c0a06030504030c0609080d1406040b1507020f06070c030b040215070c0506030603 87
    0x2980d03003548c1850032001070305111204150038116414200c61b1201030300d4824407101c201c450b04000140d44542e2031303444002440203001c400d046000c0c500c13001604d40740642c080e260040c400c00240c40995514400c01c084c001e46507003840300c01010042600094a800a010b450100d81ea003800184441d5030350008116034425000000407410188801007800002d1040003034454200c0000c114a0403c44c002a105803202d00c5560311030307034540655006903403003601554030341766000c4c0050140c01003a0802c1070310b50071076140789402048000300014000f842801070038000e64068a5801e92061942c494501501e00c03c0416143c904d010401440b41940c0e62080303140c0500c8200455030347e8101082040182c4465400d003d00c1904007a481c40e00300d42c0000c1c2181c40c83c980c111141042c103130301000850307050300039120054440403440c1070000c107004651030128070840c0700300e500b171180b810041400c004600449101618044030b0070000c0c066400e00d00011504000014202e4000003404581031106d090402d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 90216664 1250 90215414 90215417
    0x30106080f01080f100c051204050703060b0319020609040608060708040c060c03050d0513140309090705250204020912250b0a0c0317041101080c190309021c03 70
    0x40040020301604052a2800b5081e050054540b08562131803081e0341c0c00e0b44440316400c2541d00d80c0b117021a907001d98100d924001c12a4100041441c0c517003820350312072000b03100c15a444d50030014200f28510300801c02c0400042c9420b03403910325000540912510303800514203950829690f10001c50545010000a80708003c0e9079181003040c42e151030a086051103e80c07100d420b000c00c02c5255000281c1140644103110050440010540d130b40807195002442401c03005415584100c00c43d0100c038501000500010806980428454643e888229500e2140855802030300b442c1d540707607514014010070001d09040c0020005803e205035080090391382c88140100d0b41a60380001c89400d113006600300e03c00307075401d01c006001c0d5071280b800076550014030640410303000300102c404022003098054080580c010a072200d00d1002840e1034030b0014140d00704460b00038040360a083c00141d10102080c00c9852180e1400598001403028020030b601405c039400f81243d010000888220842c6071244104500038081d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 90217914 1250 90216664 90216677
    0x102070314010207060609151a1206150703020f1b0a090510030b39031305070801020a050c0f0c01020304050607061d03120a0603031e12060e070912151e02030106 71
    0x601c2d5400c8c28041c481c6e400300c404c804400107010078020300703c2e081c1e814405a2140c80641a80c456000601d00140d449811210321004100d84c010306900092101c00c0740d4101e42240c0c40d0781c0307801070403a02c030049420a40c3d9101802520501410515030012504001041d0b034406180e901c0380d8a4140085d0220380094031248408040d03642c00306112102d050034440d072040c0e602d110144030440402071100800c5984070a500c88500b204205040207103200600040008545495810034024007070361090103c200207200b40000c1c684034003c041041d00c14003005070019450a8a0300c0184200c68000e45020385816039500302c4460301290a9881c1034101c2001070142d030780d0f18013022407142d4201000d000c1401d1185020b900b0310000360401c04901ca015a01c10118940c080031800868020031000078003880c080c00c0c4500021082c82a5181902070255512400c0071161501e0055004003054000a02041c2500445400044160380322101450344410140c0e40b24805205c3e034000e0741d100303034060800a2003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 90219164 1250 90217914 90217931
    0x10180311032b0c0302090a09020a11030310030b070e030a0b070e040609020c010c0903050a03030f0912080603120a050301171603080310121505100510080105040c08060102070314010207060609 84
    0x90761043d641c00c102c06080031803c0049140101d10583d4140c000c400744990b00082e00c0c12014011240c0340940e0802030308490b90392800180402d019040c902c002c660800c8000c0215113440c2c0950b80803961090090004c15010b07065031140c0c4182400500000c0901100c1014000307692124002d82010b45030403a400340c5d4a030307a0016200c2c00c60f891520f61204000c0c0c0c2c40700a02c0040d402154110300c036038240c41d0224440c0107030340c900001054541002800c0441807080c07c2c00d141d81100b05148140802c8091b03490071040507040d0569486070712001c1b070005100b080107010b003038030005804003031014003000c03281300c444801c42010f170348600741d041035910f24000700c200318080122a220102400c0c1ca80b980700090f80ca250744000b11315041c400140310440d10390300000c0503501007542400090000402400c1055258000a004500c0038090342d8011401c00c82002c00d500c2c082c01e240c030700401041c0d0080007120700c2e50304c07001a400200005180ba9540030840180030a101d4010540a0840c81e0800070711580c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 90220414 1250 90219164 90219247
    0x60504120c0213020d060906080c04050a1b180b120a0b0a15050a030b0301230603010b013c030203180a0507090b0307050907050c1018031103 62
    0x460364010070000740d07054410050b280d0710b02002ea403014211015884080c100014800307461190403007840305140103030000c0c16507400192054040002d9400700081d071a1203d00c1400e42d0314185404100f00400c44140e400320344030300f92040b080d583c5141a800d44039115658070301d66920400c85800303448144000d205858a091142591008044540c0b004862800344103040031041c1d40d0007030007445000301e290899180a50070a84034854000e0080206000700841d46010004402005030f100140c900000e05500b0148500104000e0584079511800003480c02408040c40240b2840c0c1a020000e0b1540b98440c0001c000015005c0c2c15200540c136446d003856107400355448003411401c1382d84141c0022002c83c7c000302c0d8010551b81040c102003001c1e421100400d140c203819034800368101010400300b103001a44040940b004039041001e42d00c1108a2640c0c0005841241c214950802040704107400081d0183c890b0940c0882a241179038240020459626002411070850418407080200010000b0303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 90221664 1250 90220414 90220433
    0x5120f0a140d02160b28050c07060e0306060f120106080a020907031e1107020d0803010911070b06011b020d0b010608070302120c090a03020a06030b0a1d04020d1e060504 74
    0x118200e100500c25640074840030035030004c40c0d10030721503445070021b40031062000c40205869039004503050204149000f8100502c16488219030b0b42c114024804003003581031080c00300320803900c8020010b00301500e134242000034040022445944c0840e24001c0c0010b42f840030b001d09401020504040c00758400c0c2d40c01030001800004060408142c600900300001d0a00c4a10840a6400400b40018010b0f050020304410f0310074000085d5000440b100c600e030801c542400154143c640c680010300c00c030241406000c1c4540503c590041185e2042000114a5413140d040c010401e4401c00710040c0c0d0401d20703008038444a61030101520300e00c00a00050000c0350b0030940613a04606107140031032414080103641c0c2c07030481001d00007540c01380380041c9010007665404400c4014540052111898581d983c6001d0700078501c075031239580901400400029040e012200d0041140341d8881002a999038650801044981c800c0c0c0c1250000100c603da581c0021b544151034130201d03c64480011642818144051038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 90222914 1250 90221664 90221683
    0xd0318020a1a120a0f23040f0302071e08010f11070303051905010b07060b1f0e03030c010203090a050d02160501050904090c06030f0f0504020f060c0705040f0624050405120f0a14 78
    0x91b0803411070b034680000c01c80d184040d4402c0d04070a140946019a00d800c90030f25409602040c4e011041c0300d8411003840d00380b030480c021a8000c8008000507914540d00e4002e0719103c4440e521198030901c18080032038007036044a0340c0040ca90061410300d4007034100c2e80742114000e80080403625000300e80b0000f00112440303500b10030007044a07050015010210032101c07040d69280380b2810060424210142a101082601e500c150002c00940d03d82c41c1c82c0c00b5440e52000b9a01058410340b003151001d06d43c0c2400496919034140318402c2d80c2c0d20850420005403460381c4407a41450b0800d0b41c03002454086110b40b440316003c1c00d03d5030f80c04100f8100100382001a500252000011301c1e103820107010040c1d90b40e40d580c0c0641e600985405888030a407510719070030007401b0fa1200ba0060700388a0001c102414a6100200766444000350040d690040160061085d10030024800800c2c401c0005000e685013212004682950103c100c0d120701c0020096581480d0b403034035003110003c5d0141c45600c920304040c840442c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 90224164 1250 90222914 90222941
    0x5010c1809020a03020c01090b0403090b180105070f02150d0e0c0d02090711070e0f010902090f0105090d1502070b010b0a020303040b060d080307020d0318020a1a120a0f 74
    0xe4508140060480060580304215015a0024600100c9400307a010b4031400204100200402d40040c1407490b50040d0489003140040c81010011400044003800c0c1c90496006d080815600e2004200566a6500044042e0b4150aaa01c03c100040e6156411048514410f2003081c0d12880400300400070b0701d41054028000790030800749104940c9038041c602c000705404503824a030361317207402000740c881900c0c0491f450800c3c010300c500480d149070020109030150444014002d004c0e0783e40d9484a049000313143c0500e61101210713a583c24258407a030060002040010f14032417800d145030307441016018003100d4420f10b1603000701d00c06040c0094481003600403c141140e661a061b00c0001c020f44070321004200410700302c41c0c040412500c1e02d40f81e05002f800750340710b41d140c3e96038201040080c0d556a030060070303140064200841c0b0503402d6800f4800c0341295501400002a050404481c0c8883c009801020202520288101e0050048000327500d8003624000c080060320901041d84a820b54004000100c0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 90225414 1250 90224164 90224177
    0x40608060a05040c0e070905030615090402151b10180b0a15031a06120705061218010203100317070309030f020102070509070e0909060609010b160203150405010c 71
    0x2051410214800354400c1e00550005050b55903480c140301201407a4000c280c00600c0001003202c050b070041c46910583d60110b0440300c4a0303031182a101da0100725a105107412196490101c3c0c01414503200c07100790a0a070542c1142085190b800428201c05d0020184481d0b903c0b240c01c0528420b5188102c4540100d1100d4640b800328498603617500d85c0030098007000c0841c0c1d464100505460784003120501031503015075060702000d400046250004401e46e02c80e8810207404100c0c02070400300081780400c44030301500080c20b003031908030921030f4040000c0c020000c0f40541018154580c00c00e01c01144074030401071485403807600f0b40c20302d103a49158001019140351000c01500004c650007100140840307a000c5401e0012120500c0100d04092240d030009402010700c9045c404900c1c0c2000b881d07030701440c1c2940c00050559403044071907681e800655410313400c41098401408401d949500a250000a011060502003c10b0740807900c2d1036106209003e42030118010b105c100442030290301840501441c1c0039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 90226664 1250 90225414 90225419
    0x1e091e05030915040b040303051803060f01150c02121e01020c030904020f090a0e01140a051f090b04082107021305130c030804030201020708031201050103091103030c070f050406 78
    0x95550b032103091a814410300100076800d025940c1c00d0b04803030242044c1c0041c03548460b0f991402a006800c40c5451134074030985141a8041400d0000b00548074a43c1203000f100b4503460030017140d60100c80c2e203a100e01000150f00d100c0025071218403c0e6040c01108000401c5400760001c3c412580251441700420244d0040000244e001000001c2d910002000c13600160f4134090104500f905104200316141c1248213540000340010780306c41528122181950840203443d600702c00c0100d0201e450188580c04500100e010400464100801c580d80035035041890000d502c8803000075080d00960302410b459446503400c2404c0c50020411401c040820100c0242018050390015403040c0300100c99056455039031000aa04030500010f0380c40661708100301e078080640b02c0c00c107050568841c0c00141d0142c400c4a80000364800c0000c112404c039041e034450922940d0070300004601074480000103449050311840180b01d59501407004000e2440c0700c00040c22075500d0000e10700171120840d0311062146150001c00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 90227914 1250 90226664 90226673
    0x501020610140910030501050f0601030f02130909020402090303030a0b0102070e0f07030e120a110105010608130b070e130f060510020304061b0813090f0501031101030b0102011e091e 80
    0x4400b440741e08507441d00880e0b8490503030910100b482da001800c075608010501808110000099009402c01e07a03003404907614050404041e4400e902e0580003000c0f4051040041150300da000c8083c0d14030080c405840c014038030340024510b400c1039a8850945548464040580d0b80410804004082c0382c00c14a1152030310354031000c6541c6008204e502815250090902509000d0000b080c7c24140d00518a44071110104000c1400c4081921035606621380800800c0b03283c0144520b0f0310406411128205054481d650002d0300c200103030240e0280a0700044260750350703507590104291007012050004681032002803c070b05480e682d1b80400d002e07413400544a0859035002c01100c0c01e844044c1408400050403244c0300000c1e0b0800b240141c80c07031601050a548440751082030038121041c281d418440880b40002c00d80482c3d400b0711004140c42c1e092004141c40b54081c1e04502c4c4054014000060070300070784159684041e040000c0312042c3d9507165a9801045468100440d88507403003070094060200b80e41d0f9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 90229164 1250 90227914 90227939
    0x5040b0c09031006140102060c1201150203040305060c1206040b062512090303120b1f02160b03090d08101a040b040602210a08041704030f0506010501020610 69
    0x10032503100350005510700280c80410010001d0300c042e6200300546562000344900c3c110701c011065005002c2c6501180d44406120192014a00080c003542c0841e443c00c0301616030726007038500702e406501041c013000010460030303c00d03140329105041d20710f0364500d090201d40140810003050107102e181b40c1003044d0110345440741915200c159480d20304511121601c500c0000240b100700080058542d02c007100942a40b000016046030301c01d0f200c011840e1203010f401d01c1501c29950141c1d800c82000c0c003108003543c011b1522540b03644918015104280324001c506000d011070360304040180d060000500c0502c020401c00300781442c001c3d10b005007040c00c0c10b240300200c10384207102c0c0c102011746903d071070180316122008403001441c0c0403000b580d483c2d9840d02c01940f10100a010351030b5881461100c1d030a603041503402c86000700c2e5203945407505580c451b034030200300d08100214407150180501002c0002100f81c504410414000e40060580c2c1d8580000249406001406514900c101c01030401c00c00d04d5a04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 90230414 1250 90229164 90229171
    0xf050108040b04030e0f03030c030d14010b09011202090d05070311040b060f09010219030314010e04051c020c10051c060f0303050a0212030f0601090519060c05100903081905040b 78
    0x10b417419410107107a00141504124070b402540c50f00000412032034450001005244041000d10140030f024000841c0d003a10180c24458012007080401003201c5543c4a0340d56541079131011280181800400c901040750300340001300c11186607000110038404e00c44850004144050121004d100c209803003000300d2150301a14107115201840492f841e103441e8003e10815503c2c801c144580c02d9030040360300307004015002c01d40c008800401a0000400d90300c81c2d168040b4801c50700000240000c040306449440c4a4100c1d4441004501907215400d14990b1140311141c4501c0850341c0e002e0300c030f10815500c40d207400b840c003401c800b070700e4540001003203060350020308882142c2e007605001c1d4075110600801c0c0c0c03c00c5469800a070081c60000f0070005030700011070b201c50051000381e0f60b8040d22915402448280d80c3c0b1110b004042114101003009003500c01d40a1010f140c0c0b086090f160b450101e480108140c40103a10101d010a1521003004800c0c504a044660300b40320401c810b00c25810f0130f45401409200c0076 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 90231664 1250 90230414 90230417
    0x100b04050d02030309091f060f050a051e0a03021209030304110d06020904062303010b03060117070e0c0307020d02010b090a050c1e031e01081e1608070f050108040b0403 74
    0x124000c0c800e5503801c4c02900c000f101c0162005000b490305004070600c000f04000c8802c280c0c002d0303002c0400c1c0d151107807011241d8862191102c42c45c0001e601020b80e05070308102014541c503070760603010440a22255029000b0b0450648016031155040e188801e18080c005260ba4150f9106000300030101d0401c054844940505854028054000d41460700291080a0320701d50001d0074141d00041c140316013181e034150007800301c0c18030188660b8501014265400a080140d0550000300103204022007003041510340d031266011100740a55669000ca0440c1e030403a4001d5030700358003200b081040c580500c80040c04150030b00c001c11440306c0a800041c0401d07006420fa444c42c50360f0700002803400b03211104564545803040800c1b0240d110b600d1518000d130b0710031540d40c0d107126901200350008150307150b20681030b160035202901d0001e040c990020428a440d1410a41c64071802c1c0800c0e03000020255000060309240f00584801c508180c91452180510390145041045050400001c94804022140c026a06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 90232914 1250 90231664 90231679
    0x90f040305033706080a0b041205160525240504170a051e03030103020603041b06030501150f0e0907030e1002120105120d0e0301060f03031106100b0405 67
    0x4101c2603800302001c6070325901c4a00b070b80f14032294400d85581d1100c283ca00e4001c00030300056464030041911000403100040c42800500041000180b166081001c0c4561034504141011200412040c80582e0000b0540d003540220b15407103200c000045004580c907500301c03001c2220034500218480001c0c12440b034500300b100c440e6413403040244641308990007810704458071a00c500c407251006454604000c0116901c0c4222001c10100c41420070955480c030440c840907504681c87c1d43c0030301c009a4001802212605081040031050b152030b0310b0a00060b080300d40d40016030358140040c07154112500b48441c010301c03608005076030440703034007420349461000260b415a1960315114819405803503070004180c00740c003800090020030300556010305980b151014070342d0110b0366030b40248030500c915101c0c120f06a0b009107514101042c040c050900c13800c4405800002c031241c0c3d4402e00c1c180300030305405c110006141000003510b08a01009819080013009981d45043d0f4513054200ca0240714034494103014505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 90234164 1250 90232914 90232921
    0x504180f0b09090f060702010b030304061b02040207050307050d0507020d020d0f061a150405030d0f0e0315072007150201020408010c050406021507020a06020309010213060e030705090f04030503 85
    0x14541c00204000314042c1c0b8480403820a0800c594803050045030130300280c0300d00340003d85043d02c14003402c100988040d0285140c09d007802400c54081c080d141c1d04c1c210103500002c2000060f1541e1000b400103502400185840f03284900e49142056003001c0850100034090018401503503810354440506541181c4071101d1440e0340c6440320340707015211400b401113440c0c010074051544c400d0300e40380910f1500300c3d113200c00314081100800440c0241d01480e50540c0c046140744540d07074001d9101070344441c10f030705000c4040c105800010f403608065506400120740700c48140103400c1d8021003120b854841c0d001c02039100105c04a82d141c6c1e034442c64420010030003c0d030310040b0640350007981160b018001031030081c405054a604c01804950062103504014403801c042c51600e8895500380c00c1c051100e41c1d02420050740700c0d486110294001600d44445550300f0030051002c01c0007090341f0402070510391502c001c0c010b101410581046041d62205010300220130400203243d1254800546c4180c0c9824001c0d104d85 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 90235414 1250 90234164 90234191
    0x3010b09030a050609010204050418050d030e10021801080a0207020315130f0f0c08070806010b030406020c0d0801090f0b0f0d0320070f06090b0304150b030a0b0a0b01050418 76
    0x1a050b1002409074001c64040c40070021043d001403066a50940b8240800201001c1880001c5282c1d54080d0003a00010440c4507620300c030380c001401c0c1011400032a4191460704e580042283d20950f80c0c6080402c02c850601d2480d40c2192146a214112410846c181100d039001b00385c442c0d21500c43c0d2480c0400340c800203004601e95030140c00c2c0058014108a10f840346520f09035900380d078a1003060b14404015500040d400c2000142e000030b84200714003034003c40c1d1130183c1d00005d03500082c1044403510340a00414000a80030808000d240c8810f6a4090442d4581480101200d078a0707030181c0c4020303041c05c8580381e4030740350a4480c440140381942c8000500403607080450b200d00c01400507440b40c008611310101c00c4140018031006607010b0014135090035030303507a00c01d5030003184078866035840384001e10020700841c07401103402c0c0c00022460700c081106030511000030709100c2c8040c1c00321049002241031100c256014482c1038002242800c0c0103280030305102174503035050b03501810700712903685a440340c000e41c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 90236664 1250 90235414 90235423
    0x6090903160512040b030901060806060109092304060b01141920070e090105070915050703020a15020d11040503060c0705010605150304060b0d0305030c21090102090a0609060503010b0903 82
    0x8601501c0342d511982c541d110850141c2c419280c40e071f11503003010808600341d82c0110f6087d005140503158000881d1401401101820039000d0b1071a01703242214489220407020300c02c181c456441554001401a50a00090680e0002c0003109000d00e5040c0000225110f0800e8041d05e44510390a07c540d1140c0d201030308000903c21034410034040d000f0302d14001040d0b04807012690042460800038803541e41c035000101e50361141d81c490f0725507101d00030f440035400700d024000070708a032406071065840b801802d41f5807038008440b40754a51002640090840e0f0b00c1000762060a10b10604d19079241d245c1450100029034030072002e0548603000c040007503c00c1c01c0140942c84040240b401400c00c070b4255003140703010411a001240d064940038148041d0001d1440c0040c0f00b0103c2c603926480c0d26081d52212680603000d50452101502d41c0f41d01019659a20416800c0c060320500c003c100142e43e400b407000501103240c20651102c0140290090103000980d006000e40e815902d6102c0002d480384942d00c00039240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 90237914 1250 90236664 90236683
    0x30f130504090503070b0c070203030304020609030a0c0e100801050c030115110d020102090a0e100603020f07140a05070f0e0c07030306120606080f030913020a0306081606020105060909031605 84
    0x292408050b42e0800101101810034240250314410240da0398a0301c030300842c803c54000a52541082001070300524181001e03180c040ba02408981c0316000e0307941e58009054140d001030b50324115071004c004003c81707070303c5018000d4000c0ea8020310150504c03600303080311808180203603a21525500c039460b10147c031a4080c407103108030050448080458200c0c02a00035402010110f0017035038000008682041d60048542c01103c03004200b084c1145003003001c40007504a14441c05580bc0c1c00c02c0400c011504210302156103441c41c102810101e92189045071070f0540e2540891504029080100400c244004001da4442448070b030003030b80c032403d500d0308900601036604544003641c0340e0b0070288180306281d807052082c0d90a8004994060040d41c3c40d29580c1d004482c440c560201c6020300ca0016100140c01400c0028030318100818000d8403000f210b414203000421082c1d954000e41c03410001c207a424041c0c25080310303054505002c2400e080c0c1446480b4400c80a4514010911501107004c01008100c0b842c01c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 90239164 1250 90237914 90237919
    0x20906010c08070c050f0409030c030f110f01050f0a09021c0302011b05030601020d141602040605040203010b07121d060a0e0901170f0c01210f09110102150603030f1305 74
    0x3e45461a1800000b00b048902810b8002c10200645566504091084010840d0943c44010700501d003564200c40d00342e45c6000da801009103400d00010058020800f001d0a222480000b041502d1b0010f508030885c90028442d455860030320030a400540c07a100084088801101e01900d0710f070049090507405032a04048505c004000060214640c1d58040003450141a00f40d003540c0c030707501174004212108601d9903889410f14004000a8808104044000400354800b400c04901d00383d446001904076042603100700c00641d000a05401044071120044918003818105060038100359405072428804666980d8040c020008010461034000e19400303484d000000c20180d400d684400800d0b1280446080d14221031181100181d2815000714004c07070b030050181d45002c0c000c1c001c0000006640714158400004030713a200202981c503000341c080c0130100f501400b0403000b44041c26000902e0400f1140c48950b9500740c0000380a0301d558007100f01d620921b902d01401381c441c61003110403c2c41c404e0b00d40c002503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 90240414 1250 90239164 90239167
    0x601050d02130303080105010f11030f0904060b040303020601050a080a0302150415050103050d090b120606090604030f0305090906091608090c094003080408040b0304060e0105010503120403020906010c08 89
    0x209907220a10606a1f90282c4c6c801c2d503111219801901c2c1458100c20308441170300140844a1141054000b40084640c0100089003190741d0380e014405030303807007500b080c0c00507042203006000600302181c1c83c000800942e0000c0004510684000b512481c030144003000f500710b11800308040c052a560048035050440c0020405569640f038000d41c2d441c00d02840e0808981e0917640026100112401d8030001d505801c1c0c6044940d94840401c0909d9000b0140385901c2074040c071011010a46820a1180003071207030b100e0a5691040808124004a00509a92040c55010108442c540000c1d024810704101400c01c440d283e107409620a05160761459155040015041084249040790030b2030001c3d004d5409006100107110690104801c03481880415402c0c1d0389400c0342d0010384619650740d4011302480342903042984413459982c1c2e540c0305942c1540c1e603540f0f031b07148011423100078403805004090480c02412007158007010100b41d4001c0b480301922410500000a0990740245000094140c0c00010035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 90241664 1250 90240414 90240419
    0x503100918030e01020f06060906042004030618081b210304110907080f0a020d1b030b010203090d02120c03010504030c03140a120b0d050313030203240601050d0213 72
    0x4000d07040d10840550000702c8211424220b94000b068070302c500020712003d404c1990f9640103100c464080038240d15001a0b0314804050f01142d44145440350008924203540e840b880c41c2030075425524040030054140002d4811100081d66034000c50f00c58080907031003411034454070110103040c0006c60ac400780d400d81012400074410003420b0000c2d0303c120301c541c8201016150340002e01400120071100d250105018801080080341004c940f558000203200002d464500c42d180c40000355420100b90400701d442020180d000103400d805040751440c4203100450800b00032400183e10f180d08080040d001c0c44445580c14600d000a201c45016620054020710841c2024500106508103141082c1c0000d80644822103aa03812507080b5944032b003540ea954038030404142034150041000e100c216500004003504807000800a02c041c0c02a45101d041490002c0d141d40181410710f171400d40300484450b04090000895582c940c2510b40045080c070301103446001a00c1107800a00c54503224412811246100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 90242914 1250 90241664 90241691
    0x50406060b0c010c08010b040506030c03130516180b010816020304050904030c05100c05070305091908070f0b030103050a0305030907031a0402010e06070f0b150d08180307030305040605031009 84
    0x41300e13203e840b41d6101580340c0e0ba6a00c4200c483e0040c3d00907075600c5030082021450000303e590107580c000c44100400d002c400b00655400c1c2c5800b6088a41052a490480d030401080c607500080b4424807843c04000e00008600600080032140001c2c060703307202c0802040b0810062003002514003500700030300504402e007071a040145c840144103104903150f200342e012013210240640540d00308600e01c0e0721003e08011440d81d0560303242e04903280598206a4217000003541140c082d0554008244400107440c01034188103000900382925000140000c0c410001000081c400062544030242c051502903100c0e100c6c1c80c0a00c1c2404071590019045240b4052002c3c5120050070416000d14801d072103862240f000d5500f8444203001e0a0f00103010707154910482001305802c22400d941c0000340340d084001c06441c03440000d0030104902c0c1c06488030720001c54400e2003a8060400f48000840407402416201d00d0341d50020603920840c000d41c0100b0034040041003695071a80c50301405001002c8050001c82c044100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 90244164 1250 90242914 90242921
    0xb030f3d090203070812030f06040902032406010906090515120403030b040b0901140907030f0c091a0f0a05090607060218010807030e07060e03150709031103060f0604050406060b0c01 80
    0x10503403084c0030b84200050402000140c440c00e01c0001e4400c00e0940c1c2c0c1da0095001c074820024035403500140c5541d09140142d50901c0480c05807810842002c2c0c00e100e040b008111480001050303d41401a0b0620074002c0342e4101c1c01810444800b1204641042181014103805000e1185d20040e40200e0200303220426070150801d102103942980c0c10440350080c84108010800288980c1b03040c0c0218244100c11030074030501040d84100a401c000c03860503446031a100440c1e03840d00200001400c48841400180041424012004c030500319080c101540f0642c143c100e40300e400985030138000e0005003034181c0d40b500c005a401d60354005e00c0031500c484d07070021003402c03401c02c45400900051901c80011301d141d000344100482c0300c52080040440341d003005010340700e5a400c031005680c58400c4807000b039841000e40d40d0081c4606a6542c8902d60a840e5251004d2629912082284660003135420031a0513500b10880740d07400101201c0c046074039182d070709019008001d00d400c19880140c7c00203440206540541 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 90245414 1250 90244164 90244181
    0x70c09090507091505090109021b060c0702030f0106050105090d0302010e07180507080114040c0302070c170607020c0d0f020105070501090501020901140f03041b0b0309010f0b030f3d 80
    0x102400b07003202295003001c03e010035010f45c0e42d0052007500113003c003480301d81c0034000c800c0c0b10301007400310f100d0980d0043c0e01d4a802112605a064000107010003181810f10001c00c400041d00f00a0201601b4a000039207140902143c041c0030395007811303a030340c1458402d4100c511100220700550301c80c59200c51101c00c0d00f00442c03c10b04060b03801d21011609480c0320f0001a41212440e1601c00451441da00411014114074076802c0c08040d024000c0c0b50224060040c07a8005140003034104500b55610b00001342450002440c5005540022141003500c0e143c1809440c0c0da10b900c9000c0b14080c0d01c00d44010388660042000103040c87d8a000783c02170030400b0560080828410980f6511202c4c001c0390850b0f081880744213440340b040d10042c004240010390300d00f581102d0100ca04440b0140c2034884030240c4043c1c104030365140403a9161604421210807922900c072081314181d0240403000c0c00c0400c4255102c00403051840c044480640002100380d00e1140c88813a916402010110b800568280304040c1c404032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 90246664 1250 90245414 90245429
    0x30402040b0f0306180c0621011a031b0d020a020604200105040e0601020309030312011505070206070201120f32010e01060c050705090405160e010f03020402070c09090507 75
    0x190381c0582480c0140b4503120304100180100b03010364901e5102034081c0d0444036004894402c005811200e5603440003e03000f0801c203e41d01814581803200d41d001c0182060340444a04403c4101c0000c50399511411658842e0b403010711070b0480070b0700035244c01851007507a036041c2c0921b1000c00c44002c016404941540030701e0140b02c0a58070218440ca4201032864842100360100c4c2082000b0000202e050344403076030024050041d46d040020120100e41181c0c002003d8200340000000141304e60182000399000d109054a05603080c4111640405d02034403a0301d6000c0c0c18000276421081503240c95400080762802c060310148490494a2000700c000f1038038a03c00260380c40310805142012400c03200c254129404548883c3c42c90b440d0403800d403007525a400d0144c80034026a00b01246a486291009000d5445100141115406484607801070900b582081c0c5d912140c04004000307252003490f090341600d80442d401a80e03a055854259240700305907000c00d900904110703942007804000300f83c0f0001c42d5200e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 90247914 1250 90246664 90246671
    0x905130209040b01052104020414010305061b0a1205150411040311030607020a02150f0f0c0d09030201090510180303020a0b090606010c14010e1c02010c02010203190213090e0303040204 81
    0x1403c0055816000f110785043c003103802d5a140503a48032814080540060014000203035141c00481481c07403040c001d0b00181c0c0d0741e500801c140883c212030078040c984090b0255134101d0908081c00002030250301c2c05483c2c452103a44800200320642c688452400200f900101f04101100f07550080402c5a00b05220540d078000103144040c04500700070460345d204240c0303503026041058045c0d08000d020b882c0701301c06251003507041c0700d40090307800c1c80e200408200415442d0a62616014014a40780c0b2340030050300c10401079141006c00c0183d8008604009507002125075401401c04c0f0074040340c1c800b0301c42e18540e1048132405400000c3c550003144401c0041e00036038080076280e8450150750358660f8250741c018005174401e030a01010540074003440103070154840010400c482c0c001141d610301608a541200d840c0ca942da41009400e070248251030440301070340002d50039441c1c00000e40700b00400071030600c940c140d00007034002c400c0035074490030b80d003d1b001e480c8080003800410080b4035034a130421035003240150302e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 90249164 1250 90247914 90247931
    0x2a020c030c0d02041509020d020301050a140120030c0a0b07020610031203020f1b0d180e19020405060a030501091103060306071d0409030203191e030903090513020904 73
    0x5001c5984545540003411040c0014400d600380001000f03a044800340c2c0e01c1c400c0101141000b01c038001405c040c031148102603100c0d41401c04004014246d07034000c00c044204c510701000c1507600543e40c0c01d8620f64180017400700d00100c450090a51080000354103003401500300c240700f000215500300f8012595642150180d90b680500740e4140081030001909803000a1003684026119800500701e65034030702c0c0054140314504c0c0d08030003850802c1032200c4c02d40d0007004452006591181080c03101c54a41c101c0740d0891454180b21002c0018058145c80c1c00010a80304a1207001060b0110b400405001d4181076031001e0140b80140109000e016416140b800c0c00004007541140e28140c034000c19005001c0e1600762615003042d02c1c00ba003104c1c64030300403042c602e41e401c0d500d5545101d0310075081c2c000c0d005107503a49000705c842d400004003e200b10301808050f0346001e069003400650201601074034140012000150f09003955a00c0d040d0344003a900c034131815881a9402200c0e000340a41c044141c0d814080e825 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 90250414 1250 90249164 90249169
    0x3021e03130311030c1309051011041e0f0305060a0b010504060e01031808040602010204031110080103080c100f0228050f090411030a1b08010e01182a020c 68
    0x8540c107490800491034500600120f03501c0408031007243c0e0001c04482000c110740020460661408844900c255610240d02c030612000b4040c000420168207410440c0007240342409019004600440850814074032608158800e040a12405000006040c0c0011680c03458850391b5000200c6203503259030b0801e02c4000003075005406550681d90b0765122182010740003401180100024070303d80d2080840d02034010302040e8410018006415964000750f03a42d0b0460420006000c410310907030340141d00d01c251040b6a254410b1440303040d030760310606c02a0740c1d14071428401d00e07207808096000c020f540f4120390b40120f401c2036401402d803011000005407100440d024100d1405810301d5a100c045102000040f0515515000070940d44500a00019540c0c039492406038036a0001c507141003001d542d4500a001d148a08041c0541505103440d11003401c0d814000165003949041c4100044000c200414070500c04103900301021608031400c44c0012490840c051240100b1800a4413025010341c030441e400d01e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 90251664 1250 90250414 90250417
    0x30601020d0e09010b0c0a0606030606060f09080a06200409090c0b12070809190602040603050105060307050d091a04110907020714060a030b13020706060e0103030807080603160303021e03 82
    0x40e03002080080345a00e4068584282c0e0302108000700c6c20b01403000c0c00c03800580b01d4410a40903501483c000558030381004006080c07205000d801d60300348502c000d403c000100001a203041400d500580105400e01c0715540e00d200160034012200345000089008210781000303074004289540201c580c60303c4540d072644840407074840e5400907a01c0055100000384440d0040c07003a15040102c50040364860310921410300d21540803840c08840c8150000b9003002460340c580102c0c2e026040813510b00385075082c0340e000071b01584501501210a07640310820003040c8241c80d000340800c0840070005041d1803800d480d11400000c0c040340c00c2c600c11510319000c511020300c000780718015105030030106501c5401000c01c00444c1c1e0866021b01c070815440f9461042c0b035072a4140e124480d160b42c0240541c0b200103901c0d110b002d82e00340d43c00c2105060035003001080400da1165805030082031608007010b19450301004281400d81d071007920b00042c0384c2c0e43e500004040c0e0000b5480b401101c40f09592402c08060621540c0343d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 90252914 1250 90251664 90251687
    0xd060e0109290a0b1806150a030b0f100504090510050a03080901142a0325061811130603171b0d020706050f0c160602390307090908030601020d 63
    0x8400030503030b14000170120155a0b08403038005c00708a50b62141c04015256503101c1c403a8800040c0d10b034001310380c840c145000042c0400e00200c0e1202e006041c0f00707000510034015840b50340d05850321034000ca40c1c608040d1051101410024060b0a105a22400c091341070703511401460b800035104110400b004200e42c01a01c0114080c102001c040c2e0191a044480d0861400c080803824007040112032008038020542c03d8031004002c10045ea02c0b5030380d00307050089035566541c03400482e0b01081e51000141d05050b2000c0d420f41c04a815010340021408201d00134000341c1c100908031500107410041038a00c070405066a9000d084580d0f00c01c3d402d1761421611422041c1100e0056404101e041c410240201d028001d06034903100ea40e41000704001c0c00d0b03441d0106c61400c0310100d10340000c05000980d81480262142c20704404c164100c03241041150402031031090f00e200400b80011100c0580c3d540a00081008115024080c01000d019041c1009542d00503070744c50303001d0300c1950145114035010f42c400c9a003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 90254164 1250 90252914 90252919
    0x60609010311041a0301060609060210020f0d0c0c0203010c050d0b030c0a03020103050613060b091e03060402060c0a061a03070f080606100c05190605060406050d060e0109290a0b 78
    0xb440000c0c414031000e001c280d4610b21300010b0b40d2002c889161001d114040090043d592000c1c55640b0b05440a4104191403112151180c01003240b6804035285004503002c030300703000200082109203203a0486140301c80f00c20007541542030030603040039560b00c00c01400d8401c0001c0d00030043c410403002010707501c098200742c0d81d03000240c41d0340c00c1000d98000d030b0007182c0c000030190030000e007010049040001c0b14034582200d4078241000c5000f04031410f01d141503110b85e1044104d0300101e41401800290b4803000144000d03c00c0c44002009910b02d002442403131020742d400340d01401140d8100100b540301068140c074550107440380c83c000085050005e4900d108551901c03002d80101d40300c0005000e42191113040034420301200720141d000090341041542080301c480c0c600c04900719004d05d46041a1000504910f129504200050005640303000e051b5112590000d40040c5814080389840e000d40b65142d0090040d14503a060b50100c81c0f100c4003030708062050703403142104503654004c0c0d95048a003410301164 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 90255414 1250 90254164 90254183
    0x50c0d090608010605071e260703020c0405132604080c040b060306010512130c0306050906010816050603042a06120903050f07020112020a020d0809070e07080c190509030606090103 79
    0x281c00340c041f0b10b0180300c0340c0a140c40c0c02c884200c84500342100103461032806c403103680c00038800e03003490f46c1032002d0300c01004121400e202c0c80c24102c100500580665401030a03c140a42e0000c2c0d500900c1c9444601d0301c980c488040f03407107942c0d17502850384415100768800d00a600f0b048528a65107004011280324600585030141401d8040b0b41c1030501c2e440c01045129548800e103e0a00403400807070806005501c00c807400304140c54880c00507410407006030300c58810380d0f01c0b40c13202d042c107d54080044819118152001c6481c0c0d44c49042640090305500c2e0100600c0c00e40c840c481000c004090b1558065440c55101c2d241100740f840c402c9030441e140c502c40600080d50034000c10b504028100000e01c880790052404203070410941c801c00c000c0f0b070b20803100e840140c1d00411400301c8040e0000c03102a070001c402005090710303618000691036420401402c103800c0000c9040042c052903103030029900841054031000302e41c800c40c40300107403590384410034403031003482900001503961074651161030689a01c0301e10ad2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 90256664 1250 90255414 90255443
    0x171c020607140906040e0a0e0703050c0607020102010b040e0c09070807020303131104151d0402030d03180b04200d030f030209010207030b09010209120a0b01030f03050c0d09060801060507 82
    0x2200c071400302220902c0da0030b400b00038604950b0745807400341c0040c01d0728a80d008158207220241c1021101e0701086444960064402040803890214184078019016158035039601c0a500c0100d00520b218000c19510910b050007141070144000781c400c4500c4016680350f4442d4449800c151030710310382107a0400041c1e004000140640480e40c0c40b02603000d1054041051480380080000c080d40c2c4100744c0e510601c10084d01c00c00c03c03e11001ca00418284c41c804c0180b09500f055008207131182401c040c1072041c16142d4900740b5140ca2802ca142c085582c000d4010302940c181841d041d103140d106040d10a0200a01110308e900914003805d002600542c5501c403800521074000707040e0041d4100c10480b50540c0600000000801c5103903da544c07043c0050000107070744412420030005480003961403468a58800d0750ba00d80001d40d01c014440c1525004032000070505031038a005c41e4140304100742190540a00e0301032807416900180024240c814640381d1400d180c4e200d10046955001e18074003c0c08282021540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 90257914 1250 90256664 90256667
    0x3040c060e0d05011d0c0d020d0b1305070b0a02011b0203031609050d14060a020901080a0b04020f0c0c011103090a17010906020a09150804021008130507171c020607 72
    0x20301c0c594800030709040406205070b10380500311207100c0d0300e02d184028000244d151041d424440d11002003821030310f0301c00c060066004550b091060110013000b030503072400408c06605401444110b0342c1d921104460702c2a4a421031001340d50800403580b000341d820201c11403840e60071510441d01384040350703004608559451411200d1002405180c0c0b081c40410440840d803a100c03042840790a0740a4010440c28181e8200103501c8c0100040c80e0707054452061200b58180da0303000d50704035001410301d0300200c0c0044102d0b00260081c41030303107601e405080c2e00041880300e049010400ca1440a8262511466a0198005036490f0310034000301c02e81c49a000001409040018288084030320003070350001a20f1201903440100300e138400348051010521011041099031160b03444540c4029a81c0340810b01c0303007059404070b440481c0150501080c4800301c8009103c02415408084149400074200c0b0483c641c1c0398940d1555512004845091740030341115444030310800d01c44540c00c590203600929456442150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 90259164 1250 90257914 90257927
    0x120a0e040c05030622062706050609011427040c0809030a03020a090506040b070b180a0807060b0915010f031103060906180103030306090b010c020f0402130902030a06080f0303040c06 80
    0x1c01ea4201d8417100c4411811080c07440b80401514081603151403003103901c0c110519110459a00f020744505000301840141c0742c0c4015a1224a400c0c2000c0b40081c2244a400800e03015007030a091840c54071111044412580c014407114803d41a0340800404452407421514141c1c100e071404d40c282c0c0100300001c500c906c0307a801810b44420300d03d890405152960006541d50b8841e501080307941c4400300341141441404480d0a400c41004240c0100c807401c41401c6903120152890f000e400a0703030110309007061005036041019030200c014207a4544d4a010714000d03055442d00d00352035000a214282c1c030034055019129003108407089484550035a5181d004200c0c4200c4005c241c00e801c8ac003104400d20381c10003e0621240a903119403008241e041c100750103082202e0f0010600b60421141095440261b120000d9044011809441c0582d0b1503040107000c0380d80303120315440403060030720000401044440c140d0101042e98580002e603074030b18070440301480da01d020030754015201540c00c0c801003004600402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 90260414 1250 90259164 90259189
    0x1020a150f090b0a14090718020f0705010f050903120c03060a0509040f03080c0405090a0f02041d04020f010302040302060d0513020d0f02010206010506030c091c05120a0e040c050306 80
    0x208207005076006010a403268054122000c8083c4414880e5214060044507503000b00301300c031183c03146015013241c2d54a1610b80304115031141c800355904121001501154103d410030f0408542c1c0320b03914601b0700e0080030440f01c0c1024039031034200802d00c040404411207d003800c400240740004d444455200e846944050f140b90f502000c3e0b0705002900b500c50302c025a11541c01051403150402241c1006402d4004c01007600c0000007040206205543c0c4140d1550707000500d480001039001100c820344070080c402c40d085010f600720420404caa40d0240c040304248698403ea0b00c8510f268010300065050b4051400000c1d4450000c0c464085083d540358000c1d54401c800700314542213640c507034000c1080450300350010394590800c02d01400079560100600e42c01020165034030391641c504140007000034017860000b90302c20311741c0144280c41100e400b45140411a080001e54001c41030020002e203a80d0b0040c0800c1020911461072050189020b01c508010020961038041c5035a0710002007103000b04504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 90261664 1250 90260414 90260453
    0x201050903010b150c010605010f08070806120f2406010905061c1a03010b0904031b14011406030d030e06040303050618180c0607120503070c050d180e0601020a 70
    0x43e40c2c504050f03695011800c401d00e41200b25503a585540d0b030703942402c0d14000d40005040c08a100942e50a032030b8000c0c040c59110855140c00700040e156000041e080071a16066692944135a510240140d98045030825954200c0720400799610f855860142c0c00f4841254030a0100702d030210100030509055004004000b50440502c0010384081d0402c0225048101c820056900e88181c0d1440f41c1000d02ca441408c90044501c8116483d29607002842c100e20161180300107102030404508100744a03035219040f200f80da00a01020801024508604108448052183c8a00300804030b0180c040e1042101d81d5551002078229541c80e0348040d009080b029144540103c094910580c08403060f00010307000d004c04070b40d00d42e04034281c1401240340a0340d81e110303148681e40070072905000800455811404108504110f0340342e69502c041542c0800ca4268050154003c441082c1c1045600c8800d2a45000c9000042d8100a4480c500c402c11070604403a82400759201102000202c1d842504088040406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 90262914 1250 90261664 90261671
    0x1110d020a02031605010f0509010b131a03030c010c03050f13240c030b010e011b0b090f030406020a120801062c060a2016030f02061306110d02030406050403020105090301 75
    0x3200380c01c8031010444c40342a14681d5640c00e4400c2144603c3c042e0b16005401e0400a0042a0901001032003005a0804003c00c4590b2880c0c0817071054804820f40213542401400d40c0d0b01c40c01c180050b0317800303403e07055811000246010000f40b072001851342024002c05010101410241d00d664403101d8500c820b08500e00c0c0480079411144d40c04025000700c112100c0140e50102c3c0d00c140d40000541410505180e190501c2000001021400c50083d08060007a8111060101c0c5450780d0500a00340328140b00740e11742d18000000e000c26101c0d00001e62100a40c49045058849180c2c40c0003221598020300581e800550781d00710309012006008a0400007960320601000125001c40004050b03520001903000440d80010300c0841d6640b141141c1c500141c800c20140900e050070724000e621466083c0402003042c00c500781c11200b9900c80300180d400801c0420318107003d0907155034000d441d107408080030500c284900c3c0f2130001d40600c04001c0c2e5080781c0f041d4803214181425540150b440344c21860103180c040d0341e03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 90264164 1250 90262914 90262927
    0x804060b0a030f03020f06010801060513090f061107150209060313050c2713020d0b0703060b070b18070509131a010f0f0e0601050306131b0216060201110d020a0203 72
    0x10458180400138400c0d00240003019141c0e6426051000c1640500401d92505104000685500c80d43d83c40c5419400c10000710000546019513401c11192800b411035480e00b1082e000c1142100b000b0304605000d4180d4114110851054070b0a901c070700901e99401c01d506101150b4140140780202d60054410401e603528001c407000450001040511650407028010340c600c00f00940d1003a400750066002d14030b00f40d501410f600400d0804086c042e00500085402c0d0014270120320903405500a481c0c2c11030415611030311742c200102114030940e000003036058400204c07540c0e140000340c407908a80c00640b001c4416a2940d00c0b070b051809206205903209180c408000c403440b03214658581c0a4000450590700139400d0120329483c2075896089403544502c03034800d018207170382c00c18140c3c1d80c000011984808005001425500503002100360382d440c19900c80da84c9101960081070106184443c400015540b56880c0d808a00383c0c0d100d16651944610100464004000a5001000c7c0d80200307004803441c148 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 90265414 1250 90264164 90264173
    0xe0114040b0601180b041e1d010e1f140301020d022205030a03120c0516150506030a0305030109020f0403021002030d0515060d0905070b0d0515100804060b0a03 70
    0x108990844100c0e8964080021641c0c0110410550b131141e4000d43d003800e07042c0404821944941c0c01818100803c00881040c291202c1341d00e07d019009000c481010404840d061220503c000c0c01120300d8908028000f031203042c202004403122000d210b01103d0f26900e481e01c4100143d02e20f11170300741c140d5000c0201134901e9000e80020b0010149004020521034209541c2c00341c210800d801070740c4030340c211560140c0030036844640403c503002110b000144a004001c4151100e04c80c403141c074481003420302011403d0001e1b0040001003040b0b051001e02c607954501040645424070350300003c0114205000504c50521541c2c094020040301c9203280d4a01500c03500060b030a410030311004c4005034030000380d098151b40c0034000c4175041780391150b061354658400000916140548050b0103082c0f992015100280a82000780341c008100c404212640c48400b0034008002d4802190304101e9030013003000f40c1a2500b40403030300888003105603a83d2405912150740d13000151000301d110f1030744140520004000714 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 90266664 1250 90265414 90265451
    0x1120f0204170609060405030a27030b0a060f12080d0e0303010b0318030a090501080915161409060403140106091d012307050c07081b011707120e01 65
    0x200380ba940107115a065111501d45007400050008059402280900000607800030540c0c0340c41c6c029003000c00c0750a46030781c0807243c8400d090924074404083c039140001401980c0c1c1c41c050044288040921000e5118090645a220584221074411822036088408540580050050003032030180100b426002c18000728510f400a03084a01424800400e0100826a503c2c0f21600601c444c806142490025134014081411038800c150500070360000040458134144070006050301520300321002410705e040704104010415101c2c8010900c1d0818400310b4481240640b51590002000d00789041d0a643d1600130084880044601f20740d00c0f004085003c0e4460300405004441c002001c0481012040146e401e51380e1105020005500054480c14882c51500c2203e500038444d0401e50b6a401d8105c11b000e141031155403203000c080c020b12500080801c80c0c600291740302c1400b640c4661201d45004140100300e1f0f0155440c1010490645624000e06141d411214407182180c000180034901d650226080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 90267914 1250 90266664 90266669
    0x90301060314010605010f0c05060601030203091603061d01151a12010905220308010501030209060c0105040c0509010807060801060f0c05060411130b0102030702090a0e0d0503090712080901120f0204 87
    0x30b03035184d003c1402036581c0401166805080e07440c0103000c6098644401e900e0382e03009802281055000000251880d40c204909400c1e180c9000c41122059604d0505400428085883d05864802d4410f100d041d0ba1050040d4a582204401c01103480b03840c00b036000c0ca604c40000303a1800400010301004990f10410241e0a008081c1e111001c500c2e840c00c2520801c07003032101000f540c0e14908419410300820707400752405041d01c1e42800c0042c1d503076014200040c02401100b04000c590340c244400c0104100030320685c0030031200140c1d4904d0b01d03a41c0700d0019680311721440c0a0940040d00003c0100070449c4514220300c4240003905103288a2070058a5003424400c08440a85480b2130403800b50002d401c069185a01080f054030040209404220000f51a80f041407070183c07003a02c802c800b05102144650000c0910a41841290740c1d880c3c01000180c65500100d8040c1e209004003400081d50311b502007000b0300b25640c0402400c4c942803101c001910a4504045100201542c1d810300d5075000c81d03d44020000f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 90269164 1250 90267914 90267953
    0x20a0207090504020a03080a02150604020f1c060906090209101e180b03010b0306030d02030c0d0c0809030a031107050a030c06181503020711061815071b05041d03030c0903010603 78
    0x3065088064502e226070062f150500035481006403862a03202d00341900c07210031400410b0101e81258402c0c0e100940503a07000030300f4241c0740c10000225000c041d8002c1181050513140350b0000014030b001a01c0c01d012403030760000c1c880d02c8224213a070001d224287c0c0d4481c03a05a22044403640da03c0b1000c0740e090780c00036000040300b041d0000c02d12260745020001207802d0a21440110f24182c080035016865141c880c41840030b1141b2250302000300203d09003035521482d8040e04441c000081420000c00b903140c894030000c2d26024155001c1802d05214223248162500035019840040c40d120040300c82c140042c030b591044040c07104021455044004d0101c0c0d440f403140d030f03000d078490364141080c6c0c86060120070480d119072410000c90300301c6400345485403825542142c03c0325100720410602c0b2464441c009004100327010300c1001072007580f8800401419a0b000f5181000300e0f00d00720069003000d00608540302066032080c0b0014000301d020200921100b07001400204005550356154440c01c5110904603c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 90270414 1250 90269164 90269173
    0x809100c0b01230915010507050102071202030301180216080309010b0405101503020909150102120a170601020a02090a050a0605060c060103060b0303160206070f02090405070315020a0207090504020a03080a02 91
    0x1d02d41d100b840f80d5440c030030008132103007040b074249912203419110000000505018000c0344000a0000a50548141c0c80c2c0011000085084034400203440ba0300900486110048a030115400c1c60040c1c400ea940300b201c00030140c00481c149884440312a000200140303000d41d00d0b200c010026446902030540140002403401d085941410381080c401c1102c4000141018030502c00045a5500e06400c6070300200c4080381464502a0000100d00702081100e43e41103045001441c1000035034001108200b00f120842d40000c40c1d01c3e084012138507000e10f100042d61058090010616070386140c0c0c015504070910b01380c0080c0c11591a804a401c03030f004240100d025400000040003400414096032005c038908038003071464000044440c88841035403020190141f48c0100c0c8007801c0108508142941a800502e02d55040c5440d03e8502e580306003500045605403c04207141d81d0b21000e600980b488110a034002d0407086052154240c020710380140309980c0410700c031200101244c4131078000c202d040c4d0280d0190 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 90271664 1250 90270414 90270449
    0x5150a0506030c0a1206060f0608150402040b0d0b03030c0a061e061d0403020c0604240806060405060304081e0a03050106020604080a0503060a03021509090f040809100c0b01 76
    0x889100070030081c042d8000b8a00d040d40e507070f103c0b2003540c1982c1c620082c08040111601305400140080c2c2c200c0c181c06d2a561602151075a00480420710990605480c8140d64110340180302c280e00030341c480d99626880a00292007030308415040b240580c88c01504990421680346d03c6e0b545045284c1100351682555110800c0c8c6d80d6003da1034410144122040601440c0d03d00150f604085d004240d00c445114501b038042002c1510030320080203a40300c014002515039495020310f103440301c41d0181d02c40b403001c1d00000550069008005041c0708840080480b1309091600c402c0c40400c0e403008008036090481044003c00d0701040c442804001c2004040542e2034441d0914013038101c410607008001503500004c10400000e468108581075070480d441d10a46a0b01c43d403000c9110194540c0000b5481801c4034042070b003040110700901614081119034440507141e000074601449001e480240c40c00c42c2c00c00483c10705081000c03081c3c441000c5494041c1c4420581e07240c00d0003204080c0c000c0f0b0380000000a18 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 90272914 1250 90271664 90271681
    0x170a02060d0c1106060a0b07030314100e07030b10050a0507060f09050f010203010510030c030b0a0305010f110304050a0215130305010c030501090212061009030501140a0e0f120708070515 82
    0x50400610001c0241205d050901c001400110140b180140304500001c100040601c40e401903040d140b9100c5618140b820940c13011252340a4501031100c802c0d1450000800244c03181c003503e44094400b41440c40400c0042c44100d41d280d01000d071030000c1c0b2070200100000108036214180e45a4002c20700006d821f05585007081c100300000d600940540e0040c001031009030387e119800d4010040c1400c0026144810f000164045c24194840c264810715802d000020b202c41908034107004a0080c0080003034070203c01e0701488902050318080c144c0e40c4030441c6100141424800d41ca0301c00c40601e41541070905030318900b0188401a0401c40f40c69450340110340c81c054060085901600011505500300009042e0301c4801c5400141458402e443c260480504a401030004001641d00280248240000b6070518052280c040d03c51094540c40c06507041c2c40080041201c18010400c5405030041e0301c01c0110707903c4c45800c20704068550000400c034000000e801003103031191080800c1d01024032172920084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 90274164 1250 90272914 90272927
    0x1216060e0604050705040b040b03010c0309060b0109140607060212070c110d030c06050c0c01110315010203040b0a180b0d050702060c0309032a0105040317010b0f0301170a02060d0c 79
    0x10320051580010148000640049594419038000740c4001405194103800907000d4100c5000103609540313030130680440d036a450f0b046054100e00500d000c1c032079200d0034001100c4030035091013404084c1040b0f241203106d5280031401881c003140241000b50a02c04040400e0224610568403540071545082d000010080c5210742030f04400c9088410b203920400c6034a02070840008030100404083c0d070b45000926101e000c8003600c1541c40360400821840116009044c41503100742c40906c10300c407018009010640c0b00008890958042e002001c3c100b01e48107500303881030080b0202161444000d1030010a42008500150416041080020403a0306004101a0400e01c0180040a038003008100300200824008120395580384c2c000d240350003209603c010045a01c0b09001181425401e000c24041815880204800280c0300c00d00c544900d40d0ba00d0107d030700d40e84110301101e0140310003400100156452280741460b40000d40301900c0420a0f607a0002c2d0302a4003500c1400e0960380e40d500304240c0a98400d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 90275414 1250 90274164 90274181
    0x907060305070c0f2103021206040b0105160f1a010e090106050334030804050a060c0c0620070801020301081908030619030c090212070c0b0c0903121606 67
    0x201003140b41800d1000030440402c244018080283c2c4a60003001c10070340b809481100c0c0c1492240603007007110401c000300a54894410002c00d00c6440c80441c01a1400f44585640c2101c140c40302032a01d07424582e40f05100c000d142c01600c0c0c643c242601e85011804070800c01d034641000c0403403802190f050040b10404000c000e451303011568900f80040c070040d10001820f040c1024413000c1c4801079100b984030228550340030000c2d0701c00c10104a90000c02c10034840c000d4001d079041160301d0700b0802d40320746048848516800d4060294117202404204c214001c0b400140680034503130302522508540340303c0c80e1514034107500c45030341d80c0e5000004101749203051010f0381100ea080080700c102400b207138507000d03494003018021a01c5904030100f017000c0c0e9070450380403d0085a210030341100840d680d0000800075000b14003000c09032002100051122071040650500c07042e88041c2903050350702c5109440c21503800101c90140c0500c0f80c0440800c22414a002800140d608003d90046482c1c1368038102084c0c980c4003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 90276664 1250 90275414 90275417
    0x615060d02030a0f0608060906070302030c0d0f060305060c030c0414062703010506010c0201090b090a1d060a060804021f02010b06040e160f0915120606030b040506030613020904080403020a0608090706 88
    0x140d050108a234008983c090b007165040c0b03000360b166110505a10203a02c207011070810349625000e0340d0350390380c03040da00074804803401035059900c00d6030350321229500c9100c11140200e03040803c03c4103001300000c6654800d005030740900301504004420b240403a2011441607580c070801641408400b25160900419611500a21b03000c5040f9242d540083d00c042168003071b2041540000c1200a029244d40d82c07100700074090341103030403800d4842d0240c0000708501554940d0086005000205600c1d008000150045901500c0d045a06405405091200115880b80302c119521039015000316034a03840031b0405000201d20005071803c00110304e090510b1106186001d0002081c0071481305904a050482203c66207000c44500c01d05144040318083e012142d5001b0380c40c50316102080c080d9040e401100205410768040040d6121382040543d17a0504444800881742184e41c400014104060100d4106203e8040c481c201a100d500181105400d5040f0200141c0740c1c10070801c22000400051004000d039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 90277914 1250 90276664 90276673
    0x12042909010c08031503150403030e0d120b011709010f0605030c060a1805030618010b1e010c03120e150a060806011401111c0f030501080615060d02030a0f0608 70
    0x800103081c82002c030740701604051000c80021905214061940c040c400003d041d03514041c0c0c4905240700c003c44c15501030300000d01e0181d15481d84000003902c0b140d482415141d10710074940b0481c2280c007038121400344504111200300705558000b06048440e02451039040042801ca4007480c0c2d071000c5600f81c6e030103244070340d01220501c83c65031143c10459620401620741400d0110b1003042c0e6819240280d4403040e05481000d00b00680c030300c0c10309111001c1401c0f52009100c211030b00d604010320441c001c1032140981403280741404aa6010380107440c0f01d58480d0400c28140c400c0c800e00c880854069107501405034000c59480d1100c0d80c0111009a40701c00031200c00c102d00c9003402041c0f80e03208014041c0010591440d96000c00c1070b80201d21a64094107036030121a480c83c1240581d00d404103200344506e0115140001400004d40a40101d50680b289000105200e90310080314004283c1204810354100d101007154800c0000140001c520441d100702000c100700a122000c18203e400b2680805060303040b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 90279164 1250 90277914 90277927
    0x1a0901050609120f0a0303060312020f060a05090a0c090b10090807060e060906030a1d071415070c030b060a0e07050712021c0c05012403060e120429 65
    0x81e02800c0d034203a5101038443c002d41c07010400c00e040c6070100010640809224100c458020540d042d0011403d885c4603002071002c00d0100c01050360394144010901c042c682001d0001003042030b540d440320b5031080701c8504941504507541c460110000c156081100d905403244500719007820b0480500503030482e24500a5626450174000311f80b5a484c070f0141c8010401d803010f1120440d51080d003940e84811008001540d64108510503800401d18082400d032001c031164803120fa040404102101124401c448031031074205a00d0405c0200354191102100610302032001c1c00c046600090f4080182d485070343c65090074107201e000c12075460141c1d072084000c82821300c00c000c0c08582c003400b580c800755400301c6503100702e0a400300168100700c01c001440b4903c2110080d20418607901c00c0ca4140424061002005a640002d1806001c04d489071030041000305521810400141ca683c400e268062241c0c05403480c03240300c0e07004011954059401001c001208050304200c04007450882c0001b18800c0a00d1881c003807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 90280414 1250 90279164 90279169
    0x13030b0105190311060f0c01050411011107060e0a031b0e0c04050d030c030c050613061a030d080c1306030b040e07050a18020c010203010303020102130e06030a060f020903060a1a090105 81
    0x102e60000401c008441c1903102115114801034412424040784015100e840d0440d4090003460304079130540c0d04240d0100d145803554041c4103200395000c13041780601502420700701e051741c02c0c40d84008500c2e0050040513001020800104014081c03001d800303001c8240d545402c0c003024403406e02a10650059004001c10052591207040d6084503543c0350030080c0b0292418201540e90306400503019015004071760030484610614107000c02a94030564080006114440c00c440b9200d500c0c14100c0d405612036030070280c1c003600503182203034005001d40e1004c2c5001000014402442c1e4036500403c0403030b45441c440c894614050091140300d00c00c520040122924000c001907100c0454072a2500c3d41c40d0841201d0741c00002ea070102c0e20b01c610050025542c07035a4034a4000e000358040001e0f0b886c080b94004021940600030b1050a001c0d400017070040034945060f03240c0c10300500600d80b043d07020030341c20003c00100340c90502441c0e11514141d00c002841d500031004501800ea65600d4052003105420018802e56 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 90281664 1250 90280414 90280459
    0x20705130e06010b0406050a030c03021b01020d060b03060d0201080414030c0115060f09090f02120f010f0b0403080405060a09050d1112030405010c120c05030d02210c070609051213030b0105 83
    0x48d928a00814415460341090b80240305049405506403030901082d103001d2015001413204042d583c1013001216076230001c4080d0340c081600d2290340004d8000c2d0340000f41d8810139000350050b00a040d140395561601e00c0031407540c0d202c031401c00a282d444840480e076144942c4170350b00c0103200d642002300c101d08090400500500480c040d111600d59035141d0190300500381c1c0d058411009090340c0d0600c0a040803084003107034260902ca50305c81e1154190010800c801d6210549003101d521541c03940c1401e0501c0304000b480d8004404140070000350340300018055980d08080c8007214060680401c21107501c60078003031510103415500c4441c1d4801c1004002a9a11440e12403046402420091060407444800c0311b801342d030034201400e184408103001c0c40350309055000341110291024200d0350000c0c1d135100c0440c9078908498404083ca02403069001182c00f9030080f100240c410b005070381900c009140742240c66008100c002c580028000c50a004010610341d400d4007621044845401072400b4080c1402c11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 90282914 1250 90281664 90281677
    0xf040320010e01080f18070f050306060f1c023c0108161103070605010806012417060d0803070e030c040e0a020111120712080604090b0a020a020705130e06010b040605 73
    0x501c0c1c5c100000c00c0e441c840d0369200d90894481080d29001c50f6200350700011100715004541c402e00449012504920b403211109031420400b900307200c26a94a1300d0385002c000d00c069820f0382c00511940b4100c035048882e20050420303203280c00c0780c3d110020710562034040c682d0003442c2c098148102e4100744280700100c801c02c0030f8140180c0c50021003244e2426181ca0440c05000300080c40700b801d0600105101c4008241641682c80102119860f80e059440a07011411010441c5000c2650a500541d50040d40000035a000101401c4440b40300b106540380d4001b80e004882510001716a85178018051400781b00318558a0422282400412808031206403a49c20894001341441350103404400c03408014040c0c08a05000d100c90141c4412441c102002c401e106d5503510f47c0014250000145140b40900c641400c003508150411015980c0000d0f000007540070007240420362282200010351551056851040741c40c0380c45011a066000550070751400f1350603004034419040610003400b4240d48181960392 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 90284164 1250 90282914 90282931
    0x105040207110a081c18050d050a02150306011b0803010e06011107060c03030615080705090d020904061b1d0f150a0c0c080109050304031203020f040320010e0108 71
    0x2503a2150b841c14200c81c2c1480002030342c0140c402200081d00480104100c008860060102c0d24850400807003102ca40c8256a403c0d01030402c448000d00850900c1c00b070104100d44140300f202c40000c00e5800240304101000d404822400b0000100146940e100f9000c8140c3e00c03a089100c2d0203160560788520150205000e02600e5183c003000051301d6a1003241004499540c880642d02c030b090725074a00406d03101a151064010074144000000e42005ca00304050021030940c0c1c5025558540600881c2c103540070340012944840d0b50f43c080d030051b03500c0c0d403112030141d8401d280004103c0c02500750380b041c0b10001c0000c0340c140182e0301100d8030140000a4185a000c504440485450b007143c800106200d00c003100d041e07800100070480c0312a1940040e401c0000e14003c20b50305203080d9460140c0c60907240d080200038001c2c5c0003030108100284246182c0e110b040800e06025040004072040b40d1030035000fa50081c0c0d114118a4031070500c5042d03599031b80900001c20f00c0d2500ca81c00e13a02001a204a101518040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 90285414 1250 90284164 90284167
    0xe0a05130506040603020618090618130303020d0c0e0a06090302060417120403050c010e04050105030a080706110304080714010204050a0e130206030c040e01120f080d020c03071a071701050402 84
    0x10b55a94840d0702010103181d0080040f500c52181102c080500f49004144078024030ba040c02080482ca08003000340c20f0031034a00c200c02c02603a600542284803c9111400b142030640034080d800206000c1d018850b126840b5651741c110001d8010200b0103e041184e101200f8071550720030a02c00740c1c85000840d41526500d80059401c0654a000c5524040b40411000314202002c0b40200c10010049114078041409aa80d0a008440d10041004661080c41885da0590104132010b000030303003400140801602071000041c0205942035141000c0e407088404480300540040c6090802c00307201070301c9030103a400f000214205801d080100c0d04001e03084c081d807000201441c00017908030243c001e11008081d40500080d4513820100100201c0350418040c12680c100c0f03110020900140c0841700d030000c690405113100d0010603a40f6502c0701e41d0700c2441034840141c1c00704244951040200010000c90f03110341c603000d81d0160b00e14840039441c40050110342c200100607005180f00d8501011950550381d0464005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 90286664 1250 90285414 90285421
    0xb03010b0423150301031a01080c04110702040504050f060a0c05041701020903150105030f010e030703031d0f0a031103071109060d0615060e0d030f0e06041d01060e0a051305 76
    0x10900c00700501469520908850f80499400011005907049911a8182c203e03002040082e9581002007409a1302032940091041c84a038505500400ca1402142041d1403402c040342d00401e0948008603070a40d500d9010500300002414100148c81e0301141300314040001103010701d0002c0c0144154403a17680e1151100743d64102024003941240c0300700030300500311003488109580000c0c201000b4443c2c64030a000b0000e140d809880180204261004680301962400d000c50380d0550040c2148041400194004501580c0b4100108504c142e40c02000f4024440c108051500030510318840320340300700d50f400034000b0100107020402020303510581100d10a6456480c400807400070658103101402640c1002141689410240c0c605419640d40e5a60b000b19200c3c1e07072052081e911600080100015048060040c280e44500b60900c10b00200800f20303464507070b480c1c10749031500036884480001d0083d501d004210b03254101d8140d440d503190175a103c003201490700d000150400104801600115181e8000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 90287770 1106 90286664 90286709
    0x215240424061103070506060d05030c0609010f06090b0906010c03050f0a110c030705090406091a040602091806010906080901020c070e01030b0105060304120c0303090816020a0b03010b04 82
    0x145031544a032009d024038114640320a440b103000a208030103152100b803005501942c4001c001048113001404001e0442c0d405900c40a001171414078200403540300c116000d98400000d00380031040b0080e90030182e420f132181c0420502c500c3d40c0090000d4003d80c0000f071046075600711720100d444e545a02c1050503600c0b80c1034080c80b40e0041c1d40320005400600d070343c1c103c7c8a090744188503003c7d80c0224007141040c012130940d011964170350049056015410715a21504580b00460160011418184000703410401c2c0fa00959080100b14030000b079910710250122290210038108030f4082503070300c98980d00c6040c1d00380000c03610b001180000240514090003942c0c00b03076421148401c1039031260001501d03122800300084050540781c5511710b000c103403100c000e8503807111805698401c011603441080355180c070300c0e0801c1c180b0b0041400180701c840740410580e0242d0364020140c0c140e240240c20b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 90107914 90287770 := by
  have h0 := BRFrame.cov_init 90107914
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90107914 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 90107914 ≤ n) (h2 : n < 90287770) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
