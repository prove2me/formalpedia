-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4359
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:22:09.077739+00:00
-- url     : https://prove2.me/submissions/b74eaa7e-15f0-41ba-a93d-0326faaed280

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 783812949 ≤ n < 783992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 783814199 1250 783812949 783812977
    0x18020c0c12070902070b0603010f110a390b100b0d1503021804060b18152202120c09060909070309020d030309020906040c0909020c03040807090b12060408 68
    0x22020301c28a20300241c40e480200c03428000b05244040c41001803003184079031000c1c0d00038000b2901442e4000704965005820140075401848010403442c0700fa00c4a41d12020303a00300d0b40001009c1c1566290300c0581c12001001c40400320901070041103056052184c1112540c0000d10b181c40c00d0640001c1540240d184240100384d903105e44c140015040c01d08800110707005082c00b810b4500e407409907003a140c800c80301aa100c5080802890540c2441c02406815030380d4901080c21903203a4a601080740e001003c0d4140e4407800d03910322608030043c0300d180c2d5000d00b40b149078011398444d403a500c07058000600400e06446070100303202c01d40003900d43c0b10403107000c000304445101440c0c0d11010150000c120b1100069088040d03a840d100c105501544082ea4244c02103882c514545d0310b00c020402614030204400c1e00141ca403041c20001041c068002c0e128907640078040d41c6c185601c4600403440c03c02c80354000781607135840e106444550705040d8803003e1500070000140886140907203581e6060f20902016140b40c1e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 783815449 1250 783814199 783814219
    0xf0909050a020405010f0512030a08060f030f121801080907030308040312050c09040506060315041e090b010608090a120c111003200703020a0b060d150618020c0c 71
    0x22509001076059a9030050040240c0d5031036059503810740400f402010b01608411031811001d450000030344080318441e50310400242d49003411b20000c1039a01500581600c1003010806c65100b080c01081c04041101c000180c840e040e4040c14903580c0e004408260510001c00306000c2070143c00708100041c0c0340c06040848440e201c9d07180031141c800c0d1000c20b25198901c0d240601c108045007200402a0311022507082c0520340717071681004413510047c1c1d0107030110304541240c241d8508081d040b14142c890052002a4010301c83c0540318181e0780300c1d15048940143d80801802415040701450340c1141014005000e909425615081a00d00042401050107652002407041000c4600c46102e800e6018042914602c00e00402801400b4116680008401d9001000c040703003401c101510f4004d40c2503401031032140e18945941c021028090a030b250001c01c1c503685440400d10420122400ca1080000040c2d11032401c1110301540d02003180989925004102200e03c210300016407042e004400c6602d4094 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 783816699 1250 783815449 783815453
    0x30b0a0602030d0c110307030e101d040c050d140a1820150d02070501060e1303120e0d0206010e090d090501030b010207080f2805060f1302090c1902070f0909 69
    0x5c0c64284000042081c400000c800c000c0580c0034154160064007550803803501c5425840660380703012a000d00c0d011031070303001000190510703003600038814154040c00d2140c680200d817408401076030803181c1003541c884046014030282c600b55115030808000941d030116070303002d6560303038140245107101d2200e048010081540130301c50399030b00b00c014008110010f02541d500c0c1c41d4a07a4101075040714100341c07425460410001861701000034000c0c407031040c05510190100c7c0715502901c1500010003810030300d640e100c83d0401d0040301048200454100e58000300015071502e600704100d948004d0180c035660300226001e250042d08080018140e0f4424240440d4640300034004070b14020305648a4201882000040142e41d50041414965981441440101144102d80440030004a1000107046501070000900c1c802c901c00d203040d402070011801428041d001d500019405001a20725200b0040000b03100702112076240d5035032028044d54006400c1452510030b504104090a120710013005d0703151a54001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 783817949 1250 783816699 783816707
    0x606071a13060e06090304090f06051e03070b0c060708060f040618060501030b060a2d02010614040c0804030e030304080102160c0b070506190e100903030b0a0602030d0c 74
    0xca1002405080d160500e0004140503082400c8007040d01d0043ca00f42100d01c55a1002c10300c1d5106240440041d0300d03262400c50740c2001030400440b811000d070307520600450f040d40c490803030780601248030740f00a91040a803400c050412101303502c401e030801c00c01c122604141c000031079460792086050a2481882c1c2c0c40d08085400802018196944580750503c0440c007a02d40d81c11016640d846210200000c039140d000650481d0308880010303030307c16014401c84481c1480352542c3c7d101d034408203030712400310001d40200c3c1d0748008a81c20242c016035100e0344d050005900c42000840c880703204a905011583d4000c1c1e0182c1080c0c4060030180c200610074100c1380e02c2da102002198014404034000319551600360218600d000c0500c0e0007151402001c14001503100054070a407501170340c0020140080303842e00d0160b50740e4040265854462991241860400141c041c02800b4031404010804502c5107030714a4000c0c122200030a4244c0b140b01d041400340106503001060741c5840418143c0068661032400c010746d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 783819199 1250 783817949 783817973
    0x20127050628030e0610050d0602090d120804030e010e0f0f0402130303110d0224070c08070f0c2c041e0821150f120304060c02030709020909060607 65
    0x3010161400140c031011070f41544001008100001996681d4480d4104130319422854031415130310801200340600401c0c81c680c010072001800404c1c0c1e4940c00e0099a400410120012003980464141720030482415001a01723000358580901c0e090042038405400682c004107248007850090050308141c51103a00c2e00c1d81140d0644001b01b5140410070360303915000301500c0906880c0030840c01401080c0900c1ba000080300f100000706811400d910050780140c0494500000700f0300c008010b103500342a030104040703c0007070203814003d200ca00e60181c06030130b1000072650658041504803038002481d00c0c81c103000c0c0c40b0800741c9001c0e0075114400d544039410640806e4500e0303010484034000b042c10680400c0100b800a101c0d142c0710103265111103e000e2401c41e00000101c0b41d6280c1c3c0744155409403518604501e9903200c0200051066200501e440701640c40d60708140c2100c004948503844610a500c1c00700580f00041945000940c40c0040d03c5001c00c942c0800540894016000131450b2804c1051040e124 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 783820449 1250 783819199 783819247
    0x19050309010f051006030f110a0c030507020a0e0601020f2107151404150615080a0219030b0f06031911120f0403030501120c030305250f0201270506 65
    0x10300080c00c1c450b071104d91131030a51050300003003450544184114200c9000d40d2002458a104035400e2000f04c50066400c840046801c070100101040513a00681c0d4400c411800750030504d2030902c079490460300281c40c00e1000490a5800d9114104400b500b00e010800b02c0308280180e10644c2c0c80d149203150550b507010307020b1400b42c501420039a1414000c00b032514002d2156005041c07010171045420700010850f02c40d40100d2215410081d001c600c03560003a50500d4005142e00c40041c504041d0380e030a03802d2032141428440000e80c41d1408071b0864036106003040c1203c030044450398514245880d5207202c002e1034003c0380342138a4980301c11001c070194071015594012507110581c103292801c5030f400c0302c44090848080300460f00c0c000001c034041c031014000314055940480300b100c0450854800351651f400040e22030000451080068a0a01c400002c40c1c403072510640613421140c030742c0c0c4000341c05010303030840d11a01400c2e000c1e04905014100920442286c00513503c00f80c0e079409080b819840c0c5c501030400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 783821699 1250 783820449 783820451
    0x415060503030c060406110418111c05070e03120301050d11060403051f090803041b0f03050a0c080607020601030611070c0b030406060b0406020a390e0105010519050309010f 76
    0x4000280e15010418a10846c8100400c0001c04d0b01c020321360145010314000c0c0001c48003071505004d0700000a40c031641e06c0d403029240c01d0f400c01d9025035010301c0c5011550200c40c0c9154441c001c1c4074185070030418034003681c0307030440c00f134200c400d40c0008e0407845000521410307204103c102003003028803400890030500c0010203043d0b240c5c0d45841e41025540c0302100759403c1012440d480172101d2030002c2c5c0c0f0944842c25840b101d0145541ca03191104e4580043c0d408141400d0281c4580004000c0d50300041c020007540300b4070161100b01b07024203007203c1a415a5100d0151500304804018949901091142c152540701400103200702140e55815024060361800801a000e441303004541c2c84400000703184110300c21081031180d25183e41000919003d81c0c41503c001d640070340300880c0001c04503555800341802d080d4100031444014004403000f0824083c082003101c006400c148041e08140844c00d001d00700a090461512001074214107241009181480c1040700101c08213131001d100b174000740301d50304e86440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 783822949 1250 783821699 783821707
    0x8040b030702070f030b0a0c0905040c090503190c030311010f02040b040320030601172b08090d0203032809031827020a12050f160804020306041506050303 68
    0x49450940c02620314401600c288400011810b4001c05000305480d800500144162211300522014103600740c6000b003400398658021407a80c54a10550342d60311030302c3c0e4035805403514040a060800e244180116160b001e0082c241010405270b001040c00c0307950614000408084040e420780c01011040a9010041c1c0002000280202c440d0080d0003600e02070420f900300003041c40c6200e01c104121155181c1c26402c0dc1c0010410403e280000307000c80c1d4525000d4412440091518601803a43c820f400c810135030806521881c0550b0040b8403590008402c0005e0021641824010b035036404018204411841e050ba0950289050080008002c19044906024840f072340c0c5009809045a0711820100071171800001910440c0e592500c088a030407018101c0500781c1000300280030b540b15400007400c0c0440030010081003d003610810b885100030413820200b03401c04801b00a5004901c0300c4000c1000501c0342804090795001c15001e812581c03141c50300c800081c4500c1d8450140c440c40d40060790502000c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 783824199 1250 783822949 783822959
    0x40b030d08061c03020c0a0b13060e040204080a05160e1b0a1b0f05010f140604020c01020403052b0804030e1201060513020d0b03160b03060319110301060e1509130804 73
    0x3d05529443c0c048807800e8800d23488c0c2c03e180d0201d000b007103519400c0080d03610f0f00304611030041c022030340c883d00083c00240c81c10b07445041d80c514000742a00b040b0b813203074040c4a9910074243c0541c03080c4060460340104078140c0c100f19841d47c00b407010300303e490b03030074104001454a052400755403000140d4004c000c1104001e81141040101000c2004064907154205030b042c3c0506025841141c0d0707005850051030306641c841c2418040290440503003413010799420400840403a8042054a54004400039101c1100b110303540c400100454044450040c0000e501c18800029042919940c03211010340b10240081c0b601c00460b4003400d9140e22080e04444008200e00100b80c05400918640501c144180a0104035400741541d45030000c2c0009260811450300744000010f4200442d00207200804540c28012120005840328107d0501160030700f0480c5106003240c00c0a00030b0600034000d1504860144c43c00c508240c48140c0701c0d82c070042c07040500d20300080301041400440320300180c05c540300715141c945813 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 783825449 1250 783824199 783824203
    0x901090306090308090d032c0703050312181b06160b090a060605151204150204060e0f03010b0622080a0501050402090f0108071a0912060114040b030d08061c0302 71
    0x64491703030301034003440490704240e50280c040c0745006002c8140191040c0c0c0440300e5481d004140c112000031a0042c4100000802da041029040007000c000716400c2d5410a000c0c1c0c10340c1807810b254000150f822698420b03503072000254840e203414100340d502b681d0b50300c0b04541012000b001079900418480000c01840a0b01400181c00c1d0342182c840c40082100503111003c100c00d000700405003902005003005a142581c00320a079150b0064030841f40590344440d80d00a80c0140e0b0420340242c400505030517802c4038035161050703503040a0001603000300040ac0d4000080b42e403610a410b40080d000008071000d02ca59000441c2440050441d03c0c142c4414058510b0a00d0290400742c5080e440b446101d4003180c000524a50320034100c43e40c2e01c000340b941c00e10341110340411102e242210203649100340441d0100351901a1040303d00804a00682000e604000c0a00038514800d2140c40c060343c41c00010a186445c0003036105483d0007182441105503881c1070000340c9084001059072010702031081036104150700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 783826699 1250 783825449 783825451
    0x10c09060e0612010501050a1101111309020a02060a23040b09060c0a0503130c05060d0606030f110f0327030901080703050c0304110109080a05030d0c0e03070b0901090306090308 78
    0x9255590304000c06003500308806800f8003000005114016401084250300a0703000746452400e0741400c40ca028410a4400d013190707051100d41000500c005200d181c40e041d1048004c000d0102400e0840c100f201c07018000b956071400418000c030b60f6030f5400041002da110f500c1c601e000101080c803001c0c0f55240c540f4100b00d44020a5a07003240610441700810b01000c07000d8140e50701704010382d641606660700d282645002500c5001c0035240742200080202e21b58079504014800d80c0701000010426502e0640010129403400c40101402c0d4a445202c41d40b8030910003c583d0700190780c1320b480740c0340e44569010011312400380200c11500d0502c1e13214500000310120140801840907211180c0a94540c3c800760166041120304c40018442040001c0008150341d086c4d5450340c00c10b01d010000d254036101c2491400c81d03142416965a0300215400782c407500c142c0184020b0b07100500e000c10340500c040011940d034148074080c002142c0e03070116084446903c1002c5050003180c00440c14000c018040c01c001e8898a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 783827949 1250 783826699 783826709
    0x250f061d010806060d150306180510062111060c07091112040803150603070e12030901090b0d0e0d110105070c021f170f0f1315050612010c09 62
    0x15100482010740c0120603a0b489100c0241015241000c28100f507801070444203040607003040c0c00f031000700110790140300e191443e00d120100c00c00003541905000385880c500400c00c40043d800c004007441010700c0d410b04101080c0a4440600580da1030340b030300c0c035520000b50b0320242d0803400c00700d260641248c0c0051004100c039a8004c0800085001c201285c10b80e10801118561a80c9034001040006015000840d400610b4040c140752100e0880d0000d50254001d071018000240024507645c00e87c45c01c1d040d449440c44013000114540020600080c2c809180c600c40e8990b007603000314650114000c2c03504448007417000ba00941e00400490800504801d0840800341d009600c4c000c0000c940300c0c040c0358445080e0340c0080443c0c5d020201da884a000300c50208098404101d00301c0c0310300d003401174442281401034203d510038240381d140c8072840c0d601d90100201003d05e04025543c6020104030b545112118210102ca8042980d5580a012480540b10494980740f0b5601e0850200c545a51000041040d26 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 783829199 1250 783827949 783827987
    0x2070609031e080603121b0601030c1502010b03150618160f0206060f061303140607030c050f04050d141e0d09030305030f070c1403030402040c0503040302250f06 71
    0x244002c01c100c922600031502c0030b4156025040c2104019903a40c0604203174010a030701c0c1e0022501d8010203d090407420f074001c0f1441c805420060200003c04100c40b981c6010ba0320080001c290281d00099071100f16403440c103281d864080209585448038000440000345d01e207601c01751400c3c0640c191009201c2c2000038000200400c1e00c07000d00501c0450001d0060900810074281c0b0050442040590b07404008000150001d2000c000001400c2280e034400b2090042c0241515181c5908040c00b52100c000b0300743c0401c0401c200c2d080c1c10101303500170396058940c00d032003015035070003146401b02951240d01d01c404010304c02c83d103071500b44c0d505015000c5a14034582c000e462220760340300000d0304d03026803901008003c00c0e0103200040000c008448503d03440159880d100c1070030805611641c403081107050030140142c000008000550510340601c050350141440d0842c55440c140d14020345404a00c0e004201608400c480c0c46031a80c000c4080310050301c032070000c0e2041c09948440140442c041203030360910780 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 783830449 1250 783829199 783829247
    0x270209060108011220031002090a090504031407020402041a0a090509240d0f0b0115050306150904090b010815010902130e070c0c0608150a060518040207060903 70
    0x1075445282010304880e02e00780548a00071281d40c1310010145d005081c4640140e0b0b5100140c81039a00700711441c0001c060003401aa0b40c0d0100c402d100c4901c0c0c2ea90000c41486003840140b2000903402600d501c0d900846010795622240c0034400140644107903840101404c20407440301600e510000000c041800b40d545495440d85e070b450091102c800401c9400d440c480040410113150180b150010100786040100341402e9800785550392183c9881c8104295511800c02e801841103250140414807800040e0030b11a0940c80d03c0c070000740c0c0d01d10a0b0580c40140074400705071120140c43c0ca804c03102040d1f6000948031807540c6c4501c078640c0ea55a1000801c0142041c80c40000f41310101c2e44212030181402c1c25402240c5820304901c00c1101001410000030000c5040c400d8012507201205940509010b50b204042824a4000b0400b03007408103056603c105071415040142c1038200d811120341031034400040f0600c0b84d1100004000303009204001d8030207400e1402107410158010319502c0e17010145100c1c1c0d009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 783831699 1250 783830449 783830461
    0x1e02030604200a0506030a0903030605060c030a110f190f062a03050906040204050711030703031b05090d15180b07110d0905150f0a0f0f110a080706270209 68
    0x4420340f6100315a00280c08201242041c4003581100c110301c0d010b81030209000340c4c1c0d940443c1d4160b210400c0a041c84d000132420503e419841a201e0f84060040c41c020321181d00f04440380740e120000703410501c05140740150b00c03d081100f680740c41007145800110400c0300c0000d02c0e40c20400000800c500c0301c581c00c0307814101e016050080c85868080c410071001004207684036070920008120184c492400d015403131007420f44040d810002807058901c681d41c081260840e0308000d9038042504101c51081c4081400b900156849c5d02050540140c1c005180d113800d5000061440d00a2038401114003080391140214002c7c0b140e4980b0441c00381542d070fa12440c0c1e0040100c1681c1d210310384402c201000600c085410045441c043c0d0310704139865654800300380b809505040708001e681c00203846c04045800c0b000201c003803d0b001140c80d10000f402d410302c0035642049444068031060b841704010213551012902106000c071581c8904406c034207504c0c0c1c10140d101d90111086810f214103404034802c0c1020710001355 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 783832949 1250 783831699 783831709
    0x9030213091e05120d20040810110405030f010509071a030106050309010b0901120507080106141513030302031323010c140111070203070807060c1e0203060420 70
    0x350781c0d00501c1501c14082001c00964015100c9441540c061051202100344050303420300034001c0302018240010045000c1c4285201d9030380780c40c00c568591106200810180202040100d04400c4a0702c0009558441410780c1e4a03e00440d00800e0f094030442581c102806015070001e4024000c48041f00d4090fa0b0740c880d0122010403c1d0a50303258204180b00420005002c1d00240d03400079400b40000c0b90000040300810fa0598007640050a80104011a84c003444028080c60001c1c03c0300f00003d201590620001d280f010408824050060700c0311055075540c0d0082c001500c400858040020109a9503030900070f682e0780001c207c1e034081503c011030015143c101c0704860a14103000d08000c4000820001c0192250303010581c1c140c1740402046525903c0b1003086c440c480948903010300158842d03215005040c41d020840d042010b20307900c006000c0c400c1e140c000c1070100c02e1607400704421029900480346020400c015030002501446103105100410800590070741c034800e40c07a000c141c2c0c0c40c0400300c1004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 783834199 1250 783832949 783832961
    0xa031404030207031401200406080f070e27070504050a0b070c03060506010509031f1104030b0f06120d02100f090b060108090102070218040201090501020a08030705131509030213 78
    0x5001d60f0100c40204005180ba251240440c60f00380000654000800c020004003031280c1c10f1a04107600000b414000c80c1d0f04404c50a4000b40078002102051500c600701402da02e500c0801c0c1d40c850320402c410b20071440906c00f84904020b03110f0141d01c00600300450701400f1a0000d010f007500c60384242c8808140400440d0035520700c1500100c00546031480c640b076110080001804450400808229490300b58500308100313231104190003902807418090302c2c07240089400000015000120070003040001c01e00138501c258115400740000b102c4d5844141c00502c4108500d17581c16801e024011400404d030f40c0108580a040c1901241840b5907840c03169044200d1b6903c143c001c080c0c480a030040b4442d0b51140d01c45950062082c0300043c035140d000e800181e0a840e001c1c500388c0c07500344007404000031075038060b61380c0c80140028002041000400e99070210349000c010240803c020b00800c0640e0100c04c030144150060240076850b11200d003202c01c00900b21109400b00368022a120a040310a001030b608c924 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 783835449 1250 783834199 783834203
    0x180a080c15090d0e010c080c06010f1d0c0d0e0d020a0314030106080f0601030f022a01090f061802040603260a2102040b2101090902060706021b10020a031404 69
    0x142c5488a4251421341c2c10328804030840b4104410010190000740440000385030300a051002014550b15241008002c40d009801c40c100700300f1070444000110141100d40c5400a0111180c02e48400e9181d10440080c08410116850391281c03ca8402c0030503008101400a94001d664007406001004e0a4131a244402c5c440c13003000503500000503040316010382201c0e0300240d05140201d40001c2d0318900400783e03003080d849580180388a11351408903418030000038070410100b1340203020030304841d00c1d9801c81c005003c0b40540016264480880d410741501151400d01c1d074014000c201d9140c4a0824080100e005202514400c80d62200c680751007014600380c8100381e0290740e402c8030380320341c01c8160300800c600c80702c4400c4010b030244008540465018084c068000750f01001c1c000441d505651201081c40c1a40b01d6582c0c98070b89240c840150300c5802c200c40c141600510051303512214021034440c5084520030010890240c11080300c00894541c0041003040324a0380d09001c210f40c90680040c0400303080d200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 783836699 1250 783835449 783835453
    0x15141008010c0909180b07020d0e0d05150a0b0301060603060302040c090e07141306020f07150f0c230c18060d0605100e0411042d05180a080c1509 64
    0xf08000a0443e03800c000a5400181c80510307081c8115030b500301c1202e105544010141e0048002109200d038001c2c1c0c90b904035041181c000b04511100d40340c01d42c42c2d484042e0311148003100703040011012800340d0040c180142015000b0045a40d6031000280100b2107400203d1185040200d0401600c1c41202c102c0e099507110311a010280d204d025007510f082903090411140410180540b00302c40c8002800c10006140305c1e0003800c02d083d5401d8805040070302030340144088040705c101940c500c66018a81228000660800709041d5203035041035440d44807001c00d40f18140e0004111310700c04210104807094101e909a80362818404025a6415000d90803656250000d00069080d00428410303040107801641da1815000d1054668800c0814054102d8040c6c9103401c1e600441c00b268101481540c20004d1030100d41d000c1d1003605694a00801c0d41c0303900040101b0744940100d45850200b4800e44104442c4404035034945070b03149050400c40c1c1044071510082c1c00746004a07103001d619860058840c0ca06000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 783837949 1250 783836699 783836717
    0x50609060420090f042c070312180504050405100b120c060f071e0b0c120a091e0308010509010503030a0c080304050c090106020109110a05180415141008010c 69
    0x80b424150821045070794400156a020034654880b4403400c55030403031130144052410100c0d1803229030242c90b03504440041e480b0243c1003000c42c04145840340f800c3c1c1a40b40c4403030a01c0c81050700d0800400246c0021307038001d240c40d0a00080090004021200801c144000e000c4410f219042200f0811151000030395500844000c0d00c0900d0007600501d8425040307080039040c881380e6100c90030030b0341c84036408031650682c2400790b109000ac0c07562002c1d0b0010203006601c1c40d14035410980307500b80c04080e02907100c90f5110a0100d00b00603040c0783c5144100c280320b0200200308140e050040a0010a20a40d40503010580001c40c107400d010080f28901580c0d601c5e4044801039a5651a80a17440100291000d000f194a4801d2a684000c00345000308003690000c6041c9121741801c141d0700d062000503610070482d4040811540e200c1d060b1503140d8400c00c20400c60180e80390f0600c2800b0622844044500c0e40c9824020030510039980e0700240500d40c6000c003100085d4983d1415400c841ea9010042c0110301a80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 783839199 1250 783837949 783838001
    0x5090c0111030f070606031b14040612030c140f030a030605030a02010e190801020d02180a0e070f020c060703090614210601050d05100501030e0312011e080f010506090604 75
    0xf001041c02d2449104009081c82c1d81c0e8840f0541030054009021180d5100801045510328101d03088000c081e04950401130385141502040701a410036000034103001c903055481c014480b04800024484101c0001c4c6c4a11030718021401c0d489501200c00407000c64a40b600218440c14001488a071141c1c0c1030311595614160613040001448101d003800345441c8080001180308102800901440c428082c0c0240c1c480c006402d00590307082011600f1806202200400c000311038141d94043c0d001030007414145900c008400f0300300c1c20b0074241e800c1c5d260070060010301c1c90209940607145200721100741ea0707092074019002084040c2803080d4448070b0032000400d40c0041c2c0300902d01c2c0a5070b41203141414158074018002407107405441003101c0200b020190388108002658050194055203401038002d5868801d4003092809022018003920009041614030150700300381d12402d0b00040c20f81d07041102d401201c0441c1c224081c000840e400c40c0514480000f250150034580100b080b400302c0c004070f10744003140c03007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 783840449 1250 783839199 783839227
    0x30e10021e070213020d0501051e010c0321050f070810080303010501120207020d0f050c0a03170a02070807090608011503111002011e150501140706181505090c011103 73
    0x44050340c3c0418220301404c845a11407001780001040390340082550f603d8482044034a40000250010034021170403008103c1e82c0c0b000c1800c0c80594581040c2c81c000150034400c0000d51180000604200d14103828449180d05100145200300701d06c0d0f9031236800d61340307585229108081c14402d1511950090005114540c040c50300745500680d02000103080c1201038000558160840c0360658460782040744500500c0028058500d2030f003001d0362104013803881e5684200402e41d481e4089400d4100104541c00c07031501c00d02141c4010003458040380c801c01c0d2107002ea81c0040c00c242c4a51070b00c66103800b03c2003440d02c8854400780200d07904102c0c258a54031200080c0302005007003a0b04d041c00c5542c1c0d481c00c2081c0b000311140ea10003a90b80785500048690701001c406465003030907005107051000d10495454406402012641d00e030303620490101d11110b2560f000c0415104040f4021b02d894242c03021940101d0700c2d6407080e8420318155088400c3c07014460015602c0d43c0c417094401c3c1c400d400c2044103849a03295 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 783841699 1250 783840449 783840457
    0x3200306010b0c03071a100801150e0603161701050109090210050c0705130603031821061e0c18050604151404120b0106111c020c0907030e10021e 64
    0x122010f4903d056120344d110041403541945440e082e442c9002401800794414281c03c008d401084020807481f58220300900703204a0361b03c1055458480100003510300d0f10701744400084140301c0d070181011252145000b449491211018501e150319010000403008124001d060041c0c0e0040c0104c11064504203003115240e1007090420607601c03c01000089503184c5000b15901480260340005d0f00b60300f9450300402c070380300020072251950722902041c09a41051301c002c40300e41202c0f8910a040082038a07145020b49080b0b558554401441e81c00492103c1c40d0750085c088420f1191307980d40044120742140c00609550380200741c1c02a00c10b00c406d00c01c898040180d11900c1074141800e140f00c0b0300000400c0b0b9940e0058000d41403410782c54a12a080210000819001d482d49051981c0141c0c4400c0d01c6598407100802c008840c00018201c80094a000703102d00b003a080e001401440d41c03880c000c440079020b041d5114050085205c0e10743d00380b00c600c44e01d10948135042030155845043d0040e0200e00720117908 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 783842949 1250 783841699 783841717
    0xc030216050c012c040c0915050d110c0c010e0a0302190e250c021314010303020c030f0318060c060906070305070302070b04021e030a050703200306010b 67
    0xa4204014148400c000080c034000901c1079006120501e69007000402c010104d560040024440003107860a200c3c8a450101d20020250b80010700b0b00c0f40d0117800c42d60b480040d44000302c0341781000300241c3d81d650302c070700140b200c2030030180207100300310070700da42c5580310701c140b110942c0c40d078100c465103002c0c030340c0704806c0c09050b0000202045c5041e510b0760001030780540c042180d90001c0680a0080150300d10810000d41e01141c1e2401c040c2c8100e101d213411103001c40001860108001d4112104411541c80007603a803103110031002c04120582104041c03902e12070080c0070035800341c85403000141c0c01e4500000c426862580d40030203103081c20151100c101140d1141909194414401d001d192000c500802c142032182200320000d04c154140000c01034100d9501410050405004021071030114907400303402c84d002981612501d0b000415601b00c5050002c03080341050341802500c030714a0038450001a0320056034012032a00c01e680e00340e6140712061503106003d15030180c10440040020707000c680d0140044003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 783844199 1250 783842949 783842951
    0x406260402092502030d0c030504030203160c0b0c21090d020f031524011b24020d061a0705060c0a05070b01090e0f0d020601051207051f120b0604090c03 67
    0x8650760804003280f950b0181900180c1c070201c2c4660346c20649000702c4020700010700702003003903003000d4400a480b88207036141c0502109121081004003c85281110020200c00c00d245844440c000903994a8820880b0603d00b1000310924044200070088110f40840c0b00041039a5820140c66003405100c50a51044c507a05000300d440180880600584040c07142050100c2172103681602610100e41b1090b90004604001c1036072401404102d201e40070146c020380100102c0d1400c3c071501109000e21104201c906261800400c19010910f5140c21200030b40341c04210303006211100e00203c201c0c6028214000e4100d03400500480d02d807410140041945c5002403408518202e002c0d111141040401e80c0403113245a074904034590003200a02410204000c810090b08060351841d0000b55038541c10300401e40315450150350010401d0042180d4001080d002c1c00308119140364816842140c4014801d00700402d460004280c14020644941d06442c00b00405060405050105e140c000b400c01c00c1c4694145 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 783845449 1250 783844199 783844231
    0xf060a0b180a090507060e131805070806091905030406032403110117060d020928050a11160605150d141006030c120203011506020102040626040209 65
    0x18400c40740014800c800000b80407411030701c41c2ca41a49852055030050080105144000180ba80c610669103803048a83c0c0011510700118524280140c1c12118020803510980000107040c5c200403868600c52080c00084d1940c13510340355601d81001c16440b00080054104000c00e0141f940642c1c0124240074401c2100d000c0e0415502d85400315040a40007074a610418140d102c2d859a441250454200110340b5490007505256000c21000070307e2250007440b8000c4c42d00000c80401103586100d0301180390b4000c0e0551900c0c81034248008000565800318064204400c1800620072002141c0e10920b0036003201100c10515282d9000910001d428180c464076401c2c0b1500c0303a40d80d8495410308440c09001100c101d100b2009005251400140421106a0406a042003c100071b80d800c3e00480e64000c0c0c400c0f000702c4403032000a0040414410030064641200404a0b500da070550245c801d8840589030b00318020009185920304804102400d20404a010700080c01818020301541e007000c0c03030200d84680303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 783846699 1250 783845449 783845479
    0x30f03100b0c250311040518160f08060618070e150a18051302090301180c030b07050f090103020702240703030609020a0e0907020f120a02010e0f060a0b 67
    0x5550141004600580c050f0007643c2c04210040c2e188079194112140f9461400d1844c0e80b28001d00a4200f24244107a581d01b001900b0466400c2c8440307407102c1440c06556603882401079912281925020b1019032038a00c080126911000103003c500400c8001c080740c0c1900441a000c41c540c16009025504100d44040d104500f0f0300c80e40408070700352100d403401c1c1d5200c00700b0842c000d003010f003080c000c507500c2550346404000940f10403040450001400b00056666100100030034058080c1c00340c41003480204e071040b00c0070701210070041003c0c1c9204689403e840e172200f00045490703002d100b00c0b41004000400c4800420f41c023079402080c02e9440134000400e01800c254402c0e40541c0c80d0100c40514140c00240141059818400d10010f03005100c411800c1202202004000c0c3c80f981303490714001c070790072004500321500800080103050803040c11140c40d248140f4502c0f41c1904403824180266007030454528031a00b0119061030700348040801048030396114040880a0020894100d0f0402c0050701e0b6420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 783847949 1250 783846699 783846719
    0x60607110d2001090303200c1801030b0a050403020c0f13050403050c24041211030301080a020f040b010c0201120e100203011409010e070c0c080a050c090702070503030f0310 76
    0x145050003025032950b2203424200e0651100c0740030010504000e0070003010302c0080d412510700c0103100304040300c1191020100707080d03d19014501682681c030003000f4540020000c1e1200c04141601d101d05810070198442c0944481507600030741d00100580c105d041c003c80c09040c410001013904500800c20344610649060b650121007040d45c0c1900081e50008420360442420096601c4107050041001e503032444480c82041801d2020380020b103500303280c2d0700c0c3c54441c0d1f1041022485190343c042c1929a203513541c403c891fa0314040303080220301807250018401c510740303040d101d0202c11000c1a15110080c590359030045403d01100301d88610002ea441c2d4203410101d40800031801c894000d500700590300d505200651144490001005120f24810b800620150b01c0d08100c0941060007810645200041e030303d00018000d1043d00103085902c60b21403018180200013407012206481600d6a00711512402801c03030f2181c0440c0121501035001300724960b8000094402140d128803805074030100a07440e240890 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 783849199 1250 783847949 783847969
    0x23100e0d03031407030603050f07030804090506040209060c0304060f031103040b07050c03040608100b1e07050c10080f09010203091f020909010b03070815010c0f0510060b040314070e06060711 84
    0x4d00065951003090040180070003070301022000003401006080d15541c0c0e0003545120b1401030b100035903164004680c0c50f48458042d18015000100070540792880f002c4542e41da50014400c0c200051490550280384c903000c1c0c42208800c82ca031155042c699612500d6104900300060141802c00500700701300405c100092000e00040c241981d244101ca0403c00c6180c00a0740030b68104445034030007001000000703180c810b921090790600c072284039200d011078101503003002003d800c91504500083c0c0d098000382e40c0402c125101c0c107410301c2c00021940351b88030304500301e000c100c900521562002e0f41c0d8246e81041c10907400c01042c0115000752030560104007040b03621800703034807012100e0b80100601c942c084c1c2244070f040e400001c0407081c10701c00c04d880f00000c203440004000684a03441051510003886820302c0b030640769540750842840078030f0743c42503588220342c410b11003503956049101108052040c0032407420b04580101c842d40c226a12640300304040f80d445031604491400c03012203001c4203519250402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 783850449 1250 783849199 783849211
    0x120309030b0c09090a02091804050f0d030e10060303050d240b1c0902030d0f1101140105010306090605030a0326190606020a0209011a1323100e0d030314 67
    0xb0740d1035040c03030350500c4152200500701c0d0302d0040c01849100c0c481e07110004014402c55251900d8011510b40342085418012100c8020000d40a0603d0204055425403c81554034400004850014240f441a8000c440580c00010000b40040050f0001390950740c0040039424440340d07000b055030201e80e440f02818201c0da4094466480c02180c6d03100c40a40b602d803d020b103206140c00500c48000540e00081d2070311111107515043c80103441520f02241e2151880740e01d8014510000c20000385000c8007411080f409128450000b8100304002c140030245000b000100c3d580900103000c4080c4660301511441d483c00104544161119208103c0c5800e030701d0355500804194070001d01001daa000c03000203441319a08000b0541d48000000d0f0010384035007102504440100c07144245944400206c142c007440b03181c00f81c0000c1210401c1c00305421300090b070751644d405065010a0300c4400c1907424007084402d10009200454119164545203044c0b41d44510003541c0310f46000220842d4402900c10112819112 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 783851699 1250 783850449 783850471
    0xc09060d140f0c03040b1306090b04110d03020c0405070c0203060c0405010311090904030c02030c04090b090105011a0406030b030304090218100e0607020d020a0b0c061519120309030b 80
    0x46004004101003106401101109416400f8500307040303016a14803000d130000b00744400c450001651450051b00d21202c0c103500103014403100c02c16041c1414480000e80341903c8034540941c240b03515282c10b0342e0844107241d168001d02150800c4104210040c080100040d050102191400300180e41c2801000c0c0314200310102c447d152400e1200050840701da441100301070030005c0054403210b41d2245412a480b907494500101040020320219003090400c03a04c5c141c009080549110401045007242407082030242d0082200380c3e07039400c0303141c00c3e803825281c03031f100c1321004101c240710443c0700b40c10170100408090100c0303191940d0343c995202280c0c03102c80b4420301c0c01d40c03c10441c00c0b1450802c80400302c000c041d02c0d281004560410004540e44a10f0000a204200c4902d880046441b0300702c1c484010704d40a0340990729601e0862011742c881c54115180c1c031714010700c0c085c0300c091403030400d580b001c8030300c000c0d03e41806447c10410031002e5440e81200130b409000e801640000015580d80055100c0c5810302d030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 783852949 1250 783851699 783851711
    0x50c04060f0302070209060d061b0e09090a020f0118030c1403100506090a0e0a1406160804050a140102090405070306050a05241b060a0501030c0509060a0603050c09060d 74
    0xd0050007144544404000c060040211002507619519810741106045030030062807819403600e5001084003401c10350121a00d1082002e1080e041005400244801e45212400740d0b10840c90369102c01c41d00f40300030341c000c0b041842c80400754401c0d903402c0e194000e080410751000b80c6030b407a5090748100c158003c0e04541860140140300341070a00800c40e00804d0340500b0f1080c2d00b0079000107090150020701d4050703075079550000c9080190b0100200e900460f0070842d02c1d242c142d4030030b10240c0c69a0089803010302c02d40072528803d40e514820440c552140d500b10010300b00017081a501c0011301003036044101d00d00d41d005d00a400c110b0b5501e01c500c6000d0800b0361400100e4038a03200500411014650205100c1ea8028401100040c5c40c1c44240f005203105110f000e0b640d220261035100c1180c00071003141c11a1050fa010803800d10016030003603060b00d02071541c0c802d145e0794900801c8201072080303d1407600041092000c208040c001d4000310b4011500e12889414000d256010860301d8101c0d088440c001d90b20b4035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 783854199 1250 783852949 783852959
    0x6020d1e0c140f0d0608150c030915270d030e0d02030d0f090c0902040f0b042d12050a060b010201020a051602030705060c150702010c0e0d0206070204050c04 69
    0x1090300455444041403111412514000d00b80c800340400c0d007498004002010102000001d04854242c404400e04100c030940b5034840ca542c400c03041c0310b454101170036003000c038a4600c2514156441101c204000385400d0b001c1c5944074240100240800d01d98049001c1c041c54080c10810400c00e40e01c1600008191002d00218020290340b000000700d01a42c0085e4203452640b0f0f408405c0795501b100c04e08010620800d03a4183c08010301038a07c0140c5040259000484c114186400900071161210903404600c2d0700d5000c1c0480038842e501c85e280c0038070340c02c210a0782000110300c1c240311020346e250702c00e8a815903070301c00e4143d02001503d070886060b009840100104040781c403502c0302402082c0b0007141001440c060150040c4160708a842035150b41d40c0b004021940e007084410040d00002e03015036241c1031203d0701e0503901ca511024906640583c6c00000e48128414072036031552503200d0340c8030b00707481e104e50050040c0401c1c5a403041c1c0c1c12000c01c010a001503100e6000709400340040300c0c8025541c0b8030f40303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 783855449 1250 783854199 783854231
    0x130e030a030c0e0a050108040819020a060e03031501030b040e19150903020d140c0a0804061d090105060705010605040e030901110d02070603050c07050d08010510170103080702030a06020d 82
    0x42d945400e2001401c15410161100e042c03ca0a580c820f0903e040580c8807418400060701440a00350307a01e10b41c0c1c0340004d18465021800154040c1300c6c68044c0841c95101980d5512404207d9803e400c40c0480b14992a4944c0b00e6046140303004c40c0504009039054401036803d08003a400d5650620700c4101844100412880d1007400001c6e90300c1d4a0308211142d80c69600a458030503084068082000050030242c0b00340c500380c22541280c4d611400c40b5051840c62400380d4058000d4270031306022542840e1203480449811340d02c580d5030900104001516801c000402400390480c140a8401c0e41d0f80700c4020843d601c40740710b64500c08a28000a5869a048000042c1845008074607401c2d5034014800303c1510796000110306040c1e13005420041207a07075071035039040294020304202410a2007040c00c0f100100741c000f946581610700c142d449040e407858000c81903460102030b12000a2403c4840010800f194901d0041c2514900c000c0680e00c5903a425100c3c00283e80000e5041c0b02a940d5405010b1001005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 783856699 1250 783855449 783855461
    0x60305070617011208071b0e0a0507031406120f1b090711190614040f050c121507050f0301080708010506041802040e030d060f0513110414130e030a03 66
    0x11082c1c141949604140030070030030b0104044000e0040b60003050380b008100d81a80c0001c8651558a220340005603640360307001c2440016a56465030514000204058610a008041800301034186684107900c3c2c00c0c0510201d442d500d4000c0d19075001d040382a60b0b94400501c0900751150320761640034003288181040121507031010b040c9800b4020700b013110310071807000400e0006082d050651445401501800c1050280c0320240c2c44480401d540c40401081086026003540d940d401102190644101c0000384184400000e4902c034459214030002c03460b4101e08080d01d944842c0c580381840c18107a0021290702d10760401c0e000300e551380d005800f00348107207002440b51940c0203900720b8042c08004074503940340706003001080020707000fa51501407422100030104115018400c6030801080115a1400031211007091405000d20801c0208188001442c0902848945622440e0300d245061f2426910110f035806400c1c0c070640010300c00c600c981d080c0003207100d118121aa034601a5a07070326030b515001011161 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 783857949 1250 783856699 783856727
    0x406360c05030414061303121107030513090501050102070b0c0f0f0d021002120606160b070f09080c09160e0307030c050f0909031c0b060a02240c0d0f020903010603050706 75
    0x4007100400c0700ca040e000201c022880e806082c000c0654108d0401e42000d000030f0411125000c1303001449008040d446801801c0300101400160728042c0c444a40c14142c640070311803072340180e100542c10301c161088040180003c1828508545c08000700306402410402501e0205070130350441c0d01f000500c01e805210b50380492035408001c42c0342001c04640f004040b0b10103080b403401101e0201c3c01201134041c2c0e40084600075048800d64009161641c0010187d05010200d880024101e0000240e5500c000810903403260000744081c0e52655245469110a0081d070164410014104450f030b40d01c0e101800044061400341803111151820301c0c00703110b419000010340034000c40106040061501010040d00c16840c04841d41c51010142e460084014020015500740d002c40f002078421403182d000241e84200f140304100404001d5851240002201c00880e4103101d0340000b04a554000c040d103500507142c1c107e01c0e0f20014108000400841d085602c00d0300308998036888003e081c001d440d005031403000c44071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 783859199 1250 783857949 783857953
    0x706020601180924020d060e01030f0b061503090303070e0f0a170a06060f090b010206040f060c300e1f020f041a180406360c05030414 59
    0xd450078003080300302603455504012403643e070b040c1c880400008501d650381da10901c0340c40d03081500c1000c2d11240250300251040c030340d1900d48640029030808011181e81240d800c0150314000300e5290300c80c14800007004101540c81071954140d1280c0328003040242d40942c854a00450316490f2105004d012800f2994603144103008181c03a0b00700315600c070011482034400314608800e035170004a46940c07400040000040111b403d0290100e40380c401e1010301c07400c42d10540e0042c402e100103403005a03101c010a44024000090182048001c80c001790041381c0841007910b81280c07260a07515a01c000a000e2001d03910b07007018188140d1200e12124025203401903019005001e00c4070422041907410f00b08a007020034840d8000c01c0f03440301a4040703001c2c1c8009101c000c400c04419501c542d1041d02d250302541500640c2030ba070700301000d944c1c2040e106500c2a94107214210041500203034407210b084144e1000f6465128554652202d10280750182c1d0540420703e4460980300e04091520307540960810a0041d81a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 783860449 1250 783859199 783859201
    0x50616080c0d09140328080105010c080f091005030702070b130e0c09040207030206101a0a0e0f04020d1e0e1c0512040317150a051c06050c040302010207060206 70
    0x11040107003101e4842c082041c000450000314a0043c0500303403501e20006003800301040c0300304c141c0c42031520846d4242c02c411242010a15154094591050a029450000f40280c28400004e100200140140d00070b60400c181050090400141d0208440702087c000400c00720600c900c03107404100c10805855035202c601d00708481a011405501d4981c450400840d49040209464910813000c4800d4518082d0040d550b40800c3c0c10040d643d50340c280c505292124450780009078855003c0f100c5003010300b901ca41603181540900080321800c1111807419848945503420240c0c5907954401401d00a044410101d00d1040375111009c40e00c81c24240d064805081c0340b04081102d0010604c0489928441c81e8298200e91030781c8200c4071400746070300a1000400b00f0040c801890780080103441f0102ea101700320021a0313266010f4081140440e11003039000f48461200380070905d05040c00001d0784821076003403243c400c92600c4507400e640c019601c1802d000d0340041e0078401d55038140074450140405000034902 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 783861699 1250 783860449 783860461
    0x3023109051002090d0b0f07020f01060501090b09010318050f10050408070b09030c0307030806090106021908090429100504061b02130228020106081002070507030f05061608 76
    0x22201001c107082c09641d40011403a1407981c403c400400d0382500304d90311034541d10f014071080c0c2c81190f090b19204094461210088558401400707500d040c0c0340103a45000c101d5140011900b6981c1007079407624107040d11000171810202c807141740041c0b03950056000b4419544048003050814000075080a031090070002040045881c0d10126104585d00c000640001e6484055550450043c01c071200b00074000000d0083c03c0c19441b01013240500f0044442030401d99940400780e998007088904068050450250b13800420001d1000d03008441d00604003003603152f101c00620030720100722120542c407020f80e101d00201500300701547d05070100c69800e00ba07141078144030001d4604440b00610085580c0144a100210f4407200e80540030300490110554581e400100c198810000040031600148410340b04540030034814000c610031200c0410140031518070300e00c0c002000e948040400e0381d0178840c1e80c1002000860003450300c41c141c0d0040c0042c1c903190070f00c020705d05e094000300480b07070301001540814044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 783862949 1250 783861699 783861703
    0xc100b04090f020904020105040e150108060111150a020d0207061a01210e0c090424020f040b1e04180609020f04092408150a0c02060714040302310905 66
    0x8400c2d074040f50001500e81d2517200403111480342c0c1e0800d049140c0041c0030b100001a00910700341654209807240c0f91a0313036070a8011202c07985a40c04020f00c07640064010502c004840f9050f40d0000200711000d407600350550000c200742d92012070100c4040f540c40510190303400d03014040d61b450381d40918042d018008a06581403000c92062160000681e0f01d610009031703100304004009900d10080c00c4241d8510703007030802480311010100040c03420107108d082e22003908002d00c22100c034500c0000c1901d0916082140660180d0051078644006223040742c21010f911000c08054001800901f940341c05040c0210304086c10f50703180ba404090b8203401804407442c1c000d650400c0c0c0e4103907280c00c0d070300042e028003800c1d404400a01030303054107901c599002d0000c152060040380c508803032220159014101e0302c3da0000e00080761440800c100050308070b64003103041c6034420062009046044100103080a889400140b00c076010401905101c86540c1c00c42000800082151681d0380c841e00010441148180c03102c903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 783864199 1250 783862949 783862973
    0x105010b0a0516020a1203080a0509030a0f050706060801150611100209010c020a06020f010e0705030c0f061b01020409060806041a1803030405010b030106050913061505060c100b0409 80
    0x802030042c040781d440c0c0106001100b103030105800400e0088102e6442040a02d034010580c0d0603400102c41c6800941e0f458202d000c1c03140038111a000851420f80c400a0403915404061103d0040203000c101d030070040b83d118010480504072403400001c450580d0060160301c0421648010207201e46c48404110411010842e1210b00c01e120f0400b5a55443d1040100d5070003c1707130b410080d4818611540868041d81c0016100740701075240b170080040000311840141e883d601d030710400c3c0d41507100b03848108582c24022a080400903018107014100f041010035401010080038000c445a0350118080000e102240645002060501e01074461030405031138402c2400c070240a07008840c0003480100302000307070044401e500d9860a00a5070b469003010701c0c002d40078184442c4040d100e903003000404102d03031520a00c1a80606502e14032101e00d551950b44002c00b410350b521021510300401e40d40003400351200c02c020b00130b003200600a0220500d85001d50001c46540600003806640351443c0390b400600300701420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 783865449 1250 783864199 783864217
    0x30106080a020405100e0a06030b130c210b0a1a1e040504020a0c0605010b031303030b01020c041a0a24051e041205010608120304151b1d030105010b 65
    0x4401030399540108400a882160302c0103400c240184040c007078440d884902a00b16041c1100d01ea00001e80c1c62404a0940700c03000c219961007500b0f001e030002c4a03d41c5a0054510b04c2e100c0c00d2240c2c860b0044811900080c440000321403906031184c80207100b030301d0002c4900020f0010f8604101607129409100c0d111401603d0003644641d8943d03092680c3d079040d0b031702514001c21006200750355400024030000e0098508a4003103602a0800c4004507001c0f01d070b0700a6922408204201d40e0301880d04c5e88049015002c041506c90544c006d035626000e058440780110183c02100650304186844042c2c107100d0212002c1d4400c1d01c000b04d560000c0c1180520085c10011305000a2400c1d6844011000d510042c04042c1040d000c580071001800041a03050804c0d18402c69014038001c0020a54600503140c1700c941d44100800700000403c0090001014580b111a003512030000015050310844c0c0101b20103a400710444003c2680d091340710000209c00074100940c900d00f42d00a100a501d0405030914900600c0d400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 783866699 1250 783865449 783865457
    0xb10090909050a1b050901050607050a1502040905010608160309030207060c0302030c011805070b0a0210020711090106021b030c0a1a390a030c06022a0705041b05030106 74
    0x98801c0c404100803a40045070810b42d13104810001040100035503905203e5503008001d580b00000d1986420000c1c1e482c1c0c10b821101070300d10181c60380c0c0c48103404204081000c0c186030f800d100c085040c800c00d115560203410307151650385950a0600d060f02c900750151000200f01418841d014000035030114400044592a04080144207858502a8150300803202d15031000d618291b011101210038003400c07080d450244041e28856915440c04013170612400303a55601682c0005681140990580c4c020415070f4007070700000100742703800d100203001c4d04021b80c08800182d00c000d54282c0807a4044a8075090b507441140188043c00d00d00c400b2030042c002500c43c40c14503450517500d03c0520f001e51000c581400061131282001c2c0058403068401c41e140d460040032100d03403074030000204040c000907070700c80e80b54040d2030300f18101e81145d80d0140a507200805440c291402c40310b0400221240ca940784240f26085400340c0a0942800c0611048810300070060104542d4070040c3d411540e01704080382e054402c54070b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 783867949 1250 783866699 783866711
    0xf060909170906090306130c0803030103082d0307020604031107081507050c0613030305180c0d020105191e091d040f08030a050f010e15060d060f03050703060b100909 73
    0x2c0041c0300e9000d4000c0ba44c2e003600400c410080c4140d040b044141502c0e108001030b02944d85c840c0f400b195680424040100b5046041003c800f032104071001e03e020302c40000c1c583d00341c07102c0c14600844254005540d4140564428800e220805800c500d0102c66514114028035a403894a4501c6581d0360800000b8000c2030100d10114210754030034011100d040c0c000700304480035030a01c0100c0b41c25080c05c0300402d4001038031b4500410341c0d074000300d01071140601120f0002c19111a800c82000700390101c1d140100e052203410440c0b088040c002c0b284d07000d0400b0042d22a801d1203040140c01411404030b44104a0030020714200030301500a20409150f046105400b21070f8281d650b40ca8144814020800c2c007070000000882000b82d87d00507500440e1090340610400f03151a607031040322000a400c180c0d5003040c1311550502203074941c10300402800360942c24150200340150340f0160203200000d2a0400e440782e401400d014802e10006001d1140180025240e0350300c5101c8944c8000c0c11071005004400340203031603003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 783869199 1250 783867949 783867967
    0x402180607020f030d0203071505070f121401060906020c040603032a080d09020f0a050f06070c0509010b1314130b010c051b1e061920010f06090917 65
    0x410402405005012220440d244010181d070b0794208e49421544a0301ca0741010002040350b011303140c041d0405841d0390700300600414065819600c0000030038070341550380111400b203081e141142d90003440e65445e0f1980c2e00f0700304000203007030016416925001e80d0a01c0c0f41040001d5001c0d40020015644081080c141c42e801e0000c41d00801c01d0406c003900c0007c01140d00e02400d01d0607413280c132407188210b0b031540483c076000003842000a080d10400d0707844a0780b00c08000316402c2400081c030303605105d240c62081460b01c48000585400081e0010300300004081903000c0b0a4041c0c2c0d1031075015041c4219100200d40707081c0009400c41c44801c060880654407903c1982c150717405907203000a1103910034199501a2040c82d091400300840c800740d14807503e0001030b0b00184454504ca03c085001c030107005c203480d01310000042005404d10f00710f0030f4100101000020200c1502e000c11060b500007460000c02c0341c0c1203004062080d07402903041900c549240c25400350014126850468185403044501500e0f00322314 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 783870449 1250 783869199 783869209
    0x170f060601050f0f22091503060c0c02030601080601030201080c161511070303090203011a06300f010e010609120b150d0501091e02011b020a150206070e040218060702 73
    0x64014144c040c0c40102e84500743d01d6104c41c80390324000c0001140040e466680f5032800c25613800c220004031042d00c0080070f0005c15026001058009035a051690f0400707829400309113420003d03030086040380c1006005008540e40300c5a2690402da40b4400c00303040404250088401c1007080c0d00003400d9540e445811a9600d1640e00a40031484446c40c4440d10f40c0c4060130050007034040740008921952810818030810410100d40441801001c0c05060403d41e44004d280d40f24817803007060070900b00c03178580e1180350b408031240610f124070301032840600d90754580550722030f00c007006070800010b00c02114000d0149082c2a0b50681103290407544807142a100d02c1210303103040c0484100e940d0024006503402c07082c0300054200721a0340344200b0a540c0610314045200c3c2480102100003400101007105c0c009410f41c8d003084601000b400206001140c1366103550792070511050707010940140c2c000d00200070341250880440c200c042e0064806518000709030648244019251400d07611802e8081401c00a40d150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 783871699 1250 783870449 783870457
    0x9120310030b090d0f0306082802041803020c0f1818061f150507020613050409111f080c0c03040b040807150302090a03020433170f060601050f 63
    0x800074000b5050408685407107010025840000c20b03149656400c041e482442003004847e035820181101d407060005403030211400c5818406030341c040b05c0400e80035a0380d81c8201525442d4584440f9014102450040d080c0250010600c2c400c142e000c4520f1556115500101c1c5645241e501081d500c1d41c5003030101d00c2d0609030038203022503481000d0401031304049000040c110350148060020102c0d5981040300343d00c515420404e800550140302800040c2000703006020030311400d00c503200c021600d84022904588201206403042d05c0030180c4036541d0306005030307140c1c0b104241c144500180d80006d1400780c50910080d1428075010000240398084072410710544000e002460380096071141d07902c4030660b50700c00da40541c070108000da15200701664001d1003216a280c4020341006d243c01c5c910380801c40242180d040c0e1580c02c910b00d07100b5040701110b1002d88541c03284886030b44009541441011b00700e0320301c0240800c003e070303000394049a880308002540680c0842c007460482e69a000c00c1088500e1401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 783872949 1250 783871699 783871703
    0x3030309050a0c0311030f030f0d0b030316030e100815060d090f15060b180402030a23040c060e06090906010c0209010b2d180118080f150912031003 65
    0x103c102d004820405081041c1c288808110115502600c051502c01e4403032040c4940801000d04c2041721880119107a0005a00309400509813803e121422001d020341c22544242100090900400c2c1240b43c580800310214018880c909816540341c4200c5c28201074a0701c40c80711380304450118141521031110b4000c0740f030341a8401c101c145900c540b80b40c20041420300813007000710700b4201840891000c0140c000d03240000502d101e8620310540364020300009510181500d0802c5484038581c1c05800d012041010388408400c00405081c645401c00d500c800c0000d8008100300700745200711218690fa50000d0315800001141c80a841d5103c0c0001a91110043c0c000203400c01d41d103400006092041102030007845102d245104d401100804001d2040320448410441b228418084400784101d149007409120314103040283e40b00005185403c0031310311a41c011005540541d08003203800f88240862100100c0c00d1105a00b00c1c18888401619442030781140c2140c8003000c000a01e0b40303140d40302008019a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 783874199 1250 783872949 783872963
    0x61401201e06040b010519090207050304120f0b06010201110f032d07031109010f0503090c040213051311120403121a100206072c1e0a0b0403020a03030309050a 70
    0x20320715950240e11550700315400d4a100c0304200002a1340d0030081c1040c1400c011120f8915503281c20900d0740d4000f5000b00d0400ea40600c828000410050110301d130366a88240184041c00c80440a8900946944070062a0504690500b003520039114803a03030546400c5901070800c65166610340525411604007121484d1000c1c4d81c02401400404605513098042e8240e0390303081c004501c1405030100d9600c10300700158001010f146c444101e40f48500003550700011614140c0700c0051035100014143d800aa66104800b003030f840c000c000c40d01d081c0b10a20036142d1782d5001444060a4208140c1250060700b181b0310010b0416000602010301c03c0c11018a2068a580104001d4090388280348280009507902d0703014039210f401c80c00302240005a40d0b0310455095a84440030841c0c06200740c1d8201c4204250020048079640c0c061035a03543c03142d5800e03407100389030390f400c1c05030500c1c810000c2c50308a0707601542c5000d00402c01070002d0780341d200c00071050f0f035098280410044111300e0081d00d40401148060504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 783875449 1250 783874199 783874243
    0x30c0e090f0f09060c030606090102010e15150301050105060702101418010e01030504020f3003030f01050a03051c1101020c0c120102040509011503020c0304120606140120 75
    0x500441d01640140032821654485a50f01c11500c0d65598003611441074040051000558038580724004041002042c40042142c011054819241240e0100d201407942060030400000e4221800d02c031a01c208218024001c1d5454140031400d14405c03520007a0081162100c2e0340501802008092100346840c42c10580d00c0b004492070100c3c03d810000d1f518000392509500350360561083c040e86000796001011802400500020020108c2482c240391a051146030b501e03c03165030700484100c11520f8000c02850b503925016003201070f0071710142c100500c01e5114510034804680c0c0090503503103079031686030f41d0b640c2408dd00c00166031a10041e40e06080c19800010b03150300c8120041070b018032440c41507920303164012020040c10709030700590041e50f80019808004002c264500242401c2d42036035400c00600e4941c180d603402d030550b44a0b400200c0342d01600244501000310501c210802081024400c41d0b840c2c0000700020f2032251503407110714507501002855501b600741807044428a2010208407a11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 783876699 1250 783875449 783875461
    0xb01180e03040807050114040e06130b030a0c0e010518040303050718060518010809030a21050420010c1a070207090606030b0a0509090a020603073f1506030c0e09 71
    0x504c0615000c0d03140001c1081c401c49514100110075141966107070100604640e9030082803000c9242c0c3e05e403803100c1c00d640b0341540300803a480900c59107982d0ba0080c941c404090b070402d0b182124008041e4800b50003410181c1481501402e9406120740060b03146c86c02244a849003070701201c0b01c00c903003000c1d8071a202801800003580da8004005041c0c044411104000c1250301c0c00064034400b000700c030f03a1401034004200c0c0001c41845001544400c25030020302e51121551301e44030f1411540c0845003100c00e6001c40d403015200d10399100001c08008424030348449901103542d5140207210003040c040901c0443c00d4081150310f4028007802c40034002400b810051165035060040151403100369182c060b03d1304100100d49420a04082d40c441d842c80402045a5030b0103909201e207950000b0884000c00c94070440c0080d505043ca60307501340c00500608500b6401080604103e80307140c041d0259040d01d441e10083d240c0744249020304400b00c58283c00c0002d880c03440b000c010b80d0900310028545a101c2c400c0c2e420888 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 783877949 1250 783876699 783876703
    0x803030f190b24120903070b01170304030b2802460c0f05010c1e0804030e010203120c0301031e15020f09060c150907030b01180e030408 60
    0x100c5110450051030081d4640c441d0941291a503030b0100d904400b1a51040c03040b48084642e8880580d0780000003854150490300000128009840c001d00350303000010041c0500001e11780aa001d4400c0c0d0021200c40c00104640950b280b0a070f12005061105010000702c0e12000c42644400c4c3d00148100038074a035034414020301c029404151880d413025081454903409220301c2c00101e25050540075222240c00ca800d130040b00035508220148200316158020340c0c0019601808150301c01d200d0000480c0384100c5090241c12454006d90070200706406010642600707501200054105401d801d010440694510040b0b007588540d0120108140340c42062142400b03440740114100c80c040c08100c05401d08a9200300001204a000070700070386641e80d022030f541d02c50f0394020041003e128007018609840c0c00003081e1540c200e2000a00d0b00e40110001ba059540501080c55024083e5009000c00b68119901c07140340d060180035490004d007103002c0b503440c0906981c1c452003156145100b141d0f115030b030b202a041d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 783879199 1250 783877949 783877951
    0x80402240a09090c09052b020310020a14030c1206041107030c0c05180c090f10030b0414060a1809020a030807060c0912081e0d0204090509030406050f0c070803030f 72
    0xd40700c980b4113103e41129610600606003510402010540014084c2405030f0801d140e81c2c41c40144680c3c425030000040c0c1c0d0030400104e0f01542c506e405a1034890150707010706400d5031945a0b01052508004006158028808549a8a401c1c0f0040c100b41c4d11502c01040040045210000040c0300001d400304c1810f802c43c110300340351481288038100b40c60f1a40d00307000585e2181c41d461382c4512032403000301e640070120030080e000400380034003403003200c101110008815503006555100800d5aa00c28041e040c20705010300399814502d1b071114055400c10a012a0241c105480342aa0040c4200310a80306036a1641011a0140d0001e05024180303031681000c0e0301551001c2407ca510501d000c081d014040c2c0540c960108551700e0754010360003d1802e84520500e64807600d2580f040f0f18211002050011414003d400100d903040401a2518140038002d0304888018140c03500c04c0e801071108108040e1f100c0c08035405075006d918444d455000e03041400b407510320307190030100c460b020200800c101c6a0080151f5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 783880449 1250 783879199 783879209
    0x7240b04110c07030f031202180102190b06010309080706111902190f03050c0106171209030d0e0316060309120f0e060a0207090603080424080402240a09 67
    0x10081c0030000c0c80c0095042c82000b140d2240c80c0c10080d0200f001c60002594050f40c40d00904100c20300c2c2e04c903200104101c1c0d000c04542d2100611070440e210607540c0c1002040c1c2540244100c405041200761506504014014801c0303040540381c00c0120308110756501a2602503500080038840034050703000420703d640203200d1400060b0119203001d604144002a00d00d091084120200c00b4406282c030303030121516403e0340a40070f201e0100110b4404c40024400c11009041680d4801c03200c84ca190340d0a401c08001480402e9510410310002c1855900800e402e0b40541c05818990b80b0904540d02107400c20300000880c02ca03403c10424000b681c1901134214813491441207880b50003a000048096480703005d4080004001010003a8280c0e070350810b4001481c00d034089004580803a941c84034944166019608100c0b049280418200842800c0803040307408034502c40001858181c0d404070003800c0300401000644100119142c1d0740484c05611000140f240740601c000b81d80b000d00d110040c1001c2140e00c91 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 783881699 1250 783880449 783880451
    0x90305070308071e0b070f0509030f1605010c030801090b0117070206041b50030d08060108042d0f021002120726130e060901030c05010507240b04 64
    0x507040300908203010801301180d2085407101d00ea1191401228403801d05180f038020701ca4200300240c0c8a0350304201c0c3d0145654800010803d010b0b07001216071a80b0a01e5108a040c03002c190784180009400c920a241514072900c0001084107800e40104c03800416114007142080102c0140244180d01080282c07045c1d014910203403d0014511607140741c00400d10520407008808050500c01c1202031904d03070203a610ba0210120105c001c0c6581c1b6604640041d09405c616040862a440505041c0103150b808102801d11400c540740100010703120350350052000b801c00010040f030204441d0794400068000c8900c3c101540709070364a207402400c0101080d4203030321032200c51b0300c0782007a14800150140d441e0025a030741400c20490781d44645131032070040d080e21031101003510501401d04140700036100300d0030200c04401c20755283c00f005520319407000d0000c0b402240750300014008146400191021908280303003140e0744507024200ba031440d1100b10051200f2040300212a044010380360403140403c0b4003214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 783882949 1250 783881699 783881723
    0xd0609051b0a03020607030302030403110111090301050606070c0314010f020a03060503012a0e030a060219170f0c1c0504050c0a0b1201171014071d01080f0709030507030807 76
    0x20480c49103107503c00294030940c20000b5100003403007074024640191007414041444024100c015003950005039001c8001070000c58140403c1c5801d0048a07008102a40d419261000b141c50343c0c0700600346400082c00d600414015040005400d43c4800340550b20300100310340701c400808000b40640b0706032150034403941c00e18501c0e089408491031018000010000981203810b0500f0040d06d0311500200256490700590784d541022506600007808140c107112030f0b00d508a00c1409010f4920060380402c84607442c0c83da0300f000b807680c818010060308044000006a203a1030f03142c03150309500205129000c035031803c100500007000b60000304c0840c0740c4400c45a4801680d1906210310150040000c84142c0f0001000104a03084501e07170b20740300400c044800d54541540002401003130b520b000081554940b06101044980381d80115004000b40e4030252107100e183c0c000740000e08112014201d2142060b0803c04100410301800001c002141d004080d14602582c078104003180d90886041501e080c42202 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 783884199 1250 783882949 783883003
    0x31c0911030f0c0f15040e060103060815040f140f06010e0903090609040e03160c031502030103030e041a210f0c011407170c03070606051c110d060905 66
    0x4242d0322094041c840041444030380c05002c22030001d60f10071880703402919124001c00d00f90f050b070000b03002411030041d022440d810142c000604440a0b9401400d440c3c100e002c6001c1c00070140d040c00ea400a0b0480031000082c07289040180721490821b484030440e201d80d0b0b080c6948034601041c254122244404141c07066681d9040ca90f40b6803007006031140c0d01100030401c000c502c0c903041c0d0003104210101c408036410019034040b44141d44104410555801c000e084041040100d0b141c0c104107c0000320b5000c0d81036514564018000c4480c020400d8821912030b0404004010048802107a402001700600c3d00d00b0041c880301c40b240400c480c8c1000c01805024001c401e95000051040e0a001040c0d4612080c2c0549000d400b1440d0003c0408941c1c0700007010825032604014005400000d603100c020b10f50300c1805e450101d044860306d51000780a003e100600a0310f14460764100e802c60342c1c00c80300c903040805110000034001442c201c0d00400641c649030381e18007408000950341e40c0680902e050300254880038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 783885449 1250 783884199 783884203
    0x3090d02010e2e0e060c1909050609130f06090e0f010605010503070c081611090f060a05040b040207120c1a0105033403030e100305190c02031c091103 66
    0x3480c1101181100300031855420b000510340060000d81075100040d211044103c0d29040100a075069030760b01c2004a0740b41c49110380c0900e1079040107500e0400c000341f09d14140210341e181c000e80344000c1c4140410303045444c03007240f01d8214030f0700385c048018200311107600c0d00d80e8031000340404080b2080038440d20b8034102180d201480303040e00b9138505840382d0f41580d0702d00da01140c164001001c00c4401d58024051711402002c02c150360b5100d60b102e544403140c070f041d5081c18025054030027030203d03102125000501c91603840310802282550411348010400808080126020307100341c010040c03500d041801400b050350703800305591801350b10a810440840c030b005c03008143c048500f80202640742d0801d5100010020000000354041555800c0009030406100001c4a4408d195031003900840c0039460314a100b454500405846003507242400c0080b41400c480e03440810803850518854141e80d484a0543c1c54000c109a450640b15104506509040111040040c2c2074026089841c240b02c070925511920740 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 783886699 1250 783885449 783885463
    0x714070503030c0a05041706180d2708060c04030506060d0b1303170f07120903020a0206071a190c050a0c060b0112020c030910020c0a230603090d02010e 67
    0x100c001581180c03900100c0b4040caa101000030420b0100401c000120101d00c410300090040340c030805000c0a1a00100d070741c02c0401c100b0011005600305040a00f66030b40c1100191a00c18500c01074181401c034142005182c00364650025201032141d031081160715800b03038000b441628414001c3e518103071652000d01011407060a0002d21a101c220001001003003040700c581c002e98024908440c2c00458001003080c002c0c02503d610640750040c00800000c1d41d00681415841d803004802040300200d01d4800a45541c10316000902c0f0390070004045050014032203404d010720a500013034170640d05108808800e0408103080c0c04016078103000c05050014054400e403500820b07139490b0080744942680d10702c4002c0514012203030500002000c0b9201c072840e640b01402e402c003481d10017075989405080420903a00303d15485401154400c510020480d103c1c007030408221005024903602a43e080400011011503104078281c225001200704050a4000680f000713800020b90000c01c0156000c0d403016484d421 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 783887949 1250 783886699 783886703
    0x215040228181103040b0a0605090f0a051b0409020c0102130f060314061305070c050d1116030305040e092506170108032b0c0807081f0b0d091208071407 67
    0x6004e200180218400c1c071491640710f801c01000081242d20b6074001042050255156031401e40e5510401580c0da0280c4901d5411142e60a41610394030314101004046200b2401206002a00811003241c0c242c003d4050314068491441d20b104078603140c071442c0e05038918030722401c00000d060030321140d0418500d030f030214042e00020344840411070307120321044c000d44070107001d40c0100b11000320044045002400400d4910310542c2c3c0f0b56410a04903885203140580c1700c00100c0b0044c2020b0010000603411804031806c6070454440e010341d82d91401105030500f441ca403054506408607200031034112003c4d44441c010754045803a2618a81c0d03042010400c01c0d1824000d90341658810001c04075141c10315130040b070b1110810700d12000d04051000402d0203907480d0305075403c00320700300b941844034403904041f684c0e502c86603140d0380840444100194503410003540c40b524a1301031000a0202d4801120b41148482907044030190980b001001001000c00804659800c0090404800204019664800c8610b400c1d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 783889199 1250 783887949 783887981
    0xa0c09020f091e0d14070626040f080708190203191103130f0e060111070303081003080a08011a070c14190f030b06010f021504022818 59
    0x9001c0700c1c2030000c0300440b400ca202050540d14800d40f60356a80600900d03115220b204c100700d419850000940ca440ba080c0c1222040c003400749081480941d80e003401c5011f52110020040c519100c030b06001000810402c40030300601c500092610038025000020081c24070380003500d1140e021014030481c0c0b00e028485211040c600603040c03d660b401d2180c112542c5007500307a07055a203400745003420782e0a01c1d50242d12480000c6c030143c40401c0210030424215610060130308201d408071852200141d101ca9203400f008050000748070106803030560319000320001d154070507981980c0d8410072501030310b40d001c24883c07220401e0600703121003400f4603000140c2d2801580010b840c8150382c04e140c02d260b030401600e100c2c503801411850f03410f101e070383c1c03058806070061a8007040070b5401805c60030080d04120b002000036041c005540e00300c0340c00f2a0b0004600b01247c100d10080c0002d51100d100040b07440440d5828840e41c3c03040b80420310080441c03800d041d0211030f00c00c03040c03040c1001000c419400751510a55120469 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 783890449 1250 783889199 783889207
    0x3030f08090316141011040306050702100e0105040c050f01020d0e1306031a0601080f15040b0604082404111003060905132306010b0a050c0703050a0c09020f 69
    0x600d016591031500100900141c1c0d041101408103d082c1200000c1d040e503041d0312900e0199024030302840041403d01e5103580c240580b01ca120001c403810720440c0b2004103019520800146250b209200d400c22400009a040c440c000045070401e01074001a54265200000c0709000501c80c035211012200c1484107801038510080c040c00150f840f001302a0320560001490110040140d0003803241382c0245204580e14481e66034600d0800a0400c0e0050403207041c440c2420500c0409181001d140740e000103040301540345094050046806071140181c0d80350007000206010078120008124149450340d41070301c0c6400c0c0325600710350041d80881034501800089a070340d00c81d209030503c00c54000c6100c40d035040105120366a44503c5044070021100d482610000b40d41c04000c1041411184030a45210754003450035021a88440342c551006200d56110600001050308609015034141c481102140e0261a05e4a5481c203000741c0301c200d0b40328200d8841c0d80000011501d28003510079210360001405d102420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 783891699 1250 783890449 783890477
    0x915030b0414280b06180d171801080c092403090303010f08031c1802040203043009060e010c2001020c030f06151f11160303 55
    0x400003040015000707926440b60384802d0000d110101e005611200c10b12240003041c09089807099070401801440c2030401a00280036501c05003640c032001c0214040c5100c4600e00c1002070b07450320541e0b1008090441c0d2249400b12990910041c050600b13042c0ca40d039040070281001102c440e041150f40000c08501400398400da42000e200c00e1051124610700061182c061703110440c2e9940040b0381941c01c943c00000148541001c0103000340080001c0f20046040400031050000d1018035900c42d00d100725561000c60144c0074a03120007819064000d88119624201030600b1445124801e0001c0010050016606152015240c0d485421152641c07611174050a10704221a02d1801184007410862a00c0c00d10021406005403402004624004d007103869050341c0c00039007403a00c100c4405100f5004030700905842840450700962006c010710002e002d1900940019821802e000f1901082c007040701050002d26401c5440c0003002010780c42100c54000810051070a03131141804028001122141180c0d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 783892949 1250 783891699 783891701
    0x6010c0f08160203060a06140907020607030509010221040b060609130e01110c0a11030f0c120304030605011d011203050d05040201030f150306063c080706120b01091503 74
    0x44801450b4040d03202c4860300080e1134113105683d80041d031940c0708420401905e8034080303003a911009540002c040d1034840c40c0651200d03c0104010f062548500c00102c58250030350403240c50710412040b42c4c00500e081c0d496503000031800c803000c0310318002440205600f49481c0040e69400c00004150b04500c0d07454130010780c01343c40c44d010741107450740d04c07400e00125080303c01003e880403010250040090002c20704000708c1914030502e0726070294002c040c0044044101044031200120b094940f41602e140e951f103040d24601c1540d00c042c241c18900300001c03134070340760042c40c1c200b044140304601c0c1926602d4081e001c103600060080180411400c1084120702221a003000e0b0b403007401418005100d01500490005403a41e89000242e0240c3d040021300410006109100140240d060907006034142c03031241d84507021003450078a03800084444c12103411400e01d0029005443e4103401da0300c0c295900c201c05090302d5850708000603030a0030b101c5c5401403940308143e44c000319400d00d03031920482545183d00760 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 783894199 1250 783892949 783892957
    0x412050a18090504021309020307050f0a050916080915010e0604090f0b0718050a03020114040801020c1612240623041b0807051c05071706010c0f08 65
    0x102844111141c2000350000d150025000306420000461140342901c1041082110380e0218200b0610700544030000d40c0700000c003941926000d5521310011901c00000410658042d44526841b498980811569480c0c3c030301b5144516250380c603008025102c0c080c1d0103840c0c0b0f401c007810442c40760302c89004200c1e420a0500031030b04090007800002c1c042c405a00d8440a11207004000c0c0d59055509003401034032540610494104050144284003160820b00015614502c0b0700c00030741004a8640100700914a880459000700b0000c0000c541d5941c80a03060394480204250a10403010f1401c400550201000d05c400340035544000d03100c4000c50000401c48895100554000916035140030107d80e00d0305030328000180103920640707803000c8090306042001342c56001490419040ad00c0c01110103950b08124007540003005410701b1070b02d07400360340141d2103001c103134000304d030901e90038038050086d0244c20444103010327040c42030714500300b650b9008019600f241405d4402461032604046070400320301c641000d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 783895449 1250 783894199 783894217
    0x40b0f0315040c02010c141c020315030a0f0507051f080405070506070305280903080931060b0a0e040209060702060a081509131e0c1503050a0203041205 67
    0x101c2080d540c00e8000c6022184100e005002603950340c0c01021601e9005400303c094412221207141c034103113441112048043d4000b0014910035000f1000c102580c41e480c4221404520144c12a5034801c5681460070318401524010380790b0f030040c2e640110b09030420120940b407400b0b6080c107891080350f400d402215040c800034030590b001d0080402c04200759952000802c0b41a000ea55501d807100e01c190015402c000c1d89081e200c41600464100600c1c81303801c071544200b06c030741180e603050301e59495401003070502c015100c892615800b1610003056070b20b10342020b00d0b003560307135000c082040303a481c4c24041100c0d109410560380410110415040c041c81c0c0f6400400007090b001c2c00490900a0b1507011442941042100501140135030040102c0c07001d42250803440c0070b9040718003010742e0410780074000c0e200d0b14207207019000100c4030024130354000400d03008131412540000842d80d820398441c814504114440d030b100740000c0c1030901041e5059190b00a5078059600405140e1114841c107005507100c0d8844035070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 783896699 1250 783895449 783895471
    0x70e0904140111121608011e030b01030804080f060402150a03091205220308070303020706020918060103060504050c040524031311010c11130f09050a0501050c040b0f03 74
    0xc07501e0a120a0003101c1400e16001c034590f8403072400c40e00e00b011802004150204d88804980924103a942c0a01242c0c112080c0940c00c84851040d00601d8900c00682c3c1c0014040340c800b10000402c00600c440100121b0300c400050701c113102d0a01a8240c1c0f0b9034004d46019620015100c2000d4075040e8200042100803118140001e80314035a43c4c907116807007410f803c3c18010030000b180c00701e81c0b0741032401c25841c2c103005951b0300c0c0805410766807803001a01482c2006020581d01140d60303c1082079960495100400c0107200900840260703007204210407040750300d28006820050f0010b400d081600509010384009030740c59042a00746414060707103442280d40e007000c40c10452140c200b0428070b83c0082d07004e400007103540700c4190380c0c506200040d1468034a14904111241c1401c4011070040404074020700c0f82164211080d43c0c0080d00c44000c1c14145003110f0403d482d240d0b146040180c0002c101000700e11640c028419580d505500c1241c5000702e2103240c100d070a00b040b440d901006c0c524002d5500c4024490 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 783897949 1250 783896699 783896723
    0xa140f040f09031e02031e09041505011d060301031e020a1419060e012007120b010e0103120804020d0b010603150e0912090f06220b03070e0904 63
    0x80003406032010100c40c8104103a0300c0e0b41007400d055003c1c100540ba0080ea0014801d20303411103400030b589114821258074a0a084106101c1ca40c0030001111003580c3c0040090003000358440c110101003405110f03080c04101040340c12440c2800c40346208024043c0149402d0441c0c1c69507c81d41d10308850724640544140e00038650340d006a441c04d045501804001000d044070313204260901c062012076250501101954070420800321744e01a0140c0315090013807824941318106900c825801590004850040f801802d0012840c4c001c41c84240d285a8091010410645d0f41c1d0400c3c80072909085c000684031400c400c04448982d80034294003600548050b1508003134a1407900e40f0702441d5001c0c0c1282e4002501d46000c0c0b80c1c803030b2088503540081c200300c00503400380d0305003062000da40300b40303002c07901081d000080b0ba625001e955007140101c3e0500040c145aa0360301d4106c4c000c14401c1c41c04001c1c1e400c041030700000850707141200d805803445000561070b0740c0c03039105401c0100a10082c0c024012203818075440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 783899199 1250 783897949 783897979
    0x11d0d05060a0b06040e06061b10090501150530032107020c030601090c0e0d06020a02070609030c052b030906020f03160b07050c01060e010302040501090b0a14 70
    0x40484848a00030000351200d4141016082c080d103122141440c4958820300c000d02008861080090301b0640c01c480d60780d500c80306d05103240b5110b512242c4641c4a80503051900701100c42e035411030020039203d0740003007201c421115400e120350f03c0ca40c001e16401814000c4581c0b0202c3c12400803080360b80303400f5409401c08012503138040c55688030640d004410405051071070b91450b4440095070300401a400502802564400403c0d502e5405100703040c0d949444040391845c3d80d0042c85442030444000d030082c907900459041000c0a03511034400c200061003034460009035076208141550030f17070781c0c080c4540748014034081c01c0210741d441c42641c1d55007001f8440801c02c101c40402c000882c2c403601c207440301041c00e440c2c09400381c20103041c04443c048a401c10029640c02001c141c007107402181c0e011078900c2c041c0c0c032041411101802680400e8005601c3d00202040c0c409060b80070504a9108990a000c01da807102e0071441518a5010010b400c04145c2d02e080c00a89015080c000d24210090401c00384600e100d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 783900449 1250 783899199 783899209
    0x30c12062e0b1e1801030f021813060f0b090a0f08060a0f060e040b180d170405010908120108100e030702040b010201020d09060f0b06070206162405070e10020c011d 72
    0xa200500c04001310341c603a144203503014040c0302032640c4030400450404a9961401150705405001c0074851a4400c140302190030342c0b032341b00f0000307420035012907100031703803a600038501e40e40c041c4501e580320300007131785c400104414246052402c0da0f0540000c1c02e96901da00d20080d000d003141c0040885816140d41e004100c0c00d1081440f81d101e10b000f81484003c5e401d000390f001151014900f05807240d0f40141d0035143e401500b05180308030360403408610b002c0c03c0c0c1ea1400e000380140303071450b00140302e8800016070f92500c05101d1030b980c1c1a100b0390350641300000c42d0350308180300300c606008508405801c14451900949410343c04002c40c6c89044c0000352400340c041020300c0c11205030398403c981541e42c1d004002d6044040c2d00ca1100a1582035421500d0508140c0010f04913005034021003918203c140055000c10656407007800000c50b61203410411070740c2403080300700608030403202480000d01c0142c9e1b869482c41d040c1c1a4103c1c0c58075680103040d00581d01001110101c090b0948601c1a2a020700005074503150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 783901699 1250 783900449 783900457
    0x50303061f1b03031409011d0d0f080606041a0715090b0604090c1a0c010e0309060301030206031b070c0510020c01210908040611060f01080304090902030c12062e0b1e 73
    0x1600000586841480c8050103650956591072040e900a0700d49c407940d1a0000104c880181c0e4504105c00c0c0c6549400000d501c1d0310954010062408000c5c240f1406404c580380981000e42c41707400b61160b1580c240199804680d01610058080140d2101054460030940c0c404211180182008408540c8458140c0a280b100504c540d001d008005140007003102c0030320a41e070070303900d400014503e414030090005581c4e000601010340b08a1000000c00d0400000c0c00a01c0320f65022011415220105414680100302c880e11829009480078500022024030219548013900c105865142c3d079940890700418145d000c0c014100c201684c0e0350308502c00b103038504d80036000504695580140c2d402068a4040c1880405800402605901d000501041c0808010703101a65180c150008400e840b6000181c94a8034041000b50010504810314a000c1d00201e0020310a0340c4031408001c0ca100c80c10f0206803000400a20291500c5160300e0074080540350340000c2c0b503000e600051411404554129020a40d84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 783902949 1250 783901699 783901711
    0xa12050307021e070501110a0f0b010f0e04020328050f011d030c0a1106160f0b01050612040b04020d020a0914180c130e0a050303061f1b030314 63
    0x4008010408002d42c10082000040000300440c540250082c6075140c0c3c410080c020ba03814000c46514050a1140c01c203c0c18881582000051020703111a0429014036602030180502014180601080e5001002d80d890b025941c081c00504100c4ca507c81e801024541c819001e0381c84c01602014003010400c00c21000e03c026400c2c1000040042c84950710343c5014001103600c1d000c9400a000301c100d0004042841356140d9080510402c640740460005085c5110b808002c140e52000d607004a802d00081442c480219441101c03800e5061b620f800820440e4041c6034990048156000f00241c0002c1240482c190407510280007061f618040d980000c000403580d4100103d041d564584100201c207540301b140380c0011309280949441c8810384400340d00c0e189001d10301401400050051949455030394000007805101d401a5003010b809843d00f03588940c000e45460703208410180e070329408140e42e800140388410fa203444d19500c5814049801d4002c0d120a0f0f403e400b807507179444400300d07103014040c031b101e108003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 783904199 1250 783902949 783902957
    0x5030a020f131a0a0501080f0a0c0e10170705270a080d080907051009031e211d030c01120b0604030b04030206280f110705010207031205070906110a12 66
    0x1103c88820701c221005603512444c1001005420b0003010308503230f80b0a58000610080101d2341c802801d2040e202c1205015855410014000541894a0f40b04088924110512091001944884030b0840b028022000100e6805160b510328000c1c407140c0b1020102d03104009050194241d644500450518144450020115018001304434080d9400e010080181c402142c06210030200003c00030300b10384050000030040d0100c42c001c810341c034440402c0c0c106402d0f804070342400301e00400721642201c96000c05400001c5035008468000c40c1301840d038190700d0031304082c0c01448680440c4004540d148292550004840e584607107024a51302ca0768001d101075401414060f50a0429240c02441c3c82c000a00b11401c2502084a81c0c640d00e0070110000041d40404101203864095070143c5401404088a400244080010b51004002c010b4028014a502035140d0208404090483c20305840c8200e40c1360340007807640441800210300501312001c02d1401201220b0b1010200d641d042c080440189403a0045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 783905449 1250 783904199 783904241
    0x40906030516030b060d060b1002030a02010f02180d1e050313050108040c05040b19090e060c0c030a03090f02040c090e1012120507080d02030411040605030a020f13 72
    0x400400c0000c241d202d0680c00382001c1031495515a06012280030306241c3c40350407503a49000c01c0c00f00b41d400c541e01510004000125007400079801a60f2a0311181002016500b000d400803000c05440c804c0d225480041607181034503281d91010810b1031070b8203040840d404003c3c02d03044d0040075000070105516612880095507100e80000d0281482400c1c1d0341305038100250348080000080f07407114190b08a64044c0c4002caa0540108000b8840360303081c1308041c1e08400005400110440d540d001894880d00c10002d94109846000016100e40702d0403a0f054500e500c00c2200700642c1e4807d81c01380e0040f88c003688000008140542c0014156400c09034803100044d500300c414080c1c00310112095400141d103541c104041464140e02d11a144c02030319014044101d4412281a014003c50803610460740c03000045503a8121b0780a00d0000b50401e480659240071300395800030303090030503204501c10b4810040080100e589070384d0801440700b010300341494005c1d888640d42c0281e1141030280c141103840300380445042d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 783906699 1250 783905449 783905453
    0x503041e09050f06011e02011d10050f010509010311040207060c030504060506090603070317091009080c090106210e0f010b0f030111070807060b030d0806100e030d0518040204090603 80
    0x54410142c107245000f40c0e10401d01c286a030700300d200300c0b040c2c0351070f00800c07040740841d44026030041c00755080b404050040e00d03001944000c008a10a41700c0840420204903948035140400c1400c0c000340541500b051a03000144041406e407070002d04440c034014009498484560754000c00e86d04400d056001081c3c4540c03e10003004040d00034030340d2011081e030780132440e8076000c1c000039a00c15032840040c180c3e02807910080400d0b8100d000326a0101c0000c6e1954010000c2c102004041070028452181207014140450415141c04181c46049807099540d00594182510802940e5102c10320500c220035a070300008001d54206025100b4025880d000000340c2c00e4221090080e8191250007052203030349018188044008604c05035044580c002c26107648402c0c1c54034183c1e00804041995075414030900b00d1070307002c0940c00000c40e44152829108000c1420702d100080c2d584402d08585554150044810b0744a09807003036000d01026003450103141942d007a004081401c0fa4003541280e020281c4444003801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 783907949 1250 783906699 783906701
    0x90c031a0603120f0903150408030115030203040201050d0c0e300c0a03030c02120f1b01080702150a0915061703180913120e130c02030708070503041e09 67
    0x1c0c1c04141600034100b44070700d10301ea00d41d42d44646410013452000100300301c0025241040590140c4141000201e40360806d428450a00e0b0000d01c1030500e082001e20f06c1d031300064464000d0780c0c080c03941a19618281608082c200c0d0180803400244010001042d2091219640344d20003411708940340300907030f5106804c100d82460081c1204000300d515500044211546840303401e85c0c41c040b00c0d00352821040010a07840010001808600060190300c030b0780108405002006c03c0421031510320020000b500c6958000545071040200c0e00c11000da080040c680040c0116401e866078000780054002405a611f030341c4401c94503400303520710031001c3c0c0c0e128001e200f0f40c443c4080c8030440f09400c800860a200c036041503900b01e240440d483c1400760b80050049954010003015003035443d50b1003000300d83c0c14501c03048010104124028000d115044c002c00d10b000980c0c03148150400380807140e01462a0a482d0b0321011a954400001101e981c4001c101c005142c440184402d90b81f0041081415103461400141c03038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 783909199 1250 783907949 783907951
    0x10801060c0c09020c0f0f07050102070f143c0a050d08043305030708010506030705072d0f031715010c020301150620190b0a090c031a 59
    0x310500c26030110120100307a005600000f101d003140030243c1d8a56a03ea850780c00c2030707481e0100c1e2015100e03421403d0090100420b0704010f6034401c0c0e0881c1c1c82c1d555210300e4064811140d01c074101070321090070f01a40450420b42c4403000003aa40c81700c0000c40301ca40803944d410b4440206203001c505005032505220f103203040070380038000300b40440d902144150700b611585260700c101d1040314110a55900e203d21b20401f002850f0242500c030800e11003480000310300c003620307692003114500d0010303050200200316031500e04141c038010003242d40c8903030925816660303400f090034905885265000a52110400004180740890300d814409d4400404452946c41c0150034102e00250903500102c1a2080200a41001c14042c24964092a111610072030320b0001c00e004003000c5250303104c0040710b8030003c41c031a60800e080103003446005140781440c03d02d1815103038603494a000101040f170302140300940071402030000660840c0c3c600e00001100a0680d5850140c0e80c810303402120b8900d40282034405a00c80c00801c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 783910449 1250 783909199 783909209
    0x15040e06091e0403020a060204030b01090c030c021b0a0e0106030204061b120f050d050c090307050f09010303030914061e1602430806060105070c1503090b0403030b010801 75
    0x40392042c108141400c56010509085004881039000040c042c1807082003a9520b00390403490441d5180d44174149448105800d009102c01c4a041012003034038244248201c8040318403a038060880c201075251440b1002a20b220130582c00111f80c600411400c0074440268002c3c540c035140141e0322440d001000c0d12804003030014186240b1442940302c0031070840b03c48110403018615004034050f60a450a0b6400e000d1201c48401142c070306003c0041103500c1800a104030740048003107420265845007003119004800250030b0f0807070140001040000e02a402160007140725101010300303100e00c42d034454640013007113419000200c400b200700b58a0034281c45010382c010440401b5804501d40c1c02c2c0300a559005200680703250007580070030500c001021050316800d81a0b0054a500c1d510411180c1300850201d80d0098884500a8401041c3c441d07002d042101e44c1164003480500d0103d1030401d040c40e1a802c40b05590341490341315036203000000c86506415200f40e11a4a0000c2d0910101c0c0c0010302c1740c1d5058001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 783911699 1250 783910449 783910459
    0x70e2d1903120302030c0c06040b070e301903030609060e0903070201080916060519020705010804081e0a1805062715030906011a0f250215040e06 64
    0x1090010441c2e8081d4120b4104203410301598036154409925814813559040c140d040c02000b040c4001c010480e549076014403141d9446d0441c82c4503000810000503100f100602c04074080e1b02040040108901034603900602e400700392400f14809880f500f4070040819003c4000994070481807000400a220300b40281c000007480c030b522442c054480c51384d07a201d0100042e040c401a5000616600f900700048080d001c107100140200950302c83c40988241c03c0cc190444d000c9a03040c00b65200d261002503594120f0300169641c00700c94455032200450359011480701d0301c8c403d1101080307031110f5403100000d081150203503407100c0100615540001c422141e0b134214a2181200300410078175101c5424580d0510b01c5400b44482e650f030740d034000003070b1042c034203122407602c00e00080204512803c0101d43e042c1250901030810440c1d0040100c4401c0c0d91048a214054031101032003a4280c560320000054004401040c500030070310791302c0c0c00041a4803410500c030b4800b00c900180c1405056610300c8241d81000c01511 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 783912949 1250 783911699 783911749
    0x4060206011712040e1008010c050c100b01021903050d020f191d1507021305040c08070b041a2b0605040612060507122a0507030206070e2d 61
    0x1d9140113486103108102000e20303003102042e500511285010001c2c640d42c0000c00120320341c12400340003038000b011001110b00a450041c4510300060141d084114030507405421b420311a040e00d001140b1131010300f602040418080383c001c45000e07200604503000ca44401e19100d0b1003000801c030140c81e00c0155074040294244c0301030030300c0707070a00e44615001c0c0b8116040e1842580d92685200940144c20b40a540009002180d50034044246c0c4840c0c040c034001c107912281c0c40e41710560b1998440d5503210307491030355008003c20002c425200c00008040315000d217907640740c0040425250150300c404003140c040303007070000881ca000d00306a110741c500414080c0c82c00d105240c5085203a00c0000012100a000300b900c410005000c1489009520326030302c907a0108200c1c50f008003010034401800c028910810302002e41100d5190740c001c20a60710304607450707030041105560b40c04040345c814201c170389469080341c14000c10810310884007408908181000f0b44415510404000f004911041d80500580c4400501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 783914199 1250 783912949 783912973
    0x5011707031a09010f0e06090114210f06010f080c011b17032a031302041a030a240b031009050a02040e03091018030b06030a0503040602060117 63
    0x521003588a0510700300080c0d003510030740d1222410050509010f50000c0d02c0c10020400c2c480d076000200954031076400c080442e40d20203040c0010721101b80140c0710595100c241c80c05140c17030a0003001000050a001d0400391803101641036280480840241403181c1155006001c03059a11410320001c00324440104803030f81c11240080d1100c8d0083c0c649000c2607102442d080240158407089246039164000e0f5150b5a242003010100451480d04040c01c00d1242e20b1078030001d400c503034070989001c0c0b10003a000d0b0728425107603801c120090010145050862400200580107a0350a105484456005500340c2108048103004208240940800c942d4858a0140c1510103a2000078a994040b20840400283c00505080851030500e640c10004e5001d8203069400307054102c08000b606a469094500d101085484c40302030f02c0071580e03000c1070420b01103004801c101090b01111090303040000a410f55000c000c20b0f132205800c0d030344a5002000560702c0440100215481c540001d0016200080940500390b000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 783915449 1250 783914199 783914237
    0x9070504051e031516031b0e040b0316080309010e120c01180b450f04020d02070302030406020d0206040302030f22090509071202030606090c0d02030f100501 69
    0x41c20302e1405400440305821291000c10180c8540708a040b5420718600c2c240080040b100040710000b00041e007803884072024840405040c0e072442e884d50320b0390078040503200140002058850190356162248680c4e05c1480070060400030301a01107000a0343d0b1710340022001500f1840c40c000050f01455603c00341340004074000ca42507009100034649180c4150048169611381021604071100f80e03440084d01c035141501000980481c41400c40c801c552520025030b98418000702d00007950103041010259158900e4130040706c20651074010401030410f03000881000c100d0300075810032009640002800c0c400c641d010050013840d001c04d440100803d2400f60b0b0000d4a9000d40d440e68441c00304080b03100080c44000c810282c400d180c8226002403615511103040303015050507280340109006003100416003c1103443c4110343d042e0080e0040203592142d001303000c1c07059030080030031440083c14030078800d0b45404c0380011400b4a51810b561049410a081c40d88915006a03003c0f50620881e140c1401d040315203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 783916699 1250 783915449 783915469
    0x503060603070e091c0906121a060d18060e0c03070b0703030504110303030a050708060a051c02150403380403081803040602150603010606050720040f0b0907050405 72
    0x340300c042c00da60303103c0d01351481c0b03031018010404052907524036189080d280e008590104130352056880030440280d075041c080403151032012040c11070280007001c3e440d6080060080603e44900000000c8880b000e1220102c00032603044115221034590191944070441003040440301202280503081d003902d0040180e030396118616004041c10f488000140920044030b8592402180c06003e0366681d10384005e40c03400078202103400c640843c0060f80440d5450810307041c22410b441c006021500546118400d05030001c0070410200d900402c1c0070043c41c61700c40240007800003144110540c04080102c14a540302c84103500099007410980d0070803040398944403280b80c0d40c00c81d4050600c0300d041c2d1203031440c481c2120324078034040b2040d11000400054940c1d0000318014100e2500d01512a50b4541d00105801d840320b510070100040c0040c0282004900c52118049010802d0342902d01d070b106029020500342e520f04220b4590b65a903a11340d1004608000d490107501020354684246060300340300001d080d80038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 783917949 1250 783916699 783916709
    0x709023603062404050a0902032104050402031504060f03050d0203070b0f0a290901080703020603011701020c070b0a0806152a011d0706020318060702030312090115050306060307 78
    0x4000201c4034010f50080e04008011001030410f00040c5030410380c0d903016200303440040b0b00a1080003003802a01b5850105082c03410b00d0000702603c0c01c0e180c6030070000a500b02a06941104690a04244040da40d42c403440004243c4c50014680d00d51840c20172604015a60781c1007800c1d50010808403000841c0d045015070312111014643c0c4090f1100c131000d000401460641513481c50040e051002c1103440440401c0c00300c5000c580c0309407180e032603030900754540103a0710009420000900051103d80c07040c4d09151400800b1000044c10965209002458100b0b2644514070050002a91210300c0b6840240309510110036101c2c40e02c05072092141220301e100300404070ba40b8030301c1c01804104110514009040d8900303103000900c0b84401201c4025000c0911f6542ca042602c00d01600240c52400407090b21b07040e02c0010b0005810a00c00008c1c011940c5c40031030200d0307041c00104012070081d40c1c1080c100c2d02808001000141d01c1c05c1c2c807400b0940701c0d89160400c0d0710903030282c1c08008c100c1c1d800242c00404e1f14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 783919199 1250 783917949 783917971
    0x2e091a1c0e0c03100204090f0608030306010320030a050f1311040b040212040c050111060709050405280f0c1706131b0f02060a0501080d0c05070902360306 68
    0x41d144030803034244401800659498020060000e0307803061150054000d44651100402000c420507492030100c41092050944682003440020101d60099200040c40d164250400c07040c1203030305003a1039083d40101e44000351503075107000740b00c510400909243d40c0100c00041a1020a40c80d44500f52601c00d0000d40620480e1156403000d0503450f41d40540d0f103c0d6004018011560a06182403050760032030b4010389000407050a44100740c5500010040d004100310784404200700e092800340405094000c14245080c40c40c2c0400d00c1c40c500c50411601880349445c800020307920030410410b4251843c10080c01c1c100052203120b691020b8085030f848da0000402c0710300103a41e041c03c0070305001070154103881d069102540e0700b8041c0d01c00d420824641615006500369002655240f415804491003805445010361004081c0c401c40c0d4022000c40303074298002e00856100319903940e0000c0603a03201c1d803217210444038074041109049403141601114080201d40c10300081c101040404e81e6a40b0003000682c2007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 783920449 1250 783919199 783919211
    0x1030503070b070e0d030302090f0613030f080712021c080c0d0b1302130315110403020607030e03010608150c040303020c09150604260a0305092e091a1c 67
    0x20070f02a0034071318000c11016040e043d6503000c0341405002900300d00c1c40180119142e840c1e080b141d1412808907410640f0010660341082c0c11612003c10707001d85108220340f00a4100300d48d00100c1d010031034480508100c0e50080030a80500800d1206a440a042c20320078080c0c10010300201441d42ea09135429480200000100303080307134100107984440c036250105207042c40003075042032580d03070410341205980c014001c005408404010201c00c40d20003040103207140606000c1400146070510082c6183d41c020b02d09201640c1c981030001e800c450711680305a00d42d51104079648903220a0b582d800d5800b9001c80c600504017451610041d49644913140340300c4c4030780796280025082d104031009543ca400e03400f4103032949071074a0b01408510346d0f5040404000554075039061041050000481030386640e4583c2d85c490400303419000303108422119181600200b801da1070150b40c80c80b9003264500034900d1aa0b14994258a05600389624000110310020103a4080050482100c14071040c9117031050000c2002840c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 783921699 1250 783920449 783920461
    0x1b0503130219031217060f1e04050c0306030106052e020a120e01090b070312020901030902041401033c240905010c030902090402090a1103041506090501030503070b 72
    0x2001c1d51000702c01c1503038041d207102000388034007502125145107254544401440c044108000600c2e0121072403035105900345500e035190b00302005001b2403031102011911103007210800180541d00222001c0361030040100800c0498a000d0180b00014001551800c80060b00010460001880c82501c8002003980e2100d44814910800100040a801c01c0b840919408842d2005081d5501c0030806070016407803810200305440c940d001c1301e508950503256013001c2c41d00b0220303107400b0b0742001c1009414517070340d80d0b40301d40580c50301d01560700c02c1103e190101c0140c0d811440c00030318501d10b0306d9940342030590403204201c07240400007040741d11641081c24001e404003a8600760300080580c05c1002c10704070305500b8068a051042d0007003060103100c2e200a010b0314405032012811a003139440069404503541001c00e0150070290421500110314070000b10380301e01c103003018003c0c90b4800c0d9000c855005030700b45400014a403900c905c90207000000c0088c0100c0d403540d21640c0da6401510006804c40070801c010070f103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 783922949 1250 783921699 783921709
    0x209010e03030d0b0901051002030a03050718030807171c0e10020a1d01020f0c040e07030f080307110a210207170f060a06080a140327041b05031302 65
    0x2640c0480181169a58200f82d00c2032000342190044490281200c2000030409180c4140810740703804455008505192180608401620014049c02c00380101e06850b0600c503220b844406c00950300845030182c1e200e2903464295102c00312140104030318102440744800905c00f01d00c46150444000e0b0f00032403c0703001c05070780c0c0303003003a4140d40c0601c885440000c884003102e410090b8210352400000031400c401c90200010798840c0810021885907801a075003031340588c5099807109034030704046011a21519103d94814886c1c040c000c038143c600110120402c003810f540064610140c00000d0b01819886095681c0d20850f18030540c00d82e24622000d0001c4812540308121203401441c658240b0411a8000d0160036221a40c0244010b40c50207000700060505881d80100d1040710380c00c0c0010000c0f004a89c4500c1c0180c0c1901846010320301042264502e10100c13040301100d800b20b955901d01c006441c1d0001c21046401c0081a020401c1070040c0780d49410f030f0003905580e840125550412407440403480090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 783924199 1250 783922949 783922967
    0x617010506031003242306041109040911040c051b010e15071710090c030207051e03130e06181308130504050405100c0c0f020402070816030309030905100c06020901 72
    0x85011741c0380040d0f018200e601030204090660f122030390140c6a07160130007031209681d840500750001c900200080c0b00c0c51b050035803252200501800e00c21f4004400c0da000101514801e00d01d620001d01c010400080c1070542c52030001d01001c8030f0b4000c0100301d04144040d51501c000c80c16004c0c040e01e0180000b2003050040d60641c070401403a044100b6075180000b10450609070501031122294900180184a24082c0c0b0840d41566041801400303141c2180b080036007202500b42152032940001e011401810b2100c0c10800c003d80403022032080680760800078400030414111f60800ca8590710403d02c420144106011800c0c5900820800c4c0d5070f00300c1005c1e0401c20b00141d800250040e150204101c288000482c9900b044c0312080c07001d2080080c140b00480d10598441e002400152a964200c0c1c0145099401000d007288106c4078142400114042c25807400b0040105401094a034181d081c10507901c003911402a01c0216261141d0106000c0c1c02401c449103010020000c80d400540d10742203078010f035045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 783925449 1250 783924199 783924263
    0x1061701150c080705100507090305060c03150901090b09060103020414090a060503101d010b150c1e0a0201020f06010b09041a09010f1802090d08220617010506031003 73
    0x10940c1c444c030501e0441d03504c900100c070341c010306441d040100d081203200340509001c0701d070401d00034199511515800d40c0d55502c050046003041251001305149038490b540700c14002c1c00c60301d0380052940340c040f0034030a4045d0010300d2039041600c1080188201c403034070756200c0100780068034050100d540d2120410024440380e008160706200380c1d141c2000300c140a0f04080c41010003004400b1151000314036190030b88a00400d1294822400318141644110300c03400382caa0300481c0f900b1500c881000813400300000c04c41d21020300c819002040840199601003142000d40000c2d480103025544c50030403550464000c00c0031103803159031138580d180303030b008510429070080c05001400e00c503030365a50b446460b11101711403007142002e9001c203806114055040c82541d0780090050301140b194100c5030348000041e405490325441803010484209a0041e06d9251340014210b59160254007030b010301d94903405044142e001d41d00c41c40c410070820840d0042d00b02c0580c220780d44060351100311030820500780249400144c0d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 783926699 1250 783925449 783925463
    0x11130e180105011707050a030305190302070f0308070f020a0c0512030403050714130b010c08210a05240619050c120a27180603080c010209030601061701150c 69
    0x401d1128201e205901078416000417107074900d0396541031028207090345c400600440d40c184560082110460410071307414604d440c0052500d0100c0c0d5800034842c500650a600050000c0b08110159410403040710341103003540018481e038410f90359414504145402600d0103012141c0c4200354250b4200103440196038040c00b0750b01d40a4640500d5188035a111200c03038407650071a030300f18275400d00300d03c9519480b03141030707503034442c0d01c40c03c0c1d00c850403241d01a00c0401c0103214030b1503c1d02034030014044183e018844071103002c1510300b040041701580010303070300c103001d203e1462001c0c0c00216602d00d0200c680035820012408003211280d030050722603019403000c000e440c0c042c5050110801c0c4030750000f00418002500c5140000050104803a850300b040110100382d030038040000d0203540500741000303042142400021610503182d03a0303168116004012101001d030340110304250149001d01c00c680c050009890810358580343d04407400c908842c180701e14420584116064801540f140079034004403904002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 783927949 1250 783926699 783926701
    0x3010801091b03050601120f050307030306090506120705130e1c02060a1814011503060e1902030604030806010903020612070e060307050d0f060e040503040911130e180105 75
    0x9818064020840e048515001010b00e401c12028a50520300c2660342040003841103138240000150100b445a000781c4403000410f00003400610104000d083e2684660340c085411440c00c00e00c0d03020b031035000c2e10705403044a03559984401d040000410904a94044071940301070940d0300c803490000d1a5000714500103005101201c06100c4021301c410b90707040840e80c01c0b81c07500c0d80e070814400100d0b078007080c1c40300c2a0201610504003181e07280d400b83c010000d101000113800090000d181d402121994030031513a10752559420000c80c00144003000d1181085008a400c440d806e034000783c1c842070001c1c8010f0500407410003082c12640700d0860036014582c0a000143c0d690350074003108070050750440fa880000340d8120045041c0d41400340c1078a02400e0580c5610b8140346485110f44084c1c50920441c0c02c0090350760740001072404440d40034a01030b07406070000d5946d40e42850304e408240c40320b014180c01c40b0101004204084450012880c0c12641c0b05020118035807214001c001e03072907003104210911503084c00c2c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 783929199 1250 783927949 783927959
    0x70305030304151503080a0315091e050601020624062a0a030e040f0e0d0c02190b1209030c0f07170f121608181806090402060d0207080301 61
    0x30040d0b014500415105a01c008400940420b40c1c8220a204c0940701c0e490100704002204600900700b0510a820007141003a4102c0b01000003e10315481035030055102c0842000244070b02d5114002a950884144010320b00103002030350703c81003e080140446600103a45040343c0048500c2003007103a00814240d910040d10b6101100c2c040b070500d51802c0e2074016152109140d030700280c440b00329603040d11007401103440902040001c120740c100c03260300c17503403584141d080c101000c0c44440b4826840d07486084030303080b80380180041000301c0089118001e5100c041404a00c40c0036094a8034080802c000045958400c01001d00350f000706541d400b1107214060642c1102400440c103101038a00002d80e04007180c034240c40c003983e1107000b801045030326008a0b00003031144c02220014034464400c0e400354a104c0440ba61000ca09500150003403003400001044c2c441285014501090544040c140c05803c5042c0140000c048860262000b0720070440015480c038081d0b03868054440c00c0380c205040c0b6440350382d50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 783930449 1250 783929199 783929203
    0x1a0d02130c17010b0306090a0c02010906151a0a0c122a02040f060e0406090507080604060504061a0102151b04030b09190b070809030f1b060106021b061605070305 71
    0xc111001c0c801d11050300101305a0800b0003a64826040203101c45080d8843c241c2040082515000d801c0440d5243c101500105445004044980018040d910a11860983c88024800002522546550b810081940c61650100981c1d18054005500b902c14502200303003587c034414440c0c420064514800192103103800c44440d803c0f0300074000c2d02c041c440c1190759580340c0100d81b0203000320311000200360040b0740450705c0c030360090304554420000c0750800358944203480c0c43c00300210384c21504d0301d0b168800c1104008190140078507500d40d55188110900304600081e494041400180c0d03103800001d4000703880340351803291100142c0c000a03056aa101d860741010f03505c00c0c0085921140c14801e5401c0400720000544051106681219082e1095113410794111071004000d080e50b49688402d001541c0850030f080c0c000d2401d0006d903280840da10790f24011076030800005a2080040d50007210f403101d8a40701c60074103801c2031441120155034548611845143e1000b000601424ac1c1c4903040000c0100000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 783931699 1250 783930449 783930467
    0x105100309050d121e23090a03030b030111030f04060b0d0803040b04050c040e0f060f011a07140111040330031815090201020615030c040c0302120411010908011a0d02130c 75
    0x701c5900c600280032140746040e01b2001643d08811a600203c1018040b81c4640d11480d65400002d00101e1071014012003030351240c20543c0d005440411550174071041003414031a00c0200e0b00700b41c0740c0301400b013202d8403141c03128040204080c0401e45144009010040e05101030000540028002c1201001a0340225038502c5810200e040342c0c0300f030784081403141c44010601d5040350f480114000b862a0b06140e17003106a00040d40032200c5003e21800381d8450701d001c4c012040600244e00e05251130b145035041c00040c2c844580c0082400d072002c1c07122541410607500d04045581034904021450b280d100e20414940008220040c004180c00444802001d046407c030003c028000d9080301d42d5503c1d600401802482e0752035800d0791541c001308641c0340b282826003040c0103038507050400604201b0956404200c4150450301100c0c03603280302600644d9903801c0040d100280024038000c20a6540c03400303604030f00c0c279030b880c64161155181d918043c007103503664100c000d49914400303030030300c03400b0300c2c10601602c00b100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 783932949 1250 783931699 783931721
    0x1503030206190608030d022d09041103090a060e0a1a0703050f010b070219051e030d0507110409140709050702100b010509190906030503030105100309050d121e 70
    0x4002d420360764403072409018100c10f40350703894040c51800070b00c100100700960046007421325250600b107c1070312800b004102102c101d00303900c001655400c0f181042004403480b01c0c0c5110607001c0c0500a0225200001600380c0c10b0070340c0800300040d10402200c44501d8442c1407a4028a0351600350000b954913848948040c0c0541e0258805002a440d034842800e01140f007401404948070081c406503000d03180500d08107401c0c102c03d400694600b51a01c02084900a048000b250043d10030f00301d4880c1801c0030020b074030a50754545005070601700181d0350701c1e100003176002005124544500b075a400f4000040e1050039503c0d444800c490a45980c1d2400d90080c0000b29034032400360103004c070890104000e80c0100880600c05a40340d80c038002c000c070104070704040c000320314503a03e0341403130404542074145100742e2002d18041d0b80119225031518042140078442d040c40f143c1090f080c0440040001d1001889852010300d1381440003400210341d400900410710440c51360300040f1031130000b201110391340d402740c68a02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 783934199 1250 783932949 783932971
    0x90403200f1b100804023712110303031005060903010f051807240807090f0605040821071712010f05030607023712020d0801090603020d060209041503030206 69
    0x4000f0400581c1c0c0500101c402030342100c503624920300c100720450443c1700303804480015500100800000380100d50b4040d000640c2d01c0300d0b1038041c2c00610501160044007414120021491403401201100b01140c5501c551801000e012074031000e08c0d54290040c181c0c0c03c100344030400151500600301e40150040a2580890b405034a0f40442c441c2507802a80302140144442c00e0b11040305203000b04c1d116080141090108684100c010070b44240015411303005101035a2503640300d9051240c03080c20002035005d100c1c4003000c42c031628400301e0796070001c3c5c410843e04141d40f0384800204441c4082d0601c01ca00008000352031200c0003041d95854008800255101502140d6280e62180020713a0317a45865002e0650202c41c241c01c8800882d44480442100c921810414001840e999200040060522010700168112007000d0000c103520981450051040c01800d0144c0c0b8a035401041ca400000440030700303030f03540000d42001a40c4841d08200792800013500c0d00c00340e080d0760707007002504c0d0403007921415050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 783935449 1250 783934199 783934219
    0x120613060303020c010507020f13020a030b0f0a06030207150f090c050358140711060d0638040e0f10080d120b090403200f1b 55
    0x8105204450603a541500200b6040000e0001524140c100701c1080360302684082400303009407142e00a007250b0314a14030300940c680084c003401800f9550340c40003860080c5991091211995034413406070080b10340307034100141d94140a007428550544110803034402c150809201ca80041e07a0346d406900218040c0f50854182502c2d1000c068441484c50031a000b6690300c0a418601b1814083d0b02d50903070b0b03403040340721840704412003042c020707001182d099083c0008260700c0c2c5240d5240c001d011081a9440003040a2420041e03a40b40c460f000411000b16016107008205901469115400403000c0c2243d000301394909581c0c1080840d01c40055010715008041c003d800200400e51001541c0c16502d049101060581d00d09900714030340440100109101c0035600d034006941070080c80b046c882585035540d074000003030380d08c2c038203805503030811556901881c2d041080001091340302d0140031449100d07030070070202403440e164030928040c04100c103c01c4034020441800050601780044004810b403c0e1010915 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 783936699 1250 783935449 783935479
    0xc0a03051302062b090302151006050301090e120c0f0705091501030207020607080309060907080d0e010c060603080c1b090709030b07030615050904141b0c0703081206 73
    0x207040c1c55490001d401c1482482140600d98032030340310b90480030310080e514010740c4214490300d090f580c1103131043e0b015801c52039000aa1800042c8840d80c00000401480300b014035211000702180b2051081106040d50344408000303085061014000031641241c685448070721954000e519803c401206aa40d84110080068941000310380244618242c0d4015041c210030180150b0180d409504100e80c0548200551000a144c2002440c0500c0480c402025140742503000c0501d010496080310500303502c40781c030100c3d00640c4261f44e082c560a082c41d00d070855400514182001e01a00c0e0401011140b000c55140b540500000348204000b803501c0c2c5041107034051209102c10440b0a80e9030000280a050301480890043c0c003019400044c50720340000d145640e001440c8510142e0028100040c80005484139589403038050408600ca054a04803002e0400001144200c1103480e038a400d040c10103e4248a04142401000000c581011039590b130b54200310041641080c088034058801c1744a001c10440d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 783937949 1250 783936699 783936721
    0x7170412110f0316020411040f030b13111e120d0306060903020d0816080d05010e061e0f060408010f150b04030b0a1e0f0c0e0d0305120a140c0a0305 65
    0x302ea92036080c0514541070b2030030210007600c089084d00340d800030b455290b031510150605008100a1501c3c00c00600024150301d8550301400001c1c00c501000c50307000d6800c0c2c001c20070700b0401009203001180d50741c102007000c40181480040d000d03801c070350081c0c03e0513003800c3d4001c1c04101b0000401841e40c040000507181d040c1030b52801c030030b4080650084400d441c6075000512010042901641407038540303511003200e80d034042240e40b15116805c402c070f0721034004010071008084400c0c2c010200f00c508010103910581c5641d40408460070b103510411b10303038900302c8213a213a4604550141c02840000d01080c0262160340d40688001c040c140c860945240001030703219141c07410b507015079a112103610559240c81881c80081c0c2440e244d4251983e4041d0440e9802c04101d10644d0b08500c003483d80410b40c149200d00c09001200da0340d0303000c0d00580861204500199000084139110795054038062596124100007100518255004410724408141840781d030411610103840d2564940c0e4080c801a1703510341c5105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 783939199 1250 783937949 783937963
    0x13031e0312020a0908071203090e0609040b180312061f051b0102040e07080a0608030408070512010204090e06161701090903020c0333010503060f0717041211 69
    0xc0c0c002000407841442015082d0000c1034004450326001444546410395107080ca62030740d1064150840c04651070f810107411000b018000c01e05024940c0281c50000c0c04100740c0d440050000740251365000000f0740d00408410440d03200c102c02012a510b809a042480b01e1180d01920800d200c0e4062810008440d0140c0204c450149001e503152418402c4442001c03030060440404031070741c2d540034800490540841559148200740319620404030b410100218000c8807003030342100000f07402c204028800804005452806c1711015600c5d000105404451140203002e281c1080500508084844503102e00001e241400742014500c613252000c031610b0181d4900d05c628140f030261074445001000150740986c00440003030b000b4010f8511604d0740c540001e080004020200140e8000e251005000d5940350082060303c086c1c50415802d40d5041070300282da10900200360185083c0d001000500141c8100c840183c0304d9114080d908907030030700c1d2034404d2030380c40d8041061000030150f20301c45440740c03030018000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 783940449 1250 783939199 783939203
    0xd0b040c0e0108040f1a0a0b01020c031b0a440d08131506081009050309090615040305030d05091606271203111b040c1413031e 56
    0xc14403074007010054400310001001940c41138403502250000c02d294100d024800110100e40039903510703105e5403110031100100421411135100440401d0309490015080801c03010040703407640c00402c1c42000880740445600080340011f440c00c084460a040c090421918217110306401d020507100070700d40c407881039801000c002c1590100040e03d01c01c42c080e40426800182107200580700030710684a14021010504c1816084c036a941410403c00800b407140f806078022501050081918544801ea070303d01603a00800e2240761148085407041d030301c40c1580c229200d03051155035180c590303078207150740c4030f402914080e84076034204400a90f42507000708594400040f0440c0000040e8241031080340c003024520210b2140d09003454500c000766428115460003402e0070302d80021102d00900d00101044804451441d0660105060400b00040346503040008003081d2400140c180c0700c42d00446002d0b1071324956101e4254002003106031000001c40345410f69000f0108044010040103240e1081c080f00140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 783941699 1250 783940449 783940457
    0xf0e0102070221060403050a0507020603180616140d1401090203070e0409080a030506040612080c070e13080f0f03130203060606040501120203041b0611070504050c0702040902030a0c0b0d0b040c 85
    0x500000d001d200580700841003454864100132b05a40480d500342c2c41510511680c007610140e0820102c0100b2615511052a43c1d4180c0c2000b0082000b510401c51030100c00442d9002140c0c0c0f030005001548074030004c413240c50080d06d003565100c110800035401903585800040d458070341c558041c2002d02400c0d41c15a0f04c2842d03540b600310008800c47c000c01c000340100f84c0c49a1115400150742850000d41c460103406860352507500e084802c2060b1404c1165030044c0c100103000030411140111540e60445450740100e410b0341c0d0744014a9000b8500d1180d01c0c40c2190201c008006d12000043c070001c0306030070318802c1d0116800c3c0e071601420002c0354001d074403610f400204490f828804180c200c0e000340d1340043c40307614411401c0c000c0b0203110b0f124000640014001410008400e1031000c41003011a008000941c2c0401c0b550400340b20400c254030441601901541c0c50314420001c649080204003103854001551a4105880d404040080c2e40024408a4420b040c403a031030b0800d21b003c0c480c114a0340d00e9270300c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 783942949 1250 783941699 783941701
    0x203120a020307090e070e19140603070903240e062a04171c030509070302010f020f01110d060e01050d0605040309090207110901080f1e010f0e010207022106 69
    0x400c01035070005040408204062000043e8001034601c1140100304940304c008441000400f840701e2200c0c0700701380303084400001070100b044012455404403204401d86d4519641c0c2d81e00760094514a00d01c0e88000c00d40305100f0001d0f400300f45200c011803944114000180482c1090302003c2e136441100707451046140c050441089440618140d030b4140946002d070340c82d400c3c5aa00c8244240c00c1c4984181c0064035006848002c0780420b101c4214800500c00d0708007084517090a2486503501e400600009040c0403040144103002c0f4020094039686000600003401040b4101c092842207030480380c400d454040c1011400f1a884810b80c080c1c44c140d44000e491441c4c8030006032075800180c00050401d0b0306100c15024041034481250005000e40f9000b10055a4003030715401c00d001e0350742c8059215181e00d4008007980d071004040440c0000e4009410f044c0189500c1c480940a070040c058010001c241c00c1c940300280d01e041006402800d9264001c46079402183c0c0b40c44808a103009886045071140c0d0000c130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 783944199 1250 783942949 783942961
    0x8070206162111030a2d0b040f090309090e030f030c09180708060a050a120201030e0c130e010b040c020d080c040b0c0102030a050108121206030a060606050d0c020312 73
    0x3910b0088580314210850015202d42400c0d8048400c058500b401180d000810003085610398098003520f6881022108003105607210b2210f41c02d805085407207031154540b28038045903662500103940e00341d07006004001e90b1003280350103415840b1038843d00361500d08140f200c960f031803000710680744100c9a1500c107518540d9104042803590b0300c01505140d000203030404d00c0c01498028960140300b08915243c030310140c10b10308100140c40e500c50740018844d5110a2041c84034004000f40044010740c2800c1c04603222b0420055a4189041290f00c0c44d08000001c1000182c4031703007078104951007030b0000020031184182c11300748020790b04901656030251740640c8024941600c50006641d210b00d8a01003541081c0d201c206c2414142d02c900d0035103525a40110611101c0030152082c01d00500c559002059114202d0152641c24061407020f55204100e034000909152001d1100c1c00030641e210300c00b00003507515080040e10700c1d08104c018040740352400300807901d0640000116030740c5000d0506456160b1b565a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 783945449 1250 783944199 783944207
    0x902180414060a0b090d0606230a0f171e010c0905031204150e040f0b0f0306010513020706020f1b0607080601120b13060305010606140906031803070c12030807020616 73
    0x5c41d00d00d58010413030391511404280320b4490040a0090b00d0000d44d80185018030005245032060104c0d84110b203400000c01a80d02074812000454280d481a002c152948550315800c1900390b0b8001c00441219904040403190103610160411045071104e800e1580c1f00d105050b6214400c1c10441c84040c4104811710000b154500d50850310700083c0750400304510301c40041000c1d9a61105031002c00d82c0c9880c10010381d842d10303030080310410f00e056000304441d40c540350005081a509a0000c840107500103000c0c41880070a8040300c00360043e541c5820f5503a4400c181c0308504940032a049000ca000d600e001c200e0140c0f10f0001e003401140c2c169168017491075410702c160024164080a164072120540c101e500915482c0610340055024500000b0f400d40303000000f60210008014040b640e04080080b461107030345020075660014030301058078800c0e5400320020f074136510a03802c0141004080c3c110000301c00901015045000b0700c00e0f61803002c03a444030038090f0707968501a141c030b1f000c110450582201c0c035441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 783946699 1250 783945449 783945457
    0x40201081f080312090303130213020d02041e0e09100f270b090304030320070315090201031404080d15050604060305012607090b04060902180414060a0b 67
    0x8800c80002081c00030050703100c408556511080c46070b0400b00b0034904009140285a600600c1c1d80040c1d071a44c58002102e80c41404611002440b03914a03110440ca501c05d02d505959941140038030441d03071283c40d00503c1c8520254524150040000c0e2400810030703501161185018800d080000c00b071220607460350f64050080c3e1046200400e60740d540400004034000806080780000300072249144a80b4108214088801081c1d942e843c1d004100c200f0002e03a102002d00324010005200020480341551040d04040c42a81b000d0309000300c11381c1c90000000103a00c00311409201340c07001c03c0554800050004030440840c2e02a164100500c010b280043d0f0a412040d04541c441d114058125201e400040c06502f040d0450ba0000e592100180620000308003105100000b260001da01030000007601c40e9515214003640f4200b580300c0402c141031f034450303401800c09001002c0003035444540b82450385880c1103898040c207100d0750514060045501c00442d005010700303005404816841c1c104215420250f00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 783947949 1250 783946699 783946711
    0x8041103010b0d060f0509011104060503040809030109081903090804231f030e03040302031f06033e09010504090807060203040b0615040803090d020409050a03020606041103090604020108 82
    0x500c44120b051240e481190004205115050010342d8245420b040350031100003c05c8028160300d0058104000e1810b03a069608842c0075107042c6a4070350f035526244145020f08249180c1540c01c1100034000c1108107009448140098641d000a01900301011010756550990240c400e0904100a0180c120003c265035162010020f14881c0298a00d02045101d074640e409400b2603020308000c104034a0f454020a84801e41480066050a0550300020745480340e8284085210030000d824040d910600c1e00a0380040d500103030780e160800482c003a030102070149000789444074a5081c54080098410401d0b10409090143c0283d600360f01340380501005060501e41a160f0360814000341c0e0014806000440c803ca1260401030841c0c00c1c0300c0240960710060700041c0c0c1c04020140030501500c0300010645421700030440d1924510f602c6800414003e261440c0c001c0e049001c0d0050160506400080c014003c520591303040101c0400002c5681103400203545074003c5411400108002d503105236a0035402031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 783949199 1250 783947949 783947951
    0x120201110a1b0605120f04020d0506070201090c0501020f07030305130e040c060206010b07050d0c0314030f060906060903030f18030d020a110604440106240804110301 73
    0x89440c0500e140303010380744081252141c000d4800d624039451800345031002403040303040150038140c01220442c02c1130801004411070321801c200080c155a116010902819000002d540e031509003904024042c06601400351004001c081000555500c0041c200303c5440240014228240c00d50390212210b0b03114005641d0b0f041e210742004910455a810030b00c0c0618441c0030b20314480c0d891300030003904000c0141d2000d180200140300000104101082c10100017009140c1448040600d10701070700c1c4001201c0c40d10380e04280100c00c02001c00244000b80d402440102c2d1101003e680300000c100151081c03550391074054005014a00815040301c0141c01b0b00c44281e000003941c101030b100032034503091005011100680c000d000e400e0500c52941195040e41c20140c5105103010b0810310304a40078510021a115078070a208414015954064100d6001c4040000709070980019103401324040e020b00d02412010421007041a02807001050070042000507a446042040e651034403044108034690007869055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 783950449 1250 783949199 783949217
    0x60d0b041401021b060c070c030b0403090905041505150307140a0b0a12060902040b030606390708030c060c0a21020d0f0501060815060919081006050a120201 69
    0x40502800075000082e044d00f03002c800e030a0300c841d00d2450580040c00c0704414000400104000c11142115032082d43c0d0010720020b4591590b00d4129010ba0903076120f02c11580c41d140030b100410500b2030f8158290480b0000502043c0c60301800000c00203841021180c0c5030380030300c5003001003042c003246011044000500203100da640c0d41074103000640c0062200d9001401920642c05280000c1c8110300281c00d801c00f085041c1410b04098100b640720103002c0ca4400c51001c01c180c0b030940646d01c1d0900380c16031220aa508403008034038089101e000034007000c070b0040c0200032000c100d4000c00810f45004151100080c2120b807220101200b050303111408140400403103209501d111145424001038043d003224005a680c0c401a504104450030010351840b42030400004000003544042c4094200800d00c080e40045220423001a031144520b8200b2034100410740c190384242101c3d50744c00c0003120080703801c0e00c03d2030703031801520021106d0501401e584140c07040c03c18400341d03c85030400c1c81103a2060614806d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 783951699 1250 783950449 783950483
    0x20d0c030201140718081b01051c06030b061c150e3a111b0a18051510020d050a0908060f06030c100504181d03030f060108060d0b04 58
    0x203c1141100c0410104000e03840b010002889a40803800a00c440c8001d0810820915a1900301d0300c0e808040a041000c0400c2e180e0080341f08841000f00c080301c0c140d08125445d981c0c949050848403c4444a07c0788171030400911040101a000e404d460b0b42c4503110001c81c404ea00c40407001002d207101c4980c207510130600700e02407414104030511032541c024541d22016130300400048180c2034020601e10704002d40c84070060383c074203400500407154a12a400c1203d50414407404500740014951005117041d0303500108503000134803030b80498010450f445400302000c02c0d030810300c40b00412032980c06006034411490000000d214402803d058040c6107001c518155480d60b00c5441c205080da000015212000b013440039030700e002c00101055000c1030f04e1407111b6642e4401c02800758080d038460140c00b80071b00c00000c940d143d40c40c1c1c401500b040c240d06000700540004138040c3d5407a04101c0350151228042008a90300398000c0f0f0f801031051400608228181e03500b580c03a0750002501a008072640c1c252a1800c41c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 783952949 1250 783951699 783951731
    0x1090f060b0a090f0f08210c010f090203010b060403022b02060316090603060602071205010e060115030608030f0412050a05010513061521030e06040909050616020d0c030201 76
    0xb03042145030b9216000d035820b0101040059400768441132580c90a0b91041040030404601d0321a04164504c820032a03500d942204e500501c0b80141d40001035180600425211b03803680c0c400100c1c1d42c002da0027080781905100500c10680f0030350002940c001c960f1b00056980030352241d03800280c1c240c501c00c04000311001d83d020a05c2380e00145c1c1c000700450701030008440d50300d500a0400c0c00078601c40c070b03043c00318070b25040000e0345402481c0200d02c0b104404a0724002800801d400c010300600807602110100c0d0780d10980508403541c01c030354140c00682031090000b25030000005840b040e1100b2401145010325001842ea04503107089000c8a082c0901c202a0010900c28410680b140d4501c100f00031509400e86000d10845030440e54128070810004403e000001c2c2d8003115002e0340207101c1800c198044681400c1da4a0b240c29049070f90312150000c0d01040c0c07801c2940260072014880c40480c3c1c240d441d10100c3d20f44d1b40c0da140e08981c0040c0e000e224034950541c46007040c175003041e00030700000a401c110020081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 783954199 1250 783952949 783952957
    0x140d08071b14090f071404050a030501021b030f03160e100201020a0f0203032202150a050702040c0309030e1c0602030f06100f05092209150509120301090f060b 70
    0x41074810000c8082004240322002001c0c1d02004541000291401d180d0024074240040c000004006411070091700c13001c2614100c030003038100185125149680da18100d8080c1d400080c550f1254036105860f081d09107030010964141400042e00c05085070782e28a00450120480c1443d2130400a802c800b11505440703a02181ca1180d2065001581d40d9204446c00740c86009004c02880440d88204100112410380400400340b401003040420710300e11060000404520340c64109a12071980050f05800154001c03008005092083e2024442c00e085c041c41502100d465440282c0800c0c048074102c0074a250400d510380d90710883d0206450100b855841e480708903041142c001d41c03140442424007000e0310b003184501190342100e10380003400452900c0002d00754080d9204041c010500c0c409070310708031740800410902d098460f420400a170321181c03c0c1242640101c25000b0403c0e0f2074030010070700f1100c0110780c0c1601110b22651061542e460300d5210b200070000721544581a41d580c480c0421054181c1e0018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 783955449 1250 783954199 783954233
    0x13090c090504110913020c0f0304170c1e090c0412030e0f150f032203020a061103010f03260f180a03020d11030f03220906140d0807 58
    0x303410068108070901c02151160391144000801c14411451680c0d200340c244003520300c0c031003005a10351809000351460b00c01288202c090502010a001c105450b00e02088282524082c4c11038038005020b43c203120052aa40d03921030f02011402078503501c01e0030186171654006041102407854556504000d0300801c461103011030000b038500304400105d1528502c087c0a006085580c0d51040700204c840307402c140300d08210ac03035030254044006a02007004503011101700d140704800b00302c06425850000c1d2030301407100c0e04555451800340414805546603040da81a900c441c4866a881811a2210b10a55001c2e0408510500240800c1c0b124003000c4009080e58002c40e5513031381d480e011a1b081c103903200c5c0c949121803030140f80290710030030240e0384980b00c116159400001150300e17061400046802d00c0c4480322910400d1100141281181c0c02d0206400c1c0189060000c5406054031016010b00707640e07041c494251948040e0780207007014980890396400c058442da8003246880c10a0740d5603d902c4a0300481 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 783956699 1250 783955449 783955457
    0xf060509030406273b04030315050a0612060b0d09120e090a0905030910110c04050c34050a033f090b0f040c06090b070813090c 56
    0xc104554125814950340031012008000403815130f00b1105032a6454400c142114101ca60200541c00c8940075034040e06846519644083c0003025810440b00c0080d81c080740045c0c40c25803c0c80c0d650250300800e0050350360003064003007803a1420a00f11780d40355030094030391700d95030f901e1b2070008110203250000e01038640545c0011841174460308106060307051907000071050001400202d209655405044c0d41d00034072800303000542544070700f401440d6000c0c4041c000d070840c1301e403103d10724250b802c841010707200e410301e00889440c800c00070305003c1610310945680c1c526403000c0c0400d18400390403034404032490000c41106489242d410b2490050100c0e902d00079140368112024101c01e259216085000081100d05a1104800c81e01c416404141e080f104e0710100c003202d85080748022a064000c005216001541c41c661f604100b1140e02070310000340c0701144c038410720f01c41c0064640d0240000104499003903056600b000d0050312070780700e540d1001080d1880039560702c0000c104001544569041030b429556 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 783957949 1250 783956699 783956707
    0x1b030409060521070605070c080d0207450905070b030a050c09061611030a08180d0215162a060921080702060f0309070506070206030f040f06050903 65
    0x10500c840303d01d1022060003000c142c0109641d88210002d2090111070707481c40c019a4590190501240c0008aa040900e45000381c007010030400b94005400b009640c6606203804161508200d280340d00190942c800702c00c040040d00c1c1d504405034001050aa840103540c0101c0c074803003166201ea040684030b4002910001c400301c14000c050140307101d001e40c01124614540d241c00b0f80d5000007490f5006224142c4440e6182813000300c100708024040c01307020340002e03041700c0035a10700e8079100090390024030000340500381c0400300f00748500d420703440c00c2d41007600074018004044110501c43c00383c0e400703016104080220340c54070354000350480e40c0c00c0402c1100078034000d00310712408c3c0c40c00710b88d18001c2d0f11100401c08008000c1c400c07491003400e040300c0d52040b000c03050100c01d2140782c414040c7c000c20740d01940c4500c3c0411001100d4107220000c6100790400030903a82001d813a0000c01c103650040110181d00420144001409030048584007134025024805028188201c1e51390b01c42587c07800c0ba5414201d80003c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 783959199 1250 783957949 783957959
    0xf061207020d020c1f12020d0603021206130b0a14040609020112050402010e0103271103190b0406090f0f120f020601050d030e0a090c031407030b03060106051b03040906 74
    0xc080388060442c1c5102a2440000110000d04820b13034450380410b80784002c0d01402c86060059801042503a11044107541303689100c5540d0004006500c0103900894144802e4240300300c3c00b03d039032481040c03000c0c803c0c099018540c80d031071580003004011031081039a03070012a00c910480460b1900c9284921070100b03882030540b0006090700083c0c02d43d008240e003003c0c248030051782c2246d00129080801c0ca00003402c0e00343c4946000b1582c03e100007081c0c2c003400b03001c601801e010f030810016042d0301c802d41c1111910010201400c05240d01c61401034200e002c8500802c0014031307641c0106004900648145c0ca10244030f031203104100100301e00454619041c48514403523142c1042c0c41035003034a030a0001d80803541c58800811255150000e008040002d07511402143d40c5d10780b100d40b13000d460843e0080004403055800900144070400300d82441507032200004240611900852030300303020160140c04180d00e064025946a000040f01d007906902e4088d8180401c6803c0015000a01a491000c40d400b407a00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 783960449 1250 783959199 783959203
    0x1503140309010c020907020c190603050f13030c08040519090501080109211e080f06090c090907200a0b0703020a0914010512010321030e0c0409020f06120702 69
    0x19281018a81040c084212541c0e0408100754082d60161880200c641d94104101e081035503440003954040c0f20010318501708844020030000f52401d07620200050f446e0050100402141180c45207400c9141440ba0000030348107240340071145111703080c15070510b6260000107200150f00410054034500d241802c01110916001d02801091403400030090851182c8504001d10012858814541409803480e11582c4c4590074884050028407402c035240010320500074040768003070360f6440c407007100240810410314042884c4c1c3d0040ca20800b02900d402201001e01c946c0342c0009048405010b0109d00381c42c0025088041003902500c1400901341c02400c1c1d1070039007000c42e8007420300410144140440842c07030303070030201d5141903034a040c0c0d82034520983c80d00100e07030a204080340540c0441c003c800000420508142c02e082100d1403402c40000102100c008030704440518501c90042d030b21400760b015141c145580f1200b90b080c0050071450f405400d080204140d0b6200c8500c0c5120070822a0821411543c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 783961699 1250 783960449 783960473
    0x615060a120b060d020c0a03110c090604090614090109021e06030c070606030f030809190c150e0a0e0f0a05041a0c120108010608120708030f07050705011503 69
    0x108451060610a0103000104900707840310744091003554a85401c0140d80c1d07450240c8000c0c941d01d22095640b14001c0f070709103403211014641280811141d100705408004007040000240030040e224040c241d4401d42044058000c80d0f909561880d80d40340d0b210302000c40340039104e20a118110002c1081d84031407061000200b5100c0c2e510045092140000d2003d5451000f03e0380c0004100001c01c0d2164003e003070400c000d040079030000744110800100201050b41207201d251040310780c18144c0340c0c440194807880703e1700c0c99218801404a1014101032010110198104021140900c0c0c804c0340e0100e90300126805424a070080f06040c0080300c00c02080351341030401f20703a200d020308405109608040e96184038103018800220a01034800e00011005030142003680c0318401240215003844d40d4505490380240294011241d460040715014070b642e1444c40225102c1c507603c006030b135145681d070300d14200e501680581800108a410040c100100750240030301c4000980d600c4594922619518040f914401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 783962949 1250 783961699 783961741
    0xb09070806060d11030f013920011d0a0506070203070f060207020609060d0f05010914180a120305070e0a080a20030a0c090e0303280f020a0206 63
    0x84007004000b190b455a900070244960301009504031020b072040040c0c1003542c241c500c42507a40c6400c0385c038480041055201c0200c580340388815030700152a04042d0f00c0e00c00031060088081000c41140308000002e110340001c600e6500c4000291100c94404042245000c4c2030b009035039540a405c40ca401d10006003c4183c0211050005620b04a101c2d5102c054416100c070014000700e5012400405545444045800b40380b0020040381d606c2e144200044000e11402c104040b000d031500c400465080210f108210b44007031019000c060030351350000ea448101601d03900d80040d60041803a0400041d0003900300321a1000c440c0c0b030101352490000001010403403805980d42c840c00e100801003101c0c49012402c11500c07030b00302e4403103140401521000d0480419980300f050f00341c4103445c60030782401034400b507610075244d0701141404291040c001003a607a0206440c03d250002c540740c04240215803180b00d0f08100229103a02107841d00b010700d04032049801c03401207507001d6001401080651450000034141405c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 783964199 1250 783962949 783962953
    0x80f030d0b03060f0c130905070203070b0106030b0f06070503041e06110607140a1112041e0f05011b05061608060a15030e010f0e070320131a0d0b090708 67
    0x880c001130540e000142c00781070210101c1c0300007900b60401500101a10280c492050148100d060030703840299603030f0010009940c0c602c440000031900760b21031700031001a200018034500b6458150b0040010603805158226682d02c410440090741c0c0f0304440c0380c840110003000c51801001e140210180c9580c4c140c0800049a400c0790301004080d9030002c0d2050129207483c0f85240e11055180c00c01e403000810b00c2c12240c000d20921214201e00301c4c000000b04183c0e07020001c12081c1401d510101514075244d4040c84910703d11418090046501c190400d410101d00b50002d10400c1034992500c03400c1c042d090303c44071101c503040184604010340115640d41c20034400e5940c840301c2440c1c0301c81c41c0402103c0b501d1a10416498049602072040c0035000555041c1c00d007182001010020346425036908154841120b4244005031000050300040c9007210050750081d261420700c0c222139007000d00a00001c86000c0003251000700102c00f0703444410b000b07100b0130703c10200628181000c0101d240740141c2503200009035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 783965449 1250 783964199 783964201
    0x50412030e0a080c0c190603060b04080304090b0604170c180f04020114070203030c010e0d090b0706053402010513020109030b1806090d09060801120209040c080f030d0b0306 76
    0x600000325001520703006002c658680381d04808060800d009429116403246c80c04600c20000c1e0346041d000403c903409602c081140300e6a43d45803412a000b14850442c607604280010404d511180d04425442c3c2c8004000070728040d101c40c2a0103080c2c1100d81889003680c0070022100c501e00300050310780940002c24840c0c6403503142c5201807650300a4010310003410400b5040c490304c00040b444060382d0b0303c11380c020240d030746820055161500034003d164104009125610f506401103019940f08020349410140240c60f141541c0c44e8200134220242805000881810f0040c54260141c104451200c9410041d05180d2491400090a68002802010100c85140080380c0141e81200d09a01160b82c040c0c0b04c00d200390b85d150307040c0c5c0c200c149500e64586140a6401000007841d07001c40c58409038070700354882e5485642c640b002280c4908003402252a4803c81c0007080d809450300d43c100780c0e0300c07900c1200140440c0f5201c0011606106800042e042d03d1307440400c04031180700460140a070440c1e030903002080e40d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 783966699 1250 783965449 783965471
    0x10c030b130f0e030a0c11010e130e07120b0a0f020c15220f03090605122202150a0305061009060c0615060e03010e15010504020f0c0106060305041203 66
    0x20300d1090841c580720790342c0d07941c40c00324080060340000c20200101030035030751940840d44024040003500e18040720b600419400035036141d80104010031110304050201c0c0c05a0070600000c0300101072520075a8014032070a14002041900e082d10f902c030041c401c003041000c5080c4641238109607007400d12096411801840025250040014001e44506140aa80342991a060a101501e04414650001e9200d042c00b107881400611410a80c00520079664a140d441d40c8800444041c080d07481c42ea402d82d408100418145e0000c803050849038014072030320f0741d12007000341c0c0043c40c100e1407000c2008400c1800728034040c009406100d0b09500440542d101d407024000d07150001c1c803040341c80c0600700034010540720440c14420641d00000d03a848501d00e1f5030351640e44917003000c0c008213140c2c00c81c80c0c071035800d110f800052050003040344140300c142091100b405034288003c210294000103c440c20701101800750164841003401100c3c020802074600280d2402c043c186044075079540c4c80002d0906042040c4950 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 783967949 1250 783966699 783966709
    0x81e162112020a0903020a0b0915070507060f111b1905061e1c060905160c171210030302070b030702031206040209031506010921060c1e020708010c030b 67
    0x1400c540c184400503543c2550304001c1c2c907401620340004c1c1d00f0032010100800d9a080071001003030f10840c116465140e43ca031580c010007461045500051160f00843e50130030200d40070307041130404520241000c0e001405007003a4103142c81092025200c3d041a42030181c541804c003da20072355042d186140c80d0f000141402c0100c0d0213407041d01504104421b0384860390080340d0903c0191a21030f84410b0941c851401128180e0014007560701030301c985030745003501090301c900b00c2074502c1308200c2450f1a01140d00c211078807001c02c0d40301034581d1140c5c61002008a481c4900c100c111740340c070411044d40303211036550540c14001c0c541040b40d0803d0740395090410a01405580000644959007409c00100407030b55225408180a80154404203070540705080c0121114021018554413a0000b0f0340c809222a42c0c1d0a0242110310090440040c1400003000c98400b01344550020888101d06080078100501e1456a031241d0181600746040180c1100009001d480c900303010300c540072a0a0701e0140484001d44c8005a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 783969199 1250 783967949 783967967
    0x80c04030812060607021507023a02030c0402160c06020d080f100b0f2101060e01080604180b190c0909021305061804060b04030807081e1621 62
    0xb2003180c010b03400109030f65110300072204d600f503002d4002c10482e20085045180c0740c01515080f0b1154a2410380c00800c048180f051003180c8410888900c4102c40c00d01c00c110748031a0255051360980100d044003112a100c40c0011302149061590001c00348110b81861103140f00107410040840d00300d134031402e01c0a940f0002107904441404e40c0819507132552600040ea411003a40200c006060100e035035002028000c0183c074a108201190544104d550280102c01e694240070b00c84c0841d080f4629003103694810844d265103c00090030001d01c10308005018010200080011905081420100002d6005140d00300c0d030100420481406084840e440c0a0022010b9018091919502140d0041c0100b4245e21501c003c10025100f03a81d0345104164883c1c8003174981d440140201d00740440020036041400440e4112030704503860030700f001099078661403c1d42c000180c0c0c0c00c0368100071030308010b481240d43c006c104034000700d1a44505000c0e103140140d4482040e8031300400003d40c00850900813904a0210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 783970449 1250 783969199 783969217
    0x9150901091112071208090102010e0d120b1c2906030604080f12010f05030106050603040c03020114120114011706310204150311030408070809060f1201030201080c040308 75
    0x8480105000700f1464941107059000b804580580c0d00300f4000d01c84103c006103072a00003030b402840301c0c0b60706403501c540d40c000e1f59042d2000a217410711043c844da06250700071105081d0040c445092600800034014100c03400d410305039000ea882c490039507034105240810403c0801400d80c3d08900d8540360000a86850006001a00342d240014019001899a004035903641c0502c1c005039140f0758481c845a0b08461150144074025841d2010201d15407401d102907901c29503001407415912030441e401120030f159804684020101c0030f0041c082c4004044600c42d010b06106510450040d1024000600380414880c2c2c001c00c105828081c088245c80d1080514688800404a8460045544443c507a15000c0b0240c86490920204000c41d60342e11108806d0380701c075025581805841c6810f00341911600c01580d004003500800c22500000492400c042e1900120040c03509041000a6180803d03940c0b00e8043ca8585180040040c4115070304403031090b800c510307441c04941c101410b5540c0e8486074802c3c0c14007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 783971699 1250 783970449 783970459
    0x1d01030f020409020d0b090601050d0c090209010507050a120e040204080303160210061806060e0904120306090f09060e010605031b030a17190e011e0215091509010911 73
    0x440d06544407074002250095024042c0d280c10301603410b044d0350440007981c265400e0300484d000064585080c480081a05411400e459051443c1031840002940200081414080140401e4000c9a42400010341b414011a89548040642a0000d00140844500d50710a074130500c4207119014001007500d610010b03510300a0780040b8059026840c00140a400d03100352410004c0c041130301c402c46c8540220030100c3d030380c0900641b511201e0a90b21140c03001c0768141c00081e05800038003c1544c580300e2001c0500d007800c0005041e5200c0c440340040c0d51711058002d07129500d542814041044504c24840c00700d0214000b0001d10f828200040d441d4040d40f40c0000001403400e041d41c41554085c0302540303031542d00a0f07560805282001c0d640c00c0640003048030002001c0c081e065041014000d00b034440745207a05a40c1c160101c00802010703a143c2c0484822641184a490b098019005050382000d01440c1114020211101c1d964140d90500b03100400e15602c40e414400300070b00289403022092817000048071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 783972949 1250 783971699 783971723
    0x40e1b10140d0f02043003080c070807050105071e030e0309040902031501060f090603110901050c1507050408161a0a020307150504061d0a0b060a0504020c1005011d0103 74
    0x500300002e88804841d00b40320078130014000134209142c01003051143c4400103944800300e031610611024540b65400034020540c028002010000d60314000d00320300e80705800301800c148054a945007122800c441c5200821100b0341c1c00c2030403001c2816100d050b03a16a180a129050020341242e4a034042c4040581c0103a880340c03010011503401f408a00340002c2c140300811507940c0d65100043c180740440c91404041180741d034003c03410714420b01420056205900085181c0f070740a20046620381d04c803c40001450181000c002a1801c200311751074000c0016940306a103030f41c1030483e4941070840c1c5a0f1a021071701d1160a0030426101000d095502c0900500290340c0c50742c15846041e0b0840c49403900040c0507999034019044580000c4d882a4001e500651040046140c505031301c407420b940703203600f01200f64450070101380001c03442004154000300c09080780000c4e07a074510108050380c21001d01c401c0746402108035020b050200d403003018010800014109158540c00300141e4203444103010150002034514 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 783974199 1250 783972949 783972967
    0x8090d091e180f05010506030c0a1d031b151c09140303010608010f0911031501030e032803050c0d02090102070f1508070509010e1e040e1b1014 63
    0x11941c4002010800d4010241004800b101802080d40104a1030309610b07020010607a4280401070780d124080800a5902c0c0c80d0040303400b500c42d1602c24240718140076120340200c516442c1032042011500910905100c000f030580c003040b818841c6000f0000e0341e03100c117002c402e41d06420407003045001e10031410000f4200f0700c03c4c2030038885800d061880034aa032100000004440c3d5102500030304961288050300310054840d01c4079030a85c0c02e40d8a00031444841840824000c541600014502e81c0d0141400541c01e441c010820782503410140940b041804035864524841c0d142c1041d0340c41c4196645410441443c00d041a840e650065030401843c06c1c4e8041840d801caa40200b003803e0103454881c25030140740e6903400c24101e001400b4400b920015036000040b2b600c56010380151464502c0503102c485200c0011018402120740403c40001480752180e019809a01c45118411481101340c1c0a0f02415011052a11401000040850041c040104130400282d80000d180882d5103071101003560b101420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 783975449 1250 783974199 783974249
    0xd06180b0a0255030c0c0803070e03150c0c150f13060e030f0a020c0109140d03090b030928020d03080703150b03060a0e0603100b0d05070801060608090d09 68
    0x200b541e0b0341c841d054030000111200d4802c5030443c4040c0c0595043c02410518201181d600c1018031005001200034000b0030130403401600c0746002410080d0480d220a0340e000700200c2c4182c41507850741140ea0f400180032200c3c08050124543c664001000c1c0221130500c00d01800c040000100f00c0340804100e040d0f014100100342d00130383d08404a001c1266280e030710561071044240c1c410104c0c00c001d031042a40c0100340b54010310740c51080b6030804200301c1e45500c400d418400000103800d402c404000f0300c0800400c1e00004040503602a5a6910080048400d103031400140c1e15490207a4120380c0c500d8451074401a900d00343e071003003065814034004030b10381c540c041d055025002652940c40740c500e19240c0480c0c0440114050340c0300303130b0048424060382035031180c004560410035290160550081d80005103d400c458010f1034032100007800c0e220300c018098843e54100f003d25003200ba40c59469040c104075035031b0321084541d04014a0740281295503281c5401070640074551041e403000f95000d0348010024090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 783976699 1250 783975449 783975547
    0xe0609060d0212060103030906110c0d020111011509050103020a05010816050a090e160e0d0519020d080301091b0e0907143001060c08070f020d06180b0a02 68
    0x3c403000c40e00e0390b513144d140140c604051130044c00c0020700c0e80c0c011580110300000d9144411440a04141e0002e20035400440c0d8120005600351078540d03c4501603c60b002c11001024020045440d0018070b81d41940b040000a006c2503200504000d10720b001d02c80a07080c8415604400c0019007030899480e00e90032425034a19000d680b040c1c1d06000c81504001848540942c03080480bda1a40c84000e0201018200048286540c0c0040c1069100710447c0400203808a001001a8001403c013a6100e805554803000ba5009030080286a0748503041d100c4c4101ca29001c4403511906410600a442140400304016450040650f03041241c440072894456100318121041078144035031600c80e030026088186e060b40107030140c42810001c0c690000810f00d04c1480030b006003d500c240780500d0b0580d00c0e1565210b034000340390241e911500c550030020011f8100d1003a0260310000c0400c00d0224030403401e18410600c00201404246401045584100440144800030b40803050081c0c0d043e08040788401810484 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 783977949 1250 783976699 783976729
    0xf13030804080a0506160509010309080412051c08040206070b0403090503060a09020306090d092603070b0105012705060705100923070b0f030a02121f0e0609060d02 72
    0x3a000070040382004021568510090103402141c400b41c643e104c981c141c030080310020720005402400a040d0f5584130703400c00711600380500d40701410151504511800e11168500844090f80501c01c4d000170004140d0241d241c041440c2050241031409402050781c61003410340003401c0c65040310005d82014010034001300070785409412140a46050000f010040072161800e0b8864403c401c0000d0170460001032200a4070034a6440303529141c5002070000074089032513034200503800c0312160305041c038108001508000d406064154099454800098003069504c10407001184021000601d55080c88444c00121034066480f2030b5902e0090502508001c81480100da0380344c204082441807020810f104606603541c1c8022143c0b00700c08001c00760799000d0a110745401180309010450b185000f010145504c240308a50151802480c1d041e00411002e04035001c8100c0004841d090b0100040c1080b0400603107010800a60b090071702c10009520300400034601441042150781c010110344071710500545000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 783979199 1250 783977949 783977963
    0x304030201051b06072604021e0d0813180b0a150c0b040506040203010612030215071101050403021c180e1b0f0909060405130210180e0124050f1303 65
    0x2050000b0011700b0881840c50700143c0c000e41d41c02d80410001c40c0313603840c2c2c040c48d070051603001c28810000448094001074608a83d00c01c001d0000c00010030031220041108810303196450a2503410301c03850810003103c919480703440c146011100b4503c4c0e15450030340401e803041d85001e1306200c400030100f25501d48400c2c10081200180100340800c001c3c1c00a2241c0c00365108a000b44000ca40751250044040c0600c000036005a00850f0101c90700c05144441c240c004031103207441d5032800b64070a291402d403501a1400c0300168000003103000c2003000b4080400c0c0042e028a00031091494195500e8414000c6005005c1422206000300d840360100d00e000901c45c413091501c06458030b149000002c030304c0e0080c2000e00e015100f1800002e8a40c41c15100309403007102400c0c0480084900364007444054210300440c90f050100d00c07070703108081c5441c4180d032000605140c00038030040d40c10031000f52056a15850310724010f02419410f0f010494019060398111b1101865040c1c0304c4405000c4d4410010403548060000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 783980449 1250 783979199 783979201
    0xb040501021b0c0f09040c0902071e050303090c0604120818030d080f070c0818030a0c091d0a050c09042604030b06030a0c060f03240510020c030304030201051b06 71
    0x2500041083e12a28100712080b4500380040e50900c03139020300480f0010040c11010009200014480d070291119038051502d00344600c01c014984240503400aa0554490713101008108100340d04103d036059400060310316500301031500d054003010394010301c0000d0103050080383c8071511170707140c41c500b50130410010212400c03202c001030007818a103c26514a400c840d03034800000c0300d890085200d64121755026584c0e615120404030307117074000340740c440300343d9854000d0101003008681c9021009024002144000900b4044e805c01c00000240246c0e0190040d000300c0407c81c081031011404404900050b03c480d40309966614158858a83d01c40c1c01485444941c00303051301014030030002d48142c900c2403180c1e5446807203440c205955041c0807140140324410f600010b118052160111340380110142c01d01160340c0e224001d003280100c1401d01c0e5041c100c1a0004200458501045440143c41050000d000c0c0d18807600c0219482e84201d00000c5e051140000c0c0686841c148601e50f8900e01c840e0340309580d65 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 783981699 1250 783980449 783980497
    0x1303020c061210060206060d1113141006021f0e0307060905010f0509010209030d140405130207050d0503131b0305060f091c2f0604030f030f09050a0b04050102 70
    0xe91050f514034180349000e180105809000240301400380c1c03c018212903041d001581d47c1c001010118580640104020000c26019000b50064608826051000440c20310380011640c8141b4a154002c40456000032034082410359040d0301404916079540c408607545003400d000c289588210310005109924000c0c600003440410750120341c003000207000c24441522035110803402c0c0d0103603a035044d61507004400e51409050145a84030715900340b0101190505a4540006070350001028504480031740002d410402c11a003400301c9410904503040290850410000a01c08402d00500037095011010380c601000048090700308020340e070140840301a072804110008501c0c40c1900d4003001442000c03d0040881226110f03160500119520709208035406591603c0001d03510140501600c3c00c0144181c00c91018881c180c855030080e10307424503d07280b0440090868070176101d030342c1031603141c04030f40c0307001407000b003540d00700b4a070010b030582825159820480e009124596408110030001000201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 783982949 1250 783981699 783981727
    0x201140705031510020607030b0109080a031701090e100f0207060c0f12051b160206210901050402131d06010f0914160c0c030f080409180206031303020c06 68
    0x2100b820003403c0c0d180a68014000e0211404040c2d18100168020f1400641081d20079400b02111410525000c200c0d40e548840c5070381000c103021020740008030302103411441441d0000c1c09c14014002e8a0041210f1101c0700051526106155540200b243d01c030340c0c240a0790203103901a1180e40741c010b041000000b40640e4060540703410700c085000410013282950898009520a1a225488030f40c1c00381071240b140000f4143c80d0344025044218058801d4000303004d070310307040098100e103400211584040000340500c000c030084024524103107681003008001c010307110b00f459465410700401c00403961281d15128091441088414003440e44602800041d00040404140c01100c200c1002001410b008103100b0a04000456102c00011020107a04030120b12030780104008a0081403039010340c50700ca030342c1c40041ca00115401d403501d03000403405003c0e9100a10030035060701c036000a010484440b903400308a803400000c01000c2d900040003c034206240c001d00c040707028039030000c1102c1e65840100300005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 783984199 1250 783982949 783982951
    0xd03021f0617010504150c02030c0303152b0204090305070212071a030103110f060c032a010c090e0612060a14100f0e0a021204050708010b0d020a0302040c020114070503 74
    0xd1840b001882e1081815041c0b150a02031500151003440da1704d99100441d025000c080d1105003188030400c00c488c02e40720113101440c06a100d6495040c2c1000c14201084805c2040d000410f05085c80040b05d1170303400450600c100181a4103941c0807980400604098510340104e20020350494000c10340c030780c2c40180c0450740105890303580302c041c040305042460f024240d0009000041942c1c81500070601c0d5440c0042c03075101698401460a4503102c50107140c1360130b5400100d5a014603002040c4003a441d4888000c000051ba000300e03001300504400d448004000e05503e10410242c103c040004c54403a8490301c100d808140454400c0351110f080c2000e603c40100341c030500601c0c03401d1210021402c90382c0d02015860403148549e8111220038100190b1040900b0b01404480030182c0c00c10100650790000c8200390b214600901c00380001c24075014200d42941e0154180300e10880b4107040c02c01c016a03070300038a90140c030313015140054060551700b8280c0c0141071601c05c404804404c5070410141a6002d0015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 783985449 1250 783984199 783984209
    0x305010e0c191415130801060f09020a0816050c07180f060b0304120203071a0415021c0b0d0c18060b0f18040b13290607020d03021f06 59
    0x150b003408180303070428409031641c095800a032a40380d04081461420102460502041c40b2040b813804c0c403842004490f400c12030b03100c2d002a075107c0d2001c115881c8403024100c000c000c548404d40c540b07540380c5002404460014542c8000c82100c0400d202c0b550304c103400ba902d07840a05c0c003c17100c0003a15103600302c1c203c2041e0108004850304010082c4503401050164404552900c070311307142913072119500c2d0491441d082040700214803040c45030202140c10b03401501d00d207800b000700c20742e0f99051500b0908030030456801003801c0e6a004000140c84011091041d000701c3c0d00100f400a49020b81000080003901c407114082d14180381d071b4401003003044400ea011244030429150400002e035a60b60b016049001c0c400c400000c000301070144414840c0380001c11060440d0007000080c40c101d03100e00003040a05211020b9408613552207002d030400700e03081d850395400d2400520801000361b00300001035480c440e81034001c0c064072002d824501010b0080109145106030061845400071041078200004c042621030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 783986699 1250 783985449 783985459
    0x11360405150415060503060603070507050d0807080a060602120903100c0e0a060e0307050d11030114060a0f030b0c0705161206050604050708010302061c18020f060a0503071202040305010e0c 83
    0x18510070014803c055504544107911024110f54600c0308001d25900001c03c80014010f04100c2d40d00081c1007800122100074058444003664200b003c4014505200140382543c560304e09441401400d80004003880703035144121030285c1c1e4030340c0384001ca4100304040801200a50511450b1100c1301c1c0c01910381c10140700d05890001e080b030b40d01c01003100c2c0504801104e9401da00403000c2071140303062152a0302021405404c00d44950004440400d007198450701380e013040841d042051056910b00003903000c00401054176131900c01401c54035078034001407024040a940d00c400240740e204009042c40021b1208864a43d415003040d9a19204480c44c0241d410444e5420300e0700c80081c00a2501744562401252282d40e100c0080c2e0840c2e082c17090300d03070000400300d14207050100c6c22400160039000702c501c02c507110394100788580e00038414000074110300f0801034440c0340103111140c15941d0003000d5940c080c50500c1c2200e103409218004000034422600050102d5003401d1250b000c08030002031150b810001552 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 783987949 1250 783986699 783986711
    0x1206010501020d1707030b0409080d06180623011b0302150c030112060c1e0c050f0703030516030912060905060609010f03021522030303113604051504 66
    0x10b411500b003c407581c44504c0000c0f40d00003144441348294000c9140c5a80500001852410b0340c0ba41d46203500600000400641c0710390090052503001d8088407100d85441c58248205403c1000b1b03481042c1034a80c060503410b20786800041c0a0b03119070782d1500410104411070300015440c0c00c000b5251100c200e65039800d0f22000021603280c00c4d203401100c5c1203c4800042e1b100e00b080c9a9034400c05815901e140700c08008110070032200044e81d500e10140e5a000a8031230f0343c0d03411811301c1d04a0401c0c10218115500b034000a00400129822078110f07003003940c02c00b03401d1000344410314060394101801d4010382500e80e50050341c1c1341084899400714075842d0013001190382d03c0c3e0314003082024508003400f41104007881d000c410001800d00080340349032507409800f098203018207010005445003007065158080f8051050800505815200300741f4080014642540f03801e501188812188118030303501e48100101c41100701d07840700c900000f100c1801009100b030200742001d681620791080c04034a00c51146180c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 783989199 1250 783987949 783987973
    0x2109010e160b070501152606040b0705070501141e09070503070611100203090102070308070507031b03200105071106040203211303080403061a090a0209010e120601050102 75
    0x741d41c914080c080404507041030030030380c1040464100c0d000480c3c10799294543c0c07090344a000040341d0b01404001781841860041c1103001c406400c02c0594414082c0c00000920010500a41c83c0f6540b080090074203643d00c14107403501d2401484801440d20071100c50f5424024503040414603440211900c1d1102c04403600d840410a03104c0840f0b208081d4158040c0e8170030054035000300d8906018800484c19600201a240d81003820b0360f10880d0300f000345940c0042e21000b0142c21102d419004074080c9000ca04002590307070050300610356070346600041499290700c102014880c6494500b02d0f41c040b1448482d1030304140415010382000d64204002c02e2030070f44030020044000907900d1040d41c00500810131505078a9506840c20040065103480490810010700c50172290620300d402181b00700840c036550b0380f07541801001c803081d42c106000c43c2c001c00e0300d0f00301c0079503240760f0f07160b801101c602d0006076201c00c01001071315490005540c06422111a80718116000b10108009040790403c1e000e80d20100c41d81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 783990449 1250 783989199 783989203
    0x80a081306050103050c121f15030f051e030c070603020f0408010f0506030d02010e03121e0403120b040203041214040909060e010501060203032418040b0601090b0a05040909082109010e 81
    0x2034100008c006200b4011000586e80640142400c60716407040d6154664884d11080d1305007900642c180c510b1b5001d4001494140c590800641010b03811801450421851100307498461b41940b02e11400c0540115031b00001c5a050405c5900030800840204400e000050481014201c203c0300b10b44a8000d08201d000c0950040c00356441c40700b480c2007c0e51404030585001204803001825541c0181003488031000103880c941d040d80d01450003605c41d20996408070b602103080c2c80b0580e0015000f14018018800002c1c0c030400130050b0701600b82030280d02c2580525030b5182602459000b100011f003083c03405414004540d00900c014100c040c000d02c910fa8998200740d070340c0d120a9540000100b00c1288000b02840040c1840c17500403c02010880700b0440c154800c00b44ac00103607000c0e00c0158008040c03206640e00203800d40700504400907464149080e007030001d030807401607101e00e0580c59101c0440e80b040140040464440303030b69460380d0941d90b207400f100d11000144211100141503103000b1503051420b0380 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 783991699 1250 783990449 783990463
    0x250201030b04020a0225030f0506090105070c350d09060e0d20190c061b0213020c0c0d0b0103030212031005010c0201020a1203051e04080a081306050103050c12 70
    0x14580013401b017203e809640b94801c001882d0030155080e0002030200005083c00c4a1070b0401d8095001080e903420b02c03220740c1c2e003142c0010741050148a6000c81100000f0040181400103800314030180501d804140800d15000c1042000d580f190031000413a50748202d955481008100c2c05810204400031407180001ea035400c180101702c01050700d254078003103221402901080d5141c08041900c3c00700a0707001c0c2c030a499a2280d001200d0f040405081409407a9000500040001d403840d0624080001900425074106100c1d2818901c0780e0000b40b2580009002c0001d0b1b102003602603c14884c0d61800d041881580101780011001406811030040001e060002542e00540c1e401c448580c080745030100548080c80a1841241580a28002900400d0000c01d8030b00484d0307459140824103240c038100d6241d00c0010100540140c00c0541c2c28040400d0303001041d16401c240178249050b00381c6461404030014200000000c03c0d00e414100044104940461008403d5005507140104048540c66030703030712290 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 783992805 1106 783991699 783991717
    0xf1f0e1b0d15050f011706040e010603020307080706030b032e181b05120601030204090c03020901081c0c081c020c0f0604050d02010605101103250201030b0402 70
    0x38203c0f00b00310344c07003424a005921a41404a211803826019200a001e030342c0d2501340d5022140250302400107103800508a4903016a00e200031a070750300075030142100013410001505ea4130305000442a903030504042580300420144288221046911000100d9280d2914a2510841401400c0000103401a160804508005032940c0104043ca0307110501480020740341701c0e5060070108115041da58100c40105806e4010f09048820503c1501301940c05182400006207407100000c1260000074007100c5420700c0e0603400820780f200c01c4070750805080200204502c000160080207601c129110006005040802c0c3d0700d0090300c2d00007550041c61040d4041400e00040c094100600c1031000482d01c02805110701b403a000c03603000b08428201109001c8134000e001030320981402501c0e41c540205c0115070645203001059035031019241400c1c0e011a203084a8594581400d00840342c0c44a = true := by decide +kernel

theorem cover : BRFrame.Cov 783812949 783992805 := by
  have h0 := BRFrame.cov_init 783812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 783812949 ≤ n) (h2 : n < 783992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
