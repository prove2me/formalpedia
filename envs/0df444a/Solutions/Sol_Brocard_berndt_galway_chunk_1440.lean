-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1440
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:00:04.154363+00:00
-- url     : https://prove2.me/submissions/6e1d5617-363e-402e-bfbe-5408b27ffd5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 258812949 ≤ n < 258992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 258814199 1250 258812949 258812969
    0xb040506360f0106020105010815150a0905040b070f0f090306050c0403080705010b010f30150807031101110607110102040906030506040b0603060105280801050709060813020604 78
    0x110440960040000318203003440300a90540034440d0502c41c0001042c1a220b260380244880c4c0e803500007240ea0791141d00e90181d24540e0250000e400128040408031040c1c40040c440c001c480c0d80c0329808800c0e00c8055500b650006414814800540d4200000c6000b03d812418001002601c04c400600900e0143c032025100503107070000076981000d00300440b4061540003642e90344840c1c26003485070080004403004c5000c10060110300c081c113405040c030074891401d44601001039109041c3c90995002c11018010b490a890320012041c0601c10400d541c0640001002041803a01c0d509045900c829000b04543c140440040624000200440c43d560310440d14107004000040300c10046009201e181d1044400c1441c180c008410400b02107156405280070307160340f84458841000b01a00c42c0828032815a0000c01f100000e2440d0316046132240b0074254481c0001e2a046d0703154034182c00d4a20440340c2000140b844002880b245400041c826049000d80c00d04030000d401650120301030344650300590b4080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 258815449 1250 258814199 258814249
    0x70b03060d020d050a03080c04050603010302040209030f030a020a030e06030c0f07140111041815050f03250302010908030c12090402070c03031e020c130203070c050d0804060b040506 80
    0x154451159011286a000d882180d000d02c240c208240c942441c5c08040300021b4802d0b0110b0141f03c420350540b4140c80340100703401d1959185a0812000754000c240305074146c09119000d401381d0509001418260340c3d90340113041c1c4103645203402814a075440c400075219500c03c0c014000031410746402e45055180e40c840c840e944020906103480c060b00c61082c03640351903082504c99079001d1030b0304018004440415000c00d060b0300300640700d0002d032040c0302c3c0b030f224141405050400041c58224041507162030040c3c20341350a5400e030041400c1200e1610080e100342d180c82442081156801850403000b001c056000e10f0030906891400b0342c9070109807207014912080410780c080c0658503035044410155010b10580100e035074a00e0060840e150405841c0d443e107039641e04083c001c074000b10f13a41c6141c20340200140b480b21564590540290409028001000380009145000034010019a00d0382201615049407501e018a40403055a001e51a014000c504041c24400d4a4485040640000130300d04845164 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 258816699 1250 258815449 258815461
    0xa09020d060c170a02070302102d0914190b04080f13030201030e0c18040609022d040c1b030302130f050907020321091c020d030c11070b03 61
    0x200c5121000c0203015907151201c0e24002c2a04040c0a40b00b8070241000b00c1810f0382c461007040201d0142d00700103400742e00200d5003c0c003903040b80e51040361108800b4541410900d4400c50200c50180300040701800940d42d003202d001800002e0081d500300c5070041c0700801c516a18a003007088a10840c0314000d01d6450482c002c50200a01c2d401034038128070350702c088591181002c1d04458004200752000740d000c2032400e200d42042880116610b030300c0c804040c040482c49840051000024840140140e800994820400005079205030803038219501c01001403600c0c04140d01c005c814940c911600c03600c03c52400090114841d0840720000e400071511060340122241414203030064072404103400c0218174881804a0f0310100d000014080e1801510080e03000d54699170240d07031313038410451114411695028142d04900c02002d41700da0140c444002c4e9050021801c0468007001040b40000000d070300407031910107076160700d40b1a410301d0707204920b050040195140b120a45450070360040c2c3d0681d8000000081e1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 258817949 1250 258816699 258816709
    0x1311010509060a0c2618040216030834050306042d0509010605010816180608041202060601050904020c0a080406022109030c060306130e030d0f090503030a0902 70
    0x41c14060b000a82d0303600e101c5402440c050380100200c43c4030461603100150038540200144401c1c0007226050b03e030244050100b002c030480000e406a01980070802212220b13072066003800701601c03d40b40c1340d0075410450400010700c030700e8145108598405a04040081c88030b079002502d444c48604003c3e03a02d84030640400d000d4540900201c203001c00d84c011241c501481707c008507081501441c1d007040319031106800c807400d0b180c0c135200b200c1c0001c404001241020a0440d88404d00d1070450030311000b40812901400707d40e600da60702180100d00203100300414040020701810f1081ca06102601651600d640060300c00c0c000d240e0864010bd0b03004c03500003410801000000c0c203440d0810622904c40e84e8914000f942c40c2d05030380328034201c4143c81c180703070f000c0070304610548400b84002805040901c078808103100c101e030001071043d54060031444600600c912248141300c44901d04502841c0d851490007485010ba40080100c002c00794a00344a500100f4008420b49030803511003100443c0100c1d55000041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 258819199 1250 258817949 258817957
    0x2030a0209150a030b0601021e0c01050c0a0b0712061202090703020915040305060403030605010807090e0c09270c0702010c0b040602040b0f03150109081011040f0f03021813110105 79
    0x740c001d903e042c808014000c1010340c06204200903800c5032800da904c111541e882c0021000403444030750001546086641c0901e01920040d00207500321407a1010645800c04882016110900855002010b505807030b0203d014640180061351340d20800d0580380d9020503107803100180750608241d8046000d044559560104a50285104099944940d160308190ba00c1766801d503421408a0300c1c200e00040c2950181c50580d100704003503210b0803082460080303142c0701c003040100410908034007000500d000eaa00e040c03445000549503c048420564200e018401c000c001400342100f00310b00b84543c80c0181c0c0d002c00c98100305540040c10845a8850f841e200c07019008540101c50405004140740c400070740c042000d0343c4214991005070302d2000074000117490396545401a01000d40101d01d00122402d61b5030420194030084400325450a95204403078000103416400c0402c4600403040100305515245401a412294008480d4100c0c1004000d4180988550340c000b007500d249009449010381c00344050f5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 258820449 1250 258819199 258819241
    0x2151005031213050a0b04060509180f04050106210303090609080307080a0b0409080708030702150a0f060816060809010b310c021908040308040e0f0c0702030a0209 72
    0x4515942ea91000284180c0101030b03000d1951080c0d810010b110b00d84441203100702c0c0c040381c62091426080a5080301e596203d0303924583c000c405a015040e05050049400d8410015184808942d05062401d142901c040e640005403083d40b00452000c21000c110f078194001e0b50500740062409454588000500015800030f0314400e00070080090b4280c0140b031851143c0403041040084e04c030580104400c0301e07405200a0140036040c4520400100071500031500104140101d600c1a160901c5103031001d5400c440e032510207612101d804c884000c40d40180c2015102c0540035045207804a6149001d4600521070041040300140214803104000e50010f842a4409401c0c030303841d100d01452500313640c03c3c400f05c10000d0f44503071502d24032010440c0c0710700c203080d0070710703902a014081c0c110040c480c222210000c2a5005601000700000260040c001000184240c0030003402c18074249400c0f11402c4c400030081164040b003000450b0050382d020a86402071603046440201980310343c854010030280c0d94080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 258821699 1250 258820449 258820453
    0xe010e0c0f130f020c0d1403010b0711040f0f0c110d270311010912030c0206090328020a06020604031202031504020d0e0c04020c0309041d03030106180b030103030215100503 76
    0x200740b603c0c095001460302030036500c21500f8003181000200d03090000302d00160540541440140200040c1100914041d40105031303c00c10010320310005011914181e01c441d0040355644102d55100900b8055000c5c643c9031800c240318840c1c0c012654684817010014003000300b0a0751003003203c082031851000c100004052070031f08041358507850405041d040707690b103060109800250000d4100c481010114605902d9a285441c19001f0390078441a504075129403907250060102c1388040c200540c2001e4203031045100100502c0d84d042c011300141080c203810010842d0045070801002c0381d0042005084406007200040c3e03290382d44040d10810b10892200c49038407a00014526054403d25000400030703003400c0c002d80390008048400c0000b24484c0100c015425001071140300d4840ca0164002c00024102410b0915841c03c0c1010041c119402600f0203001b0034182090300c0c1c03040d0200c04840000d4a0b4104040d89194159100a50796403500104601000740540001d580c091188240c0f500801019003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 258822949 1250 258821699 258821711
    0x9080102090d0b0a060e330303070f02061e031501050702090f060301180302010f290402030406020d02070b04060608032703070f0602010b0f0a030201140f0405090c09040e010e0c0f13 80
    0xc080125503001c0c42024010647c282003802d192280d816894900c004014002e6190000c11756507d040c1400e8100d00340c0c2c0c440e40c18041c414a60030803401d00000300762880200d955a150450b510f2041c1c1d68844561410080184841801a01c0d80910143c220301207201d00d41c5641e81d24400207000d02020f05606500f20b001c0031980d03081540541000941607a60b110501c103800300b44941c941442c010502803000b01d1004506100e040c00d06600454025006400241c50116070214001c1039034042c5000b16007240041040000344400341c4503d2010780350010242d45070590f8041401809441c054101002d846005152115664200251002070281400904a0541c0d41c4400b03402049060420360045401c500620083d10b0b0200502c01a83e42c142c6a280110440c0d0074041101e82210380c1b0072280e810304000c0400c05903141d800003032083d84441c0500e03a0b40c00c1d0490031302044c1d45842c82015081e80c10640000e0000c1d00205500940301e00c2511904280000c590018003038000d2100e501189614100f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 258824199 1250 258822949 258822961
    0x30705011d010e010509030d0c030b0613170129011106071805060708070b0603030c0f011b180e0c07060207050a03091a0f210901060609080102090d0b0a060e 69
    0x803124880c1c4441c1d480003002000201e10006090f50b400711140026900100883c18101c4444c0e40301c4009050700340f9000a10382015004070b11180e002400058051a000400300b01d000e00702c1071400c102ca254075000303001141071504c603d41c0c110740d54042c4081100c0d90b100d5482c0c01d42d114600d0066191100001c03103140e800e1041c0068a041e01303a00b103c01000e01440d50125441c02c052049641a541c480324061501c130082c1c4840300c9541000e842150b15020802a59112072010803040d95a400f0100000942c0084080c0030080505241d60700030500200710880a110300c0d03c000c40034210b1f054082e228401396942009150079204400008140a20110b052824880001810306415209441e8100d03030603250b4604099815200e01c0c14000c49404000030740c03625441c000130748100750401102d80940b06080d0390744001600d0444103050681c2d0741c3c8004110a0358094107000041107040000c6140c005028003150040c624440003805001c203110100d0000101503101400915070b030f108903886400e10b2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 258825449 1250 258824199 258824231
    0x2130603050601171203090115030803101a09010e060904090503120c0708030103031103130602030a02010501150504060c0f05061905070302211b0c01090501060905010f051203070501 80
    0x54041500c080c8582c0c4000b062030001c880d041c02070440000010625003440700f00e020b0b01907200a0203070b0015502d9044000d42c00c007115608070040c5100c0d140300c0c3c0d200d24021682c2d20341c1c242c503940548800142303040250682ca024100700c8905040070702c1c100da0500c0054011036580d03c06d5036203c0b50403926140704a410707c013010015103941d004618495041d501e41d1540e91303d05024000c0047c2c0100c60030001040002d02886148002c5640042941c0c02c08150a48a071040c201544c040380142c2c000040d2810754640c284121405000f020f225040070001d6404000d000b8001c0c0d018000c00c2c0217112100300c06210907000303240c00e000e91000032907850303240403081842905039880ca950102401e14010400090082c020303240340302c201490384061840c035800315201d010400b8001c1e802140b04c08910320041c80e0f403030001f07002c102e6034540003182c201d11500e000c034212182c0d5031211040b40d1401005104100f040c4d0300c4175044038011100c4102136405400039500f540309500001307025602e080c680594210309 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 258826699 1250 258825449 258825461
    0x1305030705030c0f0915030114090d1e0e190308041e0510031a03070f060908010504150b03100f06050a080a0515071101050910111204080706090213 65
    0x58040c0c4900503690810705a42e804003e2100358001c0301090650081d0a100520983c001c00040c0c0b0142804844008070303003118500c0001c204d541c68220304200c2000c80410025208a80501d040d19401c01c0d010380203d080b80c00207141500700030200c007c0804136607407140c10b0501800340c107110701082656841e2007265548107104680c011040d079030f40f031101040c20480a40031a40c01903c068510315999804600511381e8040ea141d00c40548181d41c500c90320200928405440b03040c50041d906400d0200250541e03c1c0c981c01882141e041804100025451500300d4085078200c84000c280c482407580000c1c280948a20f5840c840da251001c280d0b1a072140c2e410041c201d810680d41c01030740c0ca40761030b01d013920b4130003803c000f42c0113034400c2100c849800281072480750311445514110009030915809942941d030300741d5400b40d2079440740d0480d442c811a980310302c401c504141c0410502d000902c840f0b43d8502a03000384064a04071001c81d48106200e0b5a0b0458440e072039006180c00d02e003926100d2140e0045c41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 258827949 1250 258826699 258826709
    0xb030a020d06080a080f0a030f0203040c210201050702090711101406010309031b03120c0206090c0105030103020306070813150504060e01020c07030f0203010b1c0323070b090f0313 79
    0x420907100069089020551584131504000362501d000000d0300e14021590004115200301580c4100d0f54071110020309c09140210b00c541c80c21001e03507150040d11030546159521030244120100d08080061780c0000440d070455a050b03030414404c1d03681c040700391101500f0501c103c0103070003501d801b6050305179941d0105e1044881245141d010362100340c01101181d10121008000c40e203003c001c1c03001d0741d203000c2c01500282e109240c00b04103640c15418040c190b55241c80900090307400b090500c514036000340007603a503c038070038603081d1300710344c50b540001e952084040c0c0400244128580458180000d10500000b03090700f100308890b8034a0b110b41007030014a411503041e0383d0b062512a541c00e00103018000c9a1041002d000184410f0382161602d0380c502000b00d80032a0b00d50340c2c5949190700c540b80c806404012030300c0b030703031501c0441451400c1c05042d103041602c0c0c0d0b00c040941c00c98030300441040d1009803a101904941d00c0d81440c2e132020003807454405c00026100081c4800709103c01d0380404400e400055038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 258829199 1250 258827949 258827951
    0x4111b031b0a020d0303020c071a1201091406060313061d0d020d0e1e09040b041b030210050a0309050714030f03090d0f0f1203090c05180a02130b030a020d 68
    0x803940c1c0003152207522500009500c0280c8650f20400709120b9006402c803c0202800da07032207a540c0b0700d1450801c0441103580c2a00e0741021a400140441d42500280100082d11081c405522101c005528080303004120780e119403c088045035032092090a10942180d104804101011002000086806011940e0320440c4a13071104640c0741480802c00c220841c00a40f111030f10070548408001c10350105640001002800000f5007003581c0c0c680380443c0c02603000b4075004d20b160500d800e00d40041c2800740400100d00e84c0c81442040140c40f13500010007012002e18101d501c03440300d5401100900007105001d41b03207100e030890108070f000c3c0741d4028024130201142200c407151014011036031640251101240e1003600d90703400c00040b84080c07501e0100c3d14443e0042e64920030b070555444d034070300c4c3c0304041110009507900c65550030480c1201c2e0303100161404803041002d0342c1241203501e2841d0b2009001c2484150086000700160400f509200013500601407003079128503003030302160025000105410442 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 258830449 1250 258829199 258829237
    0x51e04170118030e030309090a0f0c0212161110081f050102070506130e0705040501140322060209030a1a0a11040e04150906140604020f040504111b03 66
    0x900ca0511408882c04080803041991000b90703141903801444010410750540410804050b490f030f00d010740d81d44280640e280028210342d6007060081112409010700007907601c189038504246002c1015100107440d030030130080c810031161a11070143c0c01c032140d0311074000c0410000c0d5042d054000c40d256100f4141c02e1b0601d4600410000081c82c03030cd8441c8a1140540c02120003808203041c510300504c003071546090000c501a90390902d001005500b100d03504001480850184515a8042c01c0341e10003444810030603055041c121443c02b00c00c0c0080d628000b800482140c040100015a015074030380040080039603502c08218240855014409501207002d4641c180002e030f04c4595070302c1a40f5000362012011400c26040c40c00b01e103d80c290250040e1070301062018041039a003928020342c11081c3c440c120100309210903d4000088840c06002d9500c5139005029a0909103140400da400300c480845010540c00354501a038a40d911a101242e914641d65507032040c2114030020083c000c0b00c40504c01342c000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 258831699 1250 258830449 258830489
    0x2e06020609010b09010f0509060d140a050c06180108190c020307060509060103050c06070609061109130c050f0a09030b0f0f010b0304030e01080702190b101e090903051e04 75
    0x4132003c00d000d9854510401d500034400c0342443c00c80301d41c0c0003e000e40b80c082c0c488859182c4a40b0194062078029103540402d0114041007000d10891003404d8065850350f080050207001c020611035031107001410042e80500103071004c160405048080d401c80e40041050040c1070000948130f41c455041600c8943c240004a6100301c40090b9140c100c81d00b0402030010b101c4203604201c20307070b88005001d84890b40c40c2d030302d424003040d154070901e245800500052580c6592a1050102e03d104401c43c00610300e2400d26008415900075044803140f200c0c3c01c2800e40c0c0d4500b1244142e5003910250005070801d080c8404101c8060f1035990319601505800c18014000d81e44c41403140b01d684411940100080c500110300d41d080d50050301c869411541340d0054a0401e480707418030b4102148194010366502e070100d4141b04c2060091005c120281c07000c5a14202c120382c41d105445841070702c1e40f18100d01079540e031440c40c0c2450b106d0801d41c0e9400303051000c03080403610748070403850660b04603003d00c6141049412500c91 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 258832949 1250 258831699 258831709
    0x30610020f06061c06050109090b0703050f0711031e070204150f180212040f020a09140f0711070602070e0a0501030f0609050c040c030608070608010803032e06020609010b 75
    0x1103006910000e0007a9070394582070210754100090030a0725011013020440c00910b06016041c06001c21410004080c2020b0400200070071001e460380c0e0a0619000031702c81900c0c5281030456000311681807a48000e10f0b2842c00d0752841c8115001540720448101103000590007680007000900d0007100d081c0525651221b0f0801c04601070301c00c0c0d56013040240381c01c05c0a0900c145041785600031207000141020329620720b042d608217088070125010384640b68420304601d00605400c0142413204001c0260803c007148045207580083c00c48070004a610000803109486440356043e4044402d003510045940c98801030b546040c0d038003034811492050350000e5026003413480340604a039045540801d807204503840e510000c086840c0c0a444602034284100344d203407654018a01c3d5850301e650005001c600d0140d07a00d0030118290004030812003820010032101c8400000c1c0d0750004400c404203106010318240b649055680525403d03019003102a0000c3c102d9001b168080c0700341c512100034443c1d1003a0b502001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 258834199 1250 258832949 258832963
    0x815030a060b181608040309050411070201080c04150302070206040f03030c0606060215160c06020a0e0312070201050715140a0212071814031504060e07080607051207120c0503061002 80
    0x210071a510b4440303060445c07080c140d1507001030017414071150303d03030321a40882e040e02d00003401d0074100d09000800c401107581c40844141e101c001500c0c1c2710300702414050700c46111103822242004050300803840000b907550b4201164002c040304032521300c001c2e07524540545000c82c00001500c0391407400d02c0c0012158004500c0030705a40b0a5038518049a0f81d90100c003908101186588c8104004450404009129071004007005102e5445070004442080105071801030b0001e4a04441e29017880b001006076000426103d100c2e42c030240c0c1448040031504010001c243c3e4440b898040703490a4103200c2003402d50790042041a00706480742c1d6140d900d11000f50f0300301c41c8010252940c00b8002408002e01483e455929140403c02002d9404021402d9091507401400391429680ca0340d50340180420701804000c900d0060503074001404051921590242082c043c0b02410001e0340c6100000544403403142000c08241100c0420802000c0080c00c80288190801c603800d80c000d14000f02c1006019000040702c17 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 258835449 1250 258834199 258834211
    0x1080f010b0108061314011707060912081608071b141008150409080c190305030606090607081602010305010b0408030f0903011d0105160509100815030a060b18 70
    0x50f035243d120b59081c00003500680d40340100c0c0c1580c0e03520200b08240d00d03020b01c90080c03078000e40c99030f4072080103108030342441741507804030702400351081007049010a080c40301002c4e81d07040390002d52038242c440d0f407a03480b40340310b544010301c82c2000240a000f0000410070801200501060f0f0381207141c0c403000c2000e0088580c41da110760111460a0b03484003036201c1c85000e070b40802c0807541d03c0c0c11201440041001e8030951071049070b0603803001c2000380029a00f0001d0707282150715240030b11401411900c0140040c480a81818040c10000a040d60b01e625800f0455a0556000060a503204100303c01c2c2803842004003002ca0029041c9000020b0081c4070405407016140300c44095480c101c06180035000b0ba6100c84c188075019501d4042c124010580c40401905a908034000400c0b286081c0c078614503e00b5642000b02c0a000c0103004106081e118040100129100c900744400a9144d80c00c100011046c040302c011352620403071071840200616900a07100104040e50046289010b50500e0792640004580f4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 258836699 1250 258835449 258835457
    0xc13050d110d03110f0a02100206010614210106270810020705160b0a030509070b073f09080f0d0c1103031215010f0f1d030102030f01080f010b01 64
    0x10720206142611030410202c0c404e0410700c505441070303280141020900c81408003903400c00349043d01542082e07007a40c82c0c1d201d010710103001150306080014100042c1449040590718021500034400313001280c455035203445001a0740300b41d40c0d5a2800408040750342d5050000245403082100700000d141d6050300c01e48032401c019052100c60103c099009411401d800e44a604c100780404a5030014403800d00040c003c0c000b5031680d40d4184240181c1a600c0140c52203107075074000300c404c01109076004141c480840e0300c5040e102000383c0300812041c10b00d004061803000383e9541040000c038400d1100040c103404100303803a580080e5607550040c0e529110015901038640d00624503811840384203c1445040c0d80c03196911028107030345000441d18503000315444030f0b00c0091490078001c011411070301717040c0c00e0102464400c07000017038150001e0448240b1780c15202444807080001c1e02e107469a820541c032100d0054000c545a107041405519018000c0c0700e44034540c01041040c14285206000e40d03101c000c01030311 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 258837949 1250 258836699 258836723
    0x91d150907062604121106040503030105010c1110030b01030f0b0a0902070302070e041b0506070c140303160609060501050d0c050d08160309030302061303020c0f030309090c13050d 79
    0x2000c1d5403e400308207140d0b12060030003418040650901100900450240361010a5125420005007004100c801d00300c0c0554491b0040100180000040300d05640d800e2801d5400c64109150044e8011520311050b035000c80000d8112705c1c015815485003090180903079003440000281d070f00d02821074140c506016000710a501041c01305500580080c00c40d10b03c40e204035498a9a51300589440316030554044031100d5140b012890035070140490310000c0c10003168040d02d800096651110700394054828030003419100045100d041e40c00340203951800e12010f00d6a078225900e46420002040c80400403210386180c500045200d044c29800d09070942d50003120103116a0900040044c0421030740000c640c1d420041018a044107000f04100d03080d640b00e83c55030080d075801c0d072402909140b4001c00500f1084203262441c8046680040c3ea00080d800a6401c00c020708650404641144101c10720543c000600c501031215141c0c20000810011101e0140d1303080050b01c504c100500350180040140550b41412 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 258839199 1250 258837949 258837959
    0x70804170a080103020609010c05030307030b031203061e0312070303091208010518040f0c080f071502210405040905070905090703030f050d0f050a0b04050906070206041b091d150907 80
    0x40000d101f010300c141400d82c484165a540d0714950b51040740c018000a440b0380241d146810208159001c044189401c03074110f1408502049141c070b45001880011003600706680c1ca603032000e2008460300e42803896590b5413002181009005400c500d00102e071060503444000c00b00c14400c0321036a0688000800420071100354210380c0000100140080d2000745002105400248003a90701000601c050405400710011124001d4104101130b4400c03590101203484101c03040da4041050341c11400d880c0e060003c0e020000d111740e007041c01750703400c425001850012035006001d40058410101ca814110610840c0e4440449546a4180d80f02c0203000c18082c0c804504c003a4011800781021552080c0d0000f89000e035a001e807026200c007910784800641d600c0807a00364605150061a40c071042520040849042941000f592a8030040c000380c441e400320782500304440f80b0750080700000c0040c07000502292000600c40d1804d01e6012802400394892002c00050740000010298404c00c0800080c144d0b40e0714103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 258840449 1250 258839199 258839209
    0x2c100e01182402010b03100c0e04050c0913020c010f240e040303020319150914040c050f03030d0e0705130c090603050a06080105090a031106041707060212070804170a08010302 77
    0xb03000655407900444011070301c042040094043c0707025004a074000002034080c11400c01094840e020324105030030000c0c0c4105100803240002c2040d226030019910404180c1e0090003400c110195035405c100c81c1030315007141d0b9000341020110002600706000202064a0302c00f61492045c4040c044800c1c00203000706e80294082c50740981c49100b000140342c0e0880030350080361107026041042d002070074020711001c4020702c0350071010160b03080c0c4c06101e0300f03098031061810342e810701c02c151042c0c100328042c0740c060320240f0550318440d0b80e50a050220b40c55241c151522409079003e42400381034178104090024010703020b109044c500c0358035004851810b1807002c40280034000c2c082200d440e200c09000450803000d11400707100b03038140d40180145010501c1c005112114000c2011074941c041400d02c00850310f000e07a510a02007419072507560351040c0d46001da0180c02011803580f8406100020401c006800500c050701c1244180d41590803044400100b1041d4040d48010348002401c00c4014401403c05c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 258841699 1250 258840449 258840509
    0xf0b070c110f12160315020a020a1704030b04050303010527060f01020c030a0812010b0901080114150408011a0301051501051308070b07050d0f2c100e0118 68
    0x18004241281c0f103144050700d407002610320ba0940e81141d1104000740070b944412140002e5040e00150300d049021200250382d500d8415000c1c000ca4008000e11103d08a41c03022103000b50303448210314001c3e291600381540c40b5042482118040d0705d181415010840340102074851017100940c049003203803250300c180300c0909001700132641548100340e0700c82d8040e5000c0003686281c070f11030100350f40d81d00c61185c0c07112440c20040c2d100440801007486038112a82e0046d06c0b55055844071454100204146000a203182c0850501d40c0312003880010042445441034002042c02c3c45038440200c1100c440300c041c1407c0340d404540500500c0c01c008502020385d03101d41c009140c13140e40440d051002e207440baa0020b05100c665444003850341000104501001014000c48039086001d042500c000383c2211009009808a00c0c2c61400f10b0003001c4c0100c52100191003051034191019003040150302842d58058074002c1440d00d000c2c00320319000d94003114100914413441c1070701c81d8800030b48440c444039003a000510030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 258842949 1250 258841699 258841729
    0xb060301152a0c0b03040503030c03131227050604050d030e180601080a0507090506030406090f0303050114030f1005040816051501140102060712060806040f0b070c11 73
    0x5038900104071089181052800088814200c407034840d0b0301464690b051000f581e02841c0c0207801401040b000c41c0d004030507280e01403440c034007090b90f0381e81d0200081c0c8420208100146154002c58401903510340c000c003801d0309602c640c0300424501e480344400c402d040c2c403180b2602d90b12110402050099062107020f00e0000c0380300f410714803070130800301c1c0000703d624824811800140b64a2010041c0d19a440081103802800c80c11081105050128004000b01454020746000d0200000402c0412026501070b2883d03030b03005840600071a41518004000d840280b080e144c20400001c01103e2525002c1002c215400141004150a02e8502001c0c009004018016a404c031014006080740c8825140001896071240010b072100c00a54401d4851420701078002c82040d62204052406ca40d800144071034204680e810111a02a0080b9110020b003c8d01c0d040b02440f030041000b070001700082c00c80341001d098810840c044866a542204440803081e261002e892401c900000b000d250800f00396540e2211 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 258844199 1250 258842949 258842957
    0x70b0c030906030c0c0705100206071b020d050106060206060a060e0d020a0b0c0102040e1857090c04030303180b07051201050f01050901120f0504030f0e01030b06030115 74
    0x81e01e070100007600c41e04102c548030648440010700c10040401030010002a00044801d1282c01800c054000e590700d8005000100744150908002d251010700702c03c030341c0d00a500812140091826150580c00b07001207110f0701c005845500041561850300351520b40c140c2c3d0255070f07002040d101c240100b00c52403c54138016a08003030141030110b541004100100303a800300038800981d8480c5001d00c1d110710174400400389155117202e08582c030002540480c000316092004107600714020200304959950b590383d40d1150100345060304007114082442c01868108440c001c03800c0341e085001c0003d00580a01c11030715402c41400c2008180006806a407008100802010201c9030222080c0d80d9007039450826283c040100b02c010030710111b00da0b140780205000d05025544510804c0c08140041d03d14007a40b414141401141d80d100540c411a0b80c0c004034002a02c0f500c00c2c480c5040c642405000140070108560000e0842e1034001680d500070300820300c003548083d00e0685140e00e891150844240e016070400d00b00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 258845449 1250 258844199 258844207
    0x501120b0a03170711040212070f02010e0601090905060c0315130b06030a0b0f0f060f1803011503050d02070b03011a090d030306090605090f0c07050f100f0b09040203070b0c03 77
    0x41400c00c0101850303c070743c0f101210703503541c41070400c0c5005149008403644124010056102c08005940685412880c141400c0203480c240900503030141055480b410014800c00000080c0100c03160411070b40c0034080c01c1a120f031078540e6130205200388000c440e0b02c0d0441000460342081ca05007804203642000300080c000408908181c00110250301c1500c5680c5e046403611100c00187c07410344c034050703180f09084620350b0a0607040c00c0410114001c805810b51002400709600e016030f07c0303001c01d0a0f848000140204022040684802d4200006003c19180d0340f00e01a400c00000707000050300016181200c03015402d5a20744003030b45050241b00e40824004441c1400b2010140d1603007400400b04a200f038401081080c10210000d049480590000b40708e034100d038043c401c807294401141504014a100c840390740b1100c6e0300f4090f141125690b01c20702c4602c5908142d091103c01070b80040040c000240062203c400c5001c100001d400064401035450703000540b0401400e140c5500408801c10b00b101a00c4c10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 258846699 1250 258845449 258845453
    0x31207021507090509090a03020a1707020a030b090c1806150409021c150608130512070f1e0308130c0f0603060306060602120f1e0a17010803040501120b0a03 69
    0x10701d940550b0650082140d8600500c000d1070040c00c2540e01501403801484002001e84000b07503903000d2208080c150b1911340b080315032601e01107022a0f07605034014101700e4095540341b8100c0f19004046070400e0030f82c002c0428009103450207000c640301d141c030003824014007a241d100c2009113013421200e654003400c2003044002000140780c0080c00314007035810080a006010f04000500342c0b001d412505102c0c01c00c40c042400420b400c000e00c190411910031100c0015200c0786040ca20b800410701c55504481c2002c580c0c601082400c0c00f104260a1007a1022903100c0c00620138680844e4004100a0201d134907200054610b00c1b01b60030105081e800307000500076885e694600d910142078943c000c030001a03144c48040c42030040501649006040d948000c0482c51082c50f44000d4501503400072a81417040009e5821558030750200c0c8802c1070500200f00c3c0c0d5250500000a0003001c0700b04485090b0806800000814190100641d070444006031190464010392b44038100041c14039465107540311800364401b05c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 258847949 1250 258846699 258846733
    0x120f0902210316120801050111121305090906100b03040c05101205070909111303031101150b030906060114030a09020109170102031801060501020304170c0d0501022a03120702 77
    0x9083e070041c0c034070300035140b08407000404c0b800c01600000e040c031994901c0028003500000da0b455644084030030007070700d0303204503807202000a4455012581c400d00b100180080341201080311401110b00c100c880202d9651521f0003005400b044030080d1400c0240e0004101c0e0307003000c0b0340820b8117201a00d403184a5240e010900070456005030b03820400550a20420300661000e8410524402d603421040780c244104c0d441c10b00e5070f0310010f0000804100002141c604603290940154541d405220002811141ca41855191a070011a164140d902c10003001c00d8a035401034007805042561003255a21315914815140003070a90400100d04000f01280c0008034210024030b50042c18a000d0005607490034081b0b0388042d40c4500c1680340441e40d14140d000c0103103a80000484040b60901d26400c03003402480803a040c00e040300c0d4802d8540004000601004010041d801000010400d1541111880c80d4110710303454005605003403031440d41300f00080c0108420720102c5035800102441154400c1c401c09138494 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 258849199 1250 258847949 258847987
    0x8090405012303031e09030a0503040e06150c070512031b1e12040302010f050c0105040606150216030f080903160305060615030a0509010219120f09022103 68
    0x200000b8098091a403040c000c0000d031480d90080b801503003418410840c0b402c0d00400910074844842d070004030102e45440a00c44040290740040550351942c0c1d503001401e074084400c40301c10344295485210340d85101022400d407941800000d00a103821401d0000b0b20101001c0d0360790002441c842402003000105110b550080740c0761f0b81d400500b0070b0000481d2410013128140e8010240b84c0c1001e04c0340b5000c1c0345050261404c4980918040ca4200607610f01070318944210b0421110550a003000c02c030030300000360458011a20030442e9921002d00d203003422600c8000c0800ea134201400c1c18081080894040701c3e480b101d580c09004001d2504810f40c00280c50038104040105001480c0d000400c20b00c04103004040d8400000d0320066215180b02c0c00140f06403000a1138080f509507600085001000709605032500c4040d86204a1100801440080c284262007400f0442c00d505010f40484100040d0040d0600c840c1d0140003d02d601c0120494181070301311001c00307d4564802440508a80c016440100d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 258850449 1250 258849199 258849209
    0x1e0b03120414120f060703020a0c060c0503061206070f03330906050603060609010c0614011d0a1802010c11090a0203070813080d180501110307180303080609040809040501 75
    0x501c004141071010310460f0541d4041c200c2641d040410041c0084901040344c0b03512800c140f60040e5a0060120305607100a01000d015000c0b9207440703e6024200c0d04a402540030b032200b158040a90400950985e558000845140b000240d420300c014000a0181e0007452021592025040b204018807090703607201e0ba0607400542c071620454004000100d07051042e00d0151409a804c075165180102c0803c1c0070344181502141045112403868050003201c2c3d00010740cc0d0481c29042c203865943e0b080110000c3d4a00401b1026103805c3c00211340f400640d803050490110304940e454460007200e400668154583d03001c00d590b910a0a0b00381542c95540f0b1400302c2c4510901080180c036410480002031407188001c040024036104914901d010803038140640d0b0b24141c2030900401c1c0d0502080d045501ca5910b148000d005608003210b80c10b9508412000c0c40c80f0701c400d43d0700d900343c401940032001c030303014031520006e004654040046034842c05c00303540c1c1c02e90060098803214074112151000c01c084a10992003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 258851699 1250 258850449 258850469
    0x9120d020c1002030c0a03141c0f0b01081005061b030d020a0e03150105060d09020618031c0c03050d0e0a05010506090703020f03010b22080d0e041e0b031204 69
    0x200c4801031a2900300c2c0b003400c0030b82d84011400c0804c01441550307100c0c18944085c0a0001c0c1201d030040c01c5450404942006a012102c0398460b5114030140014001d442c0c80308808608010005c410b0354840c00c401403080c40d0541c54468928903020511040343d001216001003038000300c0300c440210908000500e0914241e020050b611800c0340c500a00c07250000f045c0034400e400484130503420200c90841d6a0544004a402683d41c064280241000b020300a000a4001d040810340100034a0fa001c5501c444007420340680d000c0340d000300507041001c1c001c0002d20011600150820000c0303440381e00a4114250140b4001031403070500c0c8145803510840e0601142c1d282c1d1a54100903180c00e00700c0c402c541000260405504080c00d561aa0380b4038041402446190b034004602c8450f060b44211890401d06c4003400500b8801c2d407207000240d12410018200070225400c0d100741c611a061511400103001401d04d042c107000c20b81428031001803c15000c003150b05105040c00000c001c081240100014444409 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 258852949 1250 258851699 258851713
    0x7030f0201020d140a20010606090f050d02090412020c060304050d1e050714250e010b0f030a0c12020c030405040501090e0606060706020d0c030207020f0307150509120d02 75
    0x3000a02c2d05483d401000d0410020810705000ca400d10410364040e0b11841c2002071b080010015840e07490500080004c3c03c541c2400b2001030901d4000140e107084d58000305040c0007654403103043c0722911034400c0009400c0019240000c012944644000301c000003030b80b054407a14214400045c0d220340080d181a240d6400c214180310072150015241010441c00c08083e5074519181403000c2d00f14014000c0c050040c5049804124a00f10305110004018605148408c012010004445007050a80c0103c0070300a11250022414407850000d8506100b04080c10501d95544d417407080010301001d0304440148024580d01c049444154000380214510480c010740d00c031482e00017003200703460043e44081d04035403030001032062119000c102141d20900c1500d00607525021450500700901c1903114114000380780091071001103505030010a0a43c4c000c55810b40038521400030141c844001d441002060b00101c041041824001c801800c41e40c50001d250b4004240071000340350401150580d80030061300040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 258854199 1250 258852949 258852953
    0x80c0703030e011d010906050c03040510030e07330201021204080306101b1101120603050102070204140f04020907030e070e07081003030504120c090c0201050a05010503030906040902130807030f 85
    0x414139a43c43c210184400f901c880804000f9254020a002d40d070108000029040c11102c420401c443c0108000340c0034940000e44080014010722100400460300e0007078002c00030b10428501040750f20710038112224041d001c1300f03014020003058460b44900a55400380b001648010842c01050301c85e6014010a5540b403500c5c038100f146c600c81040c0c185c0c0601400c2c15200c210400c032408a80b90765035101006e100b85016050049e40d0b2031b00b20041d086859030a11201204104042d00a070241d0ba00c2518184000030003945680756003e421079101d034105000318001405890700d45208c1d81c0000c59800c002802039070020304039040c030750150003081000176000b00b03000000364018513581d40b060051240e1034042d41140d032f004246125520458030701200070b0b03c4074002e004a41c803040000b0900000104214401584040c0c080c1500700d40c0400d08514010001841d41808401c4861b000c0c8000c0c140da242c40c1c101450240250481c14086010041140c0049001c0c0780401c55a400345008071400300c4245828 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 258855449 1250 258854199 258854207
    0xb010908100e06340e100f0311030601120b0a09020f04080705030c030a122d020d090501020c0103050c070c03030503041104020403171b010204090b120d0912080c0703030e01 76
    0x42c0c4402078002c01c81e2021000304185a411418405035108a0b041e11408868110f500342d1a10346110b07032200c00101b010f036000d900410845e40d00660380c2c6080c4004c81c0000300c3d90070a03000445486010998035008031004980a5100e03441c0b400004010f80b040c5a1213880c15070480c2c1210401410f00300700000d0034480c5071001c008440003084c0c2180201107580e119804a9124840f01200901c03a9403030500126840b409104140c000c85664000f1000c0909000da480b90015011010038001d401100c0e80780c0070092154220005490060700148052190400114001d140003010512080824000080003a050000302c0009501079500c842d100c0c1818101088542241148540315a104000c104006082041c192003101000444030f619a41c2045000c0058241a6096096544005004521094141d01c80b0f50803450548020702ca4020020707501d559070b2014030700f820104042c00810049c001c401d41c1e501003024483c00c9001c0c00c1075544050350303107084503079007044000c02c00f0f0140d07011f01d03542e05c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 258856699 1250 258855449 258855451
    0x228080f1002030105010903150e0604030e12070302010207060f0e100903051005040210030b030c0301050109050711060c090f03030d020c06040317131b080a0f0b070203040807090b010908100e06 85
    0xc0c1074030440c0756526000010b4640521131100400c01002d440003034062400c143d2204c001d030b6042000380c0306d4038640707071400910717010301200340d54071a0f2403030030095501c0c0d40d000411b502030360780c180c00900c09181840f8043d039003030341510940000c10004020b034624a03111186902881c00d00b035150f2207042c070b046140c400d0410780c0c00741c50070089500e04000c01c8096512610703011484021828006454000300020074100b0000020480c0c1642c204400011916101d034001403084a41341e4400c103407000c0000c48503440d03e1003503500c1e000c050020300c6101082d252000d602c05042070018201c901d4004080145d0080c2d800c6261400c60070b0704008104414190015524400c2190220401c0e1182c03820459240c05100d0514000d0451034a6400b411882d6001c03201800151080108071036400c0355516052082e02c010f01c2048a0170f0301401d0128402a0000003035030305031403880c0c001d003038400d0810100800520b82039416a0410010040000e40914180007903400043c10940105144c5403180031a03143c040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 258857949 1250 258856699 258856723
    0x1305070806060705070302040932010b0316091a0a06020609010c032307120e0a150e071505070605012909010507030e06090907020d12050103020a030228080f 69
    0x10b010002030002503c0400e440782560750407140040c4100d024100285801414038144040740c074031400c140b032020300c110303030001d41221040000d004078015802410348030f10b6030038407241c041d10072014180225002e41c2c01401c0100b402000f01900300401ea030001c1c0c01a903242c7d02040168101ca4140b0604c0d080038040d0384801412800c0521203869100340c00c4800e050582e9002d8001a07403c00410310062240088040005800c8000e0168a00800c02c440d1182c403441021602003040110b881c03a41111406440c2c8920011b8002c0c000d15454a902e851100104080140400800f0040d00d00001c40a128031070290901170111030359411404200210f440040d5091a2241c00c1800071800756a40281101c250651500d00240d001035400c0200f801401001e0285030310050710020400d410390700050300301002119075120340e0820900c0c01d16601301d440a0002035044030b010201031001d81400141e0301c407503d40d00040424400c501c01d1600101d54100d42024555801814030b0480900d0208003904200d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 258859199 1250 258857949 258857959
    0x40f0204240509060a0311040b06270f090c071e03080f18031804140403080f010b04060c02040903021e070f0e160c150501030b1801090b0408181305070806 68
    0x2041c103c00003400150107200003007210032607910315011f941b9250400600300d1809040c040e11104517051491134000d20000d02d043d10000368150f00a03601c2e2980d00416030380001b500d55051030f11141303450728281e4000c18041e00c0c120b042c154889005140d941000d11118083e40e05c8541c14140070114181d00d10000d00482c1815040c0320380d681d000d0402004441616070b4000440e0100040600031601600741100c400481e4142030041006064119002c5880b610141c201c200d141d0307884a41c02c0d0f426015a0080d00c3c005060b04112a005040c00d510400d102e90080c0112403080c805045102440728940b540504207401c42e0714200001104450031401400d01c0106c40c810070b10700102800344061407040e01e10204032410041c0414030000c16150101000740780c1080c8455a164103222005d24400d4a9010042c00c5a102c080715280061103580c2d07100340d1120070325441c0d44540d280d103200358004c58550719204440030b04098540e03603004001300503e80c505001055901d841c0b2000340c440c1c0b200514250140d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 258860449 1250 258859199 258859201
    0x11d0109050609220b0114011416060203060d0501150314010603050c300a0c0902030f0621010e1605030607090b0d060f2426040f0204240509 62
    0x540d9034070b03a181d0740702403043c0c4403c0051040b40d060139256041d0100107080701d005140003282c00b00d181001e4800740282a00d0f20301c5c02e600308141c00740881c070079107144500181e0400d4820b00001e9003900210380200000341894103100ca50b440351803c507000a103a00c250741c0380e007034801c008114517000d11203000710f0000020461035103035449490326aa8442d001b035105400b90402120410b14425001a03d1144025181030500d103020443d6a5001c50400907229994040d000180101650085138401c000034030510406480310424003204440381c41030003040a04504020f81091424800c0d00700925403840100400704c01d042e401940001141c2041d0300a821810800c55541e4000d164102211022042035a480103008042c00092400d50030444a0b00000c040010311810200001c0b01021032094520021191803c003c1e98403800274420745c0c8194135003114031101c24410440c0b0a0740f10303000703a4114400098550005044039400e0a100c02e80c0c00b04e82100d10500c200b640e5000025000a86070140a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 258861699 1250 258860449 258860461
    0xd020408010b2d091323062404230903070312020711011b020d21020d080105040c030e03030c0c06011a0d091119150c1214070b011d010905 61
    0x5460815840140500d9500c4046101c1400e080145d842051300100c1d69604a5030a07250320500342240da01d091410b10a4401081c2901e1400c42c5642d10000c0b0180c0c052101011003041c4405800c2c842d9900840c01c004055940c10300c101800703602d10614880002e15601d09a07845d016041101d20100298518410f010940c0050016051004109404d080254440800c92644141c2054031200250050001c45090782081841030410107401c123603820280d4458190001280d03a00940d040c40400290300100401030743c101540030b84070040fa146008221040b9481c4a10314650098a540001a000150101411000b8404280580526599690744018030a800070b00c0d40100003801d004039030b039007805a04000d40304624030580c200151502c920503a403030720245801c50742882090540c0041443e90b1044600c9603071b44105c116440101d0901c1013109040c200c800c0419040d00d640e044004100c1507010400e20f80c4014020081c550b803020140388112481c0180d0601a80111072480c1000c040c005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 258862949 1250 258861699 258861769
    0x6050a0501030b150a08070305060603100614070803010b09030c0126060402160311010c02010c140309010204082a090103020619091203080103050601050d020310110d020408010b 78
    0x1115001d18003c245854002c0010f14030250010341d13100c0030500003a6000005800c000403611490071610708000580d9070303078140b00803480221844405c0d01d5541009000c45401442c1c08509036480d40135040c00c201c0a60340b609500d51007030b04040400c00c03001c41c0711106407a0170004241c0144080c40c103038024401c4440c035418603000d0702902522100340c013400181d1039140c90b8180c4c1c00740e0b0401320747c02c100102c00782005000003e1141301e40d40154203050440710070354014081c508240c2d0240d03071174400c580b410014451407a000070b010701c0ca06540030440007034030070300410200035211844400c00003c05554206102e2820440090340d020784098001003000d030f0f8880040e20110000010300c00304650038210112500100e68000c8000c8510901e2040103042d4400c400724181ca2145040714916600c0303400b0410840030501c00258940d001401030302c940d80c40e0350401120304e80454502411300c0d020200c9034043e41c00c590001080d907136540c00f00300c00528200c65492195140b070021078104904000202e8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 258864199 1250 258862949 258862969
    0x1211070f0219081b0301020d0f02030f16020c010c050a02090711060708130f0201120515030c03060405030a1b02061207080f010612020c1002220b030603030706110d0606050408100605 80
    0x1c20043c101c0044c11501e51020340464803001e141c104104881e400102800d4020b400070745101c8104a0304100207128201282190240380700140c00901c80d8410301030046449102c00031089400380228201e000c0140c0728911500d000d008240c90f0f03070f8080f44400720b410f4600b00f0020107040802c4208418001542e1450440182c1d00e0781060004045000d10300050307031a2400800c440c40c000c0d152100300200070403111652180342d0412000d039101a58510b08042da1520280d40241540c1c004020390f126050081c00a029030050101c44002001c100c5d0300046d00c950081c043c3c201c000d0b1400401c00c140301c1d5000505035071001ca100d18002c00c0d035041010043c072162001d0764403d03455078009000e0050207400c201407450b1801d817400c03e560340e5410002001480160402c1c80d400016034400208010803140152807090303a0240c000d600300102511140043c041c0c401310340642c4a42000340d43e200019034024000507020175111155540e240001e51881d01001c0c0244941d03491412030300b0f200e42d41d10800c0340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 258865449 1250 258864199 258864223
    0x1080307053c0307050601080609070518060405091c08070e032b02030909040804031115030402040519020d06050f01090302060711011103180a0f080a031211070f021908 74
    0x2c00044046140500e1882004e81c05000e622800000051611000a40354410800c0c80141c410f400c1d968424883c1e4240070b2400140c03050034050001d0a07600b8a5800141d10802101c11203c1d43e11441c42881301240700b0441e10000a143e1904015044c0c0e08100c01e031240c6034080d0000c1c0400542d12920090310115605050007403c061403190300300c1c901c2002940e034090303030052068003103051a02c1c10407013a0303000303100444040b4103a903452902840d148002a0446005000a40c50f542d00c42d0f08000042c40000d02e0201a21038180325981c007014648081c1506000c45100003800504110420100c0519003101e18104042800244010386a8009448209074403001580c4000241e4005072200c1e031900c680c0100510010892400010360340098482c851400e9582184454a031a64820030040038041e503c07180e4802d98001c00002e208580318240b5001c810310016400e1841440c2c55040c0c0c2c00b62b0343c10341c3c03070910a0720000c00354545404403645101c14400c0d00a060f5141490444d00d8030002140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 258866699 1250 258865449 258865543
    0x3061b0c020120121c0506011b02011b03031d010501050d0204020304020301091704030c060e011d15040f030201120504020a060f0504080304090501060e030a030e041d060108030705 79
    0x142160381510800d210f182250050644110301e40c0f4030803c50168010411030400c09804454018000309540b003868007401041c4c0d210040b80780d5076240004400d9010404904101e004909500c0d01c1c0510342070400128400c5d54007142d18603540c00c08021100080240860a900d4000100026501d140c8501c00b01c5506883c00344c1c0744e56580c00000e00600c003c2c08040c2040040350440c1d0f42d0341d00e88500034015030344200c20703810381140c82c0da0b0219940d910204140d400728074001414802580003440c00640c10a0080400d440780402504401d100e801c41e51101c40d01c0010900c0070310071980c1205140c03800680c082e1082050f4075080c0c0010380042c00c1e500c565801e02c002000c0b112000340c41041100c0207071440b1411260754a03074500c1c0c12401060248902000220540013200541c9004030300c5080258042e030380c50310000110070030071000780302078465025064902e95003a0700c1d200701801045d000300b0694020f592280341c982485814005c20f0003041c460701c6090460311002d480c005402c283e040008590f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 258867949 1250 258866699 258866717
    0xb0307020c0a300212061e130f05012910020a11060a0207172d1209060c12030702010b0114040b07032616050f0d020904060506031003061b0c0201 64
    0x59840b049040d0f555003c2d4200140b1500702004d40300c0095000c0c0286500d80881300c5048150b0344a00855009441034a0b0746030f000d81410303020611421071465813a0080c800050ba1aa280089201104030b1503004060038540ea6a04103203490048040035500583d40082e00c07221015a036502410b03440d654000d0b01c9030b10045000031a0038800c008840141c9905a040c0c6036614050001079605c01c24058004050003425545a0b00030329580c1c0070f00450003808000707040c01c80c801202d01140c0e4008580554200c40c00740030441c2e03a158100600b42d40d44507401c42042d41c034104150006c1c00c3d035071001e42c11814861100000258140440111021903800003080c1c1d03128821840e08907498890320000c150091801c030b034030b10602078403215058003d004c625042500500c2c410000ea13020300074510101d00720107040c0000d500c003140c0c540044c034803824010000141e50ba01c0d080020b41c1d0790401d13205601c03c000e11010500400000e442807041601e5070080c0742a0450303548000500004a07490000e0403c00510 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 258869199 1250 258867949 258868019
    0x3011a09070f053703091e0f02010e240301032a140409060603080d0605030f070608041e0309170c0d0201050706060b04120302060606040f0303050307021005010b0307020c0a 76
    0x40450200d07010b03a0341c2c05803005840e80c40c004000e006040c1066a8a601f100c01c001d0100c603110544602440e4000010401302d05242c00545402c6201c030300007604150440c0f100b072003510b140c8203a500d09420400e800d645035415402d0540d02d28a03251086c08501843e00b4070081118080e0540c4400c0300e103402030b41d50324202c1a80201e00603003081003005001070300f03044e0044104583c0402404003210644020000660744c0ca080581e941802c4c3c0b110403981e00048818043c041c842c00d48954854005e451848050b620403000703d41c02e0203140019400642c2b00d070020300c003907003040311035070314104001004100e010601e000080358148041c034020706108000844104000b0b082d08013178010070380010480e84403607560461500c001140c0b05c04034014000c3e10001101464040b007070300d0070303100d002c3d01103400c19055075401c4e1080d600c0600210254030a0b43c100150501c46400303124042c02c4c3d0040070640700c0c10304074400317072800c400358440c2889071480306418007080c001010082c000d4821562400b00d510707914 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 258870449 1250 258869199 258869257
    0x5010503040210030f020403120815010801051302040b1605070b07050607031d0d020d0314040b070e060c0106030c0e07050c06070e0f030304080607140a17060f03011a09070f05 77
    0x8007044801c0c0c1800810004248120915400001003140d20341c00340507558402c520800c201d2fa046a54049490040184a942800c43d8990700ca500f845d40c00610345501d0b51440102e40c3c10001da000d092070b50802d4150100301041c003650f4001c0640a4880741804007070b54486894080041c9034404159840741030b00304400c0060b10a034501d5600c1401d6400b00782c81c0d26002500c2d01900401600441e04040346104030440c0030903144d1040d900209866140e485000048860903103400c021940a84c00303101b4031034813010030320405000b50300c11700011001c00e2420821811000008004800313100b41401100112400030030f071281c0c0581245406100100c0300f500142c10490f0403011503805103c013280c00700f078030341340003844c580108000d44410f24981460703000403c452060701c0c40440054980e6003030318000944028441c1d04400c0c000e00400101c20201c1c0401e017112a001945048002542c1130070001d07040112a0641024891900422201c010b28029205220f150801242400340c1c002d103807090040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 258871699 1250 258870449 258870461
    0x90c05030c0627181807150c080a050702091312030507050a1809020a0201051f0b0a050706060306021204120e010207030b06040f02030f010f06081e09070e1612060501050304021003 79
    0x2441001c0900349000301e181502083ca85d04080c91140c20b00100340c08003c0304401141c64044e42d0348031b00d0740509035500b940503009140180c090107010312003840165101c0d00101c0c824000c958107000e04900e46e0604002d0310440422070000d05140c40b051082540d8800125005030803141000244d030364030201d031039440741015888062181c3c4003244001036960306401c8980030301c40c0c044895070303d10320141682d04070b5032181c03207026a21070040110084003400b81005e0010319002d5a000120282e4139111f890980c1d0042d41c0d155024141709041000b00001d8111703003156031409103000e454100f841000030399030700790f02d02000d4440b002c100002000f035a100c0d000704440c3d1843c80d1082d512402c2c84004001c00001c00c0c000c61280c13056410010800c14420b80d50b01c3d207d00702e0014030704e1488041000000b00200080e00041c240d01801001003240200c540321a40101800407101c0039030540424018410304000d185d02e10101c0c10312000300720320ba80c0001680d4110340c0490b010306003a83c83c950b0540040c80303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 258872949 1250 258871699 258871729
    0x207030605071718030726130302010813051009050a0c06090f1e0b160f0506100e09070e0c040306110405120120130306090c05030c0627 60
    0x801c05041000c4682d000c0b8610510403028054002951070b10301d0b001103c19034903070072121903501c00d101403004550405100c0c0008204d1003031050800362500c01300c022a074025001500c0040900c0d50410031540c2c46a06240c0c03148a05200e00342802c034680c0d40c0798451b45ca207000c41c12556200d144640070312000b4842e01400a5000d07013609409582d5000c081c00c03180c0244200301503c0641600001e000240c0b20010210007007400c013520420b824a01401096080000314108610000103000c00040f000c0304491501c07801180280920314254014207116000c0d608048050062035061000031440041e01005494940e030b550341007aa6800414082c500865001030a05820311816003c00e9003144002c1050341c0c419903c0350a40c03000c040b140c2e4240c540004885074140300ca6070003055241841005005403440b04600310407410303a251111020b490420030203450764242e81c07104104500d010009140c5002e810380380c1c103003000c01d000702030702100c410029079080e24111f003c05000305640d20000c15441c81 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 258874199 1250 258872949 258872951
    0x1905210f09010b01051908070512091f0204080601050409060b1309060506010309020907140f0d0608010e01050402030703080310031e020405063115061106060103020906030a02090102070306 83
    0x224100c003000c0010201500c0c2015994640700300b0f2a01548901c0885114015040110180515005007190f031104018501ca08010042c4005100884501c00050290340707044001c0010030030103c071004005420081c90b0316402e1040204100c070300c1c00450101e04448049800007007080341d40c10404040d0030002c00882e4000b4220800781e020010640c081c0c4510341c016142007203207640b902e00560458510441c060344c04104c150002d0345051103017005980c180400440d031400c20204c80c28880b5030750401c450807945562940404e0180708001d119041811120500a100740e00302a008280c98529a0101400c070a40c0000001c0d40c038049014201c005540c4440b8000e018001001408851442c05408a20850504000c640b1518080c0140e8210041031700c3d07140043d4980c48250403032505200d0309070000381e486600c00d44928514191803001805940c8800706150000c0d4555424410010310103414184140020000ca40f03e450650740e008041b210b006a1752a0580011703490604c465000800c55 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 258875449 1250 258874199 258874201
    0x4060c050c12090301022a010507091d0603100507020a0b0915060120030307210b150901020106050d0c06020d090e01030206090d0f08092704020d0309031a150402190521 74
    0x443e501c86030f090400c425440007002700b6120884104d07441c1c00c0602c10f440320352070402c9030138150f0080820440e40020006088603041d0000c401008143e070001c46991015800840c028400d11047c2100706500c140e1b03820103842c8070342d900080100307180e06c054801410007980200482070000700c408850700103140a003c403038903803034490720081c61054000001c4072807809900800d61010140d004140040200800035030901c81c44843d001116041080400d04664a845002402d612661400c01d03015010321185a0000d090000191401001854650401200050402040861110a070f0649604403462a40c2e01c10410000b44280940003001d007450f1821801013041000040c02840d10030070654040c0e1908049100e0440418014140511000000d00000c0e00529016200391151b6100b810000b0510b91243c444464100d040b88481008821020502c00881c008050251403008111410b42c030700803210301c8586200b1280c245c80e200703010f80800c9241d000031480c14441c52000d082d644808003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 258876699 1250 258875449 258875497
    0x9020607151b110a03030c0e0405010306020a1707020c06031b0a0c02040b0a030c14150c0309040b0d030e040509031b070509090703030516051f0504060c050c1209030102 74
    0x3480440c1080c0b00c18141001507030380090152481000c44282c210160a14200030740b02a07019180201e44c00041002100c4000002e43e101d1007014041c60046600584030305007804060304400040401010486928040006495002400d0440f40310180d03802d64494a17500411840700408074140c121908001c00d02404890b80264410500c1e130003100c00b0301c540700d040f905103c40d08009020192201585000500c40780c0d445000600700c08a01400740c1180010304c41e880b13003940e00001118019508006010740b071524250103000c440c0c400450b0b640413456543d6134040d0003d202c060609004a0300ca0380000c039001e0050040c3c4100c5100d41400340c00100c0340c802c00588403110390160300e11030b010300c2c2d0214166841c0010b550782565410303106c10f45040500b04c28640e8055009004032818030a0215200380b8004103150401c0151045401040781c0c10186845003d0f9070030680202c00b0000c050100000c016400940c10758110585c05031399a650305103030042070180c407406000c010b94500c01401c0883c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 258877949 1250 258876699 258876701
    0xf060204060809070905150441160503040210030b120307060608030405030a0212070f090207050105130b070c050703050d0807020d0305040f0209090a0609110a1e090902060715 77
    0x200ca403142d00150b0b508240c45880003030440f1004c1c0e52601268880314440041d60605e0340c41000000c2ca44060381d513441846c070450000da19803c00309c00100100c0c00c042c1e90340001c0703010f000b1600100080414035809101d001e000b86640401000a4840c0328034044e04074190b80260b00058264202411841c048442d07040c60756582e5004082c01c5680500c0c0c0b1400040f500d0010055a0580d41c0c02409000400d103181c08015064131030b01035041c810300600600213071448400c003070a802000c00e101c025031200d4403800d2860071108010070b4501003607000030071280060f060032a032660229090401017040c0720181810b0707103071100541004100784100304401d2800c9402421092244205500319500b428032007104409551003628020301c650303982d0a01c00010f280103440658851006001c0b50102c0c0c0e0180c03500d17401d4400500c01521481c007018881c41c03140c2004000340001e44480c0d888481ca07440807120750706015070ba9103e220042c541d210054411503988000b2a000e0503044084800c145812841e410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 258879199 1250 258877949 258877951
    0x18070e0117030316081e093a050c10020c0115050a061e03020c190219141203071704061e020615120a030302091c0213090f0602040608 59
    0xe5804100301c1010040d160000084078810f2038242035003031154000000c00e9884030f2001d4600486510401e440740700d80f42c00c0c11403079440340303040301d004003250f09909414001c0000000b0390b420b802000c00301c0444282550b80105148001c0d5403030304943c0e030161000f203d414141030b0644046002d00014800b03502040c1500418014011115600c040b15a00c20411a2002e054031509002c28040e00001701e0002008112084d540c040c1e05016150403c0380b02d8180c1083c1062011001042c6a444101c0c02d6040020680766a2514101110009420900d9a005504409071080d20604007808241d0880c80300784150340c5455401095184424100d0800c03040e01e40203801443c0006480c1c0c40d42c00c1f1018504010035242140f9a005001c06486e5409000b10800a0100841d045044a0594103003000c0400c1480e84c510b000f07a40050b180c0e5011000c100134000011000340010040f9440c030000b6a441b0095440211002d000000d032011262500300500420550080c00d414804200007410b550012469 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 258880449 1250 258879199 258879209
    0x21c0902040609180b0403050403020927061026070e0405060f06060d02071a0a02070b0108070602070b0a030b04050a06030b0609190b0312071a0709140918070e01 71
    0xe005043d212500c90040700c4040c00c03441101c00c03843c580680842c6600c4240e80d0060700a2515900d410b49175000b184242c00103445031032403e40b01c2403001d104803085c0041d00179444a41d40180400b1704004801d510701e243c0034080d070706d0003034580510b130f0f803502c121f044104285006040c01e07150f12a80c0c4e14100c900c0c03501c08460035902801100700048505918100d20340c40389000808141c144034011102310000d40180504030b581d174401d40e491070816800c030141d00c1d20600c042d003400740c0c1d070703079224a017410340e00c201a0f0105145da401001d0a012550300421782c0d0040c0c804080c01140c81e032054890440c0940032410215421504c0c0a06215075045141c20180940c0c0c0554001c0181e0303103501040c05100c4034200c40f84005008681000e100750f000540188100901c02021a0609169812240e10a0380420380458009a04607070109040c140340d01c4031076000886082c80b1000f58540f100076a424008482240d02c920321507800290f0508450f031040d41200c03040c00407140025200c182002d0044c1c820700070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 258881699 1250 258880449 258880451
    0x50702011202070215030c0d05090d110703080405010804032d1b03080f0703061a03060103050903070c06050d020d022d16060504060902030609070f170c010e0103021c090204 76
    0x88040007507124000c5803c8603901400381a01c80824402c030848907000a8132282d1030040400c101d80303100700b5a0142e90b0103450044041c0c01c561347c00c00c20217007500e51300d40906001500000020404a2007042c180c0741103d5007801c0480e410390741d625048072488402c04982e00f006040a2410b04141c0100304070a0782540e0300d45401082003072072501019074040aa00c01030001e50070b000002c2106003225411a00202d51381408541c0c0c607140c40740428032b210502030020101e100481003081ca0b6034540980d03074108541d04051032a0a6480e2114160603803036000d180d09001001500c50502c4c0c05560440d031030403400c08021902c49042080200c0b160707000f200e07044682103140c18000125a0342d4000c8032544d20340d0050560410350f4580d1403102a020042040d030301c2555840031500076882c203000d6141700301946000741c200d260820b40440022242c0c1d4000201108184030081c030b04040002e504a0901803d007444c204010142004074040e00c104500348418904040400211001700e802c04404203200f210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 258882949 1250 258881699 258881717
    0x38160c06090614092b06050f1503060c070c150f0306081605190b0f0309070806042d060609060f17030703180b070b0a150e0c0903070801050705070201 66
    0x859101c4080c0c0151800f0304030803c035140085c44d1614020010b010341d40001d11019500154004401c07010f000c0c290b0301c032511007041240c041e410f400c0d581e502c54220940340a0000d01d034408a5520f2400415081c000c40000503071000f80000001610300a00b1510820412a5610a0018001e03401e0701401d001107410000041196100070808a15004c3d01102d1100d0092070141042800d1180000104511025410218003041004014400c0035070020342142d880c104440400e1401c000c652010384a90860002c0c0000580c0a41d070080142c60980c443d42603403c00e21524601000c2c1c2d24500034002440c18800140c0b108051300079400320364120300c1030101c155a4041d010100180743c4440082500f0400900300024000e900d85400704a13034440e41c450303e07615450315000d25840074200f44d911107410700401103240340d07900034a1400440124bc9451041c034264840c10b800d50302801c0070707400d00804540101681c40c100900001850568001e1005050841015080e0b9000703400681c0001c2c8010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 258884199 1250 258882949 258882959
    0x17030c0901171504020a030b04022206020120030c091e0411030405061b070c030602030114010e030a030e030c060d05010509070503041a0c0d0f060e0138160c0609 71
    0x4070300354801c054014280942c10304403c1084000d600c00026842450f90300c0032050400d07211413000d400c04030103c44011203115030022003440123100075417100b411a81403503c0c0c0a0034a100304c1c07100b00f50014582000e1f4803600e410122003124069048081e40040f02030101d52440584440c8401032110250740411109400000007504c0788002c03100506503500901c00f04a01c00000441c601111601e1707020181405507540d90510320b01460345c0181c8000b17030080010f02c005000b0300d114a2402c80b003400c01060300341442c00800d4550f0259240a01405007022104010b0784080c4960300e03c03074200500d0741c5d545004030904600180b03001c2c000e13580150490307030001c3d81d01800784084134000c6800c40c0c40b444007000100483d00e249100108840303001181400401c03000070b451700843c04003840d500c0000c41d01a0030440d9641c8042c80592010000c201c404050401c2c0541000b544490031000340b541c10101c0300c419003180c18034407030760104000d032141c0030b4442014040c81000010a0720041d580e5024099554 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 258885449 1250 258884199 258884237
    0x10602030a14030601110f060405101e05040201030612230d120509070e0f090d02010b0f0103020906071403120903042303120d09112b17030c0901 64
    0x442070000030481d695940c506200480d80a19445541403400d50400f0a60701102ca00f0003030680d00300c0c050381d40048284800c219003402040400e0549060070000200ca0a0081050729410040001d8950740c070b401040079a4401c1c6c1100024001d40701303210220703600700e02d0200400030501c0b070440d80f50030348610107003024840881d40b100c082240342d039502003420791050244014200903004103058412154001100c8020720311562091035a204030301d5851802003042030400b030030b41000300116490120314038440e43d10700411403d004001c0c0380c010b0b00e40392039501040e03a6124a440260112415005903100c1400020040c44800f03002840e8447c15180c035082180e82c0e00443c0a04403c05c209401d40b040340000304640518000c0c2d0007411901d14480c00d51038014a9403140810003080b42d20f404840b418402c07000e908454a003015212400780074a1980042c035695100c000360601e40c0b03a5100c4010a110f4180c60078160400591481036903814804203404c0943d12524905020545500310b14580008c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 258886699 1250 258885449 258885457
    0x70501090f0506040e09070909030903030f090b0301150905040f050702280303020d0b04090b070f0507050d080c0708030a140105030c090103060c05041a030604060e0907030f02011103070309090501060203 89
    0x40d20013401c06040c0884910b04182c002d01007282c80c42940300014030748005020f103140c050301a440701c2d4040c40c2141070062204040c212101c040c0400003004120001d444400c80b81107400d1650084c80481506008036510071165025561103400c1100c0703990aa803041c1e01650181c001030302200c0340122800d002004402c0102a640bc060350001c01101c00b01e802600240f0072965020380008170541c544000604032140240f0a03031b089007000d410405070030307040140f04e040c8980904201381005010f035545c564403529201c2c030708200407543d00452452084402034035100c80d441090a07840303243c09204032004260341e01c541044c3c040d02000001c0c450030302254500681c500602900441c6c0e09546a0a01401e80d2500500c10068104800105208000e10444240300711044180d502d0400c04204000c0d14980e42250006034254814070400e0700000600c10116a1b01c6080401c030200c0d40d000503502c0380c081003d151402c1c0000070b042002c05902190210544034280010811640c851070100d0780c0e402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 258887949 1250 258886699 258886709
    0x501080115061704081c0b01080702011811030a1202100c090503210c0a05010614010e030a030e150a0f09080303070c0602070204110403050d021b0f0d030e0301020c070501090f 77
    0xb40b28070201003166000d2400d5038014012480d16103440e51b80c00348080d041800707041001300c0d03950320025102c0310340e40040240c0c2c102c030140c0300078000c11140109005440d003d981c0c00402c042e041100110743d45c3c80900084000c3e9822095100122054950194039030341401b620f580c0451800d41103011700c601070070b14a402d850000e4000d060703658a01420454003140c503681501030480901c008880c0d03420030030001840324400c0d8004100c952409003042605c8042c0c1e03004505000307a02070703810456100003611491040d01881c02886138980c03000030890a0703880021080207138600041140707401e070304070300c4000c598059a80e40740700e072542da05105a203e01081c1c0d0004001224100420003151031a000f80c420075000400000d890790384080155904d6110fa0701c1100c40b5080742c02d00070807a03901402200b18240d45203200b0035000c020740d40050805000144501d2007030701901404070a05110780b030343c0044640090000c40d40d40001c02c500f00c0c0d1350301e190310a04e400540d0340e0401051402103604c00e44200c031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 258889199 1250 258887949 258887957
    0x109050c1315110f0d090b07020607031b02060711010f020604110d060213060c170909070f110718060807050303070f0512030f01031a0f04030509012001050108011506 73
    0xd800d10081101e82c1c1c0d840820101044180c9020300c0b0156420701105118480d148024094a032409401034014403165001003503051003803100402589900088907451945403600105e900120703601040424030000c000703034000b10003240300010008403468419a0010980703031100d800c40c911400f240d03941011035005082c241e6005c160185c40c18010400c0041318812600541402140e41d80360300e40008075805940000c401c1003105c3d040c0000c6810703400f20881195601864041c00341c0114844000261044e410050283d00e801c951a2168880c008448500303420b441340325503a00801c19001c0300312100079000f5850700100103a50000000c000d8201d8802030091810007010342c8078800c198556843c01da681d40280034203029403c664400441c0705111940c80310219506508001244482607040100054584010311901035181459941d0096062070301d00c2d81c2c0e070881d40040b43c051240c40c000b44c66410031a918003c01c00700c190481c80c1600d164070020891301c1d0403a00141840441c07486520003103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 258890449 1250 258889199 258889237
    0x507170604030e0306361005060103060503150103020105090d0206190f2d050c0d080702100b13090501110403140609010b010f03050c040b0309010903091a12130602030408030109050c 80
    0x4410701942c10241c01c6c4500100031900c01c0041a69805c20804a00e00041c6039914403c0202540e01842408042c200540c0240031001850184014451341800042d040c490f01042c1d40791203948161082d100c440d070242c051034031620350b2411400a44d0503480d07d0408102c450310544105403050040c0015440d0040e2255481c1c1d83d0fa540591074833441c03090032403c11104004200c510380301000307203003901442e5544850f07491a01c00d00081c201044103a00c082180e040055050b034560710814146503200c1900303800207128801d841c00c2c0c0c0c0100b00c11111f110390454041800014056011541c0384103581480c10fa502590b81c4889240c03c9070001d4400303601081c989010303989080d200394041070b4071408070b8590510b480d03181c01c241c11b007a400c1141c21400c075079140c504100415030300201c10001030900412070b000e03417107030181120540e001701001440d96110180028003401c41d85109040640d4220300219580d0405040c0200194001d01400150710b0400c80800d039032042402c110348024400c11302d11894 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 258891699 1250 258890449 258890491
    0x1518101407080a15030314090301060608040c0b04141c060507030603061508030a120212010b071b15030f02040506030708092802060702030f1f060b0301051302070507170604030e0306 80
    0x210400741c7d1038055844400740306615068600f44500406840c9907240d81c1d805140903e440b04180855402c405d401040a200400828040b40809007403420308842e00203402c0d0914008040083c1b140741b000d0510350401c02072051054044d400724041d20301800051040310145001d03842841c065105e036451540c41000550035151013071800402c20035984070050706d0250070581d01851740c2401e0b0400000381400080c18000c000c0d03442c200200a00c514540002000d10f08141610300600132002017003810780b680f104101500b90385e411034014000061a01f40c40342000d100040124004036007051541c0301c4d506040d140c2c055082c1c800005c0844000784003d1140da01d50a000c1583c2004904903007522a00520b458204400c1c070240900d0381400d48605203541d11048248285d51742c2d0384c0010b0312801308100520030341d11402c0c0312041e850780c650005607036003e50f403034000d16090141e2303c401c081403162800b5080d1800041410b074081d1340250398068105902904040d00c078201035444000c0021020303080340c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 258892949 1250 258891699 258891707
    0x3010b0a0b090d080d020301150809062d01090b03010c02190321020309011b17010302190506040f03060c030b1807020f010e06040c06021518101407080a150303 70
    0x34420b08090155120858681c0d9122081e4200c03d850005168001c0018042c200345940f85154040c007170f00e8001010300b00b803040c290316000040d00e8280000b01030000c00000c00b94201c03010010b00c00d102ea60709581d6940b0440500140111a4814803a5003007a4500003c2c510018100c5600b000c0c1003a6a0954691958140c0d00c0380c2ea403895031a0720011090004007100301d944069840b80c45010004681c41c3d100342c0c842d03171044144418040910181c03030003084103030751150001030542c1d9040d6554180c2e510001c1b6058041c9000381e1150340d00c05030018010421058202c140390480e03200d070009000c00b1414402c10707001e035240454010f03000f00c001800d003e22011040c400607000002c900545402000201d14a420341c1c030b10f2807600b4000d51058052004001c09035117405c004200a201600c101d00001038010071921014010902d0491511501345031000140000c01c2c180301d00e01420000242c1121405809803421a50640401c1780c020028000c0d419070700502c885142c00c00d40c2106100c0c00d581c0c06413 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 258894199 1250 258892949 258892957
    0x40f060804050106050a14090609090a030c05030c01110a110606010509040902040e07060509090603010203040519030e030601030605040b0702010605010906030908040902041d0901020703090e0903070605010306051503010b0a0b 99
    0x20b1525034070307014000365503240d892100c0064140d09480e0580110200c00b40042c040018003401c0c00740810208000c1040c00100d003c1c5141c0d0b074940b40c403a11180d207030f0515500d9070080c6095180c05518102248a0200306000148035251194649450304804048510784400c400c54005010600c100602c03c1d00d0714156014901c2c480c0b000304001010740e4490007451820300660000c1d004901c0001d135409481c03402e2100d1540c0010101c0096295241c2030761141d13201c0c5180c40340c1980645021400004041c041c07810b00f0082c802c040c00301c0c1c03000d40e036900b031078405480f00750750643e801501080421001841801200240c40c0c068441c050043c3c0b50400c00c500515402500380c550500c14040458400410f00003000140400c0030341c0070039004669602010b440002d010103680b41e10400c41c0d40d000a401c040780108584e11512441190303911083c40600318800c0701d0f401001c05240000100c02c209169002d81d019013000030180003200b200c0c6050500b210310035071501d83d0202404e2130421441001c14018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 258895449 1250 258894199 258894203
    0x108070201090c140111010b310c02060f0906100501211a030d0215150111060a0c030b10050d050c07050304030c03030f0507081801030b0d0605060f06040f060804 71
    0x41c900e400c9480b03034500c440e604e4000f441100000081382d03d0541c2c0c40703800e901c0f0b500307107402c02041020045070004103644142c0c40c00086211a0302c456041081c000d5880c409807540e00ca000b800500a210002900c81c80d007142ea80c86042258404111a5480026020b2140359030840300d40d0098109001524101d04e40c0d808151107d4601039100f010041500a07041c0c07016001d00a9201440240d041504144044640c02e00b15842100b880140c0d10041c445281c001c4201300c1030f03240c3d5120b9a0012521103d002149a41c01d20600341444400030403130f440340d0710345502c0e5a000c0040014901c104950f40880402c5a40007078002d021260042c0e41c10b501154110040080507450611555211400c5800030340c000d845d0304c85c0038101041455000340142c0200440c616000d40381c030080e503460720390078055040c0700400088411030050f00c5034040e0b400072030203904c010035041e20014103240510140c402200c0203400f400c410f180055003407d0a0301950309403800300100050350360a02004690a650040c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 258896699 1250 258895449 258895451
    0x1703180307090905030c070e07020303070c050102160f0b01060302090112181b08060c1303030804020d020616021e030a1b120305030916060e1003020702090907030203100b010c020108070201 83
    0x500060743e20901209a2103036001d961900c4106441a01342801d80c0e0000794240096400c01c42c200754081700300e9074858080e0821000290b41401d0a5009000340c0701c2c4413070700050031110754040c4107a0301e0f4140407041c0304100140c55a03803101d1045080c0d00030703202014049525101d003c030f94080a500411001e81c1917900740402e08489845040010b0515018492b0000c800c0c1001d011000040c8083c0b68804911030600e86040b07600c11102c1c40281540c4000307020001428081411980d4295080429030380003000d45440324000311011980d9200114120b101d41c10101c0c450402c004003c0c108088070000801a100010030350700e0b441a880d1408001030a6140310580c0800c6e04400a540c41120030300950300c1c0da40b0b910304003104510f4080d00c180001e4811403014401c2100310f51140b0281725800301138550282e2805601000e0300070f0f00030804d0080d03201d200b8404001d850000003034410101c2c0d0084044076401c3c04151140422180402043e90000c4d07482c0002c2e9015501402c0569000b049600c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 258897949 1250 258896699 258896713
    0xc021e010f140c031204020109090605011e170103060605010215060901030b070c0b0a0b0a0b1306030b0d020d050c10230a0c060c020a020906010216090b1c030504030c17031803 77
    0x40c40c80c110f500c821148140b20082c078003800f0955900c0403e09d00a0241810100902c509000000e007030104035054070044900c05030561121248100c04045000c684a032145416503181d00c1d042001c0e088501545006102c0c1740d03450980c80d01801a1b944c021007002c0d2000f103045e425515420001c203c004e007c1c206021100315620300095568445600c03892500100140d07050b220402c2002c0c20503990301c8640c680c0030501030702d080d0201c01c1402004686550400190700ca40e82008500800c1110401039401440d040c0d106007403000200d0400f400e45812a62011043d007100ca00740c85005020140c07043d00c110507030076410074140c07000090048041d10304029009052035500ca00541e458541e020006070072455441085050415010b500b0480900150a00b501590b65580300c0c0c486074841e5544481d2145040f0f6600d450b4800034003404400c41d1081060000e06080241465015120803950310442000000b80743c0c8001ea40600781c140c000c000380d03240c941c2070b0b00c00100344541541e0056060096070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 258899199 1250 258897949 258897967
    0x80403050d11010b2d030f030c0a11010810140301090816030e010305130b22051b011704020402030709080f0c010809071a07080f0a0c021e010f14 64
    0x411410000400e90b03540e48500001c04600382980c10005005000d05000c00701601c01c00c045205070080131400e48060f440540007540001d1074540185812a01800006204105080045050304409005181e09041503031420011075170203604440181c03440c9a5424203001c501240908000b0358400100085802c0804d41c847d070700305500c801d40c1d07140d04042401c0d01404145c0c10000c15185c880c000d0034100280d240800c01c116408114030401081c8104640028900080c402c01000b030503401c03109003100308141751510581c0c446c010608020751040300403800402d0740c8601160744d00f9201c0300540158075101c650901002c0e41002e402441031150240020618600c01c04c81121001c09a01c0207240c4003502d100007410643e400b80111415412501d410701045000300c0c1e143c0b10001c003e070400369454035142080545400b0340384220620740790000c1d4200c0341d140c4c000100c80b00785000b10f9103910b60101242520508802c4404c071035001c102d05007908600540288034a58070f10340044c840c285480d02c2170b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 258900449 1250 258899199 258899203
    0xf170301260a0b0c0f160812180a030807020c120102130f051e130509010c26011721070c0509010807030813050306071211120a0908040305 61
    0xd0700080c0800602412120300c0d1008220307800d07100c90940c0080c2503165015101d012440030018100c0b216020009140050f00e114001202d46402c1b000c0300148100c441c620780500c03103078081280b41c650a00603801281405000c50b0840041074242c10003406091110703603081e02d24060091604d4194054100c805000b40ca50011852135091040c00059440308181d03483d0310045810340040320103001300641840103407603030001c030800da030a01e1641e0390001d2a5a4005070700e00c0030f601000350741682071109100d6000015003011700f08220740e448001d00e00000d0068003254141e020804500030780c048004110300350650400b080064004c40a03a4443e00b0007905031040c2c0c403034a40026041810005004092060b421040340203040101c503144615450400856610f110f80c2c08050720020000820401da22100040207008000240030703252507143c068009040040810103200201d0300b4240c074a48441c1e070a908968040e4094003e0503903d4039100c00d4031004100b0500f04482021003004040003241007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 258901699 1250 258900449 258900451
    0xb010e01150e18040318120305120a090f080c060c03040201051806090402071a0610080106050904090c090c080a060609060c05030c0106080304080c0306010e040f050a0210030e010b120a0f1703 84
    0x2e600e071600200003082c80390302c440c100e960004401c00c410800420000354000201c0310500440f030b89080c0304bd214107141c3c100800c07403010700070506841c001c0720030304020541c3d018002081460081d202c00b17990344100c4442610040b140280060320070040310503100100c0350f98041e9848040c01c0d86040660030740200b812039008550641d54503011381e500082e611a180c2e0603643c040c400740c038140071900c13809101034250074041c0984400c0c040003240740300e110303151544422210f5400090796513040f80d40c2c102c210020240003420300005440f2600141000c4124040c0d181110010760300d88845d54a843c0048541550604044a0a0004000c51800080d0034000c01001d880410051a99146081001071500714120492402500040300400c0300c070306007200081d4815004100070946120302d01d003c90418148241c02540640300381800061580c5c10351181f901d040340900208544108078080140c0f26600d9642014203074404a141c40001b0100010303a04a030744500d81003103c540400c0590012a00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 258902949 1250 258901699 258901703
    0x100513021305060406080f150301090c06021009120f02030c0f06010611010c0e04020703030f150f09021c15360e1b01020a080409090b010e01150e1804 66
    0xd00800d0070422079469010900081904664092916142803070140040318001c0102d0f80401800c00000c00140c80c11584804031040100208001c204514151206c90258012180107100b584040c0a00444034031400c06010b400241c843c41000c0e14103801c58480c0c0c0840707500c4003180002c0c0801c1a00d044104031316000702034058080c0c200781d810508001d0050f21101c1c0140b00d9681000c61030b81d0300c2d03a0404401c032444041500c0150707640d203940c20b040c0c003d4031440850314405850491103441c450100e00d145c106403030054110001c0d450f0756610b00c5060307018202c04140c180f10480b1030b450070300247d030340310300f00b180d1003100c40307101c1e0b2a40c42c407547c45400c2801c5945241c01c9640b2036505801d01c441007002680c25480c43c0c04000e5400e101c1c2c55a696040d402070740c0c0f0421b5002c80703404521607000700504504150f01440c1c840c0d5454a480c5c40c01c1c042c00d8a004110b641c54110000800d0342860210100c0c107031400b00b03000c04bc021b682c0c20340490f8824820883d80d60070184900c040070140d00f4100001d03104034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 258904199 1250 258902949 258902951
    0x142b0203070b0103062f0406030917030a150503070308221203090e100303081b1918050906010215060604120303050609070f0509060d0b030105131a040308040803100513 74
    0x6d034460410035100c288454112803028111100000686103041500c1c141e86080c540020304450516103406e8411044005d640c0d000000b00c200f00746a540d907081110f91032480300c00512403da54100341030b80c80e0003500000788003e50602903081008042c2015940d118030340000f0302d010550b10003034142c0d111041070081d4001080d2000a001940b8618100da422510b0740c1000c20b8200c3c51078800a24441c2c0107862801c0d99641c00b140b52071041810740544e50080c0380076905940b01d82c1d070703e10007900c4406070402903000b660194100140f41d103854003041d849140c040e0081c4c100038078100020408000010b04442d4010030503c00402e513884103562074003489100c4d440020340d50801c6006c02030b4a00d40201703400100410a400003e00c5944038080c2c0351500d400b654400e40b2110300b0600d0303601600022040c144c0540c640010011041c0c0c0810f40c80e0481070141d420100c030722403641241869640102c0d405000321780003c0c04203000400700c1000b15403011007080d03401c1119442d00c000a042403da6a18040b181e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 258905449 1250 258904199 258904211
    0xd0207080c01110310030602030417181512070804050106090c03020a1101050705040b0c100c0801032d02010c05010b0d0c0f081b010f1107060c142b0203070b010306 72
    0x1c0d00248540b07500c180c210220241546010a40100f004c0b80f0740c000213046503004800300d070411244015090b40000c04042880e02d0708180e4015220a042401c0401c0c410280c00b0240d129a003403010855401d0154003110000580e510801582c036810090b0045034207650b240c07400141c0000718402c841e800e842a0340d016940340c1b000c080040c810207a452025900c0c1c0d1400c0203002030a80c11402301c0e000c4030001c80e902a00d03801a409902c0c2024a08e03101c0d010702609010410a41a03071011030340e070580b803254040081c50541401000d00303441414402d0b44c01d46600700b86590141d80102084070803030344144c0010407030064080c00318800d100224801c0790b8000c5c0c0b0702c0003440300500c00040800074100b074000a0400c800011aa41070700781c101ea042da418042c0b000701a002080c8546028510b00c4000c0d03045900050340c5403070003004c0e00c06500c02981c1c0d031003071001a05242d40001ca0312032071010a05d901451904000c010a08440405803c02002d6110070001c6000103000402814001c5005d00d07000994 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 258906699 1250 258905449 258905467
    0x7030302090406050613091d03040e0703112b0e370510050901060e01150807090503060a1a0319051506010813020301060e090102031605090607170d020708 68
    0x792081504143d03c2000180045c1ca644081100d40d201164070b20036000c6115140345c40d041602d0300c8e614100750380713a00000070701042411503645002e008030b1310b9603407c0010400208011480340117000319520003594034a1000c2c203050801c4c007c10380420160000107590059245c046142c588a21042080c881c0581074040c083c04504074145107660741c90103031020b14030490b40d4081e15042c1545650088035962404140c05040c2507210708080d0400144020143d6194402d0905400c0081c500700d000071900300c002107c00784640850000c40c0d401030020300003511510245030142000e1000100b41003e0086203403400c1e5408c004910b4061b99484507840041418100203050500c1013200858440e00c20b0288000781e40d20803109030f405110701d041e0400383c20300d40c80068058940d50340302c1c03141c010060007400040d0038103500071070084400c0ca1444401621400c000e80b40ca002e0030f02010341c803480901804010400e20090342c03044512903003002e4035004040c407940c0c007203030803044095a45000205030010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 258907949 1250 258906699 258906701
    0xa030c020d082a070c0b1c020a0c030e03161202030f01020a1e02030f0406080f0601030908250503280c080405040903020c042a031802091b070303020904 67
    0x2040c0c1c14901d01841c0b540f4112100307851002e2680540c0f1400a0401c110200c1d0001d9642681c402c20350115103030110a5a0369560707072541d0041c501040315070700c0e00701c20403940b52914800c60b4000a416100d1030b4007014641c40641c2c400030160b041903054090a150196550110304440c8042e02030441000700717145250050502c0e0a028002011640e1b104204003d010384c0c02c0180103402592010741c8802000e4002401c0381140030740c2e0490300c0001c60118010070070913040300941e071092004010428250740d504004405030368555502505015042024888103045540581002d410543c0d0403101d40005549003840c59001c28080d05100740e600f154903007200240103600512803950b282c41d80b540c01c1d0a4442152501c42c5100d8244030ba541d5401050401d802805140c424410041040004404a050f1010020007581001001c11141070740108000e02074442d40103c040c90b0b036903102524007a5401c1c031003100030140c424907041100d45a40d0340c0859000c00105030280c42a40d002d6111001842844 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 258909199 1250 258907949 258907963
    0xa06020c101a0f0109030b090c040c030b2404030b01030b090d080c040b13050306100303080703020a050d0b04140c0d0507080402011707030b06040608010503060109050613020a030b060a030c02 84
    0x401050422088203007000c100b4101c40d04240003254501c10b6081400016a42a80345e903100a0030200b02d2801c210342c443c00800c41000201c8159401e10407001ca0000c200c080350029002c0552204101d0003100005003030f0610700d0415400c0b103410030b203010f0311f075152500e0000090b4000c848074180c0b501000b40105c410710013204415801d0030450f4846c2028000a14640114015210b01c10780c0419034040c1c1d0340c42c1103802c50043c80081c0681311a400c0c1019407522200280c0002e90128052801040340c003071007807080303d0482c502580c076141420031901911000d400d0b02c400399a400303601c0300d85012904050000e41c5000703d00e00e00c1401c0e030701c0310180f0f440030640710024034020500203c0420400940d80040f0b588000303032045401c02e10a6034407098168010308403901801d40006000c100810100d801201b0036058400803800c0f14107a80c0d8500c0400c0640e00200da01c280c10048542a410f40d55045070040c00d526001400c0c0403d0070030f19080441e1094106082000000b41c85801249941e60103100356 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 258910449 1250 258909199 258909223
    0x5041b0309050709020426030f070b150a03050c0102010501170a020d020a0503060f0414070b0a112803090f06050702120111030c0301051e0a1202060d02030c03190c0c03080a0e0a06020c 81
    0x255003041c82070b11081d100f034051844083c01c62403d08000034000314824074000b80024004255225154403408d2582c2d6801d000c0d436060740990702c2e02c0c0000c07130154510043c58005d49000c90091074080056800e01180790b4001108a800582ea242c0102d020307034050089500c541c07181884005945418140110058940c00c8030a04680001d801480078481400480d810300c031490030014002103146d0381682c42d1108448024110380c0c071004c1c1d40c00c41c0c440740030b240662250127503a0305c00341c003521603224804c5c8440b10320590300030a000300494801428446000c601300742c4000000904100c2e2000c11a1081d4011500c4580080002006106a2524016440b40c0001540d01d50840c61010b03400305d003410701c180c010170b641e2800002c82c4008658802049401c1000f0640056480781440b00e09114507400940b0202c4c3c00d2140c00c8800741c2c016101d403282600d0241346541e404409583c5860956041030040e280320181d64036003108603904041041710344070180c802d82d801680c49421f100c0c441d042900c60650 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 258911699 1250 258910449 258910453
    0x20301060804110d0f03030b180c0d11041707090f290a03060906050106090602030705030d02090d12090312110a02100c021201051005041b0309050709020426 69
    0x10301515520804866020303512440000000c055240092140d08452400034122005401c1c02e0040540c1a0090301c00428269098458041300100c507810020080316180641c15041c02028920242170b04072101d880510520140f616465001c855100d40d034000b001d001c5548030890402c11402c07244903071410908819030420421010301c902c40642e580c00b03450902c9410008001910b0303640c5d0352025030001c0d43c2c8a042040b04113401d1603d4030207050f0900c10100860009540000c001e030010003241c212540c000099441d1200c80c1d21a10f000b500a52440c3d6080f5584001c110009802125021002c1089498a00c2d00030b00d14501000852800c04070842001811004641000fa0004910050341d034100d800c000b006185039070498605045100c080d40c0300205101d15510900190320060003002c02c80f4850070904d4407542400706880c00559410909061002d04148d41480703035002c900c00c90300c80c0301611041560358581f402a40c0154000000c20343c4c0c00081c0790050310500d000040b03d01d0780000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 258912949 1250 258911699 258911701
    0x106021c0302160201030b01031806050103120503090316060b090a091103070503100e0a0c030b0f06030d050403020d032d03060504090807030f11011d1605030606060c0a0c081f0203 79
    0x10409040c943d802414192600001d00b010307802038014015042600b841800000c541e42002d0010701401e10090b24501404528002c81a1148046030322a03207507400158030b40f148032484040c07590b00c011000e43e10320ba40c817040d1b52000d95038000380b140180b010110125802c0b8890a18840c0d985a49007003512907800400e082010380c4020400c0724400705031040c0040e103411051400c03810600600d00052241c0702001000c41080030011070705009080c0340003041ea8035aa20001d0555410300b0615040225505000410048c0791802420000603ca858500501c20b616640320200036043c9c1624013070b079480541845003055061140c0801400c0c03c58052125407070035158100c062203014000307810000e40c6140b0200d2540541c202030740603038604008001084000350303141c0d84440000c0003101c59000e500580d80d4010f88103043c07482a0b82c402409496140c69180801846500421070700806006041d1280045107880c00300c2002082003c000e040b100c03840c03100c089152081a0744016450348144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 258914199 1250 258912949 258912967
    0xf0403060c17180c01050d0b040204090608070902070804150e030a0305031f121b0b0c030d0b010503060a15030b1c02090c120624160b01080a0213020706140106021c0302 74
    0x45001c13240c1001e081071951410203503200d201900121407201e400034000640000d42e40c00e1a40b20204a0f0400b03030a650703810b0389440002d001d0344a541e9024101d8603003030109201d424040d69558a000815090140301051080d010909140141d0740036004505c0c007100700001c030200b205103030b012400712902e1840c020341000c2c0c02041824848801401007114032010078ec640403255015006040081d200c16110300003040d880d03070350354070000c11039203001c0c00c00d441c103040342d4015400d4900805004010489060610660383c0b150b0f007042514804154a4a040311865142c03250340c418040194082000b07402c00303c2c018400345a401504103280d000042080d07120314509100119006101128140e0031540750b001c02150900c1031540092080e600040d0442e1080541090260b8152240c40040031603030340c40e21010348500d0b40c44406500060304a044400286081c2c1c001c09196218250000350001e48180d801e000300e40907005100564402110b944554604035820f16064800b8541503190419030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 258915449 1250 258914199 258914203
    0x606080c0d050a110d050601030b090c09160e0a0f030503030406061706040f0507170f10020405060f0d140c0a140a2a06180c0909030e060f0403060c1718 67
    0x82c110181a1640c20900710021750341d6880c42d00b4800c0d40010440e0800d58403030030035503001c0000b601d003140356110f8205851014100704000034440d424103c401a62922184000da620810390400360f40d1002c005040414003074801d00c0c00c0380140d03028400641c4c0340d2400d0315100b800c40d42150050a5294080c00405e10350300c41c00110b4070b070310543c003212045080701d440c5025403030042d01d0740200d003c040b03000c101e21340c10310b8001451880c20030b8840100c420111011030500100d1045000f0540c000c0c0d000c0180e0350400340c0c6c810040250b01024800007075103481c2c010024900600960301c0711900329002411030030b6150311899207040c40e000a00c0cac41c0c1c40d16035850030240a407006250001d00080085c4555000d006841c8508007255402c41c5051250001c010300034002415403610440f074800c491007002c900100342d4462100700c3e50f496110103030001523980800c0000d801a01c824007045c8400c01c408800a81c050050704010000c0751150300c041d0514203254045000010f00d5105842c00841580ca41d903000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 258916699 1250 258915449 258915463
    0xc0106030b0109051b07080f030a02071a040c1a0c0a1a251101020c070311030d05030f07050f04080d0e011220030703021e0405010201060e090c01050a0302160606080c0d05 75
    0xc17600c07665035442a2a00025a0080700041e443c000008410050641c031b6607002030a06500c2142141030701801c1d10310075141148207450181c01002c00100502c00542c4840c0030801144290b44140c6c1000054442145842e00d200011681105490b01d510001901c0c2036840d50000d240615015410301c08140103d803101840c860b030701c100140450a40c8242600798120303628001900c040e510290345a0a01d0404080d11132000c074001c0c861410542c01861003002900e014000301c00c1848a00d8a513014102c86580080f2031440800600300030024004c01d04001c1c00355040107503218440c81c030900d080090b020b04015141c404c0749078100700d00780201c0c1e00130421100c40c80c03000d50340d403d440b41c440c2101140280541500312082c0b20501c4116250010007001074021190264001e003c5552107000305210284241c401240540c480003419426600950251400002c0ca1400506001c01c690551540340101e603029181c039030782c5810510a0480511200c00d001c10161011400e01d40b8030b84d10b007592501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 258917949 1250 258916699 258916741
    0x180503041203090602370212010e0705040b06180a0b0a02011509090210200d02012004050108010b07020d08030c0d06050a050a050409060609091a060405010e061e04020c0106030b010905 81
    0x810040b89100f001c46d0010340800c810380141c20403034982c5007040c0b550700078200207041103054400c40e640010f1350300e05400742d240d9202d4081c0c0341a0402d078442e003d040480e040e030401d181d0701c001c5413200454120074040140112400c66400492100c4000300d26011171050341d080094440c0c00e041900002d608ca03a688030490340217904e0a45000e24092410014060031419004494000c44034510720556054014108801c0b500c10700500c9040203074105403061080b0b1040c2c2d03000c80c0d501e000400045402c2c0018001083c0040c0402c42d41c5100341d13a03127401650046828098024011504e905250340a1040d40003600b4143e075065106801c00001071040400741c45a18400c68907000d070f4404008190300301c00c0040101c000c00340090501c6140000082504031b0b5280780396035032500084c48601d458090541258074003803030509903889240a000c05c143d4206011015001010701e0b04100f03880350710043c00c4205a1800000d0220f04510b0300009200c810b1303228820850078070741400f418420f80700b03900084003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 258919199 1250 258917949 258918013
    0x318150e030106051504061b170325260106120906090f0507051c03050403020609012f0f010510050607170a03140601020a0f0303180503041203090602 66
    0x3110340390009026040a4000681101c442804900850041c0d40504140c600e2502c17058203900301140420a2030311017100140c98241c4024034a426a5105c6006603001502503900602c04c200f0b0b0039040410382404049100000c030911010140f104000341040b10b5007400c40c1c941c0310131b13514010004248400f101e01070304070103688610400c2080700c0c81d840b600690380e205480340d400d4812070030b1854544249106243c06030720100c10019054150300c60340c040080e0300da10381c1800d05040d82c0a0140d10340202000030f060240040c08950552800c00c001c114402070010036103090380c20595410304010b003655003404503a0405051040350404011150b0607a181a1500c2e9100c800609100e460380c5c20231410340010703d0000400030b55040e07058006c41c00700401c41c8400100381e107c000049a4400d030407180502003e00d24602480000c0c0300c0d4000f0690603800595150110b00180c0300c0341e09503407040c2e1200d5101455814540c040540120040000707001c0d0f0b001800084813039140d15600100c8442c0008a12 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 258920449 1250 258919199 258919217
    0x12010f05010908010c0f082215051303051c0905031306110c031c0215130309050d08030a0902220e07060f080708041b08010b030606100504030204020d090618031815 72
    0x10116080d400c148c206103800640d20221544c1441850b1108415072800c085092400040608401c0d4809030580b540c1517440c0380c6041d40c0380007595a001c160480c0b07484065201d80503140841d0080015140c0b0091818140d02800d103000d0001c0d0002c0ca00c0d6001704036a812031145104680d174040342082c80c0040d100142e90308058481d1003242480300b04810150303050034403001d00805000c1038894184492003504c44500d55a262401c00c102c0d6440850000e008010810014244a989803c100c0d101072010306001d0f030f88403650345122803038101d498004960650b82e10300e820034401e0400c1444020216400d05e00e04403a400c0c100107000358002002e08083c0030f402000310f42007107001c481c010540e412071811071442980f5151841d000c1c4c050194001d21a00ca10800f1901e5490082c1c00003030010b1071512458902880d603400d20010307401c46130f0001c0740c490f503800c0c00f40003050050040c822180a01d005a40c14a4110720740030f402c1420302c945400503440c08850a00120108401c2019a07460385c3c1414208 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 258921699 1250 258920449 258920461
    0x50a0b120c060f0c16080d0c080a030b04110d0207020a090902010f0c03020f0615010816210b0a03060905100902010e0922050d0e0102030306030d05070812010f05010908010c0f08 78
    0x1640c401c3d8400350505102d010110501c1d40304003179550307059610900544402100d000d00c12100c40c4051100030b00724030404c101e821070f0381e80a944202a08803000d04041031306800e500714188583c020300d0005845e20340002d581011440e1910200d4003801e003040341000060703a5600000e154181d0071001c801806061901801854005c10541141d011000c04403a40b83c5040c2c103100b40191b4200c0b1400d401310740c55001140e8421904400007018000320b83e210f0101150402c224507122994184202459940f101c5080703054903104580c401560040300d000c0b035509030a20300a45881c082c1441a84110702d4003d0840050fa03002032a6407805c94107d0f0921003a40310000b9074074410203001801901681240d0020341044000b080584001103980c03100c03540100a50016600ca2000b04c80c1541d05401884109608900600280503018040e40e00340c8e00b085d1740070507181d0a01c1400e822985501100410030481588d12048010207403006600901015580c000c000d000c915824980000340048100040c00c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 258922949 1250 258921699 258921727
    0x110303012706260318240c03091f090e06040f020a080403030501050a0b030103060e120c1005010b0711100e0d08071a01080a060203100f060201050a0b120c06 69
    0x1c0c412145480412806a440030300303100900d0300442000000c032042e00c06407140c500200540c0d811007450703c400743da010856010400c14601060741c140148466100fa54031160614003d01414904e15004541d64001c03c01008911011880303209001e0703400a103081c02455005103140c08460f03081b0a100e40c107445242c0054060140d816641644520114800e00803591054550b030280b402074804104903601c0b202400400790b40750141c15000042000100000350700d0ba4003450014011070283ca104074099005e000140c0c1c0400310091003513120748074110a40006104613030050590078052172a140d20386d51141036040a040f4402c0c4500104400811800d005a403414120a4014044a02c10b0150310b04241550091142610140310541d80100c8400035280440d050310ba244004003500c4503a9550344019600c000d01d0007007a00c00b00d10300015003901c0115a007010340035035000800c041c60031407032a1040700d85101d105031284186822a080303205020568464a80c400c2e95515036030281c55400d64 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 258924199 1250 258922949 258923009
    0x2030a141902030d060906080a0b0405072103080f0708060105090a0306020307111212041401090b040c0e06090103080f0c3c0c030304260a0309060e0111030301 70
    0x84501116241d407010115404801404007030b000c0713442004403e45511004049884c1c80c013070140503600c07155906000ca4910210301e030f401807081c02100c8005850341c1c160701c0e80c5212407501944041149040e0001c040d0080c82c2568002111070585400b403400100040032030002802c480d050100004000c00c054980b0035104000e107404c401d0a55590030000001402640241e07110704e003e00a80e02c0d0b086580d06004201c46140a19511a0b0780383d480f140c59010a18000c54401c11381903586058010000390958140340c412402400c034180214684420f6030940c14000b0111131042c1c0180005200054800065407a02d800c481040703074503801c0800b9198500703250841d0054440784488070700c02c0d10540c0c00c844a8400302921141c0b480345406003075440c3c0c1c0d13203054000b030316030507001800300303100320780b18580450030400d00c0c02c43c90b14006121841d19030400ba0100380580000340e15880502c10b580e0040400d075042c00d020318007180c44220390b034441c030340f640010302400800010500c40107805902c030950503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 258925449 1250 258924199 258924217
    0x2090118150f05040e030c03030403200106080615030115092c030d0606090e0606130506120714090901171c05070b01050103141501050d020c1e01090302030a14 70
    0x303110300d0752610301a1540901c1c5202c0c242c8980d0801004170210b8134040305071091902030f00000c508580301c648d41580d141d82d105440078651441040d0742c45c541102402044010603001d000f1303049a00b010042c0c1214954222601c0e070080e0304000806005041c419111401c0b181000d00000380b20262145c81140e4581ca41541c84500317075142011038407c1008001040428100030041120a07a2590305075040d007400d100e01a90801c3c41c00000d019420000010107034282000e0401c2c0c0b2003030303d400001341c55070845c038148800700080390300300151030350064215403020b080725100c603050030000f100241413810140950400c000485424210802c400c1080100c16030000750f40e140d64000280c00140a17400810b800c0e280340c00203030700000b10b6500900c1840303100884c0140d030100b60790b24194030100c25039003121018100b05003000f1868000b56a480034020100349240034000d00214818800c899154003d48101643d00d0320289c240041e4002003150210701840c140300640705a550340f9600c05025003001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 258926699 1250 258925449 258925481
    0xd050406140909241801091d07030311150103080304020a170307060e07081e06060901031a130204050109090501050a020a05030403080411030d050d050a09030e0d02061306030207031b02090118 84
    0xc0c200d84542d002025050b0b031507e020412403a41041f0100c0b00488500341020a160490300051020910503140c0c850000c0e4600200c852403020030700d4124844d0401d034819640f104000c070500c011031511076107100c000d00b90140d624044506500025883e485445401402950f40d540c0d0783c1c0c1706c00828000c84005100c020f042c3c84503090284644240c2c0c10001c2901d4205005440c0020094942a100613050725041491101110080d41d1080030066000d0302054061101d114060f00680e100c3c042d95000c1c207940400070800b10010718000c0d0944002402200c0d00324014040c48000a03489010b99a010390907142c5010301e5180d81c00c0c901ca402c114000c0c80c80d054003ea000c0310003520340010003172000051510040001d23541d05041c00e03044410120000300000d880c0b6144058619000c14000c3c4242e0000781242d19014044014546e90070095001c4000300e900403e110041c16000040728544c0c07100f608801c030800c030050740028410a814000c540705008219164001351005e54094001d00300c504030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 258927949 1250 258926699 258926719
    0x70e0409152406030903020f01060b0a03090305160507051005041d060d060f09020a2111060418050106140403080d11070f0f140a1502030402060c0d05040614090924 72
    0x2001000380117480425000341c07044581f0700c0f00e5018144580700413078038a41101ca040038a00340c01200a0703e1898400c0e010803009021382100100b8484090034080d100e8401080d580e803403c428016800d07034520a10003800000c0c442080902040c4070002e41103410350fa40c06240ba900c100000c1e040383c10004000e05498079141c2d80d0b85965003d54032035050079000b11440e070080d59441100c6460440160841102c410104070786034005a41e10340243c0e00d506000b81803504181d103d100b6491041d520042903005252240c004012554114521550f8039910300111440d207403c40c0c449800c14450350349440c2c80c1940d10040c0c0c9450107109010f40d81000d41c440000b2040c0c0e4407034144801180b00400096a402425000b400940100010102505948400095101304901c0c0ba00c0009400090050760401410004c41065100a00c41003010801030b4850780e48950506400510100d00d24400100325101041100c03000e5075100e201a6100a0280c04906a40d20312022a002600702040803900b0401c10700c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 258929199 1250 258927949 258927959
    0x71e0519020405060402040308180a27060909080a050f070b010b070210030b0d030c0516081005011a0d0b0111060106020102120c03060a050d1a010608070e04091524 72
    0xc035000c0c00364000c55007400692a40c904000491003a440001d080020801150007812540705005424000007004401001c1c1d9402002e10707001d46804c018591900c483c441010113010610034a009411520303400c10010b40140e0b600d01c1c003845005905801e110020030080403115801003101c00841d800f48808401d56034410108920f40c03c80f51080388500d0203103040c00441c0303202c1c0c0700703c00d66054002c1c0202440c00d11074409803541c80c0e20190640d403600602c500001c00380700c260174540003020110000e081c107112001d142e100320303001a0090380020006665010f0b4014168050301e05e0316440c5c82c0f0000380c41100c003005031946c500d001c110b41140d00401d0000600e03660194098102c210b5034031b034103140954501107180510300c42129225802030449100f030000342441180e03401401d01c183c10880621880030408105000241d200f0303c0099044020003000c9a4010010100240290780034052a000e035964440c00700c47c54454100515a41e981003a9030800185980b040400c401e09000385440d06c41c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 258930449 1250 258929199 258929233
    0x5070804090c0c020102010c211122080f0c2d0a0306050601090603020c030a050a170f072709021c02030f071b080315010e180103031112071e05 63
    0x310f000d03400f5510303110110710001c1c0106d1003184030f1000e4201000d400104404030100800c410180703108007120911000302140958808059a0600d1841031042e4502e0001814070b80a0f400700340790349075003000d25650801c1d10380403905001c0c40703004c1c400001c004001d40390a80728586084886035115400d20720001c1407100c154402d500405003a47d070714501644a6038240e080c0d114401c4410610350041048815441c80b490103096450300f20f19028040c845d880c1150344c0030034003d94103140003040d0031003070008003604541a41d540000050309a01046080343d00890800c410f07114003c10245c0005191000c0e05116030f91802c1d050f0312020031034590406800302e89007150221250404181042958a84122003460440c2c100d07602043ca545180d0301d220341c100c03200307110400e0f00c0d0501030b11072040345003540d81c00c140804000c209031042c4415891414001c147d203290320b1f00814107800c140c400f811441d0480f011552881e4104800004803051030b800400b2142c3c1744400907005000da5041c0001d06855 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 258931699 1250 258930449 258930467
    0x4020904030e0d06050907050109030807021e0a140a06031a090c09120705030105070207030503070807020604180c080c0316180905010803030405010c18060804020d080a0228050d05070804090c 84
    0x106d0000c42c1c1341c064440005661055181c08007400940050003224014648060403011068a040c0c9100710984400d0128070414500e4105945100f16008009103504100724442c0041c156803805102c003204034045410b925041d5520315001d406c569000501204d0302c4803c982820901800d890171244490f142d0310b03103c01e0117005480c402c1d42413401040c04644002031440c10b40f80c0120203503183c50015551a81154015201260041d000b4000052001070107000642c10400340d080110b02000c040c1c1e0018428100100302ca500d05070148240f190b107184801fa0684040201c3c2400c001c81302d1003c9800403030ba221680244441400c01001065040022001e18022481540240400307030002c07200781c42e041d03200203000040902c0040c080100c20b1003400754035003280c00034000c01006c52041d20342c2e00041d40442c044c00d015912014200c061725a1304c031400849101c0c0e000040b40d450283d950f500c1d03242d1009075191404c1103404500c000a01c0300800840b0001c0c646028100b05850510a019000c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 258932949 1250 258931699 258931711
    0x20922091712132f030a0b01260d26010303020c010801090c02060613090b0703051008010504150e0f0601122310020c0106050301050c04050a080706020604020904030e0d0605 76
    0x819200400c0b41c503003c140c0f0090a4035800101c2c440d40d10004881c0c0b03600390710b10101da15542c401d5500404010740742446400c1c0440d01505462116604254031030303200855030380c02040c0c0104d040c4980049541c000c03840242c0da43d130500c0c0001c201207030b40c001c07985261100004c005d031070031814000008043d0000307406018864282ca50700030396030381d0755090003c0312690b20803400982c0003500001e14500d054002400340141092000524488603200c00095400488212000c00ea64805100814140050301001170050400034080da1502e66110b81c012000e079801d50040c00e07260254080c90b56030034000c09524002c00302c1140c84c60340e5985011101d010b000034090b9a1b0080798907070382d1440201c4501407071030082000d0081403131181e00b441e18070007944082d020f0112550780314800f0486a4084c007409010b407000c82e2000d502c440c03d0004221050f122507106103071a901440080001c81d4000c28815030054040300c0448076566641000d440403400b02c1d004c1903201010a42c1d1404000d5035a0100340a61 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 258934199 1250 258932949 258932977
    0x1513020a0305330a080303070e01121e020702010912030305040b150f130f02180f01021c0e061303030c030f182603030108030a120209220917 62
    0x24940b1a02d0001c40c500c514000d08480d50f4084078840c020b000000100c100b0a400342c140c1900345c0d52030843d942190026100c00d40021200e41c002c1e185503074011240444d10a05000c1001700c844c14900483e005050a1840d4030101d40120b4080213681c024407485004045040c00b020345d0f1009443c0040080c40c00f2039040303a030154110080f41c030302d95011001d4a60808003a05489030780003170404000589003000d03120000b035515015600c0e4483d40e1030014280441c66040c00e4088015404100030624440d115002c3c115030001d020702074204030b420005159400b16003081c6801c0c3c5941c50100745540b05d85e040d01c03400120f0001000040507404040f104000340207556148035000c8508003280e02c9440381c50102c400c40041801801510004801001c00040321984864080444030240381540c01c01d85c0145016040810001d4025030400b005840000070144110b00e018005400100306022351440350341074690300560b4040262a0b82c2c0b2204550f50000e1031035441030303892010060182c3c0080180040c40d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 258935449 1250 258934199 258934201
    0x40209030d09150905100e0d0c0603090b0604020309070b070303020915180f150f1b0705101b081b1f0f02040305030d1515021617151513020a0305 64
    0x5203206442542c280e540090580311a070441b00380803110b219000d140303503500010b929004000a0320300101c0780b00506a644012400e16228184114030b2800104a140114010020001d16aa002c95684c0541e11411282d903194081400c04400034080c00007102c3d005440c81410010386502e02c0e0140001130100b4070305860785007426080c42410542c0e01002500050074001d00e0389034011150241a400034200320b80350402c2800d083c8102d94040e0800a00507542286038284000e082045000641004d6424603501700d000600c00540c500a03002806024480c001c41d0000c0d06076072840f0f414183c00010803c44080b4039104210180103c044244002c210703192060316210312a40d8000d80d0210b0340c000018505001400c201d90003d04441190380f1002180d907003000c21042d100103a140c00e110040d030300034403410102c1500b0360b0300406560051a00740d8031401d02d0041c2c04a00242c04041503c040161070015200d4020b00000015a603089a82c000303208000e0011088103070703024100794240355400740303c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 258936699 1250 258935449 258935489
    0x6050f0108031204030516082a06041e150f0f0c020106050306040f080909040302030309060a0905062a040b250f0807080403150e0c0901150e040209030d09 68
    0x10301e1081105018010b403e007800a008680140b0140c0960605030915807069461560f82001503440413180c960880d030101002109a48108068140c07812108010402070619480c0c0401942c0055108182e502d01e40c0d40350010800c0146020090406890307060249691921030f08014010505050342581c0c584509038041034414010781c01182c0d0f025019020988503500d0301c071008800c1400555086100f00f00340d001907200c0980031441307a4000d034040c549904181d000d16042032000381090503820308100d00c0c6008920003140090b0400080106017443e21415109510192000b00b400d140154022800007043e421260080075401c0040074014036000c5054500382071964011030150041810000c442d0005256400501411b80601e59150605650740e446940800d02410040320705038441403205014001041402502c1e0404c40307080100303604100c060a02000788400e004108008800110701944899045407000003018060303c2611000000c05005060a03114050580d001c80d8a0840 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 258937949 1250 258936699 258936703
    0xa0f081315080610050a03050c040e0906010f0504151e0e13050f031204080f0f03070e041a0102030f0901180308040305100e0d03050402270601021b0a03060905030d060306050f0108 79
    0x5484c01ca817a46030400800700f800b04c0081c100104404003d0320300f04000b080b007980f00c4594030311030340140b4020519981009006180f5040796401303540542e003010030345480d102d00600d4650613180139840c001c0b907412000d8000003061030760368010700c0401e0f1110207001c0e5214542070007030b0704180a18101d178000ea02c80c0451940d01e208001d101403404110401040004144900818000325403500c01ca05014051041200c05d5106030380d100c01040d40c451b06100790341024081c0d442952103441c0b9540b4445880c000203901c9204aa0404030303490400165404980e010f101c6090741065030307440c11380200385c682c0b406803003560040c0030030b13a101d1194070a04046074207203014040d2016027910103052102c44040341907001d040e000c1e10481c1e102841600e0600c44048a0001000c290300d0602e5a281c1070800c080064104110a404407101d005000600aa00e890f41c03049101101e6100000190748041400e0250850207988071340b81b0f105003400c2d0f0000070300040d0303088240204110220f20009907a01c2da2125 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 258939199 1250 258937949 258937969
    0xd150320010e031509070308030109270c05240d020c0f0706140706060503010e07140f180a02040b0f0309061e041704090905100507050c0a0f0813150806 67
    0x20f905520904c1541e943c504440c4065401810450480300490345998070710316203130800d0b0405100d069656400c035402c9441013006442e03a449915000b00d42c50110740301c41012030041d0041501804860705d02030078007045404118021700c2160030103526490080c510700040d40c051522980540303d641114240d0410110f800804c8441c191250f0010258107000b407400742e0001d80c02500d8090f82c520000600351428002c81903d010604041c0440b18180a10854040c60140c000ca00960560051103541e445032603170b501c0c501c440d040c4440c045640c1c045021002e40326640041c41001c80c0030940300c000341c0014001d103004c0c031040c400b03039142659200e80110204c60b84145038441d500c034a00100300812099044e0384e007000384088800e4a0161a030b820102034410b46101200c0034ad101542c8054106010310a0b1904182d241c03900f00d20704441c102500d640c9030b0ba40440580465034000b0f40d00704000d1484201c9800f203481d6078148011039555108041d20340c20752001d0074040303030364000020280c0c941340b0588 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 258940449 1250 258939199 258939227
    0x150e03040e130f0c141203040605070212072106060b2104030c0c060909050609090307080c03040518253204090b100c0f02060d15032001 60
    0x4000182c0d901c1c890502800d0b5114016203545180c0b1182c080403c0d1080d2504001e00100303062184198094400e012900d83d6400b1420f815400510091000540c00400c0300c0c500c68046071380d40e008014030182c49003880340e1503006a01c49585032a414548480c1c1a200d01c1b03502d40682400c0020716507032010150a40f00314410b450184141c02c040c411080300640c4420340246c0a1300d027145051b2035a5480d821503030500c1c0c01000214824600c104000e070803a00445620030000d072501c0c0300301c0c00c040e21884e9481c081c2c640003c2c013030100843c01d07501d0f4250420035100100301c01007100c0aa4244403400620038003059400b4900e00d050503444290340c46c481106403108492965402140362451250042401050707441814041c5610342e00394403150710000078102822591070009074041e820070400240c0c8035815001da0503c03a0b010078003404100540c4c0c0011001c0c1c1c05a801c1e65590703c0c0944c000c00100341580070740740c00e03403003120001c414070480d608003240201103004200281e1003100019669400d01c6104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 258941699 1250 258940449 258940469
    0xd120c02030423130e010f0b0604030215220509091b06030601030f050c1308150106080a02070f03080603010605041e0b01031e09050d0f200c0a03150e0304 68
    0x2040040d005210320b85481215000d00ca082200c61900000d1520941014907006aa0320352280380c400645c00c0c464400c0100340c0c000d08201c22070401c0040f80c9240100e01c00030303104901c0d400038403c4400f490022104034440800da40f032108505490100301c1d18040303004940c05201d41c100050344107400000d0303d040001124806ea000042da8004104040d07100a01d250704058541920004101403405004e00410140103201e8582800000c004800c251942c000d0f0030390f13804080e260b003e8000114081c0d0540703510b0318088080740d869840302c1d0040e01c69124000d143c48152074070070052550221805024280c110004d2191540e10020401960076800c1603644a13070584142090300346165103d81010071040c180030451101074040051450a0b0652018800791146240e808200c002c0c4411508500941008035200d170214000070b007441c0e64800f41043c030420100700031201440411541c032908c00024054541c0507101c0c03900102103000d03104034411a500f4000e81c6c148280c00402598107440f1282c0e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 258942949 1250 258941699 258941707
    0x3011401030b040317070e130e07060806040f05270111030a0f050f011412011104030f03020c09040b040204051024120c0e131103100e06030708061501020f0f0d120c0203 74
    0x100041101070203165142340c0d564a0002090f00014002c041c0107145c4d948078030209190000030710042d51550b40e00207a480340b500040003001320070121040992400312a50041c90002c801005c0e00410400c80400d0301d0402c0401000300f102001d4201510019403481d05100c00c0e210072008030041072080c000d4040741084004801c0c85400c00941c03c480b2a840b07607002140500d03001000c0812944180c101351813119000e9000c500b41501042412104401514100d9892910351681281c000b000380c00280724589540110700386581c0201800d001d08009100c8034804a801c15604040344124120300001c5110070865041c40d41143c4501d48031000f45444028010f00c0c58010010b81132584000d42d03001e169a01885076681040c04003540c402d01c000030356411414106520081e180c0c1004001900c00e5120b000c050200f150301081b440c1d08403040b104010850820034006030f06003090311461500a104802041882c00780c002640082000b09464030585119903111040968103c1008140540e000f00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 258944199 1250 258942949 258942977
    0x141c0c1101050421170702030a18240e03010e0606011107050904030302090105040b131a03040f0206180301090b0f06060c030f0f0708120403030f0911060903011401030b04031707 78
    0x60b5004084d41c0c05151140309480c80304039880d584101584c0800059001042100b000c9800082da503010300750011100c102035191594945000c01c1a40b03a148104140501c04005180201e8050282440040003440440526014645c0d52030080307440c580084c0c070100c3c402e1140032000c11380c0320603507902401d4154680d440e0f03101500a940080e642a04100041000041448080d0090406841c0462075600d004c1e02e4201c002c0e002c0001641c600f05144010401d004c0013844180d5801001d660640d0010b8980401d40d15140d042010034506503015402d080040080017200354019103d49a0042000c000340c40d2007050046900501000d0455a40100034031150034140c00c0c06008a021150b612620300115651001c3d46c0e80c010070039004821412105210416030140203500d64000d0807001080400000c0c1c680e1094080d40149207405a03600007100d00329501c0c00c0d00421030038401da0f2035aa0480d40d6920300781c041e6240407102035002640040020440545400c0128000c203003981d100c4501e24510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 258945449 1250 258944199 258944243
    0x302030909040f02030304030b01060f0305070e011d060d020c1b060a0e030c0d030f0e061903092105040305100203070801030311070e130c09050606030106141c0c11010504 75
    0x2602c291000b010302c850038070041e64100010f0026510403604109594584000a031204040010960a06040c1810010340300c3e408141846900001d2800c102d510703004500301140c29000a00d042e4011100040e02c602c0312141d42c00030207041c0310324422514590114200c4030205005214203581c098401c01c0710428081c8112030091843c1002015180c40003d1907001410185140c0000c6020555002c14410120381002000303c0c00030041d64550310b0908005007508041c840d0407074400504d5a145025014003040c0300e900c600080603003140200107528104c0103001303500644001c03500ba01c6411a03c0d05280141e00980f03000b001161911200c03a4219601a40d90a86000b9100b88600c14402c00050410a0240b01c030300402401a550030503100505103141411401d410000501e42086c05101294813004112811a030951820b6407031551184041c80161003921a42c920345100ca01c081c1c101094140e00082c00c40342151207101444240529083c281e030f508a9000c1c050041500d140d413100140e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 258946699 1250 258945449 258945451
    0x3011424040b21040605090c0d050d03020a0c0606030b06100908070513020c0115060207060206100b030403090803070605150d02030a0816020d080306032505011404050913020901120302030909 84
    0x703c48002c0c01400d034100292008820843c3d054403401e407502d040c0b1900c0c0d20144004c0010329010740f183d0340003171039039250280c1d10064801c00800301540018044d6a5034032422071311040d207600450034000c4035500d08140ba01d4210660303085100d548044100c4014500030903442044030100c0c409011040c0c5030204014011008151000070a07030200039080b9044402c0c441d28415000e115450341c021820502e001f441d200064004d04c00755844403042c841440c151032401000c548003841007950326600c40c6411500042c560703000c0f1a0912021803000f08021a0740c00041c07051094071036031806030086070204804900499000394040d04000241d03004284014000d04081e01300034080301c400005940415014403e42200352500c0030f010050103d54a001d1165004c501c03841004188442070502c00d12211154610800e8113100005003000c03003048074041643c004020040c011034051038481004030b001840c03400200d1043c08000c0001c05c51411904502c120349816130b005600b0000f07408140146c040c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 258947949 1250 258946699 258946717
    0x912030a060e0f0a0c0c02010507171605060105030d09030f0b0a0b030a0311011109011d010309060e0c0f010504080c041e09032a082b0203011424040b 66
    0x6207454012a0310710099403101d008000a4107101000e242c80040d01e0202c4400401c000104200c40214101607a0310100b62129075070400303880d581d10002241409003501c540718183e45085a2a055102070087c0402c0480c101c680a80c03d444500c900e100c801c80e10200ca80c00001c0c0780d11805450fa80c049008010310310360005640d0b000040411200c000070340f61682c06401100040c1d84140412000c100038060390008800b5414054100701e01c580010f402c0c0102c0b030b03940ca40401403440f0325402603271194001e40d513486d4010104001207152840c015441f0311034407829500031503174910389800a503c120120f40031070f00040702800000342d1941c1044080c1c141040a40b0110b08400e4040102d59454402e07000c441d0f12907240d002284080d46840b0703d441103030150f0400e4243d40f01d600d06000c101c0380c1d400c60341c1d0030284180c03a80004480d0907181c0110702c41c903607100800c14800300c004125011040130900300e0841c215500c0c03000324500e4030000200d4031004948045c40200b4041003081c00106005048050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 258949199 1250 258947949 258947951
    0x8030a050a0534021903020f060304030513230306010b0307030f0f020f04030c090c0203030f0621070812042402150c1b0309030604031206080f060a050606030912030a 73
    0x10035185480303c200d00b00d4010340d00c0d00d107124024401c6291284011403c40a81d00395034500919640018010b26800c04005002d000000000b40070180300740c2c100c482122111483c01038094840481c100e1000441405c3e80c5042c4070010440c0080c40d00050550490f4221400e1a18590300c601044015202800d5840342c0b0ba511048080680070603030000e42808003074116113907210f51843c01c2804c82541e09038030058000303140c16191192030783c1c044126903008081a031a6142c9845e620046184a44082c04c48210501e5812070ed11410401242c40b904071074000d01101e9203014000c40300e039005e01c42c07481046884250f601440121300040128880500c020b0700641d028480c0f00b0805407085901214441808680040c2940201c141440d580041100b5031008600742190304000c41c1ea501e80141028041c42070000912285401d50341001011701451025141d100090354104c5603503c1c029143d18000d42c0c00d01001603050300f001001d41b8803c076002401000b9400e009040840c8070b44c40505140380c00303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 258950449 1250 258949199 258949237
    0x30b06191110110d0501050a0803030604020a09090218100f0c02240310150918090c18020c010e06040b0403050a030f090317010801111210080a0b0106020708030a050a05 74
    0x80c0748980b140309483d81c5401e003001c2d81e83c82060350060131564160411803140c40f4940c42405003580000549900c40340a54006030b41d1948500240d890215a42c40f1400d190300005840000d1940e030460701100e07002c241d503000d420201c00e0030260781d403210700c40c2050000f0785600340b6900585003504225405c0307420600c200e0800203a0451100d11a8011104c0c3c003003c0700300103820030218011030180c50036030143d89400c414003400c0a40140000c20715100e0740b003525484541e407405001c00810080000c0c600d0001c94120401711480001c040d40144202d500d1179440d1003600074a10700003103607003885150710140e280c41e00d81e25958295000c0d0458490101007598030480304800610520030030b10214082d03200c20710700d0322000390170610158058100d42c640d64107002c807400b5106108800d48142450075903104c0c0d015a20b511082d4841401c0d5441a1400c1c400d059881d4140f00b124080581603a00c0780e4240c9040c252200740c103e9580c410031104200080040210a507054403800c0a04103a00d0000145000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 258951699 1250 258950449 258950473
    0x31c021201030308040b01050603040c0608040611041202040e070302101101061d090f0c090109020702040e060406020c0601080c1804030201090203070602071d0c070f0c03060e030a030b061911 84
    0x103400c0c0240c00c110081440c0b04107100c18054400c0009004240407140c90b865032034984e440c00305000c5075110320020301544a0110302003200c2a00202c2c1165107402026854940d17640c15000d01c244000000d074080d926000700c6804030040410000152500070300201c001000000c41103da40d60082c00c0c1060035540c1344804250311510000e8030103c45044803400c60f8a0501c4600e60303041101c0664100c0e840e07842900c3c00e214a0b2a40d04951b41100c0511600585602071400414054170600c90116002e000d0314040208100c42d5502402648259a003155080d84e21140401c0e940c842d0f02030413682c410084c05400d184113015810241e8020b119100120304040305a0209143c8641500071102580002d1014000d100460204103a00114911800d03044d00b8410301000045c803030301601801030130040f1808030500150842c44001558080810800701d40b16400c90b40d12900640003110002341441d41482ca1898a003040c0d81d0380008d0018840303001040464240d958940c1c198041c10140919210694 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 258952949 1250 258951699 258951727
    0x1401060602030307140a08220b01081e060106080a05040f050a060b01030c030c09090f0e030c010c030f0507080a05040303061e0905062e021606110c12031c02 69
    0x80a00c0e4000716100d0810304406031030304c003003520303411204c0c80180210400c3c2d41d40806c0d8950480000c00c0e074807500c0c80c0004500da5042d8101d0f80c000c0c2000c91034000029080c4800114220300d0804004030620003003c51205da51910820300c03e502c002085180450b4502485500c5140c0207031050b0309140c001d16003985c0700d03414180402410344815980d2000f440081d6003501030702001c03040354034042140e100c2c2030703402074802e40b858041c2154880e82c40c6842c0c0703408525030740914a005509402c8945940140c80744c3c038042e141c1c1c02c8880d00000d0401c010b61034100f40900880380549216151003c02d44da86103e020000c10000b00250105a29a600052815044080410354824400c500100181024040000d40710060304d402d014142542052542d42242c1c0808e030342c21407480309504601c900205040349800018280541742004903200000c0090b000001340f010761010b4010360b2402c04002d4100b02e8171148001080c0701d25001004040c0402d508805060f00c60006144018204010407000c05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 258954199 1250 258952949 258952961
    0x3090e0a142415093606060d0603140d020309100f170a0e0c0f01083408010918030e361008010207050c301e01060515071401 55
    0x803441d0300044d0650321818010444040011401c0c0d104c05002c40302d0640c0e15006031080804c2c9140030340d5202085d03003035070f52000321008038081d004140704440d22403c0441182c0841c44040307645208001fa54a691b82c004800d0325040321005005207007440c09400203484144402c01d03c4801c101d007960f141c840503950305c0b04041c01514909000103604400054052402e8a0f82e4155442180c03071003840c4120744ea025211350b41c802046402102481910030001901c40c1c8002c0200085214010107030041c0707503002c09900c5c12074000c000c080c04804445c2075965212040c1c04009400a84045000006da05203c000c00d24207001c01450045240e08103240c125251a0b404107180005a581c8103007c030310b1b1180700342e01001d0401a0021031030001c466840e10760701c2010700d07070690181141020003070381000ba086a5071f928208080c46060814040700c11a0740340d540c40795908a582903c00a081c101400500c20f131000c1d0341000d450030044c5c854410030210903402c00d203c1107035800381d11800070301c06032004e010382 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 258955449 1250 258954199 258954229
    0x702060c0d11070501080c0a1b05070e0a1407020604080a0905030601121218140a09021b070b0901080c03270d02060f1303270303090e0a1424 62
    0x140d2410102d005050308101803a40014104000d13501400f6010940d801203d000942c1400e008841c0310042d070000c84d007082041d40180c11400b41d080c00142401c81c5010283c801c22010004122034401c2c00120540c035101907926400580c048000200010240300c0240329078422800d117008000d5443e00040e1410009810440da100804441c11042044080c80a5000c11a909051084401610002c41554040c3c4100710840d08042101d8010b41c0b2000c0151020348500c903c150341d078034440042140f10740300908510b0210310455100194080c042402c0d500418416510112541c41c5c588840aa0380c1002e0050303041280148840e0000c911840900b01e048140307040030b4007841400c80c101900300780b0000c000074805030b441420008000000c01111000580c50b09101c607020b00d0060030095604d001c00e003018146d81c92280c01000389500000a9802c0301c28448490502d44c1e0344600034000da600b0302c4070191042c0418408103202c01040c1941c00388041a01c400514040c55481c0060203c400d07075000c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 258956699 1250 258955449 258955457
    0x80403030b04181403040b030a020d090b04030e030f0f0c01111e060114040c0e04090501060b13051e0a031211011d0f0703030807030903051e03010e070804050d050702060c0d 76
    0x4203042002c2504a02080130304d08002e10f05061a050103000b02303101c001e2503141000e500080420600d91540d200d0317810f02e2713080703544040d50f403070036280150444140010191091166940c07c0f50840000106000a018418040d01e9403004403001920540300c2c0c24080d84040c05507080180220800b183303801c090401326001445030b54900344080800c007c4000d2a030780112b0030040782242c1e450b04507564404904060310002a4151281030440c0180b074039420a11251307c0010b441c080c1d0b00140c070744140550704101c0b0301480782601010440500b140c102882900030210000401c041502d81e0383c08032041e00ca80c24024200001c0c182003d08446070300214400112a100340f031408800b0030800926141c0084001708219404c646000d890715800410900415481e8408081090b00c1101640c402a45074034440501c10b1107580d00400603002409000e03d48500000064240c40c4510300d2103000d10b81242c0a0311110704400f40490703c80d4449a000c1c0d030400c50800407240c20380c00411a00001e203c0300d036a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 258957949 1250 258956699 258956741
    0xf0b0f0418052b08011a071406010b1b0115050f1302070b10120203071406040f090603032318060c030c0105040c050604030c05060a0c0f030f170c0703080403030b04 72
    0xd01102143c0a482c4000e00300030b180e50050010b0b40c004040f0001107075110081c2e54035119103241c0140c1d02c0c04901c001001500a00c0000640340300c059014210626001c00310648000d40340303980f103003260b0300d0700704a4005400c162800c20650a11582c000001c6c840034180d020320104600030740e030903a031140d08101d032080c164030100440075500b00c00c00b1b405801c0405d28032091011030380000f5030322050381c040d40300c02c5948170342c01c18065601c502c00c4a000f480c030700c0e4150707003020364441c00c0a0081c0034a10050740400c01c00e0b06080c809401c5090320503c6111743da000c03541858644005075015201c111380700ca4001d01e04001c02041e8400403c06800044480e200205071460b03c1c1c0340c074040c00207003036028501a850a000c00d0001401c152080000d8440546a1580f5019898021200032000388006004c0000c0b40100406059004a201030388a07440c1d05e44503403417031160b600704000c0001110300c1030900e401400700000107071080d40c4d110b400c40e0280c580800e034032502c100000c00b1580c900524030f0000090f20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 258959199 1250 258957949 258958003
    0x3021903201302030f062b06020706050c0a0219020109030819030c02060709031e06090b0f010b0a0e0904060609050106020309090603030301050102060f0403030e07060f030f0b0f041805 81
    0x100e546000001c160001e6045040c06a8200002c117806002d85100b81036040040031820201c0d10300c51402200300c00e06040000442c00c4c428001d500002c070945140d814040010750050049080b0703030341201298002c2244080600310300f424225003200481c1000b00007003000000c41c00d1480a4000800c034070175060111880f5800103000c4802a500714420b54006000300a41c854008668000f240d40141c02c2d4505288023210f402400841410014000d0340b41c10785680c107000300f00200034420745420056090390303621100441f440d0b003e40100300001600208420032103040c80c00100b90081c1c0702e0fa201051098a41c500003040d20000d801160051388041021586454044211900210194055071030f550400c00000e40f1508000c00f03082c00c101441c004101094071903803040103c81052400d0340e9880d80c071524010605160381d006000001d0a0066901512180703104110000c10020440641011900140800380c4010740d40380122190100600000ca4801c1c0300903441e529250640c403940b80c0001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 258960449 1250 258959199 258959209
    0x1032a0b121b181f1710030803190b03100b0a230418081810112e06080c1c0c270e0703120302130302190320 48
    0x811002d41d84030101c414888820740003084460b15036100080c035101d2803d18020400c00c0c8002d49029540d90403200c509140c080d8030504a10704142c4480021070345440e070100107030007070b80c1c01e00000e48084000c0004c549003165080800c81d12811100380414a000340000103030914061004425182d52074140741c500c2441c0100126002d8113104ac056000300f018001c0c1407610311024003029009903aa10114103194030302400c04900c0321f6220a40d50354a1503c000d140444c4402c0404490140b100d2008504025015040c5410032080f00350090103007141001c121900282c80c038200c0d0151502283c2e180c40103800d54000e01c005881420000c6c4494400101030142e44801da90111101e0040c0d00700103000640558449011550552074815524040304880310461804255100409141000c0c00b003560700f000c109401203900640b1121410f000021054040c2e120b01107280d14035a070410024401890980720300103a015131012480700460326583e40d44100002e012140f0f100707041503507103e040c074500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 258961699 1250 258960449 258960451
    0xf0302071118190c0c1203021b37030c0c050a0305012c070303080a06050409051005070201020a0207051908011103041b030b0a0504020f0301020a110613080301032a0b12 74
    0xc3d0030f4100009001c520009040f4102880000c1000800c003c9441c826071180d015550814200007004041c1081c12074540d82da001640c40c2520722680794606503002c80f506803042503282000040000e500b142aa41c1103c15901803030081710dc98290350804107480e294a038025000d10320820001444e11850280c0340c146015500c809114074002c1d40f00c81102101c00b00e41c40040303a90600340310303140b0f031141c000c54409410304d41c202c5500a4503203034041d018480e0029849411750641402003002d0785414400724240d102e50100080940e0110400300041d0038025030900402c28002001c2d080d45403101d001a0079510310f1f01210f950001c000c0140014170400041e000030380c8500e5881c0900a501d0341d03a81001c6158010709100da176695400c0083c2c00c0d52070304d0080700381d1204010000c41d81c41540040c00740c9844400e0500c0d0903a03104a42c004fc0d080840316608000844d0007011050844e1f10b1903840c00110940c01c00504404042d4400a10288aa94070b00b4005012981302e915203e43d6074051203980018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 258962949 1250 258961699 258961741
    0x1020a1403130b040b120702010e010c0507030314090318010201090f0c050102331e040c170c0a1707120320030a0e04020c07080604060b040c020703030f0302071118 72
    0x2080200b04a01010b00d0100d030388411b01c1c0d6040700220781d60342e00705a00506c484d4441d1034042d401c1c045080340060b480030041880c0b03403094804002c07111000c17504400119044034004800c0c0d03c100401088401d0301c0040d94203030001480007191605603540c5451581804590455000f010103030180b00560b01840b100901c02e4250022300a48046200020f0803109040c050742d13061070701c1a01003000c0d0403440b084c8008041c4006100c65040c1011718040400160510544294a09030f01e01490b8452001c5005054000024207a00c00507080980c1e807050151140c0c02c1c030100d80704600000030040c003120003480362176020b9100c00c00950722070394020800c0d045422000303400d03420400c00c0b401c0b110f4100c81080040c400c151401611582d10b0742c072852901d900b40d08498214414401000104206a003052400b03540945043c000d41000b0b9105980d0780100f40070040c041044192048a10351296014000b0140514000c0d1210151000410b00e601c401141c0440c64081d440d003000107010074a480805070305 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 258964199 1250 258962949 258962969
    0x315180507150f05041a090603090d090602011a2806020307060b0d050604152705010608030a05040e19050705070209060f13020c0f160312030603020906040b01020a140313 75
    0x5a03040384000c059202c3e5002d03500021046c0c5080d00026114402903030311060340030340241c0d92130902c22081ca42d114210761850002a150100104120788180942e00c0c060500090300109127005000704048641c0c0c0811041220800d13802103a800c03451a00c0c00d0008090a0300a19500c50050a08006441c8e031001ca881c054100841c40c000022000102d2590103a08880110303160020350001d8005001060b40c42050310403520010028841d00104240c41103100300000c0000759920202d0759147d024040d1020007241081c0020000031004191040c0d00074240c01c40c1baa4501c0d1240d09160032030f032007903600000040000c00e480b0114101050102d4105c00100d550300d201100d41c3c0005440f00d44e401907805180c40d00800d56082d42d0304104000d850160306c0000b5954011008200104990305912050706c1ca05038440461091328000e01c2001e041d0f0760054403d060342c5e510b140512000d0a030348641d0504510405031184082055000b4900c030a005503c0230f15039440000703404074404040c0c3d4104250340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 258965449 1250 258964199 258964217
    0x11808031605090d0303020307110607020c0108090a170d020915091201060e070c03050903060421030b010e010509031014010f0503030c100506030a050a210216031518050715 76
    0x707039a0340c1034400710203905d480c015940740d0f90080b00300d40f43c2900b080141d900780701c0c86045c0450282c0124800c15410001e0b80c6200055554880079035854024020150111140b41d0048034a0031901008004040308010094070703210015010580d0203c442d240841d0f1444085189041407604103502e4140c011024001d020079030428100d050b41020142105082c040140d00321420103000d2000d540b9988002815140d040c07410341000c0c2c0401b0301070b40000d0064001c5000810440f4001d1107000b00b11001a503a01c40241c2211005580d0744c0e00240403940d0502c2081040200c001260142012070a600d50100c4025494049103400ba0310362500031030301c26081031000d075580441c0080c4a40c11080141c5011640b40c6540e00840e061198041014200d8011071584205102e20010400c01c0845031000070b040d001000c200c2281c03905079904500068a581100802c0031070000c12004c0c1750761034a200c0014070124403000006540641540c111807580201800301b0031070381e078a0707444042090720341001351003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 258966699 1250 258965449 258965467
    0x7061d010206010b130801051e071716030e010c0f0306090e0a060506040209130b0a06030509060403120209030d0306031104021c090302070504020a0e040608070f0b0c011808031605 79
    0x46003014042c41c02c8615001c216017202104140349000101810002040750b410902452403010b0118501c0c501e43d81412804184201c1c86651603040c8030b010004001c41e203446405018a0b0003404010900c00c254580c06080c40c401d0080c0300d04c2401c3e12260300e070081104030130718025050710b520b6403002d11013a1030511044500c01000c02c201c10340f039502400c0050702da9501d00c00107000b4010f00040d42e40004203c00c0d0081a944c00c1c0e0320414140e2006c5402e5210556215000c40079104100e03000701d400c0d0089030102e4006409460020a44015034502505040704440800d180445007640100084d844500800c18004c032807032000c50031403003510301350b161260321f58880d0351008400010310103130395481c0300c02410300d132080c4001c0000e058003c006641d103801c805c81c0100500110303441c0a200302d180000020344400002f810700d00b2201c00500c0ca04c880f901e80702241055410401600f9929500d590501103644a06d040c2a0001ca218034806a02c07800d08880e000721000391455001c051000420200718 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 258967949 1250 258966699 258966703
    0x1030305360a081216020301020f030c04030c05041b031a190f09050c03071803052a1012020a0c020306040311160b040504050406020723011103040807060908070c030507061d0102 78
    0x5c56000d010035040ea03036008500c0032a00910619100956681c00441806040c4003c2401482141c0c0601e254002194541e401c10040790309654070b071305800183c64a06810315010780c008403071280d0507010b400c840180400201c2d944140690501840000700b030801d1150706003503c2c0400240c1400e40f010401454451090300c5d9600c0040d0000301032010807100009180511210320717000d55440301c01d035180e407040d61581d92030258451345020704401400c075401e810350800e0502841c03405d030303540e441460072100f040c8079000940c84041c6000030041c071440d5100c00361f01c0801000c0d000c0d91003543c4103550501008450b03810001006410002070740e00c00402c10084006005440a68908480009007502c4500c2c0900080c403450380014564188007808e6200c1c00c0c404a0300300d4050b21780a0080c02490307042c0091039260321080b60020312501042c413014021074a90707070107868558800d072103da140002c2d0340c840801d0f0501c25402160f1982c00362205100c403540c05910781060001c1030f40344584100c404d1001079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 258969199 1250 258967949 258967957
    0xa0219020f010503060a0f12110d030e01030b030a05010914010b0d0305040621180c0b0406120b0325060e0d030f030f0b180103020901050a050901030305360a0812 71
    0x75040080110110340642e0340d0000c614014001c400002d00125608c0d00900000c4e030300b0680030360b8444420301c1c03120307403034103042d80450341c540d6040e5a41e401507502040107400602007030b0360030b070b4151068400c07081c00180248100c1005078021015900018020401c850039506070380c0c1428064007061030039000090b0007005880c192449400d103100103000c041c0c0d8501d2151030149074003031141d04002e00e421174229681d4200bc150350149441e4400d45845c0c68805403d440389214042c00504144c90140b070030700c0d581d80034020a0500030b05a03603820000e02c10200d03000302543c1d107520f80c20071420000c110103a041150400c01810607100002c5031401c03510083d00106428002e00d040c1510703400303100e0395100380d80d20440e200c0c0e600400f207000b0b100e8005807181100c1400d000807802010203200100c0d09250214401d02120340052140d010741c1e08540e421106500070f840c1c40307042c841d03102090395240301402c1c4641e0311040c07242c1044a10071203200100208015680d1200c0c0303481e0404001030031039002102c01c40d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 258970449 1250 258969199 258969229
    0x1504050d12180e06010f030506010504090207050f03040b0d0506040501051c170f040e060312161541160e0603070e030f0c01080103121110020a021902 66
    0x48a401881c0c91070a54211070700102520b00a89000d2000c201c1090007000c85014000a983d56960300031a46410750464005607600c9012400c1803204004c1550303950020061280315100f030b18101184000207a2464100e0b030441171400d4408079200082440920509522140854040c0700651514010800340c40400d0781915154090070207a40520840ba0310740561034920445042e41e034864000d500d0102e80050045011460030302d80840c550707140004600402d010402105488c0c00b0912161492480440304211034407182203041101d500903910800c034600e01100c0010001c607030042e400840460401d80c100114001301e42002d00d40341d00f40c01d01180d008840d28004105030522480580c0c1609a003001158803d40c0001007000d040d9106210801c5958142c1c2281d0081d04014002900c4104061240d800030b0105401040443e400c80c1e1400c1c2e000916003040014200c00188582c14981c03002443e034050b54000900600081d410000c800b40000803030006103200d9000d034001086403a4036014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 258971699 1250 258970449 258970463
    0x513090b19090b0106020309030c030a05030a051c050118180c05060a030b04020c011d12030f13080703030c0f090503190201050c100903090e1513061703091504050d 72
    0x16660020040ea10500039143c01100680c010b61392010300039034a0780041040d0380030f030048442070552400c000030903015450344100a1820402030781c0044502e40c00c00c1d00c007602004440e0b0301d154200c00d00361107030300d01820340d0347c010f400800e81402001c42a00d01045115242c000600310290118520301110b00a81c1d4007211081d544080d0010110080e0198505c400c0c2d1203840025010b40c00d00c03055205000302c4407403e0340d1040907880003240b00d8031149a100121942c00c020030001c0c0401c0c06020b8480d41c8000d07201c4001840ca1071075120070075aa04522000c90200e0f5981d04d041d1001c81c0c01680404001c0d14038079080000c1410013010a89030300041c00850340c82003050300c085c0210382c0030b541030703560030a03103102140c0b404150078000c2e0300070f49880c10342580415040e81c1d000c24958103005405110360041c10544c141e68204c81d040c0a0044176040f0003120b030300c0d035403c8003080e50b0300003112840c019803a440045450b0702c115020041d001d0200d0444407030000040004000c0e9807070f80040c280a481e04000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 258972949 1250 258971699 258971731
    0x8070e0f1003020904061202090a0516030b01090f080f060f060f0103020313141b03010b011b03020f0f01020409180302070b0307090e040804060210090209180102040b03100513090b 79
    0x103000c0e400f13406a446407035441418040007180e0130341030300740e0508010b00880e0050706c191111254001203400c20f481e100c54040c06d040c1610030080c000d410045000d907061400c1c000340da5603080809400301290b0000700060b0043c100114826804006031504081c452103084198141800040c07400c480c1940224141030b004000500000c0b109010055201d400035200e00d80d1203042400c0c1529110802100e0b01d0040c1e2411000c00310707050521510154070010384a13000d4140d5500c1c80840008241001141140b00d070418402c14010140290203c0d401c103034001684590401d0080310540b60305d0b41c02c01c030003c0140038599001c01c2c0c1c0042e10318101c80c210151590380303484a1108440c03e1a15401c44035203402c001d0148020401010000e00464010341d0940d42d003006000c40035000d4640605000e5800304103640443c003050110912050046401c0000600c0c5c01e81c0c95800c180e0940044443c4001d440e6640030400440c20b203100b000300001800e400c1041501c0d2982d94040180f10064003e8203409441c3c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 258974199 1250 258972949 258972979
    0x1410030507090909140102130602150708060904261b120307030c0c0611040e0105040207051b030f0a060617160e0711030705070513060806150f0a0806060108070e0f 72
    0x3903110b00c01d960308000039550781010600b6230300d41c00700310301c2940018416000c00c811041140c2c110207024030b407155260a220307100c403c100701020001403c04d0300c0c482c018440c80c0d5448164102824024415181d1458403004c1e81c59821500b4510090001c40f9500b11141d01c5540c5003243d01225440410390400288500b045501101c0c1140864001800c4915010381409101c1110001d081115558441c1f00d800703070b03212024081a070088400c020583e038000c0158803803040800b46140d8501101030b0440b11034140220b90140342000c100300a0b100075644070300600140640303064246104e1015002030030500c4410209040012040c400c080740e103841c0d40c0115500a02c218807040c078804c0d12030b0469031601003a04155440d45460700c42c0030b110314100315144ca40b0f0400e0340500303800c940b1210040d0082d42d43c0c2048000811580d003091030ba015444212600741a40c80495040180400e04020192490007000262200318084c21000074807160158002e4031789d40310315802c0b01c880f005942c1e5100f140008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 258975449 1250 258974199 258974213
    0x3020a14070b030c0705010b1c02010e04240e060d0203100c14030c12060a230402070b0405060108010f140403050a030e12131a040e100306061410030507090909 70
    0x240c101c064080b030b000061050820f15400500354642c09480200311201d004802c111059200b1100030030804020700f0b000d400f5600a00155500c00310203007002c9000081604030250403074407001d03490600310320b0540500450300940a100d034409002d45107944840c2980c1c000035551140718104243c055120a01107110700e1007400d2014030110502d51781510b909003c8240505604a425642d65004841001907803d03d05500000308880d81c10b091500030002c02c05507142d403900720b00c0101c0c2e0400e40030804040014404c0c1020b078030450045014020302d50620890b9401e41e0710701d11150310014103000000f8000038034400701c29081645400c0c026512082600d05a0180ca030000e4a04800d006091806500a84003001040d40e02c82c0800319070036031600c1d0100c203650391484030881c489161084c4028090003100140300c0350041d8900e60303130034802039603503982c882512210340002a024468056140c0d00341005002c03140c1c0800e0f00e040c14451880d01c1000104901154403401da003213501c0d203d4180c103121348 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 258976699 1250 258975449 258975463
    0x120803090a050a0303090209071404300f200a05040905010b120c010e03240403051209010b010822020402093f0d050a03021c0f060e0a0903020a14 64
    0x102c81c0c1500c4224400742005001044009030030f9000760f80c60400141098070480340c12060301c1038025564182801c02400c0700890f42a0a400240d20007a16a201d134068a8260b180104520588005c03248003c5868925501c41d900e00d030b0780702003801c0c4400c20b1540395203440c810800e40b10181c07000601c115060130180e000d080e021441d6a046240d00881c0000c00344c4c00304105890034801c0c0c03115950715803100c00b85a600e034505c04107003940e81c0e00114481191080e0201d410b0300f050003840c01600344030281501e190b0b507030300a403003c4629a6483d0006c55140d41c112032100d600030104010284203608000004115040520000b0f10a950005c2c0103016a510010000800403c0154101210103148500004103c90078481509005054100c52135494002000a150344065403000d0a00c180d200003035000e0b400550404580084080c500d44c040505481606a41c20340311030049905071070a40d100c0030407940641880d450604108440010a030000b6070000c10320f0303100c81003170300025501102c00c1c10109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 258977949 1250 258976699 258976703
    0x70302070b070c0504151a0c06010e040821100911070201030f1118040b0906031b0a09110a0906020712020f04110f0307020615090703150e160201060f120803090a 71
    0x201e000c8241c030038007401594002c15540600070606807c50142070440f0309014583c591201c6501010050104201d5451800e0300320784541056810001188004a0b041150750420310200c52413400b00b281c400c1000c010030004054a4104100d0003181c010b00003114400c05501078140741d03d6951101b2845841d0348622202c544a407901c0ba11109501121840c44000d000d51620039424044a91785625128a546014400c002c00420384403900c5030500000100c400b000d80d90040303521100007041d10980c0200004103100741c0819a80f81c0303d08101400c0e5900b1500880704552006405000111422a814040b650119005a15921035400080142c86000d96034001001c01080703400c1405900006540240510380030340302c49545420792074004080149141d50300410303110108411318001c4c0d00c2000c143e0b02a44c100340c055921000c0710071194405850b0201c00c104484841c000c865820310510024080c10505659290324004100e110031200013005099040004007040da1004104500d5803029 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 258979199 1250 258977949 258977951
    0xb01151d0a03051f05100803030402130207080d0912020a0b01091d070311011d060304061806140613020309060115020f12030f07020f120a090b070818010203070302070b070c0504 78
    0x220303000c0c800c1129040c0c030740c10001e5030700e0800c3d0114010000080c00b080a481f6040011404d603603d5408201c0c1103030036241000d02d030076820429000440d41900c0180075075040072030080303800f900340d24026038dc8164440400003150400b007030304000100c00002c2c1e54111090484081042a1399219400c80306a0000038445c1c01c0c81005800003c02042429501c0340c1e404c03d8a40c42c00344507420502c141540d940840342c43d8028020000607000174419401207a401010035100d070340b4840035541d2082210025602c2d196001360420030040ba0f8a404000752a00e403080e00f005504500384070b80070541d40d605c18041e81824107014210000b0017442004111a004551070844508103c0c4401601c519030041d1910032400b01d24000207180c035800001c102140d0344c1305100514194201c06001c1c100c40e0005001101005610300c000610741a03204044d243c5640100c0015648041c0784c070720820031760318a11565055400600244000c00e802090035011545640c0703815035581e401e8500244a0f00540d0440350740030f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 258980449 1250 258979199 258979213
    0x303030e0f01061706280929010e090307050a2303040b1e031303030504020301020903070603140106081312030b040c020c010212250c1706040b01151d0a0305 69
    0x320b5941a204100e00515000340c41180e20764110f5a410038244004080c1c040f06c0466240310403040c103603c08522540034010003141c0c201c0b40d03800320070640d1a00148a4000d14108010b0054030032031240e490b0841c407014029807902206599880d03c852707458401a11030030754030340300f007180b4040b40f0f20a80c05801e0203400d4a0fa40d5407034003007030440ca80024000ea036600c0760600043c800c0802e00c204a80c02015100c101c1c0400182c0c1d99000c401078100100220b030555000e001e002d071641c07403c01912016103500c0d200400c03400d00c0411003a8642d40d050b032001f410071585805014081c18240801d5624503081403403020702c00044902035000e4405d03d8803041c2c04c9890260900e013003070360100d800c040d01c81099098843d0240320318000c601070b01800b044140c000c40808090542e410091a807404264440d120007640c15640b0700030000c00d10078140d00c0031801e820a8040000304000c2000503800f416800001c0003c403402c0c60802811114031b5074281c00c000c00a104458950380d5032100000c011135008040784c800d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 258981699 1250 258980449 258980459
    0xf140d0b041410020a05030c070201030b09010927121209020a06050910080609060d030e131b0c05030a050a0c0212011a030105060d020411070605040602090f010e0a0303030e0f0106 79
    0x794070114070021801201404003d03400c0c24000c40c1d108010559915007180c0300c1d8001e1708502d07800280c00b00d06055840120500f69192004442c5c002d000b000c1c40000e50f03e00c44124504d01e5008864a42807034482c0354480f000044142c40301100305207e0f031800d08000340309034003150f0082626460295105a9140c000201a40c0c45001416641030590301e150b251020383c401900e0040c42542c4044d840310f04580040c845040c0401c40b07154441c02450724011500449021503042400c40390100202601c8a0080600c101c170203180c1c11800c191031411340e43d09001c83c0c641c2d6460b8066079540804204c000241450850700c9104695507a40c3c000b42503401d0951102c400720b0081030b941030072613030f1111807848000e02071506104c1c2c2482480050700303180d140741e91036080100800400054080e52181401100c020905610546110724411400180d84803100802c020218404c03005480c10041e18001d41061501d45600003403c0325454200811080c61044469040c4a01000000090342c0392010000d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 258982949 1250 258981699 258981713
    0x1404030803012c0103020f0a030b010b0403030e0909030d0f0b040c0309020108100812130f1e120f020907031b020106051c02010807051e0d0c02070902040f140d0b04 72
    0x8101d5007020701161151082c04050201c1d142e180c0558101e4020350401040541000c1e480d1944181e03004095040050b09c90b0b507071400c20b8030280c00074581908041014002c25400403040d0800d1601140c20540740d24052000b60390324420300b071564080395207510005c2202c00c082c3d005035125100040040c0007000c04103100070700400806800ba4002010100400d1540f940c01320050195204030010b0980d0b10400d1030402e0041e4401c0b55060b00085035000c3c0060795100e00d00201c00500b100b50307280004126022109505840b09401c408103072030402000ca40010440855a2003080d41619003004503560840c0580040030b4000181c20314000f04111454504c1d410340c084030903104203d0342d1044076003200644608000030b10900a001c55680c5000c90503060140004c1c140318004010a907000595a01c000845c41e000700b000030a50320780b46c0c448441c4040c2c0621140010b44041d4a085040603e0002c680c00300c00a07074490004080342c281110b41a41d10784103004034070143c1010600040d400e00d032030001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 258984199 1250 258982949 258982951
    0xd05040c050402030615030c09031e0d0203270109030c090e06010e0603030901080907120308090105070201110f090102010f240618170a0c08010b03010b042a1404030803 74
    0x1649420a080d0100312031401e40700b643c4c01501c024000100b9900740c500c0c8a120303944003a21680451006002c51291039500b00b00700200303c0e03601c402038502d01000c20308252900741d00f064000c00750f41040c071101580104c0e01940d444141c07481d0094004409034080140c80950503504050208005500046003200c1682c00c080d20599996080341d06a0b0391303c00760310201c400709440540d4950400c000007415136100b4484190080001c0090386e0704241e4441c54081035003a2400c040b03001c9001c440400c88400420304c80c50b030388842d0364002408010003800788818188221210010400c030003081c0b100180e4401d600c11240781003041c000b080b8007100066060200c1d031181d08184140141c148012031064410b07050107996078607a056406000b41481e018a200440b004000c0314a071207070b151000d0120f80f4140c01e1030006e040030000001c00404100905081d55103454445001d10304205005002c2d140820703086040382510b81c03540040c000d118804031100300720101c682e001014045804018440404015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 258985449 1250 258984199 258984203
    0x10f051306051b01050f0705130806011409010806040302070e0a0f05040602040f05010215010e04030318030f03060b2704090206071a0109060302131a04020c0f0d0207230d0204020d0504 81
    0x10303402c1c3c1e14030312240718280d50b0216400c00d5072140c038501041080703008078054000800024100d220064441c00e80c41d1070701009030300125030044240e020b241582002802c0700e024000900113801e8503c0c040d180a9a0b8145c113100da003a8907031001e40064001c3d041a40080c040050b403500501c464241810082e019410074001d00741103100d05c450005040d0300019180c14010058420210f1760383c644000c50030380c410300400a80500d6115007416981580803500102000d20a440700f01e402d03000404020100d0381c940d044065131110070009081040d4000c5000c0c003800c4191381e10215000011400300b0058180b001000350000008502c550810846080c01540070340b4030342c041812a070340c501000096074800d11000c0d4004000346105030300846a074101005031040c00080800801e036013800704049034070030140205640c000078200c1e0400c0c00c060011007281c80452000300075207800e041101d03444880b5400100c01d0071189440d03c003c582c030b4684400d030245030014800c54660900242c0e0602800c02101e003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 258986699 1250 258985449 258985477
    0x3010e030901090312091a03190c0518031608030c0607020a1502031b0409020904061d06191203030515011809090c0906030c081218010f05130605 64
    0x8a828004000815203880110503500c1c1c83c0c0c083d2941c3c480e14004d07424225604100002880c000c205003840c41008007200449200e800d54030314050007982000b0a08040d1490707490b042030002c200d1940d118040e20000c0000c2144840c4090107840040e180200b01c80c40c0000700306200200042181c0c0101c05000c1448007036050710342d29942c410b400ca80301e01d11b022004054004140d0745c0300031201d290b40510740c0208190003803e05846540369003101e41d00203502061001d030300046c2885550405002e44c00003400c002e0300c502818122031641540c41e02000300600e004410281d1071103a440c1e40040c2c85401000c1220404200ca103481c10000c0103000100c9441084800740c1c2490405d03944036460b040088004007902c40038503400c000b50100039000c00c1d80709035490403c100c0c010a02c0340241c400c00c401107100e0391048104510306050a800c00e64100c1020214100921001140c4180404240c207000000d02c0c1004480d0010001987d00b806110a48a0403022101000c25402d800c05c0c01801a280c4080c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 258987949 1250 258986699 258986711
    0x32505070e16120f050a1a0d200303160804030317070f081b0c0a06180c06050913180b13080409050601090b030c1806160b0a180506060301 61
    0x1e14004150740284250300b0981d1070300200d5104030340c1005410300e1000003151040d4440c8150040c1c5106843c200c2209560710350301c040620784109203411040c010b1341c44503154185038590448150141d059040c03420900c1c030080c0c05a680074402c48080003140e0b070f201110038a040c182034000d5009404101c0c041032920703001542280103011840d01c218034699540728224402002142c1c140d002411003040074451600805071400118042c026032038402008050303114540c01d002054900d1041102d981c9130400131048042200c0c0d24401d000d0303c00034200140d4488544010441c0300d9040e42d040c0844500e06003c030383c04c0003000d2445591840c0100c86403071103a00c400d4641040741604a02c0101030341002c100402c000ca406070003880c3c3c4480b0506010300f0155840010600719442205ca0020100d000202410f801d401210070742c003002c0c03007640c0003800c3c02d4440d101d00030302401007140136044106280001d40e1b402142d400c404026504102250802089860700660b1984155103840c841e5017056 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 258989199 1250 258987949 258987959
    0x30a260304060b15040e0a0c0e030a060e0d090f121a160306080d0507020405150a030b0117070f0605031302120d031a0d140f1603150b060904020c03250507 68
    0x10003510251200d906e0a80103c0d03c0b844c1400000700b0402d038108040c440c148080d81307140d6505200c480f20b600d000b482e0203e0b014404d051080e040805003807020061105500080c40fa845014000070240e0b080f000b50304400100a041015060344d030149864080d0100d5001c202442c00c01c411006510501c030b4509004d16a12010b401e41c880c101c050312100001d0052052801614198000c41c2d0400407a0286424081918000c40c02480d02a04181e0f44c5036100b2004106400e0400b0b00300d94000d052101501c410703401d0a0851070108a203120b08010010080081040125402d0b6800100c590040c0402841608034192a032500150455a0003003860040f40e01c01070703d4005c0c1c40d03414208000300301800e4185255035082540e034011600f400c07280300e07140705003820241c100604c4200e032049040b040303003551030740c60301c0254003004405540c111820103a4540a6032921002e8a070840c00481d4056202c819200c54245940240b05440241d40c4d40303000310f126080c00d04d00e0600c5e2514054400d4851042e103072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 258990449 1250 258989199 258989239
    0x606140a06120b0429030f07030c09050711010606020d020c1804080309030d0c0903110402070c09021602090a050403030e0304060e0103020a110616020d0e030a260304060b 75
    0x70301c00e03500801c4007801d40200720308040e44420007250004100003080d0018403803031224045420344084072440e01c58008200741c5410400310300740788480d00051910038296074070051607090510503080c0c991f860718081081c036402800d500c0e0b480c0d0a90802080815500e820003075031044072030b514001500800070800e040742040d4003500d09205007581050300a446540e10b0b18080d904c02400100c40c0d00003800541210b01041c010511808104d030703508034026041d030406841401802100c544954410011000000c02405058007102c00140d401070303c600601e001c140400d1207140c4000d50000d20351007048042d0b0350b00d90115010710302990b000c2188064114000b50f4a10031401900041041c0303511a62a40d846600102484031441c50306d03400c1c4074030750021300d840c0100955a514018030005c518860140c1e04100d04d0f0b081c65a64540a80149846804203031190b0f40c0d0703440074240821514800d00c2c240207a10704501800340c1000103e95a01d13040c2448401884800340051060400d080d0041c444242 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 258991699 1250 258990449 258990469
    0x7030e0a050a080d02040506030a0203010f05060307020a0b090304080f01020421050715030f0504050d030c020c0d0f0602120f011505030c0307050d0f0501170f070f0b03040311010504060614 83
    0x1c0580240300409454a42c90030302d410400700200c0d032135000c01c004a9180c454001542c0500580240562a13505007007894040c0d50300ca4000d28020641481004400ca500041c80c001244d040a540036190f103540c00500d00b94815038000010501c10104a402c640784158001c01c11101e503640c0c110008825104480341030080090060304079406002c0c1881100b6a00ca00d41420650740d0400103030706800c400c0d040055540880b400d481ea500906901217100d81c01d03000b090900c180c0792011701052011000000c09840101c50084c01c042d000d80c03010420402550f048888580342d80c81541c0043c03411403480c0c4112202401030008403801c0ca9029000e40380200e080e41d00410106000c9410360307403400740031103094002c103c6500c10a40c4560503640802c0705445070501800791007644180b04208541000d160091004020b036640c0d00c440010070800e2001c4224009440701d020940c4d940e43c0b16030a0445034030b62610a0710986528010a200070405c0e5548800700703c8040904941042c440f42080040d5014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 258992805 1106 258991699 258991703
    0x31902030d061404050a2904020c010f0b010909020403081803010f050108030a1b021c1406010e04060c031a061b0304030803010509060d1104150e0f07030e0a 69
    0x420340501e80d80155213580a0109051007e080c6181461900c000309246480c80e05485060b50350340c041302c60700007010000744031040c41e410081c1d0042120708903441c0070810a400000f00c90980d402940d0440c2c1d0021001c82c10400d1140e00311040314040c20444e03600d5541d812000060074400e00c5003a0190510700000c0d6100c4000d0b40b070144c0815070241410541c1790500d00c4610050307644030440d041c010404c030452803592506150521840101840d4016203014140001c590311100800315403007180100c07414812080181c10a070100c2c2c8440349000e4003145480031801031400c00d5402404c00c800303100c009030b00b125060040103003140c1081e04200d40486000004005915003046059001001140d202d80405203690ba208520410744403024041c2c0c4d225400c1c92240c016414140009040c480c499036400c2c174042072041070201c0d04441a501003850081504107850001914504150b = true := by decide +kernel

theorem cover : BRFrame.Cov 258812949 258992805 := by
  have h0 := BRFrame.cov_init 258812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 258812949 ≤ n) (h2 : n < 258992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
