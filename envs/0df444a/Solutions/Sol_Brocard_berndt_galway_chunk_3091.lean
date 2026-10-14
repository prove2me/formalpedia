-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:38:07.980112+00:00
-- url     : https://prove2.me/submissions/9e6e9b51-a765-4971-a59c-f3673fbae6a0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 555755395 ≤ n < 555935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 555756645 1250 555755395 555755479
    0xe060706050717070c020d03081e01080307150e0a0b09070f030b1611100b010e041a1e0907050a0e181602030408070e07090e0906040c06051305 63
    0x143c080024810038103000f90141d055103a2a6003240d8a9460407402904000c40c084461b0209015040b051340c05031001b82e40c160403081e01601240ca144081c4c0c49070f0810740c0041681070804c601200300003002200e042c81004a0b9400321000ba966031a00400a86030b604074a020031048141440002e020384001b100e204140c03652450650ad06010480b0f5040c50f000340403094402c0148030f036000003d00b9040c00001c254545a28442000a18481c08010706101140132840810f4176507004100782c6031001e00342000845055001c0c4011150030586451042100e904010000d5513203800c07544d000000c0d071520036119460300c001502c480c404d280b001035200240231501c10814880420051052501004083d40f400400300180d030307a40150b009500990704030ba0303c244074511009600c164880c2e40c62802444460b6034107142c04084809595480b5180c10240410050160740c4411f800180a240b900f24603000c5100d2008504a0903030142c540300c0c680340d201111990200c080d80b812a80c0c072108be40d5280344c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 555757895 1250 555756645 555756647
    0x60403081b07030905010801050607020114250b0610050304030f03020a11010906050901240302040b15040905010311150306011215121401060b190203130b1b0d0903030e0607060507 79
    0x4c06584140380c00649a00c0c004109810001d0554610540c1a1225071038114100e02038078041d00180386184031240c039424a2100381c1008803071559424080c4210816905100091000c170405980c840c002380a010001d2200180d0301020740384d00202e89140050321024a000210784803940e84031807100340c1d802d00300350341c003840900e5021a0103001040000c200490001c403209000c8072404000c1d801c1c600280300d0400141c00d241e000720081c40c00040c01c0310603400400d24101c060f80c200742c0041003000d0740d440c0140100601c55000318440e03101140e0000c54091141d140c45180c1c40001e0034603041002609040b01c5003801c580000b1141d0095142050000b612001002c240060205059600840c404088080b488061040d00b0598041407200ca1408200c0c00e0000e4000311071240c0001107100800c0f16213a80b19071f00450030007800711042115070b5040050101000c2d407110b441d500c906500f12820840801d60021044011a40e041c2400061fa03103803c03000600d1030150180c045c1c0090b041508102030301d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 555759145 1250 555757895 555757907
    0x71706041416030c09061704050a0209100303020f031602011d0402030a0209040f0b0d020d1505010f063c020f012c0106030c09020711031c030f0b03060403081b0703 72
    0x302c4050780d0800c0f100342c401d202154940800e1242c0400304880d00c08001c545042001041e83c0640500c044408034041c2d0740c049945031030100c43c076000c04aa011070078800c241e418025280c2c0c010b5920001c40c1000f507030001d070081c0710300c0504009040c840740345401d402c100d00c112209011050000c2c0215103c0c03a000c19601c01a42c440880d00740310300d103071070301e09541825540302d42018031001902806c1d0f42580c982c2480f40c2060720782d400341d0707185590f9144003030854aa070103528064035829600d00031691400e00060001441d40d08002c0e00382c9511050540005400080c21911716030803964040807400d006070580c200f400380b4410b9a400c0d402c182c504040c5000780d01c450340c0b1014002c1e0740c9230309082d215a16a400c9a0325030200921a04585c5810490851203030050440140907090304112150a40002846d018000001c40d0348004503d8030404120341502ca0114101c03004501880380c032044200081e00c82d24000c00c001c1c140b04c0d0306004141c1012484002181d0018811f0120741d0740c540508000e081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 555760395 1250 555759145 555759181
    0x21090d020d1b1401020f0d0315030f050c0906040e0c0f150c060105011e08070e0a12050106030204110f0306060f04030203060702070e0c0f2a01060909110303030717060414 75
    0x2064100003000f185510000c2c0c550040f0761080042c2c030b03000015801c1100608803940d01030600301000ca101001185c010f070100001c1c030384200010102e1003425014018260002410184118600442d6055089010078400140201281d1900c0840c2c5001c001607920003450614a0000320041800b00700c0282c0042da49040e43e60981b0741c090110940c040d861061a0310a1076100090004070204413003a014014540a69000400c0c1030b89a0f5290306c0c90590743802c915281a0b6140c2e445810810079824a4882c031950031000d0b04031146440721505003443c3d40e1101070002c5004010010f216421180c00c00c054030081c650040c20b5074042d052441000350380c0d61b40c0b80074101da0300c45d900001c24450911039084902100600000c04d040400c05010f141d60328850007144002c0392404441c0c0d020341035083c0709038030140080c0365000841658900b4640701140308812900e00990042050256041d000306091891080c0454500c1060b9164000724000c1c040c01c150108142d01c09000340300000c40c40c034002240d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 555761645 1250 555760395 555760409
    0x3020d0f0608070806090a12300e030a020c010e1201050c0318070f0e0618011211030d08180c030102032403070b0d02130803040603060821090d020d1b 66
    0x1410b03a86440e443da460307060030f0b071b031000071540b2603083e05000418514048243c17802d17a0a101060404030300c18030a00e903600c2c8080d280010001d240307006508805100d000c0e0900200d130000d5041086824029540701052540e080c140400e01c020100c0941c0c42d05840b0015000c038200034046030422a0400d0220b4105442c01c2055900390850017481c01c2c00065040202c035400807103070340300754540107843c2c0c0350003806080641c00554000d0402c00303108100500d64000c0c081203110a92045043c1810b8080c140b5446165210b138009035180d0522136405600fa540214000d1054680304a501903080e107403640ca4140d035a0154004000c01c451041d450f0824445895000071110051512004141d01c0b18281d020300d1030320503024800b2a080303140d203a010702542e500150741a101151550b80251441e00194480300000783c448900740003820b02884034203c08040715580c0d5171540d2800411184500412034954001c1c81508808019507403000288070030250001c0e03622200d1b04802140500300c0e007007405482 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 555762895 1250 555761645 555761653
    0xd0c24110d0b130506090406050a1b080106020705040525050c0d0f09080d1e030b030a08030109060b1815040902030a050405010e0a081902070b1b070e0105030a0f0303020d0f0608 78
    0xda20205004283c41850010a061b0342d03591540e03101401058060690000f60b656540c2207c0351b1100d8130911480b210780c41c0c464412a6250803c0240f601d0002d07040300303005030304003410300c1002030f044840a001002114005990079000c69403c4406015280d903c0e80320b4880c2c1d0850000c00c07600041d2010205095035203c000304ca481c2d00040b90344200c085503a50000d40200c403544501c4106003101314800045260115110b1604c000103441c1403000e030760a684ca04000030040000341100d1080c0c60040c640401c080b4107001c42e40da408003111200d14030507801081007001c110100c030200c000f02d80181001c50400c5440f03040a5200074001c12003118103e07029803800450010b520742c0051500203181e0700469a52030890b14048606036060740d13202000075481041000b04039001c1c540701074080c01e0345004900d6035007084136107201d1500d581588000201c0d0b490000500c0b06407008242c1001043e00100a41011a0b062404500a01c59a10075041042c98000074040aa515800c44801c07108088101c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 555764145 1250 555762895 555762919
    0xc020604140114070f0b060a0504060603020d0c0e011b05010908040905040201110f030a120e030304050f07140a030605070e03030d140f01210303020721020d0c24110d0b 74
    0x10004070f00c01d01c1d5001e017902001c01c24140000e0040414154811b00151030584581d0780d0704045002d9410680003500420340208010428058030304c202e4883d9003191816160300c2d00c0e254006840300496240f481441d002a8810209002094000c20421a806002c060fa202da4580d0990002c01040e1812800122080ca007000e4007030380042d601c454030b01200051803030240e8151094598913040b16010501e0350b142c5401c00c14820040c00510311072400340e4043c01d401c055201940d070a0090702d410481000b4040d0140ca040d5071a8025404107a03680200b002400e0b0b107928005840000c0c0b0b01001580c10b100000312443e10a0b001d4004251401801c603000c0890b4544102206401071700740603500744212501c070a1202d030741a40300d4040c5403034003d050040c68601140c075115811020070503041c00c0c0552030245030400580c10010146005801d10b000040c480603541c0d08441c0003025002c404020782e80c52010308111404d5445040c03d241814091540c1e000041e044002400400342403603c5040d0075420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 555765395 1250 555764145 555764177
    0x121509070305100b0903010603061107032d080c1201080d170606030c0901090b070605010e09390604030c09290418020402070b010e01050616060504030c0206041401 72
    0x5030750288108800404501d1300b00940c1c0541e5800c1102c1940c2d156403108800008602d51f40f0614254003005445e142c1d49810600300502400c402a0b00d403820f05107200340b254000422440e46030031848007458100d031180c032102d40340200c034040c1103250a000b441c0b00d40001201c00b0009005601c280300b0b600d54941e000305240d0000c159860071248a50020340c1040001c81045903900100459001410600c1c0c290b40c4808210080e80c204a904494182d074402c0140a00040d40d4103250380140380d04001c140a691105c1c985150300010018030f00309082c40d1109842e081080c24189400076130291446446555900748803515550701e101d0310000324580050354035160303043c00e0108010110708030002211942c080c05e1000403c4a01400c17025130425a00b070400517a528002070a40e20f000301030140380c40d4141240482507810691186105030820000c1100d1890721441401f0303004d0704440e002405607030350b040503151503040880007540300800040200300c8001d02c0030300401202c070a9032500c0b1401d150800c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 555766645 1250 555765395 555765401
    0x306041b0905041506020a02190e0721090f060b0406050424051207060507260702010f02010c0c0609020312030412030b061c02090a0b0a051c02130302010c081215090703 74
    0x905c000507004243d08a0250810080b20b260314041c3c002d071110721039641c081c42c0c00c8946040d1024000035108008a580040d1718100c0070500b01074003981001703041201c0c4e0f5500720590343e0700300c020003da80320b00d8490340325030701c40c1e0045006090142c400e001c14400350f02c2010440b050b150183d0040301d101ca5000c50315007400e0070000f1030a01e00c0802007100d1410071905440350380000710700b140c0c202c10740b000060102d41c040400340c1b0711600601005884260a100150001c4103003101d030021a8985911a4400d540c03000b02c0f00440c0b5000360000606012038000300b82000101c2140f40c41602000060208100302c10040c0303040350380d1a030780030802104000304001c402c2c491300840780c0402c1100320410204140b41e0b8028066584000c000c1540f0580e00c0c0784149058124102c014040f0307401040c0185424400405c0f500715001c141021468001a4812104803640c00e00000e4104151070100381300f000444022203180c0001040034101c1480c14001d203217401c941300d074a170134026a069000300b00c1090180c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 555767895 1250 555766645 555766649
    0x314010f050d08030a27120314130305070605151f120203091504060c03182109030b0c070309051804060b03150c0d0b01050a08010b0306041b09050415 66
    0x200310b800b412406807a0f1101c541c001904102c40d481e82c80d1103545407661500e07252101305178590300003281180c079410600f03d9041c49801c1c2c0418181020102d400101100f48096030148501d903801c000c550807408e0032640c900407200c009181a207044140107116040c80088180540d0840c0d03000002c95200c01e80e41a07001c80601d030a0042003004207a41d45400007a0059035104e40a00c0c115800040c1c0030040d9041208140d806440090f0b940ba1040184e0b6410b0281412030030003e0314100d81d181060f602d060060318040d6407085050060040940c401c1d201d104000300a5411410407209410309142c003900d1039200030b004402003a5480c1c0e00165504020881c0c56030b10390000c1007943e0703682c0c0303546448000d0006030710155454003c2e101010003030b4182d409824011040e146400d40c81d249030704000c5e001c403811164180d060013070a0101c0070700c0980c000c0d403090644040b0030b80981c40362980000301c0d02400c3c00c45450602c5013080d41e1500f130519884410481144d40c101d4043c442d41160501d140c940305054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 555769145 1250 555767895 555767899
    0xe060108030403050111190c020d021c020406050a0e06060c0312010906050906011713240e1e0604030e0301090204061e05060903030d020f190c030f05040f090c02011b0314010f05 78
    0x400b621f084103a0091089955560010f02003040500c2a607000819030f003842e1040d640703401c002c40260010b40c200361041001400064a20880550800c002807590f8007004060a01c00d44000501c0d41c1419014400d0751021607800003a0300082d40c5800c0c034880903103500c0c0106400781c041280019030544c465008282c0b2102d244250078903540713442c1d05000000103c5501641e00710420f403030b6003507401c80c2d014500820520b98400000e494040310195400d02031404012001040042c144040c00c20001c5161a08241d050814100582d621004030f405805070a1012798840d203003075800241400c178010f00f1145503848102c034440380da4a6900b00026801803440064060f03000380b0440c4a8801c19500a01038886083e03561410021100707111000300302c03a00038540006284130800c03010150881e82e41204948903040c07440c02c1c18207020391000490114070800d0003043c0c44240d0401182d00070b51000340c100440303555084002d01c2d41c0b0009405000b0306030b1050785400407040006a00840310380220252080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 555770395 1250 555769145 555769177
    0x1e09090a0e011e0605041505100c050f060f0702060703060810020703050d06080c01020f013b01060b0306030f0f030901081008100902040c020f06010303120e060108030403050111 78
    0x22111184018106000640c0c040d41d682d000803041c0800c0003011120308691020f02007003076030401e0107100594030950581440305142c2c00091000756504c0c400500c055105240000a184182c02d02c0d52030104148042001406040f00780030f0040c002d92250362186000342c003210388a480749030b0220704681c498410100b0a40040e191030344862029001480c0765402450304606040c40314021504480b5031340c0c49007045500c850324402d81940c050003c8090301c0035400082068080c2031400c120454420f140040d90485050740484000200c070030003100c400d1254008000d0151070303100c080c015a100740c1d0400d110348500c00551892010000e0204100303200c02020b141022820f400558040c1400b8100d104c003003840d00004a03150900b002031100c40c1083d03001c046041130181c01400b04450b109090042150419030419100000020b5400d04503030741490281249540014400000c0020840c41c207468011507000080500c40000a130040e28012802000590091162039546224071700e801102014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 555771645 1250 555770395 555770401
    0x150207050111010e010509030405092d0a020403050109050f010b120a0809061b1027030e2b050c060406020d031806110711041e0506120d051e0909 64
    0x44a0600081d0000301c040002c44e8440707001c040706081d21405c407a1000f2a6202040c01c1055142031200e058111030406106030505c030302c0b0b1a001c1c0c8000c0180d0400d121802c044404180740440705d50458001310340040c002c0000084926056444003040303020203c9541c02e1400d0038203a07185c00802c0c00054108803000b400c1103c1c942e41e0366051a00010441503109030b05100902038440d00704509040e0040f00d001518000c0018502d20003100d940000286107612507448000500711003500380080190541018141d202c00c800000e8259450000f084500007904078480b171061654002d07004074184254195150340400e07074203102c42800b40d0301c151401640580b4507503120b140281d111000140b10030301005a9160b0a0312002c050b10f40a003d203d070002070010303080042c80408034092a28140440b030501c00d8a40601171900b074102c5114501c400555180045656640c50715031140440c030710f0005840d1810b6001c0c20141407a085070545040c000100180c00500180030411903008a00041445469072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 555772895 1250 555771645 555771647
    0xa091409030301051c0f2907090506040909020f040f0c110318120c030615011101060b04210b010e04030f0302030417030c0c100e07080703020f06031e09010c0305011502070501 77
    0x1440008046e034002004920b01404503140e003507a225456900303440300203c0320070002e00f140c41b0007008000404009084009120301d42e140e004940c00c49002040101c0d03848181e00001d00303203080e00c030b044541c414a03007807681d400710340e00b07802c080d48240039074480042030044014019264845c1580b0103050884003022180c035803601003901c1710368400712004c80d090300340075402013441d140003035a08504030041c191101125607070207030205201c415001c000740b14443c60042c08803854052401420b614051551080e49610311405038981038640003001c2c0c2c0328a581d100c81d2890911000e860a0300002d80b5488810040d0f4064000c4a0080383e00914003180c549880000d2400c50700007400c1c41607080800c1050086204040144441c07184444100046150081100c2440e11070950300c10b101c02d4004000420140c0e891100b07044000780c090742c5040c3d4941d00c0140d4241d400c0c0d011059109001003d506000101c4015030085200542c2030f2002c00030381c0d80341c0748010040302040300f03400c0060380105820700c215 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 555774145 1250 555772895 555772939
    0xa021c2c2103160b040b010605070c030b0c07020a030b010806180c13140a1a150d020a050c0607022109061902280506100608240a09140903030105 64
    0x5603400410380f82001d109a036082e04042c00d901c0140d8068203000c0901c014460f48281c2c480c01011a4206946818829951105403c0c21848054170030050603000511516000d8100c0300195402000c5100040d100d150510030f03040300b030090340405d100c0c250010399508140004450006000c03002044105140010064151201110446800d44500580740042c4403075003024000c00c02c41c0e030003084102c030400d000e00c00e102d500e42c0b129208680112403400c00c0c062840464810f880205c0001d641c441d500901542c0c00e01c5021103e81c01807203500c0402c80300300c1d4080f17803420044420071200843d1070994900d5200e1030164111980c1e004c6400c01c81c421925004940803400c81c40c017401603c0d0342d4407195956641d145c0c5d203595601d086540d0260301c40d00308801031003060f13484030180204130050380c2130100c02040454000c0c801c059641c9801d99115032408488210320042800500d050b04103030b150002e19010740490320b42d10320702c0c0c40c40e440494096480823041d80d0503100040c0c0740c10440c140e00d152003402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 555775395 1250 555774145 555774199
    0x9170a02010f021207020c010509011d030a0503040609060305091b04020d0e100905010e0304060807050a120c091e060f180b070b0709080705010507080a021c2c 70
    0x6540d0b82d012421050341e6240050580d0030000781c01c072001840c0030080030341458501c88145040000c200301c15404ca83e0015100310301c0302813101c0404d43c04005ca901180c907140450030081c05a12000c9400101c0c0c941c0703e0003c8041d42c105035002d108984a50842c240c0c0c03584c1d0686080080603d000e40f0000130305099016100100340074801150740e1b0130080406060035540500b28280e283c540c0180000d0003400d01446082d42ca206000b03500d8280380060080c0003030b2010749020200000081d540d10140c2c41540b003d58241e22104040184e9990f00341d01400083c4581301e8042c08044604001e500003000395503034000c86100303403a429420246030404075072a00c8041402c0440d921496400f0071700c0c640c0c4001030b01155100f6050159203040076040074051641651050540f50b00020040c00300380d030700074151080d41d9807000815442d609214001c0c0e081010a07080382943d506112181000940c1c080041c01e210f101c1c850f01441070300c6c40aa06c0318400c10801681d01c1e08414580039a05010304240440a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 555776645 1250 555775395 555775397
    0x1c05030319020702191505090904060b12010609061a03040b070f05041e090b03060103081c0605040e10060609053601030605010302030c0603090613020a05060a081909170a 75
    0x7150a5031035000a222258022507001c003480741c01c0042c0055945451b61501400250910b00c0c01e210015001445405000744002c09181d12030040e0140c6032134030550328011071003540c0280046500d40e4501c200a0030f0711320680c2354614400c128035211034800c100f168000d80d00414900c47e640c0e2500c10650300320b003030300f41c1c4841081820800014160038031080140b02044482c0f0080300c3c1d916101550f02502c0c101c80b1810312903001800108005042c034000c4651201014141c00440d07031704404400c00a0207198003141e0803506000343c00461000206185ca0810001e00341000595140c440866520141c0d000b1241c101c0c03508070b48070020202503080f40d031312200d0060951000e43c443e400650320680081c1c1c400c851b500c0e2903100600461070148901803400308141c0b80181035261400050755a244050541800184885443c609540b90900302d14007510000e08096901e402d40b00004001c0070048030303824150b8043c400d4803507000005004034000c00fa0800c1d9415810f10080207030025650001d03000034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 555777895 1250 555776645 555776647
    0x610050a021c090f0807180c080112060f0c080603060c0c071a040b04060216061b02010c060e0303130c290a0302040f03060c02010e1f020a02010207020405090c1c0503031902 76
    0x313031041c4488200c02c040d0100002800d125031410400c03e80320583c03c028042103509069059013000d0703001d1a0750381140c1012030701001d40911400c200c1d000340400060108a00c0c100300d00d01c08910340200700030f03008000a8049444564480d010301d00c5174003c001c0b40300c50315048100c00b0000c9200240e5211035046406031024070300742d980d11084140381d101b07a20517009a00040300e00003030344000c011407130014501e50800b103225540c560100c0b10600c0382098000e062294074103240301403207026400b0b141d80e119600101da40c0c0b401c01d211100011040c0c584221241c10354808041550b0452048820480000d004102d01200e4109001e010740c0d000f0079100d500300760703007030000040c034035072000100004600855001034580d0702400d0090030344590012201180c1d1188035900391410142d0404840210781120058039044518003ca02a109401d80a5400390138201030182003030011403d4410075034221f0703a1061401800c4040e041c03900700c01d107014190b50020700018601c00307821241e591403100304007001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 555779145 1250 555777895 555777899
    0xf030e18010527100806090a0512070311010606080a0e0316030509031009030507150c0c1101111501090501060c1502091c060f05090c0f0d020a0509010e0610050a021c09 74
    0x41503c0c0441201c075001d9045101c40c040085407010301046402c030b99428003800e0710710500e840e40c5517038118814405508800000316035040c980b06030340c0c1d8078a4040030002441a10f070345a5005004200c155400583c82d403030000e40c0c001100000007128044030900d61042940082514269581d8020200c00c6030540642c084c01c54400143d4818413580310b119440b42902e50006040c004800c00c091124040d40302c0c0703000040440ca0b900402d2416090754401120040c40400d0030049034805038880400d84030b40720f01207410001e50201c514080c1030b240d520b0000c11403a03981d1030044440703500094000d80f5206400b40a071203a00c0e06034005103803101000c3c0004c0303840400f00032551003a400b458800c0d904207980b243d150003a1110340c042d554000009100402c1c03400140d00000320008002188a8810002c102c866011521004d002c0001050000e09228a56070350350154185000116442403240d85010401d00c44179005d503050b622141c009170300400d03103032691480c054800300310900780a003440700401d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 555780395 1250 555779145 555779209
    0xd060501030f0221070e1002071e060c121809051b030f04110406030210050a0809240a0b090907090605041a0907020c120307210c031b08070f030e180105 67
    0x3401f4112000e0303009104840c9003642108080c02d0b01000602140c46a500c10000d03687c0c0070428401c40c541003500300f070301c001d01c221054503200410f8180e04a02c95860400107201d2066038419849580820955001d4108a030a0078242d44401c80744400700709507580106000c249142080c002e001409000050381079126000264a03000741999100000d10001d10390b1000ca40c88072100350440a0800208881d15110b40440c102c0c4a40002800da54041100002c20750700c8140c01040d0103c3d800b900d240168100401543e89030300b00c50040340582c07401c100c800959400c1500c40c4444078441d00d141c0a800010280802105a034003400e0a030451140c1d91480c04250f44900b00302e0101590b5000a6903100c0607490040f000c0c107541c2c440e8401100e00d000540e11200d40143d40917410984c5840c001e01840f0032201000c42180001c44013809403240482d108040206071403007000003034001c2d00ca20510f100101e040000141180d149801c00b404000700400060034407803114506036613054840eaa0000c0c6500e9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 555781645 1250 555780395 555780409
    0x106081b10020304170709060e2a0f0d061a0408060106080c07030302070201020a0203010f1e0b030d0302090a0e0a1415010905010f0306170c090615030103170405060d060501030f0221070e 82
    0x800780c007460b020340078401e8005e00450104ac040d00084415002c011907a070b6150311500804200c4d0130400c000140480c440070300c0d640150003030440b40700c100103c5000b919040c115600280118205d81c42044004950140203a18042c4180c01d4800502c0c034001a41d502180a500064001c0781540708948010300140ea007070003001c404400c607480c00540241400225032005c40098450000c19140100c01c4090f0786000c103984420614505001d41d54441c1c01c804a01304104592000342c0c0310046109000860300d10346c00c4000d21103050b560450b1903803640e411307100381d030061a18681d01291182008000c5940240082060030780c0c20300b40050640d0344c038010340c0c0b000c2c00706481b00f85103600704500019151074800405a00890103450074038513030445102950440c801070202822000104008100184800003100c0140c1805015951540f4840c0310b201c020345180d0242e80d010030b00f415005030a01070203100369002c001c02e0b100c00401140c0b040c2e07000f02c9401c001501110402128a0410030140c807a81 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 555782895 1250 555781645 555781649
    0x312020424260f1302030a11010905010912060504060f0617010c020a0c031709060d0209030c0303130306020d0e030a051e07080f16050106081b1002030417070906 71
    0x250100c040c2556060040c1000d030102c120805690b0200d440c006118000114641d001d08005a0034695480e000b503d07500030052800004e52500c200300900f003c0266081510308014001c2e25103e840c84d484000649180005014051080c017800640c14007268035a00400d400c10302071400080c0755400120b03080152225034100702c8541d80c442a8000c4852004d104104040c0e00304d1000d80f00901642c0e0f515036410100e4030001e014000d10074220600c1584042c2100c100b80c900802203030303540c0103842e002c4020b0340010103114442d000e1480f600f405414084200d0711307040c008810700c0003424115900c0c00020b411008120041035a01c19401821500030401840e0081072a2101525003079181009485d25200451444800c2414801c407000140742ca02503603100404609519100e01103003400c01018035030010040c00d10740c24280000740e07884c8042580030000410300410003901421006110300e0500e00c0c1988801130b44204002c02003600001d114143c00354041341030f42c0142d43c0e13682040d41076504503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 555784145 1250 555782895 555782939
    0x510031403130902040806070f05130e160c08090607050c12010204170109030e010e010201090b010f150302090604050f0607050f0d081311040216210818060403120204 73
    0x1001a64211031480c044010110a10194901790030f02152a48031907010b010078091120a0303a100030414001c0c0e0a866511654020700f241e00d80ea15004171050200a847d007a13110403060300642c40c014461480a00115002502c40c3c4c0f130402500e050050690081c0b5064511340030f82007541007641ea17000506183c0407074000025848074188503100b03820780c461181c9402c40e43e01d402d5818000075048615820000f400b420310b1440d01c000300700140c1c050010f601c4020040080000040340403c3c0c4103280031b0569004006840b00107041c10015400c0303209444d511540b19406000c200224941007107140102c2d4405440c0c28103040c0c403907a800e1702d0604110b800074066000644118040380c1c0c0801d001d0f5000b44103144481e105c802d140c4401c95010000b130b12981c09036030006801c0072034080e0b2080c0d4a4086a102c40018480b0400d0300900104d00d5400007001d000842c10381c04610002c1440c5001c0300c4c0c03401c04030041d10f040d840c0c41c0d0b030030340f494485910014181c035001c2c8000107075080400040d074400482 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 555785395 1250 555784145 555784147
    0x302060c0f1b0f0d0c03140711060d0e01050604060501050f0a21090b0601261f030c030b0711030a1115040303150e01080d110a0803040f0b0a090b0402040510031403 72
    0x20030010f0303040c200a000340b0400c00801c0071030314005c00c3e44200c86c0004d2928100e00503580d42c50905100c81a20246030700ea50f04408006035060507240594003481e800e00c0800000c04c42070f12240c00300001d40d1203501c14140029402c6c0000860103140c80001c084442d5035080682040d007240c4149112691754541841d0a0740d41c0390241d40a01401d80c2030298041c9003442d00320072241015800c000d500e0118a4941034440100380069008442c61041c4807040100f41e6640f00c03c180c0c0ca26003401d0b50120360000700c07a0006940c01280c8a0b0b4010301c08800a00484005541010300f0b41000302d0b0034006d4106800b403d803140014085115444420660160b0700950f008286464403440c10858504598801c8410f030180c5401005540d0001c101960798030142e107015010b84006c09001782c038049c5152000b912401c000130078841001200820001590b1003207030a01c001d0b40d103503410032003203400e03555014260020410000d401803034564481a03022540341c884455090b225194103464002c40c01006c04944c0c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 555786645 1250 555785395 555785413
    0x32a1407060516030f02120c210901090b0f04050a03200306040c140a0f060806010207080a150504031206091a030601150c02060f0c0604060f02070302060c0f1b 70
    0x500c10400641842c0c2010392074103480800d500d1000002c0035018081125420141c19403070320031b118000c4c59035015080140c54840c0c601f407283d00c0e03400080d00340040d0781c1d1210746c02c0380c00002e43d400d885503808161141c0703200702e01e0400c50460300e0f8029295071104074000c01c000306480d43c2d40f001ca10082c50003080035a00340f030004440781c4005180120700c0e80c800e034014000c020018510502d40003da481040b00d12201110020120b012208550000d2100c2c4042800210f000c0364000c031420b221354800d03400c49050b01d680b2040251281d80d8104054050702c5102c008240c0e1010f16000035400c00d2003440c4c00d9180c4160050440c040301d28503000304115a8036500700000112902140801c241c03402c030082c25440d450320104c00c2d2010a041104010b000da01d01c2082305640c4c481050b49c819450801c10640d031000450f030304903141c80003101d04803061440c000e42200141d241303201790760a1540c99001805c1c6c645079041d004080d034108042156400100300b0401203401c0c01d54801c1985000c0800003401126 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 555787895 1250 555786645 555786683
    0x15080d2d0f0e010e0f061c050906040218011505031023030c040608030d05090f030301090903080a0509060703111b060a0501120c060305060d021507020310050c07032a 73
    0x201001241410403130092104109941d422908409400088a9a0b55140c00c0384000200c1000860301c080180da24190402003250360120701c2c1032255100b00d90510300781844204101130b119003801401d18844810500a1000f030095009541181039055200341d070b55070744c0354014802103405030b0f1a01c610828059518541c142009100d0b000c440841e01402410305001c0459a20701800502e058001c0e12580816031141c014070001d034024241d2000d8030341d2580c5402602c0c3c090840d80904500048a030000a29002103034032509014003090350140c801501c8011089002d4a49014509281c11003080318100b5000103c000d5000112020050240703403a2440c051011030744160b215100c5082e6840f80400018540150304080d5400c42c1000540c5840b0170002c44c01d205e01a00c0000c7d007088012100214208030b40002e051124070807012a09241d07850040d20081d62000e9a0441d1011000d200a0002901800e01b161040c82401c400d0100401e1301c240c1380310566118441620300340003028404200b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 555789145 1250 555787895 555787907
    0x181505010b0406141305090405030705061b0301050f1504060e150403020a0e2e0e180d0c02060d052e050f0105030903070515070315080d2d0f 62
    0x4080e000c0441d410146000000b8003211400d40000b1680d400000300e403059030315150010390107000080c102140910b040d24050342c1e00c1d0b20010040d5024806d442c0014170b4010000c14403254082030071a0075046034a060140006903a042c90615801107031403091907110328400b00903000624490303460300104014102480802c01001c42c4404031944100000e0003da2203260160b01100d17040e00c00003100361381d64500d030320656440740030f0a400744802013600071054030813100c0741c0142d480300c4440c0c403565150700161030001c003407881c14141c0640043e0311004049015110440c2d01600240800340f410143c01854411510700b2100c00001c0314104c02040d12083c8001a1001d0140010840300050303400c00b80020b41c40c1021100c3e4030b040010000005030300038014810364800d1580f0104444642107641840f00c1c43c0c08040b142d18001900e000507641111121003445003c588292018025050906004486805013040864041152014001500301c070b41c2000c030a40ca803c5980d0601e900c4400b604c001c000e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 555790395 1250 555789145 555789149
    0x20601060906260c160c140105090306010603050703090c0e100b0309060109090201050405060a0804061b1d041d0607142b0f02120910110f03060418150501 68
    0x10010004142e04000701d802240c200584080d00104a00b81d46213000b0310103a101c3d0251980e151200b00300d45d18200049a00d41c4001c0c4c40030840810030207884100115014051b01c1070040d4198003202c010040c542c002c0c1d11858100900f440d0124000c181034035005002c0c2e042c0c0d800200f22903044000c11210750110050702c0040e000f0044042d140d0300300520b2180c1d4400c010300821354191703500e4030a10700310381c0254122030042002424007030300c807440c1c001c014004800032030b015640641003118542c081000d40c07000c108100540c1e101c00e04c5600e140c1400c3c0c50415420420150059a29844000050516482010412031500c0240b107545802d01e0010454a000420240f9410080c4814a0300c190b2103031000c0d081d87e8201100d182112504513004020300120004c16480d184006884100343c80758003002441440c1d00000c85840324828a400c030308071000c001e51921405030a118140c41ea0038035900440d040343c4000d101103440700000520a9904082910403114201c8921140c02c010940380038082c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 555791645 1250 555790395 555790397
    0x305030c0106090207030801030b130c08010f0c030204050112050c07020405180c01020309010905060c070905012c06010e090406020c031215030c01020d03020d0e0607020a0302070e0103152307020601060906 90
    0x705100e41ca030f03801f030004c08060100071318240e11600000e43c440c40e0000288400340d0000307682070086035501910341c028165802c420754260700b4003007100c020314024000c540131141c0c103035101801000410001401003001511382c007207600040200c0310141c2d50754056180a00d14001c6a102e031f250f1420b25031482d20b0100e400d004c0c1035400c140616896a0b0b00000712004840f0141d0340c42d0b41e1090700c2074845040c10030540011a206140c07800200781981c0350a6508400c0da02c0299000400081840618004008854590000d90040c8501c2c40b141810088290402d12401007d41407401c5280d0050868001540445090560404006020505481e0f040b0a01400d0300985000c1c0b143c000000c0d101c02c41c0c59038050905030001200380018045030311000d040d0080c00251140d07410100002034440c59071007010fa0051113960000305180e10080b64040c1200d90248166540c650060019405010b90101e110076100c404420342c0350301400041c000d4071405055018007003960501d100500000e6964000720 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 555792895 1250 555791645 555791647
    0x150903101814100e07080f0631170901140306130b0d0606030f060507050a020703021323040203210d0e0c1011061b0a0c06150305030c01060902 63
    0x107000c0c03200035941d4010a6003005503440d0b04410411001c0c5000da4688520b000d1603c0c02118440300c0c0008100101a00c1c030b24070a07103650801d0700d442e01d503031804103540c03c0c0810800c461204181c43d5140741c80710250350000a20754082030341522020301070480398011580460300050040340760360b8098010030700100c110380d8007419818041c0108080c42e1400240c0b08080d641c0d504907213095600c090f50182c81d1507100c00c040c015580c4a2400b51282048032904952440c14400422081801030054a21000c00c2340e0090410b2407850302044140300103002d281c55965943e003100c01c5d108a51444140140302a104540054100391050503c5c1c50410360104103503141c07035080c00d44004081002c4510711001c080b004111216440802820082c40010b01984012000e550405580d00306032a1801d0941540503a2a103175a139101103481c40410140114840200300900460f2a00a5403000c0000f40100c40000b06c1c42d075003009c0016551303400d41098445900c003056451196009000d03100107040008015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 555794145 1250 555792895 555792911
    0x80d08060d050d2109061b090509070e060415030213150219080405030303190f090b060d1506060903050f011134080903010b0a0e070311070215090310 66
    0x1841e2600d03d03a001d02801c024250b003c9840c0c140c0000760382a50b0301da00c0d00c1c040240880d0340c602100108402c1090a0300c914681402007030850141156404449002d0050360741903a9000701120044000681c803035100b43c00303000100d8099090724003404484503507240103944c1c40390380c2c500c0c502211195103e0a90b02d9000310304216980e60103d03140808002109090440016074603040725207005a80083e90184004400c1103040101d400320f58852200c800420060b50350072100f880190390a00354003609001c0d600c400707d50141407900000200500036207400360485060340080e01a02c4203503006034005900e030403040c014400180a00740d480e600d220000c04c500341101c180c4442c0350282915288800e0000c400705d0440c8001c0390f45010311305102d00ca00c0016903a083c41c00c0956a085461154065031034500032a110703003840c4000c80191012026070f00745aa445410031070192654510840c581c060501002005803030703c0000c0c200b44203411454540f11140102030601d44014190000a080c4c28a001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 555795395 1250 555794145 555794153
    0x230106050a030b0604152604050a0b040f0203010c05030a0c020c0d020409021c0f120305060906040515090907060314130f020105250c051905040c020f07080d08060d 72
    0xc40781803050600700491200b0003d000145503009507441441d42e022242d6002000c03503481300c0e421400750060502104401140710003404107000445000f860341e442a4540000301c0d4180134065030003485860351032030b115204e038040303070035504c442c82c018010070008014000280603900401c00c17400254401000e921a0706000030303000745c1ca0054041c1c001c40d502c1840605545550380d40350a20b40c0342c248450014031081c54015403901c031300725060356000c000d945000c405038464000c650190310024810342035a00c842c1d040100820001e003100c50003500b203034401c6109444d10503c0c5881542c0b002e01a100715450b14402600b0349810b00020400101030388204281c0840a00d500d5a007150007080406212109100580e4142b20754030000e60f020510b800028903a0100398074003585148217100c0c81e20019a10414081c100e220700024080100a0182c180004c1c1083d03030200e5600f001500c1200c10501442d02034501305034150304586241d812580020040701d401030b013416000002603d40801104650701c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 555796645 1250 555795395 555795397
    0x5120a0c05090603010207082d030609041103100c080a0b120304090e07050a1502010c0305061e03030f0c0708161d101e050901050d0506070809010e010f23010605 71
    0x41c16220307030965004610a52000d41c16101c0c0c03030b68480b103416a1060250000d9000350b45800d40c0d0700340b42c3c0d58110b03400000b80b803d2080d2030044401402d052015100c5650301c0f010400e2460210b034042c031445042d032000c089280a0190a80c010703403942c0c21242001c1000c541a6040006103e0069182c0d0b048403c1c02c5100004441c12100c44403000120107111800b610b080c07100300da21031503005401c610040340d000e85500110144030910b800810001900701419001d59100f00c5c0c1245d8001282c2c10300307400c2c800d907255104c941601c0007000e07030340b9041200455030410f401522644555500c446000d22140f1010003030100100e414110461746140b0b003003014100240c0001002c029000701c84081146485000514400351400c8844e0858407060888561803030314084c45124442c48105000040500f40035008410030b80e00000542403039900c4c04015035103c0c001030402c0d26030390340e10051041928801e100b1500085040d05012a115a288050300c89180307022120062900702040108541c0b42c01c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 555797895 1250 555796645 555796649
    0x30f02030103022d0a060f020f0c030c130e06040308100602030c060a020922021c1e20120f070e03061f08120d0c020304060f0c14100605120a0c 63
    0x307000d44c440c800500c1c2500440c00d810a80c901e400040c00500840c0e015008003801d200406035078201d42000b00740401080d502c817070313210111b90140c224401d1070004d4109900201c2411980b850081052000c2d850307694600541158150001882c00062042c000c507070803840c034002c02d010302c019424850b560751082d07150740c400b5120301ba040b41d001449403015110164036038841212110700031201002c085032040690300020030b0304486914030071240883c450307074402c21101c1c49041940d0700c940203d40c815500188494001c4005003a4031415902440d07560380c00900c5000f90b02e80c84194182001d00e106502c20b036002d0420001d02c801000d00c0350750341c0c400040c1c003a80050103800800700d0245410400495002c0d942140585d4002c151681802040c8034004000e1040100741c20807400b05a00c03012a200e0203180109000502c40c4240340c00741302c1c8540c280ca8540b40c001e0b59006c0310022107290042c03400742c015401900c40307034684004015074945504010302182c00311001c0e09000a0b559140c084040c114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 555799145 1250 555797895 555797929
    0xa08060609060f04020c0a050c0d0512031515210609151c0305130b0a090b0904270201171b03040501111b060705041a0c1002130303030f0203010302 65
    0x2010002e02e050365004088a40240040e000f1542d441c0440001a21070900401c25109441004031444036070412003a03160116801401500048031003180030000c50780050180070a40d8284030021400d940c0f150b41e0110034001100c404e41d591250a06080030300801c140b070100b254904501040a10f4803400741c1103a1020084010446820100000030003001909511602481d901c000c0718080640000090100301e55140c0340d8000c80341d40d10320003101d0784a000000070018901c07550030020406080003408001100a20228102114230201501444900f90080e50003641c04200700079075070403c011a903211a8030010040703a10745407100d54020246c0b0004000752450010004003403280c20744c0f001040165011000b0758178201105c1c03c88030f074a540d603034180c024043c0c4004115243d0244003114126121b103082c800c80902100020140c9800201315170f40d482c01501000d03050b000051004000141e01c0502c80302909046080040450b00f856070061840340c0704200600c0541d5034090111585500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 555800395 1250 555799145 555799159
    0x6040311030f010f020d050906041e030c020d030f1107031709010c06060e010810140703050403020307060c0504090e07032013050405030409110a09030305030c04320a080606 76
    0x91902103403504919001802840d442d118081306030080c2d42d001000019010801131043d44c039030260040e152001510004c0210100010454444420000c4c1d804180d010b424550100540c41e000b0944243c000e1500300c1c00101520042544070f07810400c1c140c25404108000c1500505640e1401305c00d8078203100385030801c94003140894040e8031940d80386d444d16512140602a80f036417006c0295a40340203000d200820300503103204c00078090851158280c65940300c100f103207141d280c40314250018800500141c1c11030100700050000314019000d41e010480055070f4090b42c0d14507200c10101203c0d002c00031041c0a4112440070030104020b40d45a201002c2604c4500010940840001e8411107544c1e255581702800c0804000a008000c8041c0c000c840c8511401c1c881c00a803000c0d100c4c0315205d50858440070900924040c00403e100c0e6010f0340d805030302c14080034036240c0c8030701c2c410110b4410a0820308400e070b807d09111425a4030b1002c007201180065441c030030b8082c02c0c20349494480b01d00a0240d4080d0003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 555801645 1250 555800395 555800423
    0x120201090e0423101503170a08061c0b0708040c080a1a0907030203120310050d0b070305060402090406120c0503030a09141c050105040c1403100209240c060c09060403 73
    0x244404e405207480e1003002c11010742421407110303a014480c48140d580501110708070700410400c408884030420182d444680b41d42d140b404000d01c00c4414a158074010100c072186100203503562000501409854070362450364030b8035151550403a41c058100f403819030084098080081c40815440340608118921903602d42d58010410f840d0018941c40a5494846d035100000c500d01014011401982d24400c803044040d15002413000d04143c81400901c200440000600350341c2c401d0b0700164000c200240094600120030000800b0b580c401c0d0008034868280075171807410821030034078020090000340c1c05103050184004008c0d0581910740704000ca440e00d001c1a80c0ca040e6520001071241084a42d503c002d07000b07150901c2c074001c0c0742c00c0302c0454501208090214115010304076558282c40000d0007801c94141111014000e5004608141d400c11362060320002c0c0070240c5540108412140c5800a850301da4010156161500141003084003200412550055807540011901600d401c82000796683c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 555802895 1250 555801645 555801713
    0x1209010203250804030813060801260c09090c0f0f0a0e09070b0a080121111009030206040905071403130807081309020309010624140f0301120201090e04 67
    0x7480e1102d00070714a80c0000307808410012084080e21105040b104a190981d4031a6410f0312584020300494034400320b42c0f041c440ca84500c04100740803228001e0265a001e02008010410300c020560350381440d90480311040b207040c00c01c00e800c0740c00800104c8509200000800200e100d84040d40200c03050032000700001200d24030204119030040c0340300308030f10f5603a071211207008080030801e020f083e1110107101011070088100c4002001080d0b00f040300b054442819200f0820f04031407030f0b1000004e20104442c0000076a03a6030020344010f0030000e41c0420350745045003004103c1468500c001d21100d1040c820b12140b010600d004041242c0d12888041d5100b04c5400d08648038041c5107803042d41840114004660807440703802841c0905107210007032101c1350300d0700d8400c80c00070003942c0842d02c02c000b00035801001c1d9100c2e040003881c0c1002c04601d45e142126240a544241d07009070007101c00c010801c1240021941e0004a1000800d4100321400c0c0c903007096030320101d1114800c030468501d018810300b05007600d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 555804145 1250 555802895 555802957
    0x101e050f070b07050c0d05030a140402130e0f01020c01020c010501120b0f0703020909070c0b0a11030609061f0309110406060e040c020f01090c090c030b060319110304060504051209010203 82
    0x4450340c3c0c17048071080c2d0002c0800405550048400c86511420b008e00045200d030013403200e42c05554010005403c0c140940b181e44001d1247c01c0384c100d000d200300034095200340d10a10050401005090025960703072000a07021b400c0d03a006a220f0703840c00ea154842040850703c144510303504050303030b02c0400c005a10303aa50304901900850240c41c0d8000004d1042c01003c94100c1401601c080c89406c4401055075100319820850380c900c841112003810810000300c0c1450724191260b0b0110303004200140401049400c00050309042c800400480d40c1ca44201b01440700035a400740200c003040350203100c0d07103041800003051056400003841c0129180d6090212b01c0340240142100c600c9280000c001e5480281012030107004103105545010340f80400c402c038090303c80d004449991a000e0196071443d15054048602a04170890318800c044e900c890703110354111a80001c40c0118050703080484c180c201800c0c02810491540d00c00b00d19034108120b900800e0360048103949846000644901015100342c94014003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 555805395 1250 555804145 555804157
    0x60402030706050d0b090903030609010e091b2403011e0321170703020a080a1a132004150c0b01230409030c03020d0e1c11101e050f070b0705 62
    0xb1141006c01045454000000614450709044607100344503640d8005240061a0554601456801090303801520f100600300d81c4000f1140a0407580204400f4468106000600007601c7c19440d80000100308202c0c56042600e4071f0f010b403668007500a0b00d10b54070040c002c0b400c860681941c3c400c403000c100d003660150a1080799040d41e0f9503242024604603a00400a501040c2000d0200e503030700c8007041440f80c2501c036101c2c81c22500c403e020f0b80700b0014020030807480f1400c0c440a00460300c4042482e541040c1c10505500c01c00140342854840e4185801d004141d454812003404210340b00a4980100f58840344460455103210344030700e203504d40300d114031144c04140c000b0140c00c00d040406031000c055005103c808003900907401d554445498500450b40b05c0140050168044119800c90a62650001100ea40244141031940d4040090008074642640400302e110106070f40105200e03030130701c0c0c3c0350346a0b02400742460201c0ca00420030b084a03605001d14900035100c0c4021800040a081c042c03003c13103817 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 555806645 1250 555805395 555805399
    0x50901240e043003020c0d170c0f160b0412021605062a06010504230403030b0f09150405011d270322050d080712030b0a0b1902060402030706050d0b 65
    0x101e25403d81201501030340c840c101c0240b1034800d005c28001194420801001400003007c40c01a940e140d03865034400607004850214908802044511000c8041d10300e051500e0f40f1900700c5c43c500e072815003804500c50429110341e900f036412038003440751003145d080c01107401d0b1a011101e407502c82c95030303041840b10000030301c4030003100c0381c0b140c80c021701a81c0b0002201c0d4102c5008aa0501c03e6a001807403280084078540c5440080d03050420200300068020f8000803140300000e8604001e00d0851000107108000c1601c02d4500c02d410505030380d80a041900501d405018005a1400d00f8003c04500f5078060303100034010402140040c005502070010144c240d504a080700d01280c0c0c1b0703440c8809403c442641c0c441d0f100000710f00c0b0324800041074140340c20502090703030704580000e080034116140d030a441c101c0941035008040c2e40d800c21101555031161140c0140040a4880381c54880092051109185c40702e01e000640d48540300b0440140d50000f99902500d00034900a074035200d80c02e00d08005019a240169 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 555807895 1250 555806645 555806723
    0xf0306040f050705031b0901060f0203030a0c030f05010314010c0201020309070b0903121c15120204050612010f0e1b0609011103040f170d080f1602030d050901240e04 73
    0x100031b21620898084400c03800c803140416a641e80c1d609451201e801c21420000da0800d000040201703030076900219140c4424200840e40c09442181c1c0170480303409800480340d00203240c11442740f081d024421a8040015400218034500b083c0000595602441c45140590440081d00c40019113040c40a14400380501104a40311980c0c0004c020034501c08462003403501d40780c5481c50315180160700c001422030780b80602c18030004900c0d40900c000f6000007800d268000c11000c040c00d902c402c092269161100501d00000b9210008114690515098402003201e0351001d169118030f80c1e940c10203c038040710090030001a00c0855511060442c05103074882031042e02c004400081c5580e8005100c88181b0900080d2400d25031444410b440295058408001003a843e40c0020754940d042c03075500c054094140101c034100f848602c01d10040e41c1c1d0495800c82d041c3d44817200c07031303802d038161806d52400d22010620710700d4424285541001444001800580302c166003245d07d103c040c00c2010031005c3c041036001d8a13 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 555809145 1250 555807895 555807913
    0x509030106080a03020f070303050909090f0703120e09061005090d0b16090608090c12030705120d06050603010311040504030309080d0615020a1e0c1809060b0f0306040f05070503 78
    0x7507520f4080c0100140c02500881241d60007990000c207000e010707030354151074850400311380205000807600d004061040511444112800220302000303020010340c4608082d035a0603450400082460b2400e40da0355000304808018002c19690325801d900c0c3c00c0940d441d05603211443c50000496032a03202d840a0440d0041d4001c0c001c100c4240d120410b4000c010b0f4a9000042e650f90404480c902400c860b0340480342c00040d00f104d990329000741542ca44040500807281010301c4d603103c1e80d04200c0c0e0900d07051805003000446880b43c4080303000d40d2000b8070003203420364195891030b00c3e000b03400101010310610513a40c0308001810180258081910980c00852180e110440c086c601001440107008030090071039443e50348180c841c400903108245a0384501c1c0710650a0413035061214411051f981250000d09501010600c0140c4070640c15041c040e8110100300c181060409108a92907500c0d1030f4060340300300003058865100002c1c141d40003079000030441d010b0499407e2190411006420565150042d101c2c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 555810395 1250 555809145 555809159
    0x90f061902150f060f0910150905030c010f2015010e04141c031d06070c06241401020708011b02060c070b011e091b0f08060604050409030509030106 65
    0x2480710580982c09038420305071100c1181000b184011103505a0220501c4012241410f0480b00d5a4000404410188486440d0510350940c20401c0b46043d0008190300360400c0b00c0e00c0c041020504071007082c00e01940c900a282e20040107106101c0c1c0344c0e001240c1c010843e2a04034000c00c84140080462002c461655071960451165000107990035252a042d58000b000e89450100e401003e54520841c10208048885020f601400240c218007040c1418500310398440c1c030007440154492503656807002e0140f00035240240841c3c040c80d41e4400c40507541c4100b00c203c2c100c049010f00c19100c3e01c1c440d0b4421841100d004078940005a04603400550070101030919407108070710201d080b05225001e0b14050f41d618190311000380103004010f0481c03100c0c07400401c19542e04050000c05070b0b003240940100742c0c0c3c035981030b8400d4943da2039a903420940c58121304900642d0024840745c014001d460158564101800002c0c01406503000b018491a9030719172500806025008403030064a000d0028880c030b40d80e400f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 555811645 1250 555810395 555810403
    0x6071a04062c030a180509040b1b0a020703080d0f062c09030f130e04030203040603110313020906010309060e030903070b12130f140105071b08090f061902 68
    0x10018010072003211102c4450300090400520800480081d418202064012104441144d46140c42009448000b140030f03222036103071500c00c0740101a01149820840e06580101d4011700c80132154050500030b401d80b01c2e07030108900c0101c1e40c010120301d072034500e0364500e20010460320303a00300700081c0b03845000540184401941500c4019424070001b04854403244201e0081040b100c10440350420400c80550905517805001c0060880d94401035541e2645084950b0617819281a00540e101240401c485949406980c0440049240580c00c4d0305150304a4190310301200390080c42040c02c440041d425903c40d60083c01e410360044c00600000c60091452502e980c00f890005000740034012020071191480c400301c50904040010398100c66442e042801304103090410210350048041500c1800319808050401000710b04100016480c10201c0d8090005540242d00391281e00d400802c41c008280044160b81c011002514910b15040c603410024035a4071a02995540941d0301851012780305038001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 555812895 1250 555811645 555811661
    0x120c02181501021b01080a05100e0405030903161503051b04031a090d050d050a0b06180916020304031707080f120606070807020d02370f08060606071a0406 68
    0xb800b928000300c5085800d06490f5130181c200d83c007080e80303200410031440325a80080d611424440c0c800d0845510f50b9010400707400161001c0da80350740082214102c6280502c122408480d0201c100c000c003601e03000c203a08807400d04030800d00c1410340e1f039000035039500c00e42d08540501761886603100369525200c2c90801d41d00d00810002c001c04e803040c0c130005402601c00003006d00c0c02040e02d07110103003804410300e01c0034043e0800401d40503007180c0b20030b002516030301c424000c0d014118102c079a50031001968000e01c400c40700e0051141100070078030302c104581d5a03008021280ce50703410505812540100840407400c034448c42000800e00c1100040113141728072608040c01241003803552030192a100c10301003110b140522000070700001e0342003003264010b14242c5c09030302906101a04940307201c09140300303a40800c0b00c5031001d0a80d820071002c0461081480c00b135280050035201e00482025030038205003035510350300100894050100010a070081c0b1079070860403403014070416540c20007441c0501c1c001010700801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 555814145 1250 555812895 555812897
    0x30603021203130933030516090b100f05160c06050a09170c060901021014060f22050705070b0c0d0501090c020a060b04020c0a0c080f0a120c02181501 66
    0xb1180450b1070410b501680b0030701e01c241043d441850340985c1e003111400d07902c00d01c14145001800000000504244040610b0518182142c04c1040c1350281d0803003541c1c1804e02061146404a02040e070383d5401003080040c4c400945481038a13401001a82040543d2440d806484180b5041002454580c040001d225290640e40d664402e581d0700c07a50b84c401c00421035042b2541d038000c0d036010005800c200d8058118544144105c0341c456514000d504101d0f00303070101c403089007141d490800082e0300702a10524400c02c1d09075a900300f1031682c010400022290502e03c022500d8840f00800c00c00e0b4428410340d100d0704d8100d0404a110304145040f031102d50301a00703850040c0f50802000080400203440751501d07002e245d4004e400340048660303030440100120b80d5035681c01079082c0000440010100701408500b84540d6071500c8103070919842c50318040c2c117081c2000c016404011128001240c0760540d109283d06410720929210151001594080b400010340c018031900504000a004140245600c02030003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 555815395 1250 555814145 555814177
    0x4050a1106160b0a0b090907030210050f0703090602060601180308030c09061303051902010203030403111204090218190b0304060b04090308151e010509030f060415050f0709090c030603021203 84
    0x881d85c18440101c0b8125130780d901c1074015800c10005801d11180d0098441506e2400e80d14110a0450b20302294008881c05d400083c0c101d05e091050507010132407690018001d090118018498018501d8200600e00008060b20400300114000c03110307030310030b031802414010003040d150348c86851012200d098520040c0d6240c8980d04c070416004508442c0c072200c1c1a01030740654503640e1a92800e40d070b01211a455049244640344050014244600207000036292003280075980f40c94520942c110a0041c8081c3c0d4426641340310300d50011001000b8000c12200c254191503201d03901d81c10081b00034286c0000d0b0580050030002070904155000040320711920207201c45030300d0081c1c801b09200034030349207034080701e4094502100460558020740c080c1101c10360040441d0034103180240312a04040099500329510310500640c4121403d032805880c3d4003980f0f40c0d580713000d50318183c0390003050f20b0110311840c02d05079512000400710320302c00d400480c091034026203c081010460b014095981d4821620020b101c0c078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 555816645 1250 555815395 555815411
    0x20f21060a05010e04020d02150309010905060109020325030b192301080a0e12040806090d0c0807061a220f050405340612060501020604050a1106160b0a 67
    0x781034441c8906942c482580000d19560b240d090014090034113174140e9000911400d241e114030340b2503000b07500c00c038000c60010410f840d603443d21502d0124180c0024080500500801298140c2c034800d2985042d030036070b00c0c0407000c00352420a0f40140300615040c0d8114404500380b001c006143d50302141210020f4507030600a5001d2444644251a07003080980010022008240140100e0b003001a034001e12206850440e90001141021030f0300c00d500240454102c0700c10000c40910603c6403150510311400c03d00c100c0302030b556514a03184100070b0300038007042d62070140d00880c15a030504119664070240c42c0c20b1b44e140074031001c44046803686406070556800e18807100d411510324000c0c01d00a650140040003400454240c0c1c1c407085031100c80782111074418181c1e980c0c1b0900080c2080e0010030460b10b411110f00e200c45003120035900c09400550540d4400c030203100014070300142e02c03645907401158000600e0003001c0060210b02c80c15582011400f441c2c80020180000c824803e40188019002000441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 555817895 1250 555816645 555816661
    0x5090108031224040f2f040b1c090606081e031602061201030303060503120c0607030c23130503070b0a03090305040905070c02040c03020322020f2106 66
    0x44540300c0c1000281c0e0102010036036143c402c244a003901d40094400b08004040100401c085501d89410080074036142e1180080051407200300c012030400362880d80d100007804445442540c8524031403141092000107040b0303141806055404015010300500740805801400e20360064001400b40c274405000308058410901e01d003042501050b8042006542462900540f403100e000e821042039800c9141044401500b0350001c1101d80a58071a441c000b401c17504080c01d261901480c100e1381c044841c402c004d2505400313000610701d9440041440d000c16014100790041341d000b10400348104014030340c250311000300b034240c801a02c1d1044c184200450004c0c0e4403020035035188094415020002d10822508041c0307031083e0400d01c003290181c10420b03c2e080d61612407904403502112020300117400d4401010840c6002d0040c021441d40b03924055045040c18a83c091008085050b0050300d03d500c441d0420454070f89842c01e00390403100800112420050700c0d5070f01c040f03c82d00d4401d01064003400001500e10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 555819145 1250 555817895 555817897
    0x250314010e0d02190308151c031412061e1f031109011707030b1c03020c010c0c1e082d07030f080c0c0d03030e0c1f050319050109060509010803 63
    0x50b600c903141003008882c2030746084c0ca01400c0030300510b9008400c0038000400d5140c03079640c00407108030400368235884002428003e0500c1400d29121860490411880e0406e00113005503603080841101c6009200148110445c02e541d81c4011795500860001803d18807021100b880c004420300d0703501d040c0a070f00d040c003101001c07a11460890a010070328991100608200031003005a000040d410001184070241c00002c1c1503180c44881001c50f60380100b074003001c1540c1442441d140c24070a00305a001c8030304a45d140340c01c80b03ca030b00a6600c202c1c03030b0710300555000561091141c01400d00505440c210680d800c04d02c1ca41d4170228801c140700c104052a01c0700344c1c03074001502ca0110b07900143d00c102104000d0f643d04202c0e41c1320f0840780703800d4483d541c0d81c044596180f40300088047e109440000c1c01402060445003464030383e45249100d00c1c203c0d00ca82c641c241841c101c10722036802030702e0000e981c0d03942c0300504520f20320f0044918803524038040002c11882c40590050091f54021a8003c00d02c2c1ea07200c0d042c6680f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 555820395 1250 555819145 555819163
    0x150924010c0503181903080409060603051623030f0402010e0a0f0513020f03070c110d08030c0c070f03050601030204060e010b180604050414040b06040e250314010e0d02 74
    0x500d901c100015212402008030030f481341c01c0000c0c030b140001c0d078000030b103100603501503001503410420000f01000a210030b440b81c0700050080d411300380550314010013512500007220580500f80500008030f40d281e24400f20300382d0b0301e0070300100340350351039051215464030040000c07223089000c546490b0240c41d862030141848412035000c460541855403c000c20b0151030a00e0a210b00000c0e07400b0f0182c0051940300d280514481d0300d00b541d907005610b41c1400d20405405c1c0b0781d081c042c010075801c134003400801c43c45001c9903480070b0032480640d551003490344210319010700c6501c200540025600084100140460042c0c120390085078240400da41328480070100e44002c0c4506014040204004070380310f52059403500b00001c0007007860382000c0d914000708050f2603c0034044d2450201ca04100800c004078080348c2c44e0052000e4800f0044100d201c0907440da1455a90300e80d2136402802100c0c40815181d81020002650740f01d80e18102044200040b07a020349000284040e45001e940015a030080c800105004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 555821645 1250 555820395 555820403
    0xe0312010312050f0301080c030105150a030b220f1505150d0507030b1003020102160f06050f0403020d06050f060409080406050f0f03090313141503150924010c 70
    0x2406074696a1140000d08091241e4014800107220b0100b0071100480514000e0280380090040300050900b0142181d40c0140b4600c010340d0300c1d50992159880ba42c4a00007a240c0c0f00c119480071ba1142c2070046281060b049021040c2007d48510300c08001c0e10a128000a1f03109006103c10040e208414200b552400c58440045c01105150b0708803a10341001519902e6000d482a545a642c0301c0d00c800b0740380746088590000514580b48204115681003240340c001841500d501d011a90612200710001c00e898440d510800c680812228080b0340058225401503034001d04c65105d01c01c5c549003800240c40c2c100c42425181c40c040700000c1040c14503010300c0b40c11707540c482e484525041c1040c0098945070031114129031000070520810a44468000086000380c084034025525981c02501c1da0402d2000e5030001e20140302e955035410159295150b2040c9c5843c03d80c01c030b850300c030340e06c000c440221a00250b080661200c0d400c0140308003040c2c10301544803000c0703090044040910b40d8200540f04031407000c200070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 555822895 1250 555821645 555821677
    0x6090302130f021209060106020d03021305090601210506012c060313140c09070f05040312050c0d030e01050703020913051305070b0408010b04090203030a1103090402070b06040e03 79
    0x10070364035141d038410034500051030001400c05402d04800c02c096042100c155841b54021401400041d40400100c034080c4a00c2c0703015490300c0030500000c00242c10701e00c2010b00600c0c0003030109403a6800345078004060903e05103410148030710042c264000c0e00f41540c1c12800704004802c011600720701e41a6005202400900c001a03e06040c0f0500901e5800103281c03440d20321050001c100001c0c12540b04401d108882001400040c030000c0421200c243c000c5c140e20144008403507907103004e9420209940407250403111044404c03800b00c01c16100da101d543c181c0507a5009a0740c90070760035901070740031800d000b2200e4000c100c0e82d035510034150103d00c262043c880d40591114010750001c0020342145900c150708420202d004a4030355101d51805026410281880b80e0215050083c1102481248510b0300300700d41c1400020040d80100391a0711a01251004012440f4482c48603030700304004561f840c1d034000d802155240000c0c10062603140080d98524455414990700310701111000080d50704080442d4280 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 555824145 1250 555822895 555822919
    0xb0c1603050306131b12020c030a02010501030b10210f0b07031506020f0a0f060f11030411010215010b070c0b0a030207050c102a0210080f0f070f1103071b030c06090302 74
    0x140c810b001d9001b40300c1c00c415020047c8003049001400a85020000d603000410103504524200101c2440242041c0d160229400200003e84000c04035030642000000004907805142c100b050132158000780150140b4480400d1101e0a40e0542c00140c10f41c4800310ae03407580b6521035100303c7e115502008002256808080c0300400300b40e29460300c0e004188100000a060300910a40c00e098495038210300f01c141001004000a01c051810501300e030800c00d201034040c40c000c464a03262050018000c0031110080800c1c00420001410031800103008050403070f940701c010100c4010040d62202c6011a494012481c4178021820103022000e816005510b03540040d00b6a80008072901d01422250b940e80030001201c140580c8488292112003050740e59040e80f00c0c81c00d0b1aa14960880251031005980031040070801080d9100043d0400071900d4501107403000c9075824400d1543c011800c020748500d1182d00310100341c007400c501220850348144004010255102c80581300d1140a100207504003400d60300b0f0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 555825395 1250 555824145 555824147
    0x81608070914010e040609091a25030212040809011101020f1602190306091118070e030c031c08070c050307030e04061220100c0b0c1603050306131b 65
    0x120381d5000810304d0202c0041d0098000038040e501c1d0303680304043c80c591781d6804d40b041c015081408199950406000b061904000c06e8000401c6403603038201d012606500141501c00d031191301101c040d00111103002c403990500d801c03d412507600c195240303408520750445c244aa19818000c0d65652200800d2140c00c05200c1002140c0384504110100d038410228030350480079140d00019800998041c03c000035000c801454502c1e0960400110f07203200b0320300340194922141d01900310a9005a1a14010700d030141070002203440c010341c1c01a11641401581075420b01c51804158000190701c16030360300ca40c00c3d1a000821f46107485840009001e82d041000400c2c0424010fa000c440008000b4000198550350f445030884118030180c2c0880754020f40304280e84020388401590303441090111941020100c2d48076018101550280d0000c01c50030000f00040c0214050b0401d80785500d411201c1070707800c0a071034a0000c05c180d004960321031203205202c00f00c64414856200328000803141c000182420080080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 555826645 1250 555825395 555825419
    0x60102010c020d1e0201110324060f0a030b0a090606020a050c0d0507121106070305130b031003020d050a1209060207060806100e0d08040807080c0603040f260a0816080709 75
    0x44204e0941d034a4042010b42846610011403245280040603000d031009079080700001c843d50f017410f9214100074490b51800000322000c4445c0e00145003000184040b041e0081500c1c100d071039101300c00240c6002e0001503400e4010803900e06a9101d0404d44058441060402920300e400785405445980640c9090014810744910814118007a10255001420a00003e01243d0150104400040000c134608403211409040403000e8031141d013616041d0301d000304840c007a80c1c00b2880081e22403120f01c0e41d61418058288045080e4903005003030000754a4040c0c1c400f07411140144503050051052580000e02d8912a20825000360002030800c060a4000c807400c90303c0c40c1c02c4952180c1c1c400e0510070320000041d04507004100a283c81c1c4054558203150459582c144849015014041e01c0304104100c0010070500c040c840c180d6001c460041c5002c0700d940800001d5405135020504200002214481142c2185001c1e201d0101d41d40c0f94450030790b800c88101e03102501681c103c00850310440c0140120030f6021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 555827895 1250 555826645 555826697
    0x150606030609020c060609092107050d020705010e042a090e0a06060e280801051801020c03040509100f0e1501020f062e0e0711070f050402070c0518060102010c020d 72
    0x4940e80b5442c9510b0444500274170b100c250f080b04100040240030000140903091101c040d900103400701d1464540040c03c6014000d070740c0d5100701d03620401015040c42c0d1140c240f15a080b14070500741e40c0b0380c078024013601284240c01111160800e20b400940c51401c01d0061000b918910740c2c42015000104084c171041241d40d0035004051001ea032461209001081206001004010004281e500380308400292215030013141080d541d00412403c05060800412a011a00152001d103081d6840c0d1050800f803444580045400d81d47d058400929580280404c0c2c3c0207800c11403c280c80b02d40040c0c01a41d0f111072400c1c0711401a085070340010680c455074a8000500d41d0300310404828403082c43c40780e440244075900301c02c1c10072140c0c2c02400360084d48042d80b0b6403400103550050001c0303030820758a2100e2480c180b04142c070540e0001020001c20001d80a008010540602208075501c055140102c02035000c894481c011340c43c02154522452000a074140c0c0340c00746407a4100c01e40d20b03200000c10100243c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 555829145 1250 555827895 555827911
    0x151f14400b03010906150f050a050d030207050306071d0604050108040f053f0403020a090f020d0e010212100f0320030a230703032703150606030609020c060609 70
    0x40d0001c100651428025000d090b4442c2000084450301000650038444150b0048802c403001d4071018000c5403150f9010805403070b02201c000c800c554092038101e1902038036030840e680500511003030002287c2c210512030483d508840318440030003a404140103080c0624132603180040c85005c0820b0100d1488141615014002c2c81520100c034542c0201d007100207107208410a000ca0346099003111550400120341c40c04034610020383c81e061554000641e40e10290280c510481d969802c030340011420f6504a075807103420b1502c00d20140f0f003910079950003500f220642c0d130f5000a450000030801c480c3c4440342001e5541d02034a8046a90130b540302c10085049035442c00100e130700c00c210b0003c8070ba60208440c06856100d15138004180080450781d8401c0350300301142103150343c00300c002800040e03008140d00000e4044480140000030007104004aa981030703900141c001200c140302008034080b103420140680744a500d041c09041ea41f0b10b0400200d1180100201c56908100041892450050b0403103804c0009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 555830395 1250 555829145 555829151
    0x141c030324090509030f0f0a090302030709020a0e0103090c17151807060c03020d081509040305090102070b090f1909020a021e0d02151f1440 62
    0x12407050405949000081d540109003000000c1000d000c0038056280c1c840b14020203981403403000f01e9816100e00400c040784800e002c002c981c80308a80c0c41120198020347c0c0007011600e4060fa42c2e26048029031003104900c000450014520480d5400390040742c80346c9621411424110b032411100104142100f040201113028821150320380c0d0243c00300750350160f24078201d1110b401500d190f03120310307208451b0300c980700344091030030803802003074000c51741c81d824a03654141076060341d44186103504104064807100f68040c0307030102480181035000e0080c060341031086e000c5035841615600c01030498010386440c90ba101d419082030107014102403410b80340c03981682200c0058640c5403042d100c20b03a00a400b0740130050303209a0100203801d0f140143c420b204071000010b00000f18032080001e4a8050303404040c15529210000306090384036105482c43e0000070891032841043e100d60000e40e9400392107054500c100504046501700e08030b050f0754403009601380c05401300e40c2d22440e15000c104044421640e980103503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 555831645 1250 555830395 555830411
    0xa05060d08030c0f0711100207030807020f18070201050f1321021f091e050a2a032907080112021f0c020a14030312060d1a0907141c0303 60
    0x241080506400b921900030740c6c1951688105005098220034082c3e030840d44020300030030202e810702c000c6560031501a2154070400c503102c0e011a00c2010b400d200710140040c0c807000c1051199040d40950302070604904001d80a884082c0e014258507048007025061020491002d0000451751a4088040b955030040c1e405d9500c44c2c10050440c2d1607400400b94410391118036a10400c204400d90724002602c4c0035031034041b0700b40b94039100c0d951746401400900c80040014501c0c5100205040010322000070314a480c65262240b90102a4a103844a6801013100c1c02e0720390980500546801c0b803058000c0d0360341d5015030b8600300c07185000c0341070340b18166003207074550411044880d040f803807072464044191100890f5518904c1403041006c0d1960000c0d02d0700160a180d90560f982c084203d60000c5854803c0d000039854104c000b6884500305040202408618a90012240001280c40340308003d0102130352201640c880304011010001040b41e54042c02c0c1c40b240f04c04505054141c0e80555019180003d400e403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 555832895 1250 555831645 555831667
    0x213080f0a0302010605031c030c030f24240c0c0803270109080c0d02041103010e0415020301150c1b09051006110601030b180718050a05060d08030c 65
    0x920804020300c40c0d005011000c0915070240140d134001c11040c0c0007442c1d00a1040020294550320b0701814081507101c1c00c4c00c000d481d100360008101d910710b0031420480498812027180140b002100c1c81c181018440c800090185024500300103d4041c1046044a0000c000001c41e0445089a4201d03040111b071180450b80b66030400c0030302601b01c5000403c22100101034014010304003078003c1d6904000d00d03031070248020540426000300c0044151210b9062007110702c00a000783c442082d92031040350010000042041c0a010301e14015401510202c0100d100c8540102c1644401d005040d84410800650300c002840780e144248400d0198265095503e45401c3c6050146c5055024903c072076115018852540c03441c0032000018241c03401e002c10031902d60003540343c03203c90501c4060845441e050003e8407803080e4088608a42c5413400a940055403105400b0542c40c01d010081c0c010645410000303600075a09201c0d450145200a100f0810b402c09a901e41205070b00c010014600ca00c801e010007903076a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 555834145 1250 555832895 555832903
    0x1b1c12050c0d030605120a020a09180f12080c0f031b0d0f06380c0708030d0c031409100504110d05030c010507090b0316030207080f0d060504060503030a03021308 71
    0x4101c50390742c04520365180001b08000c20101142d1170700c0a4001e6015040180d850102c003608590320200b000c0741d2030840c4030300c17000a0f402e00c0102400c0d0400040007403081000701c00002000c18050388840e9819225500950700500070380099940c0c100003000401c441c01c10340648180341d201c80c5a103151a10701d13036040d4141540c000c4219220115252402031040c1000d81a0142c000311006d030f81102d80030085001240340e0b04803035082804000b00010016124107080c881900500b049a048964601c3c0c00c002c2070f801000803041c01000249000030310a032046000070000c0c000d02c00f072001003a039901ea0b0340d43e41e00208005130003225401c03080030326000300f5214114110510742c000e0340a10748840d070000000742503580080c1350f04108500004140910110281a280c00900c40c3c540f600c2d1245483c4021740080c801c83c5401350071000003141d044c1b240800b440c010070030fa8610b43d2090003070541d90750a2000340e03001d030f0040b0b541c140c005010340c6404501c21b60243c403103002c2071221006140c8e0303100200d0b810 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 555835395 1250 555834145 555834163
    0xc1501031a0603330609060109140a0306090302071404020a0503060f12100e0c0306060306040308040510060e1f30020d05010c08010e070c03080718081b1c12050c 71
    0x107040425291130f48066221103045034468416120340f00c06192010000b0100322603800360f500100503401400c0d40d65103ca00050303001d5a4880001c05c0704612a080183d076608052003414003800d034a50043c00182031500a0b40c0d11034030151202c0342961901c000300840c4a0380503500b603801402a00e031410301114104502c031908402c0d1840010b028201c0b00750142030001404c0194000d61100d0144a5507850005605074131503010710301203885440760301c1c04a040104105644a07081d0031720101080d00f19000d80207901804080406200343c2d0000c550902481005204200c60250b10007040079403020300003d1402c4034401c1d4150000484a81d40c0041c01003002c03d102910300340e6641c003a614100d6004850140901413003003040c0982d00e07200c01c000b03284415074180141001070180101e68141c2c0504030340c80720704e81d21140255515880f40040c0342e840148034101d11600f00c040c01d01200600b458002880c0221010803089514910342c3c0b01c000c3d01b940d9044801041110420038009130400611078604 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 555836645 1250 555835395 555835453
    0x30503130c030305040f061704060509031b1506030f06060f0d020603131b0b040303030f021204110109060504050d020f010c0b0c032505031504060b07080c1501031a0603 74
    0xe2a05c1c10240d04c020380ca0b21613009001881810623140448407012a1520f230700c02d600c5000072074907503201c00d0000c0c21402800320113511031040e200e076021a800d000c203482e140d00030107111488540da10300e0101a0303685554000f01180e40c0068000c1000d5003441035028400910182c81030701096200e40c04581564411500c40e05080c100c2c062040800800d1240840304460540403454020306003a07028456104030300c0001c09066646c9d14900102041c0c0c0c05860301e142100a080300e19140c503092a1140017080e1080e6800180122000706140313029006072825100c010f800001001c4165090080d1400c20002090600c1250039400380050b240e4480b091180441c01d80b044d0310380c200440048416034903c1c8100c4050600d04494141e4598464240c1e9440080c1144800c4040d002c1800b00e0001d1070642c0008441c80b03070014907a8240f049090083c50000354100c101c0f0950001c110716900c01400170b000007070655000c2003500302002e80075424150007110003400d85507100e4010403c2c0e400289050302c258 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 555837895 1250 555836645 555836647
    0x1206050a061a270d0b06130c0e0114040801180c0603090f020603060f04060b071a070f0507110301020d0c080709350a030e090c07020d030503130c030305 67
    0x310412140141002090400007500390504442001103042c0038100c6001000c0300381007070089903084003c202004801c0d000d40608600348090616560140742210900d001d01212800603820307070040e12540000c0940d42d50b03030810b6072240f003004580320502a113074041503140512001c190480f0a12030080351866194450b00d003220365191070800c01000e540008181031034140e661010420b154524401580e04444140d580c0d035035240020410025405025009403030001c02142200d40c440041134402c0c081d0000e50814003a801000c07410b02c8040311039000050051078036009681c014005018070303610481603d02200a41c030007107070883e0000030040f641340c0d80380e406504583da0000401038010410b4038248112505050b5118086c1442442d1240a40c201c080c1000181a01c20140021202d0078420780d0314004041c28024078400240c13011038450700b01c21012603800300c413202c11200504e03070140800510309242d842c02c7c3c030942c000030070214150040488100020304601c1c4074401a5219440e0381e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 555839145 1250 555837895 555837901
    0x18130504120302040b0d020913060801050117060c0a050c03220306060902090114090102120d060329041e1a1b1303020603040809060c0319050a0e19120605 68
    0x3400e40d0041c0c0c04141024984100320a026101110382100d684e441c0d0880d025a5555019021410a03221031050303203c024030b03101003c1100c2006401950490b00003241403062001804c00d001c1c3c130303410207035041851680100140c8044034014400307803406c50300d5041906d0134490340c444112000c06501034200e04a1002c40002d10801c8007030300c07501c0b002d00420282142000080000a40f0840e15074202514640c004074414001d80e208100d403298089520b8103041c0c0755161400030a0140159020889020b203441110410341c02844032120400f0743c8004112442d92680c1d1203d600038510044050303008009003e103480400c58020026054080c06a654001d5140101c50505c000101e1061005050001c0250405900a151001042ea9011991507030340b92110700d040301d800e101741020141c10000c0840c0488172003d0220107460b542080064082c0400d130301c0e00c402ca606205100549000c5207801000000780e0405c8100034080301b10107007a8007203040d1074142c841b1145000800c11190076071140c3c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 555840395 1250 555839145 555839153
    0x80d0906051003050c090c0d02270405091005040f0c0315201c0e06010b0703023009041e0207140d090b160c0f0503011406130218130504 60
    0x9050790010016881110450944d9290703615504e41c00005032095051002040000c001c1400b05d4502401d0745d0011582c545d078100160320104c24440039100820600c2440029904049c010144110b003410080c050200a151400c402044044c0040e0b83c0c0c0482c41c018040020040140500514001d041d10310f5000181c0300d80038142c0380380705d040d82c2110205604000c0c01c2610802a0b40e19800704940d1101da210402e0f40400090004060303d540511600000044828041004114460103039081d5244424030b405144542c44402480d240802901c248040c80d2a4140025220000340240701160204460f0103000e03034110410651103040354005405000c102c54403280100c103402394030291a101c00d010b000940b00310094840c81c4c0c00c00360700046502c08954241001c250165000000c5411a07888119825840b5540d00400e40690310f000c1003d0b00c1698081201441107030010158001c2c00b0284402c02d001c1d40100300300148800001d0415241c0e40d903221030510711142c0c40c4100050900d06418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 555841645 1250 555840395 555840401
    0x607060f051b031303030e07030305030f0a140115050c0a06020301091a090a021e03010f030c05010c021f020a020904051522170d1b020c010906050403110607080d0906 73
    0x1e108802d80c1c1c0074500003642c8000d039050326400034603d103103800c1001d102d05081e03001d0032111035010401c0c010010080f04161704200550300030104002e04440030307a1040051411610800900c2d01d64111040040060018685040c104640e03107103000c604029a41ca42d45150031113280080710b4854001c0018009000184100304042c044c02080c14140f0b55000c0100340f9507140a8258800560006119260040c0000345280010400c581d95542d9680d64044c0000c0d040e6140411603003003e030608000380c650301c100000f07008641c0080024601280d0900c1e40c8003c400003e0540040d03024081e4404050f0ba100b24080344920300a0029104d294044074100d84c0000b8001c00d022060350f201c40040c0300740083c0c2240c5005059021001c0600f4861402e6003ca450090204403890203003000c00d07400800d10020f201000c1111a6001c030703100d030040781c80151075071a0342d07000c0c0c100020000d00040000c59403031030891130340080140201d4613015281c0c039600c00d0343d4130013040500110303100c2c5083c00030415248 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 555842895 1250 555841645 555841651
    0x60f0a1113290414041503050303041b1d04110409140d03060b120405032511031f0203180304270b0d0b04020f03060a150e040803130f020607060f05 65
    0x24441c0088010142040c29140c0600d015149050901110041070b0340c455502403041b840c00c0b011640303035440d03a91030040c0c1d0b01e500480e0200d5003c08440d003400d0088000304204001c0d02c2552207680b04152401c0910840d2400003001655032282e01d00040702551a28820060940d0149414844a1010211451500882c000290100740c6020020000010000103031000c00d0480c000520f1551103a04040e8994003c0c00d5a404000c1d5403440310481440284203103520040c415130030310070103141c60b00c01c00d41c40b100041c40100d4142491403446045001d654000c1d940a13000311500c006008680d4840c2d495904950000032000c1c05000314000301002c40c0c0308045220400340ba043c450020383c280810200121201e0003000b007060140030808665642542088418000d000c0b141c2901d40b00450300003500d0924800b1400c91451600807817032801024010303209136000314110f841e5448401c100c00d04004480c1003074400541c21800500180c0c1c80b0001449003c5c0078410200d51407551380c4a11003110409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 555844145 1250 555842895 555842939
    0x30312271a060303040302120c0306270619090606030b0916091b0c05010b12010605011205040f0f0213020d270507061d0a030c060206070908060f0a1113 67
    0x400200783c2d000011a42600c1c2d0507105130348a61000035000c0c0c80c000300e4010b02e5925008003001c011941000f40980b8a4205140340c0c00c550f51075240700e5803a110b02041d200401701c400303813001c104a0b4080c91b41120b0740f05032180304001500344d640e0722500c100707a0003a20b000303d090304450600012180c000600c4400b4040e0b600003040300f88a00c1481500c0071005e50070040911004081c0d40c020320030298007000740b20b0f01c080e00702911011409a0300c0e00a00160052902280310b07440781e184071031424812984034507400b01c011002c14800c3c0d120150306030041d882c00c80e4030445c0520b000c441e56945000ad010038640821010030070044000615204c41a8140c0704005c0880c00d9201e90301049000072282c0403504241001440b403104400c8080c000120565403e03001081312800104000c0b5002d00001110040d070f0941d46540c5481404580500e5584502c1d42d0542c44000030501e201c5d03695402c590010900100011080c00818010703001d608845000710214007806c0c003c0244500600f00c09884400c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 555845395 1250 555844145 555844193
    0x31404050a0305013603180e0703061a090105030606070c03050a1103060610050315010e0a06020f10090c1502030909090a0c080616080a180c0315020708030103031227 73
    0x142c0785c5038803085c031404c02000e4200841c115000e039016080c0c500d203034060b00d0a4000c0040310702d460344019000d02a00c0c1700c0c82c0340d04005106028001d000000076940d42e84e005070b603008c0c51604c41e1401c000e26600101015108a4500200040012401c000d0b40308810721174907007504420780704420141000d800030480c070302403881858582d110741ea1200440b54801110304000768180070000048415071900c0d822140c100d02408000f007003d640024821034484840ca0407180c1080300d1203288015601010300040c0308404000741848115040000080703284e0b0188107c1e410300d614640050b41d019802d544c06e110b283c000244080c14005604500406011000b00070b02c02410480503056461190f010f01e50108500c0c81d0200d0561651500034811160410f55001d1110300c0343d003488103810249200446400341c4050240c0c1010890780280c0d00903a4020b05040e00350b82c13846c0c806540c50071031000d4120302c260340d900005241c2100b0451202e0209030240d40c404141c1c02c03a2402e00c4080298010316820111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 555846645 1250 555845395 555845471
    0x7031d0604050d030c110603070513140a05100c06090f11030a051b220c02100e060a0203040f0c0b0a02010b010e09011502030d05070336031404050a030501 68
    0x203c42c4102144a5130603c1e000c548007005003400501010518085a0b00c124000248403000b58050042d0454110083c110701d44280c0c1c42540c2c12170622780808064000d1500c06040000c0d2a11481c60900d01089060860010f4116603454003212200e2804840b003000d50811003013444800d005200c0b01da1000c0d401041d04041646030540c4d1030364000000c0d107810982e200c2c100070340d45940c40d1884005002c43c0107c22400e00051411001c8c103203181c12080188a03443d0307c48102c444501443e0051440840640110784400d101e000196100800950300748480c03031300440000e001c00303500c0c4004021468219840d8100483d0090a5070240c165550400c0b000c8600c000890b0340b0341501904440710306a00c48100c0c0c2407050300340d081d8020301d64020189847c1508000029030940c010702007980d080040804155900345140b81020440781e0303030900c0030181c62640c0340028002c0c18007154003014180700509056840001a02c4041c1c0345c0c10455050f5101c1485846003240603804c0c1d90001c15007503040c00100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 555847895 1250 555846645 555846649
    0xa03030509011416030207020306190e0a081213020d110102060105040e071404090b07230406170903130305211e070201090f030305031008160501050d0f0207031d060405 74
    0x10314050f18115464444c0d00701d100c05140030703504840d40c0c1c80d8081d003603501d980b5040c1e08000c504480f440366442d01c54140810001c100601044410f20250b0010195040a10561580e50900d500900101622000f2403c0300f000d40d490050030b000f800e12401c54983c0c0c5001217400203081c1001a401240a14241804003e141001140382000e842401401c429040c030310b00001006071074081d83c0985003072802018000c85a500401001d0789489020000d9401010440c0b041c03152320440c4120000200c5510303624080807500d1f038551fa0000c80702800c07682013880c03401c3c4840c840800c44d4000c60f002e51024090340c084100d4904448500c4001030f182d1410010301a07142905a40113550140d0b08901c00548003085a00500170070029000c502e1a4046403500d91601601c01d030b0080c1d0310018034500c0c92074001001080080c0e0f82040c0c07800c240c0310300c40302403800c0015076858010405214115403070302d89003502592130f072002e080703014000d171385400703010303450102d02021144114101c4c1e008060401007449a9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 555849145 1250 555847895 555847931
    0x807080c01080901110705030d0c0c02060412050f011a041a09220b04060b09160207140a030b07030b0a0e0105240c070312090905060306060108090f0f0a0303050901 72
    0x101420700781104203588103680b10740108170702c201410100c14003003050018410004060140014031413000c004003034904000f0703100e0240300f00b0300950024041005020715096030f185841041d205400302ca42c103244010309035080d0382c1c0414903804483c6c41000880140d24082c043e103070b03440649081001351903000b40d0118690400040c0700030300d44422841400c6074a4855100118407070317045480f005042c1410b1030280b0140c80c88405591007401c00070041140c410303149482035041402600100062850311183e502c80da034006031060b600041c054800404292040580e0744038042c2036800040300d600480c204415074102e60080d00122185c540103000949030f00b03c94005044101c3d04054020741c1e0300c0303d520540c0c403450102c1038042c01101000000c003c1d440c20712010410654490806003a01e60008a0071a04101c581c203505a1160020072925402514032580240070345c3e081ea0707031080303444003094680a81111804007580c4158000001e05906216903600011003000a00403030061880c11148 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 555850395 1250 555849145 555849163
    0x1403010b071403040801060315050609090703023d02121207080a090f1104060506070803150d051e10051512032b06141f03060f080610080708 62
    0x40c1c0003a0b900914803026041007039500420f12031000f400b001d038a07854090801c500403800c41d6041c609000100e035540c41c0c11200c4600c1614070900030f0140500d1030b004c004074090101440c0c000c400706544440b900c10200d0b8102c00c040d045001c0085800d50718000001c0c41c1051448100b402c0c050140411404101d0b1004c00c65084a140d180c01105a11140e40300801015005001031149021041200401c88000c181c2402144106d900b0012a5641e1040c0102403180c0c40300203100c0c0e01c007040004d4182550042d684619a40500215041d09a590300c1600d400e61402c460000310300c01c510502e040b028100305d0740300e402d9105a4140900c0c28580714500316024000895882480021030800803440e0800507994405028031103106003c00c007001c907485070801141c018100c1800c0c0540070460748100c0382526000c0e500030b81080c1486010421140c9074072884820b000826895080005928000c0010039015040c400e02500303082c10440060b0354104056403294210350404c000c00c1105040100340420703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 555851645 1250 555850395 555850403
    0x403120c02031c0509040204090b010305060a0b071e05060f01090e0d0c0308090111030a0603110901080c0909150403120b090f13081606062c0109020702011b030503071403010b07 78
    0x2010000f800e01902c06018071000c50390420301c080b400040041481d009070705482000c0e2000c0081e921844c007032008407086800340b41400e000801400c0000f41050f00440740d4811850600090340030540d940d5030a21006075400c00700e4560348001800b114109205044900081200806c2544142c4601400441c4061030140c01c0c0b04004c000119158001c0d0800d400b2038400089050b601c0c40c042c00e9040080c20f044c002600c0c008078400400794941402d004d054144d90740b131001010895a0030080200114004003955810300a0b03e801c0c00c00c00380e211084601861080d1034165445800740c410707a00700c465025500788036148003801e00000310f03610f4207420703041040314036500d1800f21181045610b40c440c0d50220600c400001c0c012000703016265005c0002d07a044500b4003414501201c4d041d02d40c04a403070002e200d001000b43c0041001501c0c1d81c2c001c066140c8103041041001c294803a581c84c100e458180c064002c100000100180d195000c84070492181c00d21070040d0541d41050030f414442d00400000030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 555852895 1250 555851645 555851683
    0x270501030203130b01030b1006090b040b07080c01020703020606130915020c07050a14242a03211e0a051012030f0215150d06060b0f0403120c0203 64
    0x18000900d02d92010b2401130b0481c8485085585d131b450701b0b2001c000211100c06049220860105401344600061402c07500440b824905050420407450642d034840702c002c03107480d4020004487c01c0301e000e001401e1141c0c02900030740355914210041c03081509400c0d0600449620b091043c02c0011945500044407451102d80141c80d44008800315240240c1600319541c0144107240c009022109880b9520b0b00743d8042c1c0c0d04900e02c80038046040d0100c1542c21602110b0401409201c0f0100894500c421075410110714000580e2104c20070b49045500101349904ca170000d104403001c0144600405a8012600304107401020540c50100d81c081240a0700a08081d5100c0c0d000c5405402ca00030214090104442901d03d582540d10700070b85480c3c8900c100030090f00440400c50050399a440d00a4861502c00d81411201007010007000034001e0b0102088514523502d50001c50703841046e4010306240f000c2040c403159118110b0515400b04814120200c003000a20200c850050701c020415240101d50203c5030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 555854145 1250 555852895 555852901
    0xf0d0f0605040303060f03060e0c0109050d080304020114041203111903030b120609030307110a1133040f0b180d03110a0308041209030209010612020403020402041203270501030203 79
    0x2140a803001b1340c0616802c5404510100600011b5880155804d00b240f04031440310000c5001940c20b00b000e841100c2d444401c405a071404548440011540148145041904001c0c81c010240b141d402980180b0700002c0003107110001c154000100c07a401c0a00d040081c09660b0403554421181d404d510307002010140c0341c0c140c800450f1a000103001e039500c510015035100340b42240c40740b039690700b04955090000b0542805001501000700e80000d8454111b0252141280c40d07000344151100003660340c440c80460200010300b800401c1d080c0c00280b20044031003983d102d140c0111121003c0c510b07040915801010050131811a0811a581f100d0240549200c000460b00382400d490741c00701c4034945080e900541034000201075000301802d20440c4580003600195881407412510303e03601d804020b42007618039005210580c0202c0040c280030400c41c501500c1c00e5126030118045e600b00340d1002807081381c408800410950400d2855600b00a50800b106281200100001c0c10802c6440ba4505040d800004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 555855395 1250 555854145 555854147
    0x15121e11010f1206030327061205061309051c090e060d0c09150e010b07020306070806041e1a03030c0309040c090302041a03010507050a0206151f09050f0d0f06050403 73
    0x3c002620070110004110381640c03420050f0141088000c041c0c200c02005504403050161004400305442c0b0540c0c2e4084040030f40c01d8800000c101c050483c99002c6554900181c03010300034000c2c400458410340181903000c805100540d00008003d104100b80494000700340031030080c041c6060ba01c10422200c2401230420360034039002800680d000100c2c514213040e071068444508446800403034611441d008581da0b83c684401d40706025040340294182c1141d8041811a88103166094110b08010300008091401154000c2c407010110030303a410309600c46a04c802007107042d003484401c0c214107602961500c1c69100903180ca91050421403031003150748501e1807541d9440703079000c540070310340c00782040040300034034101c10b40c01902a4040d02d21941c01c00740010102407180701940c0c40450341e07800410858480803110f22001084881c91a00704440340c0903502d80d18030303480a6540700c244507250010658100700901410300401c2e0380b0a4000e030080501d80e800508295035265086400400c009441e40769454 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 555856645 1250 555855395 555855407
    0xc0314090f061e03090619021920030424110d080a0b0d110f0402040501140714120d050c04030c030b1003080c030c060105181915121e11010f 62
    0x43c0c00c81e001030740801004400e81000484900a021201e0105a1a50004480c0303061f80320712090000c030648000c030b000c421640240310744071a0150303034034185d41c50a004041d6035286412503030100e071070702c1c03c118990010044003400300300c0c10307841516010302014410217681d5a03078010100140100180000019081d12640d442501c494200800c40e181495603800c083c1d080886428105205000d900451065480d00d0300c2220201c40044c1c6502c040740302c0b80701c01c0a20541040310b00b40c500d90420800d00d02200300501808206519681d14035031600e0908003100100c420091100c0800703c4100000e00c00f0a5842c01c2c4030044036403000c49403005989103101001c8920103070344000d229920116264a018501001070084008004100c4035940c2e03a450402181c0c0c04085c404444035407085010802c00c0e0951442891412038500b00403440c40b00a00329000207840c542d004100f8007225140140403c51040d010143c07100942403004542941ca0300c41c3c1106544d0000300c181880b8400410440c6c05000b91 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 555857895 1250 555856645 555856687
    0x103030f020a0c0621200c031e1c1a04090311060907090c020a020a0b1e0c1014070e2101020c01050108071707091505030109030c0314090f06 62
    0x2030008802c41d0366507402074003c00040801a50074902c20400c00b035110b01714861000c100000207140d45142c6115901c042c41d90b84802e120052501007041403802000310b85404e004c0003031201900590381c003020551000604a035030700641e51681400c18120801001c81c00341d51008030110350008d00911203103810b64582d950707400301090a01806080088410000c41c602c0201e5100780780a0101d2991000201d86502696038000e6122072132802c14000b840b101000307400741400f0b95811039894841100030255640024648504680c01400c0e020202c1000f402051001140203221600b10706201c0000340440c0d00400c41c86010f03801c076000a0388000d2640b0044800809803c000b10342d103044141a09020f080b0900695041d40b0a2400008032050030034403060701e5004510103859254103103130110000c1c10801c040342940d0083c6010108203a40c003803285406a0748030341c440d090420f031946000303002e80d8002081c98400310740510484055403100503a84e44d1124007103e506039164070301d81c02da0740c07024125 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 555859145 1250 555857895 555857903
    0xa0c051e0904060e211603020c06220b03040b15031e010b12070608162114060a050f0d080f030f0106090b07150507211a0a0e0103030f020a 61
    0x480180b00c10f00c5419030002c1c0c500302204040e81c0d900354460311050708007a500240080c00b0750080060483c41c60300c200e81071200b00d11a105030b40713010075803a0014225400200504000d4041c0b8004801409444180d41004061520039075003503103025100c1344080040102039406407404040782402035a414001c1e480442400c1c1c03901d8030340841d00704880b402071100e030043c40d00650710800c00850714400000c001c8100c0d032080d640c101445c1d540c40e281d4505550b043c000030091102c0b1205060540c9040031180c45c81c0311a102c80000c1d2003130540c01410280344081c01c682e01400e04010107104d40e1722007002450112800f664283c403030305040d2500b0b0302c007481008410160b154022003442a0202000300d4a03048030401d0b660080e01c80d0701c503c000d100301c1c41803001c0100143c41c0c1d078001c2d0300c0c01c039400e80200b40d00c080305040417203500710312020314030f0600e05808c00702c9915980c03000f03021080c81d841c011840541c03506554441c040740c2482030f03c01c1c64120602025003440050b0540c603907081c0c070070881e03d0f01a580c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 555860395 1250 555859145 555859159
    0xb0711031006051302043210050315040615032003040506010602100e030421020310061e080d1b0614010510050c06010506031906120210020a0c051e 65
    0x1c08241003004000034050580b0404080083c204031203818020781d4140c0700611248582206000c50a400e460124070706920035400c41c8034a03d4041d5502101401001310f00d0701c0391507a80c50821080020b512410569610441c5802c01c280006000c4110720381d0400d13020300780001d98035401c444814010588a10802c20303502c0000820040050204849040300c0503902207850b143c840302036450649507080c020070525031082c40300300030040190003824600300c0581c8c2000828200c98010908018100a9242101f5181c0100b009000b00d0145880d40c41c040d06c90b0155407940c100b2050300e4483c1011080c1c078080009188000000902c1d400c121003c03543d0201e020800034041c01078482c01401300b4403c5c280b01d8548550790b400a280510f0031255117400c0040a48003076820f0008101f1607400182c00716079003000c0200407000c0010f00f1301c980d4020704070003455403a07040c2c00752040107401d40b441000c03441150050b9050600150040a1800c10344a0894503035a030007000c0102c6000710200010510340c001e42c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 555861645 1250 555860395 555860413
    0x5180d12231605010e061306020d140a05010e0106020313090b0406050a0e060a0b160209091905070e0c041503020a02190b060a05150906071103011410080d05040b071103 74
    0x240064001050030f03c0742c00280014104080c1682c1c585074121000240c2d561103403105000600c1d194002d011040300710f20002064192013059000704642141d0003e250b503a22030060180542c09a4881d0045c443d510080d807a02c0c071060f0f0000f40f021641d10031125015203030300450f601c81e5501e4220f000504409400c3d0280c83d561480c91070301569013a9492805074500e4400802c0c3d60200000b108c42048003148440220740b16a400d11a070000c0050000ca00e50080b02201203440c00c440c0010640e160141e401004400c0c24080c1c05040240c1c06000805c01e540108000c00c1207000046504c51418000e050040c0c0b6404044000c0e0300345844554417951455018440340c00300b00c2d03818500c90084500b62084203003141c0350707820b2141540700906154000141402044500e141c04c0e401001207074450310f02d40404c90300542c00700307007581c016003008079021260204102d1219a07040020000745640030003015541c08007180a8142e22885c007503069403290008603034091141c0865280d601c140c014003203e072010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 555862895 1250 555861645 555861667
    0x1c0c06020417061501020d0e0307031416120c03120c0605010b090a090b010f1b05060f160e24041a04031a0f04020f01030e0d110d020a1509020310090305180d1223 71
    0x42c075a1378660440c2e842020010a10f01400b000c041c00d2154080c000429250075512901e00d001844100041007004041003040080d40e180036180c000d180402c03201e51903041c4007003081030411441d0001102689454000a840d80c0d106c5a241120003031828203001c40409280c58501020326280007510301c1c8200420f00c001d00801c2c00d141ca224a6805c0e0462900c0d801005086a2503441c2e2005144d116400c141d8000541c01003100316203d11484440c501d142558824100901d181000e0301104003440c045010800c6c42240080840200c81c84e545100b440c0c60281c00a00000ca030292000e40910b06091410f08075901943c0504600c049080440310292240e1000801e0800d941c01d50b0342e41402088015000140005403411030142d001c0c2d4108a418900c0607100010284080300360392501c240300c0602c1c0303042c2c07451245402c490b000c0d981785d903900d010220940b5264014514194080e000302c500311404511491061146250b03180ba200d90b810900080c4140c503c45003000b015241c2500182000c004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 555864145 1250 555862895 555862903
    0x503030103030f02060907150207030c030b01150c050a060902040b1924020319021501150e0a0803090909010609060612110306031c0c06020417061501020d0e03070314 73
    0x364880c0d607030000030f001ca43e00120380b106030650b5442141c2c1d0001034180481c41d203200060b1b40c4090303148122080603a0380d840307000100328140e10a583c07405096006001d5090b90102400c5103440600340018900410356655503101410380010b00717001d9032403014070110758407904026854113004150134600801d1503000c0c04041c480d84034000140c0c000c04140e0541440520720700c8950b40d055005942411010100b02002c044592590021030007000d019404011a844a030f0340a020014940c2e8159140b106002d030080030004103031880345506100800000740d0000031a84071000a80e81400340c1d4a0703425010b030240c980e94102c45006405c048000c144198484180744850350300b400f081c13000041a28903c8014072042d1a13054050f003107480030040360f4904e1100d11141e2800744c54401d030081007070346507030040383c000750400d45c4c1440b800e03860f41003103400401c0f040b030300514034036a24030090303c102001075902c0410055800620241400c0e91025a1701031042c40000e68200700b00094001c3d11204450703c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 555865395 1250 555864145 555864149
    0x605120c0f040b030a11060d0504081b07050901033e010201051317030403050d05010902030403030c02011e0f021201060c0302071509050603090309040c05130518040b04170705030301 80
    0x11070000c0d000e5034007880c00b8000c50422041c044d01401c5103d910351031b81d4140300c0d00c81410300d40040080100300714501c418030071542314900404500d500d031000418940c02040071400c08060702d40c04070000b0f100a60714800e84a045980c8261030014810020140b48800c0041d8005448082038500e0040c5003462194180c54170100240e0003041190b50f00a07074201403094001014000d9100b100c4148060510030f8001c603040343c041c0c14564180341d052003d007010342d00241c0080e5451a000710900040603018029440041c15a0009100c40841c45c100c0d242003500c5030340202e02d125203440c03501202510381d80c110b400000c0f0b0303030128106540c1c4901d809041082c550208500503c2003440026141400d10000b10303210889d9079900e10902d140108000705604083c00c00b08507030004000304511551240b1a4061040303180e200d11740c5a1790100d00540019000e81d0180e40070301403021132000742d058003506440d40540c0c06401800b403501c442c200030a007980d81105003000c0a40004281040c0a400009141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 555866645 1250 555865395 555865399
    0xf070501020d03021204080c0a150903080601050304030e0f0a170601030c0509190207062a08100e04080c190b06041a330d0213080105040201020706030f0605120c 71
    0xa044030481003201203215410740010601116400300d0b001511170787c02400a900480221030012005454021221894091450745d80307554004d41c5040580110440d644000b090900720300307510b0301e07807406003003c1c40c1e10a1561180240441802c83c594800c024240034084207200c40d4500c988801815a44002c280025107201618040000e4246007090b040717440f9101d049400201605080c43d0714019401c0080300321a0951161102c082900940e4104d12010381c11007042c440e101c401c1103000d08200c0f009021840d202000201c10300c0b040c0d00304c07041e480e0001d50000049945040300424039040032881da400c3d4031598880f180100502161940c00c070b0190350308440801c4401442103482c100d44401d03500103504840140b000d10074000d030303a101d0325603002c004882d2404079607001c00700348111741d03c0b07128005031491340440c1103612155003445400181801758001c02507400c05400107503803000c051060300109900c42c0c4030714403101c18036002a4000d1401074586507200c00ea509041d42c0782d05007010024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 555867895 1250 555866645 555866653
    0x2030f07031809020910050915120a0c08010819051c090312080f011205070f080f07080106050a0302121005011202010e090c0d0b0120030408061305100513050f07050102 74
    0x1c0743c0e0390020310850b00c080c0300040114030951000e80094a0b00d401440741c080d485045188090401d0040e50020301405071251031107151803828158800c00c0700d5081c5a05010011441d0051250284c00184181c80d8944410100003004481c034100e803400c0d9032113a29003102c124041c3c4105626802018000c1503070304c2803548036403003c980030003220003844c100c840c034003000d429100402030b0f00c1c4000300c0899414001c200307550302c60f900d400c5002ca248503282e1280c00d8a90100400450300102801030034080c0118038001d10800c2d19140028501c0c0041c0c0c080644203881045500400000801c910354005111100034401980e48800354011034901030010707030101d690010690300b2454010b080d01c3c4240100d00c80c990400540501c613000804009540c14140450400101c0c41d82d64a0008090001401c60046a0b80c5081899440c10f100340500781404038410040d41500003a0041107240c40c0501044c000211681c466603615249918507002526901403504003102848000c1218800d45500380c0880d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 555869145 1250 555867895 555867899
    0x60903030a08040c120308010501030b01020a1403040906090b030616121112251404050303030a0911010c0f061808070f0c0f080c09090c060309011413020d02090702030f070318 77
    0x88a07445d0b8030f10fa004000610b88001840b45601030350008c0781202c4184100c0f4070b030401540c0d0340320b010f03850903108580301d9001103010040c10056009001c043e01892038140321007840a000b00c0d0b42c860b4068040395040c03480600085615101d80b42f401049806003c013413005c45244e016802c107603444040103c2e6000309480c0005c0c0d00e200350a6800002e1f0b00100c1c040c4451107090101150f04001c8940004200c0208000009040d54100003460140c0c01c01080002c11603000c1c54040211003001304c0c0c01c0e040c00b690302d1144011a81660300b200040da0031050110f04040107a1004c080c204e50000e0045c568a0046000414020110b95050070188940c01441e0001e44480b4110b0014503580b01d946d04560010a40304a2428020302d8103030405508801c4500301d0070102c0c002003141c5c00c100c580c0c0c04140c0d540c82d862802070043c0103489400034401c006903441c1c800f241c0c0110b00f1001032410060301440305240418000342c82001280d04401944d1a403a40b20b40c282c1c6401082d8a001040c8100c50084100c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 555870395 1250 555869145 555869159
    0x302030c0607030c020f011101140603100501080307140106090908090103150810020f09040914010b040902060f070f051209180f072007090f20030106030902060903030a08040c 77
    0x8a88800390143c130790b5084008a81d08102d41e8501c07800c3e042d1304115015400b420302d61401d024100050002c070490011074034011090610f00240c80c1a8040f20b141080010485410301004440c0031540059440300c402e2072008403e4003600300340d4002d06045160507110803d20201802520b1190070990701804090001ca00d10841c903410f0340211045500721589034500481c040d40102445682d06040e203080004240c0000d0445038600c00907184401041d4024000202c207218600d2141342c100c0d4100300c0c800d8280c02140e02c90043c40c81d0845140f0b8002081e1040c000848900032100ba40312040781d0208080baa0200510b400071025039008070007000500e50341d0f0241c034030020b10a210070658030300d80e0396402200b242c028502c01100d003130300d2400201c2c049464006010041c05003061401c045032148070180000c0803500304081c05a0714241c481070100c84132000c03008890440d0010714000c1400c42c8540001205880b480000b95410700c0b0015140708801d03045142c152040d40504007401005075500e80c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 555871645 1250 555870395 555870397
    0x603061d16050a3b0f010f030c1b03020705011701060504030f06090c0603061403010203131e141b031c050f120405100501081605010f0504150e0307050a0e06090403110312010302030c06 81
    0xb05c0b2602007040d880005100500c660b021103040f44081c40c0074860b07480c0304510f405628100d03800c20fa00680060005101c0341d40c108218040f404505001c6c04029854150020624000c40c0001405145440d60075428095150060060f07940c00441c070200213543c42a000c4c004000c07074031600423603044100b00c0c02254039040c0700f507a20079021222a240090354070b40c0c441c10701038203d02002e251250b02c2251240070910b0244a0000a48440018080c01626005110b103007400221004d210340c3c4105010310541c002409440022402400c0080d110201c41c1003140c0036015200c080d194400005080106001340020500e08800c20f820302000907036203c40405807154941961f80c10f0b01101c2e00c0e4100150b51265251a1a000041c0f41583c180703611291007004000044007440001580c0080182d4549800e02034000140001c65544003682d03d04043e0012102c0300801d201d2040c0b4000c2c00150501d401111450a5800040305582d55081400e4640358480da00303010984c0288141c854041c1642400c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 555872895 1250 555871645 555871669
    0x1020406023409020a0201051014010f02010e030f1209060103020603010b0d1d01021b160e061f02060403080f0c121503070603061d16050a3b 62
    0x40e014003a00c4455400c070808141881201500001105031080b040040e0030781e0640103006819805650b420f04030303100a080d0f4070041c0c0941801c0300d0780e240c2040141600503400d04114401c0c2000356159050460907401401e001e0050b2185000018076a0b28215220005041084402c642c07103049032203e60201e540c550f42400000d400040c104014000d000038940a03201000c005407021800001e813443d02d01d1628034102c0358012507900400c45603014501910385040402101d801004d0801e00e00d00314100c0c0301e189106601c0315698140202e071460310b885001081000400002c10001107020b80300a6488901f2202640003420f090b011072008400030001c64081c8074800001d508090781c140c0304072418500030300710048420f404400e440d01e0b6101484114002c0c540c07a103001400310b183c007120f00075813920100d803004d40326299020004c07600380c0f406507074900032070f00e1908944801984000f5a40008003000031210f856900c0c1c054800041806440c00c0c908100c0705204060000600a01c40b0b480912 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 555874145 1250 555872895 555872897
    0x2315060604050d05010b060d02030114090f391306020a03050406081905040b07110102090603011a1b010b0109050d0321090c0f1e031109060406180f060801020406 71
    0x2080100a2440c2c007040303540c2640d004c0d20001030042000750020310140c0c0038518a510154001c80100a65002c004000b030b0748810550300c0c8401c0d4039180485801e100e100402e00b148890b81041000302d007854100b03101c0b40010305030443c5401d0094a240341c8070907800c05068400c04c844504408190184081180d06810303a043d11000e00349804e01005541d61840100590074010840e0301d0003004c41428084c10b402140a03946181403810300013002001c280d2510300384200c40e8010090b0602e55103500c801c0340e04480c04582c0c816055031600c950456188100c4074106400200c0c0d422100c481001940b01e05400c16007600c0c0d0030415555a006d000080742440d1f805000b0581034182c0e010311807a04140700f0f108001c04640007450040c9540c8032240400b00384c12281246186030001c1c01a020545501100e07201140300700031400745181e070740b0b50300712800b100110b004402040c0442c1f03184c2c030f075600b20002030300a00c0750500c8800503440185000340000308200c1c64040c100031000075101e10620847d000c5d509a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 555875395 1250 555874145 555874147
    0x60117030901050a0e0913050c060702012c060c0c0108060a03030c060c050d1e0506121c021507020d0f03112508030705040f0f050d020907090323150606 67
    0x10440054070f49820000b02c080500c0102c401c500402c1d074458204921807640400c40004160442c100585003a1503510400d0044d41d08000c01c8000d80c6e042901aa11450f0701000041e0000c0c540303c0030164011000c0255801420218441d00510000b05944070070517001c0ea01d1040c035a64803410801d07024020720014020811743e021881c0171840c207402c84000040d450509529086181e400d0780100e80190030700d10160310400303082c041165035a0043c01d8000a080750b070b880204141966240e00c2d0010101c1e90078841200b6201070417100d000780700c0d104114841440340700451030400780180d140d490b200d0740f400000d01c107125a400840e00070b200310354058441c20700c0c150424041c038000c0459880602c0320110703182c80130308a0b4400650001c0081d88100f25943d0750740d895a1906a0300c102c078882c1500400112400044148a25169542d494200c0d5404031744032006522442c8080d1241d490300d0700f003d008801d10300c030032950420000d141d400c8103507402c0040302d4211000300c0c00300406181c2580c40715030082d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 555876645 1250 555875395 555875407
    0x1d09010e21030601020705091303090504022505070306060906081c050a0e0d08070809150f0a081305060c1801030b0d0f020604081515011106040201030e160b0c06011703 74
    0x7058014691094040c01101c2c0b82d81e80322000500f41d5031084400c0130500b103d91071181c04042e4003111800007008151021742c141007400b0703034202001040202e8420358010f02013100c2c050000c1001018000c6422660421881c1d4403131030301c3c2029103220b0041e0604c0f48502402820407100f8580844184d030701036550b140c24211000401c0b109020605003503a8480c11007841ea40201e8201c0000b003c0303040c412000b141d03840785013405205034048000d01c080b045050620406401980e40c404403858201c840c902002c0a60310b02061090000c0b419002501c54803403181007150f12400200100624030003000041c404265001c011001c0c1c8030180040c0703400c044c841c1d49900026800100400034144001d2699082685802c1407a1403e40c0796200818406012401c0c0040d0094443d080e510303101c400e10707110785401090105941d5035107020700028101030344d500b0080322001c0d0910840b0a0000319849211200365036401c940e000760044507040d90280100c100003d0802d90303806c1c4140107000e20401940c03c0032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 555877895 1250 555876645 555876703
    0x1e170402060f040e0f010609060206010b0316110a0f05011d191a040524151311070602120c07020306041506050909060703060b0a0e191d09010e 63
    0xe0414008031400b54400e20001c60055124041c06201d91314506070034a03207616100e0010001041603100c0015504400d0041c0030ba014100100e079070103e90180e2010401c40d81d4030007221407007608010010b0321b004081c0501300304030041d1174441c0c0ea0347c0607400038090035402001f88034030601503156015a552100c01c030701008040282c100c0c00300b40c0c090041002c1d01404105400d000c00e90480c0c0c01c032a56000403055801c50b203903010100e50f0004103804000c40624041d4110980080500602031240c04a4016100b411046402c4205501e1010045030385035071082c5882c401035000ba0485e81c04040f2210001100111448191103419030010028002500d854a841c8094208070354003105060300c075403000c1810340b1000308507402140c490000301013502c1c003240d0050807200b0781d400c070090071901040642000c0d6407004905620200451307000c8410b10300012655070681155104860307403922903200b4400007001d41a200c0c071401e200ca0091010100088200e0707194120302507110000c1c103800c04111008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 555879145 1250 555877895 555877897
    0x2091305010b2d030a021909361b0b280e010815090408090102100510050f21030702030d031401030602030415050903180301060e0c0304050316031e17040206 69
    0x71440107000d17034452507a6500404e0020103100f0000c040706000c42020080b40c404c1e4072500e000c402e07a074500e04034080302c000c5e83d510038600308405a0101428844800c400c0c001c8807020b0641c10340c0070007041c0042c6a03031424165000c4d0400c8a2441604080c03c28000c2a9494030310660310401c2540d45203d08015004015908030a0140000001c1450a015101680c4881956601036070187c030b403240d180e00d034000009160003000000800400e06000c140110300945500d844c041c1c1e8001c490098040c40c04130003161071498184400e00384242c1000007620035400200c001c1103a58001d03404d4444005540034280d01740c0300c1403030104d44040243d02c0100041240c0768061608940b04500e500c0161902c4101c000030380354150381f02586138100259184906201c2d1320404003800c02a0020701060345000404000d20030000e2800d098000000005010080c0502c22503c517038040d42000094000c031424010700301c2c1f0002007032841d86081c41510841050143c1c0113411a801d0056600c441961580d01b48001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 555880395 1250 555879145 555879229
    0x26120310080f0c101106040605090a05011a1005030709090c110f060a0f060e010e0a020c060903030412110a021002031306030f060e0108060c0a020a02091305010b 71
    0xa81034420804a4044401d0100072000080c05005042e420401410864003040d6001c0e0340050055001503030b903d032140828410350241c1c108100240c20341d9130341c2216007031108226005003a5481c040c0d80b80003040703414048058002e0141c61030311061403e81421307142d82c48152941408a48100e000f040f10300750341e82081c0c0e17001440f8500348040e0050000c5491603c100311040d50950b070003110800c110b038003662281444140d101d0806010f0903180c1526801000418058000700300307840800500e403024143c040f22035190740c00b011a2244c0c03421014a580720b42050350100e40701441c2d645046420740c414581d034181d20005402802001030700703130b003000b0174200440c444509500042c0703e9404a00c0411103a5002015284c0300441e0301c07070b01554008200c94998001ca502d4200c1b00c00107110303012000a11552007540001c52564890b89028180e00e443d0340d02600940c4440e009003000514014031511120130b0303208400a10104c42d46c8001c019007540f448050310060a8200c2000c22103010700d180f8400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 555881645 1250 555880395 555880411
    0x60d0905120304060209330d1107030c030e010806092a03130204180b0c0705010906063002060901050a090509090109031707050712030b12010501261203 67
    0x20007a0031032410401900112010f49007280c0c0070542070144d040805513020103218282c100021403d00300108044454282e4018211a034081480c0c42074000552003650341d452030429154031034889140c000c08020500c0811400141030140c00241540205441802000c0c000e0850340e850780c42000c400d203102040440c3c406d5000ba00c009840902c02000d0085004000002400b52008043e00602007a100c42c4901e04e0440000c0900c0703000840d80754911241c208228040c020b558403030741c1c1441d81c050040d600703001d00f00a28046e00090340800c1c00d1207001000282c4042c00780c03803009015403100300c00c510040c080e41107a820801201250f201d00001c20130f40c0918141380c00c070181c075032000c2980d001c02150440d00c6a9500e00044c42410781041c040c2840d58105a400b40a5113811a0010001c2c021410010246103c064084492501a401501040c94054040e1002170084505070b406001e081c440e003404280d800c01c100920405a103469900403c020340200b449441e01c5124500d50b07400103203014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 555882895 1250 555881645 555881653
    0x2070512011e021606321506030411060a020f0102030c0901030b060a020a0219120c050414151512100e060f1807180e090607110a0609020105041e030b09010902060d0905 74
    0xa031621b200c8642d40881d605840901200740741c0356214030a00d0000d0300045220b140c0c244100000541c5d003031240021100c0584603141c541c00da00b41c043e0b14004600340d2807c0c19500110801094121107000303000403c03001d03a410b100c001d0694091248611418003c040181c100240b02005420500303800c18449184a840c29580c980d40c1c0c8071020700c1070b01000119a0b45491200800c0307030340742c14000c03082c03451150009a01c881c00e280d10728040340c1ca0360080c500e0080381c4080000252012410580d60030b00d60040d074100d901c1c64a000004107407615801101c255000c0d40021030064207043e00201d806450160811f10f010110383d0105928200c002c12000400a10541050301c1081080c10a0700a00c0394600d0341545040c09100d25042c00380080581c41000840360342c030110301000140c2c1c01092600044001041546400100c4d403034401d0b1b40101e5196504c2c2c141d5404c081c0e00c50000c0504581c010b141e8440c594444034403490a0b20034121019510500500c00d03603101c008a80c0c0900702085c0f00f00300300c0f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 555884145 1250 555882895 555882941
    0x151b120b060904020c0309040c05040f060c0c1a0702040e01020c1509010603060e1f05040201080430020d090b030c1b010e060408071a0103080a030c02070512011e021606 74
    0x3e41a41e000301d02100440e00040740c2d50006041c94040e4441079030441c10300c3c40c00c16061a18a4550036440e104100801607820041c500780503030b2002d2180500147c03a0070410a801c1144100555482a074089014500d000c18416000d40184243c89240c0c0344000a0320696100b54414404040007600d0340900d035680b40390010001d12244684004034110ba0040e02d4081c0722182030b0304646000c0200b400e40503091208000c0181c0c1c2c8080300070360090780503170f14040e40b01201144a0708100800100c2c0494031461282c402c14a40002d980441454250349542000c4d440340c205004901003034801c81c08181080c0a488000c82d84449100c901c050010000910005840306103403502d501914142c40d40c1c640080c00d038081c40078000844440c12040e1601080551541e5181e0303690340b184460300c40801d581d5140b0960b2080c07081c4041401488010248259240161a041c3c020f240450400c2c1d9030b03072440345107070002e60514000d850201001001d21800018a511807030050140c2d50807070340070407000f8004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 555885395 1250 555884145 555884149
    0x6130504090b0402121203060402030a0212010311130228021212010f06020a0201080c0a020a0c0305030c010507141e0702130b120f0c0d020d0f151b120b0609 69
    0x644203641d030040080c811181818014801e0030000d540c000b84443e00211004003154404608507600700300c084c1e0740103030b8076694141850002c0c0201801c0503401c0e65448000410301031641c0c0c0056250b801141c4400d04c41d41850741200403072181c01c0205601d5038008598480030f142007050b1410b00210b5005580004000b01d40e0040c2d2944000140106000541c0050188030001c03445840a42035600050076207109640019021500090400c80c51030000101d801c50144240010b01905a0000701210303015107034907003c0e4683e00a03141c82c441035840c12000032601d034441c40320100741d046130341e008500e0991203500c03a40502001c084038100b9220b0400c18000180caa110403005041d940941c0003a40c4c000180410202d182650f0260400364031643c071244038080045842c080450080300c0c04021200203201282c3c1694400001a01d50a050b5610400348501c110b4030b940070300d04070942002001c188030444101c0072401400d41c40041c4450b414011155a50b502906141230018089420a075103640 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 555886645 1250 555885395 555885401
    0x18050306220c08030d1109062d070303090203060a15060f020114070e0306010b0414060705100207080301060305010b03070f05030a0b21061b1603050c030703031d0708060606130504 79
    0x4462040f5030300010b6003d00596080c03180390100c0001800e194600810000000c1c0f450080c05042d00b10b1003801d122904040f26400030041250310182103450701e0300c1c1e1608000e0003c14400209030300074040c41c4001603880071944100013450014100458401d42031034002c0314107c05400c1c02c5000e41d0b6841840a4144000400c500c0c4110302a5075101200d0410f0424981021010392080c5a503000c00c0c041071056581c00301b200e00a00c201611000c0d200c00c03650030320510344030346082071440e01c034030005509080c07020b0803000b075050f503900e074a06010b0b90b40d80d86810710441c801100c8034800a03000341400b0850600c668001c50304040482d1006c112440e40c0da001800c20b80005c40b44c1009250304800b42002c9034402d104050303000b109a00b02c164020102a070200541c49103414452112116410540405000e0340560326031011000071030341c682000d440c001d802448040034043c0d4103002805404080d017000030b064410340d4185000f50107913440c1d030320910680f600454081c1101070414203000c5020307203540c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 555887895 1250 555886645 555886649
    0x7030b03120901030e0105091b13020426070506030609130b0906011403060919080d060906030b06090402012a082d0f0324040203070f18050306220c 65
    0x10a06641c0d1980d00c40090121005c0f80d10010042e410311080000764000820800301c50740d04e04144407500300701c0341c0008100a80001d00720540030300c041008140580304003180f100f600201080d00000d206680c00003540c54540d0f200e000c2e403141c01040049d030f0600702410856005102d5200d08036518080d036984414032041180c003804d050380704500400103004290052000b03044158042c001c20308154882ea601c0f442c50b01000c3d500883c0395046031040200103021a0004890403004001064444407840701504c070343d20056038140d840300b011502c14a0441602c500980e8142c40f92146544500185070001c10700c1c03c564401c1c0d800b080307000404924440c00a159041d0100440680c3d003050031021084988500e06110310440280070707815900341ca5108480e0003801c541d99074000b00c802c8414589a681d0601e09841d0401d0020090180841c1c00c54140d0041042c42e4540d612481c0303901c0c412206c3c650780c038440c0741c1e8542d000402003041f004c0310220108139181e906ca81840d094042d500c450250452503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 555889145 1250 555887895 555887923
    0x60904140403021e070510021608070e0c0f03151c060504020909070b0d0b041b02060618060a09020f07020306011716030305090f011205090d030509010504081207030b03 74
    0x304000030103034184084202c200d41c0c042030082104001d02c1c2d540e501c200034004d443c052089569452080c6000308004c031024000848400c2c03415845500b5952104076a204107540381c1002070228841c4800041920785038120b0342ca0301030541c0e4030920030700c40940d900034095800150070111094641820349400c48680d02031b800110300b03030801d84180501d0038402040c1101940141e5030600070201d503a022071300301c594a548082184480c500028008100344180d90198041c021a02d40f1410f4000c0745203441780c10102c501055118034051249120304084400960111307006034103000b4043e56601800b290725803070449604080859010920f0030300280c0051110092201001c406035108001520b1440013a11120202c640340d5900646140903071200a4880d503440308080d1076503449031900c22001d0559550621041c180382d80030f00d0f25084044101c00010341003d001a031542c2c0b05000b00c2d8051544107040f0351410002a099540000c000b810030b404140e2514281000c5036002c20202030740e041c074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 555890395 1250 555889145 555889181
    0x3040f03030605100c1e120807021203240301050702070b070c030f0b060a060f020a02040c0507020904060c02010f0603020a0b130b0c06060906030f06010b0d0f0515042f0702060904 79
    0x6900f09902c03090500e070785050f042c040f002c0c29200060740c03c10b1f4560780c40405040807010b6481c1d030340d03040c1e080544440b40a5503403080402009040d003070844001c801001c10080b02c80845400c80f0a240c2a41c07002c6034000096800582c2c04c110321124140201030071401003200e40b03074980e1203540f40031540c80f03006d50130395110b001601804141d10709240390340010035a03030410080070480820b010b27480710502400a4400c46c0d489844241850145080310283c0d68010804240c614283c507080c402050301031032040066203003c00c108509074081c8190400c1c0ca80040c0000c001900d004a440382d0342d8803400803002e0101682100041c585900006002050307483c40251540b403030850184900c80800400c2288a980440e84030310000d000810410f05440e80c1c0340400d0790300c44030301003601c0103480749085000e1250724110403c0482e4200b03c2d20006695401c46091110034080c06807508500001d000c901314070007100710003140e02800f20000307001042c4050a45402c08040a0014007180c2072209201a0401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 555891645 1250 555890395 555890417
    0xc09120102090108070c1106030a0f0c030f0e0f07180204080a0c080d1412180304060804110301090b0705070204090215070311030a0c021c0b090f0708060c03040f0303060510 76
    0x4e045090194400e1036803815144540c255114030a5030081d03200140e000d400300001040303130b2007025004400c00352160b000c28051040c120000400038510b2a200e941c1c07030f91074118800c040c6c440110784150a0300c8540c00800c1181d007007550080d003002c00108003401c1c0586c00c00c000039034a041440043c0d0894095904100d10030310b40340d0300d1810420604030540421150829024101380e5038420390340b40c00c3c1e04602c2500c103a035a90701840919840c00a41c845e142c4800310f40043c1e001d602180301031142c1c0c420440b40300d484025406150a0301c00d0103500501c181148000504107500c83c80140c485580020030128003004584c002ca042d91520703200c06261480700091644c14150040905040f0381041c3c0002e52800e000010000c0c0741104a45000703104001d000c20111118081700304a410f915001000c2d40000d0600c490402d0b40d46041e0f0030303d0b81e0309020744200080d403100003284142c4141c00381042d03a85141d48583e01c1d0240799140303000441c1490f0395802d001c11207840303149120518600607220450850 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 555892895 1250 555891645 555891647
    0x315040c0e06030109170c16080115210219090c030b09100e01060c0204110d020421023001060f06270501051b0a060209040b040e060606030c091201020901 68
    0x41c600514481c0281e0505014000040205200104004414003c20b4403000f50702c800300c0c00d200944640030400c002200001c51819419849640c1100583d00d04900d46036640c85091101540703454030301407011030141100d0143c01c08131400c0301040c1c1100582c841e0301c0d4403541c3c031804903645003400700c1c002640da04c1061204c2c28481a0150445030380017091405524210000c40c010a05000c2c0c5420490742c190550119122078006030f11240551540350344404d100c801e504002d40052241a409000060464400140b0200100ca210f40c024101445040c1000c1d00b4864040d4030b100921240885480d1a80c03005000b88510000741c03140740c4488100d0741c0303020707002400300292200388d0611070002c103581800c9400075410745003154002c1c04c043e03444926000040c00450081007021364180504900300e820071110b41d00402c2c4104044608001083e45201404115400300d42d02c03201c1c592011011840c20320703180b406507a0000000d21400d140c165044007140780e042c009000109a03a4001c42d14403103075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 555894145 1250 555892895 555892919
    0xf0703030e0f100e0106030f050c09011712070f0602030a0c021618050c0403021201090317090c011d03121207050306010c0305180d0819050313110315040c 68
    0x71190300c0020607500d80701803030785921403482c4110040819652000303005018020340005009540284004007041554108544c480c00c4481c1050301c1458090300201d9100d2894280d00c82d103141c104002c0a04144480345007174981c0c4021420788180d9101c03500c03500028600d000561050100810200e0441031000019180c4181155007114035421490309220040c1000b04409a100001d040840d80f07440784d1086080612035600040c0d000b10514401c40443c08054112400c450300c2581c55500042c40c00c41e03028206042641c2c926555000442002d0296220310f804500d680610050300641000d0100040d01e0420600c4400300096004200764085c0e4054450995020945041540c0385150010000300315241c0c15200400784000801d003480d4101b01d1000d00d2501d0b6002030480450741102d81484022074000f5408407883c985070113010940c05200b0404d803401203400031200c03104d229582d9504254481c000003a0380d00b510807900180b084131612260a07001c0c50252124800480c1000c2c01c003900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 555895395 1250 555894145 555894161
    0x90307031b142103151e100203030f070509060a3e010e0601051807140a200a08161a01140a0801050c19020f0a0c09140c19050f0f070303 60
    0x100708040c010841e03030403094a0b09141448040710b0803101202c01c80e2842e0217144007000d40039042a105143d540d0459000001580640c0c210bc4120080350303a170b16021212446080c25081d00240180514022103000e00c41690000d000c501c4500c1440208240b802041d454087c8103420070200452400b036006000e1150503a000c41e5440a84402d6040c140400e059100040e02081586849400203a40d1886642c0355501c5030501001503945200b074182c018001c00310211004481c61606152858950000400345840d40d80001200e05005480c004800c02181380c450503140c842440c5418800c242c03020070045c2c043e00c1d004030b50390f180c41d0320001400f50071207190300203484580c500b0007808440e000e82400d682500d100b003402e0030b0b52002c1e0070204a09003500303001e18129034411904240c0030401d5404a13a4152220720008002c20194581201f002d50340580303452008050800421942500c00d0444c00d2120000b420400e103400c0031400c4060803a84901011841d42c1d60110b821002c0640c98091007071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 555896645 1250 555895395 555895453
    0x2130608040b0705091306081506030a200607020301020d020406030b060a050301050f011106160f0f0c141c030e060a0902030d0f021612110405090307031b14 69
    0x400746000d580d07944108401801c0070090140c003080c0c0794441c0d55406018003840003254800d0140a030b94603c07441d910403804802c51651111100010414100041e200d20702603013180d102e5248000801c03450507c0d45a08a210390803000030400800544c400340001c002800c83d103540169100d1a0850080440f0004264140718400030004240c02d80da0210699055803011252912034082c00801a17514804821148000c0c3c00307a60704000c90100c8545030203031020300580b00c00d410f1941100c81225194840c0103000c000c00da00090b0540031480010b003440e0503212080485044282400301d500034445c40310340b4000060703210101d18812040c20b224040e08403c3d880824000c10346140c0c002603c2c0c1c2016050701c0b00f04092425030702c82d454801c005000011031f2108071800140c0e19251014403080040c282550281000780c164422070a0601c500b074441c8140c540070b10708050b1560707030441d2044822882a03640c070014034545d00205210680011021020000500c22451060f48810b030032114684803071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 555897895 1250 555896645 555896657
    0xe0402040e0f060406050d2a06081f060f08100e130615150302070501060b0a020a23120a090f060e030f0c130f0f150e09030a051209011b0201021306 65
    0x2140b43c07900000751f880c440e8840c03c2c2800d1200e560212007c980714000e01c148032186002400510135402000e200e0080010040c0910b4515010b0144401404544180c01c00900500c02c1d0343d0300a03100d003c1c5075800106603028a2062980c03014900c416a405903030754901740c01c0f0019003204010b070511400b02001c0803002c94071900c2e07142200c583d08141000c8028402e143e000a683d1007000b500f07502180140c840c502066480c2c510303c4c2c6000b503940e0562041100d142c29510350b0382c022805a20b00d1081020701f04030061002403c5c1d0320098466400407079512003840504030307012400b204c41d018290701030507140d5200440d03180184c0c101442d0511b2030300d5400590708104c1c907056107919501010140e41060f0400030421007034000180c801080040d1040340c4240c42d041d48030400d40401c90440c011101c0c008014295901ca14600d40d489200c4c0b20703e0030000c00c0040205280d0148260f0b1002d41c03007020031000240742910b400000a00b080404001c01c0183d40c0010144288820010750340d000c6c050601e880c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 555899145 1250 555897895 555897899
    0x306060905040c031409012012060402090109080706050d0507081302120a020303030f06040e030c0604120306120b01081b1c0f0c120215030c0315010e0402040e0f060406 74
    0x35000d428607008040c05140c440303684201807400b940051141e0403980050460919008075094001e05400c0b0610710140c0c0101190101d880c291402e4a82008441d554074030640c4a00302080002d5006486640c140400e24038005100d01c024040c1c000203000035201e0039503070500d9030842401c036000100840700740600c80e01031007a01c980c48401c24803035aa05503000718401940203855846c10b0a200b500175458840082001603041c0d400d0003860207450150350900040a8900c10305881e0301541c2c0090407580d10403030010b000300300d050715034104076035490400081082d107500740c1e07054184c01468203488001e4400e004005003030341040000110380c6104e8200300b69221480024002c1c0b4580f0b0401145003030500c08038001e120903e00c114101039030100c1204641541c500840411100048050388101e0a00c180001590071100440340702d442424296450b55407107000c0d200980b8103071243d640c1000380d86411045945c5680c80140301078441e40c81d1600441c6000d0303860301c030f01b518000c1c0410301030740c1001c40c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 555900395 1250 555899145 555899147
    0xa0513060608061c0f2102070f300602130311012c12030412120206010906030b1f031506030203190308240a09090204180507180e0a050f0d030606 64
    0xf0080c4075684152071004240d041c1c2480642d902c0d0340303103104500c0c120745a4140081b41d000030b070314000c0300d00860845070703030710b66800240b4041c004280307280c894015048200c06e03c00403800d0400740d02ca4461130005040c0450307210200000080f0360422950f00e40d074034140344a41d41e000010000c03103908a400d00c1c0002c1240060b101d00140d000c0c001d403400b803001c0380542e0080e220248103a4016010070080c144003a030103802d05600350610341e407181003d405600004031701d60035240502d000f5a9001003480b11942c86401d0000c3c001c1040c04114400d0844209000c00000c10700070101d0001e01c000c0601242183c290300400d4204000d003851215140b160118140001c0e400c882e4081d480160300140e00769040e07001c0740109043c40180d094541c0030341881e101081c40c01f40d551118101324003e6604101c4845170310301c0740c0201ca50740308002e00242e0084804004840450044001d9840c3c0001c0100d90400c480340080c0c504110742404481c3c0750072040f0008040d00b0300308210181d651462800740269854050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 555901645 1250 555900395 555900439
    0xf03010e0d030c0207080f150916051e0a270209030c010c0201090314010c08130c1502030906030a0c140a1d0d0b040620120105040504020a051306060806 67
    0x601c00189600c035400e2448007402030014200400f12001600caa0011070301080d42c64442c3c1d10209441882030710049107004c00005044452901d84241c0c04500c0e5042100700311400780c4050303201c01c01d4103c400302c40c01301c1e80783d420969000f030017440e52220550245024803517140078501d07280001d040c1306010040d020794000910004440c0c0a013031044160540703000490700c5114030b800c0540180380c0e8142401c40120150b0018a1a0290780d9603180740c0d4840941c8050326500e103081c0a45403808100301031110245122118020700541e0049a180450000200b41d4507041140c001100c01e03038440d1500b08070303500025002007918811065529019035030301c0144c0b510325018509581504400c20300100303501d401c0080c1000c1500607240358000d1400b403805001402c0203480d140984004c00c0381c4902141c49030801d44101d1501a8100003250303003480140801000002d100380d90010000f400043c50b0385a0780c54803200d041e0850008501c8508141000c0c29074070300541810301901240110082501e0007807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 555902895 1250 555901645 555901663
    0x1b080403020f0303160b04030810060c06110c0a06020705120f031f09021209250621020705030c0d08150d030c05010e0c010207090203160503100b04140f03010e 70
    0x115500c2d0448802d0010030320354014186880b00394440341151206010204072041e10891280c0d0300c10506a41da1040708402401600c240804074030702c00c9081c000151250060400c0c0403c0100b014208170860281d03626011b00d160003500c1e940c3d80081c0c20800c2c49001d016042e0343d000384201c1c00d46040850b4a0486051000400d403001c1b02c051480c1e80190810240720400003030100b08000d64a54009000040d00304000751424440e51240c00c0c11407141c0b0345282000003d00c0aa540c10910051920030f09035803e0000038000f0560b1909125401021049031001e1b01155000700f00a40e12507040f88907040c03a0591040b81003003440303080020801e07050b402c000750044850f01603a50354040091071900751802c0e0740461004019500341014045055400906142d10403800d03422a5100c43c0d40e4080001203100545e01400e58000d1552104a803038040c400958200f000100210324450340d1740189801d94100b03810031440b55940116000480c5046903105800384002c400800030280e0b0140381075a04d030650 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 555904145 1250 555902895 555902899
    0x415151d0603180c0303070c17010504050c060a031104030615080304050d0201030902030c09150a051e190b04060203130b1602010e01051201080a05060f070e01231303031b08040302 79
    0x8800d0883c142005001ca01c5104070007030308680e02e9014600c0d00d4512501d00f80184074540c500101010010f010500070580600d0f000005481920002014040543e1007084498189a1103081040d44400c9200041c0029030082400040c460141b800d40c941148082d0321190304c9a0043c03109206c20754903100505000703903090800040105461002c02e06056000d00e60322351000a40003003012001d081c6402c1041410201d5030704008076120300400c000030b480c05000c80713a074044d94210742e5120b082420400d001c813000c1c80c0c121000682e44a40c8585940c0c401d80100005810116484018000300840d000c082d0000440740c0f0304003030fa0310003010350a0510325001707410002c2c3c0703003144481640120121400e882003841405201e684444249596075103182040b5254400e2800150000c0c0903140700038002c4110340d407904da03110150001190426280003403c881c400c11403080002e185034040041c00b8814820305440c141c1d524504010b000e510802510001c004407801a40c400240315a085401742da0f81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 555905395 1250 555904145 555904171
    0x80c030c03150c0a200d0f0c0812060d081903060f151206050411070510020c0615063105010302040b0d09050a0507060512061c03030504020415151d0603 67
    0x1040400c840da200ca030046021700135050076000d64113a00100b80002105000d03250500c6201c100c09085904115407480030f003469909109141b2544404225140c100c01c0040824140c17100c00d882e0a0095489480500000c1c921030005102e4240c040c01050003c21074202d008003071307519284181120002e012a6102005041c0101034419800340e84080702411015008000c0c000030000c200c00994000310b415a114410402c0c074890b200001d008407031850302c08502a041645a4a4090342d040200c1e440450f40680d090080c0c207112442c224070340c1226121070f02947c10100301c6040c130039001e0703801740c01c040d0415004001c180591808002111020056407500042d1003005080c41d504006411500501502a850000131f5045e40312000d040424a060310400c0d080d281d403c20441c0300301c0c496400d1b0314240340349a554001319000354000b0b40d1240c00984003242d80343c02c59003142c00070001c6401010310302441c1d03001543c142e54070a00c9103170810b20000d24902403600f85400200e207404028480e10354511 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 555906645 1250 555905395 555905407
    0x70f080406150f0906060e10020a02061e030c19030b01020c010c0305070803010b03010f15080a050c0c0a060501061d1f0210050721090314130302060301080c030c03150c 74
    0x14000403403008011210280c81c519444240c80c1340981518800e85000500300506141980303804201c80304003600d503800500c50001ca45e4203000c103d800007160000d841807101da00440d01305042e8015441421011010359951245010340e124801d030040200c01003500d0041d42840d40c0e600065603840e80c4d102420031203142d00007458200d5940c0f01e4030a00411580f00400000fa50645c1d1101441c180c1d01203000d074844c0541c4030070144201c540500c0307521002030b2a4001045081403190710040d0400b4185244510380b420907109a403500b00000d508403503042d03580c4010441075a000004c40d100c4111a02184800b07a6024000740403658a0f03011100c0540f5407103400d0342d0f110f000f04224502114124800e106c94a4612800352004018031140382540305500041003000d8560303c1020500795150300d4250107810220410300306070704600603102d40c0c0d401c0e8410110140c0da03040c02075402448181d000308200d83d0321070305040c1811540e15601d40a40d120303426501100034414a5290f0159880b80001c1d2511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 555907895 1250 555906645 555906671
    0xd18021005030624070818011112270616051603080f09010e090a1a0d1211030c030f0301050a080307030923100f080702030a021e1005100e070f080406 66
    0x4410410300506c122070001c0c80302d40c0304e9820304207280503001c240c8070040264104c0702c0c0c0c1911400200944e0040c040100040a0409140d42c1e44c160440004020003100301d004c94040396450b0311007200c9642614a41c0e41074001c01004011210415490f64162005d8500c0c564415000b40210111051a200040f5400410745d200300072070700c00c90100500108060401d52503400003440d1030120f06009807094103544116091030301440d00304940c890354981901c000c1110803540301c1030501900610740010000000146400c001504030160700f0040c00784d0325403401081210011641e0310022040e0014800780c000b00703811001c601c04030381082940320b400e16940341c10141c0c1c907038840c07450700d40c041c0e28000300c041d2143d8444050200340e02c1d070341c95601482d110a002130f42e40303004140540c0c0043e84500d92034400e180140510310b291251035411100580800c050324000d4038000c44140c0c0f03c11141900820607080d80f103503050b8000d165420b00070210003103a500204409001030024203040d403107070803036074582c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 555909145 1250 555907895 555907897
    0xc130b0409080a03061a03130507030507080c0f0d050c0105030a23040b130c06050a0309060507031b030b210a0b070f020c120a030f02030d18021005030624 68
    0x110401441000000c0c001d150010440c1c0083e14100300092070503030041503030b102000015401c20011941c0c5030659a6250324014030700000701c0c080381c45d1b024081e17000000070010170501014002c60805050414070320380500400f4035010481d24072441c503500d015404281c01040c1c241c00a8400c0ca030045e5641e50b503206150203015032070400c000310030002d0030b425918984520040e004038400c11070008140c542160011803000d0071540a0942e006010041100a02450060852480604020400410300c3d21040c1c1104d40445e00040825160508081d9130445803c2d010080c0340c86040800c52840e881010401c000442200740c1031100c2041c0050340814810410714026941c00f4000d45941d15243c02c0c01007104004107003240140c807c07401208000e28102030100341200c80381c801440005000c0c1c070102c504009446000095000811030032861009030b0185003500744180c5c408680c9007840f481800b4080401d24080340800c40180b083c8070103a541d454107250f000340c42840144540d00000918410707 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 555910395 1250 555909145 555909161
    0x1c0803060a1802030402010f03020304151e050112030e06040e0c0913020c070e011706060402030a1808071712150102070810150e040f0312110a0305040b06010e01020c13 74
    0x2c54840007104110b01209500194031651003a6654841002071040903000d07400190b800624019a01d030f0300101c4014140e000c440102c000503200702010410b072242c60700b260000c1c0c0113000b0541100341210240750b005101541b003c6026101240303020314150115207003000c0035081c50101d4100280e05403240c2e5445030480c4e4521207840781190f6650300c0300c604541d14026031040322007221211b0300018011510502000541100c0c9015081c81d076110006c0000950001700201031103561143d4030601c4410000b0b54000c0d80740306448065441d045400d05038001040341c0502e14104004216600c0c104413004401c40c3c0044031010051858003032200140d00701402034100f64011b100303134504003c4030b51640e0040c01d80c071040e0814107400b6a4417080d44001c680ea0454024000750010707406140024803541190300c0c00452444006840c035000c0c40280307640e501841c11800025100d40c1400140104da84406030481d10034205a50b403d481400041d403145141c03054107101d190b00c040000420881c58101c1e000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 555911645 1250 555910395 555910409
    0x32502100c03020d05090c2202040e0106110c04200c07081002180307082e0c0c06150e1614030c0c060907030819050d0f0c0e1c0803060a 60
    0x11a41d1070000e8002d00a400c4400001e0b840c2d0309000108a1214001c14002100c90000d1f1915051020030708000030344499807a0313109181a420400010502c5904010394080c1c0882e644010b5a400e403101410b02d00101e80c1e86d010b01c0b0300e25060900013034016005240c0b5080b1001d05410792140c907441c00e014105907040c0d20081139401510601a5804504da00400a19035200c0da041d1034070f8445070030b00d40c4d11003d40c0600310003544a200340c0010240070100c0031950351404198070b000d8030880c002d0003081c1c1303000c0305100d000f2445200a0300d080100a002d1a2401040804007440d05441d04103180d410b1000540340c2c01c0c0d0700510304000407899105031030f218055004070b01240d5403400c1008084480303510160444180b4042c001c00b0400780f60001c250101203c1e003113200f0038104503c6d02c4c215500710580012f00003e00c01c0811200b00d86503450b020712400f080610000060f0380c4600c010181030143c40c0ca09841c8601c0f01000c1c49040303105455030118055402c50360541d180c0d9101c0700894030840d02c0740c0004d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 555912895 1250 555911645 555911651
    0x50109060f0507090801020c06130c03060603080306010e060901140c010b0a030b040309150e1302070213090204050a0b030303041e1a10060302040302220612050102030a1103250210 79
    0x70031202030350425070103490299100b005840d51076001508034081e40499482a0708060040f540c1b50540d848080d2005020300310703400c0469500d541e0041128419442103800480110400c01c2640c0c100046c2c8081403410ba514a190088510000b0304140b82d040c988114528086030741c5410207425441814000300c043d0640c045251242081c501745081180c04400080c2000000700d1058220341d101122074455458510000c0c008104100c1c18061801c1224041c1c0d50030b0100c907025aa64220450803116002000124481c0c0e40c010b010640340001c05000015040c030341036440c3e946000003141d0303015811043d03903507405400103040300c1d4400e00c10001a00d000d0703801480c41c00e007100309190540a890400a2050742603030f070b03050680c1a40214400698461706040010b8000e4140192041c5a1480c1440c0010301d542c42d1038109040c074044c41c0d020785035690b010081203843c5040f0301c10441c40d4000c81000c1070843c0fa080050884040048056244006003440307000d840500810151554254000d014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 555914145 1250 555912895 555912911
    0x50c0a050c04050c0a0c0f050a240c08010f051912031215120b18101d070f0b0a090b120f0708070206160e040c030203160806091305010906 61
    0xc1e540740100031600c1d110314a0240801c078103680d10b41c1155080f28441d2034184580201d5101e00b02000c6020380191135502a1080c81c000241c0b00c0000110f0300043c07011311840740f0807840c2255003102c11400071202400f00940040c020030300450307402000c85804035040c004c04811505010700e9480c0c1c9621a041d200358280080c420141c1003400110501c205040070096078041c5070754803a2101c10781c80340d0601d20790310140e00030119840c807081544c0303c0541d42d6244040d015102c4e5881ca003022035907076540c4156803a40c03202ea00c0d00408001041141546005080c1e880c20300303c489884402c1441039138a815800a58107281600a0480c01e00802c1c3e02c01039151140342c81a41a000e1050803600e014902c01d940000500f614040d200150048900307a0003859140e0715500c00c0d0301c00519001790300c001e020f189103000314260b466010f070b81d0500c4800d42d1f026849080c0b4240d00d07046010604859018441c4480410900f5100d000701a9404000d00d40c05680100050400d40c6c0103204004019200c03c0c2071200c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 555915395 1250 555914145 555914153
    0xe0714090d0f080a0c02090f0c091507020a0602210408120903070e15100305070e09060a05060f04080c030f10051e04050c0a062c01170709090b040b06031303050c0a 72
    0x41101039900075200e0441d182d540101c0c8e01c202c45001c603546045481d0500c900d02e010304109111301590084507101610301a9141c0004010501c254400001030f40001181280c0400da81c454411154814440509040c1001d4245807034103000b9080040400002c19105020740d02042712000402d9420410010b81c200001c0e1811006003010302035004104003d19600542d211388151031080c1c034265251944085035608010302010301030102d583c0480d0350200403500b690351000070304683c406210b840d99624602650300c0c1c10704900136030041c4030341c01400207000c11020203e041520940c0304040080c083e03960640d1000300074031b000b40014511304034104000802800290766614986d0803a0301d0780701d059448034110f030002288484052516100e00320100600e11a248940c45000141491011034100400e12030004a04807015000507d0300d403000c104121940c468405031a0098030706000c0c1c482c05d01c0200e803175484098106074600c42400c4d107210500d1300c1142038403101140c810594807007180600b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 555916645 1250 555915395 555915407
    0x705190806010215060609130b1314090105040201080c0706060e0c0703090b0f12190c021005090303070f12060b0d0603020f0a0e0601050a050f040f0e0714090d0f080a 73
    0x703034680c09440b4102c55815030014860607a44075042c014805071074082a0000d00403210484a00c04000c80c0d21140c1a50b440c0d03440d0103107184c10032041c1e0380c0014200c4074050403000641d40642205d036641d25040074080035036880348410740c0c005500100c40343c0c0c4654a02d4a0030040c20b49500c0815061070010910003110070b82d070010310925001e50380d03409600391214000070640c480c0b4117048852800401403c141004080540740d4411250301080225244c0545144107542e40c0c01760759401600203c8401c0280c001600ca1544c020240d50700a60443c903142101425070034120700000c00f40080f04410f0500080343da0808070281c020b200d000c1c0d48030b200e20140c1902605050108034401d5031109450155410075443d1101192086405411507856480066507079920052043c4108841084202405c1c45044005e100400d60360110589492402c2e000c9003080b1b40141c1024204451190300000e0403400c14103843e807480044520324442e5029182201210300845001842e0340000700f209210690094 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 555917895 1250 555916645 555916651
    0x12080705011a1e1f0306030503070b1008070303120203060d020a060503190b030d030b060d06030c090b1008010317041706010e13120f030e010504260702011707051908 73
    0x83ea07030951028603800040d0094440c840f00c43e80240d003000c0340810309a20f52001c041840d140d8180040c6070740e12030719114150782c400030058401d0401d0343c043c03005440c13034035000d00000c10300350014081030381c01c503580181800703e540e03486450650044081035642d52803c0350048034a81c020003c900d0a5940e84010f04030b504201d60085182c00c19100301204030030b2034051f510382040010090502d0b1401240c00b42e00034981d807040075420100078840c814001246120340c001441c02040d650581d1450814008155003846041034001d50041060b240d4068000d0a2030f4150fa5002132100b80d095940c00444070a4007455000361f812411880e0110900c0d000800c03010b050700c00c0b045c0c5110940d901d040c040400080450b200030315240d03402c1d4511000502c40d078401e4005143c1c628000c60084800009a4250b032402e43e01a14500550b130008085485000d80c092032420600740d12030304044454001a02c0304016051403d01c00722118009002c140c400c1c0c080b905541404842c94115468084004111079421 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 555919145 1250 555917895 555917899
    0x801050f0a24050918030315040b010e1809030d020a030207260d1838060a0512010b0607030c0b0f01031709040e0106180b060406080112080705011a 65
    0x10440b0768400005520412a080035a00d001200c500e25181c02e0054000c1c005042e42c2c94200341860400080d941400110702851100540c291454190810841160510b098160604c16208861410740d29000d08000c036000000ba00c0000395074505039201d04510580340d0112020f880060911480c40d010b501030003420b809034007410b12509414990100b03180e0704151283ea80c803410712005211100581101c1c18602504034042041d101c2503840c441040481c0c0d61030f14800c1400d003043ca400740c0c2c480351790031035983d103100741403070035041010104807181e541d401041e0044003058051070710b801003500b080c640f404024000750f90700e0089090040c030301a410390b821610445810046549400c2c1003804a0582e5080385d098000d1f201800d2202c01d0503441952400d41041d2240c0211907084420320411000f0992030002601141010019408644410b240e561103484144020312006500c07a910f01d040d1400d0964000c00740003141041780e8240500c00000b07040390308048102e440c807064010000380308402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 555920395 1250 555919145 555919151
    0x41b09030516060507080315190806070207061b03020a1703060108070206150d030e030d090f05040905060a02030414011b030c0f08040b0601180b0307090b0a050703180801050f0a 78
    0x120701c40104034990750b00c5000300241c400d10020b008039488000440e004500070380b010020444e50390100f9154940e03203e64142782503034510b04203c440014004154072914900c0541542410074501070184025051608121014007025404050007008041c066a4201000780c07204030240805082d154004c83d4554005869440468030250000038114058208642c20225060004041c80600c2c0c0c1482030039401c015803030608403081e840901c403005210a0940d06c0c21022424204500d2280340f45c1c0d44018042c2d441c0503845030204001143c66078012115610140ea6601c40d07081516000cd6800f607000e443d541307448506610310148000340b041c1e54100361028408500c402009495000d0503c1d03081c004600306200060014800740c65156010305c0c14184031a0a494043d4031010500e0035401c00540f80d40004103018a20340c002850400070801d025100749400856400101180140d000c01018055040c42d121005d00700580208094002807000700030700e1500c1c4c4a80d0100e900306076001e203d0700345 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 555921645 1250 555920395 555920413
    0x6051c110a0303080a050408090603070905040b06120a02090111030a050d0f05150f130c02070e09030304031403040602120c0304020f06090120030c070b0a110c0f01030209041b090305 80
    0x14120050400c4a8050702d070300d0043d540c0c2c50b00700c50191400420423100c4c62810080130517141d803104040c5000f00c0c1d0541d80e0a02c1c841c200024441180c6544051900c0741905009c032040c3c035400d101c0e1190344a2149500540c64911075001603480b420000060318040c0804541c1c1c0445550100c003408807100b42030418000b1301c8411801c0011150159403401c200c5100f6541c107a4503003032420f4030200200700038150794a55072490b50300c4000c035540903072014016000481304000c1c400e001d490705900303c54010003861560130666009419880040300b418840c5a0200004043c071506a060324005501e0f201c00c007001c1c0c130b481f4032031201c1a031084a00324400d014405800200341440e00039203d810406840c0c0305507090315590721180c58503484031885041d1104000d105041c55091004074020203000300480c0e12858030341000f41516101d03c42090242d13010b5650444e044c1d80d01c101500803604c0130300300180c0d541e1482c0003003800340c6404400c1507100306920b100270b1303445c51703100824500f00c0b0b0040301a40e514030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 555922895 1250 555921645 555921649
    0x120f0318050604051e0a0f03050705030615010c0c05040f02040503010c030614210d030902090a140403080703020c0f0615040203090c0415090c0806040615091806051c11 74
    0x10314900400d50400341c24082841a41002c0301100a8044a42c01420242d1807002c0094a00c400700e400a246c10309040008004001c8200500800f401c021801b0300160300c0c000106070456010011410f04010003109034400f4020190312280103008041d0081c4542d83c0c2c06c4980c03c0c00b035441303842258041d628080c00402224880d00c0f54400303071440c2c0c0e0404140c3d08801410803450407400c1800490024104520311201c4204100809104129031400301c1c01c100180104030030014010301220040b42800c0301032485100c5414016402a41401c111100b44c580b080224000e000300307000b1403000d2003400342c41c60b60240001000340c8540f25030300b00f80050040940900003a40000e90b00c0130b103554010a5045454505a0401701401346004a400c0c071003651400850169a070704201400800d501034140719082c1058003070b10780540343d42c140f6420910311411005211030703928403d8080e80b07000c00c4512002301c451900400c1c0203201c000d00c203c0402d03c01c2814000300c0040e50306e00301c40201c00080090340038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 555924145 1250 555922895 555922937
    0x2010815090a0b0301020d0e070e060612040f11060a020f06101a030402010e0a12150c0503130201030b18100f0b1b0109021c020a06090b0a030f06120f03 67
    0x1182010301948000c2d1141c42c0440c015001128810f41d00d550280301c0f41c4080c420510134202440001c1b0010030300c952820f000031004034800740905000ea803040145c5101d80d1461039054ac1c01c203074420800e072110b8000d410100603000c0c10310307001c4c0c0e4424800644581099400100201440500410380b403983e10b4000c1e80c18071440d00d070710440c0b400c202084149105000071402540d8014018144204800341c41c4d00003c40341e075800d4000103101507003440c0310404d22441d0ba000141504000c101004880c03e0040c0c05062800f0040403203044540103071912085920940110000140251083d58542988109074854510486074650303644c0d032081000400a14881c4600200d0b0700d0700d2800380c6000c10100804500340e4104811810941d20317142c101c40182c0710107102036110011102ca902c1108030b244100001c01c0d00c1a030090741000101728003030100096240484003490344c1410002902c941170107468001d03007016840404036070001500358083c402d02c0f08013030900354842d031f650840713030003460a014070b007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 555925395 1250 555924145 555924181
    0x70807080304020a1e120206040801020f03100b07020108010311010309080a110111041a03040c18050108010b150a031505030a03050c0d080c0405060c03130b18150304062d09020108 79
    0x2555042800800804c0e03201000b04486d140050b0450f450310b80c40d1a843c40c03d80c1d004202005100000008025030341d25001000c038060320910543e24a01074403a00004c06490707043c00f01130030b07441805100004980c0258004509503602028254541d0286c0300041c00040c10390b41d0900389542002c000428282044c000c440c1620074210304041c0b00c0c3d175064904141031304014400c8819010030700011a540d011000c00c00180d0120b46004201581801c6100303007500c80301d907281c901541640e10100303658030750342054a02c203101e90f160014503c42d8040c0500013210160344415018040d046440b810f0540c040300512891101408948541840040c1101c4240e021203c1d050010740c00e000501103440d10740c00a120f900034010460341000501803600e6070225a0ba41700303141440c400581a04203408040d105559488211031100c04d0781541e000d428418400104020801940d805004140300f4902040301d01c503c0001550764215106841008010003900c40141d020500002c0011030580104207620780c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 555926645 1250 555925395 555925439
    0x228060905032d0706021b101e050f0a1e020c160e04081920060105091005030304210c0b130f05100804062d0e01020c12030606070807080304020a 64
    0x403404100c5e8881800a4101e0380c603400340005010000945224200820780516842c55400100310154220b003c41303d0000100e82004a41410200841025001d420641c001030210012900781140e017848001161714698001c241803022849d4400c0110000704011203d061501c51404142c40b86502c9240d0402214001c203414010040d5684903880c04500105881441c10b1000b4400e2060301054030041d180510420320b5841031004018928100c035004e5089613810031281841818440401e03140c1c0700780c7c05900c2d00f5540b0829210005603e04d90814502e94012040b00c0c4455194100c0011550094803642044030201e580031601c0b5801d2003944003141c0c0e008294102d0b501000400750ba601d503008109440b00d5075038841800f9a00d025410000302c102110304002d280070040071070076040f0783c0702079801c0d8440d80c4107000c04400364000240c1c0340280800d01c1e00b859120303501c120000d8070510907080e0040141038081101c40420014402940c050307032003224640c0e0410784580c04079407040c0d82c122030700d6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 555927895 1250 555926645 555926647
    0xe061504150c1a0603160f03081b01061e050108010608151807180e01030c052206090219021618020904090b04021f0228060905032d 58
    0x4000440421a005003100d1810507580310900b81e1603000c0c100011695441c030f0030708103c1c10450781d0714081c401c0010410740703001004050340c00c0005034241c0f400c481c00b00810214000448035008400704d01c4d0305240603107400081c007421303440d50100141d600c01c10560780203094882d000401c4640c012500c00781a26601e07075500607a6130f10016080b0080940590303054020380a00d446505950070241840c1c030500d0603868407205040424083d04a04405501c9008081a98001071001817a2200c20700102c0c1d0084504d4031003c0c0c0c0780e1071248440c00c058100c0c0e90000d89800ca001070f002d03442ea006842070304040642c2c0e90b4807205845c406c1c0d13180d000e2034110b00b80320300038180103003c1070700191044440100c400400505004503240403c0132200307030f45030070385002150108110451a15460403086c0808002401d159500c0c2e10798040d607900350903e1155039982e5041c41405c0c891030798489408201b90000c0c0d092001c083d590070b041d51a40e2002c02c240d2441203003150607104001c0c0200c1d4040d50000118805 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 555929145 1250 555927895 555927899
    0x503070804060f090b06190b09040b01200a120e0f01030f021e070b0c0412030e040e15090c0a060e0922060f0b04090206030601270603060e061504 64
    0x226181030008104540c8140c0d2100d4075091821188121070016105c0d07044050682011810011010704640100702c101d2580c45084c04486816420780e03c15003810748010a010040400581344d0900d000000101d9840b0700320400c4807050005400369403540039550024a0600c0300c1d2045408888601d13965401500c2d8006190541d44039a110186032154050014109014036000202d51200002011402c0401081e030b04240310061030120f810503508041c4510f4545403940c1e184807540008000b0302440b00d00c07120788109032a2a00038a08041075042a112034048074403804012000c1540d400580348a05c3da0b00c00c20717a04002e80000c003078820079100d401072456444100044018020244841d080750a00a44510104084143c0800c1d04c03c5001160030300d6030301414822030350401401403107a400c100c0ba040c0544c498204030381d000603082c64000303044268000f42d00c0c0aa02100203442c3c491500080010309560300d980a8000d41e000b040c00080d46458010403c209980701c51201c0014210810007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 555930395 1250 555929145 555929147
    0x18150405091e120a0503010f1202091308121611010b061b070b0423010203180f030a050d0e0301050f06060a110703020d0f05250611160305010b1201020703050307 71
    0x10321507014111030403a92980e000c06450f298640104200101050012005110b2030071b00c4056400500750f00d40c0d0100b11004182c0000c2e07030183c1c0c007070038080034032640b400d00c0700501c0581300403500c5040181e00155150309186662018041403002e08500140303042125490f100418002c3c154082c90043c4014102008900d00e00c03401401c080d000142c9101e80000000c060396650060001031071119450307034200e4120035a90400544c00500181107400c200b090b13440b14813903034403064005070303055400681d041c65103400b00385081140d85004e0b0591007890885030202b5031007542c1e001011801c1e030084c003454698409a40c4410016117032180d00c41410701ca2400c0d001d204005044030300310320308210f0b0000340d0360340c022802003500c100050740c0901850425100b404010404a2000410300c2d24100c030b030302010030038088241940d001c3c040800c10354041411109004000c15904110100010300f55180d03a40340550091661020031b5004003179810148000d05010720a40310241d4154586910310ba5400c04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 555931645 1250 555930395 555930433
    0x20303040b09040b1503010303110106150e06211005150f03100e07080a050708090d0509040207150e06071806181203030507030e07030215070c051815040509 69
    0x55801d80081d40c13001d510000790383c1d65150205207a00c00c2843c0b542d80d411418018046c014044000d512681864420858081304940520383c800070303132034104500c0c03c507d00019030314400c40e01d00304003681ea41081e4981e0341d280c40150300c0c0038200d5035206001165640c4240810603807800c0b0b0521600c03400303004401017140084c00840d80710b0402c400491095482c0c4c4940c6c8040a826500e000001e44110b00300944510702e446219009012030921201d940341c02980f9a03940c55040351a1002c101c000701e003014090f1a26016500ca413070f48801a1460030f042105c04100800f40c4880700c54503441104007003003826014160280044149d13040c4403a03034604207181550050145000d200c1e1140880c00c0c0052803050078814003500d14883e6038042980d003820300d002001d40c0c040100110380350700107100c2000182d172030b04051007010140c80311468035500c09040a00700700c101507209030341182220620903010340403440309500c038024040e218582c070500c000c10b00040321b4003200d0b0000590300c040c0380d1510242c0300003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 555932895 1250 555931645 555931657
    0x1514060304082101030b10090902030c0d030228020315060d0605071e030b03060702060105100809160b040303021203010b160609151505090411090903040e01032d020303040b 76
    0x485480c840d0405a0b003c0400c403500740d00995840c498081403003400d840341c40380c0400401e0600003d11401000ba0002030b00c48010003450392045600c40350040c1014000e0001650019512560f2180e0581c020109130004502c40f004900c20b021740310301078491518002c40b86000c1d50000d8052070000d0941c0c0d035508000d007000b030060418032074443c8100c28590101c152501c0410b0f150b0346e01280308900c0d03106141c9410300c058442020342d0130a80041c405512b5115005210b0382c0b1138034103400191105483c00d41488042a824104080190b0010403459483c0c4001c01c01c4921a600710743d0b0041c114005090140020302407284691010400340040781516040e1202150061000140340c000d0b40d07482a40d980103403500264101c0d215081e59078403110111f601c030000c02050712403441900c0c0603562030a001f031071224894402c017040f20100310104010426540907001c02c0328107010710350b12420440b12201104214154450300428104080c14203c80c1242c0e81030350240045003401c1c104072660045403c81 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 555934145 1250 555932895 555932917
    0x2211030714071b060509040c02070503120d0615110616020d030f150e0604060503010203090a060c020f030a0504090e010209100e061e03180a051f09050d0201151406030408 75
    0x3c4007031000f10b0403501000083c50107498450780d03030140f401408103840800700340300155048042c04002d65140421060710713041407044a540d403040c400784410b000700b045070071804c8110880c0600c0c01d11039410100c141e0100b540300c4200c64403591040e5030490895021508140140c00a45500074031034066005044102001000454281500200440301c050303d684440d00903000b041c10b000203401c0500c1540f01524050700290709e03518011007815520b900c41440202040c1d6540b11030709843e0710910400c000a203040066a54540c06035100800b140c01038000c46640d00d01d4090480c5442905108030703240755001801c1c0d0a035141000205a41e02404c8895032a00841c0401c0f18000820460f0b0070803036a000032112850326030030111600310b4002c03c0d8040410103a070044030382c0c6010400001d8002070a00c8400c1d070300c241904d8441c074551701904603214024250700c01c094443d4032090b0103410460b1448109480401000ea84102003e00c10781c451192680000d420004100031400850040c003a0804c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 555935251 1106 555934145 555934163
    0x220302040c0302040b070b0a1103040302010923100b0423010e070c02060417010f0f0e060f0c0405010302091c05031b0c01050906070f02221103071407 66
    0x6601b80181441c0d80b547d002980c58000742c1c101d481c241c40c1e0080055100d0800745006401703809440e1040342c1032004c444507020050840406002103124045c024054000d010407140000c09401c4e68042c2c00a44a4891420b04000143c8050204002050040342580350002c2015081c00c05000002000400c9041002696414003035800340d60200c007110a4059050115500415154003201e103d44c0c1460081111000d00c3d07440104011040700a455442c0d0710142011003641d007c0720401c3c00b000e01440306002c00d52096010f4801c025000d45114580040d643c110400c6680d003400480e1164000a819541c0060b014101c41034080000001c1030a03401401c0043d00e980a6905528010507000c24090103000015550301a074075006404511000c0e03000c952050341d80078041080f20020306250130f0320004a01c03503044901c00c0101c0c0e501c69858082c407403040916075020001c1900c40c100 = true := by decide +kernel

theorem cover : BRFrame.Cov 555755395 555935251 := by
  have h0 := BRFrame.cov_init 555755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 555755395 ≤ n) (h2 : n < 555935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
