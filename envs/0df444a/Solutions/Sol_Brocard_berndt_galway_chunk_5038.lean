-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:32:18.889657+00:00
-- url     : https://prove2.me/submissions/8a387c3a-570c-4144-b808-ee5c29fa55cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 905935251 ≤ n < 906115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 905936501 1250 905935251 905935259
    0x1b050301090b16030605060f070f0210050a1b0309060f02030412080d0e010b2d0307030c05090a02040605031306090b0103050f0c040e0601171501150324090506030304 73
    0x10070740e541c0d10421034181c1021001c102014800c0c9a80000042152404005d010305080104030301d031190301003010701014003040707150800c58049170382c0f80075a5018040e420350300803100300580641c10802e08480485d408009404032a11300c010240190360b0107a44011405140035400d54007c1c2c0701c884144c1c110700080101054900c0910301000d1554071070482c080ea5646010a00c604072100000c1244103a410510300c003265075030300d03030302e60030083e500c009040b02d8031402e00900d010300e0440600568141c000c00b64004140025603074030f00c08407042540c035101550384030b03040101248281e004d4030300440e00a1020507100404003c030310001504c100c40009008100da192508482c2c2c09030300455840d40400d0011110000500901c0a8100240d0b024091000e410005c15254030f014082c24440070310410084460440030000b0344602110303c410b508040d41c48044100d80c02503491001c0c2c02113818075600c00c00c8103100400b61a20801010387c400c07003c90070f2041100150002800059061100b844040703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 905937751 1250 905936501 905936503
    0x80a0522050f01080403090b03060a052d091e060f03031201050a0b0430080c0f070510020c040c050c01140105150403170715060b0912191b0503 63
    0x10140a00809010864901e071804100d40d100004501c9030401c0380c55020b0100007600019104c00352800d80d2042031305c070f5031a00040b468982207075020b40c1d80024040043d03000644600b401e42c1c907880407129122010000c02090200c41c090907503003401013880d070309074409040a00c042102e800c05c5e0002e10b8403070491419000a440c50300301ca82d4210402c0c10390401000940b402010040083c08110140e60405140c041c600141980c2a120108a602c02c404c1c01600c80b0120300e110810720342e004000304c0c0c549604114180c0d0b109070742c0e800c2040c0d82c4203600c0040785601c2c1001c10450348056035401800600d5085042c04040c0c2059110101071020070300400c0c6040c40e0a0041520058584050200c075616000812480f900b500c2d40b005036180e020402840441d82200ca9500b01c3c80c0700740c480c26a03640d030614041440c914050794144189183c01000b080d610941001803070090011078800c24100e240b021102c3d02c42403452400b51094124a9008000411111040c0c036009107141600580e01d40d074001203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 905939001 1250 905937751 905937787
    0x7120605091905180a0f080d0207050d090501020a0c12170c011401050604030f0b04150609020306090717070c02010210050703062d03032106090f27080a05 68
    0x246284010042011980025100f41c69000c2c1604145044510001a035152120100b10016142c40c00000f10304c02031000780c1e800c0f544041201241156980024180540c40340c0c10914880c00041701c06400041d203601c00183d0b600281c0e002140c2030120b40c600500506030005500040745c11001c510703020300020349424090170504410900200b00c10083d40e0251074149416080184121424401480400c000310094880c203940701c0a00e0301f4644075410021300c840c0074100c0c1c11480a0030090046001d11443e0040c5002d1042078400042c3c0c1c0d1102001070b40c5070080e5016044040c1c03000c20020300d0042c400c08000c0520340c0180147c4007e504110b031b0f69810f50360b01725000c001281e1a1402002100070b004220b1105e00410036400098000040c800513500f415484054100300c0c11114070392a0911080d501d00030891200010015a5500c210020103407a10b054035030301d036030316003c8c9060103000c1c2940042c1d403c7c000c04c220301c00900e00a942e82c680030b401c00192a402c006003030103c09001d900000390 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 905940251 1250 905939001 905939011
    0x50106080c1b0d020304210b0c0901090b0d06030606060c0210050f09040f0e061815100504021204030311070503090d03020316080c1209010f0e01020f07030c08060c0903060712060509 80
    0x911b0f500c0e400d05000d14403944248101e03024012085d44418040b0b030341c50440700d401015406241d69245a03880c0100c2c8c007901240c010141c40e05000640281d0980b0a0b40036904680c4248001e12640355604015207406060460194001c92007403c280c1c03072544610014501120144140c2d8100300e52140442c045810110096061542e58003104c1c4480000700b143d940d12002c003452941134017480450843e100c07000d443c1c00350003022869000c9041c202100c100f000141402400454036041802c0d400320102d00f05550640101e850a414403655404007000c41da0016000001146001c16060900403001c400040540031400248240d1030312006920b131809490f40210816510343c2c0f444c5050a080507036210160002503810003084034140d80190b158540d2041c903040840b112240d600c0140d003050407a00031500c0718081c1d031001104010244d404001650f00e42e41c00ca07005075882001540282c46140c80942d0301d40e00c00b03000202454407480c01c1c10000c0c020071002090840d0781d01c02041c4541c1050350 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 905941501 1250 905940251 905940253
    0xf090d1e080c12130603111c0b01180f0303120b1503010905221401110a0f0311090306060904110634020a120c0503060403031509050106080c1b0d02 65
    0x58482d02c01070200704010042c00c5800c203403883d100102102141c19410b03403041c00c0c24151203e1103148005200429030310291180041405441010040c2500420801c0038403070100300c80d4408070f0400c50b80005208107480da8012910442421030318103941000c1820040166181c8400e0884141d449540724a80e81003110030429071294101440001038660080454840e54100c061828000e000d0407683c5603020340040503103280c292000f84403409409014850071403214002914004c06510605003810819241c2c2e003040301c1c106145985c1154410001425419405440480c5241c9403601c54160041d00ca054a0300c1c0000b5014081030f4641c025011031104d520342c0d84155588040080084c4000c40c02c2083c99041040e0341b94001492103d0900809602d00b0303200c0368080c20424030031142005003000404940e003510341490010041e01c00141020031044210b04009119021405510305940898480812aa685071490f005035081400310300b034803010040c078403025207405111007070400085038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 905942751 1250 905941501 905941507
    0x1b103506090c070f03031a100e0f040e101d100207021e03060a0b03340816140112090c03020910080a02040b011806020a060b060f090d1e08 61
    0xc41085071541c0010b0810100031070401404002039204950000381a6250400144d40050a141a400c2c10440709445030440d124544000c1e45580003003941180c0721048451118541020042c04140c6070342c41c408030010340c440402c1120302c0303050341c000019040e00c0d080c0c01d40d58100740c0020305143c40d00c040140c010f8158001110419820201040303001841c40e074a00701301d03803241e400120b9914079005214181c0b80360745140320f40d07182e6414003100318000344280f00d81c9502220420f10100202ca400c018035580d0444410002e01a80b01064000545209540d00e041d4145400e160700d42032420b40c585181003100f020740300d103000369551083c0b00180d03000740c14480c5498110300c14015407150242003403248441d401c05c20401c42e080040c2104107164140da000c24140b80340b10060300d40e001e983c80900065101d0309400703c0c107280e00003130003198030f802082e080c00b040103400140092403240e8600d507c8502400c1040c03000381c2c1000640030460621031030310b41d200304c800c00c9004044042c10907011140000c1c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 905944001 1250 905942751 905942761
    0x14270714011b0317070504050d030933050706090827040605062a07080f06071b0b09070506130501180b120c0c100c021b1035 55
    0x102c1d1240341c0302c80007101c64070a951020b86000d001907003c0d074a00800120b00380e00046120340700742c095030014200a408914111140c1c40c0c00b034040d8078103018010320441c004031040d145c0c0924012120101118848854049000d51011501c6910184080d190103480c0e20742000001c003004001c217030b804910a1451100000000440185844800064843c0381019000d111a40e503440480d071400c0526a605201c40c11800010182400c0102d410703a4240950200001e0400002c14520702e000c105009135281c40d928400140c0303909410041c4400c02d01c54003a40710300081c02c0341035207542102020044501c6165144001007040d0b100b50100b140303a102c290020072071941c001b0f5404101c900580c12001c41c060030181451202e000e5666a2824100e410000c64151802e0b14100da04044070f210984240c1c15080748950041e04494002c40d00500c130f180c40b40d50300005450404185000028a80d8102288480080703d108188040f0601100da5005258031682e4404074103a982c0e04000c10308130002d02d42 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 905945251 1250 905944001 905944007
    0x17012405370f0203090d0c051005070c12030206070807031d03130906080307020f13020409022701080601262509030503040b0703140c060612011427071401 68
    0x340074546030030721424440760441c0326008000d0381c04e4040d099490b000048100c1c2004d514042003948601d420482e914002e4460f079038400001c3c40c155001d5181941411b90301d2205003041840304902030010703080540800c00c03441c45801181c2d00924a442d0100361204102c0c0c00300446058142d405c806548002800340310000d000b0b2440000380340f4110b0030402580380c010110740700e00c5404002446007032180040308043da6a410322072268035442e0011503e0b241c96030001c1000b50300664040d948141c050310700d0f90f82900001d003000744e41070040e0340324a404d40302d05c4015180f50600e010340800303c0c0d1a4446400e0b5802552805c039110300981c00d820922000310744400c82844501c2d4030b950080244101080c00821800070407a0101e5625229156590200c0d050486a01c40010700c408d144500024040d00380020014401d4041c0104071540c03600f00342020502400c81d03c0b94211043c07940c001500151003030807480300c105809000680040c0801d1a058440c07824000306420101485c61031502116565034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 905946501 1250 905945251 905945347
    0x20c0d0c030f02210706060f0602101406010e0118090f140a0c052706040305010e0705010504050f130b0904050709110f04290d0c17012405 61
    0x480360000c0c0c0000c2c10829416940e40c01c1102510319140b0313002a20400304051540030800601c44101002001500c0c2c3c8402505c80c00788100013801c05080c45940d010050070b00040c61b0143c83e0507152610010001001500c01d03c0c42810000f15620000c000000c8176445801014039140240b43e000509d000041000440340b0000b0700380c1a60b25141c2188640d60581000072a4108100d13030400340b1041869008007000a4080d1411a4200c80046000000c0003415040014192000c00a0348e07520703926040111140c2c0128400c1d1940110005d4200b90541000e000c983c200c64040f13840890301654210109400c40416502102d0f02c3e40b22031410002c03800c2c24031560742c0e180d03010301c040341ca0101210041c51a50141c0d0140b64010075205020031740d404841400c081000d20f1000c400d584075841d8007480c00c000e20315045482c002c24003000c1e0740304030b1585509080c0e040e1204072445003140030041001c2820815510491024040100143c00e00710450b61035400300303030140c03400034400c05154200c8800b04035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 905947751 1250 905946501 905946527
    0x11202090f0f040803150315040213110405010c05010b03060103030509030f0a030c060c020a020901090615030b03030406030b0a1e091103060f1014030405030406080105030f1c03020c0d0c03 83
    0x103186034060107103111003003604a4001c0d4005080d203407242c5802c00d448241c61401b160841d854802d20341007a080700c44d1402244c0c0f04600803110001c01d414000c0707203207082d600307070322120070700644208824050396005034041054a03025100000f240410800400d14108003a001070300450000308400b00036140030001c4411000441c005800344101560780540a8094060000c1c005500c517507030150791034420040303213404a400420007070a5503500c503e050b00405c0303d0b0041c103140844d050b40301e407185402800340001d8103601500440c50585402c40403402031510320300c2c980d841103180c40f0000f401070304088140b07046080307015280c07042d0346020307862402c0f10b03203401240b00410014000c004050703030b843e50a420b4982e000e6420030000c00541004442c0c1e451540b000f03410545010040c0300c2805400009402034034400e07107480c10541d0700c500406660310380003414500d00380e11000d500c2c0c1840814a2220054690300c1c203015003013020001ea181d0511790304200c0c442c005101c070f06000050640c0718001465035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 905949001 1250 905947751 905947771
    0xe06060f060a051204300305060109050609190b0a020d18060c021909110903060105030f0a030f0c2306011a04051e03031219020f1c0f020301120209 65
    0x205607006400f41203800f41c1402c2d10003210010380001c0600034041014610303c44c9914044242e0220986070312520200203d081000900c0c20000404650069019074207071080200046e082010680070403194081c2000e1100b58003040c1580007a004092401414120703510703801400035504150780080101411a00c158440000b103c01040f40780d4000b882e010302150151111980b076803031110701d0300c039080280c0d20129046280502032032002501d04042c0c20003640440c00c1e21020390341c42041554411034802040e2072600411840c0c00007134090b1b0400b551074042ba00780311078001107588038515030804078460709410a00c04200d00c8076005044c8001713800741c10110204801c416007000c0d5241c0c140554000e4500561001e006014000ba80c0c0780d441070301400080032242d4424250315003580c1d1000a0b034003015030b5800c400901400400c9402516842c240c04440107040c0383d80c2d190090040000d070b0800b441101d0b621070b088480300c1680d00040d4081c0a09120300200b40c0381c0d91050102c0781000404611003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 905950251 1250 905949001 905949007
    0x3070b1006020d030501050f0d020301150f0503070b0c060c0a0318140609060702071e050a2c13030f0e040e0f0c031902060318010c0c02151306050c100e06060f06 71
    0x255238000003a00307501c4c410781e03005512445c2c1d440402e004008100042140a281442c00034080344a107011609403907050b07007500c61103540c44c8013058a034040c0c0d00e100da00d90f40095000580035032a400240031008440d14020404010700401c11011000c3c00c00141c0d42c00440c0420b00000705c208008568100444a008000c545000381c0002e4032034540d8001c4010098900d0701c3c4601e4044501e00d02070141000808640c5c0003030b62000141e2180d884141d650410030800c00c0001300213001070102500c500d04041200200407200d46d42158000d0f2624194001d00003402103018064a0b05d12030b100d0320450700307001803480403c00c0d216180340c070f03c1f141c8040d8842da1244c98484111820012000c48443c1c1c181c80554690310b960620030748284200034007920329864045000825540550364501e090300a840107402c0900113096101c0c0b0b8452540302c2d00310024810000c10241d841030004000094251080e41d610219440f0008156a400b03001010707203600c2103041c0b11651070416148901c00364111200e0345 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 905951501 1250 905950251 905950259
    0x510120c03300e012f0f0307020103061e0b0a030f0213061b0510271506140303070b0417040305070512030301030302071a190c06060f08030909060303070b1006020d030501 75
    0x4a030003541c040c07200e5400030703079105d008140c80c40d444811203651000081ea5610b4540101003a0789800021042c0e00207820a000000c2c480095440d0754407803040d983c000300caa90305003103210507194080d0100404065980c0c1e07580d04064103d10240030602407028400415914110703000b4a06a425400c0c0741d00d11152140070b90024100140052203003c12050202d5210340071015403a8001100b8184038080301012104820030154000d0b40d607440030100010400c40d40c580b00d20440703100c6030700e22464140d841000018080790b40c400d2500e41c460f10601701c3c020110400700c058007058100394003c50302d1f07501c501030602186c0b8181c0c1c0f14501c0f80008d000214110b61464038025500e100c180b1810030030340000380c40803904110750300449000301100e0032100414440404001c0c88402c0c0100c0655000d40f41c42c002040c2030050034462403c5480e104001c0d030400180004100c243d000240c55160706120030845600090790611549110f003a40030400700e0110b2400401030304141c00541400201403500d030040c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 905952751 1250 905951501 905951507
    0x8180615040b040b060703050c060901061a0715110a0e0906100c050703080a080708160e0103270602030f09010504050d050702061b01060f090510120c03300e01 70
    0x328211a0494002c942960360101180040078180315403604890000b5141c000d150b002030091500b16a8082110140c0d6600701c00c0600300c0b402802140b018030708941404043c0e0040c00e02400b8030380d015415040888041000020448010781400051118081103110b1010b40020b0300e0402c030101900c1c9160307646003007400a00101e42d0210010148a040348081e82404801c101060146911440321560742084a102501e5100110f035188000341e1610001078004900c548050000c10494490004032402e4100640140810302074101004050312410900c668004048031945401090016500d00f00f40e400c041081c1401810714996030b0421003840006100021f20107643c181e503140c9591100c0c06031000402612844860026054195246207443c07017040d40a10100c9040301e070f80481e050f0343c0e0440c410a0311012144101103001c903007410022000100c000d01c10903481040b244580940700d542d107280d10f0103030340b07610b0220603400001c00001c8004041403800740d440c0e07410302e140c000382800b00013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 905954001 1250 905952751 905952781
    0x7111f0e191a0d020309010b0901051f03020f0d1b230d0203180a0c0807061809050717130615080d120b0418050d0906020d0f1806081806 60
    0x20052440041225002c41c0002c000740ca00561114005554070b00307005a03114084d0061200441c490180f00000140503d0000190f8201108900800d50f940c1c0c0d07030b0f80c03060740290011040d07417070800740c1001200901111803141031900c04c648440d400204c2c0e02e00000a141418a080c0e81c418250070429022801100400741d5007401c40350140984c1d40e0b80c640c051045121030184420310b040c0300c1c41c1502c00810407807088100c2915848001c075845959544001c0b261403503108110492883c583d40b040c007985116401803544401c0c01e0034a0034aa280a1034801c4107020200e030590030035980a000441002114028402c0c82402400c4400032103040040080e1500700301050346061000c480407107289040311783c00140142000600c01c020664840000c0c00b0450038417102110180284142c2015542c00351407402c094400759402010b0071081c046065410704841800b060905c480251441100425101040054820b66480114a05000c0c1d400504a0601e46040c3c040b0713080a0b00b00f021400311102a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 905955251 1250 905954001 905954009
    0x15010303090b0705030702130b18060d020108060a03020d080a08130c15030b03070807030219030506010509040303060b0307210b0306070c020d0204022808040b0a0207111f0e19 77
    0x80c2540e801c3c41d443c3c458503610030150000e4000211220004540b4901e44c480119108103480018881400161408443c08201e580d2948202084100c0c1c0c095441070000680c000805030503452425203130307000034203044580702c0110b4200c100060400741c01644105590f40040c44402e81e034083c0320704c43d07940d1420240300c0c1c0201c5042c1a640041604214842c0d0060b811070030015050769074036901c45048030745031007440c00241e000b146003580044a01603500c0d240c2045036045170140032142d08010410925100150040e003c041d120301f4040b400e004001c00444c042c2c0e807035460742c80105000710340c01144900c010740a0040b1514004840d98580c8011800582c4000307185011101d2484610010702062400341d000b039045880450605e0440c007928480780c0c40a10109540305080030810000c84644000301c50040283d8403010202d5003001c2280c01610f9031601c542c4905540c0700380d07400071640f56480700000b501030710042501001c040f0b030001c0c10064081350a42c0c04000212401485a0300c54903503201d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 905956501 1250 905955251 905955269
    0x315100e09160902040503150f0406090510062303030a0207050f130603062c03040303030f091a0117160b1308030301140a05180f0709080a060e1501030309 68
    0x8001810301c40c050241551540c4180001801191901e11400c004d401c18020a0f00038440c03801c140070140701c4468440d1180045101c000c1881e1740b1076541034040c1842c92011913a5100301e0300c68030507030b000b14000c9201900301104504040030455100ca12800315204c0c03010b019420800940304a55400710301c0d41c00340c401c20b0f1440e1103020f5414010414403075009100001103807a2200110402400e5041007001440c4807403c80e8968200b00503002e404052400d0003462a44100800c000090003504500345c0ca0300110000500441c0310303120f840c030351340070b411a000142c102e42c80140b21560002024008048002000301085250000c104110644a018420340050042010f4200311108810346e1b01400400302030301d0312565220504d00d50814a0400c4900ca09018440451141040b944030407001e00c0c01d01680d8065280e000d464a5039141c090700f18020007a404002088400040041643c1c040c822000041c81091421043d07062500c107109041c0e104201400400201e58040101029208000c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 905957751 1250 905956501 905956529
    0x507030f020f01020a021506030115090b010302120a020a030c021b0d020328050c0f0a06121d0c01030b0d0807121101150321140a0e06070b0105031510 66
    0x103042030b0300d01802904080e0443d80000f80d42c84285601140d68619000481134075959a215003041600380c4030085003d008071740481000b0002c5450a81011460303400c18100180b4144044940402c09441142c020441640001e21071004580c54440c00042c05581d20190911900c8408401c10072441080004d2080405103424801c1d95014001008039404184034204401d0f88480345080c9050404001d403994010040d05020b01d0905a91482d41050020441001c1030300b0210260b490401491401d03441b07a6682c020307418010482c3c801001198105401490340980f0300000500355810f10080030b0180e50011b00300030000d030100c010344801582c8160422040c81600380210b511840c0507050050303541c200701200c0b20006c1e100c0b58030400d890040c3c00810000100c044010300a2000b40c40b0400040e852a007103500e03500002014040d03960707030b62800c1005d0050081c00141c4d69000700a007520b45203c40d40041080d0310781005104442e0342020040c00303484c0b9040e101c05045180d41c3c400d03000c0c0040c0d25 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 905959001 1250 905957751 905957777
    0x212060d1112341205100c180306050105130e0d051b190201120216020f010e040204090515011106062b0302070603180f0206070c0b03040605042001050703 68
    0x188480190590030000040c00c04454602c0070b0342e00b40c1400468807030000c10040110710121072860001c4e1154108006001c20120f48402d00010841000850100510070240a0400c0500e00c0ea010046001c2c981c081415410041085651100300034041c0300d140c40c15030841100e5801149804420301142016603c03045804400552280b901c81c1141ca20f008005e00c910140103590309541e0068001c0c0e850500c1204500210380480c03080a845c400c241c03501115210042c90b10404000ca0300b0410300d401d407003620140000c0f505a0700160404200e0b103031242c007007102e00b40d69000c02d460051400d2909042c083c07010f211441d161040034200d140156042020b4002c0075411101e6a040e00c811130101518415003400c6c000d441d201c02d401107070300181c2021810030021a076117110310b403519080100001c01041c154202712040e03000035411200e51500000000d07408003201c029612803801000080b40307515051410a640b040d2910103240c03c5074070208100c02c240d07400420740340103c0d41820034200c16082 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 905960251 1250 905959001 905959003
    0x901120b0612010b03091603050616180b03010302030f0d050f090d080f0c0610060f030914012d230421020a060b062d16060212060d1112 60
    0x15103121110101c1c02c000002404483c001c0114412031495080ea05501a200b07000c88140865100107045503000c80c000c100d8010491642420180b8941441c02d02c0003501880e42034070650581c482d01b10500080010000e5040900620344084100c0000e004903000c010001b8206004207885250003480119034a0b03201d0f111985e10009051700210541c1d02c83c56500c148580c507600000042d411409064041070f03070506032010383c0c4241d850580b602218040b0030b55044006107191101078902180f8016030600041c3c084c400c0318602c0b5188554120a10160b1030350718801000d45580c0b01555140203c296144400c0380710240c04042542c03245003da842d5400c21000482c0269104120a1108190000715640005080d106c15200b04420f0001c0a01403003000703801c2c040c0000c008071004c1121041d5001c0e054103003649900480c414031160130800b07480d45040d6150f141482c01c4862a40c009170010b448bc00d112007207a4403000031141040c104000c5c1d91a103521841c841c207018007880000e60103840c9100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 905961501 1250 905960251 905960257
    0x50d08100506120a1b09060e0f100216060504080601180902040c08010f061b030309050f03040308070b0105031609050a18050606010809030a09031112060403080604060504020901120b06 81
    0x907000b050341d80c4070000c051406000500a0314100c2000b40380840d5140c000b2000c0e15443c0c044c8900b5201c0c0c070819403078100b095812550465046070301440000402a56544030100e8015041d4164000d10a0103464414502a95550b401010600c01c06100401c0320040028403181541d1983c0715821480000c072a00c5005880e0301d2a0080d480390038a5650440796900c400914121002d81d413000c00c4440d5241c4e401e032011035000310401c80c042d803001d0810001c81c0c000d8100420140c442c00c200c440d901510840b490a42d000b41d00121048400015032800f0b01007102e100350702404040b800340c43d400c6004011240c862180c2e2043c103009540b59000100c80c2c1142c0d900c002c2c14907410030f40321003400100e45002610703880c0c21a10030303000c112010081242c00b2400000e0754204031090300c40745495815507e883c1054040300c003d003030303200c000056004840101440300d81d000e94400d403a10049801c00d48104400d540182d0001c03401648180154150350380d11032043c04400c100f02d000050040d03220350118103244 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 905962751 1250 905961501 905961509
    0xa11130e030a08190e1005090313060e040c03060e0a0903030219051c06061b02041803021c02121e0f0f1c020304020a15030902100f02100603050d0810 66
    0x80008101c10358120f4000041a00c2844440714090600800c0c52040040f42c00855015403180d204242c180e010f18003e40c440c50300650b10608590401c00144042a021f644c0303a0820030003c0c0025807040254245030180701207000344e900301030191908111454200032030003000d40c01440e40b40c40c005000d06000c0da0495846111400d5800000c1c0f950103001360455000800c48110134000111b410700e1410a4400c9405440c402c1d5aa120040d800d07184061a038031a43d142a44d11954560404c6850f0340c0c100604054244280c01602003090082c041c210202c1816281d6402d40d0844e0400c810070168100c1114040c403245034009030040c80704801c0c07600c24000c0e4030ba050745c3c40d440020303084074100410000c0c0c4130303400311500e1000109003001c0919040e404181c400075042005402c0901034208010700c0c0001c0b4900d14600081d848640740c00089134490543c0c071801c0401d84100d24400e21581c14040d0380705018402900384030007491079503020359070004280c0f114100304819020030b00304490707109044010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 905964001 1250 905962751 905962753
    0x1060605040501021b0d0326040b090d080103030806062104050609070f3c18061a07031119062733110703020f0a11130e 53
    0x1a292900a8500c0d4014003400d8058402c1030a151803604030240030030084980a030100c03c0003200c80d83d00f40c3d40c003403400302a5100c448040990070354134248981014800c901514500740e1504080c4207650034800c408000004100e120001440400e07000252140c12000680340250b8448440c11b100c40e410510b110100850f042c070b541031105011001031240c0c0101010801d8503e059651b10300030410500601c94124407111420704420310600484c501180e104088001da40010710a000002d20708141e03422241500480d04c503000d2548180d80300340c001401c0000c94826800824401d6102a0700620b1002000c01c6043d66010000302c80a01c11035008014803030403c2e44001d03c074500080501400c000401c04820020a000b41c5402500e1004214640112a140c400146c480d00d191030b10700f14440c0c2040220b49042240b080c072065101c0d10350750384a580c45c815120342140c07400a04054100300151410740c400080e0780080f0304c94182d00031101c10119000c1e44e500030400342900140401030700b503001e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 905965251 1250 905964001 905964011
    0x109210212030a09140606100807080c0a11030c07030c14060306210303130b0601080106120e0c03030708040e0601050309061603141807050a0612050c090604081e120a03150801 77
    0x71780840080d010707001d11001c8440d140030f42d84502088500b8902100d4010014481c00b000c00d1842107200014000150b01c0e207018009840e280304020300d990b1044100d4409580414810018004024400c2d0041e10060161000d40d55448c000150340d0700002d0300c464030039004441100580588000c0c5000100e008205a075168504a846802c039840e003010261045d101c10f500064641d0300c500303101c90585082c2d403030300d0350844a0150650b00408a1150764092441444100045a035080002d01205807141d07803219a100d00b420800718100030040c18190500130140180400e010010840c942e01035500c0c00b40020420400740100d019044201540c922071f040f000c2402403d0190380090003a40d803d03001103c02e940d6564040c07020250103403099a000a0408100300e01c61b1110303030440342d0800701d98090309087c8203406000404a0303016911508003540301d4004045d9226150b5400321914a00c540a06020004100c1e44840c62051b1a1404101a541c10204240700070813010344001d0301c01c0710b000b044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 905966501 1250 905965251 905965283
    0x72c04030801170c0d03081f270e03091003110301030c091d06061c02040e010b12010c2f0601080c040e0a0c0e0c070b07020109210212030a09 62
    0x60100c0c02e0289492101026480741e43c01140002c16080358140609030860103405a241110520310140c1100401c1e0749084500208079610038651b03000d08082107050b180e9520520f070b80034412000300124074942c0e041c41828515090040241c0c0c030801001c0e00c804c00c101c1c28803a02180103054840220740e100201000210a0040082c4100156200f040c01000085000c281440003066040c080c081540d00c40000100a8102045000003803284d441c41c80803000c44a80c0058141c9118280c0c20b0003980d544c1d10000038914081d980f801d80b091500000b0041079510040040c0359403d090151280fa400072607031258403038031103002002407248404c155915540c449030440c0d140d400a10f092445030741031800340714000c0000300341d10101517071068008048030f00e030400301c4500f800c0c010004000c07040240400400f141528600f584a88256400080c901d9004e02c2e000454444040b40d40e130160410300c0446440c0c5070001210b001c044400c16220b42c6a80d40e03103105102070504100014403d0081600c02d02c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 905967751 1250 905966501 905966507
    0x60203100b071a070201020306130b030a02030307060c021e0319050d090b07090609050906100203090a080f1515130e0106080a1401020307050703030c05121603110408072c0403 77
    0xb10740907246110010f06900c411104909030300095860780d80c81840401e00c1840c40642d54082441120040e080d40c2d0020180d030002810364200f0303401035031015142d113007120307a0a038140200150202a03280d10840d000107840794590324010b0414040242410a103c1c08601d8014800d07201072014010050084424524241038000300c15200c2c80003140c0540804140c030380c0200c280b0302c2681c801915803400c17652088200000700744036509401c103600003000702d0a896150340390b07d03201a00c1460300500e480c100d040700e103a02c3c5c5507840c200e080c642c00301e080602070111000640448015422100040321000210500c00107104050702c03c1000c0d8600b02000036242c07008900075200ca40900d0705002841ca240c03c0e52070a03444200c0301140001c80404c59980003c0c026402000201001e1806c60f00700010740e500301c800c840054411003851795803948020b440741d5260145071041801000000c0c100751400c400c1940c1e07130985019002201405030104e00c07441d501500450301010a51240c1c2501d03040c00d0a000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 905969001 1250 905967751 905967773
    0x6070516050105040602101808041d09030a0c020d02011202210603030a410d050601030b0a12050f060c1e0c070b0d0b040e0c01030614030604060203100b07 68
    0xc0d0000004040000342a6008405650403510b151300944540440081200010840680b2102d00d648110f00004041840c64000d80044c00404941071340303620b0401010600c90000501204043d17104019114209030700c00f104918aa81c1950510f09801d1140300580b100005603d024074400c1c030210702010340d201c1c14018000e2111010510000300c1c0c176023406064407403040e40000170228210000380110024800b00000c5d0b8842201c0502540b61100110491140c4554245a80c110000f0404990414a0380714041d00400242010017507070302000041160745146214145040b40540b104906203c4207002400800d010720043e40c60b035242c0710840c0780300b6820402001e4032024056012010003513404045407a41c5800c40010000da51500342d00800315030109209411082d00d403103428100e031b11039000b034400c0404000c002c7c18102d610f80e40014100c03440fa501841030800c60445c0c54103c4e8501103201074015406c0100075983c0d9444110031040301f4055404480d040c0f00024200c1e003030044100325 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 905970251 1250 905969001 905969023
    0x30c0c060925290f070b012c16020102130f14150f0a030b09090619090c0302060307021c080f01061d13111215100203070b04020d02060705 61
    0x1102e614a1520a1810010028021544140c08203104040400800140814003102c040c03195454000f0082c10301d031803034000140803506803001c0c00c0140081a2000400d04c22103255407410144520741000f00c0c900d946020345054680720201d0043c1c0030b101d01c01c0d011503122400c0b41e440c00990030b83e141a00304809503240b00d06c0c600e00d900c100302c4e070501c0e1400c9a05007420003554542c01c0e0510350002c209107000e80c4200090340516070340f008820b070301c1d441e002c225a00c10444100a08801d151805c690a20094415880740d400c85c43c1a410b500042c14550103507050341e4040d1119601c0c1d5a0340141a8a81036200f41c1c030024503400f201c00c0c407404550110300385101d80603114402d0a980d0341d5000076900c01d500072403010b0881000000f406928100100c00c060550010940800e0200f408031300f0f00f00d06d070b00c100890a9404007550400c100e5404c00d80e113042c500d42c020b0b45c2c4203075038401003c8025103d0007191801440f0801c41e201003002d541d107804049506d035800503d01a0344890600d00180d82c0c0d456001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 905971501 1250 905970251 905970283
    0x9080f070f02280e150901090506030607031506140c0a080414040b0f01050d06091506110c1c060b1c061802090a020a0315030c031401090c0b030c0c0609 67
    0xa010020840c400012a0702400340041c0f02800340c1080b500ca90134500081c285130b4040410026000700f643d44882c058024284200e0028007400c10340149801c224004200c034041c181022480b0006144451800c001ca41f48c6142102c145520120b109040c1e1007516103162640c810502c82406000e10030004108983e9042c04014402c23402d0000c0c04180c0d450404480c1e4020920f140540d019406038000308004414404001202621084030004030303110300350311034003001c0100e100303204040d00408a1541e4200e91002480d1703c1da103020014210700800065443d60541c4000520108840381e0002040400c0003004068800c0a07491101c888005103032054805030300301401e01080c600c0b2107101c0414281c01a042a04a5680ca40140013950011909804141d640d00952a0003810040d00d0701c0075602c5010103a82c1c05207142402c000a0120300064201d603494100e28100144034000c4280490701651882c540760340c1d81100345c0a060203000d8035084a80500b00422071000741c0403c00d0400401485 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 905972751 1250 905971501 905971519
    0x1230c1b03040608061903080405040f020904060e06191a0708040911030a06170a08030c1e040501200304030f06020f0a0804150209130510081203040606060e06090409080f070f02 78
    0x1006d03042c50507105200c09045c00b00100410b200d6410b0581194540540301c4002518040040c40442c0c11142d0582c000d500c0c2e0154a0f0600c1242e281c0401c00701c0700c000c550200c8120701e41c2440e4603040e01c1c51001c0c80e200b481c60b80010741e47c1c04011082d002d0b40c2c0184908002000807840602521009901c111004071600d072500c0f10225140c200140c03180c0e00c0214000081c2411075190751511400d078030180c5025488801804650290722145203c02800301c03501c14103540307807841c0c400050500404a14009000c02c031109071084c82500000c2910105e07030304406068040d401504040d0001d120310303450890071041c0090303901000b03508000c080e802144150300f6000d68401c44c1201e00101d008941c20715a0103400c80b140002e407240b55402880d002209402c22040c070594a0328907a150a50000d4000c485c140048204014841684103403030080145080007100ca4031007100081c450700c2008a06031040c0e44da0fa6111013801003450a42d40d0f0072103409192036580c429800d102c92200303a421001c9120321404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 905974001 1250 905972751 905972779
    0xb0c0115080d0f090f032904050a1b0e0a09030e030309030a020402090619180602150424020c0102070213142d0c03060301230c1b0304060806 62
    0x21004040c115480107000c0c00104442c044200c55125101001d00c0400039200c10201d01c08844031040c800840c0300d082c50340300a0304281d0700c092400181c65102004d410030202000040703000425580103030303540126a0600c507880140261a007890a80204400075050401c20508101e56071010f50002c0c00798490001e085041030800d903482c80b44180082d0560845001a4018103040d00500101c1e0030007400c29060640a40f0007849200c000340c0e000f00002c0b0f20074103620000c60044025000b40c4007508c09031003944a058040e1881148c0a00f0090884440741c542e2001c162400c84107a161421039074013559121702c41c0046078080e41081106074400d910440ca24452480184940c0c040342050042040840e070315440d46208404425038001c003243c0d4441040304210700000c090174816003103c05001c0d1a0b0910704149402c44800d14001036201d0030407003c0b55840300e60198119480440d54507896a1448512440c5100f00c4500320341a09a11022502095880e08039001c54462002036030310076101c10503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 905975251 1250 905974001 905974031
    0x702060901060b0a2d050a0815060406050f07140c030d02010203090703260f12010e13021e030a0503070618110402030727141027050a0b0c01 62
    0x215119191011100700409131040740103445840104d000f00d000aa820260842591030700c04140c007850000860004511203000c0c0c00801058101c2c201486100b00e080b01000407901e28403a48c0100700034030801041c603d41c2c0032011001c598a1907401201c840181e078084022907a54041004c030940b0038018003c5514082c1e105200b41c07840740c152540103001c0245036845603a001d0103454007180803c110324001a6001e0001801032924200490344c20b07036580003280442c00c0c60031061704403240c14100c403018000020b0507180e0b18840c443e0101e510241410516504c0c01540d640342140a03014002d40880310280000400503040290042e0400d100300c034080109105d65a014080003850b840c403038080d0407a1f83c10703d54065540011079051004094170302e42c140c6500b0300c1c003031640c3c01a0514141014403496401c0015651110030665040c2c9101075900310140032203d41d031011a00046070126100c5900c150b500c101001020040c1c1144d5050340c9445800c40b0a92000e1004a182e40c00c0c00450424400c1e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 905976501 1250 905975251 905975261
    0x10c0201020a0c020f011701060c030f0f0210051f0e180a080301060315170c030709021c0f0b150d06060801260f0f0703031803020307061b060c03050702060901 70
    0xd00c950710440803840c51350800611094688041d810480070480c52080703000d610400034041c220a445140450070303a490018500503400803c5801c01441d03805110606030000707440f001c0c1001c0203401181560300c655034164403026580c081021421820800030340c14148000c0b690242c4c001d1381842c000c3c520b81202150342c40e582c0710801003a102003040104812442944030b209000c1c0c4801c41c1036441941c51100c0d800388081c841c0d4400c804d0f00044241030f060301e0100091401442c40500a60030099000d08155040340c4607161442c9140d211514a00d491305140c9c0409400c40d0f00815507944030204013103081140d0001c500001d0140c1c501100070034414020714a0364121a01a0500d1905d4950282402220000144102464800d0009980da100418800c1c02d01031074011004040241c030314140200310078284000c440b21398101840504c0540c0300030038000251041810040c0041c070703800c0307010440b03a02c0b0960060031302c030714241c0302c8015144e154100c0360090300f159007215050b80303038650b02d01d08030b903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 905977751 1250 905976501 905976517
    0x19240e0709050105030916060f0f110606060702030703020d03030e15040206030c090f0d0501020c0106050609060405010e0a17060124020604020111210309061602060a0f020904150602010c020102 85
    0x41c0e0044401c000e650b11440040d6070004110090310308202001e0016076116003250800e0010a14440f01e48226950000c1c001d034113080d151812020b5030054440d03194544c04040c0c51580070386400100d0105548040103804000c1d9406480e5445040c03950070024010290b040803c030003030041d06c00d81c0e1032044a6140c414040c0d50014081c0b880c50f180d440301e20860740d1002d007809030025080100e110040d590740545100c005c0c007170000981d0b10a010f841d074508540c110342201d88201428009410140c4880d820b4038152802820858800b60100c00041c42d80c0c10658010b1101429903e41c6410510002c5071030742c101daa40c0034140070405d8a0303019041107440285a0480164002e8001802561068a11041c1170100b503042d60110001600141202503140c09030b09c2c80f107000081848000c82c400c004032a0b10800300e001c4c818030101c01650007502c075000079101500e031a0301c8040260341c200d19981181c841d000024000c204901d42040c1180c0c10000c640b0940700903501c1d050610b00c0650040c001c840c042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 905979001 1250 905977751 905977757
    0x2012601081c0c120c2f09011e0e070e10090504061a1207091e080601120c1403011b1107060305060607021215070c050607020307170319240e07 63
    0xa40c122074800c8444590203201540c101702900744603402c2849490034110100705000343c0c019282400c1087c003080d0503069000c0e10303c0c00c6c6992811032480d10b40d20000d1040c1c80c1c0c142103031011034480ea44115040ca402d01700082d4416002031404804a070442c9c0382c035049441c01c2da0184803280e580e41d46c01507515200b0008402c0c8000030466400c040c1840c62056a010358079043c4075040584810141945502c40301104140380f1120341d05100185081150500404610b4803e8011004942d54000540c0309882510116805510342c42002d99080d040b0000711401d81c020704615081c0d08500900540d10403c81c407860307000300031010031940c4c441d00480c0d204a00c0900201e140c01c54550900c24061356074603a20900d402003801414541c500c410240e80a000b00743d943e10b034025240c0c1899420001c000e03049409542c002c00040c0c0000b908110482c1d0411441e480190300c0b5078420b41c464480d80080110403240c14031f41480110b8154800300e043c560040e0b2011109034a42c3c4a4031003c046c04403d44c1d198002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 905980251 1250 905979001 905979023
    0x21318150b041e080111040503150c07140118061406040e250902130f060e0907080705070203060906070e040204032a030c090506040c0c0b0402012601081c0c 69
    0x7008120003014403495500680f080105503603640050071120f90180700003554800050030805441c0404c6072012180c0002402401400c08130f05e0794225106803030b80181524032003c10072401c244294042628040006e403440d1201e0800e160507001004445103225492401c0c0020034410b01b01032160448400d00000207229800340c01c1841161080300d41607400c1c01c10928071003c11f0840080c006807003001004440031903120b04024500301c031407030300e5081a410460110707001c00042d542c80d89074035049822410081240d458851086685104608001c0c0d0144140320031b0148160001030194402c00d06070f40e483c01960304400411003a44124800507101c00c40c04910f002005408030016070204240c3c854158030a51359598001d1203240f69804150385980c1c0d0f100700070050410b8040d0038104640c030315041940c0410340d960a06141c201034000707810440ca00004200300780c102080550004680080742d403181d0307074966145964a414102e0140305000ba417002140b21401003a03108405540520b940340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 905981501 1250 905980251 905980259
    0x10b091503121c09150605060315090714160311070e16020f0d03090204151d060303210415090302151b0d14011e06050d021318150b04 59
    0xb0300e40c01404030195035030903070103402e207400e246441041d518a01c03c003031104404500d13481801c100c503000e070f014030f0260700d0420400403002800c1440070000360085a191401d51076009003101d4018902c4000c44880c0c00000da26820380d48070145c1c550300c00e44a95501203100c0302d044002a01d8090318400c4804411119000c41c1c108905d0a0b000411008184100c8869501100f441440e101c420760064020964a114007415030410b03014003c8600544140c90f04880d103404401c4220748510610f03d4401c40d20000422901d990900448070008000740307540c050726807004203030741980206441c101d83d613005415800000c03c607a4068618003940580190650350240c52810101610040c02e240001010303110b031000051380030014002d81440d9100024040c4885050b0b051600e0307042e0002e01c140c041b60381c084032040220b00441410380b03442d8039240781ca41d004c40e030340800079010b10185001c0494511070003203020301100b0304801c0c2c8118003400510043c40e540c40c940c40c29282c0c902500f4010718082000388 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 905982751 1250 905981501 905981533
    0x210c0910030e0109081201030605090d0c060c0c14070f080f03032802040b040e1503060a090804030803250302182206090209040c02010612020f0303040b0c010b091503 73
    0x582d6a4403040041903041403035940d5201c03544585000040610b8540041c030500915100b45640019800001c0010310080480a1b0142d107040200070000c94407240c01f0240c1c6813040c2c406441c86540145911400d0405042c07940d2600d42c1809109080c040c0302c000050a070000040044a640c1c1110142d0f1440d11901c010803d9040084d00009010b00035540b14030368005144000c2c070044c0090401651205d06005000d070304031502500c480d038048502614600315a4011840307642150700b800001606110358034240845000d55070020300f0070766010080100341904036100c2c50ba003004d42c118094400303200360001c0e000c80c064101e4100e0418804402c240003414820700881d549648184507101036078a0307132810025183d454100280d015004079118007103041c10300603c040400c0e81e000a00c1014280300c8070485150050401071306c54080300001788043d44081c4200c0d0040c4c00400c00b2140d545c020381c102c1e50f001c2c0020307460141c003420f00840001c0300701010610320181c00400030f001d072440f207000e11060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 905984001 1250 905982751 905982761
    0x9020f0d03050f030420180a020a0e0d06020901030c390b0406090b1e0a050a09050712020a1221030b122401050d060f060308210c091003 60
    0xca05100042000c1d11407900f00c0350186101d00d00c40c0040c107a2041b080d03200d5604001810050b14020008400c048418a0801903410740c4003010b05401a219a10140112404944e541e220754122000740c48407418030045030002c011404081e242880003208008003100c0c0b050502c03081d5070403016860381d0020032070048620460540c0c40c04400c1e2078010026222a01031b0041a00c00700c03a0310f95641078000c20800300e030980340d50090502c02c00d24449521000c0c40b11344890000c0c4820121996100041e8040140381d002c600015040390450700d00e40d450340082903c8103150720003a40b1440e4840b2001528800e106102000f40703510440c9004440880b01a0401111018084000345901d40d04080c203e510f0320390050801171240c03801009507a440034407541e40c580c80716210587c80b050800042c407407525440781040c0f1080d8455400646402e41c060070000512554000820801c0e001034203000c0c2d0380e4030802c0d030100d898801c02c41c0d1885480d45401d1101911a42042c00e802000040c0d10f11150790081e802 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 905985251 1250 905984001 905984003
    0x31213050901090902040b092221050315060412081303080a020d032405120708120306030c010f140d020f0301090912032f130303050c0c0409020f0d 65
    0x4004205a150340c00940004426080b1002140d51088904250b141034003a90755100002d8400010340d041c21820540c41b100c08450012500702999010300c100310202e01c110030360740e2001900c1040c8440c82d11004042d540704bd070f480380b0881c402d480b50080b035107443c808490803a40d0310760642c040345659944103c1e458000804503440b1050090000011800410042c0001c051a502801e030884c0300b410080d04a0b441880301009550440280c0c009104c01c5904000c02d076001110080c00080a480750241b600f0f07250303081200b403401008180355001c0e4040000c1d50140c00124240d138005006840115003440c03000c80580002400800b103501c13030007014401000110481d490140c903021441c0c034a680340342e000b07074000744109603944480c1c01440803565404d050f64845280c28004010540001c116155600324001c1c658000703094000c0d21800c4007422240f54045040042600a6490030003515941200182901c140a540515002850184906031142c2d40c0100500303030300d54000d8240188113003032800c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 905986501 1250 905985251 905985277
    0x30f02070213150902030402150f0d0c080403110604210504030b0c04090e060c0301031113050403020703150b0d06020c010b0303040306061a0f09010c02040b060706020315030303060312 81
    0x44820003680390709040206010b040440030800010f141c0603e00003400d164001c04a55105005000c0181c0e00d140c0c1c0604802550040c0075203588003445101c000e48100c1c12080c165525144c036070302030145c010110300d12403402a2644c082c841c04000070191515022200180041c00c0400d980c00400c85144c0049032003000c40ca0005e0130140c8a950746441d003d01514400074000010504010030145e86c000c0c8110748400c60040c005500380440707201054001800003c113001d00f2543c407900c40d91540101c02440f440200000d021600301814040d40f1b920302408151307100301c008110160600014060f07048648005825a0300390748860701c800000b50000e90300405255200c5131492600c0e50200003510140d805403000282e4180341034160f0052603404103142030040d0080c8410031504c0c400310295030000c0802e08125401c00040d100040040250250305a4404400700e280018003501d13a01031807281c100303010070000800469042580d2800200e450691650041c8c50f04041800004007500702035075000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 905987751 1250 905986501 905986507
    0x80a03200403061d07030c03060519021204060506011d01080414120c07080d0f0806131113090501030c1a190c1e0206031303021c0e011e0f030f02 64
    0x40d4204140e0740c05607000791000c1c1c0c1c4800031100d0202c0311080710010100300c0801410101d2450782d40850380b64446c8406030002e030341c03080002c1d43c3d0704281d0b003407842139442c003002103649900300c100e114400c2e00240c50643c0c907079140c400042d403154010f1510900300300c020203541e508002407030011901d4090080c8200c030580c0c0d144101d034040c542c08218200307070f904000701e480b034407025000c145500e00300d0158450768055015069005440c0d822900c80e40040e00702e440e25503415234424001c01d8001d0880003070010b00d54070b4180a8001c1c80344203009030006603407083c030840d4035070350b54580c03c015100c1c280400303010351040c80d000b0014007100e41c514a40c0d8141440c50f19062100c04200324441c008400d048402148c4008548010003803401d11404040500090920042200d45c02150320780c00000c2411a0301600303204807000f0300d402000718000301111004c03002070145030010300603e100b49250206021884291280b0040d9140d2020f8800c41c920507610074501c01c807141001c501074040c0034140000b040d820 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 905989001 1250 905987751 905987801
    0x6040303120b0405090619113c0f03040602160506071b211e0e12010c0c03050f0418020c06091f23040501060618062102041e0509070309080a03 63
    0x15502802c02030302c65a040f10384801d900001d02e403540f0009001991842e0801304861441709030276055401c600c000a41507903c95030785282c081d00030300c40c1d4003035200c3d03400038010700c9800c000002480c0741c800c02c40369903804203522420748188900070072904010050403051039209640b01d006005c1e0744e05162245002140b013030702c52403a2054a480380c4244030008000b01d02091403803c01035001c0d500c014505000b04a810640c000086c5528441130005041001c0000e1002500100b0402d0310090301c3d4080540001c00e64400d1203e0081d44a015200c0300c0d030040741c0010303d01040109096603031417080e00d079030043d94044581e80070040c80b030303850002e10421855807652a440c6032881c0e4288124828000007400e2804e00201600549000200301c15111a881e0280100c960110010b0710040001215001603102d0082010290189070490040c1d03541038071075800001c24200ba224225034055038004400e0b00da00c8401c50a803000e085c005400000308202c0444058429804480c2911819112042d090300c2c2d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 905990251 1250 905989001 905989031
    0x3030105090406061a070209180a111512061903030503041e083001050a031b0b03160806063402040e0304031a130311030906040303120b0405090619 65
    0x184400712081c1c1c2038003040703900c11810123580c01c81d0000c6864503c50180148225a10b0345c4243d450230052058800800502039912100c6001c05400440e6984a848901407450042004000c4405504c98400b140b5140c1280014248079820359415607280352440d9038135100d910324500d03c1482d900d000b0089100350000305800c40007404294042c00c010002c42c0c0035100940f2150010001194010350030040100140c2d07645003090821a50f0280c144420802c10303524030280486c41d5070020b07802e801c0000c200300e640985544450803034089500c401c11280c0322030702800854003a10040390070300c40702c404040c80e8400e0442c9410703007040658203031780d0302c4a00180d01060a692010524504550000c04d080c410040421690400b21030f03120403410b12803416414400d0702403280d04001e400c3c030a07140441600854140304958900c01c01505042e40ea5a0380d01c0c0c0203040d17a40b054070040c076070b52408080d80c1c40b51800c1c0c0190390141600070300504841d251500d06c03016010002e003110800c1c0f035a0703401d0f040e21407030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 905991501 1250 905990251 905990279
    0xb190305210906031e151f0207080a050606012303011206022a0d05070807020d1e05030a0305090607023d0203040b010b0f2d1801110f0303010509040606 67
    0x10916540100c030021300c007218031448002030300c1b07441a15034250b1000c0700750300d0f1020645502c140131050507190003030039441a803d11199411a90a90207201e0800d02400400503005008403000c1c2d0b140190101ca03001030840101c83c00018151611040004014440314204d001000ca4001c040c01858514030070300f46121f40036101000d4108410b0b911000c20b41c0001404403002d0b40c41c15060041c504880741d503420030f991186442c001e00ca03402002e207110612840c1ca1091007820b0b02180e1080d51903800c0e08119540350401110040000d080200141648402203800c0d4007d4406400401c2c100010040080c1c00d08810790000b5240c0d84074a400c810108000e00b04540414464000165642400d00340b00e00c0504058124080c2c0207410826081c00c01806012100b441c940c2e020007098404000b0012482584006002d807500300011079070351030141c204070400b40c0c2c844098844100d003007601d000b40c50b200c03201080b0700b00407504103000400150828076140e5034003510444001415a4490f03119a140785 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 905992751 1250 905991501 905991511
    0x306101d0717090a060b100804081803240a06150804110406030312060e040308151c03050904060807260c0301020f03161404050d0f0b07030b19030521090603 69
    0x142c441070000702072109a2207020718161b03041e5400f2030301a452520103825030304060700c0103103460300016007070264a00d02d500b0101c00c1040142a81eaa5031440004900c1c006102c1514440c2c1c0d43e108000300d41840300a00c118802c85811760b14010070000c11200544500000400680b0003500401381c4441950320f900c00e080c003a62090310b8201d11b0300481078028044902c1303500302034400d828a10500011036001b00c40340c1e07440a038900d4410b49030001007010810000c0e01c0000a00300e611395829a00c2099004006442860000e84040040c00d684100300c0c0d5a900f00c512401d22455201007501b90044042c0500400340d0f40307408200d4281101001c01b19003264088001c802c24050003009020bc03943d41083c58030301a01c081d1070f00380c001100b20000840d442c81035109152081d02003407444402c015110955101e01500880f0604403464175402c060080e10703059070000e00c01e02c40d03290a03801c1d0f04403030190101941c0e0020010300c403030302500d0705612002d500b0954000d045001031003d03100301e5503020000c5100d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 905994001 1250 905992751 905992753
    0x2040b190303020106151b08040506072108040809040c0905030a05070e0c04150f020c0a090204060e060f0307031107060c021b0111100f09050f0a020306101d071709 72
    0xc00e00d1814000e08551641e0011030081e442c0c8148440129840494042c0d4407100300800341a1003103078030749101079108a500c866000080401c001003444041d06003018036859110185580c40f51514003142c0a900131100240801802e1100903000d0405a01650300c0b450681010301c01251241d0009242007031403030045038154072054060040c3c041d00c1b442c160304504001031050a03d42130607800402c10500804182c1040813561409108038402c014034a4810400b07490001d0041c1c90300901d1020303600c2800303a2030200b1064603500115040490445009100000b400790658030742c190210701800150402d256540d40074480040428864401c47c5030001303458000301100e5004a880c030103110131044009060100c3c00c00e20302034002001c903010503d02c1c880e003030000e2601400d080e110001c09030210007070400e2044240b9920b40440006040c040513008070110b40490755200500b171607405441c002c02d010040780400c803c0b140303c40c0c4001c50380c00c05840d050500900300480c00001d2648003c951010311 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 905995251 1250 905994001 905994049
    0x14031006080c10020616030906060510020c010801060e06030609060d080a020f0c010e030a2a090f20070305030c1204060c0906020105151c0b070f08060301180f02040b 73
    0xc0d0f8603042d40324501e0907107107002038956450201100929000c0c01c8040304145600c82261004010725680140064180204800c0c8811113500d030095460703007489041c0340031503541c0d0008100c490203a0000c07411020000c0c882071550340d4160034803003005005400503400c413280d0450b1038001114000588012a1540d0080101d00740080c1c078945081d46c50b9880a05100025140780103589010030350014070341c1c0200307080403c0039024002c820f00e80d01c404912070481d4102900425a07541b00d030049039660003040c9090001d200803a1500608520314400074007280070820408001034002e80285900140b40d0564505184803230404803504441100c0450b203c9549080300c0c4840d03500714407000007a201c1807000304036500c0c00301803e081040704408a0b51141080320884040c0001c0110f64078640d540c800f800100c03d007003424000c0d040210042c01c41e40880d0100300081c61a05051140380d065100074024051607170b5640c0c542120702c844501080c1d802c2510b40c0b040c02d1240d141c5141d84001e90490800c0014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 905996501 1250 905995251 905995273
    0x4020d3306030b010816021c0908010f0b24130b03010314011a2b030203120c16030305060d05011104050316050a1406040801060e070f03090c1403100608 67
    0x2640e03006580200c801c0c5890040184120390b80140322551050115420184c00000004140c1c50040102408048010042038500c440c5502c9010041140c400c0e4009010780788200c0ea6510075188005584c40c0c1000b201c82e085000c1e07041e100e400103802e80036511036601d0110114031058254089030003500450340004010410030440680d80b1100703004807002044441e0b1510a02100891446c0b03010f8450b01c00d0038898841a580090601d51001512481058a0010b0f140c083d442c1e422501054403085081000a03100001e407408603140220101c080c0c001450f0142e07400d80091a01a00144e0400f2034405078200003002403045507280d5528582e420345440c941020186031903013651028800c511040002c001d00d4407103039410403d9900c3c0000200c8210031580100d0190b0040740c2c230885440d800c28100240d0703c90b41c2e844143c0113002c076555060a40c0403505081d4241d885501009008616449003000310310320140d0400c2c00000c0c02800c0c0e40e00f480145680e403003070301e03642e401110740c1d50429081c0c03070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 905997751 1250 905996501 905996591
    0x1206060e0f0108101802120f0a0e061009020d060506120a0b0d080702091506030a0516030c02030a0c0201021213090b042304080403170a0305010b160204020d 69
    0x1030940c000c02d2030400740034034144c091084181803511594000300e01074408031048042c0381e01900d9284240000c582554a400301d04500306a00c00d6650710001031800d0701c2c0410f07111000c1b500d648550308601c1120300c00c601c1c180b1420006d600c0001c09080c4181e4070310000c1041c0e074a0000800054000c18500c0540d41031042110b401c03603000280c0e0074800c03284204000c001600364001d50705070f19012620900b0668400040e440030308920107545a100310000200030400026030720440c01040e10303862000c14036030b591070140c0469035442000720140e4800c3c0070100303602d40306500781000c941c4188140e90155100c001e503550f05802c0580c84c00d02c1c892000c042032004060500c0703a010901001c031024001005046035440c00207000795000020360749280000342c1400b107000e080350021a80030b5007000785019115041e99041c0c100b052950b0000c0e041c140001031596401c02540ca80304034064441d80720389210341c02c1200950085040c09051034581c403144000c4031094005000f10400180e8484039004259142 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 905999001 1250 905997751 905997769
    0x1090c090213053003090a17010b101d180702031806040e0c0313080301060302040602152e09050708220b060d02030307060903030b0a08010e0604030f1206060e 70
    0x12805039461100d00c3c4c0c01c3d21120001403035000c0391401150300d0640103210403429031282d03401c0250003105140000400d40d004000090302d00f00c0030b100801c2641c03000300c00c01031110f210760039130000150b00984070f05024403080404444960014000c0d400d00d08400c044c104080e10403146180507810109443d6024001040483e00c0300b282255010300d01390404640c203840320409407040d03401d1103000c00021a4644101c01480307040d508604800d450703694842004000e0340c807900803180180503280f0f100c4114034030410550f00640207500046107400038107c2c12095004008460386601700001c2c00010460030381e1141c5401b4511543c1c400740c4504d4480602c2c400c00340c0032550000c0914075414802c0106140282480e085002140c42c610480751500002c7d240d130290450141100785400061000c2540540c4100d620f19000c0e64184046565812151300700c139410105201d0641120000a000a12455141d400046d003070034071a2420100e007100d0700403104550072a8000c20090402c01c5c059150003c25 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 906000251 1250 905999001 905999009
    0x1050f010507051218180f061507050706030f0216080c150a140f070806040207030e042d020403020607060b030708070b0307180602100c260a06050306040f08070501090c090213 77
    0x740420191807a03000820b041401030502a0781445080448e22540e2004500c009581080087c142c950340315051442e00c40101d4460711020a00d8080600c055000d01e000303407520b6400362610100c10420540b503c080710f9000090000a074050140c14580031311170f03803603d28010000d950000900c900f0301c404083c054003002e01042d030b07140100f00403c14a04e500c02c1c400c80d40f042047d6000f60304c0e0901854181c1c1c290020300d010075801070602800100d070703911500b0045000211503240000304a481c80c2001c04034032032804040d401c0902000264007240c0e0b0345d0041c0320365181c06000c0742c0f5016034a0340300c40c2c202107442d044049240b000009007c0580d0f449005071400a03201c1c0c00c6c410b41d4624140000e583c0710301da0b40e1100070712915500c1034045030307005241511200b009500b10701825203081c16510f40c41c2104448a031381141c5044004111410006085846981c2c0b00840d40d4494501e0b80721a07086403c1003000311215925101c4400c0000c41103804400180f50078000540c44140305449881800070b1600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 906001501 1250 906000251 906000259
    0xe09060c0909070f0909061712040807030204090c05060301080f011104050f0108100306150303020114040320030f12070e0d020906100306050a0b25030801050f010507051218 76
    0x810520250b0307030240d51581200860528402000c01910140e0324100035174800c003419403a1000c00034850908010900060750340c0d80a55410444c034100200c040e0040c0e01451070345510006042c001802c00c2e522042e030003405818290441591031001489541c026080021960808591209240310034041e180c100b180d1a10f08130300701800d04000c034079145448520241040103030b030003103400750340da03011103e000c1c5030414404c5c40342250711565200c07001160b00c0220015860414800d503601d882418560240d0b9050b030b28080e02c100501c008401a000d00c0d03a144101740010802075455124100040801409500a2002616141c01c003e072088066003107040c02100780d0b00390800142c0e036040880383d21890407684280e07e03a0403603000f14000d003080d40200ba000b4405c0f0a01142a020182c00303048080c10300c401c01c0c001003d03090141844102101402000300e046400180f103035181c49501d01c022000185045800c1103250f8031010303e4070030030a0404031070704000548801002a0b10a8158058605035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 906002751 1250 906001501 906001507
    0x809090a0603020f040902010c0c0e06120708060a0c18030c09050c09030709020d091b15111b010516061e0603030503040206160c09051005010801062c06040e09060c 72
    0x1d0040303210a01682c4d07600d031040d80e5032015070b0116801010424a01500401c0d4076101030317213954914082c1e8a090b2032191107551080b13111010140005210410788404401070f012030340f1040145009014211310003014042c0c1c1c810295540341c146038000740214020b200c0303044460301d042d07142c2040740c102034090074a0369020004005240c4002407540b044411000700142c0e1307031a24016000044c103003240010410411a400c4501000b511100d481c00c0d184025030550301501c400034251142540041c4114044d00415007450a05150702460856201d0606200d46001c00c0d01c41c0080e01c6012501c811590240c0d0744048c0078910300648541c100b80b41d2844410800513003540c501800324000180000e2003114001816034820745190034000c822584914980803144c3c1703500040000d844101d401e08036141450600080d150310408816040300c2040e19582c00c540c0e1006180718400c00206160003130040345004944160b200d160040004051600d1303000241d00300b40780070509000c4082c202c4802c546041c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 906004001 1250 906002751 906002753
    0x30d06050f06091009120f021810060509150412060617150c120f07020c01020a0b160e150d0e010c051903140c03160c0b18190809090a0603 61
    0x110341101c0742c1082c00c540c2d004c0100a4400110b400c044242c000c0d800301360a1510034810130140d07014840505c3c0c4200c401c00180310855108a101201c216107881c00d8050381c04040004500420040c420072a000d81140490020001c03406801d6101d81d0001041c400540c0912062026610408000c1c00e071040046140d8030400401560303a0000c0c50180703403103000e69404154500b0028088070354210890002c1302c110b16004074192440b050466903013000d030103205600002507201040101449a210304d01c4800c0340c851030030400421020280c00300074003001c039400a0b52980c601f00e044929442180f4480d03600c00140c8180c10a983c441452041268103002105400d0354000b02910100c0c040e2414044c4045449081107000d8159081d124400003a50303030500220008072001103200e001e4a0101c0b9984050700c04007140c00c1c40c143c10024080d0800580402d82607e44000705038105680c10089a0700b0a003500803810b1104002030045410101c0040c130566681800c46007d5440f00c403024041240701d01d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 906005251 1250 906004001 906004009
    0x2001140307030b010207090c081b03090a080a022a100806130c090f0609230f060313020619080c041d0415020d0b09091603060b0f090702030d06050f 65
    0xc0c04000c180b544401c90500c0ea40d01c20028030004108520050003025141040035048240a0b03902c2811314084114125500c0304410807203009598960042484002984404400340c00c408500e404600588640c14851410342400d0b13000d91280110510004941c0d2080208414844500703a003400801c1c010400c042d901d511440800070000e01c030100c1d14038071171101110041140c1d0440395120031095030109803941e00400c0e85040e2020414801210340072500007141401c0740352010340c0c1c00010490040c40300c0c140200955001a001e05d5a202400940e6002605039000340380c0e1a8200d1810000c0511090361042c201c58001101e5003c8514050801d41d4034682a555120103011216403580031808005004200e1040101502e03401c64940150290820140c0054040d03144102440340c04511510404a072020031845200d2031903e41c0351855a441c03014021039540030350701242c0c205510080d40c40340c40c1400e20075a503940c043c0d80e070380900140c0481181c03030380e8229500610003a02c0300202510b03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 906006501 1250 906005251 906005257
    0xa0b060d03170a060602150105060912160b031603050403050307050c0304050406080a03080a05070c0f0503190203040f0b0f04030605090a0c120308060904080301050108130203010504200114 83
    0x841a1003100000380541000d0328003185000c90181c14100400070072410030301c0c542c42001940c07916801c7e2408031102c4600d0220000c0203000e01c030751013281000304000518140104a03444210f0b0401e0b150300c00c1501888030107081c2c0307640c07008101c4200082009424503004603040d46e9400395040070001404c06480c000d00300e00000f040780060000000324030310300036403c0050b6401404000c009108132520b90107500d459410340b090480124882c00040707802c01030180201d500c100c10303d80e100d1003210034075102c1c0e01284403081d00c03e4a407400708010030b40c10b407411003e2480c8101640c4c2c005581c1d45151495418200c0059485021441c070280001041750300c40604840480e82c110501040301d0711508051420581c01c000000c1c4050003031030300021550401690940400d000340c444034029a200c0e414854074402c03c803802494560100018001c0e0340c0910038003074000c2101c199522101c0300c40d5004c2801c4900c160740c00daa1050142410040000d00803210107195082880c1008043e0580d0f00c0c0c0d604140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 906007751 1250 906006501 906006511
    0x19050f09040c05010f170c0406020d0201050f070f03020c1b03060112020f01050306031e210301050d080c03042d0803090d170f07060e010605060a0519050d0227030a0b 73
    0x7003040500700c41c2d11031099020514001d01c101b10038080c2d0400d100c8121070f540c86441340070058007561100f41c5200307006114042c070501e07841100d0203081c0d8410204440c1d41c12108440c0050607420701c141410034000300804805020121241c50383c0c3c5000398100b518114050b0301207107214071a00e9403070005889038469a02e800100b828056200c2e00c0e200300081c1007601c0c0745500c01c021981041c102003800b2000995030200f1180c1c00341880040500144441144004d02403660443c900c18985400901454003c003840d5141400707881c105510f88500c5100d1140c0f00c8800e844446d8184008040132481520210003804003100a61070300040c1008102700030720807000507258900668006404400c007004403424500b000d41c0e407640e2a00305180210051035a0032079a08250301c1c0801c041102d0410b68211090b0b08065140c00b8105104548000184c5503000e400000700030007030182c1034500c40d90780050181047d07110300d50030790301841444c54811888080030b036510a90001c481d00002c642048005600030b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 906009001 1250 906007751 906007757
    0x1014120a030819050703090c1707180e060403090509010e06010e0f0301060909151401030c030809060412080a0e04111204080f0a0207030c09140a09060b19050f09040c0501 75
    0x199035000d01000d88000188107203041601302001c015115500d9030048860070703c21740c4c0c40e10900d070301d881c40003040c2030314082d0504181e44101c0d02404001150340340081e404400035400303c0c1c045100c2d051a41050016076046010902c1c1140c244220320784103900c5030144c902d45c1c030b29444c107190100008021000030039450b401200c4280000d1100d4400b03411044c043c2c030719140e0600580c900c0307142a11403401c10502c8000ca10b40381010a4082070000342d11a4100e94200c803c40c20b519041da1a4003442c0d5004070000f82d8010f05c2080005840083c00107030440040c001c214144e1148034003080540411490ba10151095140c10711043c039100340d10041c2e402170b000b081714841e503a60b2946042e00c01445040c620f00400303203022845520256000580324241c0784200e5803d4081a901e030301110a90b00c590f20074080e0320010100044c5031002c140d100c240b03160700810001c903000c218000803804001e50107400c1110a11950824015401d10318110400070780181d070003400f1442c2036141e2001e0b41800d03000d11410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 906010251 1250 906009001 906009017
    0x20d140a120e030a0c20030c0603220f060f0501030c12030306170c131104030204051e04030824030304120f060c03090b070c0b0403120906051014120a03 67
    0x600905a88031032520380110302240d5941c1d40010001d81040e11407801242c00c0011081c06103140b60300082146c1d040c6002600410144072024101308640d040140000400b2a20103080c1e51074102c840c0b1a82c192038080c1180b05400d5500c0e040000c141c07150311001804d040c1c1060010000180301c40142c81c00c5461800001454800c140340890280c0126400740c6240504c40017401d018510101e1080c00c6154210b40f45280c0401003200c182c2521035040810390b1001c0140310820160a05801c019440041401074101418200c03485a01da804180c809800158188041210b22182d614820072605000050881d92a0200000a94074404c1340289070440c0c503820742c42c104003c40724240507501b540c00760042c0301130310704004c0060080c200d1484c2501e8405140700891000d50148411000c000e03004011190030399a01e4406940b403220000e181d000d26583c0302031040100350381c0d100d003d0250001c182e500c1041454031800c6684140801c98440c0b1900c1c482d88820a0910001110141c0c00c0c0e041c00d003500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 906011501 1250 906010251 906010277
    0x3080304441201080106150207360c03050a0b06090a03110d0f030519030506030604020906030f010623060f0a0e06190206180303072102190f020d140a 66
    0x205019022a0b080305822040021407900d0040d0803032010ba80c84041c84400e005091003003203070f8541c003e104450f40a8000c01d0034008050544c090f00301d25400c2c00c008111844c03480102c0e04110b41101c07080a000a54480030301c80c2d10005406440a000b000b159070a00f000500800110064128400100010f1001c09010101d46651460a038055004800615082a98280540140c3c00148a4006034200d6184560124020712a15004103c0540140354617a200d0307083c806044006882c3d1a8980b0511440d031607078401c00d0160401600e845071060304901c495100d404400c84c010000c00e40721704401d0001000b071000070030650348600000e1034540c00c900880030108006106a03880c00ca80c10495000030203095400080c0030340500d44100d6000da01c0340184030003e442e0f000954900b2700142000c140000704180c5101c6140c410f003909080149007416420012021182c008440310114032520039880c03949805114408400c0980d0508a00c84160700c07182104074030a88906400384a14541440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 906012751 1250 906011501 906011633
    0x30e09070e10051b06010605070b1b090f01021e0f0c090628180621030504060c020f040f0506011101050403090521121c0b0906041e050103080304 64
    0x6090813034168140c2e0141d5031140070080850f4003640c02640d148a605000c03800540d40d800510b85103800c4145c0aa0400145200300100b001440b031940381184102c0e03080502c82508403503401c1c0ba01226200524911544020060402c6841d03c0340c5480b4045480c200f012507101c29866206003440006071121682d40780c8600b12030740e000c0d900900b45032a103810050010600f1540160141c41030380415070f1103070659000400740c2c600701d000000c0014900340400c025403070040381c450f041c3e81d100a0040514108440210301100d0218030040c2c12651540c0a00200303582203441450700409840c0240298601910098000803141c400c90b4001d10000010b089020103001c0c0d4070019403041025503d000d1606056081c5940220742e00040751115186c1303c0103840240d11540d501000302602d8a20244da0358401c0200a20303040c0104810036111000000d28018103101e560301039407188803855101c1c1054201054000300d0444c001e00f143c140c0b0605c0340447c9500700f441445480b841c8400c0da241c400428240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 906014001 1250 906012751 906012787
    0x120d090c030602030a0b0906060316080703181a060d170d090602071103100234080403080a080610051204020105160c090c02070f03030509030712030e09070e1005 71
    0xb802c8144040144541c40034140c0100c0c00110702240d441c0095203400080103100d110942d40711042c0c0e506900070190503030040e504551300c4051814002041031206860450903214400211030700088414007000702030030222800d0300440306448201c603880c1ca175550300c800c280019940785020b40f400301d591019070310590442d0f2021984080d0942d120a15481c0c10fa107489402000640709000380c03141f284050301c1034030035901c9141074161000300e50780308040c02003400004032922040605482c403120700130034100c900500085210710006170ba903482144000302039601c0505241d110780c80046100300079170340c00030035100f80001d95030b909143c07030301c44e8801628640b04950510752204802401407040c0000104510100e030020b11050140182a410481c1c0b40e10312030080d418914000f100c2800031a01c01c42c00f8203605900901210340c0d1039192000c0300c3c3c5150795450101c0004405829446050a043c85480d4026000742816007840e030001c3c2c006052109070201e1001048000303d60031005030403c03d01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 906015251 1250 906014001 906014003
    0x706021308030a1103090f0103110c071d0901060b040b09040e06100317030105031903020a0602030a0902010e0102071a0708091c051608031204031106010620120d090c03 74
    0x14818655540c06070340e243e802141c01c00c40461036064054000e2840070040355409980101908140c65151006600610065594000c05a03040c0241030160104001020162044241c84802040042c103031840a41c001040c00301c0e203134109201001312101400590b001e8483d040d07105502c0d03040410110340100240d2017107120f40d11640d001c0c0324411602d4882c8005a82c041c03000c19003649a408080ca031a07110a200d0355070180d1002c0d40c0d1140c0400154420740c20a8400c0c4142c9070002840c1d00c07118240d800503140305907407540d41e1854074210340e000240340096600c03e0000d03050207850b213000b128000f00c803403c2022510b4000108107042001040403901070301c0004180c2c041e0103401105e01952000411011103041c03088402c1223002203064096801261000c1c1c000b1880c06e04d4881c2040603c0ca005030045050201145800850721014084036003c2c003016070710b180b81505010000c1007650050b014180303d80e001405902c40318100174084540305201800040b89004a0b484c1c203d0030112241c1c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 906016501 1250 906015251 906015277
    0x7020406090f0c17010501051c32040b010e07090503031c05130b0c0a03060e0414060c0c0604200303040e06150a170403032304170a090605070602 64
    0x401107014400381c0e00001070500d00070010480180840010707284000112104d070080380407040104910f620580091414844a801c4031041a1502d211003003650031005009a5490004035000d612150541d511215400c01a444d08810308050316140c81154040c0200005417002c400094041d90051035004e0003000090101d03a0b03a00d00c14030300c540416071506001c03500319013460080384a5003284401c002c1e0312030708540e588410761207002c0f15038455840510b401d810b040c0c454030006040780750b82d40c0203480b80d802012400d41e0031001820003400c16900500b00d4a0707020080c000c1c50782c201000100c0550081c1d220203030f05462800311891500e0082091b0f00b6641c90711000401150000c0c0032107282e400343c0d8050b21020b503060358800c034501081c050b8a1484c00001c520545020034080a0b42425070082d0290400248001480910300d003001d4050003c042c0440c448014003080020180044240f1100d0303013606810010403d1000f015000e031841090100038008c54a002408403650448130070705844d40f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 906017751 1250 906016501 906016511
    0x50a1407080603160f0906080a030203040603180b130212063d0b0d06050a031e020409080a0c050705040b010c0b040c051003060303080f0408040504110705010905030705160b1e070204 80
    0xc0d518403000c0d40306d00603908500d041400001d41c054001800c903040d85e90680245040a040c800201c008002c2410710340151005280754001089000802a00520071220305400703850702401480b80c0a0b00b5111004c00780d50050080110115145144150082e1000b20300180c11940300c4401101c942d202c552058000316420b13000610505c00300041403c10080e0b0000e2000036075400400c01e03030720120b10029105800e03a5000e5070640164040c0ba104941c4014400070703020a668541100740c0d08074040a03008505180072540030b0040400c0303080020802120103012401021700001c0090841c40c4c00180380710012004941000600c1d0b0a03c006440c010300307e1400b17007014043c010081c02042c40700740c0128209401054550074000d5070607100702d400c513019914082c40c0000b8000240b05070100f8000d445414004540091400e01840345a68061b200960710382c10300307040c40da0410001c54054914030121030717420080380e450742c010f41e088048800100303641200d1084114420703200342100203600601d41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 906019001 1250 906017751 906017759
    0x180607020315060307060c0302030d0f14150a090501120321050f06130c0e01050a0c0803100801060806090c0f01030e060a1a0307081510050d1104050a140708060316 72
    0x40d07040070303100743d00440c22a00c40c02d80c1c0740000d50b044400e00c0340140050f0400c00032140c4000882e0000b040010b19039000061000034608075500a0340c0075501c0803c40b00100f004103038645024402d4501926011504000c00d500d00042c1d9031010b5605070006007880544141502c4071500c02124100c0b145101d9000e000e10701d000441d074824400100c540314482e0343c500119036110030480c031440034003c80607110440d54444110040d949c0390844086241040f20040100d0002005900034500901c00050310949942c10b180086094030603540041e01145d00c52801c000040d0000a0701c094030907401d81e4807440a0002c1c20048014248040c0c035103a90b03104007401d110b0320100035805234000c40000e400503c100e000850404d6203a040c1403152a0055210400f0361005540d0000a42e4015100d00003e5001d959030f07402080a282d404039055400d03d55549004c0c40c503090a00a49078080e0003d44204a01e03600505c80043c1038401601241c10018010000741d0139032010480301441c50112001301400580c0c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 906020251 1250 906019001 906019033
    0x171b120a06060303031505013c03020d1b0203180a0e151e060901120609090c091401030209041211031c06290a120606051215061806070203 61
    0x901c011130000b4a0160f17515041e4440d0400c9900341c61051f5035002ca2090003051a0703403810800c0590341c181d480700001c554420741c100040201080c15544000d611000a108231200b1143c904a2094941718004034984103a0303404000c07200200000300d941c8035000000c1001c6240d410140e0400b4075000c0d008000d100d0400c00485020000c840211044408074441c0aa80400038500080b01500711005002203c2c1541c0603000e01201035851b4880041d909950307070720002c140c030100d00041e14407204400042c014000359004a05100b200c400d0701c0349040d455580030841d403a20080005e4440482d0191f2280080c0c4038011040c940762030a0101c80d112090a400c00c101d01c1e40c01c011b0420924070784400010010040720590701d040c004440c0041080080e082e040819038440380c076100401003840b0800d48840c405202d4a0041c010796a511500c3d0400d417840701038144406045070502229985211032030365509411252a80c0d080c40c21200c139111f500b804100a8002d08138002c0d418000d640c0039101c4414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 906021501 1250 906020251 906020261
    0xf031908150603280b0102030d0c020319080f090c09040f0f0507030311010f060503031801020f0a0302340603020f0d05090d171302040c0507050a0501060906171b120a06 74
    0x707144082400c801201e1320200f82150031046480c2d0143e0024407058800c803150303a001c40050703051401903e15080a01100c241741038007990300400800c1390030061007894030400c1103c0754000f0700b01c8001c0051a0b40200020041d680080c8001d00310140c0071445020408882a41400c803540107003225010341e140d14000c1c0031070450b0b080b10080b640ca02040d03061007015a0041b13408942014015510305200d083c03804110345640200103066100c0c01d20388106c0c502d410020446514040c1c1d003d808004000c2a216590901f42c07100c0d44009103d80001ca030041d122023103190215025800c0050307896001d0198a80c4500441000800d0b5900c3c041c20020002c4000c80c1c0c0c2034807500d2980d900c0202c21034250748845c40a81c00e071002c044412085602c5801404c2913404418a1000c0d81003c44c105204c0e0350f0795a00c1c01c5000391044034130b65100c000030007401100d401224041d2076403d00c461030440f0003d540d5580c0f000701900303540000007800c1000400d500d071041a07403110640d05051310104841c03070402d9000344c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 906022751 1250 906021501 906021541
    0xa150c060b060a0c0f0602070b07020c01030c080405031b28020a050a3002043902030720061b060f0c0703080702010b030d0c050f031908150603 63
    0x241844808121890000e04450760f155040e110b880c02854562507401c200f00035640c00700c8403903908010745004540005445407086000758000d2001c0200c21000605442d100c404c05400c0c84400410f100000d00c000c4295422590011082c582c0b5440322800c4030300d4034141340c0591001c101c1024103241710010800101d075005d4000d8800c841215a40c20a100106000d40301e0103203404014200200d4854461184002250304001d4842500340642c000500322019017800c11008400c0c140341405603100c8040b005a0048407003401c2030103114409010752280f007509002080c804c8409158103000700c000e00380c00c11890010b045a515844440c0070303480b0814a442d603a82c1c6500c120390000380c0da0907000b68070f80d00c19030300341c0780c03031810b0404550f0140c3d1000710290640e02595280c1c40d800006072801c01002c2f845110325a14028080c00a090090070032801140e0022107801c00c10400b1403044540000300b00907950f41c40c03d0a0251b5880c0100c00c2d011a07442c882950046001080c4000ea401540c0240d040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 906024001 1250 906022751 906022763
    0x3021309111308030a021c0e09070c02090f2206061701050103150c0509040b210705210601050922150b011b08030a021b0102030702160e01140a150c 65
    0x5516010f0140c0c0d2030040344446030069005414603a8010120b4090500704090b07400d102c00030f07840c49800551883c104071003002c002011250b2060a62a010b10141c2c1c112a00d01342c589d810f0704010f40b21001e19016044402d454025092400c1c0401026511600081001802c96500c003c62804034034060b010070320064074041d82010413000321651520404900001e903803600351421503100e0a01c0040c00f2010030155000041800607140d203010310b40d40034480241c810103088c605082c4020001154201248000703980d8000300d22000a60000803114107540003180d10344001e030740e00007401900b84080000400d0a40801181030304101c1010b0140f01c002c918038005010b4841740704011281160f0025440140303c0074501100e0125104000454100c902c0204c0945030030050304c2c194011610908607041d10340c0d800410808581e5042c061100c500c100030401602e4145000880d824011040c0102504030b0042d10104c8000c0d5140b0100034010710b403a0808142c00000c601014005140000c025034403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 906025251 1250 906024001 906024037
    0x6030f0f0a031112030f0a0b030604030f03060609300203030d060609051c03080702030f0f07020a0b1c02030718081c020f120c03090d1b05031c0302130911 68
    0x40072650030100e591301d0240c1400c6540383e43c0d048044060203843d4840885c0e0320903215090303480501c8018442e5010f6250841c04900400006040301c0c0154002d01c100030040d40e0602050300350154203c41155405022003000300c8a03022449954900d200080d85888000340c4a03520b10020b0700300c2c00450300180c403841000d80e5038405000356501484201070340141c0980b08030000a001390040c58100300349104032802d284141040d14180d500c004609040c01001013a40800c40c5403c94411000d4051402a6400d00c0480d1003001260010055070200190300800007a00c000e2040903101e0142d0383c03003940d00f030200341d640411640701c843c0b4407040040b0040c0316618150090001451170708180e400001004031692068005d141a000030540c004140802c0281c100303036940d026114030925016854000402c0b88048040141c40385a81c08940170f03400003076850010013001ca030316400220301070801580d500d80041b504450204141c200e2642d070340c0351254111540144c030300a001070b990f0100550ba8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 906026501 1250 906025251 906025277
    0x30c09100905012102011101090b0717100f0b0f0708130602190b1f03060504140d020d050711120f06010513060305120f0705010606120b010c0c03020906030f0f0a03 72
    0x1c003040c04d25101d034820603c1c4103003a1006501c0788403580000964040000380c0c8003129619880505001d8501500213860403120310340240402b10120340260610907000c4c803c41c40c1c03200a00e50f941d1b00b482070404442011990300c41c1c903100c04040780c01856108140c2a03071a0301400f80105500c6090080b1401880740003049000205450900340070103802501003d03080d0760f00020042003004094000074003400d10345000000803d540a0f843c01144980c410414040c02c00300a10324001030100340d401194000d80080f148039401208582442703070080508512110300d0004205000d05070060940184200f8203801d07400380d00850341605a1700100d0b0a000e42c181c0c89802c1d070040c0e956a000180150300031509842130701c95070000800c3da0364040405141400101d441d180d007121103560024000c140d4004104640101501c1008500d94090900035000100c03a203134660740384014080280038480d00340100b6029a0100300e00341030b1894460446824448000a441e2511100b07035045002c1903034424295 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 906027751 1250 906026501 906026519
    0xd020a171e0105040b0114070f060c140d0c0e1f0e010c05060c21040303051006050435030708040302090f0115181a0705060a0204060c0f02030c0910090501 68
    0x345280c800d181c540c00340307039082004000090146240c11410300145855000841c42108040e00301c90b030140030507404d01c2d041030034000252110071045804008002000d680807406600944243d1042010f001031001240c0c80d05039030401c0c0c82841154800b40c255a0301145a01c0440d08000200540da02c6920120007200195400b0340e000c07100503d507411840026490303042600180c4600c82e00c0001c0384101c901c0c814030707451081001b540c0540000e07031240c2c2040075103030380c078860040280f86900d481c6181c01c1c40c001c5c241131191075403400b220100111700d2000322504000c0c0f401002c07113200c1d101900e582d40040d1620481aa009100403409400324000052805154a11090407155600103035a211301c4a90000c50f2200722200590300b50f243d0002000c80d2002c4600d18100c2803000306244160f03207030480d0409510f0120010903d0100500402c003d204065019030080d0405501403082040e040080c40001d09041028403050b1f0842c0b68101000300441d2401d4001044079140720042140d640c0f90402c030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 906029001 1250 906027751 906027781
    0x9050708010c0e040906110f032a220f0f051e0303031603060815070e090907120201030222050a0602030906070803090319030b01170114040c050d020a17 67
    0x100000c20a0b00f0343c0c901540c20140c0000a55912500c000540c2c8020724250604581007940c1030a016000802008511401e40b03080300603000341800d0704203400c448840481c00b58807441d600da0b4183d112440d00c410b0010020070402e005080e0800c40c17500348070307106c00394194200028400c0a22818a19201915103501e4058042403804040d000d51303d9942c0d00e032011a210481401a1801c05548075000213000780180070500d074100f100c0181040c6814410307002010910500d40d514420444001030180d645000103000085484041d11425041e2060005030000e02130307008201031400c0600418036005400c5000541a200111002800941c442c0b108990380d010310390004c1c0e0000010040c010100f1112800b65a1241406080302d1421444444201c1c000621640302c40101c0e0300d44900c10110768100d00b4001c0c554842c0038034841158908600441d000015001450146554025400950340b1071400c5462407040010190758454090350020030071490500072030b0405c031801e400329081c442c1003614 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 906030251 1250 906029001 906029021
    0x31501090b19050408010f151d04030f02010b0d0506061c0308191d0705212505030d230307120f27060506010e0603041b03020a090905070801 62
    0x40c15041c18403040050858941071014042880f80902c80040c040000740160a00d26031260300105094104d055203e081508a81108607107809100e43c40c0d8050212100c003070f5016800d0f01e4800f0054081007020b070700400000d42400d4000c19405241030501400240c501c0c01003a00f500d2600c5110303039110407030300080d28002004000442c0400402c029005180142400402d00724002406050b00703a81d8224010101041c001a500301e10810020751070050410515201316007015401030911100080c0c461100c1c0391503400002101c3c2d48901036110312080381c400b400d0701500700c60140144410182c45030f22503484800d402442031100e450346440749400e032800790319151240d56014a40b5003c075000341c5414004021540e6071582c42600f0b28840030107484103a41d000b0090012000c1a0402a003941c0b0024111414081c800120f22210348400d811641c0c0a40c210091150180220f14480c40388c40e5150300180d4403100d20365020416102544c0405000c41c0708000301e444d10765030382c0360b42805c1e10034402c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 906031501 1250 906030251 906030269
    0xc0304030c0b0903090901081501050f1003050a090204090f1103010c0c0f02010210050a1d010203010f0e090102040f170c100807030c020328110a020a05062d03150109 73
    0xc01c240010210030740c164119000e8400d032400c1224070340114003251000d902c010650340c003a040445510740c0c2401c0d078a001d0300703080d00c2200c140c24159020484035410f800c004820035940d00f000621540aaa0080c039084c0c0d801081401110701038242034002c5181c46e5000e889010b1a20400c10041c0350500c00c06051000039244c25565402075181c0d080c1410100f1410790650244d0b80104840d01c80c2442070500c111149140000c0d45008824007031008902c4400209442c3c0c07040005000c054606203243e0f0031243c03103101405250f41c0300040c0601a01030380d03004001c8a5103e0714041914440d031042c4082c1e00da1000119820384143c80e08000b0100404046080801c11000204074180c0c402d4001c128018101c2c0100e910b45207000040081e085100c1000221500070000e0042296074440e10f500d1a100401d070003001503201c0c5800081c15103260b031045c10301c51074000440d10441000006c003610100c0703900c0c0907041c000e4600c9034000d0349688100d0b14040a0904641c15581071f6000c2d02c8001c054412001e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 906032751 1250 906031501 906031517
    0x4091a0705340c06090807061d0907020a080703050409050c070b0106080a060f0f03120203041503090314070b06150f190e1518090402030a0b04020112180203060c030403 74
    0x407081e25007060340810900c0c0540c1d0b042007248003140300950640300130300b8135a460300c40d503a150002c00340c100700e955003042c010045a0b942c0303110354540070706a00410034070440300c1a0f01a103a80c031040e490a40e24000007803d0403008a100028913402c000070308104d40502c8001e02103541c502110102c2c3d4483c8060062006210100600c8024881d003041d6038014084503000510546071006c0509007096a440030910045c451001d0003001043c0c800d008000049000070342c140b9042c001603000d034a10113482e000130903550300f81103000c0c140f06041421b4030403c1c07100c2042d5070b441d8904100070100710865aa0340150450007e82c80000407440c00c0780c0c00c2d15200380d11305003004581111240c0c3d04c5050b1b5202020819414103071292503071140d0410458171030099440f03548040745440780300c0070b12041c401e29126803500020400940c5010a0001d02240d20002500d500d03502d03032005940282c00150000300b81032a1168150144014011044815000700e0031140580e40d00c1480f40c62501c002c9600030b0010f2034003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 906034001 1250 906032751 906032797
    0x60e060304030309081611031002030f01030807031809290d02091b03011215060302010e101e0f09230909030c012c0705060f1804091a0705 61
    0xe1388001c1e0114403d400842ca0400c20304207407220042281c1007075132044449002540345140410810329034406907081076040d403410184603442400b0501c03001c0d10442e0000350340000c2500c14144c44021303051540c09030400b1600c8001c0c8400400d03180d50b49070840d20394040300080c0c1c0e20402010244d14100108031003040e0340079509018003150058694138003403804440b002c1c2020264009940a0314411070f103c110a40c41d800c10700884100b40240f446421300d03203101400940d9001c00301c0b0004c2041903802072000e0350000412640d613840d0116280e484009804071111482d4041d805c05000300155481c01d00040c0c0701d4003080e9225064038810061030f401030b00000c44906001c0c02507a40203c11000362803c140200c1855070964256080106265120403924100b8004030451800841d03e00001400e4040c20000401d2044c8200107181e02100e00100c0c2d0598540700038901a401c03200041c1003030013039154034a0031480b00c02c3e48218105541040fa40064265031190b4140d03540b4150344211102a8220 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 906035251 1250 906034001 906034007
    0x109050c0f040209030f030306010810050d0222090305042d1202060c0d030b040e01090f060e1e1011030717130b0f04020f040b031e071508090601060e06030403 70
    0x6901c0d480da0b001502800661344981c1c046c8200b001c070030303400300c05580d507481c0c1400010001100103000324490400c101302801680c03540803a185159905803481ea040106c40c0c14880c2400390b02110b00710041d810900b842003010361080c003400488030b500c0309a0200000c189003a00c1403512031000402d011845582c00c21010462034100000640007070032991900300402d0b4082e04054001c8050000300e43c8690181c0070a080c03900c1982211352202c40204425640c9646040061141c21000341c00c43d40c41d0184069104814004100380300b0481e00c241018a00300c40d1459240d070f03031030058048100c0c5406034004604c11090101ca202c0c0104d80d42c1c4820308164208400312107000074050541085030701c60404000b0f401d0b024041d000b8000240e080c030051800d8410400802451500d550045051000051041d140007a05c0c2d5695096420800100e13007030407051340e01e05006035000210a14008a0204944c2d4000010320f01400c009130913681c2a0f030302c45600762810704103044201c1c0c1154040000501081c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 906036501 1250 906035251 906035269
    0xa020d0305220f0510081b040504060909110904020102030a0804030918090b0c1c1e0c120e0607120209040603080a090612050f010506030901140a06080f0109050c 71
    0x32007820041c0c100361070341c0c03041a502c2e40c001e40d11040030b02d0b4207201880480c1c3d0b1443c0d66001040125800540e03205140c4000b8504000944805036000d040c14107812400007070301c20784008e400d0184c410002c42c2c1e555940c01010f080c01b01001c0d035800d03400095070001420682c1e01584901d4060b0001c61604804000440c0d0300f00004009408001ca48000800c01907080c61605800416519001c00c0341c142c00c0c1000122002d0160400000f164204074852510b80040b0782c00d0642c591241e8000340c1880c043d00e0030380d141d581d02103d078440d80d441d00c1042282c1d141c01c00046054020000401c0040f11400e0050a50740c86064912002051402e10f04040707909594008200003c4003030400f040c01d039601d0742c1701170280d0400300b0380c0d07000b19243d00000d10409078040ca81c6c80e5a030907510401d12072402e0003800e40ca510792040c00707902c1c003440300000006c40101f02500000f62096019500300700b98904040b003c0b00a00c0e45001c0e00d516030161085503110b0340d0381400751150490b00000588040c4000b40c0422072080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 906037751 1250 906036501 906036503
    0x1207060906271410030b010e01050a0e0307030309180203010b0306060313050f070816033c05031806090112050601110f0708120a050f0708041e05030609010c020a020d 73
    0x9102c445800c0800c2c22411081c81c000c2005034181e50600d92400e00704200c190501450000309450810540c0481c3c6c0d00500c4044240710a081a95031000a020126040307a20f0680541d010f200340000002015807081201040702c1304040c9403443c0c2c1302040c0d90781c01a40702c00c0c0700f8102203010074000f04025242020041d40c11410300301c2100b894890035918241000384500459003e1340101030204070b40c200500420150f102401302d02442d0724152340e00d0315094000306492070585181494000c0c100c900004a040c0102a1110b0404515665140880c0d407030788490072050501c03a0721034024200b800c040060301c4008130141c44600724071185850700001020000c002c14104002000e800841007024000344505070031104c040c268090501000034500101c800a0305003d4800704426040160b02100f510b559580044600c2d54403403a50405e0b80003801203804c04041555036070b00ea00144038684440408070350041c0c09607107040d51410103442c2201d10885402d005604901e00380c2005183c080d00020000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 906039001 1250 906037751 906037787
    0x1120c1a030103030315230907020d120509010e060c1305220f02090d05010213050303030622091509020f010915030203061216060e030d050a051309020f07021207060906 74
    0x60352003c0c00c1070207811146c64100c44100c4445a811f060400004607944004980010014008190001800607405155401807669507102041c0c0108003074101c40450561041110300c20304003885c01c801c00d507000c442e0002140e400386200041c207043c4080e0314603449a00c0380c200c02010b01c0702c1c60064098146200b0300b00703100358208080c00c49692850744803c1c030705000e20001610b91985016074201000340ba000244031398800c0c010041c0307a9442103e54094a015900000c500203480d03200700018080c001401010320404c50210014040c0c1c6a0040e42013074000c03181e6065076090140151400140d502a044800c1400001624503500a40003103810072400342c000381401801e041411b04201400c21919058860709001300030b2668080f09800001604a01504102080d104080d1140c8685a81c0c00c051180100c0d9506000c840c02131078800806920100f5580c4900f809040b00460f8000442240f1842ca045200884420000b4421050380c2c0961501c1644c0b43c200a4107a442501640200ca80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 906040251 1250 906039001 906039041
    0x20408011e0e0d1b05100510050a12050316050f0303040f030e0d03020304060309021503090610091b030911100e040e0a050601030803061c080a08070e01080f0703020c0601120c1a0301030303 83
    0x2506c0c062240320700c01c0807008024800c40e81407030700700b01c8185501da0103c032141310300120740000300f800807045a4129591796001100700c60546030284c141018517003440c0c1c83d400701000b08400d0103e07040310b07102014465501c6001900c038510030448409411100074006a1092000b0304c0182d0087c0e000b202e200740001c11581040c42150b2182504d40e20441c0c0c4484503801c02801e00200d00b04650b220401b4190020080c81010000c1c010b401002003003c20401c10191921a154180b20682c90103d03010000034045142084e12244081c0a0300800040d5501a500d032208000c042c02c8042041c3c000e80b94800301504a84e480c5840d0000c143c1c202901c5940d0102907400c4600b8a5500030007011a124403e04896442d92685c1d0005401c0c1e42c002442d2070244800e080101a03a81c1e40310b45419800407540b685443c05032140c1c00100d009001d0309064035460700c604800070030070f42d031101c1c440030500348511624002291500144013543c1402c21480807045001d000610010b402070f00030501d410702290b0f208031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 906041501 1250 906040251 906040273
    0x71506080c041b0c032604050d02061b0909190507090f0503070b1e040b04060206062718011803270f1206180f03140a050f0904020408011e0e0d1b05 65
    0x31b605025202252070350310001ca1003150a4040c800350f940021401d141e070308409024040b401192145c14a420712500c0810006000c0c1d81c0c2000149210513a0310800300250314010101802061003401103000c0b898081d14000f60310b02c0c0c0051801c00355858501041d003845401c0c0c080d240d1482200c110120410780c00d1001160b81c168880152004001560007440d1070b00f01041409a01002190801011340340610a03a40c1500101c2c144e541101580e0075504940d90001441c9005007400c0756215005d2203805402c506250307104084198035a007441c8605000422501c002c0414403c52007050280503e40d0b0041080c03040210100483d18000c0301c1c08100c1003041c07004d0100070354237005d0440e0240700c5c1c44182c80505902c601000c11882c0c0010707c40b40342402d0354a000e00709000340a800b07103c01a0001c1d1800150b260354069030010408079001340b0903090420b018002d200340042108000501e01005075500340400643e02c01841040c1d280c80882224a5100700220300450340152118811402c0e0b00c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 906042751 1250 906041501 906041567
    0x1407030b1003030f03051303080703150909020109050d051c0e030a03110f0a051216080c0a02120c0f01080705071203051801091106071506080c041b0c03 67
    0xd00c00c1c000c00d12046141415803a000c2d04200d07003e00c180007090301d000200461100d280b048400d450703425082c011515910007800b05c1c042c00c80420b110141f0000000e0004000c01180c0202c0071441c401d0301d03201103440d01e981c180002c4c00280b1001410582c410300e00801c0705034a007241400d14800780c1c81c0180a0008a43c04240b520000c070fa411400a00304000074142d001041c8a0710b454400c0040140415041c0d5444481d554944003030401c03455a00015180d420201c0c8005c0320801c40e0b0310091841c0c6440100b00000d0301d422100c84264001c4864140d18585050045040c00584000030140000006580011116050000c02da02c060100030044080800d4090090301800035403507070041540d18209161000f100c80114004130b40740c0c10407042c074000500c10f814042c0300c0310301915204c1d11814182080d003c1150552001e0329804e14060000c10510000701b8104541c260644062140103402e92a906a00a03292401d000182c0d00d0b01d801c800281c416100e680101c0c1907001e40f20707550384800c4002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 906044001 1250 906042751 906042773
    0x1606110c010c0c03030e0f0d050a05041a0a09170604081c0f1d031c0209030a020603090303041b0510030e0f0d0e100201051003060c03022a0c030303010b07140703 71
    0x900041036055030f82c90101503040c0101000424035402815000260008550345d82038007140103001c0c0700d070200d07480124521403c00d030b9000f8004081c04021084403180b04440c181e0105800c2e50000d05602c001054a4a0880415007070554040c0180340e0380da80c81c2c0700c1d02181d8021080052081e10344940304e2001e0f0a544c05445036007001c42d0800181500b0341c004542c205a03003ca03507000070390000c0c041c0048501085500624400c242000943c0c2d40d15030f40d0000703040080c0040001e620a60100500468040000c00f4504c43d5101d4125801c080c00c40d050034400012441c4503060344110380ea05034452240c82500064500c14035003046401008181e0710701800d00e010030303a011002588046404050340342c40565007841035404e00003000f45042031600703820110078a01016103095101e13104e00301242d04c00d0f0704403900850048049a0040d400c2c0b50400d0300c42e0740d400c550800602c1484091140740c035010003124102e40143c1032192134080036503142c012100088414030300c1409840384c0000414401c12603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 906045251 1250 906044001 906044021
    0x6020705160b1801021207030c08120103030503090c03070f033507021318030c170a05030a15050a090e03090a140108090f121c0606030c11031606110c01 67
    0x190b5407540001400014252008903426046612110800407005009001c4540080d09850075030f031441c3c00340c2800c034094465481c001e510600008000810b16501402450180000c00280c61440550300d0806d070b5507805500400d456038550090800c00201c1061130f0190b0300340e18842c55100301d502c2d104640490b05d2034051078552190001200002c51910142d115640c60418604101a0440c0e0506a200045a51f801824807030129010002d1105951610010302900c840c010703903602d00f4420080c001d400a5860720b00d6182015070402403030701112441010391f080940844407007850f146141c00500700000c0340a58502040000f40f900e0388901d003641c4054482d054811000d50480c1c80010441c072002048091035801820032600c05000104005c0404500c000110341c80d1078407121000e01030211036811549841c0b5014002a040340c054011140190941e1031391180d24603908403071a00c911070914a081801d910048040000d1301540c01b034010501103004076410042c900c81480c1c2112030140d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 906046501 1250 906045251 906045269
    0x81e190501150f08060c031b0403060b010f080f06091f0e040b0105031902060a09150e0306100e2707030803191b1116030c0806070203160602070516 65
    0x7003030004518010052002001608901100743d8500042503445140240c5954444c4000001003510207034400c02d000c0f80813680c80d100c603503a290f6914026000700038141080d80440c0d070228140140c02d0107140c180b0f2180f03082040e903081c130395202004c20a0f069801030002000390010741c0c418450001c6609454094001d108801041c0e0409051000a007101607001511a5101d04902000703403500000d80c2e25a0355040d60010740f40e14805078207031851030090300b040300c0d40f020b02c03150440c0240d40100c991005070001d40549981e610386000150301241c103805030b40b40c02c0444401003445840d5001e40301c403d00c0103640240440c03032600c0d030040341464100e60041d100aa8040240018200343c0c0e60b107085100c420b85810080c842035020705045080d00b82e4040c1060004803640f05aa400d0240300d032841d1100701e130f13507034240751510f1380b82100c0e01042c00d0013002664841c03400050005030000003160051100d00c49068400001707540c07440083e5006050448243c0260f5091152000c1d45105013070150101d08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 906047751 1250 906046501 906046511
    0x90c0f190603200a050708030703140c0d0c09060905121005010810060603060509061e090118050a05070804080d24080d09210f02030a060605030d0207081e190501 71
    0x1001c00e4007400c3e0122001c00c481c03c0f04101d00b8035501e8010084440483d8020007142d102d5441c0c40d01039000380080c0320b800301008080000c1054600d61600141100a1403100401440d852910100c464020500410300440d400301014030540c0380540c0b00d044000c446908544141c000c0030504002e56000b84d0102080d43e02040800500c0032880c003c500203002d45280400925140a000580c1210b01410483c000d2000c03618140c4690040001e503a10700301c01030074100c0740b942c0d1000c00c1040f80041d1202d040850303103440c1c04108088020300406020f80c5050b070751114661260f40f9643c0456000b14140841d0310340d030740210300c14100c1c4030441c415107000404103200640d182804035814120710040450030069a90030900018045042000c41c030031801802184850141ca441098180f100d0b0010390725124071050b1204009068100209444040d03064941c0700c10a080140d9807142d42d40182c20301c1c0d0304403165144087e01d4000044101110050468802010105071480031200418003a42c0c1c6075150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 906049001 1250 906047751 906047771
    0xb04060906050a091a0d030c050f0d1409090103060522050a23060103080f07151515080f040309030f0b0a110906070615030212030c011103090c0f190603 67
    0x103142c80f500a14002c1814030000d4003080d03440d80c0c88241c880030580306000070611841414804c1c408a0349480e40b000c03c6904c0d030b803003440fa015514511300c0c00700c0f80003411060310742c7c0003030f60303c80103079280c60b680a0b00c20301080c0d08541d2980e0140400401402440c0000c2c4600040540c0d0360f40e0000c045400b9001a03e0218118102a003e681e5581c101401a9002c085a43c144510014905044035044151136840d0340c20070030030440d54440c4a0f130241101d14428103126a000c1a90700490300940d05480b4500560b95550310300c900302410700c40720340200c0d41c6000007556492a1103003c60707200d407292901a40e4161203a03600032201100100580321814000c04108809899100e80003c1d0500384c2541420b0181c00800a0018452004002c02e050307203600384000741e400508134250286600806005440c1c50040005549420400c003034130305582440d80d40d14283d0300744d10880c4d0007031b41007801a0501c5100c3c03400b070122251901801c6500141b0002c00c104800c1e0040d424030018220702e0ba0041032170700403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 906050251 1250 906049001 906049009
    0x61009050606032202060d020d06051906170406060321080601030e19050705210105060405010605040306020903121602010809030a17181c180b04050f040b0406090605 73
    0x20007000701c0e005220400500c10360b00e2080082c0c0c1e200030242004540c403d405840403c6460090010304982c160022802041d102460b4118409a607401d45448040091205040032a80040c1c40b9840200d01443c0b00e00026102c20203d00350b103c1d0050310042402d5549544140d65082e80760b00c402c50001030304041c001c1141d800f6002d1038002c07409180a11880060405440d01c4461005103c240b8002000b48030301040028440c900007000000c1041d100d0b26100b401e04261000d9012441c20554038003000607909251510600723060701c02694501d403e243c02d550b42c0000a500080b20b450b49881030081207800c594007840100f00c61423003109091540c107902e10014081c180050700a02c1507030021302400300210307030055418849070380c0c09a214250b5200c2d41c01614a0101d0b144c88400e8074050301e012320710660304400041824000c10340d00d2040104070a504410068114082e040600c00104001c10103031500708140e000700c4200910000b90544414005400c891407503220003000b82c0c940008000c2850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 906051501 1250 906050251 906050261
    0x1505030a05090a030e060a02100615020d050a05190c0c14101e08040309030c06090303080906040f080306041104030f141c03090f02040e01240f1a0c061009 68
    0xa2108000c020b10502550050017181d407400b0068041e0b6000300721150030b90300c200040039009945400400c040e07a110480f000b24800000e0390f51026100304404004038521a40440c0c52803502030352601d0034162119100007034040c00a46d0802080600308900010440f1503050f54010130b80c504030401070111201c02d000c1640c1030b500d007110500503000c8120104034035001d07008000c40780500e4606074641e00c82c40e056850300b00d140c02c003030040c0c0c449400110355a0f4002e0f00300c00903030f4069154010380b0b40c0c1d603402c804e6540d601100c00510740300c0c0140c48030300020352207000b40d070700030000030710106034243c0c4503a1580b03c582050b44280c03003100c48030b00242c080c0022035132400d2610140c0c0024041a48a1404024409900c030345501e08066680840c08103000058030702681d10341d402401480500c1000c0da810b0b000c0c041008041d000d41030b0162956621461000502045600c0b0350000d8031101c0c50070107040c5a01d02c08800011400381c00300030f0301d5403204050112600c9440090200300010f070a010407101211 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 906052751 1250 906051501 906051511
    0x60f060a09091e06021b0a02030c0418020d1e1109060315180a02060f0d0c020c13021b01180c1d131a070201063201080705041505030a05 60
    0x5490486441d000c0740c010140e401212075040c0300c1805640513454030f10002d115844a040011902c0400e40f6007401c404128054450b0084080360401c00c0703a0b138100030440d42c480c0790f0448101940c44d0030300c0040c10f000a408070f2550060b40017400c40d01c5038000a04082d80100d00c1106e910801c282c103090103240805107690004000e40003040c0520841103400401e0300b000d84124414224007422483c035160400492034440d0f4064003558448080342d604405c140c000d0002c0b41145418014442405403002606400d810401406410000c08000b1044000d40c400c050741068168441003214a0346400d00542c0010340e50030805142d0055641400071035110f140d0440b880c21440d000d01060b01c0700d881802c16821049188010106180c0c5140c003580861301c004040010142c100c007080109501940120b0880301d030021902160404242049004c503003042601c1002c0210b00d000402c154411444503034003020303500303080c0d2600c1d8603100d031140004140792550000980000030400034613030900a46801c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 906054001 1250 906052751 906052769
    0x3040806090d051e0915040e060d110d0f08160c090203090d1b020a090e010b06030402061e13090510081c0503150a030b01090e070609050120060f060a 66
    0x3812181c0303000300144142401d40b09000c2000f9103403404040c048003200d803556002800030b58207980f02c1c10502d200c7c2c0c2051041900f0307101c64500003040360401c44098000e00f81d00c2091040618004010400341e9080b03071105580b000c4202e02404002180c02c80204510700e0740c020000c050300001c1c03400031040000c0c0e810005046005000303000780c01c500001d21110121150510240c100d904505462000260300000387d0f02412040d00001e08013441e80c1b148012000e0700c0d0080c45801c1040c41441581d2109880080d0882b00403c5400d400004406021103901c540c200701d285011580700842040c00c01c50b8206094032a030b01e0301840842203101d1800c40040100310003030001400c40c0013221440410003020101400000400100392407840c0c02810801c100003400315074241d03208c0c2003220841d60309000d0120414034084a1140050380003905130308450b03a994032844290704010045451080d1038448120714580c4581c080481c3c9400e02074141b10701e80b19a5481103926000301007101003d01030780b210b000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 906055251 1250 906054001 906054013
    0x902010e0139021011061918030f0906020a0206070209130b0a022203020112150801020f042108040603240e04110103021908090f070305071716180f0c020304080609 72
    0x30031700d40440d62540c02001002d20821017803503840c184014056801d02c058030170174800182e6040541000c0e030010020841ea5408000984524084c0c1c0e440003003240103075101d541804204010310f043c00031180c1c41101c0091042500d007a56503005103c00050310311891441e0089814000307941d010384120041c40507010340362802483c640019250800d00301c4e038503c00e280c42d03000b002c03081541c0001c07880060a01c0e000840d640c5035080030600c2281c20600503240031494a00841d0b205040c2c04000502d159048001c003860a8682407050700145804400448001d10039514000e02115419500000b0a140301c050040c3d0300c0c0c146450b505a20443c155a414148107010010038200d9178011035044110508040d41b86440d03102d6024a00085c600488000348590500401040341c0460070100321142200074182000d0719002031902c9502010070007c00b02da007003000700500c3d860b5000855010842c40300008641c0c00d0b0212000130754160034041e50142c0e00c000303010050f5000420001d944039148001401e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 906056501 1250 906055251 906055277
    0xb07030528080a0203070c0c080102040603050c1801050a022104080105070804031e05040e161418011d040501090c0e06090a140a080303010f030c090902010e01390210 73
    0xb0038070b034014042035034441e800320000c5c80560089442c0d100d096040624405240d1391540298081e500502404002a0401e40400c100015400a0f00c0403801c940390700860310780844d00111800d070000400300086100d5120001c0d400301d807650408007007103504211103a48500305912207080d0f0b10041c1100041002c0c000c2000042580001c1590140031309036030048003140421411125800303981c114010203940f01d404e200f40e01c07408510600070a080b50b19000112540d6110a0401e8050403014142d8400d5082c1e07550519881104084e040f442c4851302c0709090160380c004641111001d801c805c010507940d41e804a865500829032940d0600c0494075245050f86000108008160714450348044069040d90403580d543c1750400380300644951005c50b034403527031758030b8804043c6c150500c402c2d1900714002c100460700c46000d0190149180d01a1071343c12560000c80c00440700c2040038040e0a0101020040c0024000d4000740b1140c2295102d55001201c60320500400a550040c41565802c1c40310743c40f82c1d04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 906057751 1250 906056501 906056507
    0x60503031e090114130317070c0e1003050d02010902010e04060b04030609050f0a03091508240103020f0a030504111c0308070207050d0305030a20220b07030528 70
    0x81d2001c102401865100c00c02c8000680b501c05101c09a003528520105461070394903480d07282d183c116401030004d40c0c2d881c103a00c6900b55181c03260722009809100c40303060034130000d0200d0300e005404c402c0b900720442a031543d80d281d16080400074021100144d440b240d103030095691196044c0f81ca0b0707c08803020040c151030072016402034825440010704541e19003103071100b400400d002d0386410541d94015120266a9442c0061a51400c0e0244032460b218480205d00f2030751082d40580e10805400710513000a55014108c0f245045240308400c2c10540c00f000300303114501c20000039201300a015103000c0f99500f09440c00020202800070414000d400c1d15080c901700b8010000c80280d80c0781c06083c28140c903155a00104c0c10030001c0d0b00090b0b0040389100c031420825602100075485444109010008440c0409950808401c00031401c0040e41081c0101441848449a031800c512400035022100720390341c05a900300c0307801c401010b5000c0b510100b0005880241c0c52182d901001c44181900c003041e03a105005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 906059001 1250 906057751 906057787
    0x1030b010e120304091d0d0507080306010804021201020a1206120f1e0204050123121c1e02010905070602070e0f15032a01030b030d080907170c0406050303 68
    0x710b01c11180035a1180ca03060302401158050400880c05000903281113468203449080d0000641152150201c0710500034403d40c140d50132507a0202e40a4a140c45c1d81004441010f0041d2080c1c0e804410006182c2507003109100901e44220b517030700c40300100c181480d0f80b40304950003548102060b2900e0f08a05c00020000c50188201d01d80c00807405c00e501d40e42d44110341501c4407030340c0025049460f100000c10300c001c2c0d042d111600701c80310418114140c0c01105c107008980c3c0601000c44410341c840c4180380044c0e00010460009820a4541212110718107000c000b0388480e01491400544d40d603039070070f03000d02c9814000d880c080c041500040c001d00b40f81452080e4400f000031715030a900802e003008a078400110000034282c00000404490f0a120001e182c22240f960032541030507075003d02c00f0002185e5002e030040200c1940000c0203440d28000440e81a074804c02c0003000711450380907140c2c0204815900200d100e50f02ca15910040c80150300440034007085954a8002c5480303940103200400b02c240d131440c09 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 906060251 1250 906059001 906059027
    0xf06030e030d020703090f1212031a0402040906140612010510110a030e0405010503190f030e0904080a0f1706010e040b180402090c07051c2001020c070501030b01 71
    0x2001480c184a400d03028150300034441d00c000101d0000841ca018154050030b00020703105c00d0120030462555810600042c20f0340088002d00000383e481e580c40800c0d009500142c2c0c80c01051030710070340800000000404070703407040e00402d01080c0c1d0b03064240000c9591300001580c41d04282c0e0329928090a0f90185d00390010140f043c548035820141e29003211a05c07440407601c0d416411811981e500c0742e03519024007501c0c8220140c50141d440c3c2000007519203000148180032180b050b9954086200e65212421964221041541800008513034404161120a1554031413400f0b00e00309500c60140b0310004001038408150842003100341e80d040384520204041640d080142420500c0d181820314021034003600c13081c43e0050340811604589103401c810103030440c1c4100d1003124480002c1d40d58864018680c01110409003880d880000a11604510042c50354549107850034041800021700c0308416502c50300d0000050144d4011610465906042040002924007400c0600416241c00d00082c10342c103176554 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 906061501 1250 906060251 906060257
    0x40b031b030307140105160302180f04060b03270318010f02070e0c1308192015190905090720160e09010902060304020d03021903030501090b0603010f06 67
    0x3448803030550781002101c20f001d40c00ba242c000d902d0003e030485802040c003142c00205440c0c1c0f151140602030710031300c2110032214100c21403500e0020805c0c00e21000c1d001c0c16002c0e64105e5565400441d03c5070000e80994842c450040c6a8641c0c4610410701c00140800c2c01303d00c201c0c550090002c14240f5a903c080148446400c0c038003001503d181e010105d1800040b82c2c131504054944134240003000c1c100000501030701036511025020503580311030040d03503410702c8100c07550007480e00101d00001a041f0416034103c1c0c964050003080342602c442c00940c030320f1070040502c0d5044400046413100d202c1e515070b4100d030061107030400b4003ca524110209902941c01081d42040080039810300025951072451000f5250b041070485010340c40d0441450040004d84c00b442d540e08004d6400074000301014056407034078a80c090b05090031500c40741d0034006040c1d941c21046082d4000c1d180c0d5191181d280c074415040e41d5000e60707400704565241c0b80e0300d101110b48200c14a80235030070030401400310040402100c011a01d080ca = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 906062751 1250 906061501 906061543
    0x3131a032206050907080d181401020313140406150807051b16060824010c02040f021210050d02030a0b360106060f0f1d0a12050705040b03 61
    0xc404446005281c1008000300c0c078250a00580d007000280c59020380b4202412502e01500c40c200541c1d07908590f03c40b9805903e4402ca0621191000e494507404032201030040744c0c201141100040b00c04c0b0f0305030304100c0102c5401204030300649050302420000300b01192002d030814484110007000481d0040c4020103200001892402c00000300003110f02503450901030718441c100404484203840c400344141c100007242c0e0b0010420040c0b9600e038840425601d0074001c044042090700545511071246c1080c0d0b84281e40340000010b224150000301542c85035264403010300e180022001c580c4240a410460088078503580c150010384001401d40e14080c0c00c01420b022564980c405024800910b5040130100d10001751940103905140009510303421440e00240010707512420111070000c07400c4440b60016203044000300d4403074007511a10b40000c9840400114110001c0042000649240d008600c41d40c030408081c0c092003020b02404015040850f81030045039682c800081d590801d00c044c05034001055 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 906064001 1250 906062751 906062791
    0x71202091f050c010216230d21140a1b020c0918031603170f0109050411040e030a020c0406030809060a050d330b0417070b0c03131a03 59
    0x144083e5510742d1034050007507541b031080e5042c2d03030762104e83d110044400b9040d20380c159400d847c000050f040e840c008500100300d6544210380c200c4107030509400600c2c00801c5400220564049809903003d81350004001c88100d003008480901202d05032500180c044045560a4017003541c082940c0c0b411400440c2d001b04162039200384902d51040600c842c3d1030750710000804000c440c40b81c050304e0060501a03102e5108003a665007191000c004215803000c01c0c8043c2e08018805207000b40e00c040c1d007090180740c0d50076010a222001c541140c140c101d180f845640081211841594100b02c0241094026141805030380c1c6140da908015028a100c00c0d4403c0700081007103070800c0c1c03042064600c003508501050019046101c00c0b1207209144071040345104030907640d071310840c40940da1807104941096504600e400c0c900303116001e611803628501b9a1600403c0000581040814068807807019044040c2d55100505040700b4a1210f242c4d020000d08194442d86120a41450b01500d50101d000c540c0448038005e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 906065251 1250 906064001 906064007
    0x30507091e33050d030c0f020301050c190e300105071d0103020c1b150309060a050612071a041e08010501080c130b010905031005071202091f 62
    0x442018060900d10b006107010b9100c41d002c9440310011414141c0c042114260294000076a07140c0c0240307030300a01c001145500180c031440845065a001d1100d1039484078607940080d0960b00300740c600d01c80f003281c040385068052204000c801d1990344141403a070365105d1400f001c0f54500c6149800c0440503c1c85040b401034540e041e1801ea41d40c00a070070020403c6140040b1301504d01110781c8419171903180840603468255009108903445051110014800d0319000e110105029421001040d0001c80241e041310840c200300d80518007a040c00409003c2c02e2500314213010446500802c2c0b90300c921041c0c0280d00d9480c0c0049400e1054540c0030702e200c0102815a40c03400c1c1300d8800c1d075000c2230012100c1010010600031280e03606041c0d8603680020300c580d0341e88801d09581c1361302d12030040d588035041201007032080c1d480c1da101074060f071810304001421039030b24000682400050105c000c1a284c56070200311800350b00403010780c000801b000d000c41c105600300001ca0903440031848c44220060f4616004040030f40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 906066501 1250 906065251 906065291
    0x270509091204080703110a0e041b0b04140306060102060408160302120301080c3105090a020909071d01061706120706050705160302150a17010905010311040603050709 73
    0x40400c41d140d65540c2e0707083c10030780d1035480b84030a41c1e24000d6960015202e141501c1000101c40b00700681c45010f40710b036290100c1e6142030f080e0002c926029081c00140d00110b030f60180009001c140814610301d04403805044c10404010301d2039045402c004100800240f01c1400c2e10901701c5040c04451407100c0314038050349006140100d984d0b96103004030000903204400220416481c1081e54680e500740190400d00221017075400707400c24508055407440c040601d00b50720259129450f139003207a440d80215008111148008d8501260360b400030b2405200da60143c040110307590140001c0da0b0403541c5042c02c0100041110600c4050181250001c11020b558405408520030305203026103078000e50b503210192642c0e2001c0c0381110b0798041c1d4040c860b107001c001090380080340e8024100b0b039648407540c850780c1880e50054086a040c401a005c401d030a507540c0490842c040c1c0480040005d05504509110b9900380006003440d104604241c81407000800102d60b1008503226000e002c2069190f0010105a0722 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 906067751 1250 906066501 906066523
    0x2001140105040507050715020c1b031b0108071206030606030c081506010e0904022202040816050a09020a1b11011209030c02040b0f06220f0b0403020609060c0f0109020127050909 78
    0x703c22b1000e8500b0b03d00b45802507071880d50040b8201d581c005644581000c3c3c0b6400d80301c070316001c02c5081c400110b08500030400500401c848000c00a20b0707035225074849044030300ea9002598200080c44040c000c0700030401003000e10314800c400c0003101c0d02c3c11000003007080c458880014050a00f041c0441c046446000070f80c1c40d80302d038214062054a0318150054000d4125100e03102e01c80c0305040241500040101c1e81100303a96014009520340750074003000304040c0d0701440561040148003502c10707404450010004050f0ba1040c80984080c120b1100010800c0c91190011b0203410701c1c4c900781c0710003e600420b220400c230743e054402007002c081000020314941c81d10004035402510001e0000b000117403281640c154642c210b107040440d90344622170a801107100f4021541c60f0301c1c0c208800e10140c58040c000d40700c3c0140003003030f281ca030803e403480003405c2413207019801081da0f460300c400380211f60b0460a80d101c001900620800c0400d8220720319104030000b4490359000f4085500400d4004106011840d060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 906069001 1250 906067751 906067753
    0x4060e0405010f0f06060509120c0306041209050a140d05101406040c020f0303042627061327050709030302191703072001140105040507050715020c 65
    0x92600e801c0c468042d1030404280c0f02d465207001020300d03e0030311078800c0d40c09584440c2d40740743c280001d8078280301c0240d1074000a41304a1264480e102220703942005014801d600c100c1ea200c40000f40c148001d08a1401504102e10403200322100341f0000074110031101d42c210003107070b400800000a04201d420280000511103402c0c2c10a10158a40b51b05010320501071581a45c3c100100c00c00d5000807a1034550386092981c580e00100081004600b80600038050800610545141d02294090603886548406e82840c0b5a41017110301040f070200308031001c0d14888040d10f01500d854244e05540c505d446003030050082142c1d6412801c203000744216092080e20303078048002c00440c104404041c200d5845813100301c005118421101c5040103051941c030604d41e130b2003050555040d10485600100b038000400c900200010b4a0741e0518030f00201d071329100e08074604800019000c659504c901150032050300001e0146090009010301a07500100710380d02260400303040000c2941e40002d84000c0c1c821000201ca01e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 906070251 1250 906069001 906069029
    0x71b0c0e01090243051501090608012f0c07030803040c260601120516030c141203041e03050303010311010f080709061b140f0115030503070807020406 66
    0x342d420070303500070030800c0c4185204904950606201c81100d80e620030a0141c207000341d104101c16404a800200b00e0302d4419000d8424501031015040080d000907408108a80d03198070042000610038031580d509503003840581002c0c516505101c05002c552102000360300a000246d04a0002d01400080007031548200352907980d0405041000d80c0010034081c40d5a205414801a1a004110009100308007003d902524003613190054030b8548103080241541c607401543c501503070a45210704040c02a40c8a8400652001d00303004a0030300140500704d0039800b8040861074059044800410340c5c0c221040716a110900c6900c1040c3c0d010004000d500c010951f00c000b20021003040110030122280003000e0741c075000f000c1140e1034125150070b81500c802e80458001c2c078080c49558071940058114031251544541003600780d80c1d0303001c1c140000350f02c070700c02c0e03604030844045404a00380290701a0101005441c0b1000c0d0440c0c490035200d1103a610001d0503460300152510440d180c41d00002c0041042810b4154 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 906071501 1250 906070251 906070259
    0x9010902040815070c081605100e0106050f090a020a03021c0c17060f010c020303091804051905060f13021302070b0f130209040809030f03070605010e071b0c0e01 71
    0x690441c1c059086180074429043c04501019500c40b442400309559a0100960584504144c0da11406103140b01c2c4071400500c0000c510f0410601c4415101804e000801c0700309460314500f150300c503420040c840e045000302d810482d0340c2c82c610f043c0c006002c4000180e5603150110b040e8004c0c41010803a030011261103245654000c03640d8002c05d070b030318169156040d098402c2c02032004441801c50b401948605100c040900f5948180c0c03107034010900c0502100d18100164000965100b0980e100c88100d0300c09004100400c6418080c60003082d6012000500004c9203a82d02511108000d00d000c1b4456405800103482e1031000b000c9803e00d0341c003e000f01032901d40c2e0100d01c00180d07001c14021b54480c0f42d10402300d1400b03c1c02c407000e1881402000c0959040034001d908011002202400c1a510300078140948030080c0d03400e00a0000105103000103550b1900030345004408d86005030300c102444000b07841044001c07600020b040b94485a0740c1c001c02401d003402e00e042000c0b581c054200d0700820342d0f4800082 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 906072751 1250 906071501 906071519
    0x601050f0d060305121801090b041809231e061b04030f03050d0e151303090f0b070b0705040e04170c070602010c0324091104080d030f0b0d0c05090a06050901 69
    0x6a03490340581d1a031b29407400ca001940e4120807442580180704040000300a084014920000c4024851401050b06c4481362581071540c00c1c2201c0031205602800901c10010100f04244640c2044648104a04899208410380c959000420204490211514500c0c0c5195590101e03000355034406d190440c0d03407205082c010156040644c40440b07444c03400000c8a04404001841e2000210916203650306a503103443c034581803682403000b1010b0241000b8003240d2120b240c40c04801070500116066210380f640c3c20319021989000d0003107020b0040803c400d0240c0754814110f240d009400041e005040352404150120620601400d4480c070302032054041015076040d002042d9003042540c00344603803c081945410350803c4080b2410031006258010010000c107504400c40c2d0100c01620141051703030301c10603603050141c03c1c2103400c0000d5030740340c8546050225100d08131a00e502681d1510802c40f031030317854802d8007006002d0107224805100000d62001e0154004101400c005044102e9650f5940411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 906074001 1250 906072751 906072757
    0x9150b060d15030c0509090d030c1b060b0103050c030f04020f0f060a020106050a06022d0304080703050a150912030509071d0406111c0908191e02060601050f0d06030512 74
    0x4440800040b0070001707aa02d0141205802811108080d09500c071840c60150004d0141c10b4146c01846411781c2060300c400712420407155124010000403800758900e40c001002c443c0002c041081c0b0b410706109201464503107265603a40540d041c0c0e03400c424807500c0390008140c030f8010380d4101e6000c8000181c00102d5039040d0414011100140d40201e4620b40703540059071106041206500e24180012061042c0820000ea0403035803200030302980d02d4103455003003103820803603150000e880300c0d4040e6134594204400204030710140d001c002c40401c1603c01c65a145802c0442c40486602050340700c0b0302017040384c02c00340203920040c5482c2044442c001c1c10700d01000240e40c0704840c00ea6581e03181c0400000b9100c94003003190b20260006440b0081d2140109040c40102900c82040c1c0d0401c0d01071104155070002c01c2c03440107001400d5111640e4000c525070b0381c2180780c0700c0b4140713680442d00120188005641c006050700c4100520702c000644071a002080d80c001070401c1d0340040d105215290102490901c04401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 906075251 1250 906074001 906074003
    0x120906090629100c1b032303040612091419020906121f020705030301090603140c0a140301020d050708042102070509040812070207081009150b060d1503 67
    0x40422641d8070191a1030140000d62071041d004110b0007401c441c40e40c8191845141244203052090754442000700104170307902250011a030700c102c0e40340f100304a210a1079512152002c0400110f1a2900305000100101400050381e0009a201c070b1240003000841d60b6513034016651101142d10040d40880004410701c0310b000c0507070240c502030002c105641040044082d40c04000d80c000c001c8490400ea043c540744140032400800c1035800e004002c00102c0a0000b14000c2c42804808075200d0308504011046014508880740b843d40803100d60080d940350400c0340c008a401d124001c07041d4594400210340a031180d0101206c1c131500e0101007050160300051083e0065005008400007901364085454240050465800c00341c1c5c032655080020b0b10706624a280d00620651311242000e041c1085402c40c1a800d840310005030300840c60510102e4010085510904070f100414000c040b525151008040310840000f204562115150011900c5500c12103140038560305017000a221010480c1683e1540c0d400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 906076501 1250 906075251 906075281
    0x50303010510080903031302011101020c011d031c2007080315030706080115090e0f01050108090c1327150b040c050306190f06020703050607050f0403031209060906 72
    0x2852400c0c10740320b1856184103003038184c01149107440741042940c00c8210218104e040001c6c0140745c5000072021300103400c01007850300000c5240d6101584800d450b041c2c00741c5214643c1d00600a042d4068003105c68146030a01d14040010300440a03426002d61940c03100307440d0540c9000180c000f0400003190f000b10321076484120150010981041015102d00b114400d4100250942e0b0040c01641d0b1070461108001400e814120b85580d59410070001100d81100c2880145000b100100030079600416215440511100074203d00440d05000801c2407618102c124080c660b035207003980f90b003440c00000030706800180b42d6a45440c3c600d0f103060104000c210713102c5501c603400c185d501d140604041c000c24222a190b81c94081c00d40d41c07074030280141d22891150003030242078046c400044080d19400d65401416469010300031850950501c245051005040042048420001880150002410384090340c0e4540780c0791000d00b07040702641000c0d1440c0c1e1000342c103441c540b400c1c00303040040560100084004041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 906077751 1250 906076501 906076519
    0x2090c0d0c20190308070e100e040b0402040807030b0603030c0106080706021207080f03130803090a030201150e0402060f0c0d0309051c1d04060902030f0915090d03020f0c01090503030105 82
    0x2d010107844014a00c10800c1032a2141140d0340004e000380220343d4400c100340390402e461309031a00041c03414603220010102180344c039404400380c0d0515020740411140251415880c0510742200340e0b0313990225203c00740004090101045140d941030007100c2d12550f83c01c009111403500c41410079294420b900c980c4001d403084005001e007014841065030401600048150b08050000718405410307840140241c5255610748034680001c0c0c440b00146000314000c9000784403440700740c0340190854189405c1d403a0140c1c1000400c01140105001c2564000da0543e203c03525912440f00014250103207100005c0507015400d42c50160a6041c0d100d840528042c10444030b16821031000f01030b0a540781c0084074000351044150080e07415404c03a8a5010150140001850a645400800490f0025500200303005000340602800800401c02d42403880d000e442a49503d00700340e40c60725078032828840741005058020801c608d03269000419135460314061402031140c0744c128900503850780d0007401400d21941c1c0300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 906079001 1250 906077751 906077807
    0x30906020c01050108011d060f37060609050301020909060609030a0f08070303051e070f020c0a09050f0c0c25051309030201060b090d2a0906030204230402090c0d0c 72
    0x54123034020034403941052252744a02c0030010f205c010390000c80c00d400d2030b03109407449002100000b07400c2d1113660410000307816003000c030010b0844210341e00c218070981c010300c901c401c19035a401c1c2090704250102d80e050b41d1003072040d0100341058ac8002340a00340c1400c900c00401401384010040c11075a00c2540c0c100702c95500e21030b2510004400c66030401851039101c000034185c2e13000344914003d00c81c1a00440d030022441d9030000300c00c50607039044000c0c240d031035105124081107c4001c00d0b0b000010401100d0030007040102282d5030f0341d4042c1200f0384070000f810050082985001000001d00f1018000d4469480d100400e00050141c191049005610788000041d90301c95503001d55000c01001005045c00140c13544070b4448170043d10948030451002c0c0e41070440c2c204540680c0d42c00510721203601256403807550040008944802c980ca002d0008032001414054540c0108036510550407505a0425111182e01a134680170b1064107008803031500d07400c07823081c94005000454041000280c0340394030f091 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 906080251 1250 906079001 906079003
    0x9030105161d01050d020a0315061103030f13060f15090c1b0606091b0e091e07140c0a05061302060a0f030b0604030b0105041a0f01030906020c01050108011d 69
    0x406104040028008525004100b04440c04200c280d001407500505140c403510085049030b0182c90280c01081c2d403540485078800c48121403d0080c10300e400d005c0d4602061020154481c0b0000704101e0f00d14000500040808d10a98480161150440001c101e1845a81d50707c00091195000300d10080c0e000c3c1d0800140c6400b54021020325405c00c1d82c030386517440529400c20300d05440c514030803501c064035428007048060b0240304201142c0312508203203849000d60140a45281040011180540e00c05002c10141d441c074034481c07001c2d400048002c000035941c0d800c02140c0d0001d00d000e040c1f040f0703040040c41c01d880c05400103034056100d000d9000e40700300352280400ea400d00d542000c3c00075040b00082c4001440140a000400c902210034240480e10704800c0000515951054200722041c00a600052003642804c1c421190300c09501e054000b0340b11070701d000140c1101c800f032094904064032441d803c070070015290151074424580c0c100074003c1e96124690745d4003903c0719400c000c600c014100002090028 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 906081501 1250 906080251 906080281
    0x706050f090d120e01090b2d062218030305011502030c06070305041b030c1703030601020705271501020607050703091a1209060603070510121a030304030809030105 72
    0x102a03c407101111020641a406005501c00c100019583c48126002090380b0f9184180300c0c41a100001d8241c2c903016546041003040d020362032040140c04c0c1d041003c1d070748980300384240e40724400308800200e005a0810801030500d40ca02c1411103004108288101074254000d14140d8403c030032820095508103a00f00e949004d590360800130382e801500443c030014020340c4240e80040c01050f82002e052000700400704820300ba0b6100b10b4141c68818010001440b9041c003ca03400b0305080c0255145060a000007951811940183d9108400b000e0141080c0b000c4201800075424040869401d0340c5000102a4102d481021103540540603040024141521074801c848499a050f2104861641007900720042c2d1010718001041c0c48004106983c4100c0f40d0886903485070805100a02c001c1c6060300606062020a83c000341c022580e00045051041d08200c0703282c501d0300219000202e0819180c24035154481c10155107030503000006000c814007862030020962040254000c0c4100d03100c1000e4a54070103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 906082751 1250 906081501 906081523
    0x518010915020d02090924010c02010c120e0d05010b1309080d0c03060b0c030a02010e030903151f0e0702070e1e0a111605160609050919020706050f09 66
    0x1a16500d4a18000c801d54094982001c8002e00107007464125008100701040c262808040a80c802058178400c4014001c100911002071908a460962960003c0d10318441d200000304015500448981c842d44903041ea07e00d050001030070040c0b000d0f403a0920f54020700040841d2802200d59a120940313162003401441c14080d0311000b007074500100908000010000080464101074a03040d00141120380d2201a12185d044039001e5541c0301c0c404600070342100c1c0d5400513000c2c5030304288032042e800d950200e171848103a8190789105000d03686811035050301921080d8100c1220120b1080440d40d010760b4074110b4401ca006408980b0b2640c3c550007803410749401110031340e4014518130440700c1c0502d1404c1206400c04801d010106240540b24005040390300500d4196220310b6800c2d000c8018040d0402c510b9203110b868281c4118503c1c1401c100504a070703582e004083c0103040940115002200300042c6c001c440d00d042508644403049450306d14045c2800f0740d2500352420b210400f10310020000f048400c409 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 906084001 1250 906082751 906082763
    0x120c0307030816020a0e01050f09060102030a030f1d031b030f040605070f200301061e03021908010e0615270705160f0b090714010c02210105180109 65
    0x1a07459960381d03005683c0510021510700d20003000c0d00c0010707112030082c0f50240451654000b03040d07040c103043c00b44030000078070342e6481111000103109203a6000300c01c942030788203e46004504424000765103c0600520040ba0300c4001c2d4584185840d190040082c0110117440c641c150124440e0841081d62800303180d0015404010030402005041e0244000f4801c2510451003081e052141d42c07141d00f807800c8000c14803000341c50604440b0781c03c1d00d000c0c0300d140c01a1100c0800c501125140181c1c81076016141e01009010708032800700c1e000503403e5000c80d4001000000000e010040000e42c190b0b80380c041c01e59450409080038520b0841c9807610518440a22030f881a1a0080440e5510402c1b02100040c08600070300504205d0320045010040c02048254020400c030640e00c1c1032454079042c0c017a001404d82c0c0d030039004410b0601244d4000610005018424640028240114000512224244222000f940c3c0c42c28002c12a100c1c010340046224108807107082200f2080c1640d034509880d0065802400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 906085251 1250 906084001 906084013
    0x5070c11091e070c0507080d0c23120c120405100e0112020f031501170114060d061205061f12051618050a090b04031b1709120c03 57
    0x11410503002076070b489180845026107180003441e41e4080c0850944440001810100d11002841402c118010081c040d2000a22010301c2c402c00043c01c8450308400104154000c2014095410704240a480108080c9041e1509020303880e001e10080d41c00790a5120302c5d400361300d04081417100d80d00d00350f404950b001703441c480300510707000c42c111010300d00741d400981449000040203190000390300c068a100c0900603a4544d690406089464540101c1d0303981c1810030000110102e01102000c1d21603044907180100e04002200e400c0010b2810700034400c088801500d08540000c0c00c299000b20401c0c0d46004209075107460302c1d100401c2d090014051001114241a00390822014001ca10502155405041620400d000e800300e420314002c1300da840200f4014030901980060700b140d22030690810610281008490256615003105c2c00c4020000b600740016200c4000c1c1c24030400e04c3d1442e206034407400c0e0b241c2e84591215000c0d6290841c4403142d0040e0241c1004500e0340e5000600160054802130040c85c07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 906086501 1250 906085251 906085283
    0x90c020601060c0b091203090706030614010509011112130e06041104051c02120106052d01030902130e030a02010c18030b1315050610020109030c08030924090105070c 73
    0x41c1303d10068a100000d1195090782c528024000e0042c501400000c0080c0c0301082c544240102030320b1468100d031004286271503080c0302c07503078100044601148081c00d1011413146900003803030070003540f04644c2c40941c0d0000751620030500000501c605544056180c12459200c100620040301c04118030701c00005c008100502c101d203040c0707981c1900101060054060300041d90302187c10b0070b942d4880e0701600d80d1582801e1040e4503051250102c942c640550b89055510050408000120f15186003818035640300c805009644a145400e103102c070f062003090000310110002c481c1c0e203500c056207410041d442c0c002c0703c03100c0030b2150701001c1c090071003e08150021803c43e224148020710107002c10310104417011081d00000c1c1c6142c1c041000c0d203c0c0d48000103052038454103100c00c20501d55a01000c5900d00001240040d030031004010806421040c55070716075030b4050905143c001c204100032180800c0356001c880c00059161418800c0d524a4003c1c011138590301c1080e2154070703410000620144555104c21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 906087751 1250 906086501 906086513
    0x207051302090a031403160609020102061815070309060c0816090e01090b0f0a08070608011208030f060406080a060203150d021813020a031b140a0501140f13090c020601060c 76
    0x69102c1c840282070721f16000007041200340701050300c0c908944030341d2074030039042c02c0d90707018404143d00208151201441c030480b004e1035a220466011030342984080c45000c104014400d0f8810038100e40d100208002000b1b11040182c84c84c0411240b84015062001d2069400b85c45924644101c401c29032043c0600d0b420310f070b02c440140280300d10864000040c103600c640c550390390300c4030382004108100142101c2030925100804001058004040410100740c030389002400b52800c4a81c8074000a47d60306440d2140030001d0050600c1d50701c240d0082c0b040c50241c80c00c5c040380e64011400707900540d600c0c3c01102c0380a014081c200c0300034400a540046c8004034401a1481301b50a142d1056400d6801074200c0303043e030300050820300e00c0e0f00180d07101c881d104403440200380c1d8600b411000d40329030348800c00f40c0511080000c600c03041e280201230411481c50224030058280c1c0c025140d0b5954541c01081d00c0b50300703110a1812081c01446502c1a480c100190030b90098000b003a03140c10381d0110340c2c8065446845e51618 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 906089001 1250 906087751 906087773
    0xa0b09190206030415060b0a1d0d0f030e041a0906120a12051215040b1e060706091211191205031801110c0c0103051317190207051302090a03 62
    0x5880c040c1030703044860a007045622505001e1f04441c92160303102c007192038000707000502d40d034002041000f55090202d01a0303542c090303031060594008005103481c102c519007161203a42401b1007941050801c200450300702c170140d40c0030342d20f418292008001540d64100b0465801005091026960400443c0e4808100d441742602d04042690500354582495004110780400e4110f8009041c240d8265440003545400e001d088030303c4c07508583d201003004500c16948200d01602450611480780081c0f52801c00602c1c0e00442c85068002c0303072403c0480b61200d0080c1034070b514501070f018540036580b5030508110511002c08181c0c1e4001d800154800980e00042c2c4443d400a0b10030901e0305444400d09040381f609010709244503c004080c036440b864810482480e10310f8051030503040c1810b2104000802680180c225440c03508000752502d8400305a4030305802e84507600500481c104a2200104829000615502100c038181c450b8090345031140340742d00c01c034001d020401354481c141041c1000030401c0c044003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 906090251 1250 906089001 906089003
    0x21030914100b09013005070f050a0914160e030f0105010509010e040525031b17070308071709090405030301081b0f0f010e130b04110406140d09140a0b091902060304 72
    0x302145c0064242c1b01c440c9000c400782e01420042c64802e42c240010b09060b261300e4003c0412010502c07080c05401910480142c00504483d42021005205450544101101c00c4841400b03400c3d00c0c00300644840c500e011300000d00035903024552a500019030058190400c6114981003005400d1844034a404820049280c099a0050803055000031010441d501001c0d00101d800d200b0000002d031604072603211038540c030070f08004a504a5203080011421140c1103c5426074848446103c81c81c1240d000e0000f8001d1803040364214025004200801030700000840c180c0380814121010883ca2440c80614a11010b80147c1c010350100c15458180c20100d89002101c1414189180291a08404208500c400c981040392168442035043c1d03060605100c1c22680d040e00b8500c4515250070f100b000fa220300401c105410380c3d10000200807442040c60350041d040030b07500c03000c22560640250000c60707030780501c80002d5821000381710100707140d018000b52100c440040101d010018003644c1e020803100b40c20040c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 906091501 1250 906090251 906090329
    0x20f010e0105070f080906040b0c0d111203220506040302160f051023070c0e04080405010c060f050708062106010b071103010914060a0921030914100b0901 68
    0xc4950340507540c60000c8c4c8090003a0a041a80350100e000c1139034039240405403c4000e12000f05c01540300c000340481d030340a054000841c0aa5213843e075074452010004480320f248958620f003000441004800b1543c240124025800c507240340a402c40e031031403034801038821a10140a140e108000c207040070502080d00c5840c5040207d919604a0a1141c1440406403041c840325400a044802c1018030710103e40500102000c02d80c1524040e03540c1d00d50782c41607005042c1400f60305c820603000c0103140d402c55000d019414000380024100018003030000314003030702c0712840f401ca5440340d9540c04956244184290030840c2c001d0000364a003091100e5203038800c03031080e900e00d04e03514800c007103e880c00d01039511782d28414100082041031140b805802e000018002c9540c0700e04089001c004604100d8407103141200403a20a0b040030740104041d0b000300204c0e10010080300300070158080f008404150300d1403004400f00140486800c40d410801242000d020701c1000318840e140001003401880e00e01e00301410003003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 906092751 1250 906091501 906091507
    0x20114160303270b1e090c21010c0c0201030b06090102120d0b04090b07090f0f06050a0309051906110403020117060a050a080105150405090d030c050d06030b04020f010e0105070f08 79
    0x40611009041c0d145030a90310300100074103128000190f03000941758200c001c90418590708000c0301c0b0340d469108500455100d01049407040c0740c081000070f03490421080c0e00c2d000700011079804130040c000741d0320840280d0200385490024001814000101c401c1903005a01918000c0004282c1d140a60003101090700000e46d02c400b4907105851314810400c00c140180d030360881c64509128000d08072801034100b2840060f01e55010864481c2005c0070909540550405030784030001030104400616078008050030718032500e042000014188440c0311000780c05440184148664402c601c1d10b9407199201c02800294071520f4120211740c642c44268010754000d104500841d034880c0082c000c40123541280c4550f0350740f401804030743e400480c00903a00c802c2c00d907800d02c80342c0341004034551078000b0f2a100d1010b0607120515400c03114440c400321014401c810400704003a980380c1c188503510300740071a001c0703020301c20140c20710715298040d12952100600c160b4800c0c1c54815a13542d1085c4443d2143e0702119925024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 906094001 1250 906092751 906092801
    0x609040c1802030402040c02071a070609060c0c05010c050f12060604080303010b030a050703110405011d0306010824040b0402190504020703050c011406032109040e010603020114160303 81
    0x41c018818a180001c0941c0b2810540100300864070020b22020540d4495203041058580144440f071200415115551302d501480c02c00c070300500068400201028585400c81180319040403580d1040c0b0b000e01c00810024000d4402555580f01c1c907840c0c200c42001c02e2000007415005907030b40d0703540080041c05803070805584405852860b04213170801c85000001104002041016200d01640941326180510404103078422801c0c884c82203010342d6040020540c0f0403204140ca80901c900c0001000d01114110b607075035a5100d85071f4030510011448280d08101401c91588150b1086005541004500c040c0342c4440e800c02520729070401c041e0400c558404400107180c0d07120f20180220034004c0d207800b642c550110080c1800c60b100f0f05000072003050b00380140310716500c0004203400d11a404001c0320f48880841c190200c483d00031990640d034018103082e90004a620190008800c0341d2003a2038072210070002c403101d0f030802e020f107811041903060a44104004070744039030030407006c4118040030207a4101071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 906095251 1250 906094001 906094019
    0x708040e0f010320060405090903161202160b030a18060c0914010f0c02130b030303010b13121203050604090204020c070e07020a0209060d052a100c02090609040c 71
    0x1124602080d14000c0010020301c02c807441600304c40712920010501104003040000d885015a000f0b080c040d04540c40000d004030070420441d04540d483c4014552445054601981c4001e902030001e03005002d6016084900310012035088150340001c0999401c50755201d0b0010700808880c20400c00350325040700740e03a0125020748030712002042503940b03ca044504104124407040e43c10110309041181c040c26a45215a020400090003581140e00d0a817407080191000c0140000d901e2169040c0000400056140300341d100814486040100b8103c1c1140d0798484000f01d0001484050440c58200c0b01040c0943e20950100740e00903c010710000f070b05043e58010130201c1e040030201540310781c07241509114000d0310290361684001c40e48000c1c505103d055021448095025006600412606498008208042c800c0d011800d450800802003014801021010160440d2180380200e02c00100103038124451f984104c420b039006403503150700351101000d05c80d075200000c00c2564a014400f6012400c220 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 906096501 1250 906095251 906095279
    0x31407062012010b0a050f1305041b020a06050402030102090303180a12030f050a02070905070e18220c080319031104150f032c07120b191112041b08070b070804 70
    0x413582410145d41400d000501088820bc002030784507804020484100c182d5000483d1103160f41d100703070081002d803907a2011a0290146101865043c000030403d61354442104011900446003200c20070710050303803240c04611180701c5100c040d000500d4000c4039540e00c1d0150006005450092046500c071682d10241142194010780d01c03140010000c80c0c0f219803510707000c510f02801d00441580710105082c540c94800c01d00440081c4d00b1b0700380f0401c1c40d00c6030500c503110702100014880c0ca0250b07a60b0721a03001e5515444501040910086854107184188520684040e9400c0e240050030244e11911810010b17594001c00b81407231020141c903117802020241303040c807514100b0a000300070b62460602d103491940c10650b550300b00d007030360140204600e00844e81500322142c108002807000c581c0406070341c511802802c0000b00c0d0301e070140000517421b00f02c40c0540074528466401a207500b081c514005202d644080d07141d01c544402c80c0c2c003c8005002407196000200603452040c11441d10b0310b41d5a084501d0000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 906097751 1250 906096501 906096517
    0x3020703060615020f070e01120303090c123035010617060607060b21100506090f0628090c0906020304060f0c031407062012010b0a050f 60
    0x38103c10102d10b159010010041d000326030307401400f4410305203109007612050500c10401c0c9003601304d408005150083e4485004107420006080303480d030b1240808401c0e580f03802c004590000b00390600404101c400fa41015804090120155042c0c0c40000c1c1180c17a50b100070003500b070303118055514003060321114082c04481e0107401c079100030641c5052030203810040301a00082246402608000780c9542d13403001c03aaa01a807200002400c1c0804601168900f4521965101e0304141d11500d1a0901ca00058000c140c1640c0d45c014030490340e0301c1080c00402e200684204600f00001c0c400710b8114030300039860030050748000102140203500c1d215002256441584080326840c0d4880596001e07a9102c1d00034006088140011171505140c428020a030114880505003080702d03907480ca404040c441c0e10f410001845020442d03840302103d061050013403c111041c0f4240d041d4008070310101000700c805507803e0003c4000d50424981ca05055842a5800701814404218080010003047d100e2103016065503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 906099001 1250 906097751 906097769
    0x1104080a0302060702011808030c0c03091002010b090a020703080a1e0218030c0f0105030a0c020a08190e0f0d080c0a120206040b01060914040b010c05070b0a0930030207030606 77
    0x284c00c00e007501908403549100e20164440104401c4400301d8120310840f600a4407000d5125910070341001d50508601440c98016403010407040c06907109581500400f0001c58225201144c6842d02214003040303218401005000c903212100103014210294404c0100c8035024054400c00c2e40138600c200e080703a010440d94030100740d0030704e90340c4041e0030f040240070068401035034041441c2c0302035000605140001020703152010b4a400c07036400b80074424807041241c02d9100300b00c152a4401c8508514800750244040c200046030310f51008018a4503060400080401901e40412801c1c0358844020a078403003820181c540c4501007003603002990f4510080138038002507000e03124a043c11f1900f091003040c180c0c454030402c0070900061007192402140e05e090418125000250b52025100503600707801c0040c0050030a0140c032100040000c1e410004040c40c0d1150355988200c01d840e0b02028100b80b03000c009500c1810030707a82c4080c94160307180710038116281c0640101c1d0000e030b0b41ca0ba00c02c02a940c5030740120ba01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 906100251 1250 906099001 906099013
    0x1503050d0504171b19080703080408060601020c060a0c1112010621020f120c04060b0903071205030403111504031a0f070e09131b0303110a0c091104080a0302 69
    0x4140030f4008000c030784464030103800c1c0c0200038410700348204070042285200f5403465886071040d14101e800080140035140a176025142c5d2410800f0180e0424812641c80340140d2001036095032000c02c00351905030740100300d107003040c000000c1214108281e51702290947c402d01d4801400d90f40307907000303e16405410800850498248041f907039004c1d8081c400400e010070b1700400d000c0141d90364695405503810641b07812400c1d000c4c00d400319241038007402c000c98006282c172502140500e1940000d1040c0d6a0980850703201c0c2e0360300c00308115000800384002d84103410912060000541441c6031341009503004050301240920207803c074100d54095030084030541424282c00300300c18805c4001f960303c020000c1c0350410305c0c90100000f07030594000035200703413054003280001584620007800e0f07111800c2d0465600340c82908088001c0303040300180d0105401042c030449400020540c001840001e0503880300f030140c011480d00c64020050464030459992500f002c2c407002c1174030071041104180c00ca010750f0003891 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 906101501 1250 906100251 906100259
    0x140903010203040501060f0b040317090d230c0a0e0f101701050a181e0302120a0917031e131d1f0f0b07020a030b01081507030b090a1503050d0504 64
    0x10f03a007c5c0e0b503200038007040041c4800c002080501046046060440980355560855100041d0700540f4a03200100550141800400261200e455403e241c1c9500030803079403500c6407181001003001c1c0ba4422011660f0207400000d041d03240c0c0341704198000003107c0e082484c1e07035202c440b2040032100710701805841d07a43d07907001c11440d800c2c5809245200d18440c1850840521651100200c481c002410b03241f50403180c0050783d00b0540700b001503254036140c1c0c5241d41d440d201c9100c4010040c0e1424070640914456492543c800d082c8084200c807800c1a629030a540d00c0f1903c00304103200340c9c200840702140e00b0a034180015220000c0d404101400409400305e40d124901031001d07086002c0b010403030350001e00c0004410302c02840b20040001c00c0c0d0b900000743d140c44828902c00203020f1300d034036003000740341c1e240d19400000e02d4140002d01942a040e180050f5a903130f40c3e03600302203080390040300151354000f01410106985a00e2640710b00020081d4241c000c0c00151a61502850b084501060200107800014108 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 906102751 1250 906101501 906101519
    0x3030902042f0c1501060c1106040b070303020304020d06020f0a020f1203041e020a06030b040f09020604090207230102120a0912080601110d200a1203020c071701140105100f14090301020304050106 86
    0x101008e1801c441850800d0304200c049010342c000c1450050038144d000000c60259651a0380b0100034940c0000195503860b181c008110840c1c0007012000003520a190f60300008a40215401c4411042d00c4451802c5580307649a581a40c2c407609180361003c0c200012000268641d11541006041c2d15180810100d030000c1c1400308541030b10b901d80040c103240c010309500503a43c110803502110301501026842e60340078188405000c100300080d4034660007500010058583c1034000d05200015151110034954642a8000607603110020003011801062000e020701801014266001700042c50907041400307452200b2454440c01a0030f107004108080c0c0515400d07a80075400020008540b009040c100c0700c680c0c1c03100610030402071240c090640218ad940d00300c20301003050303d00a0a4011038024540040c100d024001e0030f40c9482031041c04081c80010035582400402c1c000710001c00c0d40c1d0084000310700032080f101c000e12412080841141049502d1050f5000d0000c0c40c0918004c00002405a10342554a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 906104001 1250 906102751 906102773
    0x50915060c1912050703081b090301090b06010e0603040f020112020c03370212070218100513020702180429010806090705011407020f04060303030902042f0c1501060c 73
    0x10a0070003504005c8103001991081c0361075040551035050754502c2c03906524050320f0f400741186880d015803a10100405002165690038001d000c2030b2201010f0682c2c10013842040e00c42110f014002c0c0040c0017060005511621051081500c0780c91300608250035140345900f941d0010107919851a0681110594644148407007500c2080c410176010440e030036401e02a488a08981480104080120310582951111555040c1b4810a403d0300d071001e107041d0348040401800ca0243c10300516550a20942014851088525031030f001004828070020350011030441c0c0074020821981c0f8070585200010742000458809400380181130400029818480094500300b002404d100300ea51002400304841d90304509601070010621000954030941800401c892011035468241c209213440030000600d130703050b072001d100315100300c0e420306c9403425200440c4000c0341031110b101c5c2d4094101c00c00c1c0b842c807480c0300028804140c0c4c00d0217030b03443d8411048002a84613800d0340b180000c034400c01840300401031141d042e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 906105251 1250 906104001 906104033
    0x5010e060a0b030721060905030d0515060304021905031009031103030105011b260715090c090f11030c07120809101e1b03060609050915060c19 63
    0x308014080b00b000029070384548a11603a0340c0001000d80320705652000d0451283d040d500182c05000344226494203503540d40c031190b46079290b98605404100490545070140004040c018401411a19641c00f00b002000c050180d9114208120300c0c0002c00c0e0320140402d1b100c80140c00b90000b4100543e0401510145a00c0c20300c0d2480c1c1c000300014000f41c0e070402c1d071454000040d0302024101c3e28203403a000702c204d105c00f4518656854000104175001d084c0e0001028030300d02c580c0e04100a03a0b014a00705003601d0002c400108410244502480b000d19503034040d220508038105c0218201010f0440d4204e03650042d45c08c034425560024265080c08000c8204a208000380c1c03a061145181200c2c26035160203011600e601c4442c0c039514a01d92901800c405c0101c0403040d06410403201c40302c1d03600162508008244c0e400828103010002800c00e0040200508a91001d4444040740d0349010446000c84820b80740e280d4001410701ca510074041082201c8008010a51146681040306045c0640803c0c00251 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 906106501 1250 906105251 906105271
    0x2040911040312110a0813030212010221090a08070f032703021c05010e060105010f02011a04020c0115090905010b0a24090b21070912080c07090905010e06 68
    0x842040060b120226410000c4000c0c03500b00000030310704c603207a81816507041c0060851100482e405c946418511700d0a81240e00c00c80b0030185080120406600780d00554841c40e8002030603911500f000c80020307409035031003041d4805451140d1016034680c00a60400103007540c0340142061144105500080d504074940344166507820a0554082c41045110150000a0240030011440808881c0942c907094085a20030000c0c44100c610319003060b56413500b442020300081405101800e2540103106510450f5000c02c2d181611000c0d240a000180d030003c1000c0495641e41c00d00c03561106110011440030b0700f0203030301c0404c8030001d0341009030a5800340880f151080440640030002c1d02c0203902c900101008007900f08240382d400050550f000b003401d40c003800c905200080c070385800c54080c54402002c15072601c074084c041d840d41340080302c22218500560001c84020301642000c58410005041290301075800c84861039210680b40041e02d810001c100d40d260f440e2007400d00e100b9000c5c0100c6a0220002d9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 906107751 1250 906106501 906106507
    0xf0306090c120403050d0209040e0615040515010c0c080d0207090e031204110d150b03061b03130516060e04050a09032109050102390304090e010b0a080102040911 71
    0x31040048071030050b1005040c8240043d041b0307440d00d03464040c1ca40d0300310000e20401946145260b0f80b03881e0070742125490503084004107050500c0c03905200f841c0c000c840310001126404050401502c200038807a02c25a0a0400500001a08e010400090000c0c1600e603024083c410b02e0f018180090364040940f003045900309000c40301c020100c109402c1d0703201c0d0300611960910084400890340004028a0190200720003540e090405801b5800200302e4001c1581280d455070f40b04504001c844004c190f261800042c02c00200c1c3c60841c0000043c1100b41c010001d8a050014000b810008806107030700000100b40010445085840c00d44122030388188154424400500c3c07558004080801400c5044a41202d1140803540802d040e80905801d0340c1c844c000715510034240703d0361450090b140305100e000300348110440b0f40c2c01c03100601403400040c507500114100f9080848950107040458940750241d9aa4201020a503036402d403000c00610304030740016a00c90a00d01d00300203a5001507a8848210820 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 906109001 1250 906107751 906107767
    0x9060203160206120a150e090604022715011707020a140114191107050c060d0b10030e070906060207050d03032405030c0d030f0315050301020f0306090c 67
    0x100444000504100c10300d4110003040c030000300140034484e5045600319003070040001d058a158000c0e200114400041d00c1d401ea540c1640030052982100c04d80c6036a0040000b140040c2042032541c449000d007508001c041102841d410180000216012030300d1107154940d8a0711540c100c8880905a030b81070b80b014041e4a00200003035034030001100021300f400b80c0c9030801000ca02c800e40c011010840f0010101e40743e0704028242c3c03000503040c01c0450011303524040246005014450031144400c6c1e2040141c40342d0ba000c070b400c2143e650011008100400e88880761505255211040384540780041e071030000310b170080b6149580c54400716401600721a890680140241600010000200e45003107070a507501601e20700d021809002c008590b02c8024000c05210004171101f130080c0b000f0741304164122030000310301c00304004420051680c00380101d2900144458020b11a13000540f80d000389050b0103402c1ca0b59040400c1c02ca030b00c407484d882d014030b0021052204603c4c00100158105d220800102e041c0911 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 906110251 1250 906109001 906109003
    0x80f150d0b040501020408030c0a0204060f050306041106120a020a02060906010612020d240306050a02030c04170c03060709031a100b0c0a0c0e0a0f0608030d020c010e0a21090602 78
    0x84035024203250010400101004402d4040742c0140070a401a00d40700da81b5031401319a24500e48804074421800c15002055002c00b448040301101c0e8000c0081c851900ca80d16052102c3e440c1480050300020708000b0482d40d11000c126160241480745070040e643c4409040090407d0400b51160342180c014500401a856106000311000701a590300180c2d121076413485203004006a14000300b80007d0a0341c80c103141080d24039440e00301e0b0b00500080c000c0341d440c2c1021400700c0c442121314074802c0b0020f1000388100c10362800f221801103180c3c000c6500102100c00001d260402c00c49540d000a15003c0c400c1c800c10112818000d8214102075686402d170404414400c400040c0b07002d500c01405000c594810b6a43d000c0050100c1c10b40c10011914020f80c45860806ca07568084402c481d005003811804138061510b1f100380300448403240040c605054031895250003a5100039202a507a44d200c2420f2001d0380d030305005d284a268400c4400e8510790441010301034001200a04180c2404044c500c00c00010b50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 906111501 1250 906110251 906110269
    0xf15090a020f0c150708090102030108100c02030706111e180423070c03030507021c050c0304091d0c01140a140412140708190b0705090907080f15 64
    0x4404034000d80c40300410032003a0b00d1800f45500700d2400b407060001c1c000c50809003c4406000d14115030b501041c0d5900d07480b50a090344400c3c4146486a40002119100072046901a503c1d03122b061055a160100e40d0300c03a8020313203485054001c075244002440c000b203d6010030341881e200c1c4514000a0a024280c90034961041d0078106603070040d5107d480d100a10142080a024513480030070003902c0c141040b00e801000c414103950214042440c02020400d050300000e000c03444030fa4140410601e04601c46400c950340d4020899102a5200c240008101d020843c0207030050940c44a80c6401c0543d00040d179140b0b000401c0700b0060600c00844103104c0314042d131008490200c020b50910011100b00341440620b0303031089500c00880c880504500a04101d050b41602d03d070104503500f200d44048c1c80f110400c0d103071102c03035031a04003440003000c0210004040000240c2d00506030708120f4107003001358000c20001d240403501c4200041c000030401203812004600a13402080440c3c03d4280030200d0800319032210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 906112751 1250 906111501 906111511
    0x40206032205061e01030f022211190302030402011e09090903030c0f0206060d15200c01050708010f210629100207060f050c12030f1509 60
    0x480008005515980141d0700600ca911501911020310322007420a030351a1a0191403e403040110718030382d600b10001041c00141640d0300403000d00c3c0070307018550030030816041c1c0448459090103909140111095603100d5002c20310f0501e0070702c41d1340704481e03204210042c60f410350031401d01d40305109120141c1d9214000b0010151503100003d92000c0d00102600d0300700c0746501c08030406081c5444002015450382080700151181c1c0c40da8911700c41c1120040e40c40344412500c040d0410b44a118900c00724204503800041c82540800c0014440b032250f10078075089001c4003404514400c00600d0812002d400d02c5959405180ca1914101550400201c2201c40140f4070500304904100982c4c100703130680c12503100c100f1960000703040020380035004d142c0502c07000140c488a0039080b10760380c6141034100044c450881041560117400010f081c120150703010400000080c0070010103024a0001800401c02c00a43d10100344445449140503070a810590000506660504007001d0414010781c4840c2c4001d42c020b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 906114001 1250 906112751 906112759
    0xe10090906290f0903060a14060d080901300203160f1e1206030b2e030209070507060606120e01020c0736020705010506010207032d080a02100605040606080402 70
    0x1031041c0142d101ca6074052040191742c540a52010710503110099444100c0b0601d000c0d00c00341c41681c03240c0c00c00c02c5181e240c0c10040c190b02000c10418205610460146c120300b100036044600300072180b010520504005806102c1c0c1580c0041481201e44038403a2500311000c5a14204020b000a604c0051050815104074850045250a2001410302640d0002040140c0715000c01074075a49003045481400282c0d9000ea900260742400640c0b82c0c5491002000b41402c0f800001c0c0407451079090282a0354014103010800600740904800140513000d60760007480c0c0b0740e07105d680b1049000301c080b08440320408042800c0c0c0c41001036032522580854080d003210020000400d400b8940d85230400381882030a00000d003069480c0c043e860b0300040e54090168680201e0007000541c1c2e40700016662903000303000240c00314070801e01034580203050b101c121000082c17030030724600104103996600242d500300980080250704000070000c2e218502e449150b00801044030144041842c0c080082d0407100301400103809 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 906115107 1106 906114001 906114007
    0x23010906051e030601110f0303041b030f110103231b0304050a0f060b04020714120315040515032e020901090b07030e1009090629 57
    0x403900151510a10b0035451402d42051904010074440c100400c90390301100c4400c0502891010140310802107441e07050a1402003120f0302c480b08020506e4a0480c800c00100c2c954019003c0328503005421580c65502150048010744404401760024055500201640340f000103001072242805005024114900038440c000030b110940d0050301aa000ca094100860074254030402018840c0c440001d00c0200301000c00c00b80c1e0030240b41961560409918a04002e80c1840204200070600600510350b01e0440c404564807850804818022070303032100010f4400c02d1007482030b0400c640040c01c03241841285020340d01404d2451491841c918021155028881154001c1c0c0307148410584031501b02500b0000300001682024005404200b03c2c1c3c1c1280d0860f80b11916480440001941c0d80e00d441410410f00a0950340c2d180d20100000d4030740c0d00c80409100c0d4901028200314106550596 = true := by decide +kernel

theorem cover : BRFrame.Cov 905935251 906115107 := by
  have h0 := BRFrame.cov_init 905935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 905935251 ≤ n) (h2 : n < 906115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
