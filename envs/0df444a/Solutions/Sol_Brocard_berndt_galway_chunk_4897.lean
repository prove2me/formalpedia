-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4897
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:05:27.565532+00:00
-- url     : https://prove2.me/submissions/dc28484b-75c4-43e6-9a1d-f33cc40b130f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 880575539 ≤ n < 880755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 880576789 1250 880575539 880575569
    0x41506020606040b0a05060708122202010e030a0c06020c010e0d15200703050d1a01020c0111030c0a06020a090e010609120c080109050114010b0708030c1321020109 72
    0x20103507a44000602e00743c070481e1200c05841080e204e1204e003c0040901519640e101e20b454030302011140c00c00d901d8000d0604040c8005503501c0304039590300506100441107821b003440e031390f00111103550002c0d00b11034240c421841d0355400a45041c10351401050143d0140c20808850b600060106112280303080c800e250300109a0702144000104141c1916071910000e100c071022035003000603101030b602140c60b9240c08190300f0107042d0007400421030a404140100a145819001a005405617401e0113005a10256403c805940035500b40301d0601a0141201e0170314000f2000a49865030b039003000c5070240d801041c20b40020b42c0105020014240a6080001c20341c1018001000d1542038030858880047d540000c0080c012180c4000c0050b10b14040240600805414280e018100011904850201c0d80c000091490254000d03544581d91043d041480d60700c4a02100c81d86400c1525031f5000d1868503c00011094801d41c40403032032401c00003c040c60200340e4000508462142c0c1d00c080401c0c21592 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 880578039 1250 880576789 880576799
    0x70501020f061306090b0a0b210303040609030315270219120609091110020d120b030f0715031b1403070c0204110706060b0a05092206060e0415 63
    0x1282280e80522014541c1d00110360f0fa06100000e0900210003400540c040824400d030070030a600b01401868044c0c80e500c8010350541403c040707403d048008005c007030300140049000542e0907040003441a0081ca4041000d04000e001c120750105a944109000264540384942051010b0044040402014811818000b0300c94800111600c0c03101c202c0308214021004040c0c0b00402d0740031102911240d402005649020301c2c0c440b107407070183c6850505c17810701f000c3d001a92078400940d249020350945e0303400d030f98124076503401800f40400b00900c2c0d41c14001d04e030192003d41004c1011000030090f0036641508419210070107000c40303140c04001104101d0303200d4801110340c2c2000c83d003000307000310007001941c13036076400380c221444806400000e500c81d00301003402d00d4105400740a012035034090300c0100b0206a6950b0041c40501c20300b00c8003000b041090249002030720f07100149420360b800c80c00382c42110818101204044a480350440c101040941c4603802d41c1c1d042c00c0c03082c502c050150080b200351460800c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 880579289 1250 880578039 880578043
    0xb0f06030a2303160201031d07060c06020403051b0a06021c05030a0239150c091201050c250b0115020c031203070e010c0b010b03150d030c020102070501020f 69
    0x4901030805401036140805440010081400c0c5035100d1043d2a00c5082c81c0034141015031001000782e0000b4181813540b40ea64040e08030380ba00d0758261f903000b0b0100c18501003040d581800050410b462041d820b010010204100344070070b0f14003082800703420502c01421003c1100702802034100c3c900710340c00010800080c1a040842a4a0074180d04000c1c1d00c80c0c0d42d0b10f5032007010384100c100302e402150348441d020b481c019605600f0001040c0003030150b04c0b80c84014100954800e15081408681e450340004200d181b84c403240100f982110182041001d9407403841c00034251341c0c090701e03100f1911400059004c3c141c200741405a401e400f00070015854449140c5402419610602441a4054026014030101030080110003400d190103420348001c500e01707043d42920f0750011941140070030813008005186600ca0500c802e003a503401a180c01d044e90800309144402d4100412001e2125482d1020407482d558040b028454036200c1e55600e10807000e6403000a00701101796000340e0656200003501d009000300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 880580539 1250 880579289 880579303
    0x20108010e0c07080f0c2b0201150306090501020f070305090f0418060c11070e010e06030a030f030506010c02211e100b0303040e100e13211106010b070b0f0603 70
    0x2185000d80c403407030030100705c03000c500c40c0c0764400d14588510400c068480040303c0b0401c808500350740b08003c810003c55026801c0e194481807000b001d0801c1002440002d1175503000101d0103000744001400c0076114020f6141507441184290049000401c6502180c5480c050030343d1f035404183c40c14044550040c0128401c4d940842004060940350f001d000c014601c24440300410514203011500c15030b90368030041074403c00a01071a001320008000140c4103003000554481001e03030641c1c1e50001d8070034041044000702400b03030400d170420100d03000b4800580c0d04e124180405125000b0409542c00c0703424041480c1c11500f584100a02e51203049107240c0a20100300041e451220744000f00f8421101c0000034114030554100000d15840d50f0144081d0418071007138101900c105003410f81d0a82c480c40f081d004500c842c02c82c014560990022058000400f00b07890440344a4a0304180c0b191508200f001400c004098100d0881c1800c0415441e0901c41c0f0b180300c580c1c11010500314001c190030100d0101c2d132a07041e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 880581789 1250 880580539 880580543
    0xe0609010e030109020901150306081c0810080703200d021e04180309080d020604050a0602090637170406050606160b04141605090601021e010504020108010e0c07 71
    0x300001c035a480c02e400418441d54002c00401d0395684502c60f5082d00080b2100350340000e4a840350106a2440028100c0e5400389980701b1010803103080c2d60111a901c03002803c05908140e4060005196481041018091445401076000603006203070320019800824891a1198025905900c0540c4030040060002c03c000c01000580e00071100c0030801030215188481c02a04021602809240d40110800c2c1519110310a40d00c0c000010780c000c9907101010360b4043c0c02030f0040262003001130841d80c0103140450340a0b100c05c2c1480d280c900c180300e44c89080108410560101c8815451002b131001003a01c3e9081d0b01d003000e82901002485010488000030300c002c1c100e541e01d40c041001d0765030f00c205030348600070300840c15040101c1030300c0c000e5540042602d08407040c01d158040602c9180021989250001d40002c1e214400341c80d000030001c51030320103000641940160403404480f030046440e004502e0341d001002003000c0c1030510004049500c1680221180c800302424000411402002c850f42e242d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 880583039 1250 880581789 880581797
    0x402370809150c13030c09051f061b060e16060f050403081606061a07050c04050405030d090816200607050304030807062c1006080c0d0c092a0e060901 66
    0x45442d1002c004e10721596000500742c0d420100c000600d408650b00301e144200040d4140c131a11248070103000e030210209000c0e00780842c9610341c1c151860f40c0500c00a007011405070402148080301440f20a003081c0d00c1440000d641502d42d0b0062000c981c000086200f14034662405500c4e19240d5180d0030380601550004609007105c5104100074000e4035040540640110070b4010f900d452031000200741548010011119800b0f0303613402c0e0499140c50300c1217034800d81c0c21270091440c06002810810061540c2070701124078030410300403404868131030300a280540d84034803401c60751040707600055586647e21503019489800200318407000240003000303840469501c283e01585440350351030505c000d40034901401040c1000c40c040d031603541c603004031040040d10b4403005441c07403103d02200c100103940b841c0c01000c401d42d00107044190213003440401d040c5514003e60103071a4850b114811201900c84031072503200ca030281e41c400b0f030380d01c0c2e10513003072244006080d800c0c0368881d110f048c1c012030254040c5541a038140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 880584289 1250 880583039 880583047
    0x3060c0f0706020f04150e04151e180902010311040302211c050901080a090804180e060a05040312140a09020f0301140a060b040f03020402370809150c 66
    0xc240e805880d4079102e0301060607155a20707404a00d00302c0c2101b1405e9800100f40400e09502e0f403c1505c41c1d01d1003108088280110581004008419400b00491005480c1140f241c00610f050742030541d0308442488440c00f1490740c0c200e0000505854854192001400c001c01042005a580c101543c142c5c0c1207040303c8445000c43d00030614140031060f4411881094070b07010103000140d200c0024241014241c0b241d2040da1500800b0201304c403201d160013451264100001c1c0204046442864040e100c00d19001c140f40017002001070a00105a6201c0d01d03603920303a030920007015042a11541c0d46141c0d100200025050464108041c29020f011210a1541c8400d08030564690340c50710404140044c0081c00310b000901341c01c80c0159030407560160401d14218002c103800b4564400c4504480104214804950450302080000e41c804030a0842000100760081218074140d00308040400100d101c00710324051541002d03209520042008a5581205103040030042031a440d02d6003216030740003c681c40d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 880585539 1250 880584289 880584293
    0x706020102160f0c17010207060507050711060903030f0408070303020607080c031b09032505120318120a030806010e2b050f0f06160507050a0f05100203070c02030c03060c0f07 77
    0x903440f003900504100180200c500d014171105400070210244986410880c42e03981c03801c119054060580020424102c100224009142c950040e040608000701524501015240303c40d00e01d501552154a098118460400500d5011703c0a550701c258181400d9015213040c08400401e07120041c43e44035140c40440d100020300725207200361803460320080c040350340011103d00c151003500700d0f52011b40e01e018008a0003080c80e0800c4028030741a840410029810141a00640ca0b42d07901e41005254028054003182c1541003810803915800c00d000351110710543c10084001810441c0c0407030802d00a6030081542c15000d85603045008008588140c10000c0d0010392400034102802c001e500141d52060349141091030502088890041c90703211204c00000b00302013000c0c6e4035030003101c0d0041e0460b040440c2c101c1c04942000688502d580c03049041c2c64800180c070001c1e0049804c246d580a0011307104e000c60a0460404002124112608400030241071030809205000d030f200e55503039044c00d02404178584003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 880586789 1250 880585539 880585553
    0x50a090504111215010b04151142010b1206221d060c03191104060f03051503030d0e011514010801140d02040b0619110706020102160f 59
    0x81d1a02c0000e1411404001800c9141d0b0381e845420001d40c00342d0b51140c00051184c004400b21f400700c070b03034111145120340000541aa0300005802c209e120501070340060b03203d14500401c90201d81194003280711617401a0444c4040e140130030190a41c00c0032201c80044c42034400302c0d0140c3d119103226052800c12a903030080403a0170b01041014401380c001440c1c4030750502c0c0320306812042000d020000c40c0024840c01e580791a540c4c0c0c0058440c0448200304101052a06042034500f10f104c2c540c041001c40d07418505020144c0943c004d0b8803000000300c800040780311165041c0103054015800c0200c201d5600b4203000040d4a0b44604554030301b03d0b960703403d451a4002401e42041a101040e1211841c0d481d0340c03038042d88a148102c24241e030015004100100b5544211008061241005071442c5d00303440240e4244130007055171450481d44888140126040e0400303480054012014030f640d20006c0b448030070000c03481c02500d500f041007564010310080c500303000c0100a06e1016600026414034010f50390500030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 880588039 1250 880586789 880586813
    0x3070c12060f1505040b030105040804090902031c0203030a0509030c070b090f0a0b04050436060603062a02030703120b0409051903021b0306070305070504051309060c0801050a090504 80
    0x1842c0755081c8184060f80d40035000c1c0b140c00700d40302550103000409041e01010f00300c0e001124010400c0c0403d2005021400442d40301d01040342c8050200ca50741c6120700c5142c00e8010100c02c0180040c1c1c000020080a5032886c0503d581200070000114100300805800316241c00003805150b94020b000300c8c0c54109561000482202e1950180c0159680c94555a84440c594054012180074508100d25400c00518980e90200702c4544400d100c2c5a4080407400c0f40200c0d082450152442c0e502c8420100200300c95105c1c40031017980c032000e40032940c401141d814012141a06000342176410a100701300c0861b401080c541543c0e84414400541e1864a8000030010803c098000e480c80c480d1144103411075401e031421220300750103502181c91241040445089840758001c149405030002070204050178000c0e00400d421241c0740c10310504003034803500443d40405400442108440c0c942c500182400340314400e04d01e200c641454515030640c10403001c01c803100f110740b14540040c1d54600008080c01540c4284c9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 880589289 1250 880588039 880588061
    0x110108131412040909060c08010503030304060902041b020604050d02060912090301150803070624030305070204060e090a03081503031e070f030c021c0312150b0703050408060903070c1206 82
    0x2c9038445071203200b814014108104d0855965140508000d095030140c0030503812143d0007002580345995964440c001780c44c08000890704244c40306c060910000005400595500c250b5008296501c0c00d418040e240c88941141e04043d900200c0034000c050341b002c1440e07181f0184c0011143c0d591100840468018011819480c0e900c02002c080425119008802096480e0041100380094a01c6000345554607014683c0304440d443c1c04d600401c00240103102611109000600c0022510396032a025125918101e94000198001803c2c0d10300300b541084500ba001a805224441c0f01c610f07a078003103030341c80c466100304d050540e072400c0d09400a02a0001252100c071752016102041c2c002d01d1402909484029030300b01e02c1043e070500d02600d817a0031001071002854156451441841209030108010700d00d131001096a001b8180001c0b400c41c2d0980001c0000034031176036690b5540c80c51300c001241010005001d84c9038076001085004085003040007140103650b0100201160f0044608d00200240002864 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 880590539 1250 880589289 880589323
    0xb091503030f280302090d0b04031806030605011803050c240c0c0f030102160b0c1e0a030e0615040203070302120711070815130501060e10031101081314 67
    0x4000d0b03c0007800410003800c2c0110b10000c092242144040d4140e0080c1c0a04e00c0d00014030b948403002007010007110603002401390802c02d03c02200201101c82412035500320388042615540104400d50384a425030404100207002c14000f0780c1550784503074a8562561056100d0220071803101ca140940140c041802555403007415614041d003841d480e00c0d20000250f180c070910301e00c1101011810180201d031a140301003034001c4c40301480b5654003030b407904000c1c0402884080030701502c204d0304103103881d008044980c681d446443e019080802010355030309029101c0c90790404000e01c2828201d00c0d4505800800031100543c0720340c0d079903504900038080c50941c06208081007003403021003034101401d200408084002d441d10217440c1c0c184181d950400840f200c0c0d480101da000a07489007010311041a0441c032610012030705580d140210310a080050782d00bd0364010050b002042045030740c200075203426000382800310642c6401842492a82112500900066030304014005a40c0c070602107903d0307852002130 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 880591789 1250 880590539 880590547
    0x305120114090c04081f2004030c08122506090812010b031302011b0b01030c09050a0b15030a0b10030c020c0f1f03060906170d030b091503030f 63
    0x9940c0d41c01e89807403500c41c0c0c025109200814030240214003120165468840144000024400480300c0c04101220b121340c07007941d8018640346a00f4004046c0d80440101c405a501c1e5030030760030000c16400d13056002c9412540100380150446503a2810b4508080a800206d0900c1c0900c2c008003105500c071241c0100307040d242007010002c015040002c1c1c030410b4181d181220642c1e1325020003100b90320095031015003011214440000540c4909481d82207580700307102c0300440170407560320a01400d10a17001181d220344050b5090007461802e119050b8011040c01050003000308541c0411a07601c1142c100155120300040010184078860b04840300140c0d01501303800140d0b00640d0020000c0c150584140014002e42c100154107280c600f15614404600800088085d10704e6207132110716092981c0440281501e84c03a000070f901c6043e106090003040103c2102e07a007420103007100c41c00d0561803c018424907240001d030508a860b00c541d6240c0c444800c600c3e43e0715003001b080019155000303a010341942d1300302c001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 880593039 1250 880591789 880591799
    0x120c0501060e01060e03060103051903140408061603050c0414242d0a0302130f08030a09090c090306050a090227070c051c14121b130902030403051201 66
    0x40c000340c104c0701107a0310790268107100c0c0d0405480c2c1c4030a00c009002584400034510584c0e9002003480110b500ca0b0900030312070001130607038500742c2d045980000e0b159084402084140031412440710160740417803400300400e2400d0400c1c1c0400b8001c500030030034422900c0d0188411900d030384101c00218181c4030312314003414441c2049454a0790011006042c6030400d2a000300c002034080c00760b6511081350105181c20080381c1541100250809203030b01c11318510444001441a010200c000040c100b000c0c051a9200078807103010f4203050460f0301025200b4608000c410081c3c0d44000c1001c01c1c2c0b0f41c03200001c0303065200c15000c036000e0281410041c1d8815a004801d05400f00f0400f03000d10000840300681401e41d6406030252032604444001901e1508054000607401130000100e40030308059090810600c40308039a500402d0b001a40b00301c000c200141d051111075500d40e0744035041801c08620962415655103a500c3e00340540d4461b80b0740c03080d0040040740c01c00d03000d207068950520149852a03295a518 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 880594289 1250 880593039 880593059
    0xe0604180c180c0e040515090c09151213080c01020d020301080609060933070c03030b0402030702031c141f060206040c0e100b0c0724020604120c050106 67
    0x900c1142c401620b40050842c03419258000d032070302074003d5115000d040d1500b00c1440007402c8014500071683d245041100601c0e0780c0c850f8018042d0b0ba926410303540303c1441c2024072507452901d980e04007001c0d505025507510f04210402460740b09400084095442045180c0007095001f80341080c03149500209895102d09a150301841c101c46a07030381242c0141e154010000c7d12a2400d59100200750001481601310360b1002c480b82d07080309041d54290483c58050b0307204a034840b001703030303044000664446420000d0646c5400382c0c42c65403a08031030451a60800c42006540c0e44190b640f07507a58825000c20003408174680c1c0e0302c042480c03200326210441918144510314901d91141d8494070348200d12030b0740800c3d07540c40050050f10440d40b0004c481d0000e41416405800d03180d0050198203014030400d0302051541825001d40a0503106100802c203003030501e0705215260000d2420f200918651170408c00703015074005051500540c10031783c1d4404000008008a030385040359032014240790b0801900003028030038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 880595539 1250 880594289 880594313
    0x131e0512160302010609090f0314040f0306022a19060e03031008120f040506030604200307030b01021204090506010516050d0e010e0f09090a1520130e060418 69
    0xc0b0754020001c00342c6900802c3e04441c200c11014050380701c1c181039a0002030040b0321482d0000159580307942083c1e6119103500b00c06855800480d035041e000f0590317a1214403469280408a405d81d807103401c0300d142074500313a640d03840c2900c41c079510301e200b1f01100d00038030103182d01200100e14441d007503d03038900d4007032201e40c1200d00034030400e290b41c80f0b4000541c0c03c40a5400640b02c8401000c0720041c40c007458030081094980014110765030192f55500807001500018440c0710680280d0303400c00c2e84a10381072401800700d50300418014159040071a0020b10b115030241260203640389141c000506896039030040303519000e03080700b207100309281c1c070400002d1100018151418000c541d452003400079482004440d041c03042c01d00e19800031540d0040110b0342c60b00c04021a4000156401c45207500d0094036240740d140005180141880d030340c0c04071000e1312480c42d1600f11034064240354242c6044900850103840c83c00074411101d2182c07249001c10781a6465801c045030307010304c14643c0030a11f0701d6410140c1004170 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 880596789 1250 880595539 880595543
    0xa09170c1002060c070620070f061104181d0610080706030606051801030209150903060105090906040311150a0c020c03010b010f1b0503030103140105131e051216 71
    0x41e104401001c184000354042c4294508a0514240500b0385c1e02c200160100300300e010440c03030305078140c0300b110007148020f042200e00a40c640d09545090342060401c4440280705c1c0c00c182c030710810040c451050768428440c07101e15010800191050038904034a0350020050031605580210010300c840c403c801d58200c0c0c25540c8403025a2138003a5200015130859615100d040007040d400c1c030406a6040d0704642505060300103040161811182d10006034140c00849440d090300c01d000706009145060400810380545001d0f5a903800c0740c10084640b41d610316000f00020200003810700c1445404405210550508243d64990f0056050440d02c010141c84c29480901c0113100d03508c480c114a2805000340350500006841e0700c400c554480340201d1303e2a4104511054030b40f0345214000010b201000114021401a40c01800310341c08000090b0940d0700240455000c1c184070036030344010560264000d000c4841c2c50003000c01c05541d625220b8188100b044c203641e002c01d00400c500310510080051400f00038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 880598039 1250 880596789 880596799
    0x608071107030b0103080d06090617070e130b070302090411090916050316030e0307050c09070315061b0b24010207030b0c03060105070b09010f06080309090c0a09170c 73
    0x1000a000310340c1d00c00d007a200203031940d0542c400410204000320010310100c4500d000100c5e00c291101024016140541d100d50300000044800404083c1c05003c80c9010b4020000f1710384440c10071500101c8240c1c0f4500010306008449800320b01d10301c1c040d40c121014014081e10601c095041101820500c0e0004c595241c0140b10083c0050004002841c0604000340952a81825601c80340c02600404c0c11803102c5009255480350704034802013040000d0001d041c49040144150b400360780602045503400340604041c90b0501c010107500b004015200700c1900c01503c0c3c590340744800e4104c0f002d10202c2940000d00502458018840d40c1c02100740c440c441c1e140e03a2a0165103070030502004a0b61110305120141010300d481c4046001c144070040256007114051501070708291454680100020042d16141460303992000d4481c86208175004000040a03a00055414203c41c007001c9404590020881d41c4041c00c0000e401c4c010030700501002d0054a092180616030b000c0c00700e091960341c22500b454620130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 880599289 1250 880598039 880598057
    0x1b031202030717090a0812030a1d0304090f0605090a0c02060c09010827100c080a0240061706120d0c03120e0a030e01031a060d15060807 60
    0x814000011203801d260b125451001d8015032012141c0144c0000c80031541c008210f14000881c040100503402e000c400c10303032005540f81084401c40c1c003203a4900d491f9984906800585400130000801a102122240100800c170150f00c0c1d2451402010140c121a030311285990502c80080303041d900003070303510700941c084502545500c501840c150081d400e40500103540750340000c0e14000304d14803c01944062110308181030081e540072170300344411a071a118100b59101e4000f40c041340d1051100c0d811005280d002c503c2d0407000300c03a0144d4400c4851003c0b40800700d0422201000f00c4900d5100020078503640304405903615917100404942e54007a21204035444c00c00030644500e800e2040c80d0f56040200e00600c60385080550690300403985040c203806100102d0f40c54656100c0a0161384211040030340a040ca462741840c0203041540361221003810149090398880b0701440407010388410440031950b45884141101104020b4034500c240120302801da6400080d0389500080064000e03601c0392156082 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 880600539 1250 880599289 880599323
    0x3060504021305150d02071514060612180102040f05011214010620070603230103050714060405030111030601140306130b030c0a15091403031e071b03 66
    0x240d02900e10300580e100d8140c60100502d10b440c800b00e0400004c0d1400f2107041082c0281140c0c00c0360803080d8180d40c01c1d601c58103040096402031113210100c044049484a69041000224006005544000000003052004554000c4031a5907203800300c03041c800203642d956142c0b0340c04045002030344070f0180803989000311044518194015442004015001401e45a20f00402105c56008a046600c10900c1001c031420346100e00340480800780040b503c01186021807000007030300c00040e0b0352040015803152001440042e00c0800c1510441c0d203c03282071410b1501030030000301035106580c80150b1562130031343c60700504a0043d02962040c44244c80e103412404e95000030841c2c61204607030155118090300710750403030720303c10354001510001d025007211040704208c4045040ea0150b074100ca100404003200750000150300021080290400b10802a070180c1494046642c3c0c0c0a402564440c407020b00321888c000d8242c0e0826500c0040d0002c0301d81080c2c001600c80c1c0481002d10740829114240b0061002c44 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 880601789 1250 880600539 880600541
    0x30f070b18010207120201050f0d06080102070209330118260d0e09071b0302011a0118120201180603050121081812101a0102070f1206060b1903060504 66
    0xc1710280340700c1260030051507004503029408121756542419090000807418030135441882d0240401200060740c415846c010802640c070300400c1c00100030384c1c031102c1c00b0225901c01140c1e03000019000742a40b11280e501e0060701d680c00492403483c07842e000c0c9940001c00b0042030a081c2c805681c90820b00b00d0700e241c0d0103044ca031120301c4070320160301142e0120f80010180c00c08070032039940a0b0040c6012884025030461082c0408100282940183c0d15079030040740d40c1c1111070510303040040908103000002d8903900400c0040e90340d44100300c03080c0500040300082d64001d68191b203d0021420301103095075201c02001c2c3c01081e00317001e041040808061408402c4100c6807908035000d40110b032103410811900403000c41a40a8000d00350012840c44401001900c10030100c0481c207018500441e4220150581060f9158a00d00c250304640c81100c1c20401e400b42d81000405441d07000307651608422050401c031010b401103030704c410511880000c64500d07664502c4040130741115030f40d8050081d80ea43c1e4003004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 880603039 1250 880601789 880601803
    0x30d0227010f0e0f130b03010540060203040b0403090e041a19050a1a03030403030f0f020c090705031905100b130b070303050414061e0402030f070b180102 68
    0x15000c07615812003101c0c42c501074400c001500300300512802c80e400c41c65002c01d0010b03031240d09450403140c40e00405e03001172800780030f007592200d240c060403009016008c0c52132004060122900c144207070700140c2c10943c2e000c0309030081c00c210380000c410b43d901e060500e00103051020856080c2d0015030052000316200410808150045030400491806000601b004040700380c1c02074860b001105965580140c4070050f400707181d200d0074283c3c0d4009072950940d100e264035902800001e500c80c0d003003008280300217604081c0305003400300075180c1001074045001080c0d04c0d14999041c59503101d08490100700205900c07900546c882e60b07c9441090566840c001000c1c10b81d6010388600b100e1741031800052040c0145100075010048880d55101007003a030390b13035182d1020340c4038900030743c000ba44440402090125002c072940c414001100240503074179019100c016010164449450302e031244401080540d90b0801000c84820060002e0307800c20350b0790b520707400c0203903120424144510f40190003000c01980042010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 880604289 1250 880603039 880603117
    0xf04030203040509150310020405010f170f0c4830040f090e0601030f0f060f0e010c0207050103180f140a03020705040f0b130506040e030d02 62
    0x840c2003d04000400c007100c6401014406010144402d00680361750420854640012100c40140d80e40c0c1048001007000001c1c400c00d4091001d0f1050006144290711921548504034810544d800d403594090101d4502c507400061202400407911402055082407124402c40e8000d0038180384003100c022100540c130300403074070000c1ca500b102a085c032940300580105520b0a507030140c024505d04407050a80c0c0c0680150f040814800e0741300b603050003040c0852190b0424800c0020040c10907600d15500c402c9801e4040320000d00d6080094604400c001d856009006103121075241801a21000030103203009041200c20900180300f441c20010f0154000c3c4200d6625812054000c0320500950b110045541c1003c04d049441074001000502c100c001400499a2144280d014110300703440c21b0108411340342c80a03280440c0358604201002103a980604010909000704404106641c4d01000500200b5104000f1105d07404002118019404143d00614403143d24a130302000c819043e2114a40340c0200d0b1100b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 880605539 1250 880604289 880604293
    0x30a060e090a0b090c03010905010b0909010e0d12020403020901060c0201031a030d2f030c0d090b040909030903051002090414060102060601112401060201241509030c0b120f040302 79
    0x42c84010542c0080c900d0390012031501100c03201304000c0042821513280340e85c00d0f280351f5560032260585207488240550003400b0325000f8800c003000c10a1300c945554400c0700042c140603901102414502d030740e4040c0d038015500206000170560751203102900340c01c8902c0d0224002454140b9014428407640070346101007030054010306124500700021f440482c00279401210107a903c0d60ba914244e07215a40045c0d0540b4107070b020315200e102841c40b8900c0c083c0d00c1b8040c04140104580144295080441a00c0443e500441c0100703003070800d4203082c0d80442e01504040c2840c015002e80c0054a64143c00802d01d90405032010040755080c04983c2c4000101980d40d507005030000000b10f501c82d03101d0741c88464886100300540701d8490000e01c20740c414140c0b07104e44c40e01c50301c0b91000421101d81c0a2084c41340007a600d01c7d40c0414030400c0c1296010100b014003c0d19a100c401c0c80c40b159607140304024401c041c40e80514015410790311610300d12134a8000385400002c400ca0240000c0506e01c4c480c90701c0380201e80c1a00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 880606789 1250 880605539 880605553
    0x204090b09010f111c02090303040308040501120605030a15290a1409180f030a17010618030611250b06010c1707020d0618050c100c060506030a120302030a060e09 71
    0x722022105c92421a061a13140d0240040c112954050000b03000843c85811520b981e42d181c00c0000d00850504030740b580c0400c1c0740410410140d100412194403141d84040d81090815a0307407950070050440500d50062072030802c0141c0080ea0703c48141c0f0703681d10421070304c1d200e00c0b966650920020f401c680d0610303a0055405008110302c070000001040d001c0c48a0360a845440546011051843d0465591403000840440e80010103c07580e080040c0500024500104011050101c640e0740c41b2503440000e0000e50703140d819010f0b05d07034080190340110402c940c0369900c128484001d946404003d02c8207235039180d0f001010400390360042148107130701e60780044100d4214046c005618083e42100405903045104083c0c0308000458902c950b40c60000c000c542c4010225690802e1490b10a00010050107034010204240301e90390400000c2500583c030100204042e540e40700428100b41c6075501c018281d2070601400d400007034140d0041c601c01c901040703040040755624490328816240c01c0e9441c000725040b280c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 880608039 1250 880606789 880606807
    0x9610303140903010908030f06040501090b06071713060210062907030e0d0305031006111518070b03041202030306010c060b19180b0303250f0204090b09010f11 70
    0x762641c880b00400014aa13401038403001540d030b000321400301d10160300a04100583c5081e1180b14007402c00f82404010345214680401c0d01031054002c00307030502e50407404002900030720200b2220b0421040a004001540c0d403500a0340e5008020030242003c1e052510105284200c207419200c076030304105407900d210402d410000016400200300b5820010b010807589410b855103440c1c011524440c2e600e00ba5a0b144c146c0b02c002d40d9021a400c05420021140111800c120000a100242c62800d9000f40c5141d2121005524880f4007200b00056030b0107400000159030080c00c010754840c6010322500a4207400e5040101d80301e101c21038881d8085484003001e0404a1541c1d803003054482405032002030003000c4250304101d00c40d41c0c3d40c444180c000503412020661941030090421300f00d000e030025414020718100040320313040e040c04070900c00008102e9003814860004440f4000c65005002000b0502c42c505051791020710480306401c8641c02c26071034002d044131600c034024000c40f005007894205803541c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 880609289 1250 880608039 880608077
    0xb06100f050a050c010c0e03010b1027050a06020f06090c090406020d18080a020f0118020f0310020307030b090f060a062102120105041409610303 64
    0xba00101004010b00a01c600d0030404d2040034281e05071a1591548080c0920805095413201204207004403201d000d1945001d41012082c005508401540450594070f02100150810031313501041d801100c1810000340e01d5000b0480741c02c800710351015100740e580d0758481d182c0e6a44190820a401a0814000070f001c54256030140510f00c03440c600100d110b000080c50200000c0e84000252114800003c01003265501000b06003100303404440244000c4030f81450302551000004c03000781c0a02c0c0048420031040e50706100314121590354240031900e078100303004020000d007804d4041034000c080d040003040c040302e6100c00051141d58014684914941885002c0310500003134510b154402044e0f500c003442407182030025080c07886c5201414100782d0301d0441000244c0d402a0b0400310390191000a02035401008644482d000250308501c0c2d255200f2a810519400d0503801180c500d4030100c42500021900070031000c0254502008041101a19802c00081c45403240700007400b054807e86080481403074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 880610539 1250 880609289 880609297
    0x50a060f090203010c0f03061d160c02030d1e0509030303040318080a0303090c0905160503060a0b03010b1803240903090a03030513060f0c031d03010e0a0b06100f05 72
    0x202440820520402d601190944443d5104280424942420b102c4615031520980005191000d28484540c0b00b020812074402000350465000140d00b0380100900c1d4040e401e280d03401640070b030881d040c0e031500c000006c1c40d80c160103000030b2014500c0254001c0701031203801624400c1800402851841e26940e42c296030202900c110480c0242d83c03008000340c807000600c00046601e010341c40201c4c201e8154504500030a5140d04803c02c034a03c0c14051281404507070618104954050600a6072a01c4060018050b49015841420350050000011542c00003040280c0f610490403c44040518841d4080644400706642c0d5540608a0000c2c440a610010020150011446025285040808408529084441d40055020590005419400500340d0b80c00c01c0045c006440c041504d14841c8034001c00207201c07003030003030204110b074214451900d442c54924280300350010007c00040342880c5070140c0381c25400f4030940f1a071806800007070190406490103031942c03010f541d0303070b02140110303640079246504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 880611789 1250 880610539 880610561
    0x110a050108010630021b010513080c100207030c0308071d0402090d1e050d02070f0e150307030507060f0504031505070c0c030b2d07030c0521040b010e04050a06 70
    0x140d201d034001800c0195504640c66107121805039496992481404004c6c03009048244d40c6d80c580420007106404501100701515072102c0f800c0da481601701c556500e401c07070b10f4030744010151000032000b0405800a00300c40403c1d1181d1a1000d80d542d621805880405561080c001e04516008a590103450698000d2018143c01002c1122140c3d40341c44e40000d05100c246010500300e50712181038180001000070603100b1fa074038401008410b090101c010032500540c03040a0292340004049407a0740842c00c0340c2410710b00c02500300c0310240e81da400c0299584035244600400304044104ca082401d100300100e900340c0341c0080c1400c54030280316400f80000c04008100504100d420000900040c1030800850006c0d80a964128003c1c1040d40e62200d2410310301e4107034851039000f24900b5200c08500820f851b444040703401c00040c1c600c54243c0985880c45441180f2641421949243d0380710341c000c2041038003a6000302d1a10400341c0c0c0b12900c494400318240e80180071076000350300540005030360fa0040c0c04020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 880613039 1250 880611789 880611827
    0x513060e0112020d0504050f0d120f1112070908030f070f0c1805011406030906070c021c08040810110403080a0315090203071205011a0c1513110a0501080106 69
    0x4000342d0400c0481e0411080b00041985640a000078400300308181c0c8080f20700c60000d001d50499401001c0d044140c82d000c800000e0b44c590104456083c125400360750004100c02e0300343c1d5181e10995a010391a14116011b0012450344500450a128004261031014100001c007629100312034031140901c100302c0d1800c9803140740c1d8030000300707100005400701e0b500d0442d1107101003801d50504403603644440c1d05c005114020b4605104009081c4c100180700da4220300c003405e003041c8481c5a800442e07602c451400f03080030180e00644a8000300910700c80140200d40800040c0c0714102148001c01041e41d80700700c80e41100c68014402800072900c0c00c402041c8414241c240050074080c40c0002d078040d0540b83d84440c5d90b41d40d012003082a2150045985c11880c002e1800412180d8140b11890502501307216000d0b08820011030700b0306500c00b042110004480c540c00e00d00c105460f0840700e500b041c4c0544442201d02034078104031544a8200201307960180c0740140c4410155030f00300802244e80040020b2151040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 880614289 1250 880613039 880613057
    0xf110a0c15060b0d05060402030717070201090203120c010510080601030305030a0e24070311030c0f071a01150c11151c06050f0906030a080901050d051006030c0513060e01 75
    0x1070400e0b100341030090008501c00c0313071140c0c8400c0c00c050880e80010300c25400703140100f0070002c941d580801040305005503000c414940703407a42c46040713004156011000f501440f5500ea00c10405a5800c0a00720040021000788059510100d0840031124144030b0070910ba801a001440003e0244003d03503030002200b840000c0325850070a05c18a08520002d00b900d505160314444501c04420840c2181d00241034103060002254210b0f0002007840000c01205094501103004442400160f003100c0c5440d4000360034080d22201007002152a600c02e00c94602485150507030900140e00078030f004482d85401803101a4114407840602044110203425840e50600c100700705903241985d01c0d0190217462a02500040e0070741000240001704643c001250302c0f5040800c00c2200036a80083e03500c058070351150145450f006d500340140d034140106c80c01841c3c41400c06040010740c0b2555443e2200703c95060340c2c148003e500030f81c0252164810700700300020b500751001040c8003c5002d0050320a84880625203600c6c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 880615539 1250 880614289 880614323
    0x605210a06090227041e0302120a18150306170d0c0309180e060a020708090f0a05030d0807020c010327050f0d0c050706110a17070b190f110a0c 63
    0x4c1801400d041421000038418007082c003004030407203480100701420b101d1966240e130b00d01a5441e203103500c0c018090360700007038420383c040d1088110b0072807070f0298483c084030251601856229080d02200b04030003c0e141c910002011203405507080f00c0d40319440d000c5c0c2014002030a0445069001d0a002c0c0e051004000340090102314224a40c0295044402e00045000c64181080c0c2415005401c22000a0040c80201e0208240004881d44890100e03014450800b0703a00104a41c0d0b41e040c0d01a50f414010340544524003904481c0c80c5100b48001d5080c0e40000e004180107408441848541c0403d146c503400c04d480d031a1b10b03030340030540fa41e5000e8400c40303440e12041038601e0715218460150b070000511608c0003008125003000403d02034031241c20501500c0141c0345000e80c3d200c98102d406002c94488082a503602d04c4004101c5400075005a1020b10502e04444819804026514168034541c541800c101980d031151141d0484003880881e00f130b141104080b81181e8002c16090159070810507004c2c1025 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 880616789 1250 880615539 880615579
    0x3050912030a0e01090f0b09031c0908010510030803010e091006060207030219210c05040603080340060209090106080108070f0e0403110a0b0403030605210a060902 72
    0x504402200440c0c0c0d80c040c03030b000103002c0141c4070a55814130815540610400c29081840401e88801c041d2071925005241d000920b4503810803210900215840040014140e02074041c2c0c0c2681c0c0300c3c0000748255260801003054240883c40084c2c1005070030710040c468441c04031070950308400c5c03030f00448640f0b003103c40c1141d0071508268003e03c056802588100308508004280d10444190707500301c580050b1901e0704d1054800c0d400440303a480040316401940c10010946411405024003800400103039489203041405c50b8000d0300c14000007003d244410507211070301d0b030030b040e0340c0400562002d120340a8800900709000c1080c1c021200207400744400c0103036454410300f590003032815039208403c55161003111401e045135604150f22014103000301b0310444002c1d16109030410352600d01428608003110b0402c1c2030605500c002010706d04030405000505505410490644408445c0f403000f200b09000426495122421408081e800c03811150000c902544d01104449001501c03080d141c022902c0d01e41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 880618039 1250 880616789 880616809
    0x1b210c0f0b04111e21030405150409060605040e1302100f1b0c060806060c0d050d02041806080106060e0d0b0604090506070206090c01170f150628080402010c0609030509 74
    0x2122840300a0743c0c1303613403a240244507800040da02150448180c940015101d03228443d0f80686800750001c01c02c600040f01c4c0c0304084500405900c4400c000c055100d420041c040c0c0e11a100e1a285c10750a1004648590201740c40c074404a80d00409954512040035015030b00c140b00541150144040d0849050185481c6e06540c0c6240e4460388000c01d025003007080145c05040013400450081501f84241c1c060b42400040d051280090303410300700c0d214036100714800082d1080742c00501c01201d8040c0004804881e5400c01815101014000e205042d2614011102c0000110601d0b5010000740c800d81c0209108180007900480040c1c00440c1e40b018035100e141c0b901074140c6140b40140c1c017140810442c4202884040ea001c0380900e000345116509410701c0c400d200c0048d0040d9007210050001c0b4506941d100c4201c114824080d010a0725841451680003440c1c0340590011003201c50070302d007003160034460030060303104560503107654a8110803529280010549100d0840502c0420030000303800356601c103654 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 880619289 1250 880618039 880618069
    0x4080d03090219050a0902070602161a0106030e0d0e0d0f05061b0405090411180c120c0c03041206060e0c04051002011b030c1b210c0f0b0411 62
    0x100e0700060314418041e00705540021607090380d41c0030074103010581c0d400b0403030781c01c89480010145e102c20103424800f000740305802a4002e5900540505400c000300c407030301070442e1140305508502d560707a1003600b81c2c1a101c034003c40440c0da401100fa8401c0082c000c80e030b03219000501070200c103032841c032076964001d210504c13070401e03909680b02d901000000c0c00c0e200e00342c4009004d0340411900386490031000c600f1404010b0310082203010700c108030800d65102c0c0080040c8480c40720a8003030941c20000659900b9920a20404010f84020740020301c00e00d40c403d040300c0500880c1d8004501c0c0c9460300c2d0540305d580103541e20480310703180c46480000b5070745101c1140c43d0140901d11035407a0740d0703486c0004004500c14110000d60542e410300c40030301801c1e240302c005054030400d0ba00f40490146580301e412540000c00d681024132404030700460100384500038212004841d10109684e54200d0307500001e07554462070f20b5000740306202001400001030944032055400c684103104603c0410a41c1d00011030b071100003000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 880620539 1250 880619289 880619291
    0x1706013002030f0c04051003050705130e0a0e0303011421030406020309010306080c1e0a05030307060507020706020712080f190c0b13020a0506130b0a02030306031b2404080d03 77
    0xa1188101c4624000c0303030008044d0264a1a1510b00000301d041c520a2034800c038145540c600014080d0790041c07049600442c80c6410904401c1d855841d035806443e000d0380c000d00e205103440c0c104d16030a6000400c49042e505580000310117407060f8810041c04c402140341e400400b046a0f41d120a400400b00050009444907802854807400038000050403552a640640c600d54044002c081150311150303007034485000c105820440e081c9800300403030700c04000c039480640c0605c00011045c0c144102e541c0304501540c034035401c0d50092661220201d0341d80c0028000e12800309813884200000820540045c02c0c102c142d44042c5040482243d00d0200c503e0442e085d110100f90115404400c04c440500141c0c1e21010b5042c92000e0070300c2540201e02d810b070300c60040038000d44001891103003803004280c074100201602803205580744000c4100949a40041d10760728040e200b00000d0310307a105140500c00d141300c1c6016094181084810742c103d14210055903c0a8102d41c003044003060040e07050080d42145169920 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 880621789 1250 880620539 880620541
    0x7050705040e120310050f09220c12050106140405010803030106050a1e020f06090106260102070245130606030503030c0a02150c041a091306031101170601300203 71
    0x10b0000f401c2c07c2281c1d140c4206c09400402003110002070050030f421200d5125014a18020305c2c1c81c10049000e40c10114081c00c0e488000000c100381500020169480604400d8101d02c0801c00c2c4015140c00b8020080240c000f0b10040c420a8400c5001d01000d5032540380011028404000d100e007585003242900c1c1c0143c00400031403075128410040582c008801c4802040210b18001c3c0f840c0402c0f80e2901e900c908207170308840810f44103409406490819400610056514149045d4140c1d8800c03d003104c00454652601c4840e030003010f80c0c1e4480d00690317058001200e142c0d9100083c90130403407400402c0f120b0030307030303600010001c40e0003080694824140c40c4021030707442c3d20310310001e4074010944840c4031300070b82001d0410006407500000d60f0304503032a46e0090110f081901c41403210302c0c0610702c01640c0100e00d21003007410b6901581c0200c004c9030b00421942c00d070004d00800448804132482f40c1b54006110030000b0902c2940b2904200101d2200354440303040301c40c104022840203001a540e0325400c250040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 880623039 1250 880621789 880621799
    0x2e1b1b150507020115030308270f06090d020a030c02011116090209030c0405060607081e07210206150f010c020603150f0603090a080f07021804030207090207050705040e120310 77
    0x4429101d5021803170100540c56442c5a0340181142401441c0c0e222420009040020030200e0340e62203040089800252003003401c044902e0b50752282e080321041c05510410b43c0200d026400415054002605903560550b41c50040d00103651050448040c55003522440c10044180c85030540300b0801780001e11405a40c2d4404801014a020070301d00da0030703104500d80418410150f440c10100d454003940040d0340741d1190701080d424102000007000b8480c8a240000b000d908020b64500c1c28840320326110125401d962260100326920b400403110905552346441a0800d6403070200080310300c0110506d00480e4500140e0b012900c2078105565506039103440340c80c20b1486242030106420034a4064070043d045242801801b50b03602ea000202601c0d5800001300b020340d0740308900445140a401400701e080080c040c04c1130000c0b845045400364014001ca83c0003083e0841c0c28000c48400325080001069050300307000800c4014016444140d15500c100d440034002e400302d04029610484160307000d0040940b40c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 880624289 1250 880623039 880623041
    0x20a05071a07120c09090504060615090801060902042904080304031407151416170304060f0b130b030102130305030a080108010207121d032e1b1b1505070201 69
    0x44968030711404c041c54904a03030f9011128500311001d2040101e07840d1a1810544000c1515402071020559403c9039000c5580e0421291011120004d0007005601c0c1d0f6103022100701d0241b4050020a161003010344903e61a003107400c031020328000210140360650324500705203035074002d500484100381b400c8440e0700c1b02c001c10b00c40c103402403030300c44013064a00d02c034000001c107101000d4000c03801c9440d0110b40079500924100c008020580d1192441e9198428078040309855001210708540181c01d000e405460408280981c2d6118000a0b02c01030401c80c0780e4400c80090b011810766240c1540d800d01c4000c07050308070003a241d0021801003010350703541c9103858802040d07440140c020b0402c0b603004020200c0010140c251050a41184d0302d462000c01081c3d510320034080c1000c3d441d4503130503c903581018850002c0074440c004118a00c90b40c000300740c074103900104240c0b40c5802401c0742c3d458017800103900d0380b1300904064003204840d203941c9a00303110564440c00a801074010f48440f5a41d101d0400c0881502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 880625539 1250 880624289 880624307
    0xf03110406140111030d02040e150d0312020c030d050a1b020a0f1202011d03030a14010b03070813081207090b09030d0f0e0d0501090201020c1f03020a05071a07 70
    0xa4034140145420708410040e0b2040000c64941004480b441c0301c503d040050054851411070000199551607036130309410803003a4140c0303400041002c1d4140341441403074107020312240e03d941034559400026507185044001d4200f4216107100d400104005442103940c2d1241611400b10030070000b07616500d500900e4015030110503a801136500101d80200420504120551565844013000714014145c2400728090a49200784001e640c0030285c001d403440c40c0102c055072007203c01e460200301d5070401e004008503544086c455408412070400104146038460302d84664881c031481100d44842c4903d0f5100c03d02680000100b011070b40400051004c4607500814000c01001030b500c5c11030400004000098a943c90340c4046420f002040c41801043d034002c000c0c902c100100240824001c284c1d90030114064210401c04074014040d0490896081c508810200c0c0e900880a0314843c1030361522406030001e41c80840c0103014490305224102c0000d420031a046644d203010ba441d0283c40c1881440900f400341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 880626789 1250 880625539 880625573
    0xc07031a0708100506091c0b0f060307050d1511041d130305120a0f021206040f0e07090c0e060a0e030f03091818030a0c03080f040b19060b040f03 64
    0x19001c01802051403d0b140c400e415100301725001135554410600046019911403c00003002c0050000c100c00e000d040e00030355209111010010348155514420503440d1000d50040b00e9011128004050204690001908001041e034900044074000580800d070f082d00942c0c00030141680181178000321011400d015a0000745592080c1d500c002c2c640e8000d0f000f400b4105040070305502e0040000c00041c0980c011035000c6841010855079101415070700301c50b03400125002030003a800c00384070399040c401c07510070400f880c0045409040ca2506141545025110120898081015441250020380d4a920041c203c819080c3c03500c41d04100041c0c285420700301c2880484120750401e02c05001c803500d0300b0800722418072a8400740302c03507503a890001441c04000900301000f1440301240c41d11016401080d00c1c102d41c2c2c025182d030041c9a449425020b600381d02214010031810700000071481508686510000104407024082000c0340c840d5800011500903a001c96402d1002c004200300323010744c59440302c045003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 880628039 1250 880626789 880626797
    0x7121529070611190e0108190b090a09020307120b01030b041118090118030906180b07060501030507170d0e04020702040528110a140708070506060a0b0a0807050c030c07031a07 77
    0x2811720001030300f101002006820030340700c0f61500003005e03e4190300020b500c041c02000d0400351304003074070380c00000d20215004034001e03c5180b10115400381020088141d89a000b4608001607080d55609481703680d02420840b6140354002100070107075504818001d038180700500c03a060900d0018101c07820354103d03d1159219400b09004036001c00e40c40360030402910200d0908100c500300c051200c4986400da51b1065001039804204441013000c950091030480e0301447c1120803041c2c5404240d0341da8900384c050343c0c4680d4018500f001d0302501075081c0c41403803800100018140b0007140c010905541044a12502e808250700b03090040300020319980c102c10384041010010412003c03001841c07449007011040600c84090b00c07000c104040b0400720b0700050381c400760780703038440f00f036440c09569031700c1d082e54403a124500e03031000403500559182c1611a040269910352002e902ea080084e41c1c1c5501c07140d00039410703000402c1007070721100e0b0070000200290711540030046025801c100a040310720703001d032280b4200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 880629289 1250 880628039 880628057
    0x60901061b0602090a0e0a051f06050a030903031112040314090d0605090a020d050705010e040b010e040b0f06120f0f070f11150712152907061119 64
    0x18009001c40301d0303015800580d240040c000184401c0c107107600c440c056010304000c005100c201900301500624581c1c4210420844420900d010480710f80104000034200748800324525110b034000703d44050013824000307088480c142020049a01440781e21669800d0130041c8410140c0c001440b80788045030700005410882d18a000443c040608100600021380700d0002c210606c40902002d144117034020082c0c050601035140c032540b02e10081c454180071175690600002142054010702c885030070140c0d21407030ac1940b0342e0104001001480c000c1508090036202d040701030f85a03007005107084240e0341e4242c003141c5001080c403c881400101039140d41425902441009030300600c80d440c0500307541c102a640c5500c911191442e1001c80100c20740800f0052090120458100c0038102c1c1d54514003800f400000300e0702541e44003040d2548200c0c00401c50b074014019269058403079910800c000088413519007010340d115101900c0b0203080b940607660000401d08040c1840c00701d6034911a030941080c2d504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 880630539 1250 880629289 880629317
    0x9090308010b1303080f220305010506100f08092503150b150c03070c030f050c090c03071103070203030c0c13090f06050604091406062b290403030506090106 69
    0xc008004d12005004120214943c60030191301402c1c2e40b0803c1d03600544103060064008108961105440251500d5181c0804210b0782c5c00c100054000342c20050305d03050000103006004480841c8000c124000c1c5000d840ca090500e10f082c2030404205000540002c1d0200341141403107c1c0301c2d890201c1c076002e40d500d006080d1311551500f0b407003449201c01c0486134a4580d0402c04101d800c601c01e0344002032118400e41008000c11854402c1c6481e181d000703801305c036100c041d00c500740311640e40161040e050984052000610403885060b448060604900c05e882c10660a84d001c00e140d508040900c0781d80da004420100c0c01070610505240340c0c0d8605800906c818603554030344045d615001d48000c0c4c1400d03255000580240c40755004684401d0b480a0703c00080845080810307203034107090713a44c41e21074202d03000d01e4076049100c1c941c2000f500300950170044035601203998028148003108480d0106103800d086901a1354000241d0910030344c000c0c0c030003207624505003080101d4088140c00038418000e5000804003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 880631789 1250 880630539 880630567
    0x2a1209090b012c060d0f021305060a1e090f08070e060114090906040615110d03200705150a060302010e0109140f1306080a06052505030703020d0609090308010b 70
    0x452103400f50710080c0c06441d0310040791682c4038803000703e007015090481045e9200e110384d00074850b02d024400c19a244545401c00c001c0944a8100c103c1c000481c0c0d5086a21032044070405000f924000c1e05017034940c10796031165049040c807a64407045141c0c010780e10070000781640440c40783d031200c3c007403810200d15400300c00000b8944c01034205850144640d000016041e4841340d2020007e0901d05c0f544401d034808400d0010035a1015904884842c0508031100c4032543c081c2c05810041d011806081c204851010b030074012035044600240c1d1184a0141061000a960704541d8011000c0b00b4002c554542140009440705c0b1854030041d0402c02c50140c100201c0c5c061001d8208040c00803075603030820000c80c60000c2c021152000b4045107440c900400002c07000c80018540780a50320500d0103100c41d0b591a036981d08034110710300040c02c0c1d44c01d000f000c8c5030805200304021544401d640c00c0050a20600000050450310aa0440c584059842c5011400c0c035401c0740e9914014501c9820b003c4c50550140105c01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 880633039 1250 880631789 880631837
    0x140708070e03071206050a1521110d0b0103050f070b030a050a0f051006090b070305030402060d02040905010b07030810050a170c0324010806072a1209090b01 69
    0x70400c40d0540c00141d56010300019005040c20304241401c0f00e10390816200400041c0c4000e04190b24142e420003076041c944c04141d0444041d40c0d451050003852603030010a00300c022600301c428107a15882143e641d510060754600c254050000c0320425030451070001e10380301005c3d0441d0b19540c018403040000d0040d007012a40c0c801441103011920361100c11608010b030403076050014456042c1410070400c0424030200b0b404a808598816943d16501c40c8055102d11a43c100600010ae04000040260500c2030080c6102000e01c840146807555807500e0204a510a8001d00100c09000500c0800d0550282c1c0c2c0c40c0d0400409400300003460300d003c002401c51101c40c40b43c2003200800c85940040b03a1410701c07900d020248082d083d21014440328401041c3e940d40c0400100c0241e0f00c62001080000340052098811041c5e5202c1d03160281541030f4850042d03022844801803600104107070310008040314480503495049403150400f0600f845c1e620000d80b41c01c12140381c10000011040340320108454810 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 880634289 1250 880633039 880633051
    0x1b0a0b01091109041a040c03090c1a1b010218030613141015060f020f0303040b0a09140f0f0a0b0c0a1403181603020619120c12140708 59
    0xc0c002c400e4402c6041d050090f81d646039070151800144440400390144032580f81e200c01c4408121810307103d0b10a80071500b0034000030701900c80d44102403120284820920f906100d81c030115904101038125a0071005030483d194004594000c0340b01603904180100ea460040ca04038050049440c10100c50841c040341d50030050300400300302e0000080514148002c1e00000262001801321204041000310102c1c0b0030302c03450700000c3e801c0449c1c06c8024408914100c0c44035440300518a142c40c0c9465114850304003400119200795240c6c080000200c402142800000b504005006141070032040c1c1e0b4248000c143d222042e80d0064000800080c3d198000c140d888108412082d41b900b090141c00c6480d0700b14501d070a01348240010601c291030b481c4c001000703059030040e0100d59041e14441c100c20941580c512000350030820074016406070281240c0000300402c194a4191000d00000c03044009640c00d070072211001c079489907d50a06c0030343e2401214035103040c0074001800c03801e1000c00104000402058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 880635539 1250 880634289 880634291
    0x8010605060f0715020d0f14010b030f0a0902040605063001050102032709041a07020d052b0c030b09060907140c010b13020a020c03070303090b09030312010b1b0a0b0109 74
    0x49404c0303542d11541522201503078100100a24540d07041d60320700510001d03000190040040b800028003108076421079204460b0780c0e1503c04584c80d0000200040c0c2240e09080341d1241e01e030080405c80791114005000322007000074000450074215552a2442507802240c03a42c411108070050113981d070000201c6400f500c02c040c1982d40c1c003500c070080f0301c1e00260b840d2071980d10a884400740400d1100001c0d045028400e00c401415140e103545070180c0c0d03181c3c8442d0442c000300300d0900240508207091f81e40c0303601f4030047e140020b0800c2044a810411114100a9180070a5840050140c02e0526001c0ea0b58415020b40c1c4a04a509041c64003425002c80381b092030074100400551041c0d560000e400c000325009018040340c0490040341d0131200650000b0341c1400c014401c5080302a114a000140c01045980640301d0300410703420800120403561283d030100c0d40500c01081130101d10303e100b060f65030013007040b00c500c152a82091000e07203202c40402a00010264025a20b080c08161341a507401e0444015400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 880636789 1250 880635539 880635563
    0xb0a1d06130809030a03051e031501050705011e150b041a0714011802010e01030b0924031c0201051e0a0b130f05061903030c140f07060908010605060f07 67
    0x80c04200720f110369000e40b5014001c21201404068001780602401c03024100d15a50b41002c40c5000442404100c0b1402514082065400b1031540550001c00e22a03010303030000304000c3d401002c0036158500c40c41840720050f95450441e000da4040d0303030f10400542101d802481c5403610705602a1880002405084084e21000802c03004029209813801d00c0071000d030000740032030840e0945884040070907140580c0841c900c1d42540000e50321a03c9000707001603009285220755210701105a04140600182c0103010070501c602600703d640810600c500d82d0516041070b511400e071400000d082d944080c5c0084001c2860311651990103030003510159212401a0b80002c0b080104800035070300d005015074030760300107140142c081101a40ba4200303522480041c2e1342c04100c1020100c0b100c117142041c1c0f10250008101c0031190000410722001d4a05806040e0125400054500d81c0c0e20306000f00d5510201c0030a4050b1020080290300f0b00400004200032240103060612441d5062024401c0007401824514810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 880638039 1250 880636789 880636793
    0x80c0603130f0b011d040f060b04061d04150501060f0f020a15050603060903190c0c0509100906080a030509100c0b160e0f060a080c0708070b0a1d0613 66
    0x3010380301c0429000a2412003030001400c1c2110581002e01903800262070045048103002802c02e030460003582c0c4010781d0741ca0141a5180c4200400440111547c01501c9010004602115110841d419902601c07600480d050900d401d4404e83e25a120112140d400c100040001c150460010301c035403007260a081103d40d03150703a022070400c40502001030810030f04d400c41d54094015036100c584640015000c454840c1c444810321503032400fa1564103c0c6404070000c62689452040303881e480382c81d10440002c00b04c907803200c001829200b000c54000803d92441801081310003054011032004140300c8010b4103100315075440080c49481011078503409400603110032080c25104061724812590040e040c0c51480c10310b0800240050303481758200001402c0d40e0314044092600000c07000034008010902e5142020541080d9030b840030041007002c10034420b2000d1408200341400030580248281c7e411442c0d0f240107001030013168003129200302200044915001c209800148580d0411030b01e080080d26612a8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 880639289 1250 880638039 880638061
    0x206070f060f0c0f03060302030304051903060509010e0d030b030c09190c0f030b0102030f161403070302010504021008070f18050607060209012007050108040311150601090807080c0603 81
    0x29180052070350349011488980c0d61595400704490756000c1d6104001c00c1c090420442c1550581d01010798140c204001c1008903261405079841200042c50181c002a640c5c1c0e1520001c0301e07402c81d5400c54036510f40b64100d40c4491b0510003c07107544601c0c2010004843d541010070fa458002c0702c4c050340100040c0300801e1801503016103c4581d10304403042170003010071901009150110b0303004100007107410000318040d15030011098038400c0d4106442142028056102d47c0c0918141c001d0070350f6900d400c82e1030003068050034030052400600940000c509418a4414012076880500c40c43c020042040d0901c1001640701440007010b0103149000410f0440340001d102401d03c803540712070350090002800c00b04200081c0c01804001c00c00341c913807410307450403c0c41d00d10b49007402a09896040c1c000d00d1042c07103658001c22105401074040e1801c0103d00305030202451400b008007244420f103c1480301000440d41c0e1141d1a400034200d080c020349074441c9040215645e131320402003190702c99140400050034a10b46 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 880640539 1250 880639289 880639313
    0xe0f07050307030f0e1c0f080a02090d0503040b1216020a020d1e1b05030c0307091104030609081305040b03030d1d0303040b010f090b06031306060905100905090f0703020607 76
    0x902420400c45c11507400003a42d41060b420103003c520328050039446014003d92100a40440d1625602e2140e90303510309000c000d6001001050340018280e03c500d01251080028101920012143c507640304800021007215840040c00300c00c9091243d40d0700d0709003a50200c0d803401c400d541501d520440084502e000b2000b000f4a051240e00082c240c20b0030300500c6860501040d4640f800c1c10a14111601c0f6801d050b02e80c8074030155190941d100c024200620700303003030b0f001d440050110b070803103800c198480d660700082d00e05140c820b88942d40040348594000400041000c001d0004590030004600c9000100f81c0f280244101c08001d155143c0700c80e0a00b00950070031540c06070054040ea07541e8501032502c0c1e14a000700380035070f4088002c2c81c04040341111891045401034100241018110750b0381c403100440401d20480c08440240e2a410b00007440c0d02d460203034500513025001005403403400c0ca500501140c0c0010020b40040d84004101b034040c80700800d030f0070f045d60380503a542951804503040c50038503241 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 880641789 1250 880640539 880640561
    0x160c14010203070c03080f0f070c080d020a0905010806240a0e032d06042f0d051c08010308030c0f0f040914070c1a09010e1006030c0e0f0705030703 65
    0x400042003000183c0e1103041040013510a03203910701603072a00340486081d598210750f086828001c007404106000d00400c8031083e41842030301c07014900710724081000700340c3c0c0064002c4404a030300c0726014002d40da00700700c401c3e900034030645d012800030411240b0004001c3c00010ba0210030034000580e0350100d80300b0105400d03503030405000c480220070303056601c441c100b52141c80d2400d00103921030100f041d002d000c02c0706802140c008a0081780c401802c2c282648200800c080d40a03022a85165600e43d9141c4501d8036080501810141100f412900e807080c400070b1070560b0394010400000010700006420909132034002099001c1162220f40c41e00402c41e151103100340e10600054003207000150b204654100a00200128031100c070300f0b482d06c200c02e6400450054000340f030040f1080c03544400411807401940d00600940010a0100d101092a0309207404071000c0b9588640355607052003071203100340e2000d00600f55400c5e0035130545080c55500940d10405059103040020020100f15200d110790406050f0744 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 880643039 1250 880641789 880641791
    0x80f0d03021e040b09040b030a080f090d1203090605070e0618030a02090a0b010921021527090117190825150e0a0311070e01060903050c09160c1401 65
    0x19869413800c0b00581c1085480503c02e41c207014281c0028100894400c100c6513000c42e045040071444010049241c10001c40c0680201d0390455000204101a4003000424169100020703401000d041c940d05031480141000140301c3c0c0402820003940740c0034101c56100b100800710440103035403100000e05001c01c11070080d5118042c00180240c02666500052038400300362100324507555a0040108078402001605600710130070070f5414058280314543c04421420805420b1030812040c4a900c046801c0503c00c005009008034019141d01703000d2125405400e800740d200c490000004000c0344c0e00c09a444402e400c98400000d03003070401c5100030546030305802000882a41d502c1204c4465038108803500309480c90036120324000c0380110030344101818120120050148105c1507103054982e124040c404103903e100f070b181c00191a4000da045036011380020765501c003205142d03050440c40c20300e5546010307104044000c14000c3d0141103c156110804040c2403003d0700c10050b08184810b4008140014899 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 880644289 1250 880643039 880643047
    0x40315020f0406021605010905010c06020a090302030d030b1e0a1e0305030a0807020105070327050c04020406170f010b0d0903030e010f050105011d060d09081b03090406080f0d03021e 80
    0x1213600030400c556013100c0d2040c2d0540380b40c2ea0b0b1004498542c04c03841a64003140b1030f08800c0e00400c1a54008203240c411500340f40d80482e07900e5000c07a1410440c10034040011b503803000d49500e0b0703182000c0c440042c0300d00c02e0001c003009041c000000d2401610341c0318503601508940040f20800812844c410020350b04082503a07140c01001c14081c0c04136800b00c443c0c6006502e401c00080e241c6000c0c1c0302c0d071010010021121640c0f11401141003100204640083c0e42c07520864240308016503c1d400140085c110079a01e0301078440c40d100d030086e0303262806490750013281b2043d001401080070300d03000d50711118201600801d4512803800c042e4004e1000302044000355080100c02100090150402030483d00c0030380e0340f045525070360800c072101c108010101e582e00c00d800300721b10900c00000d81c200301c0441d402402d005142c0240580242c0c051300402c16600e000d5000403d1101d110b1800d441003100801105c1d0240c41c1e070680b2032020684880c07034003964078241507001c50a49101c455910720010440f0003100038907a5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 880645539 1250 880644289 880644299
    0xa08030a0501090e0a11090a06051309121b060c1715010206060604030c03080f04050a03050f1207390b04080c030102090a181107120e04060605040315020f04 69
    0xd00700901480007440d00301000c40c0441c1500245105030365070040c224a8205158004001142001a00c0401001d4680c01e02045039920079201c0755004018400014072401070b45000d5640080c2d00c4088000e001d44050180e42403400d8460302030b222544940c0000b10b4181c0c043d800c0d81c20f030350003481c0142c040107600c1c104550400e511810f05040e0209808032005991403c041008900c00c07400000d20207040c0203000c2002841c200050300840790fa014840b0f04050712280402c82c4450300c0d0340150780c1640908255851000c050100f0364040d103031502c01d0b0f881c2489a03160145401c202c6042c55041040340d60800c00920860340e18180006264100f100c02955117020240d052340050241c00028021f5200f8142c0307921f814170865800110150024043c1c80c80c01814280004640886410b1140c80d1802069000300341701c0204a2503210365880700403580c84240050003240c24003030190203103141038002d00490380c002c070503070302101c1c0e1102004030a18007000590003e4000e840d85460507000104011070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 880646789 1250 880645539 880645541
    0x10e09210a0306081c03051801020708220312051612031a0303040303080112030e04110703032d09050c0a08031209072103050c16080c030f0303180a08030a 68
    0x401c41442c2e5041c00081e45440c80c041d103800d07220440743d1041070340081c0c2620b01402030b003040760b021030766800b002c1c10100c00544c001d0a90b0300c0540300711400000081c209400858448042c9101161040d1496541d03055940b5000107a80d91500d007400d00c00085585040840d00e0b1045030b2665030710031b141c0c20648815000140140174200f40c52680b87d581d00c1d0652040b824008107480440c1e415030f40d84031040e444d080c14031040c46041304007602080186d500d00b640039200c60007080007418440447d2550340710541001030850f08071002d41c07442044118801c4580c08800d00340e0034500c87e101d00c80083c500300300e8038115140c007900076041c5421004d01800090b03a60701c040084c10142004400c2c4072000d6468104c40b070f40750b24290140d1076208010240c12900890030442c0500c00300d00c0781c10b1061926001154003860702244c14500c16820300c08110034808401d05020507014014258000c03c42000b05544040d103a000c02450085203440c80d0fa101001d90408000b5548025082034215513203040c6113003020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 880648039 1250 880646789 880646797
    0xf090803060f01110a02040509071a09120c030601031b08010e2416052a0105010501020d052b06050607060b010f0e061c15090b03010606030b09010e0921 67
    0x148104a0042048803c0d40030760301c6041112400c001810300002d49900b00002084098040c0f41d880c4076043e004140460041c4d00e07954100c040f0611541c440c8030306002c009000d00e000c1c0c280541038000c40700d0070015441c00925141569072295034103c000c4642c1e203081480308800d602800c1300358200b010003859544045403c184e2510140c0c1c2d90000c00b1400d40c0705540d03a00302560a1a10300001c2103403003010311310502c00f0302820074902c100f0a4018400c5038169101e0001070720740141c6a5511001000390350f0301000100540747c15414a0750801d2602e8015007008070400f030100c04900107056642da40c54142d42e1101c1c000d000003c05c950307111641824644028404e02510300d011411041c110845a4040c0304030a00740000100110b1401010324940b411740403425030440c65094550340c450038050341114060000d011901400518410410304050940b081a8010000d1502d0000501701503141e8034940307410750351280b140f41400d88400c0080d62408010700c800303900001101c811030242425030305c020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 880649289 1250 880648039 880648051
    0x1b010b181b0c0d1d0d03030506010206090106061205040206120f041a1b0702121b191401200a150c0801060f2006041a16020a14010f090803 61
    0x44200344480e4105110144035012080d00303550f0203100c810440b07a1103450b105442105500c10814210300e10000b050284480030001c4000c84c0d254000c0001c6542c0c1003180e50fa03c94003030310081c8119840c2100140002c0e441410724010386440381d0014040d500c0b10b0003226840c1008800c00c803924641140110f840ba0010f8030102d40e00000c00141c0c002c6042e00078140c50003503041a00310840302c0e8500030782030000d501181781241c210200240c481c030240703410700203050190300241018030400003c0c0100090014220b0f501949000002d81c01d00400b2003030951300358074035002c3c00c00c0c0366041e035114580c4108444510107038045110301d500c2c04080280e4440f028101402100b024802c1e000402000c0e10100d4090180130300182c007114000d13051a200d61602040020150300080207140c0b2111082d06186080300c0603a04034000190721661402044480c551100402d140649560030000000307485240138800600826030585400c0484402035100811100030b0000802017280f4514140c03056400440d02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 880650539 1250 880649289 880649311
    0xc010c0f0509010206070c0f050a03023a1b0b011e0504020304050a02040f0603051509160e0406090c08011802031b060702100203040302060309010b041b051b010b18 72
    0x6410406400742003030b0354003004141c026100c590365030103085a0510701c0711010b40c0e4601c621000038001c640705000818140303000c3c0d80644200b402103407050003100700c0c030343c034841100341104142c040d0014180b01e000b554101502c2c0541c00c42c40c0052010105400b0f01802030302400311500009440c0c0081200140b41d81d0002182c1d0800075928020002240002c40d409803c6402c900c020b0320043c50325038440519800300c0e16000500c2e90312500e6251400003101901941210308400303005001d1b40400c072500141007a84204004141491003c0c081d414010b000146459141e50340101086000360500c409060000c008000c0c0c0d110407684440350f103000c04010b03030190141c0c0817414080102e0007003600304004040c0020340341c01d01c10781c24440d070484140b0340c840850000344004801079407030400840c00b44d4020800881c0041c0c0f031404200032035240140503460003450b2181140204e40181c213a817510321050041b4401d05002c508414094101110305903445401322490380005112824418060405114 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 880651789 1250 880650539 880650557
    0x1701170606271e100b0a0804080415090e180d05090604155d02030f01081506090f070201150b0d0608070506040b0d141e060d0b0105040b01050f0c010c 66
    0x403045a4000180c081d85080417400c10000120134001c4140c03a40051042c040ba41c03826968941c0d1000d16620702080e440005c00240082001a5440c0010342e0004213049085001c080c540005030f43d5091294055800d02030040b40344006070b514442038500500c0819400f1226001c1d813080204a42c00d0028288824180381c88e0808009085040451b040c28403a1a03266808000754801c5c45068031452041e401e40d054490084030040041c000386008141d8600030000c554100080582003011030076a03805092807180400a01e96145004681c001d81000c60301130181d190303481e0417030250043c141420a8014a89000284102090300415044801d950100b0a1a850b400707a40e403260081d20903d580b1100c2880140f104240d884001c1c00032000109001550320b040c0014550121401c0b0340034000e650100250082c10302c400100a41e20100c121100202402a661407000010060042501955445280e20000c0e4000c100311040380041c01911034440007c030081d43c2c0600a600c00c20030000d01448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 880653039 1250 880651789 880651801
    0xb04050708061c0f05030408070f060f05040302010507020d0203071e1a09101e0201060918021e28060905060301180209010e101701170606271e 63
    0x8041402807000030101440c1c0020308040c00b28590f9001c00030b031840c2206120500000b401000200000c10903032015003081e6240c0400312695049950110701131041090480071615031040031241900d90900305603480700b1141c0003082d04030500e06e20003901841800c90100b01c4050340101d144c402d950090f0781701c800c80d88815004001e12034900000b4024502030010b909146400d07000c60304080c91034501800c00c42000c101240c403081300c40c04410050b0355140c00034400c146017405014840250007000d0b10703e56071154049094490b04103d0043c100d0483c0c0000106030707850f8440d000d031503041000401604100c02101092603ca14411a40821003844000800d0f0070a0f034256412101c0c0c0344c044e41040c01000d00b540001e90f110305503090420060560703082c815900d1409e100d40e181000d50720040b0f652589249806901c0c0103030011100c0103030150400103980c070000350840d0710460544c0c2110500001c00341c204403090065407107202c0382243c0c40402c44000d09603040b5000800e0703044200b1045880301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 880654289 1250 880653039 880653047
    0xa140a080d0c050c0d0801091a0906041116080301080d030e030a0e03070308040803070b0f0615090301060306020f030702060a14161202030c0405090a0e03040513110406030b040507 79
    0x5050014603035502440501c40c91003003640400440105030410502d0454420001ea08140b2603120080105200c0401809501e96901c00d030318203641a80146429090008006080e90780d00800300c0344940c0c0c6802568802d62400c0007543c401c4060410740010b0007000780307040c001c190024002c41815115a40231400854030034041d21320a9410769001e1450024011801c43d10f45194010558041c40f449000000203010380009200510001d405143c4031007481c40c20400ca81000b03402071003107040d45401d014403556881d16011510042c0c0022566900b24240441e01405041e44003503c20751000c500740f4202528400114844c42c01d40e8207440e880d640b0a1160021200201a0f03030180d8000100090003023215071044420170074890500600c500c2e04000e6000c10f990084412001e00307a0081000c0040c4e003040d1800640100d00f40310203001d000e112081c02641d90059204040c41b0320003680b503001441c45a0361250307900720900d9005aa460b40c41d80c101801921010380c002d4022440d043c001040036202d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 880655539 1250 880654289 880654303
    0x9100c051804060b0304171e0304061a01080a0207170304050106080d091a0306130e071412030a0e1c0809130216020f011b0c05011b0305120a0612050a14 67
    0x110b04c1d08a41540c80390703120b120031082400018445160208503000d0341e0a008004145c050190ba02604e59910301440d2070001c0c2d8580520001c4450101c3c040340c04183e8201c0b010300e1380021103e500586840c5981403803560342225219000411760000f09110a00c0410742110098480781811034810004144084400822502c11066015011000c111f00501810011900041c0007803950150b04609031400c422180841c2007080d0341c5d40306c0d0b54100517107030003001081c100300001c8407000182c0c0c9103981115100d101e0046410104441b42d41c07804080d645440000c5090643d81072b511880007000c0c50401c80d5588401501481b400d295591074040749490b00854103d0f588c51700c2c80d01d42100c40c030388c20311021070420440382c1d040c0f10000304940ca04040b420194499640a2100620f080d841c0600151190301008200080c0312503850849001c6070700305c2d040380c0c0581c6860f00c029010303540340130208000b04410340200201100c2c1542107018408e0020b014107416015151030040700a503034490940d14a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 880656789 1250 880655539 880655549
    0xd08010e090304090b010309021c110604080334030309050105060f01051803071211040c0305091e1009060b040e0309010905060919060503091c090e09100c05180406 72
    0x10003040144440c03404c94000301150541030402003015010799000401c000c0102083c0b4902c01c0070b1034684400d00134000040500780e4001d6030101d00d45400c040b03805449101d40780400986010106a0902c0341071212196428424560f035607000140c11460010040d00c1d5464003a6000c1d820b00c8040b600c03600e00b00c0441103846205131201c80c588076016112900d00c0c00741d590b101c5e5042c0520440011041c410703e9035005040e115950000c143c3d91100204012142400426020545440c0800c03000c020005030800f1041da4107d40045c01c0000340700c55034903184402c9141041325041c58007800c108211500061920441101c0501c013501012070615900c0c02020506030004654075420081c03801d00c94001e013400e05c4090036840d0002d1140401c0710706518503038032040000f1000800c00c01010f82c140806120031403030f00c03d20310501d840200010004082800344c0c8208000d0a00404c000c4201044411110507410b0014048030900640141c82604031104100e4901c030096906081403926103c3c0100b958 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 880658039 1250 880656789 880656793
    0x1509060c03010608150303041d09060c0715110a050a030b010f14160f08070c0608040803060f0102010905161d24030312090d1101020702090a0c050405120d08010e09 72
    0x303842c2950465114070050429005c04180803072243e5a51424401071018045030f05908030586100c40310700180c07a030010300a07001500031109114908980034219501140c1080100500303080b40c0e08440000e009045008034010000164443d04c1504280031b0500103840d510108a40800d01c8010754403038400303584510000d1480d81040d00103174a410064040100710f00303050070082a059540b002c1e03104400b441500c9010000c18282c007040114113444000d0855480c0000107070801e80c3c0e92100310300000e81114402c900c4284403940d242d100358844010307581c10000f00c400781180c8e00702070b41f160308103401032102c2080702c03800300804e000e0030f10300150041c0121846101c054860b941d0103036500d500c1b03a210301d6040c00308100f601000241d0a007120b0043c11807001815842c80750365030207829001001c100803030f00d0340141329080c056174a08003115840052120003113844044402c040703c0b031b44500e40240f42d0089021101d045105400039586050501e245c81e148442d036240e000c0b0700181071086800315525 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 880659289 1250 880658039 880658041
    0x306170309150d090f08070b071b060522060b1203430b090d140304030e12010c020105040b090703020a032603090a120504140103091109091509060c03 66
    0xb0039221402015152030003040010060095540c900015000f11000e546180f40801c3c45000c0c007600d1700045800c1030301818001074a180c407074054030a03940900d4002d80b107107a4810004401840b8420480f40c600c044090b070030f0380207100d450310a00419016040030300850f5644500501041d0020490389004890b8100240c0710006425654071301e020f00003d07a040002100c0343c0301c0044e912209070b09000744505040102480c04400d9545082c0301010030b6410005104100b20b00c4142884c1200d800030713014170309540c000350b0380001300ea50184800620000c40d8030782135211400c0c03941944a01d008034481c50a4200503128000740380c1da80d19007070101941c007038000201003000440f128510301c0c0000c0307082018010548042c254202d140c200301d4040070f05810200c604000c101080440a805051070306185050034141400758155018100c640c50606645207680f00600c0001804280004030003031281000d49003a030070080c1c407070300415042c101c4a011307600484c800d0080491454841d06805e0501425 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 880660539 1250 880659289 880659319
    0x15060509040b130c0203030403022b03020c011113050301050c03010803190311070b07020c1906030e030705010606181202150901050c0115052b020409021306060306170309 75
    0x2071210070354881d4410071100c500f003043c90b403d02035007203880b00381e40240d40c0320300d880c3c10064100162409020902182c8103071442240c1c50305070040c0070345c60702840c0060300d44100000c040e00404008081c02d2180c070002c100480c0052080325810b05494007600244003546810061901c0c0c0e000030702612185d6081440501c03c14200c180c0d50b030307100f1505490040341036611010300d840301d43e01c00c0c1806d51342055510104403d09404001c101d40c44070301507641c1d000e000081c8012140003400e038000c51302015240e20340302d00b5204042095910017a00b15000b0085640c1c0d400002d40700140000300b000003c010f2003c005031401c14450307034210140d0044c18002200798007403418001c43d48a0202281071103424080104518401d100e0220f51a01000f10800424203080c1045048201d071042242200841500000c028500c5e055228825905075004100401030348001241000c0480d2031103181881c1c000c2c0040c007280d00d03401c07a01c01c54405400e18494503050800032a00c910400100c1074000802c0c2da04002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 880661789 1250 880660539 880660541
    0x2d030a14150d0804090203090106210b0708061908100608070e0606131502060103110d0302070510200c1f05090d1704091a010e0d03320c011506050904 66
    0x10b00d282c03082d10041d10f004d880308400412030b00240c8040c8880d0395511000d120030822000c000900a49412010b0341c4003060b0742c0c0d02e180114000b0306400802c1a040080b52042d1200340b4480790905e00e9004401c003031601c03004500d9a80d80350a9030b0304807880c24104001450880861a40140d40b5015490740480c0d03900c00c103020083d4440c1111260a20501100155001c100040207030010555800b61103154518107202ca850b4001180203132043d0035240310b040000e600002c080c802c4130002d4400e92030014550005581c0c00240040e2901c01c048005d80e42c0326480000700b01222080001c9500310b81586401460860581040d0640740200e14100204c02940ca408210304002500c00c0c1c00f0340490080090034003140d50442d80c8020780d40340d01c52024010b140b81680ca0341701c1c0890203103400c030b8802c43c000c1d000444a801603080941400144c81040b1500701c3c0c4035089402c0d200003052421032000302e104d0004499408840c2c40c04442d440d02c420341480c2130340c0561701c10448a481c1e4590b400c186201d81000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 880663039 1250 880661789 880661809
    0x70605040b01120c03080a020a081602010206010b1306080903090307031a07020102041409040f020406151218080f040312050d0509070807090e010915060314010c0f052d030a1415 78
    0x4019072227400f080b00c0c0000c0811005000d4a0382d114480a072103420b91002a1901e441070304036401b50030090000440030540b910155044480358506840d0640368180c0944c210310802c01c1c0e064250007a0308001c0240b110392440c1c1c0c0c00050354804540b030595541c4508a08074000d600402c401c1c1151218580050f18000e0350568002d0f000d1132178902c60344450390020b0300310f44855100d0399170400086070304120141c01005200b152040c020741030141080310000b40d50b0b030355180e40c40107054100220351544000142d20a840286901011109010310030003809000303900300c5142000858207000c002104070201203104011140d0010081c030303200d401c200f0900060720405003582c4840d981c45820310082009100d4801e032030158084001401c07802c506041c00c540c00c0c0e1000351889a03040a000040c0154010f11030f000e40d100310b291003502e03030034003040d040c503e0314007071158400b0095611030405440030114010741c0036680d541d004101000d01450326031001e000444140950402c0000240c0043c10300c44081 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 880664289 1250 880663039 880663057
    0x4110103090812090607020f0109050c15070f0c091805070e131704140303040f03060b061c0e0c0f0105030105150f0d0c02100b06161106070605040b01120c0308 70
    0x903d041c02070b5402d60400350901210300103401c0e400340d000d20030100c2d0140b0451840881e40802403042896036150179a80d145c00f6440d280c090043d940780e15000c00e031900c0988030003d90240d003042d0144007900b44030400014030f0240d01015413914550450b404440f400300d6000c15400409041080e1400241e0080c02c10010420300c00c40d0041003c102c0016074600a40c4040020006819160760800c9595400122000e20300c40c007a500c204801c1c810740540410050440340d100402180042000c004103030310740501311200450113100c2206141380c607803a0b00489490b02c4090308803001c5581c03840030044c0100001d403100d8007081040005101c1c0d41881c40303c001c000016032110918164082c1074003c5594081000c030010959140004804c56905010a20941e00c40f4034044c4007030b900040c0043c650384105104009074001e51340754101042004030246e84a610000c2c80603031111021700b81200500000c5508072100300d8420008034804113005240c8215580103011020110b045640d40021644001c0394 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 880665539 1250 880664289 880664303
    0x110f09101b0b07050f16050c06030903040e0c1303030818030a050a0e120715031401061b06060e070909140f16030603020a2303010501060e0103020a030b0409050a02090f0411010309 79
    0x4544130b1340d50701c0350060086c01d88a54406003002202d04000c1d0400048050407440fa24041080c48a003960000507a01a201c502c00341030001e4071410341260f9148075901c240c4a0940000c4000030905412111251140e01080c80d01c80b926900c2c495219101d104424640f000b182d42800034070304030391240156030505d03400a85090303c3c001c0c20202c603c0c44c02c41d650f0310109030000d07035003854103080c2d902d409841341064815007005025410040d01402028105c000701801c040b02400800500c9070700d0700404010013041070748280c1803c041200425610044c01000d110300c1c2482c046c040ca003000018514401c0e46000340c03211945e218400007680e03d101c183c0c291010142c40307a2011001da96840900d400800f510140320f0b1112140e150f131324007588400e00b0010b1003640340000401009411403404403401c0001d04e0016540c1007680f82c180c000340508000300303411238030340000f9000b04040003030880e60722b034001c4075100c0d86680c82e10355090f0340c0d4404950003002200d490780035214650080c1c000c88032052140c22 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 880666789 1250 880665539 880665547
    0x30a14090301090b16032f160b070f050406170a023c090a0b0306030a080406050d18050c220e030405010305090a08071e120305040c060c020904080d110f09101b0b0705 73
    0x8d150500070740e00081c00e9802c3e0150000384050603410980990800c0350343e0174940d051514019000d42000075418a0034001079a100c0001c480304000e0741111109054003412054160840101000c004c2d0030204c0800000005060031140014840c283e5428100c001c04921501d4200842158a50400f5040c50303050300c1030400c110000b41012002e8400703800c00380c1d115611890b041c090b49003a207810b01c98030000018550801c1010690114154540c60000d80f895103142c10200d10a000391a141c1c91301c1c6400500d4400031030308800b40840200b040368400d0b82d0500032900c44100142d261900000d000740110001c210110000e40e080b040c440d02c080906c070046d80c1441c8140c4500c2074440c907000400d800030366076130108010003a1441800b800b80040e840c2440741e0740e00f980d0201e001c08034003a0001e03040e1040840e1501c2c08030306a8101408965402d045692981c40c00420780182703410840c0c505104030220320017226011710559900b11a4841e412240004504a071183c082040001d0541c00800c82e00b04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 880668039 1250 880666789 880666807
    0xb1909120b190e100c050d331815150c0209281505121c0203030c16060b060310060206150102030a14090301090b16032f 53
    0x5001666541e00507615680586000564103030a4503180c414904014544245008210f100240091007103c0d110000136500c910007030152994051070404070082e504141c005a03440c42c44502d80d029030403c512550581075510b03140e03260340700c01c41e00079102c040008034285000c0c4688d40d0400c00d08840240c0c2c201191940f203082120520704240031800c081001006910118100001c88641c00361400e242d92540d1000b0103034049020400d02d000742da025440b01d05102408210082e1500240801480780d01201c0c400c140d16500c8001d28004003007414a0100c90a480c1c500200403240b02d00c40803440e0078a8005000c20b035040d01c1c0c000e003c0950308036a40b00701c03160b0705d515040300a5010780880c04400b20030724030700369000b441c0940041100c0c003440d440c406000d250340d07000400c2e2603440002c1d050110200d0f03a0f00d02e10a049004564680c0d91540c20140c500040c800c60064a0380151107e446d2038180411840c030507004d803031405a408006036820b0a480c0b8074009841d0101c00e90701c1e400c005c640c1c40c0012403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 880669289 1250 880668039 880668059
    0x90a120f0306032f0405011512060b070627020105040909063e0f040b1c0207060902040b01020c01080103060b2202190804050c062a060403090f0b1909 66
    0x40c1984c1e600c012402c424000040ca485156401c00a904460520007507042c40300d03074028400c40c61008800d04c180b00030035204140494002002600c458048203403503e243d400d00758007074110b078484884a034410f5503256407050010300c420360465406840f02460705180ca009003004114040040d01d11590f140d408203800c1340d80440c0840a550103411400d0190102c188050f020002d010b0284169481000544032405d4801d040c1c80c102c41d00900394030b448500d00000800b241810740c00940c1580d01c0024000100020b81c3d00150040707000b5103003042999255030042e60744400c04100c4034089884180100700041d440e4120310341e50350018040402203101601c032103524443e9031805407052500884c0e41d8903406038120704900d5814203803601c1d00035170810740c807207544408070044441e000340350006500c0c50000701c011803001400d1940908800060507200c103151aa401aa021800900c0103840014034481280780781080d900e4200845142500d03c00c03d2080c4144c8000055081c051810070003c4e044000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 880670539 1250 880669289 880669313
    0x10e16051b0109120f0315031403040806010605040807050603040203060402090417040b04030b0624030901060b0408030a0e0105031501030506030a0b07050409181a040c091b08090a120f030603 84
    0xc500024040c20a0050303029184005d440c0d4410b0030103161503203500101d100001458220394122a0300e18004000220135400c500c100c3d042560103100e502c00001d0002e602034001d02c00c6403640341c00d56510a48800401c00c20b4407003920060351592200000c03a000d4649608000d4106100703a000000305000000c401285170010781c401803105201140810622a82c81002d1382c0c000790031a030581e45002d8000d10a8001e05552604400000cdd01000050ba1800254040e90185c690513aa00d502e80d40d81e002d180380d42c0d5020314031160014055840000c1654040d03410750303010300b90b02c040d10300034185203900450003000d000b080d0700e40c1440b5070b110701400b14503440301460151445907101580c82c0d0401102c02e00350703241041841300d49091401c02c140440d02100d841c0482040c10652607a050b101c905211920a1709500301c456220316001c003140700508000130000104440c0e40300e8004964801410784c3c0c58020441010781440d401c054007100841c41389030001648000c90400040301c6440b911540c080c149 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 880671789 1250 880670539 880670543
    0x1e23010503130c170615010c080a05040902030a0623090a09080f0d06030c08031201180905010e161205030d0506120f011d01020c0d0503091e0d08010e16051b0109 71
    0x40d152132001038984140000c40d40f05a09029401d100409080000c0c1030820702c02c405015017030081764401400340329404079001041c400c04155100d040c404000001420f03544a8000c400d110800d00c0d06008a070100110281c0200410401c055a2104013960207046600d10488140608000140641c07038254090400d696034080006011070a600e4a000100c82c43d4010001e56881803284281680200d81542d054031072040080e00b20b403003002d01400c060240800010825424016910182d10002071041c00342218602104121075031072f60801c841c01e10400b806070043d041004040a0348080e40c10103a0401400780031801e45035002400541012802621100565100c0510103580409411414540020381c0000c40c5020194040241d40e82e800c0741e80c801c1440380c040001182c1c194103201042d2500380941c104e01c0c0507007108000700d880714049005a408951084000b040a20044001c980314501c0b01e00402510260f5160a44941c1c01c07801144d0300041c0480301c8001c46010a001e03003803920b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 880673039 1250 880671789 880671809
    0x1e1101090618170720122a0f010e1207030212060415050f040b060a08010e061b09012a1a160810180204030503041e23010503130c 57
    0x1020525204072192840300c00020f004009008060128000d40155403a10140b03c1441409018400100c0c1c480d501c41c004030390442c041c0c428400350b0000c0484980340040d003c02c400c0e4108170746c2d500c06c0001d0640a018070f14009500c605001c0c680d400e06021032589421440110b440700350b0b4079400a00c60350450391402000c0e80114080c00204400c011303001d051245502010b1001d072a103089440d04000004102800c140444004284a602c511841c140a01404030007446201801d0900d903a40c2d10007640d0602e5150112071042d41252610016248100d005035507516507441140d4500700340c080301c40079202c8441c1c0821150030008100d40700300d0744081e05007007010710f00e4541244a540c80080201c2c2e600203210b00d0b6010041c1100d5000907a4098610903c01020a000c8191b002002400385401c000c006204c00200410321684042d51000803281c40181c6010707240d2039640b0808000060150b040c03d54600424100056005001845c1e10a1180656880031005034641000c289501d9000440f44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 880674289 1250 880673039 880673081
    0xc030a0f02010f0506060d0506040b060d0b181314240f060a0e01090e0c03060a09021c03080703021810050a140c0c0603060a03050a0b0f071e11010906 66
    0x4503028000c28052100d4403e040101e0b1a0140104401d4400d90f60303d032810a03507540000d0002c1d90389910440284034060a040d440c0c12100e0440c8005141884405115128110b200c00710f00402901c441c2c40340c55a040501201401c0d0f0b0b44000383c5d402480841e001e18001d503141101740b0500c40581c0101c0001406c8002c400d42442910204094000b904107400b95249400c180300c07030081c20b0300d1281150002c820000b090781815040c1d500781481d500c84687e0602030b03c02440080c2000c1e402c041640740c0215000b011002e514034503000400b0614900401181d404000117003801c0c002e40c09481d102c0c21420389403001c00b1040000481c4a0f091212a101207540490044c0c080c1d540560307407441d1a41741811103460a0b45410125640e8445220700758400d0000000081c11038541540304c4c07004551000884480f51075504c1c1c0704002050869113100d03e110350000055084c0d124654024440036140c0c2e0f00b00920b16543c504030f0310070400c50842c1e80b20350b40700c2c003640000991504c199001c0c2010f0907110b0000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 880675539 1250 880674289 880674317
    0x122701150905070917160f1401050309150c040905090d0801090c08040602090f150a08060406050f0907090812090f010806090a0506030703020a1e0602210c030c030a 72
    0x306114580101c5001481c12080002d055040740f204010386481a00110460140b510020300c1d0407104002101141a40c141c002804003140da5070b40c0941d10a210402c8a01c07461800465080c00b0403115506140d00070300444c404645001c0b02640c101c601d900290345855101c01e0144166002900c03800d01c142e1000c0030100342c480e800a036180c0503141c0441d06000402c4c6825000745280b10180c405040142e000441000541c0c41400c90b90006001601241080881c06500200790304682e1a06003c00c03141000a8030fa8a800d12541080e038900601048178186003409101c4401030090400c02070000d0000003242c550b008002c20286001d41100080d80c80c07514030b05008a0307550011a4605103c124420f20040c0c0d070391000c5a90b840750000c0760020b084e0340e400001901e460207503030000e504502d1191001caa07080031281812510140103004100c140e42da0901240c0c1c41c4000034085070000b10314a40e03625100c4a050041c00d124190301c0883e8107114502e601c083c00e540c88282502e010802007440240c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 880676789 1250 880675539 880675571
    0x100804140304060c03050d0f090f0c09020f071211160807120305040501081b070b0a1409030301091a04110318150105130f090303051e010506122701 65
    0x54406480400796080c9458408040c0ca03541d038501e0014207202021800c2c91062482e6030110a901d09615401d00c0161480c0c1840c100c502d0340300c031003138900842902002c62030410328021141183c100126440c5031000c0c54840e80748640d07224a140d02003006400c0c920200420070020036424404041814404600e03100c612458066642d0010044101039001c030408290070905980c229042801d003508940d440c0b501d5542800b8009201d244e0242c030109440040c000a009011700c14418501d08100b41445100c0060241004950302c208542c410001070200120640180082103400e1085499139202080018140d900040340d4501c00700001c400c114032014a0904100604d100e5400f400e0700310030040ca00203038510305004d03050286081d54081c126107806030b03103d05140c61140b1001c10021340d1614005000e42001da511080b0342c03450700400f8041144180c0355504070f42008060b985080a03a040113211114020801c446034003038005020307042c00c0c030b50b550b8008980c00342c0000201c40580500c0c0c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 880678039 1250 880676789 880676813
    0x908091008060604030b09070e010306050a0f0902030a1709030304120b31020a1e090b0a0e15040e0a030e041a0139060608060c1c020a050405100804 65
    0x40030804441c080c0805925440304840642c0d42240d6110a15640c00c1091850315400794015240c1c901060000414409681d0003140a0440c1e180244409245188481d09545103420082c0d419000940c94000141e2100242e200404001c40035601b00400c031400241140c020b0713880812520301e03000d801010082c4002903140d0102a00f031054845401c0140c0c030210f00c00c01c0042a959226500101c0305c00d550714503454200500c0420200e0f0506560303034076210039405041c0308a00e1510b05200c68044185003681c3c28109071841d19545441c42e46c0d911031014001190165282d402076507914500310308000a02030400d9150007520303401c0f031286c0e106061104544801c401a000b0020001d1b04415680e8001c048041c1c800da020300200d116031030f41c0e0720700d8826181c1495690f1007255485880d810800380d60000c138100c50a406c00d0394280da030340c0100d40600d4424200820034407901c904440700e1b40441c95004d0440803000e4900141400c4d00c4030085202255045a07510110761240108800c128031101c2e09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 880679289 1250 880678039 880678069
    0x20904111309090201120501090c2c090a0e06011215020424181d0f060609120304030501020a03051603360b0c070302070e09031b10090809 61
    0x610300e41a0105081c00d0508058000c1001070b5880340319203815a0701c1260121071403008050200a5569a00c0201d001000041d04042c08a00c194140060a5079040e45130b11140c1a40303010344501d03481020811808d200002d010351310403541c2d40b4070300000e010308220140c080c0c00c800280304813989841c1005040505480500d40125004000c18440d1240400e034986845c801260500e10302c01d2241c0054070511049110100400041d010001d0903007070721008910451080e400701c0745a505e5015082d0080201150440d81000c800c01603802c050400b41c1a840c9051a8401035a08050b120350320982640c1c459001000040e07115420b00c00682e000f500d40b081c0c0101c0d0340c2010800c0000c8680e01c0d08015020880c0200c0c0766030803e20f50342c1c90002c01c9030041c080c554042c2000c2e28500d020a846c04480d00040c40680c010701c00c07101c01040c440d001820050003005028000d50400300d0380f030f503403c000c102400b803400100d002c5c0c100c0c0c88802108030701500303410034403598982d40c44483d8481800440904c803020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 880680539 1250 880679289 880679321
    0xa1208060a080706050906030402130905060a0c0503014e060b04090f0803091905011a010f080133031e020403030804110612070e03120306010f0e150c01020904 70
    0x40201d1a080004c5681b00c810680c0c1c200c1d108e41c0c3e980009161041c452215a139483c0c1008909803c0010100e0302c244a0004c0003801c000300704007880201c5242c0000d0056501d031820303200b0040348020990002e08004514000d840c0b102d904900c00b0200310922041f1001c1c405004000c1d0744040007450f00400c00310f0711303043d5030400a004c1c182d114243c05034108180a00260000004161001c80038090480304403103010300002d0341c80706850514000c10103444ca480d5009801d5025010640c4505480d01c6d07281d500c0d0741c0d0f9054507400c20924220201680750704a00c2c490600f442c4402240c51410811302c690701741e45002035400d41001407140e880b40000001e00c0e11901c1003005000013a0000480c0740c006810543e03200c40d50040d640461b08901c141010501c04900c80002c00c241e165002c02c00880102041d001e44211140120704031410b1700003a1a0180826020f40001600500c503100c107810b0588003d1a240c000c502e55206440d00b81e005030515079140c1d400041c03145445c14180161200d60b214112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 880681789 1250 880680539 880680553
    0x50403090905040503030a0b120316020a0e0106080417041212020609011104170307050303100305070905070e01120605060429130303120b0604171b010906110a1208060a08 75
    0x6140c0742caa21004141070422603650181601030380310040d04071040400401220754030708410b0f1208801121410048dc4036040180003c602d84108920a504955060701d80701002c0d141c6585c1c40d0f207800260201c2d81140001848005064214030149141b20b501501550030203400606009040410003041121940e0400c003036a880178082e04101c9040301c09003404030403510180c500341030452007402009459480b010040c8030381c0126401c81c050840c1c1c031990450341c0b500d643c0c0c003429003640d6088842c4400315018001c010319a50080d0000210100c03d4880010303402c0d00d440c002000343e045600080080d00302101c80f4154030400d940c010000160300c0038140d0510103015090503040e00180030017030400c000e10191002010103030704190042d000003040e0365190f0343c4451004132500300c82c03e40c02c101d9124924401e110030407030f5140c1d030b104901c040c0c1d0fa10704d0160402000b80c54040c096240010144141c10440001c20740c4a166008000c015a403042001d00700b440c200108483ca07034018140f16000b403a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 880683039 1250 880681789 880681793
    0x50d060303050301082415040906050108160906080705040207060f110a09060c15020a110d0c0b0f0714160b100617010b1c09210306090e151302030d020105040309090504 74
    0x502540e9014064106501d217102c0c1e1f080114000d80b008450040225040800102e00e514010905140210485a556801d07558807070106080c2c612501c515001900f060b281031000d0305081d0010104c0d5030040c2404101800d1142da01000c89140c000301000441003c01c0300000c0641c000c0e005401070856241c841400b1030325403141c0500100c0b01190054881e400540c61054034012100088040e07410800c1c0d0301060b11718080a00341d07924607182140e00c1a024000142ca010800321001d000701d070666140f022403c6401d0440380190f0100c0081049050354409560004500220f1988240900811640102c0c074101d40988819880e601d0780328211400d000510220080000b680d202c0241c80d0750000c1c1e0025805403003030040070740580142003050781c41c91080704229045e400e0903001e00300d075904010701030760f4614102c02c80d0036418100001c0c2c1c204d522100340466036403a12a0708803003d54038103885c07888030384d0001c0c0c03034580600040c10260351900104818150410104401003000d0a03050166141035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 880684289 1250 880683039 880683103
    0x7050109030e04060509130618030206040201021606120b0f13140c0702030d03050406060e0703021305010f0c08031009140411090f061e030d020f0714010c0b07050d06030305030108 79
    0x82841182401100045003801070503080712095452454027000c4e210542c1c2002901d605003101c05901600c511a403403080b600d54400384804070344156035959081380c1d64000c80009422001c102c1a071001620300d00c603d5950701c141c18030910240d00e060016400404100d0305030480c10041405061120900000340562000724032800986d2032440d001401e070380c803454650000c001d00d41001d012402076400300402c25801d94002c10b001e1043c0c1d41140b10495840d0011521502030740801800030f06003200c1c040000b000d40c0d000d503410486100c0c010484507100d00d050f0007145c00000d4045010300e400024031050100401c4106c10a45064480c61031910b0044040700c6420b6019050758094510f090310703818a40074901c00c5862914008040d203032401c158110007035603070010442c090145d000e1120001070010010801c01c2d00e11006031185441a9500c0e25011204a00100107009101c2e04000f16802e186480c401c4901541c4a80c481070b0300ca504116070507107440302601c1c01510820045586218803100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 880685539 1250 880684289 880684291
    0x18060b0909100e1503100e07060f11010c180608011d0901020c06160f0806100503091606170c03040c15141303030f09140402070609050307050109030e04060509 70
    0x20a984941e042c0d112542d1146000359298480d0128084a106119500112030509000031904408850198010b190b840c000c40d880c081da680c176180e1240008010f81ba00902d101007030b004250a0000c5200d0300c0c499542d00b511201030040000903254105051140b02301e81e80100642502c0c50208455818400b904c4801550010310400070040c120004207400b109404039407041c03103a40166411420a5400d407800b4100c483c280802154407003482007402c9114000c01440354900900302d080b0042c003001c2c1990180d0004d07000c40310340d010b801901c180c03201d600b43c4100010010b80d03850100c50410002c051440aa001c0e04012013404200240804602d820f40c8000640f1080c0c022540030502008003940d1540303400c12042132080300420000100d8071144c3c19401164041c1d00e0750400d1905401044810340c1407401213105a05242070706402c10b044c01d078007505000307108100000fa20003598031480e1864102e100c0c100c030141e4503510300c00101640080c0d0884002025201403200c1d50600002801c4400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 880686789 1250 880685539 880685557
    0xb271b04090218040921140702060a1e05130906180b061b01021903020f0a14070b0c1c060605121506070c140d1101320418060b 56
    0x14012420540640c601c07201003040020013441000200c1040c60801b01d83e42d0100c40c0e0a40210b2040c0002c00c1040c040c03a0640f60304012010141e1410003258204505034005c90248400c03c8140000c5a41e003400028424081c0310503038440980343d01503a00726001e8130042d6041304035081d040403c201b000d4801500c203060303004160b4602180644800c404161207020b2031000b0401181515500e001036507040d401004650041d00b992203014940c0e007002e030142c0c41944481043c1c240c08115002001d80325003010100ca108902d016861700780682c941c0c41c4a04408e0390000d6184038002100c1008180000c1d189001c404407440a0081c14600313030703000e003841c040c1209100d80c21520700001480003220b0904409861801072100d40c485c0c446041031890783c8154040c0c10729110342c0811840184c40c115a0300303040307a58003520a0109000c200c00440c2c0d0300340c210f0503040d07002030754003101c025030030340800720503003c454604100740c40e54500b202c1c202d404130006595a00302413904400780083d100341c1c800c0b106005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 880688039 1250 880686789 880686791
    0x61f03030912150f0209030f06040f08070303020c10050a0b090408031602070312020706080a02030c032d01080f0705060c0c0405060a0905090307030908160e0a0b271b0409 75
    0x80c1420110f266000d6101072980c441e10713240c2c03002400c84160740909140c030720039812214118403052846985a8090300c0c0500580455040000040e4440c0000c08404c0d11030324025052504092030310b0f03d4100400a81c0d00c1a686400801020031340900c11500c00f184210380c50406400c003a200e2007250310020b400002c43c0b080907103089880f280200b1455008560288103219100626200251540e80034020003001a0101c00070810106eaa402a00d00401c03030201182d145449500303417800020501e8900f034a81d400e29210860b01c246521113501d0003011414060700b05c1912000c822400d21529401c900c1c492002800010302480c80000c801c16032000540e1300003420b4888500080410b042940407a0311141000c04202480e60302101402078144039417034001c0d0035915840c5541e280c845100902d0001d42c2070384410401d1014880500fa001203400701e002522001000c042414100c0ba040030840a0b1121000e41d84241400042c0561082800d105540203410b99501d0580c0c038881c0d841125056 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 880689289 1250 880688039 880688069
    0xf060a1202120402120a0b270609010504060b061c0b2205150102030c03120c07020901060f0905060c060f0c21190506100f032703031401120803091e061f030309 70
    0x2143c000480c2e40045050001265518032b403201d029030190000712821100345050911410303160401005464a494a00a00e20402e1803840d00c58070003090b1112005910114150020b01a0340b040340320008011010742c0045044d10784410715000c5805045981d5046520030480321140200200c00d0790087d041c3c6c0707200c451160301c601c0c1d044016402406806548070052100002c0c4075600310045140d00000b5407a4495a1641c400c1040a1030241c0d03201e100003600303c000051180b0f101c01c100e01da44003421003207071414500e20282200d40c07102c9003008040c40300080c1c028800c50400c42500d85001d24078054040c44546490030104070340100c81c81c03010040c07101d040c180d840800d0081e00404d864043c0f140801403140304081c0600600d54105100f54041303071030008045152140c46020b81c5c16100c00c8510a00310244550b80c2d0320140d40006c12000c0c1c14020b1124203050150303002c049140303401c1d540000b4a40d84c10714611680060300d401ca04940c1410702e54804000281d0001c003d48101c0381241d00c04020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 880690539 1250 880689289 880689331
    0x6151505071509050d080f060d02130f0e071d01090207022d0301050a0b1011071503020c0f03041802090307060f0e03070e0106020f010b0f060a1202120402120a0b 71
    0x10700700c01080100340d03000d486005c40d2000d42c05001c4070f1151791810394001c91516004d0134050b2005810101a40001d650309240034850003e0300324104034020b1010024030075607980c841c60b09000305074005c200d1503001d00d00b0800440010f04d01e4075000d0815584210300c3c0c40c0041d0f00140310b1041000315511086a200828103102c0c2d01d00120710038100c0054028080741c0303400ca0001e0005e20b078003c55244101508008211068422050000725100c02c40051004908100c10004e000da026a2840c0070903800708030216240100348a80450141003030025912242017058070845110401a001815841442500d203d81d4002407800c0072500b02c0d041000e000b40d030158084503000030640085805205000c40042c03080c21007079000c0d041b03d600d60300761034140d006000714a00f07171510704e2000c0da800460580b04468a160400081101c04914100240c624850a50b094243d030007944840500c40305100401066007003041c1c9540301d1031940b80140945c288169200c4542c80f201a044280342c980c14030072042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 880691789 1250 880690539 880690541
    0x25031e030231120b0a14060a091806110a110313090b010e1207090506030f0c060306062503021006060c06111c0f15030210050a120504061515050715 65
    0x2d0a000c1203980c9051032142413403094000c0546141e569585400d000c0020120070140d502d004090007082080030743d00e0b00b0603100191242c5c9141030302480c500c03e01240002e525106031210340780c0c0780022030340341c03c5400340c098905001d50501c00300a4000b040000b9030103541c5090392058400801c0e0001c0c2480d44080101c07014107001c03500940000f100c91170b0455600340028000c0c100d9a6448080c8025502c2c9004d140c0c440304c4018202d84560701c80c4c070004040b0310780403020b1030388900090840b40c00c0c0401c000c4401d844903140b6003502c1c4903024401c03c1d00c0038140d061000d03951110040800f400b1103480c0440042c0b44110250000e0b081c1c5541c0e94080032a0b500380d104440c0780b003550a52070070700b9280128107036009020010071a202c032481e100c13a1100403034000038004200c81d0018505140c011400c441a06e0992014011504214015120b01400c3d180c0d40b083c98080c60040d6400600900490850705a030003035030700700e01101400c00c03000038503e95000b000c580085600018846a8030054804e01e8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 880693039 1250 880691789 880691887
    0x90a030512092404020906011823040227010c030813050a1709010e03011808030a0603020d030903030f0e0a1401020a0515040b0a090f0825031e0302 65
    0xc1c0082032107a41e21101e10902010180c01517000300c8248010761500740045d125880c8004095803080c4200300100b244444201640760a800c081003122007007000600064201e034410501c2003100381c075800509051036450840c41564510a0804940b0460035032400b1342030140c000d02400e10070186c0041c98003004424000f02020079400110300c1640201c004520200380c2140c20490b00003282c4400000ca00c0ca4140030b6113031014807000e12400c0c40c445035243c45226503c018111403003903440b4180000142c44458020f00d28500a03510a00f0710b6045d4540180291980000341c002c00403100c060080c1e030354806030000c0c101da8075841e04074070006003500180c2c00d0101d03005000c0c09034007404072142d580c00c014190103881127201c0c811900f01642e070070100c80c0848030701400241000ca0504140300005240b24010002c0e041580c401c01080422415105407144640008500040180c2011144548401400300ea881080c5c182941000195501c20100c0f00c21031036031101041d00d8030103e8590883d405080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 880694289 1250 880693039 880693063
    0xd0e072c09190501020a023a0525060b01050a02151305070e100b0f030408130509150a050a03050c060a090510110c010f050318010f090308060306090a03051209 70
    0x51402c05150400a000b500118446030150081a0540042c0d1482c08a4113003103284c2d1205448010300302c2944500444007070300601050040070800044160001c1843e40c1c0800c0c000c8003000328003015490010140c500d40b680e036034107004080c0300b403082498001ca00252204000c01c0703400c0071a65003101980c04034201c041e000d03105000701d000114a40d0b00210505208200d0240705614403a075580c1c07154001d205901e2510001c120038000700303001501000040ca400040f4904485000d500d0f000000c41c5581c003610201000d0750295401c04079400c050801c1802400101c1d842d402003403031034035000e0301c48501c165118898880043c00018480c060b25006010341000350046400044c0190003030501821742e0b07803407001445030003d410a50b61150f107003407070014281c2d541c403070030761712580780402030b803c59604040415500e6000c0040000d180344122096035029588003401341c20318006260a100d4040c00744252a00300b18603101c003103a088021103500241e0206008115078403524140d0600d0400c0001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 880695539 1250 880694289 880694323
    0x13110402120609010509011809020103060e2d10050603040807060e0d180506041401020109060213140a030515090708060a0219020d121a060d0e072c09 66
    0x10010751204219944240b034155034203c1903907220010022400024400c05c1c03c0c2036036551030080c010711241c00c5281e05510604000c02c00700d07200c01d510a06160100c4141d440c0b505034110b00e180e8031401c826074614030001582d42d42418240804c10090321400350182c14010100000420104221142120010758000c0f40c104602c00301e240015465062031070300c0a0008401c12102106050780500020485600420461030709260191003644400101c460b00c1c1995668414607002c00c41500051400e40c07041224144442e040c881c041030340b81e40100c116030003000209028030002d440041c2100d9099025500601141c0e40c11000628092054202034818010403042c010148680c1d00948005500310611214040c1186c50032a035401300d00503600e00040c02d0245034000034050768004850884026000c481d01034030a00490766560041c03110410466903080c549070359140501440008c0d020745240c0801c44101500101d02c0400741e454286d07900c840c0c1038085400c001c0100000440340109a0b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 880696789 1250 880695539 880695547
    0x261912090b22081224012f0f010507030c02010204050a09090c1802030709090b09014a070504030b010e0a020c0a0309050f01050c10050a02090a0e15010503060913110402 74
    0x44c0e8a1010b481996800c060320030302448608009600c44004408a5041c0d40e0b00010f03070450104c6a0130540304020411200707480440042c6180c009000b42486c6a0f400c10022440f400d1482e00181280d030f08050b444110392050005100a54a0514040c2229101c02010403001c1990a00030581e04440e480703034162038154146540d0060040d0061032040c501604c5080c103240d594034180c016035401816040e40303c43c01000601c00c40002d03002250799010650225480451030011000c14201081c0724501001c0c8203400103600c02940804082c0c1c41189460401d050a186941f8649242018000e42c040404003100180f4600c00a0341510001c24000d0103c8005201c1810b02924090071802240c2c010110040b01c00c9440d4040c1d8100c07440707010503000405840540c035964400501c1c02414200390306c1d40070859004e090b50782d0444480503003185d02040ca030b10304100814401c40301d641400e0310b05000d410f004010003640c4000c2010791020040c05203421034038561514110a40105041c59440f0744082 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 880698039 1250 880696789 880696807
    0x12090813090f150303050a0825020a121103030c0d0f050f0901050f0601050f0c07120318080106030f02010503092e050114030307261912090b2208 64
    0x1401419214154000c10440c0d1126140da020f01d018a500024000c100100002041584218489640700700c801140c1101c1a07000512003a03070852220360180141e10280c0b184007400a040d161000c0310a050174580119050941d64680b280002420f2004080c00400c466480c4039980d0480c05204003104c03001c11451034911400b06209009445150345903103000c000509032101c6200e81e43c010034050711010708108e0303811024121580210341d41c3d86a80101d03000002c080d80d0745030441043c544640c584400070402d41035050380700d1400d40d20140c89130b0b04007902080860400154040755a80a28042d641c84d075a0403940c3e8540030300382d0114540e2103044040c500020800d10303950701159002c42014803450b41da075107030316140324404882a6415001001104001401c02942d01c16035145500240304503204010704c526180c1140100150104144400c4110355a02c41980c41100810000c2000b002125031504040420300901001002c204030346448102c2801011003804243e0048003165185948 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 880699289 1250 880698039 880698041
    0x9030320030313110d0b0c16020603010303030c1d0a050907111006050424090513120503040308010e190b2803021009080c0108190c0e031c1209081309 66
    0x229001d455035035980d0015019860800f000000c420342003a9480101d451f458070b0b1114980c00b608032500c100b20310a245038010703207039500a18001d40c041c6d100012070507400c1c91b0142c40c101d030006048811503185c0c640040c06940700300c00c000594034280c0e0030503032079650140d003a18a100300c0c400c0c880040c407903501c0c031004a0590381c0100b030981c0c8060380c082c094180c15a034aa0055a06140c2200d41d580b10071710184611903a5074002a84000b4003403440000e2402911144015510034400000080e400030400003810f4100c103140380145250703002041c0fa440c02141d100038404000084021454403204010480c0d5240000109001e200046822000c6030141041081130400d2101700d005040264a8a0500c0c0c000da240c0c1c0b04442511029124045035080116003c007402441d4004590340b0122861601c00240310f1f13807080140300e0300c0d26040030200400f090715141079070150b09600c0610050005a0951110155055150080c404282c0e04501e2600c02c41071b000b0002c0c05040c154124070005003003046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 880700539 1250 880699289 880699321
    0x30609060702010e2113050d03080108010612030f030b033904020406140921210c0a020114090402030f01060e0d080307051c02040f06030e010606090303200303 70
    0x5070001c10030021040244d41d25458048444032140b0050300380c07405529400c500034840b003603031007600d54511a12100020b925441241060300040d004d00010321030740b0001d10505012b00b01040218030041e0260341c00401400d0b0140e121420151103110304001034804010303940c3d188654101c50000385030b82c001e80c040c012032101403500003015500d803075a09a081074421603054603070030f80e03514010302409200c3e0b0b4000d50007201e03865044030545600c08446440c9480c900c4403907010101414518000901d0203003040203024003940000020030250039035403c00984030310402d5081c01c11554040c911a00040076024804d141038100c2e0002081140b90981c1c0400c00c2c0c16160365485522440c02a10280011892104001003d0703400420100c0c149a00034000b529010545615100340f1a854440344030983c1c02540c400d0003821118102440700507014001c0041c00b1050800030401c60b0b1410000070020122413002506215050110240091608003450121720280e001c4a9a80c148600304030a0585 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 880701789 1250 880700539 880700551
    0xf030507050705120a051005010b121e070c02040e0d081f0905090f16031214070c17010b010e15030603030d1a09090f0d05030603070e0a051806010e041203060503060906 74
    0x25005d0038010b641c1f130900c1400e040e50908a10f041c14183c95490a0150800140415017032444011203e195501c03c0307500c552140f40c0c1566003820850292040c4000d03240100c803035840343e0b00000c5002c2180c6501049003548038500382e102d0032031202110f40119081080303410035611981000100400075000040f40060690214200d8010140456075009250018000105a81e07003000141082c14070075403481c9900080c4920203807400328669160b8980b80c80da030740450b41040c09480b44403540d410070310840344c00ca1001c0c00d00c9010104d000001514202d1109813000140a0202c04a00715440030400e07900340c0405220204440e2495415410034802e007003280c0c034401c1255400081d01d008000c00d8862644407050000c1c00720030f00c106d00c2590350f500000c00d565054403d001d00003800310f0b0494a42c134022446803000048508100000f0a09032002020110603a0f0114004101014103840c0183d8055008491400302880e0300404070302a00482c0c2c00107a061280b40306010f100500032038883c1c0944 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 880703039 1250 880701789 880701793
    0x12050c0a0c0305070e010b1818040c06080108030901140a03021c0b0405012102240403110901050d0b0a02030406020706020304060e01270209190216110604030f030507050705120a05 79
    0x2079030f035081e16041910309004225407d001030001d090140010481c050103214010240101d81e03540c401203a2034248102d6040e10015154441044801c0d00082450301502000014500d00102c3d00d0010380900b22240c0740d0100c1003030015600c44850b03c254103888403201c0c045166000901c0d0f5030390880c080d0041203840ca200c0d81c501000040d17820340d800030f100a02c954224030b4909083c05130b020483c036101c40c0c0c51782c0e01c6464110200e40c82d2494580d00100040c61003401c0d02400e8520280520401d0007050308541e00070031019500360b021416619459520072100d00003d030383c0742d4441c902072020340540803000b049180040300f40410850300780c0045181d800960020000d5284680600d140d03040790b803108440090703058a820016041078915994030040b1100200342d49008001003404903442440b08100410207200a0f4040094071549101284001c440da1810b150a43d29900404520010000e0504c1300010ba0542040814040722004002c020300f124139245185030f01030b44400440104403458 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 880704289 1250 880703039 880703053
    0x3050d11031603180b01090c11030c1e16170a0c06080601034a06040b040b09030f030a09020f0307081f060e1302010203120c0910170412050c0a0c0305 66
    0x1c131400540f00031800d41080006440f03074078103d1802c004184104144040009180e80102c892004000422a441750200203202502c44040e5001381c2d0b0810404100c4030ba003001c604072070200034240d0f14005984204111000040f0009006c03071424098840040c01500c00c0b0303400052850308125000e21820080c0c80a020211500088610307464294010030f80c00b054000b4041200c554465071010f10685001d1a034007242e0b1602c01051a2001c02c07101110107100803000c00041011010050360440c003104001d41c14210740c041280181c1c000142050003041d9140e0100341550744060086c100a20080c0c20303140b81d0358030391020507166141c02502e000c40300c102d140c07030f10007908407407003880c0440321040200364451711807440898040d070310400181c1c114070050040045940780003020a00030a4070781d0f1300b40d41e37500a08081c402e0307030500460361390140954500f85852128410340482d42c003540c44915500241c01000d010740300c2e40105450080d01c1c0c410014200b0030801061404000d40f4010400c440d46 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 880705539 1250 880704289 880704311
    0x106030c0819050702072301022406011d040f060f1401020a33140609040b1512011d011b050715020702090708061009080a03050d11031603 61
    0x14641c82501c0c10303002c40418415281d41c103200c0d64842500100d040c416295032a81d1411501110150701a49860300032813036404650940e010084064501d1011084580ba161400d0b40a03034640401072a05040c01031400402e4a4503002005201103103000070010020016042d41d490000d00d11740c043c4541c02031124101145111300700d02d544110000590080280324403039a11000e04e012507125544e00803c03080d039801c0c801000c42d01701c602041010140020b0b040c030700d400074501910025040c54056150b00c0288008502840c0c5202d601110005071f001c0c03a00d0003071b00030544540392030b041c0c8001c6500e002000c0c202400540341000801440900034811f00480303140300400c1c40c0741c881c8403d001c0740080000000140101d82207c0100701300600040c00c0040540100b020f0f02012a803440c000350002c030810526107014198420088074900d0960309841c00e19041c150b4420a110001d403c0c000003092800c40d040694026442031880168142c1e140d080000315a90703507201322903558020905190b06519 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 880706789 1250 880705539 880705547
    0x3010b030304230f0d03051c02040e070c0f0206130509010905161b15230603070512030d23090316030c0f0c0612060905130318080709050106030c 64
    0x4162054152400303004000c3c40303075002c0c8450940c0c2c034032030b000020404021541c0e0340304070072400da0703500940b106941c8101c0040c41842d120201d40080340264810300040c40340c03520310011a82e10410608182030b40c11124188055082510300000390b02c01c1001480500540004406108590003a100c0c5203603643c942d070700c030810340d007080b0781301302100500c131003003504051140108100368094481c3d00a0303103c2283d164400d40154181d00b10007070340d0310b41540040601000751410f40c0070708445051112414100300080c1c5030300c0075100750b5110303000580c140030400400388203e0701d030501011402c0000802c04a005404820700e00d94120b0040c8a0710300140c40c00c880030007216550805e00c441055000c0103650b044c0e81c0d10500351130036245a007941e11503100080305c0808080c00b410442c0c442d60031205e05694010140c9000d40c00c01b040c002d00344400c0c4203566403140b80040d582a070500344141c600c10501c0f1070074000c2885a200c51311a205c0c084000607e410b080e40041d0503a1026034041c07182d035801e044159 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 880708039 1250 880706789 880706797
    0x121602010f05060d110109090c0203130b0c0a080a1b06060501020d17070807141210090c05091e0901181a0609102001140906010f031202030405040504050c03010b0303 73
    0xd6002008402d140c00080c030304800c1017032201414140001e1568550803c1421100201244030160340002000780d515100b65070601e006103090700095142c40c00c80421540c17185900040103080ca0004030311004401c0c02516490410003410300c400011800340d00b07000024051354815030b0b000d402500e10b44000c862040c80307100c4103031800801008003503c0d041c0b02201c1d1303200d00038826820803200c4c40d001e0656202030401042d01615040c030204590800340b100c88507948035030f0300c440c0ad80b6140c8180b284a1ba40c008040d2003075044226030724100c0d4a403000070034154504c85103080350300a0030007001040d650f041e0306240440344501c80d0204070ba0070902482410003100c184000d0f5010509004100c207a1401d400703120311520881c40c2c10540c50800081004c012076141c0080381107651503400701c1d01d0320003400120070740c0500c601005240d2545031500c40c00401c41076020141000038110315511540c3e0080040b00d0042ca000307441000f4925050038100e494140d107043c020b10035420f240c02c10704070349000400d90b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 880709289 1250 880708039 880708051
    0x209060a05070c051f140f0c0a0b06040c020d080c04050913030e0f091f030615030323030117030403080409050412090501080613061d04150603030507030e010302121602010f05 77
    0x141c9902030070405580503003e12400d07800c1d402c007c00c00100740b110004041c4c080b19040030000c0003440784a10740340304146001003829015524158452109540c0000e060008260b68107220190707840c0c030003c0b410503101d560052070300410300000740801e81440010088110303010795610003000c2241c42c10041e0482121500d154001700c0311011450140c0d040030106070300d04a50031b0708900645c0e00d950f48070590384880707641042d10703010b07540030030905800040a0708251000180009126544020310b001e0b40410f0080c0011a0100d20741c400d0451010004c46004d1904400066107075079a45034030324080c10b021a41140c84005480030040d001c4d015021007010b0341c034140c413144015524070341071101c44d0030f0380c401118596407583c100140c680c0e0102d090f000401c10f11aa490444e18160418503001840d4110030031102e4548003080010070307800f006440d840f540c0340c0b07000070480c030940c00101d0180c082e0032804060940d071070044c880d9820304421205002d8900790000e204007030440f080d0008441080714a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 880710539 1250 880709289 880709329
    0x2070e012909132a08150f09070804020d080d060614090d032708010914121c0b130c030506010e0d020409051e06091902130c030209060a05070c05 64
    0x6503c02626400000d007510450b040070001c240f2000c401d0032840c10034480c00c0081411581805400540b82c8091011414143d40b0300152400032070114214440052481040104820200f01155201c1000780a034a802035501502c0d45c40c0340e100c041c02070215109040220341030094004020921800f51407000d00d0003860540d1a60107900d064501c011040304d8900365080c00c1d0090032102c440c424001d0080c00842000140503001450a00c14908151300304150300c0d40822000080c566042c0f0403a562901d2706041c02074040d140100090290030400c840d03a9110114084401d108006540580b40b2a1001d54040c0401c2d00c409005444044200340303410b802142000c64080941815000881518410000c95a07002c0e11100c6103409103080468508080e0400c20500c41707412002c02442c00101e008002c01c00003006258001074060300c030300c03190801940d280c800000c031050003a81a184c0c120805000c070f55680e9034a090051403580140d504459021714810045500e0400ca0680c14541c0c5503030b04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 880711789 1250 880710539 880710559
    0xe070501030e061b0405031b040e0a0b0c1c061202130b01020a02060f040e010b0304050c010f050a031a09100e0a0203041a280207020f01021507030c02070e012909 71
    0x107900d40488907055401041c0141c10040098a51810055101062481c1d9104c0300e120311001f00300400e2b9494030b0400c00065008101600204184400d1190400c1495240303075954a0034a021032a4500d844407401c202d503182c8200024021380b540c0c1c124051354800c4811034803500100c1900b808558880200c0360040e40030070032a4005050000042007195030080c249401c00d07540305100c1101080036003000300034a1002c0244010090700b00b0100c100c0c0d9400342041014070040e182d000b050350003412011010152038012445d0580c5020403c440301000140984e081498510204d050004c6144507402c46894010009240a21a8030980e4007842c0d00180341c2a13000c00302040ca1341c40c02d002900c01c00903400088854105a101c15244241070440f141001d40c403030309940100650b4144030301a19041d508401910501100c0342c01107650b000705030b810001002425294100d1034405907800001c1c203400b880001280c81148256010000b84040c041c2c2c15208601016180381405030100315504002400b0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 880713039 1250 880711789 880711801
    0x7021b010509030f07060e01110d08061c02030109030302130e130b0403020709050103030306060f2f0a06020c010f1506022d010c09050a05040b0a0e04080f0d0e070501030e06 76
    0x64010900e00b5402421102c040400e00c1c2050304104107a03100348046240c400c011001c55030411818404520440054060702400542c0641440401030110744165101c070041e8101170490a8050342050300030300200140c000c503140c0030707000794060300c170201004008420009152800700c0320284100c41c0c03400051070540040d030300c03800e1113600544110b06501030b8510103e0165424810176008601a5401040c954074180c0080c0c1611500c0c02c481080080700084d05000e20302c500e240c007914820a4011642e0280400c2c4428100114910000c00c1207000040400103d00b054022115101c81d640c0200f0600c00290344420710390025101d0500582c00c209100024100c4003000002c01481c402c49284c10340b850702c0300d0282181e4039000b0300004101030344002c3c44075003440258800908401d4070100941c4807600001203442d13041c0d21400d41d160003174100203010010b06609548560390b00d44001a1215041229400030300000c9840141c1403080070301c009000d43c0b081c00380d80c40b0f10907414068000c80c0c481ca = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 880714289 1250 880713039 880713047
    0xf09020c15070203120f070c022202070b040606060201060e0a0c1407150b01080c1602030106320306190b0102120d0c1b05070b0307140a051207021b01 66
    0x2820440340074045041c1a0242a44640e5200d29040c0d030207959185049107044000b410054481010041418104410540c01c09401d02c00c450b0112140756002014040c05041c0810560712030b9040e03400422010b0400600c40707440f40c0a10703c80c80301071240907110b40c2c0403803c80e112441503040700705414021405c480d1a40c0c0c00014208418640041141282e140e109981e60002c68115582103148201507005202841040742701d80003440d15884505162035040e046000344020280030b2009403e108003103503004d500a4008001c049400101a12520740007000c1300010f07151720f003c13244d00110800c030794079010505c940302d034403502c17004841c41354039400c000024981a40348a0540c480c0c29240f04010f00d082000d820490820304000c951300160060050030040c10018440c030740a41c1e48400e000140b0045028410742e03009000c2e0907183da44d050030440c2c1031001c894004480b0703100003a00c4c4c80403d500c48000e05448002d0400c4481c6511518422640c8210012501c40000c51040110b4101c0d845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 880715539 1250 880714289 880714297
    0x50325060c0f0206070827010807142808090a020a0e0618180111120a0c0c06060305010b1e0f091f141c080d09030918090b0109060f0902 60
    0x1c078281c441800b019808a41294041401a91a0354011401c020489440107008140b40121100304040351440c4001030b04440e070181590080c8400d4030300412541c10f1010540c3d180351418500d00d80301c091702030004080c0350010442800029104000682d8101c0002017103012a5800350060302424900801072441000240c003240d404001e1782c6203480c40725020044075000e4008904100e01800f106c060081c00c4400301e54140805c03010600070b0513001c104500b4244e500c0f041c20100840c0c85292800c0c00c40305440034442c0103119a04c2d04c400481400070550007402c1412059031841c400400c0c52608501d450304103580c1c160f0002030102c058601d810700e084000d0b001101c81c4550100c420105000c07010b50203440d084030040301c11001304540c2c07034680310b03603124030118501c28031480381c83d20340d11104800d01c01c100c40d480c001d41e150040001058400c0c07040200408140704c0214800108944140c05064520000e665485d505000032821140074801c086c21a03040c0c0003c6482c031481c000f036070310207900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 880716789 1250 880715539 880715543
    0x201171501030207030509030d3908071113020301181116031b08031005060a020706082a0c0c1509150712080f0a020a08010315060816050325060c 64
    0x50140302c0400251410846858270481549507070711403038000d450015181c00b403c040c06d084a403001c1c58090000c4d280d9404c034020660806150340c1d580f14039040c40c11540403440b44c4036800800b81e41c002090100d05501a6040c0c0b0103a68103801c0d81c076045034581c2d0940f42a443c1030108003008029810010f400c0c007824003101403007070601452900c0504c404d001d003800d4a032801c0d036001c880002042480d0344100c12040140c88203c510500b000304d00b910081d513a21003400b0307072014044044082400070a04500c250300844080c40d0004410640800b898400d0308500381c0e1320101d10903241009024a49503000c503150300c0c0616010390801c80c03c2070070466100303210046aa001e60701007029901084880403500300010141d10368013158180070722480c800b848000e010562041c8180f0640011a9110300035904481c0c01a00d20421802000601e900034940c42e840140b25108403050480c01c0205808441c00302c440c00c80a0b41c200031550791501f52030340d60105003030000a2540700d041c018107000e148291700c41c41c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 880718039 1250 880716789 880716797
    0x1a0907032103240302120102031317040b16030e010e060328230a0b06070809011b05010b0109060306260a0503041202090c07050705060a020a0b010e0103020117150103020703 76
    0x40340320906042005070b1030315549002000f0f0344050056040c03d0707000649400429000b149507241c031140b546d031103004402000340404104410700001e2140c074004e80e00500190380e0b1340c654a000e40034006081c10265001140802d034000180c01181d8010020b0b41e041610151a0924503511801e080e0300313540c058104840200b8000824a050101a02c0781c01c038500300131800058007840c1c02010f0560102c00905004402e42000c0009244d41ca5401c16070b0607003603110309401d464400980c01a608018068103d165000c0d00c5060081480b50541118211100a0b03c070040d0780364442c18124145c0e03000d070040700910714454070f900c0b25018042501140303844003030342030f1141041c0e03654549042d0742c025030144145001058115040d4a080e11200303400000306444a440c2c0301641e502c01da150b042038442d0602c07406010034801b020a0080c8030352000950321030b030701c4101580c540c04c0c01041c1000a010581c00220b0414654280b0841820303150b01405840c40e69004050200340110060744c0260344c114200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 880719289 1250 880718039 880718051
    0x2040e010e031303031e0903020906040f1e05010909030e0d0c0f14031b01021b040f0c1e020c0d151d01091a060a0504110c07031a0907032103 62
    0x800d100b030010740307140840300203038a0300907245003002848036149104100c0101c0c0005050041e407908900d440c0700702ca5056400d801265a003078009401411140020001a400d10000200c207440c0180c1c481045ea1908404001c00d98894034024101d0320024402808200070748004030142c500b0071800f6051174414a42001c10603198075590409032060f5204080904440d403000300341f85400c0c400c040350303018600c00308030549004000003941c44006030018038426407031094003015600e03030390030040410581007820f0100116107500144030102210103c0c0208406400d00d0221520102d4003030070010000b803500d4901e0b80740e034035050348281d00c0c0c0345500f01d90707a950203e10b519110b0350f081c241807040c010000042c0c2d001d0141400754501040036204012078910508010150365164005019207000b92030010f040081040a04000d00c14045c44202522032107600004012800b004041411510111160307140c9030481903503503c040701d0000500381d50810b00e500342000f81d03c032140c82d1544034600c1c0228003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 880720539 1250 880719289 880719311
    0x605090f0316030f2606030f1e0106050d02090606030702010219110606102703081207090b0403030c0b07120603080306120f0a1b0b0a0507170702090402040e01 70
    0x16540c04004240d01c050b41541249040c150029003104000c15a0306000300d1611900d400c241c400c1002c5040c59100700700300c0011464640b810440c400d1107800b61012200c0403296004080c48480c2c011000c105d103517003058404201c07404c024a200ca91281c1c0503100a92548a0700704010700c540000b44002c04541d070074058039820011401001413035207180e480e00040340c0c119042807030801d1030081c8a00d0141c000e6641d42011903901ca030035120110081d00405580454040007405c110402d44d0024261840c0440c0705600840c43d0f1107603900508858035801c840ca07a070780310b820415004078800179001c14400c040d00c20201d4440d00381954403098070302d0150100f076411290f14040b58082c1c0c2080d18207840c04420800d150501074896110009190014540000010340d055515084030400804008803403681c24034900b00c00501c040604119408103031145c00b2128010b01d150401c060030340c3c1100c20099100640342008007207a82c1c4c10340207000000b090796240c0034000900f0b400601d0711100d40d0303601c0740918 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 880721789 1250 880720539 880720543
    0xd1101140f0423040b180603070308030c0901031d0606041109100206071206080c1003020f030c03062110200c0a140609060a0c03110301091b1404030605090f 69
    0x101400c0e0100101d890108505481c0c1c03a09450803c1d00d6024620b17050800002d070761910b500b40c0c54081c54030505003c0343c1c0d41701c4c00310f41441c80c16800100003170300210922035501252006040d25900030390b410030030150311a15034480800d520030320413a90f81141e404101c81d810300c0e8106aa10385034452002d483e221408020400e41ca440924800049e04080305010544d40c0c41030040503203000588003805014182000e0b142c4880c580c0007024443d00320b8804001c0c116000b501038504450b104050a912031030904004843d82d401204c0161107000302600c010641820000d00d015200d404000401d02c10b03c0c01c12a5400400c007040800c036200345000001c0d00f0b6000440d006000742901500034200c0c000480c98000c0202c20178076000c8485800907000c012030180002080c941c03010414801090310034088130160000c0410319680c141000c40040040b540d224180c000b204000b1058489071ba014814042c01c940400003003074026511001000100003040c0340d038104130307042074004094900c560401d040b03240c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 880723039 1250 880721789 880721797
    0xa0506010c0b1f0f171b0609012f06150a210f060f0222050d200a0605040608070306080706050d1b20011a0d110a03030503150d1101140f 60
    0x12601c070780209001071003000140f046c060001a46640764a00400450005441c1d016410102e410840948040d01c481c100b100e2071b800c000707400c0c0308654020700c1c804149a5140c0340304440e160381e910302c0c840303801c295401e0100e00201140d07450855494407003030250001c01c2d140600c2c0b106880c0070003e82081404204a4440e21101c00c1c01420f0050340c464942600030b05880200204005140e0921001c000c0354a910400d0907d0036030155803814007000104103420740103440e41d140d6802c40c10340d64020030416040401801a2251522841c1442c4d135111404c80558203180a480020303040300c40c0810043c0e000300090b100d02001c0c3d040c04159a4070780a42d003a800d001000d6160b000a41411907070300c825030030b50303c20046008680c009100b40401c10400c209c01d08086001031340618681001c107014000030140f260030082004101613461596400d0080a032b400680303c041d80c4070b00b801d28411207498a0140c020000364020080c40c11701c40c0d00d0006490100e46100c03e0300540b1001c000c210003501c0841d00130 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 880724289 1250 880723039 880723049
    0x32701050a0333052404031b0b030c0414042a051e030601170403020601051c080d0b030f01060501081b1e07060506100c020f270a0506010c0b1f0f 64
    0x40d007001c0d00c0d00040240c503500c010030f00302000704500c9440080c042c02404030303804c0d01d820000f0342030304e402c0e410000200b2230442d6014820081c008401d00c68519004e100400c1103961703810420003010032070b00401c02150b0b180015100241402e02e80441c0d021400c0c1103003404801607042c924100092204082200c03011100466a12940001002815a001a1208651a16095000201e02d001d540183d030700c032818014a88580003940c0d44498200d000210800401e500161054070340400304000006080ca55105601c68000c25220100001c414401c1d501210303816952000140c40b0115804207005505281391000c02e420080b100011081c0d240c0b510f200b088125650360b840d0802d0a040d4215000946800c2c4102060410048600e510140c0701c3e180c01d0b01204c242c00c00d148400c00040312034019840b0078070300d185031008041c1c9100c0c018080c2d61196240000903c07843e52148011210801030000003030407030b45c0004c0400c0c0031442d00c00d10f603602c1d12034940701d4103216030f110105014404d070b9503806 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 880725539 1250 880724289 880724381
    0x6040209120c12010905060a0207050102070c0b070308180c121014010e0106020c0a05101101060f1701020c031204030e031203011508090712081b032701050a03 70
    0x142c039a41c14400100c49221541d4002007010001654580d80c80c0c240180440d040c498000c1082c50030b000080d070407181c41aa00a8000c0c951503642c0300310b100290403050066000c604e00c0f100252006c40160b0800f01c814840c42c014104120090040185281d04841101c580c0c1c458014440d81c02c0000703101d091001c070503201c401c001c590705d0b141015140100580000046400016504105072508000d000a07124201d5074550314400e10300d0110b0b0821032607090449076600b001000034100c1103007440081522510051940c0d142d400344941401d030320420106030801d60080200c075040d405518036040e00284030b8a040905100b001c00000d01d00407520303078484001000003004001001004046601019150600080703e1410100d000e440e580903100f003031068580132a11008010041045800c944030035075800c06007507480c0b1202d030758039000141d400074400414140445442c0d0b0054150341c645a05943d0706142a42c072000232009010000001e40114001d0440409902c0280070b50250312640060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 880726789 1250 880725539 880725553
    0x6061202030d0201020403030f0c020301150b1b01020f0406140f03010e0709050904030206071107120507030b100b04141c030e040c0e0105190c021003150e0910050604020912 76
    0x416060800740c4540c54150781c810002000000d1700500b02c01840c0700c0c503042c002b002c843c440c0003190240403070984070038210030070301804a40d500c40740028000b00c0c00c1c1517240194510a241080b401c130300c03544908040200050104004c450311900b4081d805400c503140880c01c0c0640c3d48013401c0300e500283c028980311607100041194003617101824100510b400ca9900e810303030410384c034082d446c1c43c000741640b010000301c403410401c62402040b213440103104204100c42d01840c14280703e5103503550340c04100c42c1e074034800001c2a03401b10035080c035400f540c03110180189054030f4016002c070111003441a4507009a03482c000900c001080c1c49100a601e80203440324507201c6e0100042000f2101502250030601c066a00e10100036684041528900400c40c08001c2e1200307074035034080c2c501c012401002544580c40b40740085009515400c1a0117031040c4003000c01d60240c81e104480b05041c0c0480b40b00f035460f480b2128549002441d07822282d00010301910051402c00c149002c40e80c0260010b0510746c007a4800b034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 880728039 1250 880726789 880726793
    0x40b030a0c0f1a2a0309120f0709051b071a18011409030d09050708030408100b0904120f031e0e0f0a021f09050316180905030405011b060612 62
    0xc81c03e440440070000110316007140e00c2449080300c208211401041c201d0303440510b880110400c1150040d031702c014850780d0004101a8000d83c0d0314802c03402899140506100001d8151a40c002c0600503100c212020385070350510108c01c03403550044c1d60156503d40152210460303110304c14030350600504a442501507166000c009090950340c040e40d20b1200c101c20103042141405002c01540d040340407003400480c0419050400e6442e04015401c03c9829000001e0b0018103143c000490141850741940140301464080302040685030007260041c2200c104981c10052491141c2d030040c01c4803000f801d000807403103440307080801d03a0340303031481d48151080d9079070100300304001c04001e04907407007072a80024840e290842d07010400d0100281d001040c940e0340d44408400c0540a403075810701504001e01100e0007905450844060300c800c5110398454120144d5640c3d01e0540c8900990040307170b0300700d4000d40c5428540001142c4007104940c40c01407043c400700c401e50000f0b4840c047d0300020b0030340d02c4002c40312401c98 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 880729289 1250 880728039 880728059
    0x203090d0903030806130e010e1c030b0f1201180c05031203130f020102120d02030403110c0d030f050c1501090c11070504230f040b0105060711040b030a0c0f 69
    0x1203408280180c400e4108000f9900c0340e0003a030710140c00d0303440001900310703008054050401640404181d50030010540811040010100c52030308403082e0050f50804c02c0c62040c3d04071440024401d0708020100c1040c0780d076050440302c114200001100001e42219904003030f58803141e26074411258155810010000c9150070070000640e0396240c4030840c514203048002c1c0d03141c0c3c0003101c8020004404d061001c025a0300038030014401070222098035580310040201d401c02540126003c40c04102088080500041c0001d0070302d40c0024040c009801c03820701c0e42c81c10348103960489103100400c0010041d0000c400c2050010700c07078003c50300480c50707290750402e188070042c0e40030103120404103d031001e40411901e40c002001001c542c4250b0380003074240c0801c020840c81ca14590000d1400818107000d20106900000c0d0103482140101452402130b40c07a0010025107100d80000900607a808001001d900c2c5040c0d0301000c0e202e0700c01400c40b00340d0000d40c4e44283c3d91948551150800045809d0204018022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 880730539 1250 880729289 880729303
    0x20a051e010f021204030f0206120117060f1303080901060f030507030b130807062007050303060f120307031107080a1406010504020f0708030703150824010815130c09020309 76
    0x2c1c0c2c00600450101c0404011140c000c1d840090721a076403101c0c3d8041551071b08400c444c5038140b00c0070038404942c0c49045240507145001a900380740d200760400200b183c1040c00c066800b40c40e074252284681e03001601d003100e80d0301c0c0240004585540c1d602c00091200c0306c0c4c480060040d4442c002500d11306140d0704010080f050000c0440607160710810405000410a6084403189588440300041c1c0ca00f81100c0e000040c0c0307100440012a00000584c2d106005e000070207544208801c46a50303010031980c006220740a482410b80907829807040c00780b500000c0c00340310707444a03032452038003182c0086984200407031500c0c40d0603800340d0b007009007800000030643c4140305050151000b66403c1d0314006070f92840c500d4600c00d002018001100c040b001c0748401e4800e07088441d040f41d034090810300c401d03146c0500701d80720544032008204070390040c8401c4085c407030201c000e0741c121807131400644140d280e0b010303422808820003000494441e880907010340000b21040d0011003c0c00ac1c0301ca0068607490607200311490000c07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 880731789 1250 880730539 880730567
    0x324110d0b0f0a1a030c0c010c120b03070e0a02070816030306060206011d040303020a0e03011b0905120c1014130f12051c032a03150308040909020a051e01 68
    0x24451007071103055450034100c4c0c1150310310300e145566941d802607045c90034058210020381550030b01d621a00520381c4400c003000713414040c120410140800c1020595115414072407010700d004143c001900914160b0b0103420141e0140540070300d000c510206168407900007400071400300380d4030003061000390390401019015002222040e5211410b02c528403c80803401400203042507000a11f00c254140300300e9006000d00c0014000b4030200284001220f41301e05060070704400100003460000e002d00e0b01503081884c109490010745070425030312042c000c4140307a020040041c4444403041001c841484801401c4d0908040c0541940b1410104040042c50180c7c0c40034040401c0d201a07030000c55804038600c0036100b0070800100642c05404010380141005030381d40902c442c442101c41e65003150b20f284109109480360380c1082149000c01c14941841d41d20300028107200c000340030501000410b82e12480d1031340e0000f07081c9524142c0d1000000d041d84a414034001e040c20140004541071358110000c1c00a40c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 880733039 1250 880731789 880731799
    0xd02040801200919120302150a0b0a050f01091205011b0f051902250503120c030a03090c18020706050c0c0c01180e0f041406010324110d0b0f 62
    0x49980d60044010f014402400303100755022180d00b10744a030302e45410401805841c40103000c4c11250300f0040d46071503e040b00a03031300035512000100c1e506103038410107403407140080100000509101c144030005c110b0740c04c85030504c5184040800c83c03100c06030b00b140800c1d04c80d100208603010308031030000f98600d00361041c109005401104000c80c0e9081000d440b0340e2035440101354a5080c1549080341f40a00103010315110b40c2c00c14407084c10859807003440505640042c3c0c02c958002454010000b114451385c0702419003504103011100d0310a1207904588000d03401100022101d6031a080c4140040c888580ca140b00680d00044080c2080310714010f45a1004089035130504040d02103040c1501e80e220040c142e070400c078103c130b00300000c1440041d910300642101e01c0421881d1401c0800684166010348040d80e041010020900814200050700d81c10f0700c0e40940d9004500c210280c16501244446100c4a645510b40003025400742c1d61401a101c0410684000700e80d0320303060014021403621000c10f2501503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 880734289 1250 880733039 880733081
    0xc03010506091f150509030c1c1e06060f030201081e18011103040b010609270c020f010f0c11060402090f1003060e0a021305090a0201050f07080d02040801 68
    0x2e0b52011405580304810340071180070450400b1401c241c504a40e088240c2c1c2d1000c00c02d074031543c1a03225001d051102e0080c0c0403200207112041c20000900c4200662801c040380f018400c2c80010214202a032004024112640004207196515400d8071200c2c3c02a99101000c0c001c1041990782c0107103644e8029030311011046107808800b0100200500040c6201c0f10030409003031021400c50254092103540700c0c3d803c0300a03220b040030301c0c0059849500703100361400600c4031f0901060030f8509403004011030b05c0102074481e11600c10040c80029002010401c01503004101011081c05404c1c003a441240f00b88038400038410214502c09412103082d4402111980d0081e000c11005807940205550070048400548146a1782d8070b440c06048003150300000d2410b418400520004d000002d101d40e2400e10071103125084914800c14802203c600302c500384103d5218003544000355004500422141c503240070702901e0700c03480c2d466040a6500210700038442c1e640c0010100440c040c01e03c103402d26103280910a03441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 880735539 1250 880734289 880734301
    0x170a0c0e060a020a1127060312032e0b031f080d020a1106190201090b0a0902010f080403030e01060e10080f1002090a0f0605130f0f030b09150405030c0c030105 70
    0x83c4021512004252050091300541c03640d481000703070407000450442100c00004011b0240001c4030054a000e0302911420602c640c00012000c25a84600400c0020000c4421805c8800d0f582680032001c0b42840c18a00c10302240e2501c0550086101e005551740c020040e840040c41c1a011100b20b51005116401c145a40a040b030b501043c1441c010b9041071a00c1136911811001454500c140305200702c140c4404140d006105806402000070140140ca55501c25540c814100043c0c0744840b074028002283c602001200b18050250f26070054000d280000d5075000103403020307003102c03401c0c0c00404649407450104529a80e0f600d503a00b02501c0500090b11149030300c84d1010743e07984c44042c15a420140c01180d0303e003c60b212008500001c202d0b601020041c00d036620350207011a800010080300f0035407480c40209130b001208003100200c65450300e1583e142407a54607101d801307002c040c1020510740101804a8010038151010b0360007103016101070b541d078401c02c01500d0f20f40703c1c600140300d0007030341080d04000c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 880736789 1250 880735539 880735543
    0x70602210c040b0a030f061706160504030804030803090109050f2d0309060d0b0904030801140409150f0612230c030316020f0d11040e150a0c170a0c0e060a02 69
    0x41c8007400d174203000c68140d11038542100549559003040e030a5032804d00c201611800002a03c0740608003031819491100240b0708100d8440c070a501000c4c0a94401300f104000141c5c6002c002d5501500090001520613019500c581c101800b0980c42c0c00254818800c440304500100880c40401e40d0030103407604903100032020282c5a00a1106061041f080400c030804500ca5641200c1e50240c1d00400c001c0c01403603d85805031850000f80a03001c5182c0b80da04040300681450300c82c9503861034200a00b403251100e4551804040e100780c1c0000c18100e42c540200145800b9200d0044000310f200348200318100021441d104e48060002a4508070b55125500c0c3e8183ea440c080110b81032000e0155084a81c0c3c02d05001151500003508030040d04140340350b03001000d1002e0510300c9010008222020320801c4409000c0581d02c0c503412408009011070000403e11800340c2c0c3d40021003505290402d41c0c0c0d10b001c0705039582c2c201503040b14075104003520b03414540350712a801080c4055112007110403d0a001840000075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 880738039 1250 880736789 880736797
    0x130f02130b031014031204030c2d1511030f041406030f01141824010903051005130218090c15030417040f0b07110f011211070602210c040b 61
    0x1112184c0010002200d5072418410400404501c1e228290344540c0d91a040441c1c0c040c0384034022000c10184406810009048100324201e624919035014003400c0040c021101841c5003894418051503c403801e0700c00341c0c141f0141407041c000c0307883d02d5100c0e450181c00707100d0350041c2000c140c072659040003082090b6500f5502c05040d241d600e054240c0c0ba100210115812202200e03424880890340e03420400780c140da25003070074000c4031140400a08100b9810064454418900008000760040c491008241d00036a014960103500c510030705200c1c085a1300824a0f07400c0c0425400c542d00c3d191020090130074001c10003034480355420349100702070001c00c11076524540005440144480081c50082400d144030380c3c01e40d0040d050026a0070600c48d521902da0030746920170300d400c80b2510000c07a6160101e2600400c481074544040c1c40b90300400c00c001812400400d091074480403594000d00c808008104548080c03d030702c4400311511810511450540c1a48410060001c4d652050802c02071006d044844141c1e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 880739289 1250 880738039 880738049
    0x1050d02031b03010b0603010e04050709020309330702030304141b0d0606051c020a1401080c13080604142e02090d082d03090d05030402130f02130b0310 67
    0x100501c2140b80000b80580f00102e6001c0d400782021001041d03140e68118110b004d1407080303080340d07003c0b03940c0c910000582c001120a0501500900c0c0b0011814001004c21211590110010551001a042c004000d010b041c1e4000340168000700400c002c00900924011041550780000d2215007015801c140d41d04198120301c40c006c00250582c03804005564000102901c0300409149440301c0402c040c14640c1c11605080c0e00c1540d41100c000354032540800518200c01e410380d00c0300a81e55510003100e0055000c210310144403181c103000000c0d1070006000f100e00441c46886003c90112403018400d20305441314000441d2003002403084104482090700440c03034038031016000b5854101d10000a0f0305003481c2000070788044000500810508021070007892002e90100c05c503503104000103080e042c80e00003240e4101055100418070a1854002c00145031702c20300c003d241d1103403c00761b100d03004c050322144221700d0701c03198001c5002c40301034002141107809050085100c0b42107281041c06270442d091140301e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 880740539 1250 880739289 880739323
    0x2803050313060c0213090809090702010203060f01080907061803050102030c0307090605120106200102070b0a15141302040503010912030b1806040c05090306040c090501060f121d0106030503030105040501050d0203 93
    0x907207420051587c0c20f071244550000e0002a6a241991020b4040d501c1203441034031404440e40b003030ac580e600800705580152905801001d0302801c020081c2e8032040031082d0b885c0605040d100010001d442400190321074411581c2241c0c0b20306003420090242c6110b42c009000780a014400d120001300c2000000381100d080b0700c1e201d0408500050325000400c02e001290489500014096051002205049018140a4031f003001520048062401f40f40c0d454051802200b140d003903040b02d580b505800300c0d0400e1074080001482e2039641c0001074211030f04a241150403500d1800c503440800d805115003841c0c0350050300c510300003448400101220010003040a44a80c2d0342e40880280325214105484600d0000303011981d00d41003c0c204110100c00e070388160720f69107003000d0000c14a144a1844c4d44409032103519481c4400303481540840103488500b1940f04041c50b00240d13854203100034081c0a0003940550701442e500d50600c0144020f42d0016000f541c001c40848181e800140c0340050034030a10176403600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 880741789 1250 880740539 880740551
    0x60406031218080706080103020a080f060f06031c110f061b070804031a090105010501230304031112071406090d2a060e010f14062803050313060c0213 66
    0x750b2060450300a42090303e1610900c0c0c03005c505035801c004164140c900803941c4052241c0c7e20011135075220303000d001c0b460458201c0404103007501486029150080c0b001016100310f2404c149010740500301002414000400015503820020010b010150002c216000584003c0c5030516800e4116040003400140c2aa400504641402000015140a140e0088440e100c2240007400074003402ca003034400c0c030169480c0000004056002d280c1c02242182046070680340c10910030b003101056080140181c0c04e109450a1b1175003140c0040c0000004107010f079181603111105402c10010000c46010010601e03840ba07414000e50400000c0c0304021040c0900e000720142c4c40b100f01501b6503188200e480c9000d8003265440f00d0400816400018881100c4030080090680b038404c00410b69842c00c0c0724861310f150450215019060615079041110b07180b00d0000c2c03051142154142001d0703070359030003a0b5040c0c0001c2500f0480c80e2038071211000402440c46e000841c03078003a80008802041c126028001c04e50307249 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 880743039 1250 880741789 880741817
    0x9120904020c030f030118140103031d04050f09010b03070b0405210d0e040b09060a140402040e04080901081e07080a1d1005010603020c03030a0c02030c0a0f03080604060312 76
    0x30301110504a400019070751545001010b400f1135070003c2c081d113120380303400062401481070a0310880c0c11312400d0300c00000c034a0740386840c10303035a130705104034050030010145a8070803803038807203010f49405042c401d00d031040189442452682154140b002c401d200360401c040801201b03040b5402c3e02c0681d84100c403481c001504400c0010b4841990201111440c0990b0081d0005a50011070f20380c1c80000070303203083c0a00502001044440d030004c448007030f0700c0b0301440010b10000105061a096458016100620707194481c07180fa1a8051300325011614544001410982540c1c46804035030404421041d08851650320501e00400c404000c000e4810040a01d0010b4072074940c680282c80106c501c1120002e021310440a560349031241c0340d10050703900c0d042000000d185442807084442c0c0c04446006907007551101040e6901821060828100718803062106201d005010308c03030a081e07944107594403103c411007858058956840141581d01c190301d041d4007000418a108900d0510040354034200303441000b55 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 880744289 1250 880743039 880743041
    0x50a020f0f03102c0303040c15050304120302040b12090d0c03020a080a18081015060c020108041104021c0c030b0d1113060602010b0a080a080418020409090c1d09120904 74
    0x4c8080030400c080c01110292800c0b0110040d40254090410384115a40b141601114055401e030200e000035010400500401d0f6424881c8803409454900945400d5542d845440140c210040162019481806000051000700990fa4068a0b07500701080c10400b90385000c0c0d2143d40c810f0014201c60000503070b03038018500c106170390103040a1102c441c28071940c0b41c0414580c2c03600441c1603c042540342100303151107041d035202c848048a69070303510301c203c01d00103a00454001801510440762203c0c1100c1e10b00c2c0303c0d5140d001402003482214004901c14010503506025a0000305e0074400b80342c600b9416000303070b4440105410700c0c6a002218601e4005482012901c07154503100b84030312203403900c200403036500d074190825054554105c64650750203031500c11003602c58181e00f40040c036201003080b0810101c1c00c0c918415a10091640d40181050340e40c4092100396100d00000710342d081c0c0140e80030b220400507600282104030f007500c080c4407545090002103030f0f1864065074034025031a01165141a030b50b12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 880745539 1250 880744289 880744331
    0x503090c0a060503150a0302101404090c021516170702193512131e02100c1101080c090a081c1106060d1e050a020f0f0310 54
    0x6005401c1d500c0d6501001041c3c0d4100383c0c3c0600d0000700c105403820451404800c50401e90303400400c5152003031080e00041c1d440c3d40d500c6082010100090000103901c031818403c0307950007100364000d094800741c413880e1050700110040c0b6540e0184142c0d44040d020551000c40c104a12044221480058403401c409910309502d220714140c000300c240105c4000c21902c40708a02121002c80c0b031203511317080e07101070356000c3c40e03441e200030841004140714a4041441d2040403580000301d0705a004044001c5840b540c0300c4110048500044401704403062003103007055105031249405038501018400010f960305c004051007104010304101c410800305282e0800070b0100c8250034402807400301200d40e20a480390700e44181d9504000440101100104c0d01030081390604d000e00c40d070b000501850f40d1030340c080010f20840e07054152108185000c1c001d910703410030030603010b241c1e000710b0040400420038810001459094a19140503080b8403080b4003064400140001200c0c80310b20b80424000300841400b80d248403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 880746789 1250 880745539 880745563
    0xa050a0302250b060315220b010e1009050402100c0309090f06080709050c070f050a02130209040c09050a030308040602090607030f14030708040b0a1401062c0a0303050309 75
    0x14140300d401020b088107040e1410603071044201101c26507844c000c050705c512800e80060803001c1300300001941102d102c01d0a1280c5c44002c200d80030084050f03140c0c4d600c2c400090300225030039883d5006000e42201551405002055060001d00c100d10303003540800c001100d01100f480034842c104040c1030415002c0d040d880084e2104480401c180c441503c1d8001c041c0446108400f0f46025903040800c00794004c2c0205032068440960440c9031102036907468895850703000302500c2500620100d9001640d50480040346030001031405611401789000708002c41d407071401d0980c14800c94000800c25034481d000024112501030820010a1b0764504250003c0d2203403c503200d40c48003000401004044e040780c041483c0d4103a1740e0344c1e00d00d0100010030344000c51005950200c00b00e2904000507002551048903c0e90100c0c800e50042080316110a003c0c4503881c0c280c101c1c1001c01c18014902488002540b40e0060002801c1c441c1040401868080303441d004050001804100000002402c40007042201c130384100b03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 880748039 1250 880746789 880746817
    0xd080705100e0c01080a0b06121b07080a11070323030f040e010f0e010e010b1b0d021f0212070e031f1e0510050f0d0506010e090d0906050a050a0302 65
    0x101035007a406444043c500155804a00c0d82c10108034002c016100e990003140014142d249484a80c81d4128400c582c01480c20100c40c0c2003681c0c0b0035003110410041d040051160724140d4898004001c050465503512154003c00d502a40080000c501c4030340303c070400b40d000c03255541050b802e2029090300314071030001c0011100f0800580040c603d2580340350170b8100d0344441d041c1055943c8940308605000028819042800c0c5102c005010440060004007040600c41d03003540001c179003d10002d81400300e54690301c40981c0042041c0b440b1005800d0b14940c0c0c6010a0a04500d042c001c80031809090300090415010810341d48412030300d0780c504003d1240d114000c030305401c2210000510150181c6114070003036154862009241104c61051b000d07240c094411800c1c4034101c2402c000a0040b06400b0301c1225900580010300c6401095050080d680681183d105059152600d03245035850460001511408c00c190004100302c9158040c080d03d08965181c9021079440d042c5040460181c028451360081c18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 880749289 1250 880748039 880748051
    0x1e03060e100602070803130e06060d15090b03010b060d0b0a080f071a070b0a050c160c0819020a030f03140a02030a030605061c0513062d09020d08070510 67
    0x6105407107441c821242240d01300c81038982c64481d0640c91303001d950b803407a444030034501080c0942001c11880384c0c1c0c0418060304450400c00d00041000680714510790140d643c029260007800507941e5801084114101500280700000311100440c03840d01c14a40350901541c0c0c0c528102e01ea560b1010041c00050201c0c004032424450105940f540303c030824450140c1d041c684800703c4295990030816160002e800801c0d404d40d0b41e64402a4801400b40100620b801c0740b0200706285504640c0b0003402100740c01030010002050801c0071040c58000c0d00c40c0c15400280d000010f83d00103035214001d03076003a00c0c0d0005180241e010503140607100e00c43c140c600c1c035080c0c030800316007021b0003a400005000d03113240c81c0c0d4040c00320316a1101400317804c2c4500c402300d01510050305490b030011915a04180d4005035003d8090100c0e03c040e4680200f150081b4142480e61b001c0302600003503402e2109420030b808400e0300002c10454103254002141000030700c0c0d00400514000c200a41800030501c0b141d1011a14850103001d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 880750539 1250 880749289 880749301
    0x2040917130602060f0721020a020307050c0d12141314100c0503160510020408060f0a06050d03031d0f100e010209030c0d0813090b0406090b011e03060e 67
    0x10740c029080d158084074041c0360000b885440091454040e6200344d0144100d9110070504688030303404000241c2d00b400c4040010085080a8402010360221a03800707151100304602e42141400703880d625841c03042240f825803001040302c4a4800521403d80d0406010740280c800d81c11005002e110042d81c0d861081000010301160f080400b000a0030342140c0c158107005d080030b41a61035245850b40581154400d21003107035080590106024000e000d90101c1e407100303043c801c80ca81640e2082d0028807180e0004000d0258100223240303c581c0001e50504240008d03401c0801003071181110183c007030101a100c0001120751000d05018443c5101800c040d1030421400a64150f60380b1001c00309822064505412807421403018401d41b041c1200003400703490829140420440c91441018042e5000342e020000c0311440661165468002c2640940205007100142c040008440899202107074840c01c10758482047c1c1c1c1c0c0465440100207081e0b89a50f01c105103620304800525040d000103586044e0201441a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 880751789 1250 880750539 880750583
    0x18270f0c030c0c030906140d02070c050a0b161106121501020610030b01050f04110a0801080c060f0a0311040902070501020c0f01090b0f04031206030809010237020409 73
    0x85010068405009040e03140c1c00c12120f990040d80003a00042d280e050921117144100480140350b2800101542448081c0c400d001c101e0380f1483c01220580300141c401c200d5030511010312001041002070190403d0343c481522883c0030354241c4010305240d0700040b01d255564034001965820000d01c09606d40c680f5004240c1c2034500d000c03c5e04907001d4424480020b10941141a0203000c1c0d0b5031143c00b0401503483c20382401250003852a000d0703409610f4000c40e2440c1e2100340060658180d8a07030340c1290070351420680b1030801c40140d4509009030810002c03000518450002c83e07400130454a400179816200c07103072a00b1107000d00d4100030015400040d08005101054018002e03103103140e0107440003443c000d900344d402c80300c9241300100745040c46000100400381000305035600500900308645c0060007840d600e01180c2e000e0b002268001c8002c243c480280d60b0403c03201005c05c0e0810610784101c80290b1a610758070040d03003c450310801030030040d542151103540081e100107a22050755110304c0c4150300c52003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 880753039 1250 880751789 880751801
    0x20c010b03011a06040e0901090f0c0312230d110d14090f0d050d060e01060909140f13020d1a011a030f06060901031508030307030c18270f 61
    0x14841d43c02c0407410b00c0c80c00c035071018054504500a00c894981450513080c0c80304143c0050911415540c0c400340720740070401340516548020310440c403400800c0d08603d00900d07414400040e203010400b400440c0a0444004240307505d908a0b108070882d107543c014051136014028024032840450400310f03002e0310000d055002aa0b4011030043d410f2016661028002c0e038400c480c00300f801c1c0641c020a41045064040d400412890280310000b0400e2500c0d1101201ea0b64400e0b0710400c0003440c42081008200303200d1040e102c1c3c0c4134503552a0210740c200410401e9646030041c2050840c80706012848086544003640741c595580c0c00300001020002c1c0c1c4013012203a880900c5a001c1880e005480ba0043cbc2211000301d83c4a09050600315116440701c0d010b1103995000030040a0503d507a4101088008800c3d80c000001843e422004596901d41004001c00795100e10850300c082c070411000284404c50314001030030545801580f95825420745100030346614409183c07004206140890808e03078448950059 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 880754289 1250 880753039 880753061
    0x71e39050103020c03250b040807110f01080f13141b06030405061f080a0f0201180e06100203040f08100b1008130203011e051f0f0b030613020c01 64
    0x1008850340c8000641c103a2080c1034441c0301680082007120f12840180302000c6181c55817030f00106101440d9520356030300050594060300ea001d00402c010003081040c4030800d00d034190942c1d0180040842c000040c200f80405007200030712403148000200a011a01301c648100307500640c0c02c100809010030b01079190140d00c901818108541c040002c0c4508081c01284e004560150052041e070351182040c891003041c0c404008018440342c200000c001000304114040a80950112014440b4034800500290101d070903404440361401c104018903010484107585c4250700f80c0340074401c69800d00e422030541c4200e4020010440349800c000c90544400121120281c650040400202d42d00b0420003100c44000039000780000c0f82200010300306400d07042c404440a1000c1e001043d40640d40203001c5d000d641c09a5820541030380c078001c02400d03243c00240709150f1340c504840c600000d41000301c1e80d18008042d00480001d00c3c4000013081c4903403a0318120480120001004640329410104028041d080382c0c100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 880755395 1106 880754289 880754393
    0xe191707110a08010b01121503060e03042d080c0a091d030d091a0412080403300c09080c010e030c12060f0903071e 51
    0x7424003501402c000172034045004800100304404099140107401d0801c2c11240b1400e000110310340c00e603500908045107410301c51510614601c502da0002d021030000c0c0000c2d0ba220344c48000443c2441111000c1a02c030560380d4901030f0394a900c1001c9283e0b0100d1242e0f01000b0407045030780094002d400301130b070484a0718082c1e105103086801c00800603046503120146041008110540e0114803081d0305c40c10b070b48505064856810041c1d03890320036420b2214010100d014107000f403450a4240b414620310f4030011410240e000c01ca002c0f42983d1540d038a0400f10a002c103a070040e0001010303030b41030b4001003901190000c011101010034000c000c0d014010313920b00390060f03181c80040007000d0382c806008203058180410505207483e0001e109500e241c0090200340000303241000d0302c0c5002d80a004110050401908141c11400d51240385182803652140814180b0850321541030f5141c0c01e5041 = true := by decide +kernel

theorem cover : BRFrame.Cov 880575539 880755395 := by
  have h0 := BRFrame.cov_init 880575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 880575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 880575539 ≤ n) (h2 : n < 880755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
