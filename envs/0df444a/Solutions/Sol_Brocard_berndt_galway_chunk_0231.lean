-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0231
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:37:34.786915+00:00
-- url     : https://prove2.me/submissions/215fbcba-ddf3-46ba-823b-e24ad1fff52e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 41366911 ≤ n < 41546767 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 41368161 1250 41366911 41366921
    0xd05060f060f03071d0906040b030c03012405090408030105010c1a150405061203031f03020316050111010e0a2003061f06030b060f0307140307030f0513030c03110c04 73
    0x141c200c0c640c00414041126030010343c10505c0b0002009080c010070180d07000601c2e4800c0a0f1013248295100c1c40500403e40c0c00303200c0e8000300362006000304060f4152130300310800b0b610404040589210728010006260a200741058812540504e00c10b16682c02c0200550301c83c5070a4000303440750328031001e01c0740440703429a10355409416290454401d20a040b01000213640c402040d490040c184502c00c98842d5100200b070365005243c1c60a000c102000c01007201032026102c0e8000303981403160041409a04000d00d41c1c001c282c441c20b82c1c0e500c6e1f003420012038060070f960601108170007561240c40000e0103e070720321001d82450381704504074080d54241000081c0c945103041d0b9884e552190f828071001c1440001907841402826181000d0280060483c0080c030640940124051b00c044004002411184100000034034021031400050703c5e420325050003001401005952440300b40303080d000c2242440070000c8510301c44d5040e69103061604007540d048030716801d10100755a403441112851491a50f0f28014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 41369411 1250 41368161 41368177
    0x6040e0903070804030605060f0f03100b04020715021801110a0305090a1d160c031709070305060108010b03010506010e03032205030a060e010c08101203050405040c110d0f050d05060f06 81
    0x202147e141800300802031030400381e403159031080c03903401c80e880c039140c5020510040242c03240328005000c2d9413150201c0c000e486030103030007469524451605e0f41c03005601c3e4068103044004100700c002e040c00c100e005460090030380000340f01da81c1c000950000007910800050503820805042e40d0704c00c41e580e47c0c614031032031110300c000410303c9110810040896045c074011100d0b08401c0c40d0a00c852025030b2006009044440c414202001c0388000094440c9401c00900c001154090102d506969486000314001c1c803040e803c040c800d500b01004149298460007040004440c010043c40c0340103c0041c00507065a05140000079140c11044005243d650a0007050b488a0041030081041c090030220719007110400702c1e5420501c001c0500b40304075001d074882100143c0300018000481c4d603200c1c2c10103890038081c0746d21190740581040717048804c3d00e034486880d5074540e085108031548520b416800381c7d4141a098920700000e9028042c188000c003c6800c160f070000320140410244800390300c041003042e406240 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 41370661 1250 41369411 41369423
    0xc031e0b04020720120102250219030c0f0f05090106080a0f11070510200c010209030709060302030606040c02280f0303090b07030204050d02040e03090d05070504060b0906040e090307080403 83
    0x8030000690a011403540384c000c260100031450402042c07800507000c0810780c0d40782c8c1040f01c01d4032182e046480796190010940201c0050740b03101075a81c5040110030300306003c1c10b849051500c1c0300242c061034102002041d03840051110703c260f8203143c021617060300000d002212558880e1076952661003180304030450f0310391800d40c50341e440a20341050b900e85003078000d4840311a0320386040704500b245910196591801c1034041d5035035901d038085015000e03000d07003040b031581400340300ca00207840032659008030201c138429800e4a40658940d010402224091544800541c2090b803142480f1001e50030507040c10a9084812403d40c81c80c0d4a54101e118000213045010960710716141084c42000b0301d580f46d2010a1303181c254a0700f802c0c000440c03c1c0a181040080c003841c0c40d00c0d00c40710548000c2c403d9618400000d0f10720b03440c0007a5400d14a43d51445445131900072450210080303101042d40302111740080b00645001c4c0b40a1801d56030340140c000c020700c00c02c400e0005120030400210020b00801c02540505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 41371911 1250 41370661 41370713
    0x2506090609080c0d05041202010c05100e030901030605010206040308010306021e041707051009150e03060a0902041a1806061603050403030801050907021c02011b020a060c031e0b040207 81
    0x250084c98002445000700c2070210600003081a012590664880254203207800700c07003101140b500614100180e802c01058904283c84200444000000340030849070907a014401603036518016600e540040e10090002040d02d0010b20202da4250001d2150740e48100b80044c81013111440d206003600150029a2010030461450400400c200075050150104030b400c8032603c41080340c0507058020a11503002c803681c210701644900c6015070790102d003105019041c0c1e0000d107854a002d000401c0e0b10301d000c0b4441c5e0315122200112030b1000480403103214001d0020320301c2001d0a00c000794043c2004100300d5021000300410030011000d85e400344c1d4180c3c880c3d01e03501d8a490075446c1c094510780050b00124010361a41c4104141558001204910300e4607280d0210500143d8000072030162110040700b4145610f800000100290300090586020b4010304040107521080281201560f182c070340c0303e0030034980004140800312160740c0000c500d440010700041ca0720301f203555122101e443c6a2540b49401843d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 41373161 1250 41371911 41371927
    0xc040c050403110f010f080915130201090e0106020309120313120c0b191b05031b0f0105070f0f030b040513050607020606060301090b0a0e0109020405120102250609060908 75
    0x202011a2641e0304442504c00c07245442c000802c6501c000f60450308012540000c600d6481050002e80c524801e0628900d0b11460640614802060015001c074001520190001000040507000d18182c2d4590f81c0a107150803416420000c0d01c0421202c12000c500040002024060701c1e19100f00041c6502981803c3c0903509090041c40ea008a52103a044071000300f28003964024184450911001241040c541c80c40440316100c0c51000e04c4540280306220005540c1d558040044802c2600c54000040b203200d034105500d0309003682d0701900c2c90400f04603201802c810242c0a0000c078101014075150008006c0502400101034581c2500c50b03281a072001002401400418041907901486030300052000d4107142002c560544814803031110841c0d07407591181070b25510070ba010002070801580c80030301035840b13000003c0294451b114243c81020041e412122014041c000d031210540841604000030554044410f11500c2050045840300da03124050f1001480510038035903802e00913505c003502c170605 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 41374411 1250 41373161 41373173
    0x3010624021e0c01080405150103110a0503160302040e0f010501060507020f0d02010806040e0f0f01020d050105030d091a0702040e0a0c05011803060c17010e040506070c080d05090c040c050403 84
    0x14050b140c640c2c0318802c420400c0d0000080d05940c1c1540a1900440c250350f2800c219060074208240c41c01440044e0340000b06001c0700c50040c07a07042008440c0c03600b80703550f02e2040554400f00c800060804821616080002d031426501a80642c070140d000e481c1d0724068000300310b0844000360020030105001181c0c98040d424071946004810300c00b510030103243c079403580018007220401040c03184030b95192080c81c12440805e001c034000c481c050200b158603240051076154081d40041c0000d4501f18500b03000001d030b0b4900000c018420310b01d640c40b2256007904103050250103891086048021103400c20802005840e14480c90006203116000382030740c4620741c580740300c80c1800da600407410013085040144070100003101c901c048039801880001c03200b12080060396034003090004086c00740c07030b8030000007030108840360000d1142c0d200e002600c4091781c6404041e1090080400c000e801540288015a02000e459114039000002c901c1201d010488240c0040c0a441d0900003c1000075008a010002c2042c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 41375661 1250 41374411 41374423
    0xa090f0608040314040b090409060f0207080903010e15040b090c0607060f1401050a060507050c09010b1309050f06040c020f06070906030506030102090306060108100305010c050415020f07140301062402 88
    0x11810103141924081421b0451701079810200d02c215507450110007040034940c003524404030a0702040d52910321030b050412054008000b500e00950078031001d05403840000c03600000201240b1038034950307a15607440e0140321101c001d00c9010144201e80101c1010303170312800a0310f812440344001151940c003450b00c40302658291400c2c4100c854203030340103004070b80e607060300103050307944903e88070b51074401a0800c1d038680886403c4903504480101300100724031031002c00800d5403c20b07040400300704c599500440c0080b0780c000c031114181000810302103915890030ba00202d411000c00d2048418000c1070804180c140442511000c0105c0d202000802115806004242d4400c500301c1c000c504202d129000b103a12640014044d50400c0031034400031307080c1481d101081c002780d034208008002e00ca140020260841c0c2c054001c4602c152090700c0040d24142c40001e40e180c50117925000b4210440c03603c004409200100401c40c0d40c907540b141e82c0816000c444040d0f0a0f942c0d40c5100c8006203c02c030302c0c000642091 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 41376911 1250 41375661 41375687
    0x1b051c020f0109031101180504020d02090a080703020a03141c02060601110705030607052503020102250203120307050d090c05150307020d080604060e07020105040215130b0a090f06080403 82
    0xf50b002080030500d03030300c1032a00c2001c080c00d2000510036680142e40e4804142e40220340e000e0b10104041c00901c2c12503010b00f80e0a00c060350718030705094958413803640c1c42009100080d4803100148060000500d51f000f100c0010301e64408841403180d0301041c1c134000f40c0402c0200310060317010400f0410a903038031140504004642380c0c09000710b5820031006c26100e07034000342818140000011203000e801c0c82e801009950100424000302075100c2807030000e02030741c03144c0210500c02c0701161005c080001641007924000e070380200107041981200c0c0380a640c54000800340414802c003407150040b407800c14040c0c80200d42c4100e0358440345500b03000412805a00725619610308c02c605008002e445500000d6640301c0500300e00300351a0990382c0e400050007408840d00070716a0400044207210b01c5a80540119000d20b01c00c440600070f03448400030b1056a4000c240c40050740c402d102404008501458009020030109843c1058405444100e0706901d542d0981c030a800180d03503d01004103165215028203008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 41378161 1250 41376911 41376917
    0x1209011b060b040b0a12060b150a0201202502190902040f1a0409090206090424080d020703080f0f0c07030b060604031109180709061404060b071b051c020f01 69
    0x1a6040500c1c1102c010003440340241416a41c0c0d4102e40c20384e440c80f109627070007014040c1c51651404007040080c060f03d132040c6c00070900d02128000c14008100c0c07005848442000017074160341c00c0600c001e8a034030030400840590700540c10511250000d09240200e002a200481340544e07194585444214a40032650007100c880f102c00c5044110325111900310f80c22a46908000702e03980115000043c1607202c0c0e626142c1d8007510303100c0015003481803800b0025698401a04000149548410180c1c40e1002c0500751070040e00a4501031000504000180030410b000c06005410b14000200000c01a8000003540320280d00c40c007010010000c108405681c00310023540d005007410f00d55590541c81c0c0300f40351500b521601c400720000d000d1340c0c0c4184403041d0a034074840443e0041c3d90b4400200300142900d00074107104824000745442d0605042c01128100c0710201c40061511031592141c82e03000d0b9105600c840011100ba4000070383e80c0d1518910402c00f15150211003000140c2e00c1000f8840e1280100c09042c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 41379411 1250 41378161 41378179
    0xf2102160f0302011b0303020f0706050403020c010e01020709020a0c020307030507030b150907030c12090b0709060203070b0a090f0803010f060801120309050f0402040509090a020109171209011b060b040b 89
    0x142d03030120060629002031705141030400854035007500a4011000e07400b184034030109540e03040c0a4640c105a000e54002c3e025100b0f002d00b11001181c807041c0d0074210701d01507800300700200503c200702d50080c81d064260f81391642c2c5184083c0c2c0024140b220550007507800d40c4c410002802884140c8922a402015104003080d1144401c000b050000800801030018103540700c4105882a008812500303030441c0d116403c000300310300c0b0301e4034100d0030000303031425030001d8000b28000c6941e50000040785c6109400c10000c40c2c032640c1d0181e012014200c030720000c030b51070341c1e007030200400040c0f48002460280440c2d00c26180f07510300700760005203c0c0c1d005a011070603682000c40402d01203900f1905c241305440c004d50326400c0c140c0100c000702d07000c0d110b107600c009d40118021702001200d80c0d010401c52001803003607841c0700c080769491150f010700305007409001c0c400745c010454001c6411001401000c2040c4107040403281c4c58022074585d1500700c034a820030b81d5520340314900442a480c03c0d1050454040c011100b42c88 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 41380661 1250 41379411 41379413
    0x4030b090601060c031404120b040302100b031b0a0510050a14090f04110408070611150915040501091202010516050f0d0e15041505010807030f0f2102160f03 69
    0x318049400b00040e003801040c58901480d602c219013247d000e00b04c40036029822070003601c2e01107000f2804803810380060054580c4c1340c440031114011001c215400038020041100c1c00c0481c0c5045c41741a06050390702c0600e501c0c0002b42d5841e07504a840a210558650948412070440c024150250b0303078500250040081219080d1940e9440c00c8003201c40094070002004503584410741903d20641d00704c101540720380000055525400b44442c086e03900b1010660b80c0c51a400c13030505440c1c0c04241c03240256600044072800204c0b003102200341d0301600403400800c902c00c0b02e444410341c8a00005203100140d4645042000d421b05510141c0585202440d10f1468030103c0d601d210b595009001e0403c8030745440740250110300c0c40800000c502408003444c1c00030103040a20341940400c02000c0321000307107420b01c0c00008180ba030106001c02129040301600c2c6101c02c01e0355a2001c102c011031800c8420103c80404400d034807010900401c002d108a070002c280609400700585d03203440c01644542142c010005045c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 41381911 1250 41380661 41380667
    0xd0f08010e07081504020d0204050a0b031e07020a1a16020a030807030c0212030a050712020403051209032103060103060806010503100b01050d0c050301030c05040524030a05030f04030b09060106 85
    0xa680140c241ca4602c03c50b45409180c6034500c0134880034154424000f140c04100800c00f940140200c4200b11941d12030269151100e4219000449800000040c281400034a0500888803186e100010f4416a85141c3d903a40d903c0080404180c07035107007078a441c0030400003000c60000c001100301c0003500040c81182c080303680050241c0d20040c007180030140c8880821000034000c11110b104081d0144490380c5900d03015891200820b0700312071000008840c1c0c501440f001131039108075002ea9030800050084200100200605580002d5401760503102d2207540f42c404d01c41032a0040c011406142c0c40c240c1e80c3c10302100040c10b807451900b1078045500103500411080e50b000400c062403c82010010803a000e0304070040c1d466010302440b806a070f50811000320021a4032100440c10780344034502d00325286032242c0903c422a00200d17000c0c5030070310241c8005e071004140c1041c01c403c002c100904490b00c4c8040f07a80c500d800c40d00700c030400442c2e25a01141c288100010f02c0d580035404031440e4020f100643c9005001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 41383161 1250 41381911 41381939
    0x3060c030c1b120e030105040b060f100915050d0905060105120f07150917031309020a0507020f030f030711040b010201110d090c051017090c060702090c07020405090d0f0801 76
    0x102001008400f01040318095614a50340082c005e00030811441d2a080296100d04119015440340015520620007031529190710001400e03c1d5540481150400f0760700041d4410188016081c40414089100c103203540c1d02030591024402c10190146514001c244204002044401c40681d002204500c46400000408008441c0403480c01c001007503003003506a500c2000f0350000402c100c0c1805c0d50740a0a0000001088000c80080401c5038956803016038800300d0280d0403906000500070052400540b40c5000e901c910a44020281c0b03100b4110000740c1440d60b40668411103502200c41d8002109107454802c07003000e444203000a0145011000039100140700d1200300103600c5c4d0b650103d400c1400600702ca00000f034032010300540509000140054104102c07a4140d24003034030b091000440d241c8002c0741c40d80d907014019007078a0418425600308401a2802071181c03440350300900400015a1391401000c3c042d0b080d031000360503502040200100107140d40c40070201800b03000801000440b040f640380c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 41384411 1250 41383161 41383163
    0x60d09030305150d0308180106060906080606030705040509060307090e2a01090302090405010603170301080618100c02011506050405030f0114060409020f0a0b0301091d0c04050402180103060c030c1b 87
    0x4c02d007407079034900007c2804441d00c40040e102d158609440400e66942084100d800c4c0d80c00354903041c15a6841004002c140c1c4411103907100001d0703003884104028242400440d80000008055a03101521083d1010444419284081055001c402a210321420796007420075900c4000300d602055121160000c2c045540320301c402030180e10380f0400603040c00b4080d0f01950203107a0090003560001c110307010020035504203000d10f1141d4002c040c040f612081c200c8401d040142c940a020780f42841958040d0002845c800358144203554a90340302c040a075100243d8480a4460f07500c80644032401c2106151501b603180690a47c1ca80c50014144140c038140c11071750b0f81c041802c840106c1c14081500c0414011220400f190350085418500410389810442c0a581a1141344d003041051500d90103042940341690102c0d124550489803008003581441c0d0007032540a40050305416400d07451000c5075828001c242e10a4950a0303840c0e40c1c02110a03814011a07200402e1460580c0f40d40070100301081310708003950380c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 41385661 1250 41384411 41384417
    0x3021b070e0f041502030c030601080c21100321020c01091a0318030a0c150908030a020a02070e0a0204030201020706080c1204020103110a0806090601050301030c180209060d09030305150d03 83
    0x3904000c544030307205000c03450b500313030a41d02c0e82007101004a460304180c404a001c83d100c1000504098041c40540320340c201030155201d0b0b00080448601e40d411000f911400b0003c50000010012030704420015050600d040c00310300030f00d09940c80c02410b02204248060420081840801561107105402c820512440501680d80d403560048420b145901c010141d010b404081180c101e03403600140b468441c3d601441a90718070360200300d6050700f05c0c1d85c04140145500d405001142603041942d0280152051714011035245680319001c4c00064041101d2080c02c1c42e03000035040c000c5580c1444003800800c00c40c1411149810440d44841e014041c0050400034407541c040010151382c440e40208010412500c0c4081da503d2072102d00408080007110424000c0c507822000c0382d0194411700880c0d041300e4102c850842d040d0304240004900c101e1000074095040d80070f002002c11640e44a00a0040a241c10700026031341c41d46140150544000400c400040000c0045203121500c039030314403c0400f54140b07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 41386911 1250 41385661 41385691
    0x1508070e0301020909090c0112020f070803040c0306140702010f0b0901120f0206040b040306150e0c13051f020610030201140a030609020c01020406140a050702040e10050703021b070e 80
    0x1800300b80240a40c90403141c2c01800d01003070025125000ca0b195407003540a0b0307540741c204a03402140500382e10506540c00d4600100700400004140c2002c080c0d604548110741c0505000c0d92900e80d0700c01e40d64440d940103000d00c2c41c1320071b0000080d0240b240701d01d904500801440071041e000002580124140308038001502e94416070340400c87e9554012410076030007042151107644515010f46650024007040300c0b41e914200c2828500038400c00f40301c044529204819005541da81d20081c2103401c03400c004141140540b2003c541f903540c1d0740055808081e840e100d400c41c0146100000c0c07901038060260007480400074014009030341e0082d44400050007210312035640d54040b04040f401003215601520065101089006a0380c0040d0000c0c01210340607075440c852550291818940fa00c41c00070740c03c000c00e070200011001405c2c06e41040c010130008200390784101100e00d0380c030380543d5411a00100003a60003d501c031203201200300080d00f4200c2e03d40041900c2402e0122078032808601a1070201e40798980d07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 41388161 1250 41386911 41386937
    0xf080703170c030601120203060a0303110708030a03090c0909030801031b080a0f0201030e0d05040e06040204030204090c1505071502160503070b040308071b230703030c020a150807 79
    0x1600009040c144085108812458000741060b010780040d21481e000807520700490980e481c2c14000e0701d0080e032004100041851941d034083c1c400656003480d00c030003401031080002e40b00b20288041c0145c04210b440104d42040c0a01d4940821480e40d040480b4032882e004182002c25803220b0510f040d00d90150f44032039500260750451440482540c03181400f0321900322444204642c041c41c0c1c0c002c8074407e0301d050041400c0421400d4440300c011000074005041400100040c403070380c0b80e041b81c0008000d0401441c2a84070703004202034a62040d13082e41c081840701c030201310303035130340307012a03146525192810701d00304901a52042c0303910702e44949048100c0d4006c2042642c04c4404001030390119840800c45e51750307451500c2c203484914422501074002c5520000002c4205000302c040606101d06080c1174041c0c0c105a0b5115032403001107050410440300c001c80b42294400d000c11142c0c010f18003d4503180f80d0f0140510400060310856080002d096607006c1c0707503d003e19008102c09400003880e04104d00d5841070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 41389411 1250 41388161 41388167
    0x709050907050324030f1c0503060915010c02100305040b0f06100804111002100609020307090b0d1113080105060301020c0304151101020d05090c03070303050405010c030504080625020a0f080703 85
    0x101300281c1d80e142c0600e0b01c0030410300360005000740c0c0301d40c0c202c52644102942600e080c1d405000072154113400c54000030010300030031402c0305a880580c0050502e84810038007a00840e010480c2c0580e04008070769a0014031007800328240781280e2100e90901c4450742d030f02d40752010a01400035600d2040500a2030804201089414007000b41041006401c2c500301d80002c0000940d6a030800c106911418903101011811107610f0003102c0c8510034680b07404805524240b828a00b5034400c460740e00c80903556440341c3c5082da4290000b000c1c00c03110307103041c0c0c1044c9080007022802c50300d0141101e4030030380c810480300703401071008000d4400320381d08025a61b5150f02c82403801e442c01124a034826945510000d4810203811980d44440c1c0a00310100440b41192100f070189a80d501c024040503000c100b00b0720040010b903100c0c219015003d80700c3c0c40c2140c100f070b503107615007440d0070b5050b5104032107045070300e84030f140c0c052141d40112402c0944c0c0c8014010400c003500d03121550341502c880541b61440014000b024540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 41390661 1250 41389411 41389471
    0x60603020607050a0209070804020603010b0307030f150f090204031109070912030c110303032e08010608060714031603050a090f051506030703110f04110f0307090509070503 76
    0x2801525003651000b851a101d03444980c0f4910891141e601400841c2c812440794000394890356014104a1559081030b101031102e400050000c01099101d030700c03408001030b4600a042c00080b243c08043e2405003810b40d040300d4140550403025900c0d20602003040800d0096070428003800090351021003544445c001104d8103880790300b010200c20003a081107010140e11140300d9940600403c1d0000241140d0000c264a0344015100010043e1004907004074410030044000302114070f126040318801c3c0d40d80380ba1402d40740c50740d001000d260021810880c6007904851200070380c44012042510714681a20380343c0ba000c0e198803c0c4c908055940d40002c0c540d485640c04600d507150460340000084803d0b103019950b4640c82024030f4903800301030001c90702a040014050081e01d6201c41c910320150303202d0302803100b0f4400c01c102e050b610546946035181040c4503c80108071600b441c2c10116036a00d4002000391001c00c041d44a2405500790000300055a0380c814240c81c0c000790f5030720301c0400300108481c404050070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 41391911 1250 41390661 41390663
    0x80c0d140111070b01050f09010501120b1912110603040201050711030a081c0b060c0d08090309150c190b040b10090507030e010b040209010e150d0606030504050c100e010c060603 78
    0x250002503400240804550000d0489000325001f95036414100180300c8451001e208090200780000b4400400701019001003180c00005070800841041200e1141d109451076805080000400241d90041c04042021040814010b4403000e00c0c506042d80001d2a52051400240402c40e11821040166030b09001040c140d40e080105a0344480c0120344e200d91119040e1060340f40c003450034807403550030300b000310070f4a440800500140201c10103021302030712490002807182c20230380000c00c01d00c0780b00e5031041c02d03c400c0d1542201d4815111180c1c0030380a0300c1c00b5108040d03503000c41429400000011020b1948a40c81079002d402e01642d5141c00390604d203103072038941041001310305001c100050154580d001100b40c07500c420080c020042c000c01408124456180490700144600c4402c120764207241c4680b01d6080c447e00d000d03510307010020141104480f80c5401000010b502d03007003480140001003210100156040b544459a0b5001120160079944000f5485062200d00300d0340f50180140e5900c810021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 41393161 1250 41391911 41391941
    0x4050f190e12041502011e0b01020106171c021903110a050a0302030c150c0a030c140d0b0f0916110c0604030506040c0b03190f020d0903090303020106080c0d1401 71
    0x1c001642c100034240d0418014045842070b02500c402c4034510500401c840c1041d40f444003c00580703040a16405454001115815592a040d00042c40c2c1440e0005400e03429002000d0040380c04403601418404501415a0341190b10411100c0302d02c002211600b1802a8181401000e600780d03d100c55060a08450002d40680214405c0105041d00800180790b410341c1c000a6403900f44510300d841c1c001140c15118100601024007860450b14081d502c25580c040d42c0b400d24080c1c04081d00c2141c0d0291348448181481c098880b840b803d103d00b40346a5200d4880c108803800d50503403420303034414103000c245610301d4010030280400100c9441c00a00c252141b5080103445140d07903c0e100d040c010b60352001524201c0f082080c6082c001044918502520700603200c02c400800313164244400c100c0035262921281034155070811000c2c42042c4940301d42058244251541202e403071035410081c0c00c40384035034044640343d04042048003450f643e040010002583c0004080d28075900c0ca40b0031401800710410304050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 41394411 1250 41393161 41393173
    0x70f1103130312020f030405090c04030c08030c060f060603070c080405041d100608151005040f0903030c052b0e06010605130614030106080411030d0f090504050f190e 73
    0x1c0340c0628080010380c0d005510a48048114140490f07992035914440302c00d54000348400c1c00f251500e1a40c59402180e882c102c1820075407a078a5248106034594003104142d440001e40000001003402056840031180ca0640001c0c50a10702140d240d2000918640c200b00b903802000040000c1041520054007000d0300c00c110032403202c9044803510080240307014683c4640220b0250f0b1078518041c0c0005d550303040001c0d080445207890820304115005d000c031000310541c4e000c042400e490703074850800354003003a800c003040c40c075691705005e0110b600781441e001c20004100509000703401084400502590344100c49551000700420b01002401c054a00024034090030000045e45584140500203901a0701640a5400d90b60791054544a10f448140000c1840510041101e5405040004d82c42401200c0700040401c0e44000241000d00315034492021410026018007407a07800301000002e0602586c6c100950700340488e503019500030041c102206804001c0c04010840010b4000e41460b614050840394 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 41395661 1250 41394411 41394427
    0x9140a0903140f040f0f03080403080d020c1c0e010801030b0105060705190606030311010615030902010509030d080a110f0d09080d050c0406080903090a0b090f0603040807050f15070f1103 82
    0x3a0b0f6900c24850341c00e980224060210341207141c000f4150880b6440315845207440d00c0d50391140181d1304604040b850459080c130040440907000e1140100054008148210108a000002e05400c140d1411030b41007240038801400052a0318415a055680c116600c544405180c07401c079180070303d1540c41d00c00385440200080b081203201d800010550303110751a00007a645400c40943e0803190365124040400204059452242c6d0195008000c0076006143c11072034180300c00d020a14011149417607800082500d010003100d0406403150240c24208640154034003561610f54140074081d040d45065040d0f40c690114080108500884110608a01d030900552500e075410901c20f800a215404c0400d06050008018070b1010080300c034102e400511a0b038116042001080035900311810b070640186500d4072444c02035440300d000d90304c01e40c030500b0119690b25040c900541842d020010340c1d089640b140058a00c15005412003d50100c1342c1e16060041c2247c010301112030303403000b5101002501000442d20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 41396911 1250 41395661 41395687
    0x1a0a030b0702060f130201080712051509090a02030709020906041e0303030b0d1a040302010f0e030c010b06040503280f03021c020c01051215060a12050109140a090314 73
    0x107200380195029140c943e83c81c58884401040219800c5203100c1c0519a00c100642c0170310b000d5900080e09240c036910400900941404841003583c885850008074040c00078149040d414903588480d485015104405855000c2540c501140c014140015000710360b0b04515103642d0103980040c0085819404001200040d000190005010070380c0000c0c14000c6002d003605110300446076895002d000801317010010401c12111140c0035004030115501c0d900541e040711031a00481c050340c45044051659017000110031070850328031540848c0941000d1204200d9590007040c2e036001c89001c685030b022198541607100003140f410180c020504902c240c071820615a0010b0a01c1055800c800a140d08241e1a10141e90f98400400f000d0300242d020809508040520070000d60044000c40d41c15840c0d10003070002542c550041d0140344006050f00040107036000e02809410b004083d41081000712961000305040031483c0109114107440d2140c4007402018458085207182c000741c0160941c940d83c59151304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 41398161 1250 41396911 41396933
    0xc0a12050711010e0d030509030a05010203070207060e090f06060d0b0306072f19080c0105010b030f1506040302100e0a180c03020903060604090201140d091202010506131a0a03 77
    0x690316200c8481442c081c03035000f4442a050404010030480c2e01744050360301200c0035840040c6494260203000781e04000154240040d500409498001d03020150400d17000074070081400110f58801c8031241d0034002622854900035801032000d0352000e94031216203031400090480010410317094452041007000240d4050078080c0c00c0800720403030168441010b80d0090040c3c0760b4a11303080301c6402030303075441d81c00003226441400b031076105040d0a0300b00810809080d023150381c00d900002e032280f00003041051410760710944a500010000406500007140d0006c5986ea025601000340100e031919200031816001d0f808405c02c0020003401c04801c20b1b146c01404001c0c05000000c07102081c104110342c40b21a0017402542c1c10b82d5006401800f5607a103600c20000500824035003a81886854000c01000080e100c008020a6000071400310340726006181c82d404a40c00c031200b0808591408050021340d55804840801c208034551000c101030146803119160b0000c0f072190316500c4000f92a0000810160280e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 41399411 1250 41398161 41398163
    0x90b0d051c080c0a141c09060b2107030b0601140d0c020c0a05030c040b04020f04060809061e040f060b030714120601060912050a0f08091002030c030f0c0a120507 71
    0x1a8000b035152404402e581d40a04011207003c1400c01c0c07040c0901540c0840074040c41c0103070820622040401902c51030445040004c2900c0c00342d142d450350101c41c24071408184516000440c002c0c1d0300300c10551450b17141c0c3c015010080c4a9107040002c224070740c0c03052205595240714416041d0341e0b211400f50303102c01001c41c3d00c82d031b8001d40282061090b16203000c201050450760058003400c060030b804000c000c0100107421225070300c02d50034046055103500480285c0040c2180362520103050400c82c54440ca05100205a030900c04244800b9184100c8040d100f1904141d100d28100781403840b501c2c000b4050441006100e0b0544075804000590f1034a040c0d2510150b141035500e004a540c914490580f00c42003400781c10040b40c0050003c1012914050610803128081c105891003103519550b030440321491120107a51592010400306c0c007a251400c1750044040ca03070300041d40b0f8003044001c0aa101d0003003a024070000316000c181c0e00c1e600007040c000342c030500e40e10040e502c01d0600350900c050b0403a045460 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 41400661 1250 41399411 41399417
    0x705120f10090e070e0901140f01090509010204050d02090702150c040303031103250302090a0b04080c0f01020d0c0606150309170403020604030204020706091b05030c030105060a090b0d051c 83
    0x290000d288281c500c00c0c2c0c000040040003500b1020b01788140303507401e51030280c0441829981c51400a0880900060141c0201007505618803035500d400101030642d02d001e0300e441c03c1a4410001040300b59580c0e0b174201c0080fa0305607a01030345503445810a0b420b1101c030b512403d00c4c243d0308801708030240118200810030750f4031a460810000d541d04500d1401303408206c40d1000050b8044600c18131440c455441c00a0740340140c500546400800000300303035460b419501003903110710301041c18042c00801f4000c2d90380d840d105650241d0040f0050340005e540300003400000051112001101d0144140303900303c1c0024140168401c401e10807803007070081c02801040d000b81c480050800214850391011400c841c1141d80041c0040c0c106825502088002d5201580854203c1d03661720700240000c212080d2078460072408070788031000914002c1414108031048240c10310a07490581042410364442044100b65454040300156000c807003000f2500b906181407025000340b190f04045d80303914a00744690819003d80da5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 41401911 1250 41400661 41400691
    0x201110a0506090d020102040e13050304030c06020c040b04020702031509010e0a050c010905010c0302060c0f0405030a0507050907090b03010902030a060315020c01140103030c2d0503090a0f0e0f0705120f 89
    0x2c4c0c0407400c030b001d20300641c10542c0d03d0304040343e08001002c0380e80907031074000e100b941c0c0703003c0d0381c0e580c0c0f480d0102046c0d06c07080168000d641c4142e01840c083c4600720019800361019072804600c2c0e40062303111051906110031050620001c82c03105803096004000c0e400700030040b5002600c3e6420b1072030f910360301d40b01c540d40001c851850201d00e5500c5400700d581015496002480151a0900b0500440c0c0280300e01d4010f800b0184000152694204481080076002c1c0c809818424200303020702540300e00081c207010500c800c8a80400000e802802201d046400c4090016169200c4020303010280a455001812030351203000511519480e80c0d00400126041400810007013809119005a42209101c09000f08025105043c04100a10340c820f0710007180065201d507858041d04218a42c40303842c9802d840d268000300d01c0c3e402130700b844406d220190146c3d91f00c00c01e0141c0f0300380303699010986c02000d010110381003501207108980610151004118462081665450071095414440300b0494001c181c1103092 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 41403161 1250 41401911 41401933
    0xb040b1804020406050a0804111809070803090a03030311090d08030109140c07080307030e060c070507170d0f0c06020f0a0201050a0b0a09090212010e1c05040e010608040201110a050609 81
    0x82c0300303c4007280c00e143c49650820207080c20643d14800020816594a1142c804043d01030382c80c0a046c000d6400c400061840a0a1088869180c0400354010304100e61040220700082c0d5200c401c4030b801c680d8540303000710380f0303001d4180b042d01c260240f40003007070300105890b0304001040241c5000c0c5040c0c541441c3d041040c0009042c824040103401d803031510301005c0c200a9030021554000003103500c40341030308000c41d5510101c500c0750324022040700c0c00150100041800c0c0b00300308060155800602140c0342c41d22014180788041038560b8280007084041c090b1000c8c44802c014086c0c1984030480d41c000030215220b26055a201881c0d07800300d200c039001540380400050000c1c241e8451020540d8014081c0d882d014144075544005200c984816640801c55003004003441100b4003604c8080311000d4003502c0741a104144000ca40c00d5180c0003042403000900007889448000703010541100c020313241c4203c0c561a82c0c001600c1d54845145201c50364020500048103000000800c0c5001e464900c04550310110070f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 41404411 1250 41403161 41403169
    0x9030f05040e0a0b0f0310020a090e36010608160501030212060f03010b041107230d030b040207060c0c03020705040e0a0209060102030903030c010b09010504050f1b040b040b18 77
    0xd5028501d074003021400814503c1d01a60710020304c144018180300c00301c2991034002483c14580c1d4041c00d03181600040c60030089903001024030700400085000103860700b481c48620b4034107102410150011100c0085032030000450380c3e00d07500209081402040301544500043d5190780c0140b11015200c07441c044009000c0d44a071084a2440c2880e0f07043d030049484040420010030303200f0040c698590348401c5002c20b1569944140040900c545240c00d5540f5182d180c6644c02d0003000310140303514144100f0780381d180c0401154032545080c50b86000115100480c0000b002400341c0d00010f0100303490054281d07400f0f40c100c03120380344150203602159502580d0710100420b0b42d0030700c00740741900e4200c40085801400e00c000c00c2c582002d014010f99080a0007800032a1941e00002e902000b01c0c1e444000d200c0c0702d0f08041140502411081c1d80922542c0307400c510840f20340202070088403000704106881b82c0080403540c2070b07070080d040184119075501d41d103007040c01380c0b500030800780c0030965044d07407401111f032038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 41405661 1250 41404411 41404417
    0x219050d0f0c0e090a120203091008041203110f070f0b0703020304050c1210052703180d020d030c020109051005040807120b1303030e03070b160801230a080d0309030f05 74
    0x2c414004c0409001d2a601c4c0d0b111b5a001c5103034082584028040c86040341e445105d0715100d0030b80340e61000310303900d890f0520144041e403041640c0c1c1454600302c00a480007031000f0448501c540c1036004ca45e6581d200c0c0c58402c5050002c1040549001c03c0d00080c07040d0030368503800a501641c003803021217030700d20036034010070030703c1a016400c903151a400041c240ca003a4034a5048a540f000d40c0076510844e10000507100403040883d400010310f19000087c80a003501c2000010b1903204a090700d0b036850b2112550701051040840d6a40502072110041c0302e04210782c40341c1c024070007404014005140c901c0400c01d0160590b04030b80610740c440c0c040d000300400d0160f0310204030311445422408580b900c2e11039164401c0015030f6144280c04244d00c2d1101031200c01001c200070300780284180c800300300318034110070481c01860700c0755004410460050010441c0d176400c00e1400030305a04209043c241c0d0b030202030000795040e4680e44540154040c0d0040701c180c02e60144d1210110a00a464414080340500000c5075144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 41406911 1250 41405661 41405671
    0xe01050c04050427030504050a15090e0c071202010c031a030714060f07123c0509090a0504030e0d17090f040207060c0e040207020105070219050d0f0c0e 67
    0x203a0288020070180c5003070b4109000389070200c0c4990410380751a40b0912414031030300b1810340c0032450019040055082a071703640030040001e80c2c02c41d80e050b104034070018080d560034070030700d409500550081000d8011443c11521669404000040210725400002e03019005000e0341201291030802900d41c2000c20310020241d03c10003c000d010b800d03084c141d240750040040b1102e2500b042d0280044600384210900819209000348101d109035000ca0f40000c00e14407406036944449201c41803444080c485821141d0b42e0200300300001803010600c4c210071603150241d91207203980220782000307000f60200c032070744441e004600a690b11a8034004a005000000c418603900500080400b040721084d80c8040001e03203800c08005010054200e031032400070f0b041c0e8100490a5962581d55054001d031107410513007404590f48107a9003581000540d40018295028821000c1d01442c00548400001c12a48000341c008d013600800280c3cac0c0210700d04091409941c504411106002e560001040d0340450707980d014818 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 41408161 1250 41406911 41406931
    0x70504050306040b0a060302030604030503160906020c041e020d05010503010b060702060313080f040303021b0102070503120711040915180c03030c03110607031505330403080706020307030e0105 85
    0x40e00e4542c1c6604064400605a20b03280740d46a06c0440103950038000180500d00940c1c0340341e20f81c20300c2031003000344091028005007441786040080181940105902c46107000403100000c4420000707101082c511411140b07049030510000310f40303640a5032a48800e040c0c41064008104e406092028004103100703464010754080424000502d070101c1d40d441d6074034520b100b0800141045041001c541603500030750002c5015801c101110035030000c0c0c840512442240900c0101251441c0c00007203038076509a04000c01c1907460006000060000c61070040d002c61030080c004000e40155800d1104180030351000350148a402c003003180f40ca4449001040352074903000142d8504040c9550f4040e203042c04032800403010320244242d00090944103020302403084181e501c02089800c01c520000ca488115038229910030b00c010030044084040140c590004110955080e00e40000b190030440564001c1d80e01c010004840001c0900c20010b0680186008101c292000d001002c02110801d0030313a0310807a01c0ea903074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 41409411 1250 41408161 41408173
    0x8010204030308041b0302060a0302040524180105070512070201080a09021815090109060602100213050609030f0105040c030b0105030a12120b030f0c03160b0906090109120303140705040503 83
    0x80b0b020481c00950069000345d81341400790307603503000c00d1858100d0510716000c0b036404181000941022070441309049040d4080c42240c04900a02b030300300340a14a4440c501710804450041c603a40100f080b0b4800d180c0000031641400d0200105100580c84008100c3c0041d20140124461002500071002c20541c010b2007104040344c080380e000000c1a008000c840ea070465914a0202c5455024046019144403040415680d051810191070890406451103400d40704008514040c1c00106030001511000c41d40325a8841c04440001d2400c41510821041c40d4600020300080201c000d0708031049a22403041001a40e90382d104150300c0f010301c030002420b43d607a82c000b2005d0b09031003070b418590078403401c48001440701c119501107490984503131007201c1581d20200204403289400c124000983d02c0300d0120342801c40c18240c3d01d215500030042510302603480840e6840290b0300030341854010304148880c2e10701c42c6225042c01800f500c03a0980843d01901417101007840749100360216016038401400400c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 41410661 1250 41409411 41409413
    0x1050f120c07060e07030309120c05090405070b030109020418020f18040236040b0d030f050d020f180f060912150403020f010606020705010f030f1d03070308010801020403030804 78
    0x2031168001081441d25010410030000040c0701e41c0b00c0c400c285100e000080c82a03e00310310b070141c6014003d0708010086c0034500740d4079001030661854013090301c0d0140c518000f1034495140c21850459150461810b0b000c0100000c01c0c0d03210036074040d10440d419040040c0f800301902d0013a500701d10035850042030400003042442c1001c4c10341d00c80350074000c9002e4801403501c12092007107a08880c00d6a8032100001c00000e54488001005011708000340c000c8800700480c0c14900c0001e900f44001050003424031503ca80c070600114042e00980351520480348042d5a500307403015003204a40d01c80864440c02d588400c116202601703000c940c5902a810140c80d151920b84280e080180000702d01d43c130100d540c4601440310414400114905009038403d4000b0000840e00b03181041c29030b041c0e6001a002c541c0700c03034020410768ac1d1102c1d40c0c10f4140264100001e54840c81c5e00c2a00151a031100151117807000241241c003d038000100400003103000350303288003059807103034111401c3c0d02c10351002400003401600890 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 41411911 1250 41410661 41410687
    0x10e06070b070c06020d06050301050c030126100501030311060f010308090409020d0c06030c1202090906060a02010e010603032316060c0908060f0a0509060403020a060c090e0a0204090b01050f 84
    0x5410482c1810071a20260581e554241660b000300d1030311308915103920703040099003002d0189a411034072064865042d58140000341070f68001800100c2410081e003010005032100c2070100030110648440240325960716428050301c40307003c1c42c035015007500c034800005441240b4110700c3c50507a6030080c810348c58038006004010152181e8038080c0c1e03104204001080c00111040d10f01d00c0103044546002c9a40040070314003800d4580044103910310326004000b0350905a45100d03c0c15804441250200e1b2030301c1e81d00070102d00401030b0f5400f218440d0f10f840000700c180340e0040301d03105072030401d0414101c162010355000325103030088409041d0b9818441e081617000405a40000041c0c03036a074030701100300554451086181a8054440005100041040c054200003501415910070161300c000c01142c00c3c540e030002d40e92601d0210143ca9259900440f0301000d12900000000744031489034a01d03a4108003040701c009510902c2506462480e10210401703c1d40120191040c0040a5401908002c04c1c00e07904 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 41413161 1250 41411911 41411933
    0x1804022103090301140105090610050702040c031107060e011b02070b03040201170a0915060621020d020c010b09070e06041e0e090a030806090606041e0b1605010605010e0607 76
    0x103140010311141d00ea03600d0074410002000802d0041d00b425514150602c5042d00c0013918403405110310721140f0708000d400c041110303205a4180e4000400c12400c0038110010500d02c242032a003a440003a05900f40007050300048603d81000000708040c0c6001690200d0a5603031400c00d0015070421141003001d460501c000e154894010305140c40c19880d40901700070390b01001c07210000441c0c2e44131030000500c81d80b19030340201d0160100302044040d080c45005003100110240c60340110704049a4100c120b450340e0191107004501180954070780d94840007480c06086600100340c0105d240800080601d132041e2281d44c1c0809010b49414903060410346912640000107010a0310100d0003100002c00b11039101c0c02d07601c1000144050030000003107203801040d03503a01521240c41a00c810044c0030150b500c540448040703030448008220390f9184075126100c4800309a12a8078180300103e5603950104442d0306410103e48030320002c2002e01e03250300c0113403400c2507107088440c1c0080d000c0c01000d0000e0403500389 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 41414411 1250 41413161 41413219
    0x306110d0f1815270b0907030b0a0504030306051210050a05010f030b0a02041a0a120c02030f0705010b0307141206040b0609070e0306070f03060801050421230306180402 74
    0x3103134000440c0e403d807000e100400101e605088503000500c0602490161050300803100d0070103802c0142c903544030380d550014003509d808021a591008541054003951240c0300804001e0040380c1c1e2403030074401a07a201c440ba200c40902040c14070001075004000da210305c178141ca1070100300c0202c0900f940c5840f00c000c40014840c1c01c65075420000400d00e0034610030007408403550302c0e1503543c2e141c2861900620345829020301c8000d150900042142284d004420707100107a036201e0300726841d007100742003081c054500d284000d60107004005000c148884040c249400148041e20038841880081151551312101294058041010000811020b1412080b01398100205e0303d800c641c03036108400040e05011080d58a1000300b1a50069043c01c40d400d40124401421598000c010518185d00d0f900007030f00c00c03114099616030108841c407007098065400603c3c0b56500d149821007526045010b10b6080c0d00c1940c0d1240b00341603820382c01c000038005000c45c5101d02d6001d000c48140b402680c4441443c0080041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 41415661 1250 41414411 41414453
    0x30209060708070804180207170d0204030812070f0c0b0f04020a05090a051515040b07030908030c01060501021902130c02210316050a0c0803060105040306110d0f18 72
    0x8655000702d000701d405040c01d5401380310070710341d501e140000840c0c41e0b5000f000c40b083c4280c018071105011a031030041006000750315050070303036271107001056a800910868000074140c00c000700b0520244509140014441c0e103e60f142e914006d00703110800e842e00c40041c0c000402404284002400c0700c123403008041d81051024106003c0342d5221700c002816088104c0d240b0b001c869441081011880f500d0005602d10441034030150301c3c603c145440011107100f18001e02400000000b008010148141486801000c0349401d4035100d000d22500c140c00385c18507109081c010b02c17a41d840c0090807011020303c000036680c000c02030585009210b499201034200c000d0b0000950003600b1000303080b05400300703012034004140a4415a6481d0206c0049018a803082c08036080100c18003900041c550020400708a103a0807019158480d990304e0700494680c41590030091110b030801c6441c0c4c0340500014050300010032200d5041c411010310321034600484010485080c003410b071400ca84c1001c81d650900ca5004640655 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 41416911 1250 41415661 41415667
    0x20406050603010b030411061e0c0a05060106021e1627060620031e2803020705010e0c010207060309020d0b010e010305100e0303010501031e050f0106020c0f0a0603020906 75
    0x2100064180e042640700807aa1311001040200700016507448414102040b41e0617828845003034241d8400e8010b02c8101d0340c0d0440001562400c0d00002c2000c400074950100450b0525030311088000d4403100c0c02030324061072074110220b958030701c603000c100401260341c3c41918888003841c15025840300c0741404201c0c40464130b4803140082144050151001912107501d884080350519401c01000b0483e03070a503007800344c00900c60340780d9003240030210042034201c40c901280c03540c04848070420b04001d4070b8402080d6000d03141404180d20307016005030001d54000c500800000428408040e214032801c1d103100d0043e00070300740a2002d00e000c2c6c0e200c054541d00140000c07101c0328041e0b6585101400c2071704a0b80700000e410004004000c0100520981b00032032100034803680c0e07042c040681e540e000c180a25414503458002c5151020620055059420002182804030717061020040d14582c800f80110401400f40240194250500000340055104060900001c40b40b03041d200302c0c000d40040176460350003c010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 41418161 1250 41416911 41416919
    0x3120d0e070e0613020708030703021e0a0c030906030509060402120712080c012003150d06020304030306030209010602030906120705090a03030306081e0c01080402030c130b0307120519020406 84
    0x7042820041c02c040da401501c1030a0a800f00a02c0201c022401c420450041000c20001201700f41500e4000510b07080c00358680381c07145812200d8184402041703c3c10701c1c0c01b060300c400e420761003450031000c0d5010b501d80701c20481e1551012029a0b0382264250f8050340b051010a006081507132185030000c0d240815580c0e12a141d801d44404c10304807010681c0d80080100300248110000c1c4620b8070f1a00003942170390303950f049141c0030020502000740403440007600044042c0a03034580d07a18010220341c3c012802c40d903e151034580500140003a00050340205803800000c00c8041c000800c43d4039a020051142e070404c429100b00540d02440240700c141008418040a039aa44801d411040918882d4030041441030410f02841d1030079036000030900c201500500351410059021030403003c101c4003860500019a40d40c0086864210700e00344042c0c000c848544280500d5407154010b01c0d04010450a46894a0b41c40e004440150b103d64400f8065403c08c0080c122140403025407284194409040070950507030f1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 41419411 1250 41418161 41418163
    0x609060311210a1b0906050307140114031f0e061c050a0206030c0c010f091e020315090c09010e040308162102220b0d020a05040f0305150702030903120d0e 68
    0x8000204c400040012003044100f42004854014041c0c40c83c04002d0549000c00080d43c42d2071600c02c95440500b401903404007a40704103414a0120b04a03200607580781000101d6120140e00b00030100d071011424800131410b03c030b650703194030300848005004003e011080320182c0030300559002e003100c880c4548240900107072500c0f00510b1080104c0102c007a2079000e14240a42590341402d41400c0c29481d0451060010b0580c001204415821294000c0640075610100f480c1500c5084102d10055092040040e00c99001414200700d20f01030710410900c0e60385a00e0101080401c3d2002000b14082c00d00107030401c0f202d600120320101e000c0c03070442c0402c6802400b000282c00005141d10405400080b0316800d0003461844035140176281009045d560f140002c094038901079410030040311a000a000604180304c2c04c155000307000a2070468482e07594038075005964448542203800005801070000390914008170580d1f00340c0714050b000c0e04903100c0700941118168084100c1c1a00b0b540c0e200c90000c041c0f98 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 41420661 1250 41419411 41419423
    0x3070519050708070305070b03090c090a0c0f05070c0510050f0c01060317070314030a020f0408030309070b030c0d0c110a030f02060c070323041d01050103060906031121 74
    0x3a61a821004000c418100380d402c0000c80d401c10f1281c0d6008520400000d140042e4050482d86c098000b19241e44035100554249120484215440789812051055001c210b6122010360034281c0c64840c0c4116151005440e580100d1901174813241011104001506203d600201a034200340b810910348000300701c1080c0c41e9000b001480041d69503400042c03040140608605410040e081c1550341407043c41d0f900200000003011401d40d01210100107e90b0440d103d070199540b10b0240e40405440701d890b002000d50307030f400c1100c04038224402c0d0a00010b9445015040381d0045503d5103025140214171082e44010f4400c0d40d500c0f00c10090b6031200315010350424040004041d22031354542d40c0720040700100a19102000c0c0800545400800500000981061010072982d0800303803c0f4121881148180005005940c4107145603200015601c01000d848001141aa2003d0700c042014a032140c4403241181c805000c014030300e070302e1241e000b2050319051800310765040001d8030b91803001c1e0000c17a00c5400c0003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 41421911 1250 41420661 41420683
    0xd1706040f020f0a0c1a090a02040f11040306090b060103060b0711010c0c1d07020c01020d0c080c0d0801150c0c0306150306060f05010314060306040f06060e1006030b0301051b0c030705 81
    0x59a51100c40e0204080406d0000d01c001808a25502504240c2d5106844909408009200300e03903400210480084680140d1100c100c4661111f40b03450760ba05005000e0701d0226021030340c0202d2000003c00703030740c001c2c402c00d416500c3c10007055041842c1542c402081070b07203c281d1b850600a00e0404100002c4403542000041c1800d280301c0c0809110721031082c0030000700900028155008441503282e1a40d0004041140700070a1030524a144d0803410240010321a04524000c54081c140e0040c80b2141c02c012421b0488569960008502e040540200ca4040303054000910310030703228104101082094112000d03000910906044059403907440c80111080c0ea4080800121a0707281040380d50b03018411216505441c804030000303494010000394964000400c010100107495003004180803080d803203040074280c106903c0b51b56007030508502600c1c007401d1103440c0c0000c1c182b20013a80c0038101030040d540030b900c11b805c9400c07603441d05c0300c0340c0080d0390041841003005200038840390002c00d10402c03c9103016 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 41423161 1250 41421911 41421917
    0x9032604060c02030105060f06032a0307020114130203030403060b030102190206060a06110304050d17040608061f0206060f040e07030f060e0d020c100c02040504030e030d1706040f020f0a 82
    0xc042e144149800d40c1c0004003503074400e060071501c84d000e5803501c0781202e5100c1c2200b0540b020304916012184221103501031070003a0040c01104100015405510030300165444120203600c075510b0602612621050100094160304184000c1001501980080c8030080000b40050309004000843c4210100d03914000c8005030702480503c512802e200b021440581074610303000800955086403603039a48102e2062a01481400300d40380d083c440c1e4116980f1080ca501c1e100203030748030354540c030040044100382c811500c00ca05451848203480305010403038031618072980180045a441604202e14420000c401d2500070f1b455483c0760b400094280700c42c0015510403c9003030030a1202d820000c1c00c8aa6260b0002066031050804030341c2030303800142d407040006080350034034003840e000c40f421100d0075090f0f18004c2d0130504210502040603002103081080f1641942145c01031802c85400312203030070044420300f19130002180800d40500701508100c070180c40d40c910240c6800e80d0768100c0e001d00c0c2d100040724400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 41424411 1250 41423161 41423177
    0x111204030e03030a091806031a0a0507110a030c0203030904020a02010e0d09060801140114030a0509121608030a0e030c03070606090203012d030c15110604030903260406 74
    0x80680007518001c268506500940c1803100d100000743c01d00f44140202c1101c0c010003d84540c000380350750001c1010f5503010903501e0108010b0002440070316030030b46504000c942000009000188542c200303107190138400005013000d0116840980d0f0a0348030800a83c1c0600041114050913250740c001045c1504669000250700c03c0d140c5107450612101c14201010003140520801025030310000c0c05043d910f003405070f4400b950544d0300683d94110788940d060f41c00b00003c8104850209150321080c071070074010003905c6100c9044801c0600a114024082159211711240800440c140c1405503a00a80001c5c001030501d41c1c0480c0540b0715040600d111100d81d000080140401c2010b00914009010150b0258155410160100340640384040103080640007074010080d1b2444881500e00151b402a00092241d07490b0296091030b00039107690300c00403492035103181d0001e000020b04540305680681d50f40c0ba0580c04e543e1500300804108844c800d06032a98190030503400074107030042000304015226124 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 41425661 1250 41424411 41424413
    0x1f03050607120e0a050303070f0309050d050d050a06030b070309051f0c18080c1302070209070201020a03060e06030c0108040507030b10030204050c12010b0f0706060f05090c0f0a03050a111204 84
    0x2060321200f05042520390002a8910001180041626005030702410080d2503075070812002c600406240c400a40319200e59102c2510142e0810018080c12556240912599543c0701c2050b0036036201d48401080010741c400081d0a05219902030030704180300b0350544644001d030040d0101d042e4005409403484036907608516440300e810082c60824610442e40c00c0600c2c03490906550b03200c807199086c40c1d026804840c102c00d03186125a0449032a00e6004091081e81c0c00c0000f8000d000350800e10001011074904030700031440c1c20404002d80d208030070003401011000c41e148011034a0340b0300504104e038144184a8003000080306451719500c201207584108284503d1401080107880010748104850002045120400000f0490301411341c1c0c5001d01c408e0707507440444400006846211030207812189448004a032202500d1000c904940c0c045803100701545a1060030100c5108000c40004030700341c10814082602c2c080e4018660088034800d000070f10021070a00a000741d445804403a4000714800304000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 41426911 1250 41425661 41425697
    0x602030c040906080303061c150b1302131403010209030304052b030201230103020d030804080408070e04050d0f021906090b0708100602071a0304050f12070b0610081f03050607 77
    0x103e8031f483d0080022300d444400c2c1c407080b9400303003601d120803c9a500c845942410f0345403401c640c0d062035600c071000c5565002c401c107040002c9445000304035410020781c1c3c03424000c0c0340500a480d06014000c018520f480c0c43c0074100309681180340d95a0f800036400c622400d29882441200904442c001e40003c10288005110301c114007420081c6030b6800080d500c014000b5844244084404640c182032014440c0c80342d080000c101e0045500c15043c5128039880415000154032907036000d03034030400480755486042d00c015600b124500940308016407100182c00c0c581c603da4410741082070f000e0440080c0b80f0255803119101480d044880e2400328101006001e94021044100c0008003880c0c809050114101050000c0e1b4203810612a40c55100110204061001c14814a80801c091070304803046654035a4900c40716400c04001904d84072518400902141400d03e40c001e40c42100781c1d81d4900b5a43c0309640c4480d600790001c98500d420025481c0030000502c2005428014016500c60b03000c407002c6840d6074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 41428161 1250 41426911 41426929
    0xf0303080105060f0a0c0203120d0e07090203150108100b07030e091312050715060f06021204140d03030b041104050f03011a0904030c0503070c0603050a050709030602030c04090608030306 82
    0x703401003908000c4041c0140d610802e8445d1403074940380104920203075000184c03a00490f40d207028194900042c000801c900c16034080007020a8000c00d880e002c56480c26520100d010455540d201c0c81e8902c0c02c02d041c158801c800c6c07294010741c52030640d203c1d103841c0d0720b84e1315084e0402c4c01c2c00c5000c100b40404080040c40c0c030342c03c2c20740d20015901614208400966039013144040d5182994180301c40032880d40100104504114250380000c3d004200c5c490b83c4010390814a1010722601e400743c000c40310700404465181c0e00712800d07503128210340ea4044280d40d0a0000c0c0041c920410b80415690301818501d0342d80390701802c01e035921552811a15207003494204144452a801a544240c0c0740c40c000109004104810f513140300702c1203a4074803159580c7d04095400100c0084000e056020000b20382c01081007a10041050b0f0703139075a130100b00581d95020703030702c0071108261028008198504800c100144481e0000d6a10034a5002c000b0300b4a950342d0f465405841c010340080020303410210400003142061180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 41429411 1250 41428161 41428169
    0x30306011119020918030705011a030a050c09040606080609060601030b0a0303020c040513020d050d090f061e031d010906180c14010c020909060a05360703020a0f03030801 75
    0x5000c24501c421030289550805601c028090220301380090803c0d0641e030719010811900c0302c1035a0741c1d10600e19081d802401070340040c944030006481c2d0382040341000103101c1c21480d0322800504000160000300002d1840041040b0340c070f10744a00011500903014044a40a680f49500030602401d2010000d02650394400c503043c0902c050b81020808a40d00144021021100b0756000880340c03100e514544084074800006900700100c0981c20082000001c0c0766169030030300c1c0c0e8a040346941c544903110303401e0b002c500c95000000e0345c128031441d01824610310090404118280020f403104050340303030b0344152003241140406941d86d18052044c0f14481c054052081c0b00001c03080c1d00d1005650350031000c510300b070203006030707248044080343c2d60380e4020504160b81c0e40e0004c0c41c111851800c000e055035a07440844075400c105080c0000314501c0c25030ba80e42e1207070b40800306484610b401c0314100b02c0d0409094000d9082c982d40301e032003070010250701c4038007910f0041d1051501030500d075419030034040d1031818180e00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 41430661 1250 41429411 41429413
    0x6060102030f0d15030f0803010611010b010503040204020903100e0f010e010606081906030c0909051903050a230304080c1203010609050405090a2003100e0601050907110105090303060111 82
    0x269075a9001c2d44421590781441d401c07000034074407140480303242c50040070b03820003041c2c04c040da0745400c240090480507504031410341c0d49101c20040c54441c00c2d0300fa035001e0a0040d000c03030000c1c40071600526184d0050303c0b10b400c016007110248064503175800d0a072140402140b4094108100701c01d400c0c2d10a01a0845401111000748580740c030309a8003d04401000381034100024034002c24841303032034107908400c1c0150b8000d44208090380d00c0b98007142c0102030121044855100d2a0821218846031700003080005405407240d50400618003010354444121500118442c814011181d0651076204003450041d8010801541c03110f80413a10036103442400c1034800751317400301070004002e40d640c000c020006a940c291008640fa80302e000c410f038507040c1252802403190030000c3c07448136855180902030142c504220100e45c03c000b118008007080307905d400f0611480790410700050000d42840008550010007500e8001c0120404031300701c0b400c680e416a07161030250400000d1200342d41e40540b20490080141c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 41431911 1250 41430661 41430667
    0xf0203031506030702100509030a0306050108060306010b0310030c0806060418170703121a030d0302160204020901050408060f0a1109010804030f0e06040801060e01090b060a0509031009050c030606010203 89
    0x12000044041d035030582522942c4000300003003e891003440003946000054070180a9806d0040d20710740c0701d40020b80600b0001e071a000b0001400d610a0b041d250207194090301820b1541d0a0017035030f00341d680c0020720844109865403000400201400c07030100051441001500c1c03e814900304002c03d035641c00705080c0140c1059146000481d0a000000200d00c401d1444140d8545483c60159946450071056880d00da00d00410311941020440c1380c070301c1151040341a5860146000425070803802607003509048842d034036180030010b003403e17401043c2d201d905040039414565540e00f550314106080720f59051914900041c004417401e540258a600b01100d6203503410301c08250002480382c24001d00c050100101092885040703800b03900007103104080905a2942e850b1a009a240a4603051041d03484144850000041c201300910035000d907940e0040c1224600300805404030b420390800644e1941c140949010200c1d50200740c03140310f00052180340504040101c0c6020035080442c01003e950540d0020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 41433161 1250 41431911 41431921
    0x16023f070b070c0302010b04050f07020106081b0607020a0506040b0712050a0f081305060702070e060d021809070f030605040209071701050411040b0a03050916060203070b0c070609060209010f020303 87
    0x41d0540d403128452600c0a003440b40da00341280075090f035146003600315281105100e5a03c462001c02445142a50000c5c800c00d030f41c9480455441e054070b4021b9001ca12002d00403c0751740391200083c04030707900092907140750603101d800040c809c0e40179600600454100140340410480d0042c4440300b400c8040c10f150341400d10010025120843e015081d508128084001400d50448508035401c42030300f000403901c42e840c007414007a41d540454003030042203030040c5001400d90300d0a9000070740000e90241c48a41035214001c4c190312080d0000d000c104103030040b900c0205000c40300c002c0351030040d4064480804e240c245401032200e0700c9070291500d020801004183c80c0d2081d5030208850441d00280c03000a0503004010b80420300380a00d80080750103500006615003040d606401079401560b84030b041d103141c02140080808443c0760780c855203001d41c00a125000c00300ba02417000325800101b03107640c1e51130b00c6810742c0c03110200c8010420480704245e000c95003031550359100718072800382c0005000852440c201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 41434411 1250 41433161 41433173
    0x708070e010603090203010213080f01180c0b030405030c121207020105040b0f0907030b0405010c09061704030311040b0a09180b0904060e0114010f141816023f07 71
    0x140500c6003455104c44035501151025411550380141e0b10743c8800d480303900c46080a441e624034000319007580d824803a07040400c0740c90003100c02c43c1b0b507402400c1c524a2031914501034102d8000501c15a03d40c0402c1c80b21020110091200d82541c662507a11280d42d04c0403264a02d9603100c000d07000c0411607240c1004c00c00018820001c19401c0089260202119503500234030300c1c40e140780c9410080990711210140420040150011070081200c0d0310381e02803445d104d160880e000d00ca80d03140502d64440400200700481e02960108a62410800c0d4003454103440b401034400a0b0b1009041200080141200f0045044c081c4d400c15440c1664010600043c800400001c040000c007a001800b030503a106040142c20500354400f040c000c0100749503080b5980d40d0041c05484034414402c0100503907000d01d85001d20300c0e0002d004650405284841902d50b1143c4040381150a170110340d100035171150503004c40c1104090b4080000380982210038056010582c52078400b103600468554030002c40a201070320014075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 41435661 1250 41434411 41434439
    0xc020a020d0c091103090d0201020903030d0b0a150f0201060503010b0109060806190e04140114010303030e070b03151f0516060b06070809090f04030807050706020d06090e070807 78
    0x501294503106020751410840798481003070740000301003450b048110303603c003a032580a50310034400d440643e91407003100d501c282c3c04c1c0e215125102c2e526400411038000d041d41568004001c0d614007403c100c040315200e0340d07001d041100e164411400300e120866411000ea50901405001e13203002d800900080104c200003a18134900c40c001d401c02d200c10754000552030784a0314140b042000002044241d402d984080d44260241c003aa404d8840c024400c0d10001d002c00305003d0414081101e041c80e945c260b1071078030110020f00c7d98851030386082c01902c2000a40105542c05940515510012204890b0505041282d4001041d40c3c1d00d08240c6503409480300d054100080d1650003c036000200300c210804e01d00701006142d5242e0a5502240200b00c0d07805100d00100a081402c000351248806038540c080ca500e40d082d4120707002800144100c0c0004c0307010b44a0005048503910500c400750503c0c1000388150142e80298000c03810035a41d890300414071840401410008044e034002400d0034034240110034040710 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 41436911 1250 41435661 41435663
    0x9020907090608060d110604030c050a120b0c0c0a05010504030302030603010614240c010612060c0c02030c060a020307020301060305150705030906072006041b05030102120a090201030e0d0216090c020a 88
    0x7464003805d203801c0c030295084040c0c90200050049545684a10f00203403841c6160107068040c199020f40400d00d04003921a1900346a0071203605136a40da600c0342a0441d0343c5c0007601c00c0303103103020b403d0081d00040c00c01d0040501952180d00d0141c0c903440d1403002d05084031b00c254000e009400754440c0e850560f4032041c4141441150000b002e000e4a250b240300001940b1501d0002c0c280c40d0320700040094140c200750341c10590035126000502880520100032a072004020307102035813540043c48180703164a0401c2c024081d00b080d40c01501d0501d00c0035000a402c4921581c01a211a0400d004c0c400710340c00f4800903030380d0041c0203042490440c240707060001da4914008011030306000020080018000701820f40f401c0304c007909000c07900740d03142c81d01d03101090384012900c100000e411010003103210302d41030003a00d20f40018034824003001e83c2d4600c00c038400340c40075840c103070705040c0e4800d240f00703d090003030140480c254810780040444031032002600784442c24550122081500e030a0205050a5001c902d2005c09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 41438161 1250 41436911 41436919
    0x80903160e090d1d010201140106050a020c0405012402010f060e010e0105060a080a05060d0f05010b040b0406050d0308040206090603010608070e01030204060804080a11030d06050109050904111509130902090709060806 95
    0x13402e0f4050050f8010300300e501c0b0360042e900115000159030355000c002404081400e5095034144040174041c0402c1d40c0307003070003070503141810400c14030790520002c45510b403402038078800440d4010045010b982129000c6d040040c20300005801070005504d410700d40ca004203010f071600d07480c0032041c003c014441c00c8060000c580164843c0c0100d40d459540c415204641034110001d10414a000d2510300d00910b00344803510f001c0d0b82494034041c01480c083c03081408942029040748200c08035a0703021240c00d20024400c9074095030070300000030aa192a000b0358042d01072511040c00e0707403c22040141900307030070804c0c040c101401000144092688041980c3d00640e0000c4034540710b010410b415a403400550b42c01207403501c40032844481c86240d940003081241c0d800c0e01d4900f41c8a0f161010301c1202348044030f01410000c1c0c210302011071401c0960076401f0508811641038101011070340001c03080c00030943e0b1081c0c4583c03541c60001c103525201442d035400480d6030820100142c9044409000b03207900402070351203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 41439411 1250 41438161 41438207
    0xf030309051c02120f150109050f04020901140102030415030501030b010e040c060e1c060b0f04060e07050c070e010603050403170f0c220e0a0507090b04050d080903160e090d 76
    0x30042d4100540303096103c814091b03500c11010207a8109681c0e100348100c0c400c550400c1d01107001d103d00981c0c41400f071500900110550780c01d100a000c42c60b824961120704503c4200400100110140500c1c0d5115000d0b5030701203459451414240c0d41e00d0b0701a007244240340713004000d0000207815104402c00b1500103050000c4070b41e0711240001d80b055010b41008501000113010001000703d10780c40f529502c8011030b050036900415405000840c1e02c80e0151000c0b000d000408141007a0007500030703082c1220300408490b00291920340a01504800380d011101007519201800300b01900b0000d0007280c2111207c08502c07500c0d15080b4028002400f801f031802070f80000811000d81c0c00740f04141c0c80d1400000c00c40c1c1644554583c03031082100401c896400300c0328640000700d0000e502c0b4003689021039030a90039440c03e260510040008000074241c080303940d010100901ca4103903c00b8851008600e5006070008007007440c0c1305400341e0b000401003010901380c210182c500b080c81c0d04060700280940488030b42c00e42c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 41440661 1250 41439411 41439439
    0x10e072c0109030f0c05030d0507031715030a0c0501020d1e0c02040e0f0a050609160b090a030c1403010605060c030a03050406090501020c0d021603030e040509070f0f030309051c02 79
    0xc580d5040d0f00080c04030455000d0030310900c10241ca568045400540031160308141644046407a4020f90344000c0001c1e00413201c8908040300300c19000c0d009440700900e84250324100001034501440e200b001c0b20001e40e00348081149603018091f0b00808081c0d07040c10000003003519840440f02141e110307031005103c03152003840c00b90744855114a00d03030001c9004031942e44035040c5813544e55890780c0300102c49a20541001400081d4003140407d4008800f56424400c03c0c104007003952a0b821810b100380c0c01c02d01c904000008100c0740c0c04e042c0020101c1c50021662250014185803e481d580c1d003100d401036004000301062468000211920080d880c80d00246940310b070f02d80007002e480b0030b0102030002e600120714000c83c0c1700041186190407030340b50222404544142c0d0884034800562101501080c407800b0380c0c1d0543c1c2401d401007540300c10084191203905454560507894402250407668080088010910415800c00d030044040c00d03040310340032440c04c00b0602c452615a02c0c030400074054401144810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 41441911 1250 41440661 41440667
    0x106090312110106090e0615030d110c040603030c02180403200109020406030602040e010806040b0f0c120702071a090604090e0a0c06120b01030903080a200f03010e072c01 75
    0x90b1881540003e010280d950010030014064440031001a40102c0c808107115400311b0110020303415003c0c3c0540103034002c6103401e90b40071491000300030301d030302501b030b007181107550f81d48a600040d52090b00d80040b0300d40d09005004460104d118a99140064402031001294012a0b001104400d40e91300100e40c05800f240305025042c1002c00a402c00d041110100c02c0240b0340c1c02800540340d0142c0407100b00ea0369220950b5485400303580207414808403401180400141401303555105400204241ca0001600741c04071890b201201c201c0c0058101395814024005444031507847c0003d030b1102d103410883c4a500050b107511a511401e20003560320307109080e0403e4188143c4c1101c1380c20480384820599202e401a04804000c1002c10340c2c1441d000f024486076000344100c015031601561081c0aa5076076280b00c00044c107070340c51601100c4003e000c0c000c00c5200c00c03c00600e000b40032414040d40303d500d0100051000e0001501c01401c0c01101c199188200c80c024401c5009000700d80c40c4c80e90000480c400503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 41443161 1250 41441911 41441927
    0x82503020a0b060f040203011d070f1b080708030f01080118022107080d0c06060905090c0f040209030106080a02030105160507060f02041809050c06090f06031e04030c05010506090106090312 83
    0x20345d0f0424000300001902100302d0703460f01e030420092420258107a03a410400c1f10b26040c0800a58007080402030300c40400102c0c4290442c0281c801c1d80344130b00e4511680c071525503036002110103042404500e401480314060a004100e07071400210f000203130301c0041d039000030fa481348409408400e003254050240940141000785800802000301a074521411002d0020410340400c0401c1d60441d09122001950018a118042c407901111000d80741d01454003041010045881c0201d0354090f400f4000010f1070354003840380703100400b40a40101a5691a4418942540c60003080303010030010341c89480b00101c1c4c1000486448503130182001500803801c001e80c3d4001d010303580182008424041480000c4006030740a48981c2c0e0240c0c01b01c465440410041007240c0c8961400b160b00302c000082050310a09002c4003441c0c1000170360140c512000704d101c0e2400003980c800c036000e90025007003180900c2806000c0c070a15400500030303901071b04a9810100040c1620304a03200050035804072030696000203100b80c000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 41444411 1250 41443161 41443189
    0x20c0a060e070e09060106050a0c030201150b040f150c0b070903060504030f1e0518130203041a0c030402220e0f0609010608060415020a050412082503020a0b06 70
    0x401c101110030128580e584071602070300e40f1a11800c0c0204401c681c0c0056518100c031401c0e03131950f00d0003044802c2110030340c440d04000c81c1036640303481c429018985100f20b0780c0003600341143c406490b80d00d04031500400301da80b43c0c844040c10b002180d2494410f0317403140c01c590015402184801c40f03915181002ca074103912070351010341490324142c140000c240d8020602e00410312542d8900c1c08070074200e824030107140401200e11022803010000450000183d200041c20494028043e050725244c1d0a41b07102664000ca0341110f266035072840b00207030b6941c2e410000b07800c0001c03103601604503e8941d020640301c0d12488242d14400c602030300c810701943c165030408003510603004192580f68980510442c0d0300c1e202542d4400ca2035080020209440f040060038600c11b603004040180410601580040203501000a0200b049020403011840e040d03181034080040e80f15808040e0341c2c103114007012041c3c82100d20704070601c054114440010aa0020704000526040707d4a6151500c07100009805080c034000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 41445661 1250 41444411 41444423
    0x206040312030c08060402130501080601230a0908030a020c0d0809060d1415060409020711190801060603060308070b25080402090708010602030307050d0902040905030304110103020f070204020c0a 86
    0x1c0c89886141c0e040e045000b031003600707484844580d1101c6003008240d001310754003900c580e004844100065849110620303048441130401e06041400c41c25070503011403060060801241000031743d221100d51080b403507001800408043c50601d41a81002900d0780c51801d4641d1003020400000303401e03c82540115004210002d00b1117540b035403000c5440e0090181c0c040f11040d1070420034000381400c00e03512038400d11010300804040c9414100255000250040c8006480d1074000b00308400d100d4980084000200c00c102c0744511245180603119804d44813640c01900030503050160410025044000f6030342c03010391040c501c2c06941d54071711445408800c0320308007040c005048605a008260070600042c040c0340280c0365078656030b036171040c180e81c07030344080c0708000040c2d10800014080d940b0600c00b0f4175000314800d00225600e500d5030000790070340303d8007881a07032aa040041840200302410001d81c0b03140200b8203041d4282060340d042d54885000b0600c000c0e0045d82c0010360518007c2c0c0a000c2a60402c0d8010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 41446911 1250 41445661 41445683
    0xc0f03071715090c090102030a031a030a0b0f0c1305040c11250f050306040209070903080304060e010b0102010b03030417030702040f0905060a050609041101020c0904030e010e010c0f03080402060403 87
    0x5240e0740c0e4205011510340c01203803c240400c411441a1040390b0300c0d080d0603001117150402c2020220300078043c031004026958000c0303000b803180707035000c0c00354058140c0196100c01d000e04040110310048600503064030213078041000320b002d014003007061120848804460000701300d280454103844508a071000b01c1d50601586c840704242c030140c0b424080200c1180a151402c0944440c0961b10300003240c0a89a0b05600c240002001031501e68180d0344d00014900d0700a4603687d481d52030144540060740d0445146032945d403841e8200100344141c0300040000d1000b4000701d09408042501da1107035004003024000c2c1350140b46402c004c10400c0720b002d90303805002003180000c94071040300186000c481c1203401d0301403440400c101035014001c031800b40d035004000c41c6036501c440d40d620040c981004402d03810750082c41640d44e440e40c0c449000350f00c254003a4882c440203e002c04001080d5804407040c1c24140071080c5010303400719003242d002001030303a0305003007600d1b05c0d80300d070300000e4a20301940d440241205151 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 41448161 1250 41446911 41446921
    0x204080d0507080706061806061b1b08010606080601110120030a1808040510090b120406060b0304050d081003050a08030a0e030a030b040c0302090d020409140d080105030706020102030c0f030717 85
    0x8007c410240c5034442c0c4104030458980350304580d4603181c2480000764034030740d102100214420310b410340130101d080c03481c40030540c1d501c4078140e00b550500d80c0000d0128022404001d443e5805c19601520641128020880c0100396091111150243c424040c80d140000c00025411509503009096881c01c0c80b10b040c20319044d0b8a05204981d0007070040078001d8a000200800b03160050f00443e0542e03444401860800d5100100d400d0b03400401001600c000b902c900f80025540003440045010302d0042c03002c0c03c501880480060017084015180381510000000b04201268005c00e40e01d060383d9110110035680c0e294800050050401e104072100c690100250455003650164420f680c00c42c0242c0c2c080c031030030240070303400c0c3d0480c05041d044540103030410311588018980b07a80144800c0c2d1184040001d4804100030451030054180140d0001c1112036005100900c3d040112100801585c1700951840c9001d036448805805035504002c0003100c003101141c3c2c1e6074000d42110200c1d00d417480306d0244d98644 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 41449411 1250 41448161 41448179
    0x50a0c0c030c020402091816050a020a0602070302010b0904111e101805190e010509040210030513060203130b0903190c11060a080f0907080d0e06040801060e01180204080d050708070606 81
    0x10948010541071035521003410b62034049c000343d5246004980240c2040515a00c49101070f6100c1c0714100c003107550352802640700340c0d262030219000d1030141c5404428651844203201c09060003403694440d1303100701c1964148503540c51450310720354902c52401c4036103409903403000020407855410695101d491281c01103450094600c0d8042220344101521210340d85e9401231200581c03055030301035000b0b4400310740c06003007a00079004030382c0114030300405192061041e101d817000c903002a28510034082110034004140640510203a400585140c091840c0055480182014640743c0c26140c00b40000050007070148100100204140000a030240d80c2d110320440303004201000446540c000d03188280c0114035000b00000b02001510040781c010030391590506010307a1040807165203664032036410803000c01c0c600c000f806840001d024071b46d030f00301c499410281d20856001b907004e46150020300c10300042010100000d082c0c8115406810407959406030740c201036005104542d4083c0c4407500b032031400a51068 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 41450661 1250 41449411 41449459
    0x110301060201051015170c1201080f070b030c09041e1107060c050703020d0e040b03100207060506010519080c0c0604030c02030c030f070b0313020a08030a03050a0c0c030c02040209 79
    0xc80e0b130a0505059210000b00b1000d80041c002e080002d4220b0707216a00458941c009103801c03840034003140c0d0038910210781d03611a5071001d80110303a85030400e03c0015901039041249102030003031842e051341149000c41080b2814000c4010080c07040d600c036603501e245100c21601409885a00e8002880410a07c01180c000341d07200e02800c4642e1403405000c00e0380244035800b920f40859056010381505c01d185c40044555602a1603040c1d8050b0740c0313020344422590104001c000c0d1464800300961a0080c3d070500301f0854000918886c1030007010042a100100318406c407980c440403d003407144007074644c80c01070301e0280900e00a412052090105000905030403181a040603442213048803084aa00414180c03103842d40e08040d0010750040b68240118200380d030140d580103242c68420b5142101c140c0000b01e9115417039226403625000020301c0c5d11800d506008055128460300802d1050b1802004003c040c480c2500c0040c0401600c010604215566901200c3c84102c1c020402c0780341012a5000d020621 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 41451911 1250 41450661 41450671
    0xc05070507060309050d03060e040201030506030c3a0305070308070504030623070f0509040e0f0a030504140d020d030503060d0c09060602010e07030f03050c070b03070302070201031a0901050f0411030106020105 92
    0x442441b50030711040d40b090142c1c40554085010400c56600c803a40150b010b008040c0c40a507142c02400305480355501c1c1e03c4c00315040d400216203079412044191100551420002601041703074400c40380724a011036080790403502d0741903251802c2c031041d54446404503250301690304010115810140806440c8070035a5209604e101020414011a15807110607143e80281c070502901240050144100a2400b42e02c0100880315007401d81d602040d99564103810320007214011008104041420300c58020400d900e807030000380540d0202030310000d64001885164901400804001c00040091060b8655012140300154400b00c07000c0c6958840300401d0141c0424046c404c01507181180d00403038032100007540e50880740c2040320362560f01e01548003141c641e8000100c041d011312607810006003811214000314400e420715a001600c0744150700c0014251010900001018a018800c1d590307203a88011201d13044890868070940708004010104015192800c10354103450f8001c000041c090b45c0641042d8410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 41453161 1250 41451911 41451913
    0x90302010f08011809020102010e060906090708150a0f09020a030b01061202040f05060306060c07030b0f0112051e01090b0112030e0316050907031d0a0b0711030306040c0507050706030905 82
    0x49000e0300c500b01d494280c244503005201c51051251140b50103158000600c4500600c004503003202c001070b90320700d000010745201e5400e41c001d4040280b080402d001c0d4402030801c1c4006880a80c1181040002c030100c00741082e01001c1c2d841a00f100c03070b0000c0307510080c601075000e0190b04009030303a801e0440c40f40d4001d204110100702c1103004604180007a2007220309480c040f6402c1d00426080c0340902c0403940000b0401508408104108166160104040401144150395a030b03035a19016855610440060f400481a2400e2490700b0703001802c041800c480d607080120b05000041c41c803036034050141c64101d00141440e14184004914070b02d419040360303002c1340a5112042400744031028543d1755041c4080100d01d011081c401031259152100805030052410f00e808074645070071094501c482c25085a221304030781d02c24800030302042040440190b00159600300715181c5941e00032465102e110041040e4480c036074452080081d140103009072588990408211942d954070360602800806180340180d544d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 41454411 1250 41453161 41453177
    0x120a0f0b0c070507150e09010b030403030609023a090506060907020d120218060f03070f08090a03110a080301060207080c0d0201050703122706150b0a05130b04030309030201 76
    0x80510000c0440382d101d50f0000040906034a4120031070b40d650329801544040010a5112a1840d500d0030217460191418280443c0e90b403e051030050200c84540c5d008444c00c50052212124012004454920080e4078a01140340700e0301e803211100a00001e03481c1c81d02c0c0c4d0b6142125510074048000782e810322440c1d054038121a00d403540070090b0b80d1125480c006000080540003c0ca1080d82c3c00e4002d400843c011100500d80360310004000340c03141c0c000b086040c070040004005c011442e42d22901d5182d04040310f0034540700d20b003402d0301195203801c10050081c0a0014800e0056041401040803110041c0c105141a44a584a01e8001e40354502b92040b06030910800b00024164545038410070580d590584a107450150599401d40e010403c0302810340d4003503a00d5503040e041e8440c100070405000101220b155070890b1510b043c40440d14034058680c10141d031400c083c0451a50001200e401140e03c0c01d00326194010341041060300006500098003603107000c42c00104150b0403107030010030340f4401d80792803030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 41455661 1250 41454411 41454421
    0x3091517010506130605160609030503190621080f0406020c0307060203120105010e040f1505190503030d05040807140703020a09021602040b0102100504140d020d0e0f120a0f0b 77
    0x200c1401180c62444e00d40b040500100401c40c0590003c1003e01310036076a011980c55a034946504450300d640c4181e0214100104103c804996410708045505400008101e0581001404030200c21414079086581e400e03045e440042c82000b030155807000300c0d40c0d0b0754150785036142d440081d00c034101484880c5c00f0b132081100101d8480e00100a0700c42c010000c00c070141c060380c606001112070f5800f801d401c5800c140c2d50001034001411501450707100c80c0c6110b042c41c596030324240512803031a86840c140c1407418540c040920032650003104803000f000a0f0306000c135403034803141006040c038400c1240c000d060540f40c2c0940b84006c00082000800c4078000c4803d021030340e030380740c07120810b91240a90800c0c5101d14802640010b2615501030034211a042c4120f41800c0d0410011030119541504c0c140ca0000d141c0310302ca00300e041c1c01c001040303245805102801c0c1700700c0e0410025148031501c0040c180714980322404c19240741c460000c59035150341000c040710007001c61030500c04026a46488140e4403004411b000903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 41456911 1250 41455661 41455669
    0x1302040609050d050c040506010c02040203070e0306090111030112060605060c0601090c030b01020d080703020d0f0e0c030d020d030905010b0d06020a02060f090a021e0307030c0807090b01051204030915170105 91
    0x40300c107640140c09003d04560b08170420006000c020075803414069201c11400160f00c961001d544034000e0394448240d040700520805180000050010103668101281d80482000d1001581d04603203e0900140c6080c2c01450070201070031043e08140e801c00380c081803160715110009000d5040b0749200d0790422401240c10303005c42c2610041201c45015a2268642c1d02403135200f00c035681e600c010030745001414031080d09600c1c42a5074480c102c030043c4584070101c510030344178140807c2d90900300841c01040e07031104054002e501c62080b0003120f800d06958050001c1804402e401546109400500000290702030f854460029000750310110014440c0c540001c0100e07502d03191b41c078003404601c0c00a1880000503400c100841c50a0070030040108510340a61005460405c80d010103907220f01310134801c09050100140c9406420741c441003100341041800032030703a43c12101704c070190030049440340c040350303500e0505880f151707501da0280c142544518421b1101c0e940c00900040d00e428110404403c1d80d81e110100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 41458161 1250 41456911 41456929
    0x60909060506030705030402010c0b090a05060a02040623070203070902031f06050306060d02040801090c03120f0818190605100801060e070302130f0608041716020f010c02130204060905 81
    0x19038110b4410008190168052005103910510500d81100501d0310b90b60f07554685070381239911440580c0f1414544040103018080e0300d80c0800ae00d0800c41c1418907091004100443c440002c0b0f0600021602401425240704210b400594000c3d00308e884169030341a0303020007980100e038074842200341d040d541c801c614540c559070001c0352110380d0f0b1542580ca882d0100300490340711418401d840c603400c0000284100307007801000301c8240501d1a0a41d01031850500c022140802c801c0f040c00c1001c07514a800c91641c00014007600320180d14a100c00c10207088428910b414030504c020620991003c0c154401c0065642065115003184400b410819542e14403590a9407814010440c140000710005034a8610a6000c0e180e4075120f441c949403010798400c0949070800c042c0d0000800501c00b14104418402400c1801002d540811641031030483d5101100040b070b40b4039403000340b02d00268031415803168403402c820303200c282e00142124406607101c040e40000794014072444000c80c00e0382c5030000b0a440d080c100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 41459411 1250 41458161 41458169
    0x516090b0d0b15120102030603010c0203040e0705030402131521020d060905030f03040303050405070f052107080106080a11012d03060911030f0c03070203071506030501110406090906 80
    0x4190500d040c156240c295215006190041d000200c0c3e50b030b015a070341e4408011a01614041c001039982c00c12000381425941c0d0390303d0740c02c1950320410040100a00f42d07a800781e4030007003510340310362030385c50740d2000a15103044203400303001440c28491500d80140700007803541c0032501142550039102480c079a809081d036181c501d000c1e501403001c80d003400125055405c409034803032040d8240c0e0320b0b1400c104585459038106035000e6000942d92000c01041000801281c40a000b88000000d1f0f40c61400c40000d04212104640944941500054609459082000030007925a08009000d181d0711949000e1341c4445611040d175000303034900700b0180994080c0c214a40803040b04c14103940400781140c59620042c1c0f03c000d55208140c1c0c0c03643e000885c02014443e04400301c03a9070f80860381d24107240c60b00e85010940079000050f40b04c0108240300d01150004122800039a20208030041c2d624141d6050009020a41c8007614550814141c0082c2d103040b00001c100351503080d00e40141c2103480d1b200e00300c203c850b5170007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 41460661 1250 41459411 41459419
    0x15030706020c0108040c0905041b05031903051b0d0c02091005090408300108010b030c1c030201090209040804150203030c0406110c0d0602030115080412080c070f0516090b 75
    0x702e42e09541d4420001c1c0b6038860700412020014580d00d00c80202101c108803000d503100034140c100c1700400307146c0c2e4002000a04040300141010308100000c2e00141000200003424020002103594403183c0d01c01392200400c03050001c0c1c07061400c45010103408407058500c100d200324112000505c8140810580b6425200003030012404c9a442d9a90383c00c155001c061003200d030b40d100f50955080342240c0c844407002c00ea07809a01c1c0da910b514145001e820b44091040d554400c3e04030851100303403901c620034400401076141d5103441d0480750508041c3e00410040340c029410074002c0d400c03c018006104018000c403915540100203003d007064040741c69000968407010300c960108010060240300b070b402194100740e044141e55250b04480c00241c0e000100c0c841c201e40c540d40100c010001d401000e42900c030b80c941c040c18044054605580d038000d440f411280404188030301100810140c0000074150360403984d00ca060100429014200141c0c0da10b50710b8a002900314042002044000d154012044a050050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 41461911 1250 41460661 41460673
    0xb18010b03070207080106300317060d05030c0d02070e04080301030b07120c021011040b0f03090102070f0503031014060307030509030f0f0304060f11031303021006060201051503070602 81
    0x4860341d440030708103900310f22039040d010400a000788101e0008102c480709040c06031488030044d4100035140c5100401d0544801c0c040004a03400c202048002e4141070510480782e40d601c2d000500408010350301410f41d1002041e24904100300188030300703218010f6000c17507050070740d40c0251900ba8101140d008082002c2072004000140d01e40c210640c00803528207000111840040080007110007405001c00182c0c400301c00c8841e01501880b840300203081d0314003403900c1e050600444e0030440c8101c80302201842c20000018040100a40c1a076500c140d020000c42d26143d1142040340e0f070303a0000e403000e24800c100d059000a000171200e00d00100c140c8013504542c01c61781c60000c1603000700340060040300140020002c0d03440b200195801010138000d070240d800d807282000c5c18801d0031030b40d01340e044540790782c503201d2185405085030042d245e0000f211445041e006800d0320b0300f02e04068074540d211501c0c904282010a2258040d000359110b0081d0500b0f01d0440040e1804259484c080780c440c090250f0004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 41463161 1250 41461911 41461919
    0x409060e01120807050c04050c030a1109010f0e030f0114041103060403081f050a06020a0302060604020c030403020607110d0609060c031505010f020703050a0c0f060c0203070b03070c06050106050c010b1801 90
    0x3c2d0240c5015070095003614003001c0c8480205017920411142ca600d42440001007105018070f6225011098503400c45c041c0c2072800c01000078040100507070844041c007900c0307100c4000c180d03010417401c180c90219500901c402413005c00b0500c400f450965003144d650020050054050a000401034480c94241d81d9000168851107070200c6602c010903801080000c1d800c001081549034020220000c1c1055401081048400d0800038245000035101504c01c40c01080011a421000001c0d03909403901104e100303643c2e803001c0c0f6120b00d1b2103440c080b20035004140b114240091007080d034460071000b03004010501c0362200c03050007102100c0c0d800c01960322002c040c06042c4915440b80101e00a000c0031801140c0d15952661903191170004010011079176001042c009200c10349a0340300d51401040f103410034443c0c01405038006603e80e1418010381100c00c02c0440010701e428800c1407d4a4007a4110408201950312018010642e0f8000908440b4560030880107034114100034001000a03403039070100c86d0a503420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 41464411 1250 41463161 41463173
    0x90c0602061902160209070809010c0201060302100f110109150b0d0b0a05070201060902030c09010212030c03150d150501050301180203060a0f15060903030e0409201201020a03020409060e0112 84
    0x4080004e06000e020304140016100c0e501094050b40c060b440b09003091500802c96400d41e45031242d12021079040040c01c000580310782d10341c007050720201d003040c0c0135480c9030702c03411214440040c003444a030350301701203011090103a48490341d00c440000d10b209000030f282c1c0d0020301c414003001d0400140913404810020ba10240c0c1a070199800c00c1c06840040b800b0356640a0304802d9030401d0360706e8013514000042d190a070b03680400450600c89075000b241425032034000140c40050000130308212185060030040d1007903580b001070300710a080e8070810381c0d80e0a808007841c00000700406d028041c041d40c0b80403036003411403622130003000301c1580c000e00800c1c1d0b9640d640c2c0800054a507054031030012540300d03850503249201001084015121581e0345035045031850800622012015094500132494465010041030142440c60301001d109070240500c000c904001c110700100d409520056544049a042c28181d8150000e1045844280003404030948038180d801c0d02140a2003550302c100c039041032010004003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 41465661 1250 41464411 41464417
    0x30307030b0a0810061508131e0c030605070305090303101e170a03020d051201050418020303041509050a050306060d290106030f05241210090c0602061902 68
    0x1000c1c02100107595600d1038140740c139500c010a21041c0307465032000c0c0840b070030115001621441a1503c00520b090500100003151207041e40905500d0180c40c0c0300c412030701c0da660702209069002e0012642075903070b400d205009000540c3c10340c1c0000c1c01c1c00d010580b07002e400000e40340200c4ca51707201041c40c580303018100d60b000000b010744ad220703106d420180000c1302402d0704904903407203890001400b03151134645402420b000c0704035044014444d00b0b1040c0402c0108000155045d68400d07900020041c3c0c1c5d15032003c0040d041c80c40002e43c503100010340818098400d01c91840f041005031a0107032070944a1040221200d140d0050a405511540c0021024508043d48120181c0038030166850301955803020004003207007000070424078020100400407194184149107a01002c01e60411880c20400c150300004440c00030480100381200e081410701d0340d207207070b114512030040d4803c032040f00140c1c000800140803008800d0307440044180780022a540085480c5100da1401701034003103034004242c00c20000b50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 41466911 1250 41465661 41465681
    0x1060303090b0a1e0201091b06120902010519050d060e061003020f040f03060c0f03230c1b01061406040e0604020706021603020604021302090d1217070e01020706090803030703 77
    0x148503044858803000013085000b400c040d6001242c1c0580600b1b0002c0300c0252502001c0442007201c10801c403003075020000281c014a5981c0101e41c914150004031a60300807007084210102030035402e00700741500400140b102e0248080140603c03590348402001c010412107000b60000e0412124400303c40c402d070300074010583d900740712504040c2c45500c2800038400d1070b08111041a626070b407a00d58281c0100300d0205009061030180040c490070010001d1082c84150502c00030981100070501203202c0b02c040e583c0c1e4152248011319090060300d0418041c050031320030000c07100030341883c040040c01d09200702c80590390810030380e442c103403540014000207500450b804e6400c1d40d030902c00c6c40ca840c81d803281359418181c000d500501d458100341c0104203000c034201c3c51020300b90344100700000c26a02d8030034070310b8000c54212a903d13141c0c0020740404d54031030400c03001000f81070205408100d940d58011011f00c040300c50a0307084035107031602c811003541c1307480690203200b815910a0001070140c034800e8200090361 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 41468161 1250 41466911 41466917
    0x140a110a0507210201050d1e140a0b01050c1c020c0909010c0306060302130b031f080a21090b09030a0c080c010e04150302120a0209070309050f01060303090b0a 70
    0x4600004005400c0800c468401ca6003500240c5081015202c5404a8400600d4103003100b00d40e503c41c0d0340060818818040000c0d031254035465400305111060041860015040130140088150740c001c44803e10400c0354030903001485d0813070171810340d4890002d580750f02c182c9c1c4000b45499040c1c8107400241d41d000003017034800c500c201754282c89240c884a5181d0300800715a000480c4400d801c82c0080c2c180c5140340c001504052042c45185000d060004030042244d07035188010b0ba807500c86103c04056164201034510528140072000510150000b440451041c080d081c0249a2840c00d182050341480c3d909122001941c481d2051041f0076a6100a00c8032001c0101181e4100c1c07200e560301280d502a5a00254031908030400742096035822a0b0382d00c00300c210072282004881c074000002d0800ca00b007400044d000e100e00d4590b1020001c4208034130034040760000d002c0d07182ca1400d248000e0140c01c60a10480d0303180a00b5136214404007050090301e0a0320791540310044024100700440d04260020301c001020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 41469411 1250 41468161 41468177
    0xc0b0a020c01020706020301051008040c09020c0106050a0e1b0408060402090a0213080115290c0703080c010c09080d020a0b07030b1c0203070608010b0a1206081506100203040501140a 80
    0x81d074400744028000e052140708050b80ba5803402c02040001d54642c1000320a000221081000003146010300c4030a0380c258200040e15040184401801440301c0c2c1c01043d00800f03120000300303103554100c55042c400c5000010b40c290b0f1020600040070719010303500c078100300d960002c000708005190503048190310404c1c0c1480142040c80d081c441c0070414000e5404800565958041007000c420102d200d00302030001d094103c1010a0540032404c0c4c0303000c0c40046003823450030100f100440ca220a000726002550007070201c540702c200e0907803014000c0c48a01c0d6102c0c0401d401c00030001340c034103000c02d010344a03210b41d801034020601a519403106194000749000109076030b89840000d10b990724001c405a444114805284410703051050504d05400360700842c0c02d21155400400c00c0e07102450031103510056038640780c44050310140440c4003618580e0000d02580c0107195020580035030032030140d03210b2001240c90300d5a08600400c01d0b600c13442140a444d000442440c43d0005c1c0c0d160800040c41950060315105130 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 41470661 1250 41469411 41469427
    0x20a02010518060d0504030306050409050a0215040e0c030601030501060f1b0204020d0216110d020a1404150e091204060f030e0a0b09030714060c0409090c05041a0909030702010c0b0a02 81
    0x2965500003400354601170360300c40600051603494814030000d0318003507070104803c44690f16003980d548004400240304120340c803c50303800d03242e440042da402081c0042c0c901f9540c3c10b200c50760189541040b242140000e1902d0000900d65200d001c8074146100e03591a444490459248010b482c244840c03130076a00302d80c08101c00c7d41100d04c940300a252710150603000000046483c50310844d103116180000740310350147da40e1540540d0390460301c9001c40b40c0f4803c01803405148003000c02c0103800c80a0030420f8422260400064000141d002c603031213490500180c91b441004a070b68100f00d8001ca000c0e002c00500500020050180070398851316060100f441101c900072b903e580c80c2c02d0204800c88915007139030004621401000303d401d681c0056032141d403010f03201c5840c285030210590b000301c0c0309002103281c07203007500c034240105000c4003000b919000c0d01c10700588a006120385401012005618011503255000441221002c025107502e41d07070594800d0101411501d880111110251610004071fa080046403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 41471911 1250 41470661 41470669
    0x150302030d09031b0b09010c0627020108060414011a0c010203091501090b030606040b010c0203011a01020f03090d03030207080c0628051e0709050d0506010f1203020a02010518 77
    0x804100550703901c91420314118600700d1340b040c02c0c0034141d00442098500c240183d100040070b445400d442031030505c2c080c1d40780341442e030054120494241d840141600b106040f00400030003c640380c1c0d000f07032508901e0b52118030a100c22540d007002d0840390030f481180140541c900d0740045618455a40303220905040006032040e00b203a00984200c0800e51010b900d000903054507440940c010640c03a18200803815805010035141c02005181501c915619050080d040e03002e0000c00d011190060005c00144050780c2e0600000a031810383d0382d000d413041c0000400002d40c0041217540c3e402c009000342d0701c00c070020b42d800e0b00a5041041c048507408418481c0d40004c11040100e984994800780a201148082ca10840300d40000b880c00e4400c16424101040b101c1c41c9500c0e0410310409050641d0b10265803603000071140003d0b55000b140d401050008140c2c00d1180010341e06060300c00d80d58881040c256202d050300801e44500c60010b0168210400880266010300098022003c401c4c40c21005104224005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 41473161 1250 41471911 41471923
    0x6040e0a150501090c090803040303120608060f0603102007030302041a07060b060309060f06030304050d060b040f0b010c0b0a151d0a0203011409040206040305030f0309010b01021f15030203 83
    0x34050240c0e10401001303082d20501552020358030b1800c1c00c074a0a030600001d15100d20543c00090103201c12450000e0001c4890786c804e030000c0c40580c0507140d26041040141540131000d41d249d501c24414594848942d10491107400400032103a40040f001c4020549900e4241e081681e058007499400e100001344640c01c001241c411295803182c0c903589075500d24140007203403c1403109034000c08092013004400080096603e800c07968500c84002f0681c0d44030700007461889940c021030381200300044003008010141d00010a442d03001c603420700c0035140c050a03030011038080352005030008500c202e111000c60005445103400c05c00c41c4101041c2030341e54011102c03141c0b419600200090b05440003600044083c100010380189161405524552500c02000d000e200d0301d43c4042c6c400c0b0184000700e011544d07000225002180e010003031b03035100c2442c0c0501601036001250945030550070540075150640c4041180d580d1014820311a14840100b440c070700c0000c0c000b8001c1025402848800803025076410804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 41474411 1250 41473161 41473193
    0x2d070c0e0103050d0513090b040b1302040501030b0f060415020c030d050a081e060f030f0a080318010b060a030504020f0a03060c1b0812091e0106050405060f0906040e0a 74
    0x44105039500d0361610618046078500380a040003024030000f40c040306a0003034407003150f280c43d1000c1075040c041d40002c0e00030080016071503070106988081038240310040c1c000d0130480c1d100762001c100a01424041c817000703600d502000e42e8041d50800c4144040c5454a500114100c180d20494040e4040724020a00d05250b148054001c502d001c1440030070190310808180c1d1040441043c1d65603811110300f952201000a0b00161048074402914010354a040000d80b03c3e42080b542100d642131481c0c2003c5440b80d106840901d00300554061708801413005010300f11209002501c101e103001c00e4100101d00404c0050400c99011800c03000030318a40c5d803071030804005107005e100c0000d01114601c1c2c02034170920134040485400d81c0ca000c3c0d81c0c07000c140c850041c1c0e240c40004140c2030304640ea0302c207540350610460000d03d0040c0c41c40c9018500740700405600c120191001600e0420a5445030f104000e106510010703e00c0e4001d100b580081c289082c02d8001501e44030469046403003196050b9101d40f0540f1181d0701c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 41475661 1250 41474411 41474429
    0x2502030412020d150e1c0f021e0a0512030108150c07060504060e01020c010f060518040204021315120f02070803150604180905120403020d080f0f1602030c04022d070c 73
    0x1210807000c10103510301a1141b4070381402d0005e92041d410281d1104140440001c1c0b682022204410302c24040c49120902613004040d00e44462403050191100d401c01c1c0516011841204840d150b1313981100a4117001c0c1002414150420490f640c1c1c0b60090400208101c410079102d4121043e0003d00340040c01d50b5010140010034090038054908040700c00aa2140d0720890b044141540070305200707900c0581142c1c05840142e5034074800348044044001c6548407490701e5268840c50341c02c482d4040e042b0000503210101c00c3c07080f0295141f9180981c01580341c0903110100810104e03d9040e009043d00e440350030050112414999214601e2686414003030301200d4050f1103007181d2041240602c5a800a461080c0100d41064255004641da21050080060000728000b44046647c20020181c9100d050440c4020707640b0020341c44400e80704140e01000320b0091107407442c0c03103803d403400f030094821001d85001b110208003840c806500201c0c81400d480286150700b04407000c08548000007a10282400003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 41476911 1250 41475661 41475673
    0x2130509030a180506220f0803030708090102040f050f03211209010c0e0111010e0a03030f0b040e0c010c022101050108070806100501262502030412020d150e 69
    0x2e940076046a141c01a9440780308140c40307060100765220020354910404003c03041140c182c0200781942410340c280c224920140803480005903413600080254807a03940f83c4d541020340d480e07002504c0d00342c2c0543d001d04100290540300038403ca050001c00004205c2d0018100c946288070003281a54582d039001604605060000d00d495050714410342c06604100204002c00910071505002044021302c80c0c5410b040100c140e0058079a81d02c250003030310810a408050b07800c201118039002e001008a95044441c0c0c60808480c0d40d1245498440c030f5201a03444005488060403030001194442d040ca0b0080384d101e250361256064140c8101895540c0285903800002d141d410300d0301c8645840031a40c00040264004003c2200314103005001204440c0282404c0179451034620b8200590403800c0348000b08510118200204080910300c0310807090302403400f03145681d1007048120f889104a01030b05a69181828808006042203c00c007021a4002d800c1202d0800c103140c45801680da074543c04040651182c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 41478161 1250 41476911 41476927
    0x501020714210c150405070315090c060f080403050a02010e071409010503070308041a0904051006090b0703090e13021203040f240f02010b0d0605010314010509060a090213050903 78
    0x358040703074440442d02c400d905100101440c141e4409554840145091020b800320703082180800141e030203150b1194200c2d030b02c5030a04c000f44d0700a141d90001602d40d0340ca003880c0041c5540c020701825110500950f200011540c0c1c03900d0a0703880b0340c01b0122602c1190360307540d980601504140840400707414a509180310f040c1c89041004020702040c2c004504c41c0d0800c160400001311014100c600f01ca189108059170f9581d6038004001900498103d2500a82864100500ea000c601c0d0407000707580e0305850343e02c110364403001000841d01942200802241024405000200c160016564030500d182c0d42c1020781d01d401d0780800c10101a8841e030b81d80755400030405100d045801074403280034141d50001180b10202400f50076a100301c0c03d103001018409900c80320207802d41f01790444003001074080c2160700305407090300c0c00200401d424801a218960166084103810700c06002e00c80c02003004c0002000251201c03030320703403004185180d0100e07840211941140007441150180d03921a80300c0c20f003d55101e40344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 41479411 1250 41478161 41478193
    0x1209050a0501050108060105031908040f090f1406100507050f07150807020309100503090c1203040314010905030306100909050f011502010b130c050408010510170705030c010c0501020714 82
    0x3c1a00480b400381c0040e40140300b2510300150351215546c40f4540403140620031304003080300b4411600601aa45039410010401d100c043d00440000050001e08101ca0070b0902ca00c0010100242c403025400380041e5158041148203a0103000303a640148291042c4400355080c0303900c1d02d000c1d0390081c020401003000401e0015000010958006142d0020b5407038400b500c00051494085568090140280400400c1e501d10003008109010030014104450700300207880348565a810078482140d560049401c2c018049406000c1d100fa2158058003c2d4150303110b00d801c010340340181c4140e850400c89900000614007850b409000d00850070f44506031450350401215456008a11400106580c1001080740403611021038481032061442e5000039007103c55a004c490b140700e19032101580c0e60800003448403401c501c1100c0401c0705d04120360090001d01c1c1c00039194488103a4410240d1581000c0401d91855004410048050b4412000103181000300c0c0d450924659800072040a582d0020400070200a5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 41480661 1250 41479411 41479421
    0x126010b130b01020d020607080403051b010903030f0c091202240307080601030b0d0506010e070203040801020c15060108040b06060d0b030a0b010305121e0c010e0d0e0103050109050c16031209050a0501 88
    0x240341c0c0b0107047d50340713030401d0301400020004e00010100000042c0907a487d142c201f000a2400340c140e0020302860130b0f581402400348c490801000e006500d00501d10322494003401d400000c9400880242e42d40c84195000c2115040100124003003c840405d000d08521a1a600440c4214019120031001c1d05000d0001000c0340c1890010601821010894601088001686174115003520080e00b15955a0110803400c50140340d11207151980003040c000d03801400401c000707845806041c002076041e6142e90044809080549000d8044800900404c9507824500d004000c480c1440202150a80c02c28011a242c000500c8007950420030080040c02000320901c0518010740104503200d080c080c5441c010b0b403040015003003000615200168411080c942074002c000c40450038021340304200401000504544406031441c2c1c00640303003800100d040d11041c442c00d4020b585143e00181415565a94500000d411140c02d80c1032024003114070848a40724010407400324401c2018041c4600c640c03410509540b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 41481911 1250 41480661 41480683
    0x60405031e060f01050612060a1a0c1507090902090303130815070509011209021906120c09060507020118050306090a0605090303090a03080705120c0c150126010b130b0102 75
    0x143c3c1500401c001d0740d07200191075010081814a0040b51115800508911050360015a4448281016070411000c9202400b05d04e0700c01400d82d0071000c65103c120200740f608548850120f085403400b40040541a4050089040041e00310303450080c0140c1581030705000e5910503911640b1281c0104800381c1082c0030541c000300d036420b10300e0804c1003400019021041310540601c0c030310350f0b51005100b99071f01c00c0b13509400c0928080c2140910358070343c5d80043c0b402000458900b031203030501c03e4504941c3d11580700700f07080303422a0340e42a080800690044440c10701444415080207202400400c103a0b4050228038055004c04000704090303401490160152540104949502c0c0c0043c0200180040d007c02c182e0000b0b036051601071480d50b502d4005131210301a02c1c038419146c20015003004181c043c014001e20000032060308542a0700000311461840e12001d000380c84064030980184c0c0440c2414180980d41010a071001180211001000c1041040042112580e143c1c84a5480c0500e5805104a00041d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 41483161 1250 41481911 41481931
    0x606030f050114060c010603060914061810020306011e0206010609090204030b012709050703030905030a15020d0b04110706050108030f04050d020d1a0106080a0c091202060405031e06 80
    0x561400e0910f08000a02c60b0b01c4601400f00010340e00720400d03081d0b000b6400340d41d00030420400701011b803d050500e50300d1683c0c00c1040d4070541000c20340540000070508000c6c03403104001d0034040001076107070000e074001411290500c403240710010725480c40280d48140003441e80d401017070590700d4004001c0021320594808021a44108070a1020400445c40e1505503074121481000d0000c0f0b507500d585015000c210341280c200c0c0340c15015030401001142e1081228002e43d07640703c0107904c070b900f011740320114000b001304504c4040c0a800c2d2156955000382042610300c840008010100070045420303661102b114a019032000600b0320f0401c17402e44034460241c0b21003001541010300030700c40311000340300ba070048500c02ca180c070000c00c0440d55050301440f541c82d40001c0c0d54151147c804a00c1b070300c41400f800b03510b0128020310000b801c1c0b51140d114000201d0000c0d03444d0080c0b01d180050300c119003940b9000c00c0e60030100402021030f09480800983d0060345402c0341102d510340e9441401820f003c8080c2230310f450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 41484411 1250 41483161 41483171
    0x40b0105060a090e0924010503060601050309031210050a0905010e07020d0f181206020910020f15060301091a0403090905070e0405060a080d020307020307050f2107080304090606030f 80
    0x2240c0c000b211100391481a042135020b5110004245d00e4095818419054039540038012210000031109290491b081034085441c4c58994138015545400210b0703d41040d40c0c01030040d5201c0300019020182c00008040780e50580700e07241d1009c9030b009080c0d40c0050744401d4a90700104000038145003599440a040d102a0184640c80b1038000c010643c0320005800700314004020816408198802c2d200808100a420242000600d49140603400541e074581c0f060024400644c0d5003400454036050031140c1c0b10250000040c560100d500510010b0302c16a01507590340d95800c00a100044441c00e0740c51301c00008a064985803800901e540c549410420640381003506003e480750300005003854a060458000c02d2030386d1400041503040d65107610501342c0f031051107410750782107401000030904030b40243e098810881e1076030240036040c0030a561503074220110384000c101c0400c00c091000000001d0f90192504170781d640a0f02ea19542083d0019004241d40b0740080003116010b11414165150400013440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 41485661 1250 41484411 41484427
    0x10030603050d02011a0a0e040314090409120305060d05100905100c1e03060e13050114011806050f0d030c0c150e01080106020d0f03020a020c0d060b120604051903140d05040b010506 79
    0xb0000050002424000084804030ae00d0850300306443c1c2015000c0d0013080b50700700605004007484c2599085001207494840030800c5414120b0301e146900d90003000034040c6603a00382440000300030034041951a0f0044440c949400302450180f02c00781405956511542a10607104600a081e00030541c4181490303c04200445801407804681c032010310140307a2034407413035810920b000d08902e81c0202c00900911002045140444089074802001403d041280c9600c51f000c0c001052914220107a014034000d0b0802c00092107150081c003078078880c0314404441540d58203078130121020300818a0215446481012003560700c02072081c01445144001d1520541c1020081c020044c6082000c0401d070f0002020643d5500810100784c406038050412000d80b0128181540140091408144600124414800c0e81e00c40080d443d801030790448007a0000121900304030449802c440d9040b42840381c3d6511040d040a00c070b43c080c0900702001c003404201450709142c44040c008058014910403082809188 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 41486911 1250 41485661 41485679
    0x1140f01030b0c0c030703030c080903040302010c020d0c08100b030105060418020d02060c030a0507150209090a09110607050c0909010e0d030e01020c0f030703110102040509040210030603050d02011a0a 88
    0x40c1141c1d000840000a901d9540351000e0501c9030000070032407403200084900815900d40d03c954032204903640d0b40035040d20740c000095264825480041d001079140035951000d0f190955400040300d05c81c11100da81241c2e240d0300207042c41c0500524076019555120481c840c0d040a000d155880382d4200e608210003000007101125030580000060701074141c8001410842d1902c40840b000c1000b1941200c0d266840c00d140140140d00c00c03e4216a02d254429900c2922040c83c0240d44042000502055045c1d07075901f13000c1c00412100f001036410404032182c800b4180c40700700051051700e000b00302402c04038004005000c80f1072009070601c0300d942c0c94845100912200410311422881c00c520780480d034004141a0140640a001c020001c10700560310002810307000040188900d503c0381d180d4443d4040c040006508031f0145109554001c2000f40c0007500601e0800000000e0310714908001607d00e4580d1a014500300d4841c00f4200507171341d9425204807402d661303a04014a00c03c1202e0103604203041107844 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 41488161 1250 41486911 41486941
    0x1050306090f0402010e060d0c14070c052b03090306140108030d02070323071205030606030a0f140f0114120309040b15070615050102010e0c0603060102011e09050114 73
    0x2c003420711820301c0490110781c80f846c0b0306d80c2c030314070001c00b803d4407800d80e43c014400502e4001820804a00908a0081d5200c401000c0c0c401541d0809039012003a86070030306120101003400000102d00d140054290b80244107000c1030356186000c1c0d594141e4107425071515400f150703030314030b003090121016000410503c1c1c000801c0368405807400c01301603280c211515060718540000d000e03a40740a112001010905084000504000f41c00362003800c1407501902d005031818401969251340000342000090b01c216060303005400c505c80100c40000383c081c50090900e006042c01c0e204c0c0980c001c80400100118544841c8644210f030044925184000d014107091f5942c2c031032740e9140c9008035190b81040d01e0b15643e01210340d0710340c1d2040d0303030151340ca11203072400130002c20b0741c0401642d0b42ca02c29040400c0300d52052089e0207800e000b500c01895491021810400c00d900010511811592101e00c0d224000076030707171070764041007110070404582e00c40a480d05509503101c5200c002d42d02d6080703204001c02c55100c1049 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 41489411 1250 41488161 41488171
    0xa11030c100c030b09010803071205030403020c010c030507120206070e040212040b04081306020a06050f0702060a0e070b0703030906050f04030c080a03060504092001020601360e07060206060105030609 88
    0x80d041207402c009070301070550000d0b1154088541400003c0b151740210043c20b44503c22411980458030300e031800e50302400181c0b07001d00140e20008124006501400848130b1990180c10064104a03195480005100032091858010381200f02130006a6801c88110003200d80e0840c2e056050141c5070f58030300405034004101a041c0d4a000d00420244495141214a810a04002f2050300c80d140e45e40a961403d0103038040303c0c1c80d8607003000113000c983e0050b02d290040b030036503001c1d01d820703110010040701600045503040802d000b4200c00240350000303031004040003442510042003c2101d1b0802a0440b05d00606040307019200300100030000341e03c030300303001919507100304000c0c0c445603403540407070041c645c6811085d006480c00500405002c0c2210748841c08502500c11000f0f0f40752080c1c012616110203100340890103403a0400c03401d2411010000701c2107000218024a00c0500024201081c0c401211084841c1c1c0c01000003401040e505000e03490380305800382400791071803c1110200c3c440f6200104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 41490661 1250 41489411 41489443
    0xe030d021c050903040e010504150302060a090503070f081005010b070311010e07031103011802060d0207031112071703070912060b09010803030105211902060d02030c0a11030c 77
    0x10807101d03086032032010586110104008110b54a003c0e0401a83c0341e03c14018058001c000000015a6140c50f005580c42843c03e01c01009015144d5070074008580c001a80314014406011f001141640b800c020250007011001c0000355241d142018103400c0c0300355242c8216891707040900603c114030910044420003941441c040d6030801e2541501ea005001c0900907641c18004d4400c004240b181c3c114105103031000c202c00800881c1d45c107440300c40e50186014002500f04400780010203030550346501500080380a401c203d50455001d04506042010810030303000300b800c0210300401488281040850616a4660f2051031410400800340445009100e00d42908408289000400100b5046150040b6000e0320014245d40c49240603600c0e90001d00a150084100042040c915004410400340c240704170000340c598003070110240e0011014004050380c12240403c6009140c80d07151000b50300c2805400d1a0f01d031a44c05c0d00034010700b01d006048529540f0b601c00e000d943c44090020401414403d6401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 41491911 1250 41490661 41490667
    0x3040510080612070f0501030c0e030c2b12030b090f0619120f0605090a0f1e02030a0303051b0a080a050a060504090b06040f061503050601050f041d0108010e030d02 72
    0x40b0000c0c80048260300542428020881e0000710f04031181d807801d05540090b00c00741305108600303004039601130641810384d9140c0d00071151144182001c00e011707480400b40d8404100245803008556000380313000f036400c94140d00e001810354140c40d4548107034400307928101d40784000c0781040401c250560360094015442030754a69000f410908008208100401469020556211450030111740748610420180e881c9800c1100141b03001d1008540600b003a0f603c4070008202010545031103080e1181d1802c607840030180c107140180903039020000c440d0018840d0341d012505e0310b031070009000325503200342d45040b249a040c001c0c80c110a4001c50311603031180e04404c0020340780c4d440c0d44101d0003519459101641061078142c00744180f00003110317090703c10341e801c0d541484414016010b08040b103046111b80b0004010780500c031030203240b19070000394000105142a60070418450801c607415400307a44000340300c0c814100c0100588411860440c0180340f0000200030400d100c040417501c910400c02c2d180700300c541c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 41493161 1250 41491911 41491921
    0xd081b010204030b151203090303040b0d0e0304260105010b07030807020a1704060e240d0b0a1202040e010b01230403051606080a0207050709020d09020d06020a110304051008 76
    0x2581642c0007035401c141405060305001121140c400744c00d45070180a8428100d0422a50307600004035507425030042c008502d0300d0302e1b200700c0800355000800c0d03240d481912068030b21100d15040000d40702401c01a90f181202d4485550102410182c001d40c0900b903074108001000594044801d4507205505802c1921b500e0341c030540300302d08000103500001c24205580e807008215401b002c0c05001070307802a48900140040c0c10741007108042200e03c03040c0c3e0300360aa61041d95041c00000103820755514040d000300c0c20010490001d00b8000c1160810626403040308411015407900307001c0d03c410320b00444000c1124401d1600020550316001c904c01081402c03403800c400c1e8480d40f01f02250011740d0040f050b02c41c10390501c0c56440b000035980c4121400101140c0101d0b01c80b146600c201ca00b0f05900000400b0910f2418503a040a5040080c0c0d890300940d803110a80003685070002c0c03070080d42c0d10603400181d4900c3c101001420b620411031400080c0d901c14003007804551100001440c05001c6070130504500d0b035075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 41494411 1250 41493161 41493163
    0x7090b0d0c080102090a0806010e0402060a0512090313120c0e180604050d0305010602060115122909070908060105040b120307050106050109060503190903050d021602040b0d081b 78
    0x10010000c241400c103990000c2d10392010750207041c45c8075044440502050380e4624440d80c9020078042d203940c5040820120b0010b19040c00104800c0c0881e00b0518102405201015106203044640c0b002941000441c040d00280c0c901000024244000780d411000071203849540d070411090040c0300d05868102c000c61492094070522225036014041261414601841d1141d19004154081c502003824500007140444c000b007000344c1030750000700c2c040c00c28042032002112030250ba81081002c040d43c1c1c00e00c4c80d4450007101c0d125610015011000b054174000f540500a000f00010b00c010302300480b13140b0500142d007003c107140e81120011580418004071074000140a0750800c18080440c3c070000030107604201d010742095048500036200c01608960711407003513440e44021920343d103444032202c60304012543c4030343c40340f180c941c020f10b8200c0c14400d040f844034089030700501c44800c15600f2101e0f004d045103407a00410102c0d54041d01d180074101d405990702c02c028080d40190b43c0c1640e00e001e43c5207182c454 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 41495661 1250 41494411 41494429
    0x10c03030e010914010b04090f08070c120308040506060102030a090506071707140c060702010905010c030c06020a120b0301090503030c0a17070302070501050609040b06010e030115140109060f0207090b 88
    0x40c01c00c0003001201c810f4985041c0c1e00401e00600103281d420315041d0b00381880c00b485003c4034581c0125024440c3c0c101692468499445011308a5402248040c08242c601500b400000032a1098031258070034141401c040c2d25000004014904651040200e136010582c0110380100b00c070010368000fa11450741c0d103070501d444016552140500c000100314041480702c02c0c95101d08484224041c1c441c10712420040c00568810100040e010460314441007145510039801068440d01074945000003000583e00c12080e80d00c0028403d0007d140c07c580030800303034030300d105500990200302c1c0200909050f9507603540c3c4901006154210b8510003041084444d070091740342400b0510b40381650050341c5442c0c04064003d41100034156282e40ca4200011035038140820428080c44d000b401841380ca90f038050044422094442880740c16540324404885120307140c1840c0e0b40a01004403e415412a00c180010311880c0f10340e1040081001e60480f1441e2660046090340c103590300e81c1c3d00411038007000f0303000c200c4040d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 41496911 1250 41495661 41495681
    0x2a06050f0c030a0c0201120504080304020603090a06050c180604080a081e0a020319030203100513020909040c030b0f04170f0418060303081b030c03150901030312060905090c010c0303 80
    0x40000543c04060303a911400c40151181701762248140c09590b4007007041182c2e01240c0040c82c5034030800110300586842c030040c582c0b00b8001c3c01128a0721405a94607021344100b525203a00894020520031408203440141d050120b07001e85805040c0342c41c0c6803816a5540c54903201810b000c2001038400c01c088059070b2180000030300c40b00110b036a011850b000940e25800114110b640805ca004255400d52090007221b0041c0c11076801d81c1001414401041080c10341c5000495000d81c4c00c0017000c0c90b5032038041c0228400d0340282d5a0b080d6083c41c5003000d000707024001b03103110364903902d1400f00400106d0142d200745104a0845034103441e48064403558240c1c0c4202c0c5c0008403c0c3c040342200041c0c01c103941c1c0120707040e0ba10958681c01e09441d003d1003508501403031079003066442024400a600e0045250145512909480e000b00e00700a0340030119403140c0083e0015800600c0c5035084100c81300140c001c03140108000d13601002181780001080ba290a036490440f410082807980c010300385846a0012080307c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 41498161 1250 41496911 41496913
    0x3190203070314030c0c22051f0e09060718060c020319060e1002040807090f06090e0d020105100302090103030c050a050f0a0c050d030212030a091703042a06050f0c 72
    0xa4088818041c4c0e41e0300040d604604610034180591014100410f00c40312189880400c1c0403201e80c000c1244000d840014a400707031440c2d464100a13001c12004c143c1d0802480741f0740848a69040c840221820600700808890a00c004580402e08810020442c08d080740c1343c2d49000a00441c551000a0800310450142e10101c40c54010340310034044180c0c00010a02c0303521040b42e1b45080705002d50801d0780564030425400b0340255000f041102c02c1078001080d103405a4400003112910783c00203104417118070305480d070941e0180034440b900325024401c150f00711541441081e0050701e1540004c0b06454140401010007030302600c14010040100842c40050750f0000c141c68810700d006100325074038020701d00e094480d0443d40c0400100350400009602d0b1b100d4050380074140007407003020300324602d0b031010b848009034a0707949404101051105c2005181e10b180b2441e81a50790429050004c84200e0307141000c51448014900030b4131126404504d02c2c2116068103141c1d84514040900e251103016812081300c00b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 41499411 1250 41498161 41498183
    0x30c031303020a080a080114010f050301090f0608071419080a0201030c050909150102070b070b010b030402030a1205070201090e07080403031104050a080705041b05030403030b0609180105031b031902030703 90
    0x1170b15401100e00da05a030522039030120400010f02c01141c041050399151004200104010712198090303800c1400460212240030403956541c82910b03180c01481c0d8130044420824440500d0546403e20401178641103110191100c58101015251514400000207044c16078813008502240c1c028420307221044402043e42116107020100075a400d0032003d40103005019400000c1100710340101079441d075680000c1380d284160700b4208900c00380e40c0054420f80c2d2610510090000061940b050140da000ca103070398035525035505100260202c1d2003900b24190f14440e060402010136400103c4560198241c6400300b140da00035034085803517100d076030003084d0032600c800d0002c11031480000d8441c0c221b031002d4404006001440b01554019007440c2e09005c002132040001c100440c1c4680c01c000c0015000608c5145000b901c0c07000980141c445e004d04c0b503004040a8010003042c6170a0098942d00589606c05192581c60000003030748401c045402c55001c03101512440056450070088200074507031140d0201070f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 41500661 1250 41499411 41499427
    0x120f06090203040c05040609230c09060304030504050901060306031101030b010e0a030b0117010603050604110301150806180c030a060908040801020f0d060519060f031e0917030c031303020a08 84
    0x2001c4c140728000c450046080c481d0010f481e4143c0d2180d00107070041402102038024000d0004148014082c0c0b0180c0c00340014070100001d517880c01d0007075005e035100b52141a50740b8503000a02c0b10782c00c0141d200383d041c9442c0c55010004100c03010060000e18000b440e00080700d480010042c3c545c2000550080d4100002c210040108510180d001381600d400000c100d00b084148403515081c0c070302ca4007004200ea004440403400103103130114040d803d810010b0004c24004c100303d0003d0080c404039401288942d02000030300c1759039030620404c03503898092400500040e001c0000400c0d03840460b42d0700240704a42d500b03420070a0001050595003d0301c6054004c3d5584c0f40d081c0d05481e500d410010608400d03614103980050703140f03040000981030508112102c00207610f070500a0380d0070142420954141510b4059419006071504860781d0502d40420001941c01b126040405101c54480c10340122481300f04103000350102910300341d0794400c1d0440799494024042d0702c0d0483c10890031240003000081d012034845 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 41501911 1250 41500661 41500673
    0x3080414120d030911190b0304060209090a06031101030c051b0102040b0a020a020a0806010503060403030b0402120c190305060904120c17030f0702150f1008150a0516120f0609020304 80
    0x307044030301900b40703410a4171010701000510071020f100302004034900d0500700901541c80000c3d541c041d000d2007005042a68003004610201412240c210050f43d86000034010044810b546400e5201c01b03181c1001070440d101d00c047c0540c071481c6e080704000640319058580801c001d4046402515101041d0358075170124400280d582c4142110480c411071140340c02042c0b20ba80002c14a040340e0008008104546a40c2ca060b0020003410003e203800c5a02001202e040000c10701845004003602a40305540740220744110076220300310300040c0205410700c414440c9544d501d8003010342207030300888168013130f820000c0306480d0007883c80d0b002480704c4010250718100b0100039020314401c4461401d81d84403540d50280c1241c41e091009000c03012000140081888001c0342c1510795841491000780b00e8030552a40c240030314015900c440c00b03004507800001c10540e0034090082c16001801051040504012040301031303c5041c8150342100b103165503e614850012084c1c000b42c00604050004642e45e092a0502c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 41503161 1250 41501911 41501921
    0x4151701020d0608030c0a080304020d0209070809010506040b03060c0c03040e010e07090e01050d030c05030f18100f0c0303050a0b060301080c1e010504180902060c0618030403080414120d03 83
    0x40b0003010f10707000c2c0008900f03a0100480344018108005084003110030380d255955904040c00a0707800c00384c400c50010040c0c45045070380e409401c260b110007105181c450340d11401d5500c0280a00c0c042c0d810918407854036103000543c1c9410a044010150300d4524400342c90346107010383d5002803e4144801c000242d19081e40022600858095503a05400341d25030504040c103003420310a00d40c0020032001100701083c4500d01c0344110714401da05603854034070011a070b40c41c290802822041d85e100d030320300259401d2031702c1080701c410403005041050b0045070804024040c000524000380c145a140e0000807070000591f4800d20b0b41010081201e600d9584038030255558603801050a400750049110354031074010607034220481e01405039512407400341040040c4441e5402c201040c050241ca0340c07101e00c01a03450002801d00000c054004101a103440f03005800c00301180e05001c030050304108824070100d0f1034030086a081d80c0506000c00302c503621110111704a82d044500707031903060003103441c01c800d920341c142c01c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 41504411 1250 41503161 41503177
    0x4020d05010c170601020d120506130c0306050117040308010509070c02030105040f03030c0905030319020a06020d09020a06110d05070311060c0c070b0f160f080309030a09120209060415170102 84
    0x1000c3d40b80e599a0016a84d82e24448014070101e4400d542441d5000000d80215500141c041c0a1480912102503050140c6160009210109032107101c00d10032560b101b030500070194968145004c01d82030645003e040c600041c098207003e4a0f26400080b07845000e9404c40c0f00a5501600810503850036051800390f02d2070f00c403000c50000741002c1c1c1030002c09115209030010745030300602441c9042c24601800c5040e00c2001108000d500848820f070000c40d10f284050121040300c0103001c503101d00c0700d01c10050082c08507002801031000020002c00c3c4080b0018203400003031a603040c615901e16a5040559168502c0045043c03588907880c1007000180d0040c0103411404010400c6074034480e00c0b209100624011500503002200c02800070f0036840004103920540b1034020180703000d072600a074890b4881c503801243e02c5006940b0004400e9862503000080f00c0c001c2c141d41a08400d0a03965074005100460f0280040f0300c56911205640403554114051900900000c00e100c1c1800c81c0400c0014041d422840c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 41505661 1250 41504411 41504447
    0x127170604050d05160b0a0902030c03120a0c02180a090b090a0209040209071403090703030206100b03160e03010c0210050612030a03020a05191101050117070e04020d05010c 76
    0x844451841000415a0040d0b50250191800c596940383c201c9658000c1c000c404066998000403001203a00f0060843c01141404804620000e090040c180f030440700800a40c040c4e44090046011100c1d00c200340c075203981d01482d16089120850000401e400c400f20b4448402d030108005003c00d920082d40144050f034414885060542e40b22742c8004d4403110380e18030103134100c440000060010700e414042d550744491203040c10360401041504038401074004955415a5074440441801130640410244d5030000d03810b41180c41040c101040894140005004a901d00301d52131030031034841e80aa540d1041b40748001d0000c2212004c2210002e41d50440e890300105202e00c3d00303011891a003050000507a10356a0034004520b0074480742d00440c0254401010602045014441942c03107002034000034030081c0540d41c81c0c149000c0229800f60031110180d200a040f80001080800c0380b01c00469640119200342d004812203a41ba80045400150343c03400090040d4a003e180140440e0000d91180000d84011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 41506911 1250 41505661 41505689
    0x60510170603121806070b01060c0309080c0d12030e1b18040812100b030103150c020c22020909010f0609060c02031b0102030904090503030a0b030304030c050f0127 72
    0x820305071141c52441c0c031140c00f00820468503018281e50400311351610805444035203072900a4440001d0040e082c1c0108000580e004012024940d04c46161000341c880680500204020f2000041c0c4054010100922440482d04400308280c0a503200318162500711055030703400d103090340401b40303290b800c13401c03c5d8402c0036000c02c0005144c1d082c181582c0701710380c84041240360040c2c240040c445650014010340304800e1214001c180c90880b035000d54021486003002c000c17044030b2030a00c6815034903401101000c660080d900308280d0368801c0b4a036110750340141c1da0b101c5020780118084c00a8030545a100b40c1140420000240b600b0118503120300301c6006039250035403940c44500859168580c544003941c1580580c514554481104030400303490385050040724071b010141c80101e01a140300c0c080c103540e590004010000798001c54041e89203a03244c114047c500d05401c44d0b4034000200464081c01d4003900c030301c1620100590160340100960109840c08100d03055803000c580d05094017030300030988010000b03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 41508161 1250 41506911 41506921
    0x20715030203010503030405010c0c030807050102071e030e130b040e0304030201141305040c030b030a030c0203061005090406110f0403050c04060b1804320f1303080a0f06051017 78
    0x81c401da0f030507a4402800745190918000044030a01c06080c2e050b00d00da09034100000005003448010400184100d0000d0385420060030f00700024001601d80040101110918400007540034841071082038044400d41c0300301d01103114040040003140b0482e508076181c1524080f00480020141044034401da0b5002481c0301000c445041c58002e441d607480d04080314000a000c1890150001040c224240c80c0000746454100c000a25000c0501c10650200e652003411405506003446070301d034045680c8843c01011484e220209180107002440940172075074411041c0803001d081412a400501151150394a031912030030041d442d10b000c489034030701c1a0f14041001424503500007d8502544050b031010303180c542d4120a100c003401c0d000d0f4003424900c580d000c46e080301c68a914100f012600000c611203200386405200005c1548000c0e25090400c2c2400d98040006940003400580c8440c54220109d0f0200450900301d02801c00354112950048030140c0700041c1070b611400b0442c1c010007081d60384d241610740d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 41509411 1250 41508161 41508167
    0xc0c07080f07080c0d060f0908041202180c0d15051011060603060c040302060705120310030201020618060402010f05041203030b0306070c080a0c0201090812030115030c0c11040e0607020715 83
    0x180805500442c4803145c4001040c2d050b0700154004142d64000316a8420319030325114035a020750825200b00b03c544108005504101031010803480e00302d01c03008524101107600e02158000d0b030661491850301c80b100c0c03510b15110403400000520b000391001500d000b1901d0003414400b850000c00d841071003100000380d0301e46030009200d406121182d11940c0b0b07041c02c60b000d100081d80450000d540c0d52042c0c210034000e84a400000f144a031582d1031030740d13000504500c0024207015028080e0135030f40d61902383c60f081090022508a402a9090800740011400110f0075506170046511544801c0d815403404000e06815410601c1c41035000c8040d2081a030b40c5010030b481340c1000d81c801400c44041400f408441500580341545080e005040030028980e031401c40750300e00312030301291040603030002c001005050f0900040c43b001c0582800c0601507440c08140040003500c200c0c201a18200b100e100c42c01d0192200d501c038150300706008055510030300c0c00c1003001c1d603280c0e039174860150300444400340103c84500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 41510661 1250 41509411 41509423
    0x702150f070906032a03020c0c030c090c070320070302010314100303030507020106030f050d0f05071e020f0d0311070603110d090c080a030201061409010315050c0c07080f0708 77
    0x595a110169030034280f4004600070507001d544442d0720329071081300041e4080c11301440c07811070100da03602595400110717040f9420201d0303481c9002d00a030700c54200d000c00c540d5059422548160f8401d8030640b00d814038202103403d01d41401c02526266060600d100342d180000c0740b080f013502c1c001c2e2000d21000e40d68001c5c00040701d800311080d4400700005081400001e00caa003001390407a880e0b02c0003040203603d0b40c446000d90b450381e071011900380c6e00c081c083d0051203411100c603e4446565003019800c0c07400030348945605a175088035203d5a054000d4200d404c664460100e041d03c2c07078014000490180c0a03140213000c220000c002c07021144100c100019040d8801e0040c148007000d2614036905048214074490043d0120500c100c1d4404030480e40862000b00030070121120328000e0b400855002e1501506540034200c142c500c038000d840c0440140042032044c0f20302e40c1c4840088100040303e03a56501441c1c0203015582c0c0c07111041c064000001002a0005644204000b400301914903142d40e41c481c05640700 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 41511911 1250 41510661 41510671
    0x11103070203030a050603010e0706050d0e0c0d030804020a03060905010504020301051b071e051614063c040b12060901050916020a150203180606060301120f05060702150f 75
    0x68000c00000b130104a2941001e50000f2010303002241949401c008a0b0070000c0d41c0c1c0001d80014800b04210744010182c0c0038850b11103100601500c9850184004a25800c9600741c0140510640c00701180441d101e03418190000c640203001007010750003a2412902900d81603905a101e5801e00707002c02c103000c600b8480f0680507111440e0851400c0805d68a1010800c1695014003c2601c01450780300450024003200901280b140b0740025030504150741c1004520142d04e0300da004803024820b2004101506918484280c600a680d0400b001030b01c844500c080e006048452a203040850001850080303503014101d0900280b13030750211980e0f0380c0188900040c0074803480b0360001010001c03801002c0940f50750390390305141d4415640412820386680f144d11548144d10b1400c59030000070403003920000307842c07110b00c900c941001c0c0407a824400001102d500060140c1c50007240094000020444424001400c5581c4081510000d15260380060b403182d807001410072141c001e20000079107420311000c0f814450 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 41513161 1250 41511911 41511913
    0x60c08061008180309060a02010209031501050612060d14060105010e0d11150d09030903031101020a09180f11070b0c0a020d080c040e10180c0c020d0512070b090111030702 75
    0x20f81d00c4140d001c2c40e19002c0396103000240002c01080110341c558400801c981c1c0c2c8242c001503558a8040e0916203031100c517480b42c1306100d07803240045c482680c6a10403100900034010406410b81c5883c4009180442551401008040341b03a46403070400c50302007107460480348262141100315103001d084c410000401e0700c004011064000c800c440a00e0008410a003111000c1d1210382000555503a56003105d409a50903008246400701c10003c01da4040b040109004469000f50b003052182c55015004039481e00514100000c0c00306e0061070500aa1700410400c4407151052002441419461050b50f100030780035107605c84d085000810503e4000d00b207031007040659004141d03040e01403204844030760000d0100c0020701010840001e00213816404540504408550304501ca460204001da0203c400300d4289030090804c02182035140d042032000540c1038041e01d80c0030b03060340240350090414601c8a0340400c08a400b281c01d809002d103070240148214010300c020003034080303022541c0b07a0a000486d400001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 41514411 1250 41513161 41513177
    0x30c020c010c021302070b0901060905070c030c0609140318030f0a0b0f06041b030e06071e1803210f0215010302041802060a0c06051003030f0c14010504060c080610 72
    0x504250002640d613007441c0400500342070042d5200d1002c01001d41d003084161b0b442d44000d2140f5841803058903040945814065400c1e8043d5038090b04060116030094801a41d4a0014091280d10004a0803000d1803400b80c1ea03441e12a287e6010203105e42046080c028402c000350300000d0a0002070800c0300ca5007001130034110390380d29100602001c00042c030964109071030700d40c92010016908074814805086490101e031400340d284504c3d141c000c0050a56041050040042519a00e006083e0b206030440d45080b05c3e0030107803c41041240e440c583d10042000a06100801c10100418003030a000341b629602c111100c14a010103c1c0e5a200c1c01039014521502c00c070040006261503804079180b5580750100d06401001d540004150b0b030031a41d0714201285200300340c50100710540c410036500c0356071031030443c00c10350031900c0080c60008005802000c7c0500050841c0510241d40ca400d600f1952070002407080f45070601d00903014056401145020543c00c80100303106142030540c0305442e00080e070722121 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 41515661 1250 41514411 41514413
    0x110c031516030b041406030c15090402070609050304032103110301050f1c060f060503010e06040b0c120709060f11061b040302030303040c14060304050c01230d0c030c020c010c 77
    0x7140c0d012620300c680505903608001d032442c2d25280522601ca0003031460401462074110145800c281000710f6240c4034140c03800305d404141c1c00510665419041c141d400584550300c80c40c05400500407035901625038400801c00100f040940903d559040d200306000541c041214501a001d076000030a0b1040086c6003070005100f40e050040c0c0006006400a14031018180b4100c075503891041841410307a0b405480707102402040c051805001c0050105030020000d20041035034098a9110142c0000c2c04030a82401050030b2507808402d940d40440c0d0b10304560b009090622024003400074612650340030500b90068094060f000d4600503007840265400b8243c3d036a6074064a111004200c402120302520030300000c40075803401c1010b1446035104180041d5100e0404c407140d0b0155034031518403481844108104400190b0100d4006d9101e002070034002884043d5a0440d000786c6450030f9038100520012442c0044856582c03c12180b024440d20100003001d401d140072a02c0c0d0750780002c070a0104102c000040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 41516911 1250 41515661 41515681
    0x409050402010905060c010501061808061302010c14010b03010f0606080601080c0408011104141f05090d020d0303050601030e072121050a1103090a0302061315110c0315 74
    0xe501510515101d800161075000040c29a0030001c030501082c1e64440040c0141d0b604107407a02c18074912110f00700e158514080c41e46030365000050140300c10341e0100c400241164050301600200540c01800654884030304e607a414000c00000c48294482d40c00c01c80f0301d003802c0d0000d2203540191402541c503041203980310070055403200760280c50303070341c882c44200400170741c401c002e00c0b0321640d040001c40525600c03440c009580419160400c0c685105203031092440c503802c428400030305580314481c00c041d0740b15000b11002601c9002c001d00060b4101c0d04814101c010181d1640c46103100701c0c0b00362401c0104286401c00641c0d0b035442c6000e00420504a00b104068908a0024400c4064402c01c00e00019072900c00078000e1284100c2d100c1e4005c44d0022924080d019000360500f20710342c0c0007000941c2807290000000d140e0a1813407001030300521000559034125104490958060700602c240301c6440c002e400402442010000c00310020b034062044404040c0c5004200641c03c50444801c0001e07607102c0000d29 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 41518161 1250 41516911 41516921
    0x311040e1602160f0e1006050417010e071503051e0a0e0102041a0c0d02030f0702010e0d02040c050408070512060f06120a0302010603030f020c010210020c0106030f06050406110309030409 82
    0x7403000d620074141d0744250501040d940c600034200a04000182501d80074100b814840b0180c507807107280186140500100794061b05403000c03101600c051442c80e0f00540f40d0640145441c0c040c107502401440c6011030300c0405d18480064070061940c00b0021a5589141041070019455140c14500d101ca40412480300b00c0e81c0102c02c0e00f0342058001442c00760750310540c202130407071141c050134a00c00124900d0000b050500600240d40c1441c001b55103807508580c51310156106102009040c401030414407034460700d0748010b14803c1540640704000c40100c405e4040c0c020703009071141d0032262088100119240c14403448001d0b90603e8203008128645546800c0c03000d003040141b54a800c40224450f0200c0c2c0b08007002040c1d0454000c1d000040d03040e003942002880c02120700d5148096501c2001c400d21a030742d00007408a14106903c40c0143c031041200c42a40c0900300343d5001034003140f805402817045c010154415030140e8850001041170700c00621003280303070380411101e002082e00180401c00490305c540d004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 41519411 1250 41518161 41518201
    0x60103121704050a03080f010303020a081c0c030b0a050d03020a080c0a050307060e010c08010302031c0e03010c032304150903030204050402070b06041a03030a120209030706020d0311040e 82
    0x115411508400d803100c44407100450341030392160711402000d01415040790f501e54200e8142c2403190400d604513200030b5900d13014a2002403e9100c0025941d05104680720450500040c0400c00d2025102d400801000352200000c82882501c2c00304000640385400c0002c04e440703583c1034020303020209664403580310607000500d020b80729000340e00007100090820b000070503400b44503040c000742c1098a50071150031104030440d0203042c00b0301c8030010304c0036a8000540340e02440d980900e8070808076440c03a084038064460002c0c1a01907013001d0503911010f800d038004d00d2040040f5403022003088088189403182600c182d03006080500820041070034490345400500b042402814090300d4240c3c1d90011404a904c02c03072040d40c01d00b03000c2d002d12030546040d000300c6440134034100040801038080c500080e100d1041010340400e0201039500c0a100611903015510104002002d4840c12070b80d4010107525010a42014400a032a0512580c4e40001c0d0806640c00d950184954600c1035851a00747d203008007001007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 41520661 1250 41519411 41519417
    0x5091e0a0605011e080601030305040b03040302070e07050904111306050d11030711160605030a0b01090f03030305040c08060c04050103021c060b0a0e120a0605060d0b040302030a08010b0c06010312 86
    0x900403010480c10b019990003004c0144840303000400c8039041c0d8000d411a50004800c0350860303001080440d51000560301a500501403032641c83d00c80b454240c0c64103025038099501c840b41d59080041d081d030040302a1170040c105035400d00c07102d05140d80080f403500c2180007409003424026406d010903807045010384249248070310000b80c4d00003205011120760700212042c0000030340409102649003420b12140c901111052245600c41c0d08020000e8500d000040c54070525039500c22960300203070301c03a68400c4002c10070f264103071101c0c2e5120b0500901420741151b0a440b4082e0008000506500018800740b240034005d0001e420182400b0044029521018055480c3d00c801c441c101f400072221700ca02c1c0000d0650401d502d0b0340b0000745170b019028003000350415220346c1c01d010320b68095400100e150f00d195a407001300000d1079602cac0300004040e00c24910f0050100e40c0007000300020550004010003005056484900860703a84010303c6059118800301000690840d01c010400990038162111000c482d9007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 41521911 1250 41520661 41520673
    0x203060c0c0703140307060c030507080403120b060d021207090305030406051821010501080102040f030b090a17130e010b19020106080d020102090a0b03011a0f09131d0105091e 77
    0x130300c440b0495000075000a40c1a0400950711041003241d02c82e80f846c000440c1410b0100303250103000039103030800080026043c08204500c65641c1d80a513800414007860080045458181d906040f50080d0095060490810b400c1000b18240d075004101c01011030754400d008500c3c0c0360400c0000c0760070381c004101412842c00c4c2035a5242c502d41d2010845040d2150701c0d01000c00e03424409003220b09544060703010101c240d104000500003060301300102010349801c03031080c034070300d0311a0030101e40760080c04007000e00206607040a50080c0140b0300010710550444840300382c00c0766140c0b03203100314849082c800c0d940b001c40100240c022083c3ea80c01d8881d810645ca00000800b583c0e600841403c21400009000c0143d600003240c458624040e02c0b6040030307080f1110050305660410b410a4503200121481d8000340b000803c4103505406440b08031804014094220100684910594000340c08524010015003082d0030840a0781030741445214131034404031000304000c04881d07800b504070102d2103500c641d02d40201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 41523161 1250 41521911 41521913
    0x2030714040906140708070912080f160c17060105010c0618080409021314030a03051c0f051e060108070c02010e030706110f03090904080d0b090f19090203060c0c0703 73
    0xa0300c80c0200243c03021180c1413281c034100400401c0020010411414002e02ca1000d0141c00301d40d05403111415480449030b0707a22050b00503ca0054000e818110041c00044030340c2008121581500303d0032111103080e00c010356420200c659860303c009008660000301d1441040c804500e0301d4021040201c85584a440f2400107526106401e81c0f00d03401004803280c001404082e19103100c0c02ca003004000020700500c06070080c134006130301e03191401005010858041802104001044d030191311070340020908020100c240e50a62020b000c04171003040e03010310305a01400c5541c1c0e08003840c0380300f48016520881d0503a030701d0b0f505a400b860b1490090781000440f918078640d43d102008002c0c0981a9030b1070f505850700d03245200c503150070f6004d5100690368000303204250543d250011000c3d00b065104414a8132000c41c410400020304a41440a81c0500003006010900700c1e41c0300940d000340300e0010515800d680b629100700c1961041700d402901603100e1030010301e600c1c250901501c0604080c000b541c03502940c0e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 41524411 1250 41523161 41523173
    0xf0319021605061501020606030d0f0203040b04060306090c021906020c0709050a02030a050601051201030803060d0f0c051512060607050a02120d08070c080a03090819090e06060304020307140409 85
    0x910307044445030310241c28003035202c64400e07144c18400400d100078142da29180001c02c0d203c02e181100c0b142440b100d0354091399114000c0c07041c1c42c0035140c086445901c4a41c0d480b0b0042c0500800d02c82e0340345040c42e00000f0606a4408950044a80058500c1d80b44041a6030750f03080082d03208442c8a15580508000821049518010f0354080c13403164002586a0605041d80400c80c0c5c2c028240300c0c1031182c20002011a008403401003411a60070000141e100d58031240804e00700120410010500c1d01022002c608210351076403d1019501c0603600000c00e400c82c41c1d132528592081c0e403a0616001c84820000b80e1500e0160010203d40d8812000c6e51240e40a5a011405098803900000543e41103458040e00d815441005c0d940c0c81f0000d0f00d401c0d508c108507512490f40324401e0886c1481010b40b941110001d003e20001100d9580c42c07080340c000c1410380c07107540082c9801034078054200761006c0d91022881030b280c0001540c0c0110307001005804040e240180e42031480d003d00d03020503086500c1394410404650 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 41525661 1250 41524411 41524447
    0x40f0602130e06030c040b090f100b041205010c020106141323070e0607030c030c0512031801050108010b030606090711151617060d020a0314010b03120f031902 70
    0x10902c2480106030a00c402010308029010103401c0c0228070b0464522010742c1c3d0081d040c0e0304142616000d10346e40e1103c240c81d518205258100554281c00014002000c0c4403c501100e4414004c100810038103201c000200e007a2000391146e101940c8464012440d40d144c40c48c2d03002c002518070440027542040b40800ca10b004014020001d0540e200741c810000c071207800c080c00240c0b01c2c00841c5d100b4508a442d07600940442c103400c00280800c01c01051090800808100840000b61500800c0d600ea00e881e15004e055460450300741d44d030f02c2d400d1000029490005029264a03014024090503803607907144c090008c0301000404600401c1040522003442d004240004414903070404045100761400c5028803003a81403803a021000c0117074142003122401000014940c00c0300c01151844002c07165800000c03103441d0300c1d0300b02038410440b5849d0082600350541c041c600205065094510381d05041c1484130550003a000c4d064101d03801080003c100034201c00500c40c03100c6c3c64581c0181401813008091140d21 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 41526911 1250 41525661 41525669
    0x6090d180801090f0203060a092d02040e0d02070f030b0a0b031606030c0806010c0510020d0902060313021503010303050307030c1116090e0a0c14031c08040c06030c08040f060213 78
    0x1c0c1300d00741c0c0b842903007401c2c05141d074461400241032001c1803040d0350301180d00c0c41c4000007220036100359130310340507daa00f50800c02400e90000c00c02c3c08043c00c041c41454845c07500060a6003d44a4004e0011b6100f11240703031182280e8101403000c44a603652840782c0060013000118035454001c07844040380c421044030b4480040c1c0100d0381c00060000040e60003a140f040041d101a040c0220317985c2003000a400007400c8203000d00b0070900562550520002c110103814242802540303d540802001404d03481c0c42002c907929402140c07000d4410028070742e10050b41c8028040500003a5040001405003802038000710b285070314902d80a8503910380069050b00306410202000c501500c40b900030020900c1038083c50f000324603010301800c82c100703942d5101508182c4911403003d4400f00088051201ea509105d003203800b0030b5140b040c41c110243c14100411800c01204e00b100c4005500101141e681d00c644aa00c1905010380c4030340d5100d03111900c440c80d000c14a070100b101d1749502040a440c0728580c50340030300c000b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 41528161 1250 41526911 41526923
    0x14070510091a0405060717160f0506060105071203050603030d020319150b180a080109080408010c0504050f0120011503021c0305120a06030c0e06090906090d18080109 73
    0xa9030602c1c442d8640c00d07206021100000da8148070501c03041d642c1c80121103031554416a1942444004810403650b0700440142c203a958000c10841c80502c50440d60f46d41050348180181c4607280e440400540e02c40c00703500405480306040001e0440b0507402a44580c0e00028002c2c101d90410110100c00c00c02d80e03100b01c900300f00074981c1c0c1c0050004000c00f4010441c503401032280c042d0ba00790501c850000c040c01240c0da0a14500c4d5419080081c0307803900311190024102e0500240420304250821204039449442072011542c86e15042070f0713172644294180c1d000d5640c0180042120301c1248011a8005118162854112080420784010358001d00c5105030400c0191506581e10345103004100c00501b99150711031561501c01000000694000708448054015440d5010f4985444d0307400402400d03c0e801c0100714091581e00854039841115400340f0428003105e041c078035642d58800c00d645035241640c0c0b40c00168400038580003c54090707240240683e903c200300703501d52655540e640342940c0d42440240c0703079 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 41529411 1250 41528161 41528177
    0x10e040c0e090a060216030f140d11130305070f0608010e0a0911090709060e030f1c0207030602040803040f05040b010c030e030c0910030507080f0c100908030d0605040506030f0a14070510 82
    0x20590070a001c040740080c18140389a00380300e101c880c1009e0b4494804101d0143d95100c030551404031040741591000303440c1500c99040581c4030314045507202c4490191000080c1c03034200001e810752098403207d0603902c24a40b00c1d4441c0d1600c101c203401401410200729182d074043c0c0404200d07901c80c040c02510811440e5200b01c01241f51440142211003520340d014083d40009200d07403c080c400041600c0040c81c010700c1c40540880c403000490420303060b6040144a01d000080c00101c48100001a10503104a492401030144d0398804210071940c25800140c08600d00c0c0c0030203c00310b400740c401a03164040160946010402040c00560001022240c102c0b08254840c0d0500034440100312140c043e003400c0000b0002020014481c035a0b540c0b840c05118807404030300015100301842070b00c0c01002414203104072925101940103800160a090140038065440d040025034075240018480d03500742c0a5030f001e0b0007280c041e910380e1011424800403030052403144001c00245501c0300d5110140064582d601c1c404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 41530661 1250 41529411 41529413
    0x40201270303031d030403020f01170a0506011d030a02090402130609050a0e0c030a0b0702010609060b0a020c0a05010e0405091c0503090114160305040c090204090c0206010e040c0e090a060216 84
    0x1311988407015420401c07502c040e0342d064a0b4008101c0d020b484e01100c1c914005807076100100c81e400c3c1e01002890012100780140032042c0f00302d40220340128401d0301c80ba030a401c10188001c25070710115070150f606500500944000d4140034500640103400a08040f08400440c034896043c0c445940c8502c1d401d568400c00c0000580482c411000300300800300141101c52200e60010381d54070903001c03000c0d10780741429001c1401c3d28000d51196004060200060041c181e540c008148103800403800040507016400b04400b046c5045150300040d5038050719500061442c40c03003400003e08008066240620031542c5541d08a4040e003038030707650003486660b8a942ca191200040e0700752810404007511388058042400b80c0c5074041d12543c2c140608038a0f0016450703030382d8200700e5180070040e0f200e20b1026100150100da000d00580180c070500c03c0940850b4544c2e6650200780c41d00550850b800341207842d041341c0c24800340760120384060b0031035455021590384100640f03a4000b01ea21158100413001d0500d94110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 41531911 1250 41530661 41530667
    0x5040216050c0f0a0302010503090c0d140c12070603090f02130917030702070603020a0318080405120318060717040b0d06170d0f0201180b0403090e01030317040201270303 75
    0x1400100b041d28601e06901032000410204255408001d050100100000d902448204101010218001c020301102462070030203d9001d03c2d510044483c80c002c00c1c1c4031103110304002c0703541000112081e008106d002d01d084401c0f4010310489104541c02c140c00c1c2c80940160342c64148801d048c6a809500054030040c0f0320b4410110800c9984c2c01600010500401c00795a801107200400c40340075090240c1c3e503400080d42100200038085009070040c140625101c280040f201c0a0710a84406030344003107040030301001c410341d2802002c8100c5a1243c2c0104551030505245d4042d24132503220341c041d505030000c240300c452907030317001500082d1111a002c10520307010200382c040c00000341840c1e03600296030300c88005611b8940300d00c10220b1080c420381807010f521561003540311090205090924030780b0f6201d545090f075995041a1000d0740040d44200000c102e40710020150340c100c0768980c903107c1860321000c0700700e61300d180010301c140c1c14840e101c0c85000c619401c080c09402c00250541f484100e05007146006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 41533161 1250 41531911 41531923
    0x3003010b0a113405060d0b0103050702072304020f040b09030c01030515091f03080d051605030f100b160605010608011a09030a06020c060103140d090306150504021605 73
    0x581c20070b50086605504a500342d202c00d110002082e90400083c0003510504050510b140c0d2250ba001840001c1c1240203618652003284c1e5820241c2e030904c070503102c201c800c03a5078427420302030b0b002c10480c6026080e42c0281460f400750100007014102505000f14144140c1c043d400070707070025911210004260304c0615003807006480d00304090900700900e0510044c01420901700700c4030f040c021444d02c0c01041c64810960444901c4070b00480011459a84070320300340e519070300080300fa04d6043e03041c0301c003180c60a242c070802142040616070316582150b03100c030603080000034090043e00142c0d15003800030404508a00007040202a0000080440c000c03902e0490115201640306804021413074005000c03d25005070113a0360001c614030380315140c0d450307100024100294485c00030043d07440040ca04140e4480403030114101c80c05480400c16000404580a49a5a5403442c9000040ea403540038030002c1c00c03a500c90341b50100304400d400c9440742c035900858100c1e441400c1c40d501d10403140c519a01000b03020805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 41534411 1250 41533161 41533187
    0xc030908010516181502070e0a1a010807090302090c0415020d05030a0f0f060915080a080a050309010e0703050609070609030503040504020717040b070606090207053003010b0a 77
    0xc20207460601c1000c01d840070941000c40802c0022a602d450b00f02d80f88240300082d01078042080e00c1e00a504c50040d540706002d08c120110740d103a04c000101850020b1281d00b140c40d01d00101c03c145150494011201003d000304810103001c0840d02c040b0258440907a460b1044013860701c03180d40e072404d19402c0c64030039100403405400c5610002065185c558058292030304003151401c0400d03209107178104000a480c4491800c1c2c0301c0c1c1d2811100052040480d003002c080b030441d002950000719102d02101c4c0d2900c04c0d40310090301000003001009041c902c02d200a580c0005804000030b44014041c04d150704059550780182c4441d8400c8040c440384040c18000b00d0000e241398240320b14503900e90390318035449014510400340f0840d80071440e4000e200300741d138522543c1802e001c1c1c3d0540d915142c01c04034489070050700003600c2c0c907460302801250381d80461085a032042d07006802000a07280c14000d8407409000380440085202111107c0c510b5807010f00c0c003660103040d003902c10380d48840e00f400c0010450350720010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 41535661 1250 41534411 41534413
    0xb030303070e01230d060306110f090108060d0f050c090a060f0306050a021605010c02150402090f040201020f030a110607020309060409020a0e0d08030702010605060c070603020702040f0204060c030908 88
    0x180030000740c210b070080e000e625003800c2c040140e520584104001e1000c01d0890f1241d1100002d42a2840034940e01140030740e4441c00c003c00c80d10b4002d4000103154050720040511070071040001c200c0c2580182c10040c0d2104004100c8150304000d580d68014828102104484a902501c02140d8501d050f0020035032000141c10100186840d1a061200074040c40c80060811503070b8002103580c00e03810b0f0301207825400001403004482c0165282003402029400310910050013440b840a800042c0e01e00d03d180281d030000c041448030380718888960740302c0c000500128154070843c0d100300d6892505102809041c1580d407a112094160841c40c1414010002c261504540041003c20300556811094500380c80c1241d200503107503142c03204140e624280c0340840d1070344415110541d00420014000940c03203801a40e0092080a51f01c4051081c28000c0c01c41d03140058020f030105110795442035000e002c0c43c5000034404101c903804002644100c3e4082e411100000303030001d02c1113042c56004104003005090b600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 41536911 1250 41535661 41535667
    0x5090606040303030216020411210106140a030b0a140307092007060b061b010b090105011e0207050a0f060f020309060a0309030210050906160903080409020702130c0c03030b0303 78
    0x1400180952160b404010b042c9640802e2046050050f0740e000c02d8007944c050020011030243c003882c00702075001104090f14200f06202503140f800b0104d00120b0488107145c03030b451000600380c24008000e0300200d0401e01010742e2603000c1c1c180c95880d9422000181811202c0035800c07800c2d0014182002c09541040c0501400c110070300300340560803c0307110700701c0e2880094551110014034285000e0880d030403c59a00a101090701c403580e0304098024000221900002c0003080f070700c0307020300240754803d200c0d1a000c01c1311800617030b0201d400000000b025a03c2032041c1c0740c2c1d10b905c420000300743c4040d5800007240031408035014820380750070070340d51001e000c6c0d640002c500305000c4000048652140c280f080080603101c1c1510b0b0105402005074540c110103000d008e001d5850700e076010b950b45e240221040c0040505a80c960301d030160040d28110292038002a20b02c0c50181856082c1300a58003944040360070400d0301c121416074040e42c0c8210010203055a0351030640450901300241071b1400c1c2c2d106184603800030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 41538161 1250 41536911 41536921
    0x6020d021504060905160e0f0a140601030c020c0d082101030f0f020105040504050a090308070f12050c0412030207080105060a05060307080a0e0d081e090709090f0210180509 76
    0x2071102a80a64800000309030700c0030724901103050825110100c00c0a00e10f0310800303d0a1442e0083c0c0622800742500310140c507582d10fa120100341c8404401c48050003108101150340783d40320350042c840582041c01182d550880220124060122050b0183c400d410007040024038080601c03030441001c102010110000d50640d01d039140c0001c40e10400a043d204910100300840e4082c0701030742e0061400800400180c0380029404014000c609811000120203c00240185004088a00c1e50030410755408114121614101c00100030203070041d640500244400640415203114451050303220394040c140c4a880c00040c107096a10141c6014030840c03038500c2c280700503111841903a5005d0b10750b152100c40c40d01d441040b440103101d22400f24900340034080442c0c18454220107500d0052100020040d40c0c401c446481c07800544091701c074111150401001042201c5891f044459550701440c0403104c41e00081d07000458100d25070340582c1c00300700c41c3c1640420034146401e040004041c15100d0f001d1514203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 41539411 1250 41538161 41538193
    0x302030603030d09020117070c0b090708030d0b030a170c190f02060304020103091b17010b013c030b120114070513080d2f070e040204020d0f0606020d02 67
    0x9900241c0d000e9070341c030f12011065a118a88081c010020300483d41f0960801030402444184004003c0c0d50b11206400400e9204000040e4030080f2441c07030020b9800d20354059900d801800050342c01c9035061041c203090101140c01c54082c100721200d42c901d550340e602c2d070611850f82000d0462009544000e0700b410dd80700412400120301c0e00c3d803941114110b40d079964510041e0700401407407038050484c40c982100c2d04480d601c3c06000b9030640b0688140103c0716000c014109080e14500c10302c01c2d00007088145041100544e1203506680ba40c0da66180c0484440308542d000901040e0b007021a000a45600f04200c0c1ba0500c01c03407a2454604540084c01081c038140c00309604580040c1c5010100800020740d11424130100c10303410090328210059a441c2d10300c00c1c2008040d40d001946103c44500c0301003002a00300010301e17990b41d0410300b21018086071898100700c18241c08008000b642c1054080010001201c40c52007400c0c080c46810780300091903410b000d0000d1038050f041d0402000d640c0407054000b080d081c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 41540661 1250 41539411 41539417
    0x18030b06010c080d0f060503010b061303020f0102030f0a021507020604050d1d03010f05060405100f03260304060509070501050708030a05040c0503150103020f04020f09010f09120b16030203060303 86
    0x20a081400054141d8640184648100c1072013130356551030800411400c50f26604040c0880e4001c82c020700c00c2040c903a080140034440c01920100400c44c103c01000181441d1203001c151410500541e81030106035424041d86a10240801006070080380051a80094075002140c100e081803006143c140b6069480994801c5800f1021050014104100c0c6113000d40107180d030006034000d0000e108080800040401801003514010710407801c00000884005030070744020100c51250103515841c61954640c0c040d0a4034582680340d000b640040c801c0c85810700100114040d5101c1c180004d81c1e46030840d110341c01c1c040e140c0c000e40e041100170800c0c08040f034440740641b41c000c4106000010b05458501d0300218204050748069014040c07000790345060b24402040354100d90003079652815451201007040120320410003445001e1000f8032418029501c103980d900240324441c10708e59a070a440e0b07130b2201c0c4506210001100c3c2e4201c810304002c0900300170244111040103606081d4214200600003030317101c2c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 41541911 1250 41540661 41540671
    0x1060f0e0111010b0a0b0d0528020a0e0604030807020915010504050108090f010615032301030f030c0204050a0204050112060602071811030703060501020d090b040603021303050102030a050718030b 86
    0x45070034042d003070300030030b0a501029074841c000304002e50080d0b035894141e01c9a044040c0d1401c01c10b240900107407192549402040610001481070103031420450800b00c0250850a044801c000810105006c0d036100c060080c0302950040e01c0d00c03500c810607032040201791000104001c0c907211414407101c0e40ca0b6080025181075940c24240030145684014800740380811280030440e02c2d600744000092030009503081c03400c40c4e030025502805901c42502c072102201ca9108244030012012500410100d039441d03486050740351003854158051541a00001d080e075030255080703070034603500140c00c201e40d6800001c014103030341c401281801f13003504d049006900c40701c2c94481d1064400d103014202118104507406100005170b00010640c03603007004540200241107a0190b51301510032501d100300c040c0e020b41036030030845068400707281c5070a0a210701140039401c81c502d6042e030650300a4002c40010003e0015501c211814000002c203407400d2940203202c51a005421f5009140c1003c091000c150078810301c40d842 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 41543161 1250 41541911 41541917
    0x2011109041e0f15060806010f050d020904060b0a031404020607030e0111150105010e0d0c0b0906090307030609030e0907020601091805060412020706050c0a120306030206030c07050601060f0e01 85
    0xd08080006620a03142e22110345655070314018007a0040c0c41182c0c09090003803181202038200756243c01040c0c811000540e075050114181c0d8804100152282e0000d101e040c101801c00750402c07032408041802d441d86038100240d040004210301e0909980743c0705508900356010144015420240c0206203a44551807014040241c0001000d510f64010344c54008a45a0b0100300c444201a0309145411001c003802041e002460f40304501d00240b51114601e820a85c0200310b02640c0352400281040d55400000415002041445441415941800054025070207410701148070b000502e030040c1004940340d440303486202c2003801d0080c0c00c1e07400500745041da44101e200007a414010307103003050004c902c18401401031085d00200010045607880002110082c2d0302180d6556440e144280c13000e009060010520f40d0000c100c03400850800001d8150100c01030400086598480d004500103600c00c58811510090014100b0100401005441e005203403900c1e20011551080701c00421442c5840d80d11810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 41544411 1250 41543161 41543171
    0x90305040b0d090b01030501050415050402031b010908030d050105040b01050412060c0306030c171204080d050904060b0a11070602070f050f040e06070f02011a03030306010503090f060103030e0f010201110904 91
    0x41c00900c1c0d2142d12501d030040c4c0188469a9a840c0c890301901c0115401c03211324a02d10340c03008201155004e511700959005014002d40c0c5101c40e200032140c9982042d171410010000f20019043c42c0910041c00102c880002c081030350b6041c48144410390302c0f8a803100341000340c10001048605000f202c000c034920b510002c0402c40700400c0c001140509105d420107020641c24032400520600c5d400070f06400300b1804400c0c0d410025140303200789400e005521404409802511601c00b040703108800401c0244001000050055183c103800303c100c1d04200d0181700481c00010881102d004200040c00c010030f060f00c01030155901b0300f2720110810082c0d10409006001d580c5252003145c0e0b841d008200b00c9100c1d1001c4600d1843e008400a10407854003201c40059440c0004140303002c02103a0089020352030242c003c42c915150303280112419480101040c0540c02544c000c0b00050700c0900c9140d00a5000759241000100c00100300325510818001c624103680c03420b01141e100c00040701c20b031001280202ca000070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 41545661 1250 41544411 41544427
    0x9081212071101060b0304051b030c061c0504030f08090d0e040504080c060403080106031a0a0611160602030304140f0604030e010e0307090f0b03070b030c031314010e10090305040b 79
    0xc0301c660b4008405055401c140b0007003800c90321032014500c1540034608866204c2c441611030125100c0c00003130960103400c4003840840504020005244003018903075480442ea4000c0c0380c0c1c10031540d080d603040b400505000d120b5240660702601013074003d0b101c4005021034010100029154901340f21489000b140c4590014040c070000384103680c2007103c90415505585441e00d4000c1c40e080b001d0280c107010a00c1e00d440c1c48140d440d901c054205841c80504228940d0f4100342c81511000f100b2182e801940c40f420b80d0707401c0819081c00314030009000c2600115141e0505285c90520100800b008100a601140b004003007600d00046880e009905400d20500280d08480102d9600901c652b800303170184900710000880380d019510061200c5070519040241a50381000c05803201c0c41480f482c9a1a0028804900b002c1209001141c20505011214150038250307520038138456040e80440055075502c2e1108010f05400340401001c000295600b080b06c41015a0050403e005600a06400c2030010500308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 41546767 1106 41545661 41545667
    0x20c01021002071704030c06030506060a0e010c0303022a010c020f0304031704050907020f0601090e03120901020903010618110406050d0207020315070c02010908121207 74
    0x8407011001c02003810103904240d0701035507014041d140030441d0710321100c0100300840c45541441700d5189020000343c204c441c0104268010750701042840001a807010400f4061642401c1070510000103060880090040c501081401c0d120304550341180e4050050782d80030780d240e88000780541c1e081c50700c0032602d81075004800141a4414230040c00040c441300e4080600001c1e070356805050603030300e1000840c0508142c0f034180c096002118229890f15041c8580c034050244c03403406102440c030850950b47d40e882040d8250b078070505032001151003518203404171501c20000034001e0041640b2104800c182d010105070350f00d940343c600101c28501480020a40c0c0480301952502c604055020141e04081e61107100103c2c0d15000d0714401040344105040003900842d032a07a5600c5448140d03200244c540032458000c1d602c540d01c50350010060f0b00d410021581c40c28054203010810380c450340c1d429 = true := by decide +kernel

theorem cover : BRFrame.Cov 41366911 41546767 := by
  have h0 := BRFrame.cov_init 41366911
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41366911 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 41366911 ≤ n) (h2 : n < 41546767) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
