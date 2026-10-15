-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3995
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:16:16.796397+00:00
-- url     : https://prove2.me/submissions/d8a38d1c-0752-4a0d-bc91-b5da80314e95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 718345323 ≤ n < 718525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 718346573 1250 718345323 718345349
    0x20d03170a0b04152306160f060b09131b0e010e0405010b04021c020915030c1201150c02010c03030f0e01020c190825061406090f190216050d02030301 66
    0x840d1880c0d0303d903813401c592510545110a54480407a0380d0000114001d45400020400101c0d62140100c0400030a403401500c41d00c03c050154945402501c50105400d03115002c0c440c24441c040c00907000c44201d079075002070084580f0f20b06071180d88204200354000381421080000020790042c665203101c0c42244a00700030001ca0001c60100000c9008844c028288a9607198442c850281103900819202400a045030344502480c0c4070b004540e842285e103c1c001c0d46000c41c001c0030465004000c5405041801124503240004400040445400300300290400120681c14401c3c94040d50040340c0854402e40144001c501404645010354842040a0300d68403418090b0480b1480b0b000b000001c17030368020285440c3c124840017890460703d0845699407110480c12034500001c159102c1c00e6120112625600001c1c0341100403c401c09800410f0b610764030301020100080c124001c2518407500b0b940c5e141c0181c07203a010102040607042c944d440107110707203e103000a080300343d00040918105c03141511000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 718347823 1250 718346573 718346591
    0x91312030509030d0b04090203033105030613080705060c09241615090b100e040f06020c1501181503050a170720040b120703020d03170a0b04 62
    0xc0499600315520b250070342040c000e0000d0510726030803070410000d000b0b0000c2a0200160000b0742907500068403410b204200c0c05050510400d80f503600302e40d50030343e8400e0f00d0580b45040e01280d1a240700600284c90003c4070789c500001c201c0040180d84a1540010855405140c950300c10006540440a91403241e8007000e550a0300180d20b07091030811441c0f203480301d810590f00c1d00e01d039a40100d802c1ea049a005c0309200c070140c0304115a06c101c030481401088170700c29900b4007000900300502203170403012026081d5410080401d10300300c1144079450b800b0000594445c021a01d0b181080000403405210070001d10000880400171030a005103800c85442c01c00c4083c049a200c041c645156210040043d0443c0f503803400070405c1048010f980c0b15520161030720300201e030742e210054501481c0d0f601541c1e1540090440f8281007512520821000c1601d800f090000e51044059860015110080c03017031407201c408408152040e802d81e040b8440707002d00c03084981088418480070b4540c411341d4501842c41c01841d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 718349073 1250 718347823 718347827
    0xc1b120307030903020d0f051507031401030305030f041b08060a0614090103080c03040f0803071209061409030106150c061b050f0313291f150e091312 66
    0x4400d9194183c64a89806185030b00780302c2d240c48081c40070780340e001c40103070301c040864814071008284000d4801d0903505803400c560041d04903010280095198010034005000282e003213000c076030300080803042100e0550b40724640f2205019071880c10412a420304000060003820001da514000c50803d03109011642e101c058108154142000d074641c402c1f5802c0041000c2002600203042449104d401c0c0d1b0310b41600c0d00c50b82c0002540c1544150090360001905205103c0206100a20f51403985000c0d180c1714980381006040d100703e04030b03010100f24000380c061010b980960007100142400c03805900103450407603002d001c0a0030a003091307841c1401d245e10f0941c0b9010381c0b0300c5030b5144101c58884500301421114400b109800041c84007161480d0441a01c001c07681a2420608155802c2c041007860841040b2124010384007a0040c114002e4088030300901000041c20b640c29680420400012101102001c40c0c0102010310321301e800500c50700034050708400b0f00e0310702603010b40110581e9407030f0b220f01a01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 718350323 1250 718349073 718349077
    0xa050405120706020c1b010f08060312090406121407121e06140f0a0e0c0a06080702100e030706060501020307030f1407020402040b0307020c03070e0609040204020c1b1203 75
    0x40101550008455201d82448010141521030300841d80141003d400d6075032580b0301140c00b480891003d02c100089051903a0040000080001528011080741042400b00b6601c0e4440e13100541051800300f50440503031a203600040060451300d1040680350868180380c05409100d08441c1070303a00900d030000c11020081e400f0311b021541c1c001b0b066411604000084046070b640c3c41001c44143c0c6e100c80c8601041a1000c2e00d482c0144d58480851800d030400d242c1d800101c83c0003240390801d6421614080600b50b86c3c03a00400100d81d018203002d4010741e41c00c8000c03400c000f080f448014600c0c5c5801041c81c8a1280000506120b0384100342c10080252140016652402029001000503010320000360202d4418100d41510b002668406030030046c2640c0050143d8000703800c008001c54001c0700304049030340d0400c07007142803102c1131380076020003030600f0900d428124005089038010019400400c00315200c41d4101d5891a444005403941c9840d0359001c00c1410f68056074991160404100c2c080c054031010007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 718351573 1250 718350323 718350331
    0x30f0a0e1207020603060409080a080601090f06020c041a060a0f0210020405061909091a0f0a03150209192702090a06110a02031509061e01060e0d12170a05 68
    0x900307a041c054180c0c2080003980c001070001d6085a04c031900040001e0803880030700b40c3e101c1c441d2a580c0c003a01e04000010944a00342c1e1120002c40c1018404201c51a00443c4044000c0400d45000c2005603601a00201c1440f42d8050b4030741001d40020030882499201011a4020b181036081d82c00c02c1800208200690041d80286503000e181006420082040c4c0d45c92070b48000c8203801c01c041d1890fa140010030440324610802c4050300780c0c980c40b02d0303018a00310104045031242115080201c0e41141c8840d440321481d00204807420ba070009181880b99140230b01c2d1507403482a250062100c5844450001030080036041002a05498546030f01c1009298002d40b03860000150495407803e250240484411f05800454102800b88058110142c0c0f4240900740c8607449002c81e0403058142114802e10700b00c0f000301019000c080802d695118002007002d0581110050302c0c050b030f4a8201000000c2c243c40815030300401d01c003c014002210303580c000c0800016a40051800b200d260344802601d02a03917400c035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 718352823 1250 718351573 718351603
    0xc170301050a05120115060c02040b04050c0306060a020715050403111f05070f0c09090b0112030206010611030d06142e140f040f0513090201020717030f030f0a0e 71
    0x140140320354100003e904c0000c8001c400041001c1c2da14a6541180740c40c41d8101200144100914409504050182c0e45a40300155800c10041c03800000c408101e01010340003a109071800941c400c01c8610070407045028082c0740350811034941a0840c0940180e106100840c2d1105907a501d80540d45002c0c0032040c2000f4901e00c0950003c0a0460216120360050070308981c0c201460010030040341521038620007034541c0d0b400000d138091041c1444441100305034050543c048856005c000001d50200f00d082c1161458141000b6030350000303040782d081d4010002681c41c0e0a1070b224000418144036080074036620400c2ea9112404071001c2a441c11241d21008401000d00d603140900001a01c00c00d100706560005400c040d00344403001030110605c5d40a9445040c08040501c0c090009241905d40000048000102044000c00c207a001039142c1c2c1c010320544d415010501ca4803041e805043c421039102000c0f524145a030b9203040c8900d10280c020a444251140d071801c00783d0180400001007141982c9040d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 718354073 1250 718352823 718352839
    0x70c150806091e1305190f0206030a1d070608092b0905120604170315010c03030e01020d060e060301020a021b03070b0c031e041203080c07120c17030105 67
    0x580284a4404000740810554004188107500041e5500c1c4049000751100c244403a0684c0e00c40c100280b038000c85880340001d40104841320000222001000441c43d54180c54007501c1b5030351a84801c004084516824144242e002c1d100840814040381d514283c1d181503c1f02c14181e1103111000b550b8501441102442482d92015800702ea480807032156807002e0a40f0340381120741c0e15440418a918180829020141d0200086c0010021104641d071440321081f40c00b907003035285c12050610b40e00c0707901600c40e041c40300d9401c2940074540320750032411110704030100940d915010018102c00510003403082c240c0f0b5244a0300483e14038541802100d020b941d85138018003040d032000c50707012102d4400301402036242c81842c000092125002024205500c403501c090342c3c6902035004258060120f01590300b0f4080343c100b0003485200481182d030044a9010300d05880260f44510170000c061261490182c1181c0301354890069003544401da44c6d406034482d048000308413180b2070304c0040c1800280a80342c0d00c1030301e0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 718355323 1250 718354073 718354081
    0x3100506011b050703080a08160305161214090c090a33090c0518031501091a04060b04080f0105090604030f02150a0c0e0607050a290903070c1508 64
    0x301582c0c4003a024003c2094807250350352607865030241d90181501c1d20106400300100480c0e4405040100c543da60181002e1140c0c1c6800039072981060f902202d02402c1c040005603400f4084c06503440801d0007003804007038000b2402c02c246116070f80d00d240100306128201d002c00180030242180140f079818030144520345506c5054000c50040060b0048464083d03c519980000b080192401814090007032604e903c2d544003101c1e4031100d0f0301e100301c451481c00781d40018408007811041146090445141040010b62490692541085026900542036110b8101000400da12004600410403112014105d0b40310035098240c0900360742085a0600903500030740b00240c0801c0c0507501d45d543e051105d2040e0340810b1800001c0400d1401c2c16600300248540e0341d5900c009a54112403030b001218000c480c40d50619109070360b81d07036032010400001424081860382c0d40214070b01100c000c0340c4204181043c0075a42c902030785007664980000c0130945211201c40c1000822600583c4188484002603991501341c1d62 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 718356573 1250 718355323 718355357
    0x402210a060f0503032d070b0703061410120c0201020d091103160806040f080909040f0512340b190b0d08030a050c16030c0c0828060902100c020310050601 68
    0x100204c6611b1a00c1d60410450002480d103010140c41010359480003d03140e8248000c002d86814400840c60145a0440c0303030240080e00711030319007420b1080f0400840c004090000032400b81c003c140d0381341041801c1102200800600741010f81c145041a03080390001c000c0c0c6400342004510034484d80b616904904080f90104512280c0228018040c0d0486440c3c552114085084242c0c1220306850302c94a030540142005000d014810810240c20402402c141d1400100307200c514101e10203189004420504088105076012100d105540004091001e45807a0950040070340b40340c409c0c030110b84d00d8184022400e1800f8801041c50030341000d803a5045940360001c0e14020070001d4007a0320100c1c418404032010722140317400c2e825803038803d5841107142615444c01201111468001d101c03150400c110f5145d450540e10000e80d041d025032480300004001d2814100014040e00c44065000340c8072081c48540035420486802d032a62007a011074400340c05d681103c1e0200e40080c3c0c0c10724002880f1030a4002c80c41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 718357823 1250 718356573 718356637
    0x2010504090c0c0b0a020a08070e0307050405090a050f060708100f0501050a0e04020a02070e060f030d080421110d0309020906120f030d051905040201020304050402210a060f050303 79
    0x100c2c140c140f03114400740d55252000d03025012038801005680009107500321581c05005150400c1c01030502c2030210004c0300001c0d4807003041d0302616000c0d60346e8400041d030861082101801994000c03080d40e408092801103240c8032030044992201103401d0358003080d26054000c0380c01c0101c4541c20030f40d03160705040100440302940050708403001c010100300e112486580d144010b1182011540041c6001450070707009d103c005000030b10141c41035802d5031070512261404546968400c0e00c0d481c00c03002d140d440d45400c0f1101c62410409400440000d088822502c0d00124240c6a07819080115400140b28500071005d90702980301c02904014440f0118009007841e0980741c000310360303200039038842503141215146076070411800100402d41310424460b0640a0001c01c920b1200c25a07030901c51841c0540000c1c0d45c92250384100d6000d550300040c443c50380c400e5529011312400d003802800714039060100034100070b8101030046410030711455000207124500082241e00d0080b120100780420103031000103c04003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 718359073 1250 718357823 718357841
    0x3060a0e0103080712270801061a030610180305010b0108091c0513090f0b090117070e180a0b01030311070f090f110f0d1b021b010e0d05060103060e010203040201050409 74
    0x21100e00800c08090703000c2030913003030072018106c1c02c64031030b01313142c06031503800e40700315510003020700080780480103200c09000202d0350b0010701541e580070204880b060444484403001d003080441e0080441c08000c215042d0444c03404880d0076a1240582e0b1107080070145c40d2855a032141000c44102c2c0d0300d020100703010318007070942444910b00d80184155940c0f40c0005803112181d200d2100c0307907900d02c0c0039514034104242c1405090304082a241c000801913251b031740c610480c0100c2038440d00c2c10300001e000b00d0080041002d0585c20700251a001589898482c02c0420300b130008402140c0015589103200200242d080301301c40300328400b8400f1515241d00d000080800d00c1e4603515043c2c880c0c1c044402050a000103003183e24034540d0807990f03510301440c04000c685408020420801c1a40c0d0001c003255030020726504840c0c02e40c0303007821940e120000184c480380c44a04456401c400d11203101c6040c02000724901d4100d90144d42e0074031600c3c8100b043c0608174131080fa0024003240080c0f00034440054141d20450320 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 718360323 1250 718359073 718359077
    0xa080d020a1733060a03060e1608010303050d0b060a030504200a260d200613020f0f0a0801140912030112080421020126180a140303060a0e0103080712 66
    0x1400d4040f0100340700b588620031040100ba12130b40c0070003500c0c100c0c600403544443d4881d102c80f039409454500401e04441840090100311003c180301e503d07112580e1141d0003541c0b00402113562506a00b8011703028000456090b40c540040800a400c0c0d113042030790003d03500d8001460300703450a00301400711280d009440340303400701004003070300b10101010104803038900d401150701c5a00c0b50f40003411142c2800c070500c4160b901150048400e002ca0301900a003031003612641280c0480101c00c400000c80c0c0c65a00700c070541c9a2101c0082c0f8001039182c4103520080d075948041110f80c025031344094040c3d50315031503142ca910449900700010003032415407400b1802410301c100c4030340e498a6030301d4030310200320303c18403000d002e14203176000c01c080456800c1183e0f000380c8151404200c40c0c04a200c0b03000b2603030f42801461030b81c1002c85000d0300c010441043c400b224085070301401054440002401c0c0b00e0303403500100d880600900d80c1b980c012a00007452045607048a5208055518080d030b2941c036110344414043c41203007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 718361573 1250 718360323 718360411
    0xf041701230a020c030c103c0c020c03060c0406090806061305042609040c03141815041b06091a071e050a0c060e030705040903020a080d020a17 63
    0x42643d014030070402c15115207000401c1090b805151004800b83e10f0b80050302d9940245d902e0b421008d101c42000c1e812100e01d800c00900c464010805a04000c00f020a00760315014039400c02002d06880c07400740c0190307001a900c00701025190349440d5a60007081d40c0c0c5e10391120010520042081ca141c101c150f021b0f1107202140d03000010803051600045958200300c14816000c60f524030541441d1051001d03a41c494038060000004000c07510141d40c0026140c141a040750b0842120700c1e0070200205003c0000d03d010b0040705152504000400402c0c080170140c900300c0c0c800000a65038822090720007956002e104003070107100700c11419410359100d11703812500c905800109007074000140c030004503000c1c050700160540018902d010118003926801003014068200d14212130341e100002d10209035030090714001801d0aa60034181c0c07620301c2d0303d00024181c103c0000d40d03003040700d00d030303005413003140e01702e84809035428840c0051807000b12040b2070b554084050702d1030024000d0b10090314800c2d5600f0008200d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 718362823 1250 718361573 718361587
    0x20c15040317030f060d1a0603010e1626031803150c030a060801050127060e16020c09280b090709031406070519050f041701230a020c03 60
    0x3410340707080000440c2220702c022040061444c1007105aa0303015170115103903522000c02da0781c1e410b0700d10050306000c0c0c8624501000204991000d50100145032410390846001c03c0d55003610380360f424002d00845050340303e159001c819807034a80c8a000c090108001c095410301050209840816a100c03d14590501c02d1602c01100403851909050042030a000d0072039683c030302842e5110075183d070755022400d1689010b00400060558281c8480e2500c070006001c1c02c0c502c0954100c10180011f034102c6090a045902407145451040340800c175511125026100141d10400421101d482d04a4521100091010100d440300c984089581c0c10080815800600c01c0080300c04610360500c00c07203481c40403899010f03060060040c49400d88203104503000040c100707880c02200c01482400303414208000700c1002d140050071f050240c0290780c0070441c01c3c00002c0c0c803559500010002d20480c04120f200f25440c0008a900302c400c00c403540901348520f000d851200d91a5400032400a51200f00e201520b800140306035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 718364073 1250 718362823 718362833
    0xe09010605060f0301030219082505100c1205090306010306090201050c070b0d0b0a12110a0b0a030c11061003140a06090f0b0610020c241210060906020c150403 70
    0x1401c4101200729440752690b045205000c9101041c560b20400404e440c030040000c05000105102504002b20446450440c0c0076003c2600c9030460f0042d5a128031054011248680d1105285200c0e5008440420f503800d407100301510b42d4462a08042d030150840e00c01070020a20b030380c100281c440c0c41850080d15245046c001e9905110298002c20840000019400030381e00301070040c42600101225541e818526054071403030080484030000708104100d0406a08690b04c0310070710300003003260b0218070350b540391050f40060003400104843c502180c05a61807001010001505921400440440e91100c906607184d030008032640d2125800c0b113118010b040c50002c2e201d40140e0112511504a440c0d00100520306144e02c048010712490150081507210320002d40e00045407101000c00340d988044010854240e00444181d0403191000700900154591702009001d04140c4140c1132040d01c0e4070b44985460089424001c030b40b05101c0107074060301c8400f0992620001d03950b01d00384e051146074581035481d520 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 718365323 1250 718364073 718364077
    0x2208040b1b07080102090904020f04090b250c02010e010309080d23011a03010315140c030604061406070803090f01060b120f01050d030503090a0b09010c0207090c05040e0901060506 79
    0x114110303040100001e00d031940c10031440c005007030340f64001d500f8504a00042802500018406071181d5681d00b542d101c00e44a6901140006800c0020780d030003403410b18100c0780c4520804106103801004201e200303480700d214102800b000381c1c0c16910001e110001c1c80045000c1d248040c001c0e1034284007044007282c076008900c940000701c030f0714401903482e01528803440018244140d000300040c0400e1401d403203164540008907419254880d0b58000c4203090014078000400141030768031150040030301400007980c84400a103200c1d110841e0b0a20110b5240e0919010a0180c1070100346c00030070038400d41c400240100081d55015409600310f0707035155050310419094030540c5e800440301140c00545e40b10600c0401400c00e6010102d48000241545444041080114a110045d0401401201054101100b8000050b88542002941041d0700b40207039100c2c024001c0c403000101602c2106400a0405064000d9a825440383d85a01d41810301d4481a50902c6400500c03a00443d560341c100850a9500c42c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 718366573 1250 718365323 718365337
    0x19171311120c04180303240b0f0409110c0f0d0f0e15030a02040e0115050a081504060b0918090304140a18020909060d020328020a0b070314032208040b 66
    0x21840101414030f01740a0100ca40982140d051180054a841c00510200d525a02282c801c801400c0e030f82e601c00c0071540c505002c1d0f500300c40103850410741c0e1040d5981c0d8500107002c00c10003003415283c188180300c6140c1d6582140188480c04100d50001c001000c40c003800c50b40d80d030410042c003801c0201c8079170380103400154400c6840300c80843d804030301440f403c85030554075400f4041c218025854003c403c40301610078003902c800e44040041c00070004806444044452164903c041c00600c002c5403200c444410380d8100c036070054090401940e0100f0300300004150745008010075030241d45400e05240c80c0103180c103038200035550002580c3c64000348000c044001c0c8103207080720700401a25142c1ca841082034980c0060310745440349150001e03030310160b54003240e02417a2901c101003c20450060b502000109050303248042d511030701540c1c0009030ba10100c0000d110f8a031099448004000c1142c5110105000aa0320703003540035601005d0841001d010090070711045d001d030f040c803030038180d4652160115901200e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 718367823 1250 718366573 718366601
    0x5070305010507022812110607090806071430100501020c0a0e070807031d010209091b030403030902010210020406020a0219180203060619171311120c04 67
    0x10403050513810f005040080c40454a4070f641480e00d00f401400030180d1010280c007080c5007480481c0214002e42c07500705014410b1042d00ca50780350400c3c010300140040d106a18542c0520302c0010343c2c180c410b1283c2d01280084031038150400070b4103800040003042c50400e04150703c40200c1c22a07040c0d24401c1c00b4500c240c503409001d444aa0504000a052512100840340642c1003001d05008242000a180d64042040e00d80034a040c0d9074100c08801601c0c1007074019800d03070f402e56054181c09006400500c001a4103480f000e0035501e8603100f007401c0300c1c864500c043d092070092000c900007a03c65080001001d005104030703100940d0704007050701260300c0ba0b441140507074001c003242021401c0403a0f641c0d02442d90b04504842c0c0030301d40141201c51190103d140301d40243d00000190041e07a501090b69008444610f0034400c1420481002c4e0103460600d2074000000e8825001514000c240c003003604c4041d078002e2001c2443e6103240248006c600b00b0050006850068800c080c015490300c0c8a101640d0f2804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 718369073 1250 718367823 718367831
    0x6090b0c0418110307120b060f04061803021f020c130c0e120616020f060106110709061203030f0938040b040311071502071a0309070b0d090507030501 66
    0x4008481442e5041c28072848040c1840d8000001d0310192054a6014000e400c10110002c42052200c0c0200f80314032625520520124601017441040b002900c00d680c0d107500da400505072406000c051a13066803100035405041400b09041c1700781c41a03440c01400c4402d0044841982c801c100080030204141c80c0c03420055902e00e1001607195101c02007000250058510300c0c0428221100c9540703c4c40000c1c6842071841c0907e0300c0e003c07400d1080050b070404944000c02d031740295844480040c008420142d400d49640b08251002c20301401903c100401c56078464018055a0f0f62590181e01401da181e0300166010750302c03209080400e01414040c40c1c6862140308802d5011114002074103140109000f140c46244c0c404204000182d0316840581c1154240c1440d941c1008071610f05440c0c8405a040f51a181c1c844250340c08006400098840664200b403041007440d1049180d11000d90004942400403540062410800390000b00000c0407050b28a07603000c0380010090701e4080c5400c842c0c0c1d00031141c9070b42d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 718370323 1250 718369073 718369079
    0x9030d1104081c260402060c07091b02010c0519030b0d0f0309081b0307030609081b0a210509010804060b100203120a020304020d03081005040905030c0d2a06090b0c04 73
    0x40816000c0202000c00841380348248081c561135903041d80280000e005640000344596202001c0015200825001c0d8040c01540051200344c0907442c1620b62140266080c1900c1d11072260149054404010b0082503001005a000e10120701070212040d007603400480c000c130820040303401d034440c1000c0300e4040d484142c1c6403850200fa007841c00c1c7c0101441d941d5280180241d83c1c46035400324984003240c1e002800419051181e0038030286503c91010503d020002050303140101c02000304107001c5080c000d043d902e002da10b208071800456a56450f144000039030401201d0600d41c0101d1201d0382050091f04000b5145c107070351002c03230010100410820056440440c006014000032002c070342d8420690700b810f500313500b4a580407c18101402030028244201d45d00020550b00440030030320006d000040c0140031001140c04c1c0162079030700c4043c0c604c003140107a00b140040c0b140a03040c01080c1c40032590300200550361104040158061444088940d19100d54035400400d2000010501858610209940d1545 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 718371573 1250 718370323 718370327
    0x301050f0402030d0507020a1a21060a03030c0602090d050d030b0306151011010510080c0f01090b0f0c01020301062604021e010c080a090810061a03040f061103070f0809030d1104081c 80
    0x2e0300c41c00344030400602b4010400c440e02c84004080441e40e0504024104962602d40803010380501d1f01130a4200c00c3c110640400c5c40000156800e050f11581c50400980001d0414180c540004951000540b2040502c001ca1343c100b50380013407200b000306e2400100712042c15650303a0a403039058891b16412144542c0520049a040c1324000100e002107401041c664604000039180940c640f15804610f000850102d107200400800c452010315000000c66881d0b8446070050b0010f0910b2543c04c0c84060074022108642c4a50743c0f03c24011500102804911044071410702d00f002d44c01030581f03040005d194803010001c0c0aa074040d05248065071a45851142803c0240e868a082d0902541006041910801506004d800790a0030040040c00050b66543c80c0d09001880308407100005211030b1030100103415500d4810007440c0920800d5545144043c4c031010120384248050742c0b00303019900208800d0741c01048c81c1e4001801c03640070715011410250344400481c213289007808190f81046054101c1d00c03c1907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 718372823 1250 718371573 718371607
    0xe040c120605061e2212030905011d120a060203012309040b2d0f060f040e1c0e1002030403051005090c130b1306050301050f0402030d0507020a1a 64
    0x4001d80300c150410310541e5891004503820075024008130300c0040da00c8201c4510366807907562a00e0031881488441d50310115011403d20b40c14098000034910b8801140031762260b000d80200c1c8252418001300e4034014420440a06020009060980b04403003201c40028080c1c0059802415018403c101a442100e612203100600c500540d100d1400322040000080074002445e811880112124207500402c0c1a4441c00c802d203003005450154007003003000160701000103180d109880944a801001c07910a0500096942c1d40e20000350799040130340030122001a118812000d10b03c9071a01801c040014400300350001100340d172682c0144c100140c28070500c0020001c0342000600c011040019283c0714461039114003109503114400c1400c240711100401a07500099905040142692101c00903c0001b178001d200708e1040074003950920340050001d05804800902c03540d0090064000d9072000082240e80354040c00040342c1c41b00501c800414401c211100c40d00c0c11a502030112660b80040040301c031a02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 718374073 1250 718372823 718372829
    0x160803030103140105090d0e010c150b1201020a0c030c021503040b0405010b0303040510112a12010c05042d0306020702130510180e030c0c01090902030708060d030e040c1206 76
    0x740e0400c2c06110301d01b00c000038642c0c0a040313185400262403548a0049a0500314620050134000d00701000e08a411010b500182c17680c0401c490300035500c07508403461380c2031f40a02a08003001c905c0543c0c02c1400b0034054072918046a100402c2002c0007a0f070504441c800d50810380c1c1c1526401d00300d1080008101c000d04c1142d82c41241200250f0415241c0706c0010155080443ca802c20001c14203d46061058100b0141c0c40211100540310001c260180031040c4845402d0b5000d84198010140d8281030041881426100003c960303606140c103040048068800e0719030703072283c4004480c9050601d20102d000c03070b0400c0907510800e40540e0b10398050040100360f003000c0c0161880035140c40c0610281075144d002030001c031141e1244c030980300c8540051171001050658428400d6000002c1d181d611810041086429801c00f601c48052441d1102102001c0f80422598400854202004600c141c030300312414075119031180c80c2105040010b0008501540c422540d002e01107614081b8a402046031801040c000e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 718375323 1250 718374073 718374113
    0x18071205010b04030206071e061b05131403070807030b010302040e0105090c040b040f061712030919080408010c03060e1303020a0b090f0601060c2d020f0102160803030103 75
    0xe9504016602400388160f110003441800006550010050003810b5480e01d906046c284d9140c2010a04100014100d032140e030092740a000c0348a900010300881c280d42c51042581e420716050783c00c140600301c2d440c04c0b54180035403511400200007000380080009101841c4225002c0030254910f20500050b03c900303e1201c0f0a90f410902000041c00001402d55a00030084a0201d1132250b5900410004d00c00c42e0380d5400da007030030000081800c0100c0001c03000701e010920200c42d10449076072030080c4180010b40d04000c07a8cc0001c1070080282a00507903440b0078a0041c1c001e01c0ca4144e680141d40c1c215154281c00b0800300780c0b01d0030104450410414255403125107884c036241740c0c40070396400135115055204002c004100e102d01003815003204103d401018050002200c00c1e5503160134004e400980300410484071640e9991154506049c2e1082080c044200e140311a42d060401e03030308020304401d00c1141b03d03046200d1a003c80620480762584440101401406140c1e00c0d41582003950804c9401c00800b04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 718376573 1250 718375323 718375331
    0x91803040807210206071b350d0c08030a150e0417040627122109060c080307110106090902040510050d240c03050a0507080702030d0b06040302180712 66
    0x40503032204412a5240c61f4088a0140306c10048040800ca251407074100a0300000211501c89950454901c013580510f40c8038213070400c07079141e042d01503510b46044100c0030000c1d280b903054900203810400035517001780c448000892910040d4150000000da50f078004116a8028402d000a025014580002140507844014540360a003100a05800c0d400340305c00c1c405007004801034180c0b403c61441e15003c0c043d09110301001d480a82040e00d0b01c010044404c000b0000301070610b01c07400b03024400345c0003101c12948072100101801e032185c1c00305400040600d01403281051905194640a100d1070000d45075403d40001c00c106140148022510002d00765190580242000d100560b604038000505a034802c0c0b24503601c1c410440000c66200d4644406001c45007070080c22003130213402d6040b1900ca040054001c01442d5603d02c801c843e13844007a525140903800401410301412400e400820555078090003103442c01c1d40d00d5011a11001464000700c5642e2004410700c206640e001c810a04103240d454070a00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 718377823 1250 718376573 718376639
    0x1406010303050a0c03050408030408030318010905070b030c190206071101150911120403090320090604020c01061e0f0501080907140d080c0a020a0614040302091803040807 75
    0x41e215210f000b058806025041d038a21080600c2041102c0c040e01d211000e03030b600c072940c40c01250350f00e130000d03a01e200072550650940c0c0380410301440740075101604400240f035020b10301440003006a1001c2c140810070348040061001d40001d1003c900401c1d0398650040406142c00507006009903201000c02c1c1e07859040c0b0142011000e003120014017515518040004e058030783d00311080d401c0c40780c01030144205150500700418141c005880c9011640210915045484d01100050401d140501c07501d520400b101d01145150400c2d6001d8520b0340300134000000d10342d441e00b25040601514111070072042e040741b0001c0c001201486202d0004003403e080121090505e480400d445001c0360040414040c0702032549003013680d508200c0c05806070020034159680c800042c810f070b141e160b00c40c001c0c0c2c0940c02d6020002a910712580003043c032101400c11880c103260550f403c1041840018000038610950000a1100b000c0144000c20003441c0110040a1040c6048060807051180f180e400c544807121054030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 718379073 1250 718377823 718377827
    0x2100204030515090102041e0303020c0423060f030a060b0406080c0a06050a1b0f0c0b0f040b0c0304090c17011e0b0915040b0c01060b16150f0c08041406010303 70
    0x24490350341c080c5100c14000d41d81c0d030980c1402405a580300101800c00c50000e04203074241c030b0f078000007074900035426296156040c00030305c01a5054185c40ed50500101410506a01101141d041d040b0400401c811400200cad500060b181142c400e005445240c0c0d00c4001c1c80b09458103200704030007007249201524502510200107802840503100703050901c03c0c00918030b4a114801c08000e40b810a50048821456060341003140072048000402c444800030703e0300105a00d121041602c10702d509181c11141f0749800c100c54100130344c222040000680c03109000c04661718145006e0940416416651003410340c101a180c80b00002d4180d200e05140741954425013000004c800902003a152449003466844040c0004600c00c581c1800b078a44030380c2008240030504000100003001c0d80300c1041c000740441e54072003103000d1980c440c410710358110f850306458440010390004200740035101c85190004440c00724000c4c0d0410b8030070017005803001802000420080082190b80b206c02159a44010501c0398190f030744c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 718380323 1250 718379073 718379083
    0x103020612040602070f0c08160b030118091208040b0f13020405130210020607020c0301060803090405040510020708030708010e060d0201030b0a03020445030c020a09020307020d021002040305 84
    0x100c1c61108120004061149540480d140c085d801802c07107080546c41c1c02d0441d00308050740205c0c0003038040d402220088072101c4144805554240c0300d06490342c0d2038000c0100fa029041801081840d032500d903a0b10100d18403501d55082c01d245a211701600385400d140174840148005c1220711100c62020034001802d2461303005030351407a815500044c0b1364a802506031041540d201c0000d43c040000c88075448050b80c003184550080f5065000c48900b10041d00c10142078604902481d2201d600500404465241c00c2d004590060701910a4850740f08074404d20501340ea2000344256200c2c0400800c0c89403495120316040e0040031200718151003400e1020002c2c1006140034800303410036454104031451075807802d090714002c5038028020003040702c0360049058100b4240341c42c0c08039448140003011140305055154103100c0300740345c4092007040e40c5940648250b20702080990b002000600041141703402440114054105038004040003020b411000307181410900b40c0400300c80c010701c0100001000029 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 718381573 1250 718380323 718380337
    0xb15041508060609100324060c2012010207020913150b030c031f05090304060215091006060314061c03031113030c14010201090c05010804060608030f13050901030206 73
    0x1501c4441610303104001040750042440c0d0710b9000c12814964840281c00d54480d2204220030301c1049400300302e5090012142c8518072442002c03840700005680001c03c240d2100d6030901c000c4160b0a556036003c0041010000c072201c5840050b940040d00205520300448207644c0040864000701c1c6a071060741c1c81c0ca40546250b4008138219440302480d51560b50144141c40c09420007600301d81e40c0000c8064004c9840f0168005e0015461400002c5540050088111400e540058004010607541c9011003515544001c0c80c4e4902800380c146510781e41d00303217402039030020112507030f0118849421110b0f84030358401c0030b4640751056010001d00c40c00c0c9072034a4506045103415040000c0c4034020000080c10a100c1e03d442c805001c401100c010003048480c003a080182c6903c110210043e841545c01a402c032100010003808400d51004100050b6100c0c184081e03025220729008030720aa9102e02c500e01e9034101c030350501c41030500401c0242c2d0f0300d9441000c900050004540001040d4510717000b04456101c0d490f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 718382823 1250 718381573 718381577
    0x62c0c0405120a02060d020409050c12041e020907030c020c0d020a1e05090115080a0c020303040f02030f060106031a040b090114060708030106080a110903070b0307210b150415 77
    0x100300c02980c0c02c814041120325039000f406103903031a000244500000e40c410301400c42ca451402000c100c501a00c0c80640300e01c8c1c00700c216002500d80700d039164640301101d80842c0700c6260b0003902601c030040e102d1210702801380019460114500c004400041c2c01d00307403407680c03403070040035080e00d800056995444070034101c0e4108041c5500b0340d0070011200418400340c0c0c000075089580c030f000010742458890703c580c45041166850b0001606c8121182040c0c4052104410059000b8030202e00865044404d2105580c4000d00310340c3c2070048500c4090030070344241e001c03001084c5d44142e12041c070f6950100f400d420910850301000068252800103d1084041c0140d6200b030a0000c0c8000709134507102c08980d070075500310040341e480f5a034889000b010300f078080359082202800c00c4006204026200291440128014003512202e420f00d410300040c0c0c2c00080403001046520704881d01003140311f038800024911203400c04105100c00d00103203c10801824242d030341440d000c207c1000a20005000318086802c0c074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 718384073 1250 718382823 718382839
    0xe0a0b0a0e0f0c030706080705040e0a020403060c12110405210f2505121522060504020a06111c090b0a0c060510060f0c15062c0c0405 59
    0x4146800140a24080707204680300b007031500304160700300180c00c1c1001041201200c1e1015160354089a0b092829604c00c000309009120601c8801c80080c4141d60000d51b0301d80040c01e180c0d6940b1820250380c044440f01000c51a030080c448c0038100107004411a00c0c0000480701d1806180c403010a40c03000c15540d001808181a0011400800044c0103800090480000311070628104981d441181c1807286008810100d0300e000000b040d041060741c80358901c00d000080d00229130001e0711444042001880b2030395440c40158502c0240d403940c6085192907004002c0010a03107481d10600030b04000e40d4001109100c58440382c48150706001400e42c003508a41c07406440e00c0c1d40100f5068134030760500e070400d580b0400701042d0401101d900120b07805002c3d010380801c1c4100d0701c03100712903c200340060050a002a9450070031040d020b003e2140f00b11a64421407401d0744102d40c200e0b00700221a080c1d04400c0c03003a079038000c2c07440d42c50044200c07a0314044c61800034440a070424249070740c201e02c41d81c4100e501465403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 718385323 1250 718384073 718384081
    0x301120f02040b0d0c080c1f0305040501091b061101050f062103070b25020319050c06040515090f0a170d0501060906020106080a08030601210c0e090603010e0a0b 71
    0x10300c0c3c021070801071020380000e85460302c2c1d28004110414a00903006030b4411070003103c0b00fa207030120791442611011802c1c01c4862942e00300807005420000e20559080d92646a220000790342520341680884007000c21210702e0781070840040c00d102e1449203044081c1e04150500200500120349960012011107000140c0c80c1502042c411007807e200000035079020110b070500500502c1201c50348194208210f105141e102150304c469650040c8580740700682c0188030708401d6452200702c0402c02803641c280142486041c0d6941481c110003290b0442e201d030400060303886005508603400703800c18150005061080081100c1c07560340c121304800a029980c00310102030107503d95504a407000850400280510f40e100d1501a004001a101e41c0d0015864850b000401420100c2e60240c615840340e1581c2c91a151000115158600d0b26035a03a40b01c011130031320100760141c510401c5860303440d5444241c040c1c0b00080420054000040049002e41d04040c410310000501040c1107a01540c0030400d0240c0383c407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 718386573 1250 718385323 718385329
    0x320040221130818041119050a0c29010b04080d0f12050a0603050c2e1403090a0b0c0918040507080f0c030708120a050d02090a0b03040c0603020301120f02 68
    0x34520a01400c003c200180000c2d003202600603001c0849010b440601200711800c1c603401c101c0c40b4070032000320307480b50160043c507580c1e06c074800902020301030b441c210013144465201c0890040e001100342c3d47c0a400305d2030320300c5091546801c2e503006103907000c1300302c2c00d00d03180c21400ca0316162a4000c100800c26040c0104041134024001038600e03104120303041002e0303d03282c09544020070b01c0f0700041d1120f12031500c95454a1600040014a8400c0c545840c01c82e00b908400054842440b950044140019412010069500c2202842c40b546c041c0009142104140c1011154444060555020b00e2020019514039844c2e4200c141109500c01c040003007141e941e401c101e8244020f40d00800d000703000d80d0458840d50200003525400f80801141907403c195a2103580aa4610040104900d5000e00740b00c1c1e0180c2c40e0142c80904240c48000d01d01628125003000004c140041a41115210007004010710085c4004120204003600c92810114919410950741902d850321030000180704186c61010201152 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 718387823 1250 718386573 718386601
    0xa0b04020a090e0a230405100506030304090902030f060f0f1f14040605090709061d100507210507060c080709050409080c07080a120c022101150320040221 68
    0x83c0040b000a90003945c404610300100041c5c0e4159128481c1d084080c001c000759201c0d1902802e0000d00852420f0700d0b09480002a0040c210180da050280c17800040310014180301207071140d440030710417145070725108107070100c03001c8050b01c0203060300b203403101e40706408110600c0c2109071201c904c500c26255241c10b000034052700b03854000d16046444002400047c5070000c0450007038030460b4a41402e201c105a00c040075a001c903501c4541d000c2442c001d440c41080c0518010302d00305000780c918036054001c1500e43d82001d584060100d000031800034441091010380d1181000d521a5460301108504049038000d140900e0340c002c0501c0340b0394458880c400c0002c0401142c10785c0e401c207415144820323075410030148c982500000984100b0314062502c15054410b402007801281e008000c00030100c00003c4107a10b43e40c045890700f40b0ba65817000180341d41d840b00204500151703c81c41d4030620400d00c0c0034452002107180400e0a010314018000400080411840751405030401d5080c80e03003d594001c4d80c801c60b4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 718389073 1250 718387823 718387841
    0x3070f03080a021309020408010b0d050a0b1e0106020a0c0602031201050114070c0801020a180b0406032c0d0f021f090804030b011403011b0e0d02190803030a0b04020a090e0a 76
    0x2412011380d0004164140c2d401030021140d00700020031498800c01c042c001052041540140207800a45074803000502c2c003141150001030040807400c07007203004050313408690004e80001d4050307804085502d04108510b40e122014000920245040000e0719000c802c841c01c0600036076050007442c078100c58101807190152500e0540110f00680b10b00d96070060319000394089140c0303034000381c650180c1c220380b1900c0185802c201da03280310307000389003d191960440082c0751001d41030140c03038071030070600d0600f200300d1840e94080401c0a01524100d450804058038070b00d000c6000105540180c5aa860443e4003601600e0721008082030108489419107848480c0d4801c1b07401c01401d43e102c2c0c90000c0740c0e0314103904d645554250284c0007004410703d140c002c0d83c065511903812000181d8035000c0c0560340d08180c844c420701540302074480d4180b1150706040400058464004c42c10070340c004000c00801c500c00b4060b50315020000d59046142c0409518010254200b41c000c40c240c82c030088000c15503058139a8046512 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 718390323 1250 718389073 718389097
    0xc05090604060e040608030901140a0e0a03080a030e160506070807080c161d18010906110904051e060d0c0806160e0a0605030a09030314101703070f03080a02 69
    0x1a07a511000c010b0500403990a07658040c0e40b400d280480c102d00000122081003070140c485c4c0c22074900c10654001d465109030b1003601000244a1140708035140c100800e406584103204a41d00e41d002170038014101c4400940c4801c070b9500944040d00360003100018070080d07400c1560030950301c55103810010403500c58900010f0041c500056035060220001c00c95031640f0b211108440170307103a522000690004440c14104803d24803031001701390307030100c400b00311210a1460800800e102c1043d80f100411181c9803640c00305106d00001d184d10451501d480b07069402003a44821500044107442d001440c010300400d03207400354a072188c0040030b12901001d00002045140100c0b20203152501c80b425041c0c0d030810588020400181100346c40c1d141820324002034403074035a5101e040d541c44c044024068401641c0c1581890794515020515a10f01007609100d140c50b46400e0103000d28001d8500e4400c45007008140e0250010b00030f03038000400707685021404941510384031509444001c5020000d22400100c019 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 718391573 1250 718390323 718390327
    0x30f030103050a03022e0c1b0c1d1e0601090314070509070824011404030b06090708010803090d031e031a0303040f053105010f06030902060d0c050906 66
    0x104000000a075202810b10030360070f84410441d5114219080103216005000340e601b048001c0041c01c015a210f000061458640800c00304440c903c490100a01c001d419100e00d80301c048180000058907140704400008440d1094607850700340113261401243d045c480755010304410129030740d42e11503804400607580102c074854140c0c1000503056901c0310709115043c021203880000580d81800703004403c1c0f00324803828050186e0b1020403c03844075087c4040000d81840241030036603408910746d50240c4003862050364000b96a0a02108000300818000d014070100b2000f00010711000c04044151000608180c8106030201040d00d42030f501c40707100d540e60b0744810222009180c201941a080540344d80c00d0000f0071072030f103c0d44009044c2c07179100da07000d12091614200400c00450504040410b0000480c40340c0d4140070424140300d542185100c051082e155807984014041151000c00d240014001c41c00c0400030540140c1c0820168092100c0207509030b84e40300c0c41420014003c1c02250400a0000d19041d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 718392823 1250 718391573 718391579
    0x30902090a0506010e0d03020a0f1713051309150f110c1c110a03110c040603050d0201180b0f0402040626070b04030c1a0403050106030303050412090b0f0705030f0301 73
    0x3500410b41100c8003400548458a107840d41e043c0744c00101561a0958007411200c0910345441060320b404036001c80341310a82d440c40c6040014140d014001504440c02400681c625013000c2240144040100c003001901e41705116001900100b03440707504420440c80451080b0000103070200a04420000f80d001d0344000070921884003000c128459499001e50280d02180b00e080b104840110014011640b01c2c0e0050b82450082070242e401243c00443e0102154141c000d2440410140c44076980211034644c0b04404481c0a150280034540700303800715140c1c0c80e0301c07503038142c68031822490042d29400440039001e0106056441d40c0d003050014208000c40c80b070510500004203051030a030b44404428a004038a00842c80d042d1034400c80b011641c12102040c0c0450a01076010b1401c210340014111040003000700000040c030a0240d400150b0082d00d000411f1b2500e03003008010108924190001c1140e83d110522036200c1d14020744c1e0b900d0100710b025580341c2c0c407503240c5540746100754a030500c90484084000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 718394073 1250 718392823 718392841
    0xd0f0504140c060f1803010e030c120a051806270a060908030a2d020109030f031b0806060d14040507050108240f040c030b0901080d08150103090209 65
    0x60203503110303400116041c01452034154030b511902c070480c0d500807000c00c00c2c10034035041300303014101c82a00007058411a8055400103400c503900314034500443d42010031090318010042c00a10400b681c4601d846160010011000306544201641510322100f420100400c6495070415a2649017000c04c041d00e201c00501024040b500d090344800d03224040103000070560742e21a030284012208400019030034400900e8050b02d00b00c680845e079250303c1e4046d492900703200c5048982210383c0351245e000041c5520260500501d1146c12001400501d8104203650540d1079840700121000c03025403524058a40700c0b10005145d0388600344100c07001904104158050300c01044c0c401c0c1c06607128508444040c0c0d510b40c01134881c484221122803061000078582001800ca40a14840001d0001d100d13903d09441c5400180c00c0320359200c10500001d98440390a246420200301940c05001e103400107200c94015890000c1105c10010102107030008022400c42403a4001d4021041e9103a00074001d04142c0707018080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 718395323 1250 718394073 718394081
    0x1508040312050f04050111250609080a030c02011a06401401020a150b010504050402180f01051603050c03130e100e0606070b090c090a0902010212040e011203050d0f 72
    0x4169646d500e482403003c0d070444c108003105c00b28a60202d1424054006080b0b41e181080d181c841601c07244d07150b03481a400035125400800703115500d5100002d0340c001d54a0000d08542d00b280d0140c49400c20b0a0140e0941daa074a02500e9800465070b05907010f041000d5881590304000609076403694440d5a04004000b46400b4210140c914640040b07600082c16401242d940c191203001500d0500c080e503501170b008a81d5002000d210030113040003450140d40c6c5d07000ca4201d80c0410754000c01004944003114041c58115003815200400b4070b03200e03091010a00c00742d10200340810300207082c42030009004640070000c1c01564024500d060403c03244035136480c0d0039400b00c101141c41d220980f4540501040d00d5100e42c080a000b810003601142c2000200e43e44c00c09122005090b00107944a41e881e24a02640c90104191042c0c010a001198800d024800607203080080c1441c1502030340c041c0810302071035026200c5581120070880302a1016501d0381000e40f0148684115100c9060504011014003001500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 718396573 1250 718395323 718395331
    0xc05060903120a1404030c0809060d0b09070807050901181203110d0302040311010e0613172803140d0212061c0b0f07050408191202071508040312050f 66
    0x202c4070300b9a0742d078030703401030101e400d0003107540034080c110408500400c0c4a800035440c0d09105600403444c11042e54009030305500035508824040b52120b40c0e2000c3c42c100361119030303000221814803900d20b0070304100c0500030340100340d01c55042001d0704100700b6100b035040125000500c0030215102200c14907060041c14018a4517403049036109072481e503507030b840c440e108550449800c0304001c052008100d00458080c0c0007060100d07440301050107640010069403403080024844200006c0d04200300c044e0321400c3c8003002480d01111510b0075034a15600202410541d1ba841d810325050f00031401d580103c8400340142411450358a01c0825504d604e48800c00c1051b0107000304449880300808032901c40140700910140081c0109102404117050340c0740508200c0d006092400c2480c201174544070300901c0c055140c405254400c03c06030700c140c18411100e241082a4000c0c2c806480028141111901c034254400030705802c0008800010b010b1502c1132800c0100c55107030400c280518180001000c4100340180c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 718397823 1250 718396573 718396597
    0x20a0b030f070206010b0d020a11030c100606031109091015120506090717060a0506070503040e0105040b060a05090d02060a020f0717071a070512030f0903031e070c05060903 76
    0x30000c42d01d8603000280140c129840080307071a00d0300f20080300d858003070b400402c450002d01c903052070010ba0003203050015015043d004001001180c1450300c0c00303410386504be03000c03e0a25240102d4030505901c040e0803600d4642042c0c1341d060f00da4803401d501e015018070359405114044079000d4011303141c41d40080c10805514085000340041c0d1607450030480000340c10380d02100072075001d05444500c04408a8130580c821401000e8003081903845003c214203500800b0216aa908000381c1480078200c17515201d4050403040d1001c00840c4c41d080013282c075900c202d0f0074904c140f10000c5481d0300242e0310300344100b440c10742c0034005a4613000804406580c504001400e03039418001d0305404590303003c01d003001c20301c1800070354020521186010303004001c07042d415401034280c05041290f507000c907604100007030380020b41100a60b90b901e85100121803017a0f018140d0f0205402c10000d002c007080120030328102e0807120f00c43d00034260b01c0301081542c00c0d62039694010014040c02007040b120420100103851456054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 718399073 1250 718397823 718397851
    0xf032f03040c0e0f130f0512040e1014061c1b020c181b070c06093b060f0301050408090f0616030e190803090a060203090f1903020a0b03 60
    0x122860010030004413200c6002c694500006241c005035800c1c1d040001e4000c0445090105540e2120380c240101d583d03241c030b051500000c080100b410714104956200e0501490480d4240c2004030408645540342085480b48002240c248551151a20b90407400c07181c4d5041084000703031b1030b41e04800c0c5911003c03021000d405409098102410300c0c0c42c0081004004510b0700820b951546500803000610005111049205214a0b8001a000401440030f0b1145884070840c881c5400b00302c500d2030032030824030400d6129040121a50f440da8941403e151030190304075420340c0d601e41000c201d8000005480390360640c00c1c0400e00c02404440d40080400300e00030b07100804500c01d020103101c400c0c410030b078158558244070025980807a2040104080600000780180c1040c03031000c0901e0f04000032600020744a410008101d4003a01d00511100010000f07030000c1c5041c0a10240000e0441c9828001113000b140d50080e00c200035920141c440002d160300601000d282a1141c0504041b0380080b200c1c8801c403001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 718400323 1250 718399073 718399079
    0x3080601021504290a060311011707050a030905030a0809191725110108060103270201030605030f0105041b050306010320040603030206091c0f032f03040c 68
    0x40800c1c0c461000051542c281c21035161a0380e484c403410881031120200c220081180c02c40a1095200d90b070203250340020200c4c41c1d5056082070248180c08401140c140815050070b000e2820540c0d010303580c0b0001078105107071038895500d000c0d0f001c1c00301e02d07000804034080005c0342c000b1190442c1c0c000c0d0113407201c2c5044403506110224408400038083c2c3c006800380302420101420594034100602c0d02c880c1024400d040c01039044c04107411400d0140c0c08662880c20641c111402c0d590000301507521a209180601246004034400180d20305620781d40388404ca0a160b00d181564000e410510051202030b0480c0c042c28201100750b8001e100c1680c00b01c811105c192001500c0302d0350302e1000c401761030008000e400345900c0e60340c61840520682c400740c0c0d940081844103840da41e54510905c4010f41c040c0d000740c6038500d400c0e5041800c0109240c10060b45c500174441e05200b240c0e201036009005c101a00340001c810060b1840c018040c01c12880403440750b0b0071500884c8800c01c40101550042c0d225444c640d001a407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 718401573 1250 718400323 718400327
    0x304080c010f020c07180b1206160203090d020d11060301060f02070f150503040f02040501030804050906030114070c06020f162006030a090f1203020a020705030c060d09080408010f060303080601 85
    0x10030340d404e81c0e10503400068103110030048508002c0c0c10080c5058002450420700c00030882c20f4440d110400041e4000308208400d4080c040103070961b141d0180b018500d0300c502800021101c007001032020b070144560070b40b20810880207102001d51190003c00303d40d1a5a03443c500100703400c0000e03601038014000c1440011b4404034250b0b80b401030f1149076513050482c0e50180c01c203c8158000030000d0340e104d030100203d180583c4680c82864081e50007040c08555a500b44401e0051184007c0c0555001f40c0c94402204d41001440c01d80c0f64100005142850038201c0d582465400b07070103070039050710f1036680014600003c1c03822030f5800c40e0b00390310400c0c1c1290404402400c00807500301c030003111601701c50700f000014004d00c130642c0000700c154450480f80b922500c1c20344440c070070040311010750400f0903400200390201c107404100c410300a180c200c0080c0020341c50303e0086949809081040384c0359948802050081003021410b440c060308440008200c10507a20010001600441c0310503408240b10310003089441d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 718402823 1250 718401573 718401577
    0x3010612080d0e07031709010e09040c050913020a0f0e0726041e0c03060615090b0901051e030f01151d010306080106030c0503010f020408060408090d02060304080c010f02 75
    0x150851031075801d00849070740100c0681103c411650560084141c00b100090081c00c0d058042080c0182035500c625840700058120190050500c0c400c14040d4200400680011805002ea4005540310304080c1c55203c500a41002c45050082d4000c480c4c00c4089400c00d42e0102540c11107030100c0c15495030380c450000c2034459120303d8a10658a0f807080400c013600410b10005250802c4c070402d110011303840c0041d06003503041001d8500b240c0b0003d68950400c01e002c654011075011381929031100d0744080d440340740500084210b200d03488681401054142003a0300604c2070b00d0720660003044003240c2d91811a0340806070f034400c0700c1000d50030742040300108108504466041007850944c80b070080000c40b0350416500460712050386810140c5a04010031440e1080c004c001c01180f0031248417040c50b00f03080801d42942e90070310314180d03107610500081002c2000014415002600021144c1d61418108003044200a45402c06034114900005100070044140003d09070031241c400200b26914804c6200d006034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 718404073 1250 718402823 718402859
    0x30309170f07050606060a1707090302040903020c09010506040b070201230415020f031e0d0e070f08010b0d02030a0201080901060f0e07120506010519030b1017010b030720030c0f0c030106 82
    0xc02c02348081c0b00302c00e034041110360464154142071014a5882e80060113550b048001180142c01070810095542011079100f805003070215041420a03043c28004501c90003500800b0b81040003070001406850001d41c0145c01060302440d107190713240d0b1102e4440c207940c1e8080c200b020043c03186141e0030100740d50202c01d40319858411030104803524841c0c0d400304015040140d449042c9541c840e062800a002003140c400104445c43c5826002c1e4502032900c1e0849145508150090450104040043e60081281c0d4070540d82403c10b0803982e12000cc98500605150300054549401e80f48013184035004500d10902c101c0d55941d400d031080c24421500740503a4810b45800740429014041c1c08510300301c00c1c5070564114241c1c0b4002070190090300000342000c8489030a040841c12054030140740c1103c4010640c050b0204040c15883c508141c84000c000300d0b10b108180d040e0a4410414010035801481160545c400880486814a00c00940682c07a2112008000e200c0d618100000401c48001c121a1641c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 718405323 1250 718404073 718404077
    0x1406100801140f0301020c06010e0601140c030306010c0c030503040303120b040b3109080409110c0706050706020415120f0e0303150d0c0e0f0708090a030309170f07050606060a 77
    0x8040c40c5014000f00d800d0441c800c0364555001d01103209540000c02180e802481c050075101490300b029000900f40060310410380b19101410000100340313400000c2207980017442880d101844001d03504110802180f160002400750100040000034075601c50364100105800100c01c10505000340108812524019181c541140c1843c0c9446003184082c0c041245c0518115100d18550b02543d0f104400c03202d1240046a0720000070500740403951031407141181e40400c0d80780203031500d00c1d000a6680e55400c60312403042004000240d44041144c2501a68000c2803881d20f64682040782c0c460203010305003030f207400381017452524450003c010000c1c010f00403c4da5041010b945140c440307d4000001e030300044d4100350064080c10319000001c5031080c03900c004000d648141c118a050103500d1010f41e1b00060211005c120706401030003000f5070089070701c000e1654141030004400000e860700800d5141c05080c9841c4480010034481c00e0462114010510389104600ba1786d00c0e83d4a803030420180303004080807400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 718406573 1250 718405323 718405349
    0xa1713021309080d020714010b04060e0f09030d0c050d110406050a0c050f120a03050901051909061b0c0c0f060c021908060a0b010807020c03030307180302041406100801 74
    0x1c0112440c0d1050401a000e0803180d450082c942c044c510903640004000c07a80003030401e5800080c503a00b84100300c12210120f80070300540d4900002035164002c06450b01c2c1041e02c01d00042506072404104840e080e541052050048110a40e000341440e000064218a103500301601801c4002e040c4041314142d52a0380c5405080c4000300e0012185911500d0382204c00303105500c00140e0407241013100b8030309000f4400989903201c020040c020305a50000c1c003540c90583c1008140038102003041041300040003c5440095000070300e08080006d88807001030140c8144512441ea18495400800302071214011a0300c7e5008a40e2040786444901c0c49100c0d0341c00003100c0130003410043c80c021102109040300c4550b00c05440d920b8000d82d41c01c0a00940e140c1d040950380341c4440301d0310358001d000b490780f0211a0024000300410346001c6a141e01c0000c005030100941685c5050070310099402e5000a1600078004012403101c4c016100b5420209840f200e10a64402e450403200c140f0910700f16060b9014000186 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 718407823 1250 718406573 718406599
    0x2010e0706050d0209040216031704020607020913061b030e12040b0f04180218032b021212040501051609090507141c050a09020d0b040503040b0a171302 67
    0x41c1d15401a001000c0f0f52502040b0300251030341d42d03001070b0070300405842d855003901003075103000b500300d004601214484120580402c405070f07a0300c00684041d01d0301510905019920f1194420b000c01091034020a03031840c040e40c2590403846e40414007180806907c00b0000080703861400383da241060030391b4940301502000f052012000c64006030007002d42c0c56604900302500d80d07081723540202000c01c0c46540d0340d13408a1a404040101d040a03031841a080d000340044181507145000c44100b4105000c45011803620740341c5000703100300303c1d1314a890400404c0c2515582641c100d444001010795058809600341804a00e003504041c01c00412140245c480d2160145062182406460b00900100901c6440c111500d01080b441d0001d02000c0c0600c010080179807080c401000c1140e601800c1d0207403a81c41c096000e001a11100d40c40b01e800790b004403035020300f0b5849140c4203141d4802c640001e49030701404146001e00942045402202c2e01c9420500c00b070750350b07405407a1028030040b89806507200034410001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 718409073 1250 718407823 718407827
    0x20f0d0209061903050d02010f0605041407030e2a120610030f0302010b09070c03020d02071d1512060108011a18070c02060a02030d0b0d051e01020c06240102010e0706 73
    0x6610000c43d000081c030510b660b40c2c0c41e040e042511004810025035110085001200828420341c8040d04040300c0030010300c43d50780011807401000600f0301d07062666480d0b00554091041040204c0c4000900103100600c01d18150384071291001d45a2600807608441d030b00c0f001040100312140f080c00d9440c2550007507451620b5005186c0c8510f9425010355590f000c0e100303a1511074000c0a8458641525002d400d44203502d0001d242c0601c00b403a07501190000f10003400310f80140380500040c0300f804c1c80c4005940d126280741d500b0304092060b6507035214040080317040e0400404941d0038100c40c6408002c00c103d1104170340e010100b407a82f94190f540800e00240a8120b1a094800307941c201300c85103081d003034000140d800304095a009071464000359002052410303140381c0345e000e15038030404240c403060007202041d0344a964588082e242d4a460442d0b00040d102c00d0740095041c0c6500b8000072089509a0400c0d20351401001c08266178811001c40d440c2c9900300c1540140101507260302c10f0401000c80c1c910304081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 718410323 1250 718409073 718409089
    0x1c020105190e0d0c03020325050f0103110d05010314010b1003270b01080f01020408120703180914070e030607141b0606041b120c0921020f0d020906 65
    0x140000303204803070381c4002c07a0f030301e40f842d80070b43d01486040c00079607050035801010700d410f0f8003000c0011070320710303040c2e0350007020b0184540c00003240c00c19924003d920044000580c00b0f46225010420301350000719540c145501582c0041e030480b4021030b0b503000c82042421585003650030400c0b400740c107e040c4509249640d840b03940024201259666002403820100d0f10b181c080501110058540c4490301d070060043d020306000e0780c541010194000c51409142101d0140c640008d1400c01c08645008980817041c0b6008400050b010b1465403d06001d082e161502d400080000c0740c040203014500e940020b03071540c09140321008003400140144025a2001c00840e100103000d59003040d0b41505000004003004503101c80921040404003500082c50010180001c841580e4160101c003900e0385100f9103429000090610f00e004414008200800d0028054643c3c006690100c5c01090300740ca61012007001136409510b4840c0b085a0307210003403440c4401c20010b1154044065070104a07003010030b0403485d01c0b4030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 718411573 1250 718410323 718410367
    0x203090118050619030b0f0a1206020c0f030d0f0b01050304140f0d02071d13030305061c050a02090a0e1203040f0503040f0e0601021b040f0e0d05091c020105 69
    0x101079022651103a010030300c1038101d0200c2c09041d18901c0581c10030700782c250042030b0050f00152803400300c80c6041400502160304c98481c0c0c18245005c40c0c0001c0500030560129000c0720311050443ea80b850303031240519600c1d4840c042800c4114503010b5060042c40d920300456040010503528982180c940d0b0702c03641000304d116040e0745c1d446c0c802d40c0405e09c12030006002c0d0000d0008036170040c150b414a4030859600000b0182d03084604010104100258440d203100c40403c9650107107030014507590307180d003c5106a0841c0c1d141c01c1140c4021000c5004000000540c26062403083e070356001151103094440c000d0742c0c0071444060483d0040c098085900c12401c0141d9801406055100c0745010b0079100c83c1d0030f6900a0b00414110110144184108601025282c4d000103081c030041c007a08103414206041150907401d000c0c40f494175145000081a5036070042c0f40c9202440d01540e41300c00000d18050001c1c0c4c0466036003805011001e6901254500b205202d104480d0180c4a0a15107002c04800c4181c01c0902c003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 718412823 1250 718411573 718411607
    0x8070608060f011101061d2a0c1501030f1506030c120302030409050c0306011d030a0308070e040c21060f0312140a020105190903021c053c0a02030901 66
    0xb0508000c076024041d0070000c0455007402c00300004001c08481c3c010702c00030300745423420b160328a1308540d44180c0b000348250000c810304099140c40c0015916420642c111000760303c500780d00f00003c001d10042030414a01184580008412502c8094030001591031a02c4090720070000c40758100701014280c002c0079642403203032054a2625880743ea04008441095900c40340060740071040107035951300000b05690301400c0c3c88c0001022260f14ac00659951503000c0c00030100420320021565490017401b6291482d20010014447c40075002c000900d2450610740444481036040a0340701c038030a80c0c5c41650142e8501864110030341d800c540310130b4020341d442e0000300f08211019940410b506001c40c003900d17030340d8800e500104d09400d00100800f251032000d040d00c0141032800440700f0019800080c5640c0b1049042e140710800342e0412000d0794903001c0c800f0030620720002c41100c01c0d403465107440340e101c501440205c843d0070311142030b0548040340181084800541e10403c03000c60107601829880080c0340c0b002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 718414073 1250 718412823 718412837
    0xf073f0b0405150a080a0c0306021b01050702010504061a031002030c091804050111040e0f1f090506030d02030f1608090d06020711030c01050901121b021608070608060f01 75
    0x2000840c048030002c40b0082080945000c3c91506850140d81943c0206100001850301580eaa00e03841c140920a200c010310b2603500094012001100d14500c0c981183c4000003002145003050780a0301910342102c086400e07034948040c3e6255000e00042c41801824060001c00c04400d005250000a6001034646420908140181d15195480710083c09950302588c468164609191510310309440c00c4001000170210f05000c18080f400c07800340c400707903c09440700815605496106c0400714100d03000c0b8640f4942d00c601c80002c41c00541d0382e003140d8080c6d401502281c0c19043c1c0c0410490712806110b8064803106000c0000080803100c0620011125020b034200300d14019404001400c1403207282c0b811180f450300458441c0a0007080c410f80c00d440c000c107070040c0c160110503000003085441131341141810f002c0340e000d02e2400f0800680c401e0b0008041d110314040b0103855800d0295591842c61901c50301102010700200303180c030020401c0d00880d666900c4107070345c50700c8050070080a01c900340c440314100044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 718415323 1250 718414073 718414091
    0x3031805030303150639070e0112020d0204110d0b090a1a2710060e1203160314070309081603020a0b0913060603020a0905030606090a0203060d05060f073f 68
    0x10680c206d036003142c41c5000300403413150910002424003985910008840f036080c8010400310a40469640015604690080070011075100141c002c1200420400e03110101181110b0817440e107600050441004840e64110b998492810b00103403040700070301050701c3e020034041c52480c0c20110604191058426018044524500c02120721150115840c204000707071808100251a080200b480440034140c2d2541040d400300e0030302d1507076403140c2c4010783c0d411800400050249803040306201c3d007880e52460003c0d40c0d60000d00b4024080041d901400ba054000c0000710301008003250004000c49a0142c241a0b141c1d280c28401466500001005500030359045030320741c12040d851083c1c20141c4019103006841c0c040c200e2000b4070306c140940040707000794040700a05c0300f5542e58503a070760380c041c503211000740c0d580d9202e00128207045403881c0d00070054440e200c02d00004030015542c3d01e01c00d00316555190068070324002200400302404c1e02c0c018010300c04040790700d4009944420f046a03e900460085a0b0711320f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 718416573 1250 718415323 718415377
    0x5090c070b040303020301050f012309040608030d060608180a0609080906220603090b0114030f03030405060a050a0c05072d15110f03130c0f030318050303031506 71
    0x8411070b412800a503001005018a14101e1420303c0303011800c0ca0440310042013180362140f0742c540e08540500e06040070032840700907910b58002002030302c03441c400e41c1d03180caa01d0f041d244050710007030054601054821000880aa4005019401c0d8580241c005c044c1031800740c40b044000d00070501700340e4031030390100722004030b82e200c0000502030707180301061401070170100c42181c243e201c6403070b0084e0080501308003c160100b404045040d05582c08044031a110a801c0c1c8002840c183c4900c01c224003900001c0204414050041813031071140c08212428070460381da621401040314640c0c0a8000401c1080c4071000200300c1003182128039000540103000103c0c440e8804112071018020215452076220502c241070701d006004101c04014943c611500b050340101c130319070302c0f03010081c10300d080d0344e81c044006800c0c02940d80c1458014161615a441c940384c07603003001414810381d03844444200d4070340000028941000000c5a1040e10400584500150250b08001c0994008440302d00c01d1009412081382c011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 718417823 1250 718416573 718416593
    0x40b070c03020d12030507080603031e07050a1a060f1c020a090e010b030c060307090b0a0203120a051f032a030203010c05121f05090c160321051005090c07 68
    0xb80107000600e4100c01e444e100500742c40740141040f0400155205001440d1000404e40b8500110b8680c0386d040e800d4100151441030240b03e401400714890104c60005000803843c03140c3d04841d0a000740021991280309000c40400807000c00f60f0401c0c404201180b141c1e03a462001c4020b5480142002d10240c1e485034000182c5901c0c500e20700c92a50744405550b0300b4501085540152001a1082401c51030200c1010707195001501c00c0c0350843c0c000044040b26180b0038021a00d0120501c2c008402c5400c3c2400c807940141811100013a410200350007134071103918022240400c0b01d44c0100c014403c644482035400218002d0046100343d842040c001000582d42801080c0940c03200343ea40315100c0b00c2d001c400c001c000101400e42d810403844002054051100c1511000c03c1e40c0007507030003522607101d5031491840c074407458250711414281c00b0142c908259009000070507161380e5200681803041600b08450842e60b066410001d9003003000001c10241c108500308513884145080d4803401e00c142e6403a010040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 718419073 1250 718417823 718417849
    0x301230409141f06030b0a0c0512100302010905041a04151212031b020c040b0109030b0709060816120c020c031207230a110a08031605070e060303040b070c0302 70
    0x940220080f1000a0007060807a02c070342d10311140c03e00c452440d40c1c40349103200901400c24030010340c0320003891108500810444061040404030700d0b4880c40c18445a43c42040e0902080780003590201000859144c54083d00000da035819448800201c42403007084001d1014640b240c44020078000001584102c0f1288210000d000c3c0b800d0b50300800c2c4044c8020704403494500040c4004aa00d11900103683d400507400a4148003910000341400d000f0b0010386003c20300d071744002c200345409000c00200e90751081c080343c104e503855154000b803520350f40c0003400c00503c68014000010401e40418003220002d8000c000035610b5801030794208103481001c01e00f400c2c1070881101040300000350590402c541d1307203651550002d910001110746d0051554041c3c0f12041c2d544050490700040c4001d0203030b81d8603424a880102800720031240e60f0070380084600000030190205840318003407448009070030240d01c2c280718803908000b40614982810500810720315080508140c0d1b241c15010004001600c0349480850f40d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 718420323 1250 718419073 718419113
    0x50705010c0b0a05060f1809011d03180a09020c03180301020a0c1704091d0d020601030206040302300a0506060a0602030a0c03050904021b010c0903021f1707050304170301230409 78
    0xc4c2d00d0f0023080c081c251440c49144001414103a40000103c42e8040240d40c08000081111313915a01914000341c0010020340080510728800240b4850303604d000001040e0b110718425403c00c1a20b80c01003054200e0040507004404201c03c481c11000150a03800b003255088184c1031440c1c24552290401c404540441c0d076440d000f881d80074082400400101f0070000144441d1009021960450b80481c003e402113100c028000c01041510782070300c5400461940d2001901c10012103004500083c590ba10003144409490038005e060100d445401c21900390410765040d42c00442c07802a440340212140340000106030308101041c410003505a54500092100306100083c0c0489501e407040070908540084610174240070000c1420401038503001800020782c0450340107122045501901500c030b405414a4610341d0085080c100301e012500035002e0340c0500c0c01224128940018222985a50b100031b00030800035840003c40c3c0c4158030702051a00c42c0c0080050008296440244d0712400f0310311403c200c0e454 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 718421573 1250 718420323 718420369
    0x510090f0b09120a050109151e020901031b1d030a0b0610050c251512200d1506020f100f090f1a100f1703040f08010207050705010c0b0a05060f 63
    0x1d01c030110701c0d80401c0d42e000c0e90080040e109e82c030420000240701082151a150703004103076800720741c1c0641d100320905807102450180145c8038800043c104118039940317406414809184d061a801d0011754403441c10761041590f0b150b5102c0760100309404101020000c01c002c0c2c20040381745100b1043c00400006290021074808022503210b040c0c4417030409422817000b03007400049604280b5800118000e14600d020400140b200942c010742c80402c4c00d8100c1c170070f2202270001c0d803104400300341c1e80011542e00c820240202241d80b11001240c071125068000302c0c907a0f20025045010620340d601428a100d8000d50000f20a003032a0f41d060440f25001c0c40c142d0b515404045040d41d00b0000c0c1d6002c1c1e0340200c1900074441c410741400f01114403100103025541d201001546688464101041110054120300048a031401c1c0e5510b2018041d40c0720700012941801608400215135024000c601102644808014a81c3d0f450001000082000034205680704040c06d40c5480305446440181407081c8a08803c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 718422823 1250 718421573 718421591
    0x2090118090816030228021003110f1c02040315050c0409090b100e01050d03030905030408010e031b03040501080c0702011202192d140c1005010510090f0b09120a0501 73
    0x40d0600d8403203643c42604070640071405c0a10304241b8039541b041c0b581111300b00c003107001065007140240f90280c0000c00102c00051a402200b014002505101e0451280c14101d1140d2030b0001c020390007144001009111500400c2080442c1500066400030f00c00084c6130400341d4079002c1400340c802c618070644074031646006001c0c109122003182005072580d0403565010b54900b2000c1440c44481c01d0000c1c04140c1c1d5440d103401045000d00483d030040a8110081c40001c100052844e225404000c45655503403aa0090300e009007004004e0b602241c80c1619402070a82d1146400405031b88103c10890400c03030030f50b803003005203250b51000d004202100c803107400d5810b00b00705003d4400c500900c1da15074108074135400c0e550500030b84d1a0000080e10300b450b00d112044106d801d44845402101c000f00082c3c081c0344075242e60f000065100504031601261141130003100010140c604081d1030003034540d690359280c028072500900c1e2008040010000c0c205038885c0c1d1560b1005824918011011180d5035107501d041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 718424073 1250 718422823 718422827
    0xf04060e01080f0f13021807020304180506010c150f0c030b030d090b0a0e0d0c0b07030e1f110c0d050f01110a0c0b13020d11090c070209011809081603 66
    0x140b5840701c842480c9071404d00300f141009440c408018660302034024100010021921905072085034800600d800350198108500040d4903500240103040140b041105480c0580e212402018050b40068403241c10b03031012520780c3d02d103003030111440c00525611030050381070300c2c4454410340b0040140ca81c0d0000e46141441d040504002000e8103101c2003021120040c0030001e11001283c3e00750000d1b042c1a1400c2500c907011689035240c1c0200038001207007164000840c0703105400180005131003540d440000c039803c20200a21f40030002e41001c21001090132008030140034410003a0b22100c510b0454900c2e04c8107030b00140c0c0c4e600e0b6825040f230310340c0c0242080c9401a0424002d46403034003d5203e25030304010312440c00401c1c000002a0161036610000040707100620200100a851034004c1e00060398010329050070741c50b044000044078040c5000800281207400c00c80c1c1a14400b91f801001d0031410b91920201d450001c1e404014108040d030b64424a00c00143c445008217401c00a9404904003010f0600b80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 718425323 1250 718424073 718424087
    0x8340903120e1309080904180803150a050a210816030c020301060509040308132103141f1a0f040611010501050108130308042a052d010809030f04060e01 67
    0x1100120740d05044240c0009030081c0c2c10350b1b920540581c0d0000301044404440c074580c140082015016000000502034414080e100707452403120241c4a10016a0303039501403142d00c80040c40341c2080f000c840d54420782103030460705c8810a410300075090fa904041010200d604201e0154408602143c500f04110046003000c3c040e140042000b25054401071134a030324041c20210000745000c90500b04883c44600700070b043d2410b03560741c204940c036035600903405100250041580700d082044486600002400180c140d00054030032140800005903114904080600a000b04000080c0c80210910117143c420100d07102030b00c024420b0340d42c1c030f0b40004d44807a10f00c1d00315501a008141003100950402500d41054150b140c250740d414506518655075504001200d06100904400d0140c066004000d1300c03a110030740d29080c0ca030100e81e940c0d070b0302a4400941207808581e0107084c0004040c44140d003031641c06154010f52203191032044e0f910302811500d00c40d001c0c0d802a00f01c180810700350402d445d51940e00c042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 718426573 1250 718425323 718425349
    0x8030913020a1e09081504020405091f0c09030f0506070915020304050d11040504080a090b03090a03080606071b0e07020316120c020405011508340903120e 68
    0x4114505030318180300038022080a0034072441c3c0f4418142070a9024480e040107030003068900165050b0344180025410036000907a4140d218905000204070007000125500307101ca103080140d2208564215280e00161501040d450140018660300001049194407504115441200507091924103170f8400380c05001c03680c05c0740c46401400c00800400c50340003c100c0d400e81d802200c140d10302c10b40d545000c01816081440f82900241001e0034041040048800b6221100c840d46803d01190f464001d009880c2c0011140c0c514581c0c40300d240203000c207001700e0a541e0414400752000d45000349645070448400404c0052982c81084d032042002401c420542594001c080e0344040c526000c075032007030400c00c000b019002030441a1000c501e50781460213405040700040d0701400501c19076035100f01130000b10114200003800301e111540010850081380c664070007000f92104540f030242240c418248128039081800c00240800c16101102064610030000b102c801c03296190483c00b11113909110410b20420 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 718427823 1250 718426573 718426609
    0x50114040501080a170f0408101d241003021c0614190b03100c080a0c0513090b0103090618020315070207090e10050415050609040206071b030606080309 67
    0x103500001542c02001c1045050145811034591b0300c03190140301c080c410303640908050300c199082d03445100c2042d042a020300304403600401f02c1c904017501c00c1d45c54841c40c8028134030f1030803005440400d0580140096401c448215000b2507207075103e6001c1200700448110380902da0b00c24050038002c0011601890540c980002c0380c03003005061556001210741101e44000e045943c640031080500d8508111200e03402c5a58402400032544440016140c000c0c15220410300178100600c080e00c550148e4211803030250003a050381c00c1103140c08501c4008202c800e90240c101510303a5440310229145018058500420b0801c000b0350072000d20402d89041d410382c2201900344402e1013003001e03503078012805504803516a600440c0d0348056511f040c0c01c00d120007040e140130350b180409000504c440004032442209901504000f00d4441004020b480c41d001c0b500298001f004000369800a5503000268031000448071000565940300c0c3e8400302030312400d0f00300a8459202203a000d00301d00c0c044100c84103001c0c0c41c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 718429073 1250 718427823 718427833
    0x2133314030402040902180a0e01050f0408041a090a0320011707141b1c0c0203071505120c0306100c170307140c01020a090819200405011404050108 65
    0xc402540140001031010703120325541c8000e0030030754407500000280101140302804091a0120140d001401c0b280151a00d543c40d245c005614031107000102c9000d141c10100882c1802e14110809030060103000700c410041d00140b1070070300039481d4102c0705406540720f540705201141010104103108140142c24a04100320044c1460540301d031000700f1600182c0b1841c01920800c6462a028158800c03089031010500c1400c0b6581c04c0b18101141c00380712041601140d1030559440300d03007203402d84101d002c041c0d40754110030800c010708a200c0384140c405c5622424242d042207a800b9824801b41411039001000507c008108030701440d08802c4060380c0d880c90b0800c0c05014505d915202100001010ac0c00c244400000206800354003424040c08840078104410359039120454049002c0d4204801c0c0c9004141d081d10040f0b032a43c00403400d00c000114a5040c40620f4065031213156070142c1d00b10104256684400046000c0c0e19203020341400707002c0345c0740034180c0030309584140070031640140d011000d580c1103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 718430323 1250 718429073 718429097
    0xb0d0b01030917030601020f1b030f0d02060c0d060b0a0c02011b05150618010f08070b18091807030c0f120b0712020909012403061404021333 62
    0x7120000b100f001c0f0308480d80c0780c2d80d506005070b1130010107190031001482070485402e101600c2182d1000e40500560541e41ca0700010182e2680e0b03107c0c0311903640050f0700103e000032220004080609004e00d01e109000c5080784d80c6000b010080c3d403260320b51100141284560005558002a8000406001001041c0350801a4031038607160901030f0380c00f040803a444008580640c0e81c10740203090101d551400080907513515012030001c50020710946681e4041c942000840318200d90507a03103500182040590207400380700030440c00c0d070401842190701c2c03014000ba110140008100b060003861003407659014403801d0110119a074001644100c00d80c2d0001ca01d00c4000401444816401c44000d04081c0c00010045a400010740a69400c1c08d0304400000c00001d8a1185024409101f03303044010500d45160702c10120140e9000b8007800303400c0751170602000c0184c242a8000d0410010380342e4002e420a450301c1740903000500081c0103115255800c4100c03112544000a124401c203172504180342940781c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 718431573 1250 718430323 718430333
    0x114101404090501021e0d0e1c451e0b0310120303050a05060f01140702270711190206030a020d0603081c0b0a030204021e040b0d0b010309 61
    0x18a0504a0040e6102c103804410800c094050341c80440300000d0f01c101c0d800400d5586031294000150713040046042040309a50040b0104150001d084442c4005450200304d00c02038030f605010140c4410401049900c42414001945641d849518180e0980380f085285550361400544107800032800301001d100c00d108062011000402200e88211a054407036881300d04031580d411095001c10406010031410b01f00b01681a4410761141c8694002040240c03210300510980c0c02c1c9841d902d07800300380401c0c1e881d4401508200544551803009281112518400e203646800c0c05040e01c01d0081c041060040c015542e800030440c51014924400901035001c610380d151203010484813029004000c0007000c0340c109402901210311045010006122203a40c0740303054801603029545100d03886290121141c620751060241c1920300d00003d102484960468081200079400002d81c0c0814040c005c009018480c18180500010300903000b9864807101401c28034010b6428900e25181050301d01513070f03480014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 718432823 1250 718431573 718431599
    0x71b060f09051f120606020102120f1302090a1d010501050a0b1c0902041d0c0120150907170705010306240e0a0906030605041b0302060712090f0602011410 68
    0x1480000808041071000d00c3c1680e41d00340d201c02111510303040034030100b02550150001c107103440350444001c2041d1f07115110300788410026600c05407181401045103001d07142000c420341c0c00c0860154001800c400e180e20399024464900c00340001c2d651140c004100f280360400703040000b0421507002a02c5d1207071701d0074031480c2500c000100d6043d00e5600d081240a40d01d6650019030f400c01c0d84481d030080f810035403042944d1a60b400c0c2c400340c0050046680010040011004102c0d40c0000b02d0087c100c00640740c10300310041c240106013040720310444000040601031070036805480170711000600107641c10f010004042e10800c2d04038807070b030300103100d0501b5a1600f188840300c200da9881c0f90040a01c10b00d80e00282402c030705680072504960402038007105000b51580710718003c911030804440b208011400d4a41081224800a548443c05005040200e110809450310b079458620b404101c040d206c2c0c003104400f110310b81016005039074502000640d1b101c2100020780010a040560048619200f5815440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 718434073 1250 718432823 718432849
    0x705031507050d200a021c050f07030309020607062a020d08070f020106091e0b0d0203120304080904050a05150108040803010603113a0b06030a05060303071b060f0905 73
    0x1a9520344203821180002c0c44040d0604d121031030030640c0c8070500600259545032000c1c02c007401d0480084c41d00c00c0e16000d03100b110840302d001450b03242000c0c01c03514150020720814005a0b000401008001d00260170380c403448041c40c0304080c01c0b411040340c1c4c801e0204051440e01110040d5445040c805ca041c9420500c82076014040f07140c107812044c40d11900300d02410345030748007507100d50400c00514940304440d0903201d00d0000208040144080309000c10402d590f070300b900650945c00113040411840c01d18402190f009000750500c4c2e02d009850b1001c20210b40301100c0b050803031641c0b90180072925004e80d04128090740246001754007801c05881d022042c1c40180b20b4481031590b20b074032860404e52000161440036135100c030101c2c6504054034080b64a2240d0404001003100c20b0418580d04d01040e1150b90b003004c0014105506580d52004054000d00340504400c0e0305100c10300a80c400a4204d80d410802d00c5000441e020400e85006000f070140d02c810508a014018403901c240401e03261512072001c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 718435323 1250 718434073 718434097
    0x203010914070f0f0909050f1c0f2307170705030a030f05060916110106030b0f0106050f032202030d09050f0f090429040606030b070903150b03031605070503150705 72
    0x340c11018074100746407100801c010111400360040c110b002000c19208502242d100340c0301c140c10907034108c0f012526001400600002c0c48102f07180c14000c1c00d44c1c0c42c09450762502c00c4501a68402c2c5011040780c050300031042c00c69951b4000107840b5140703603042c081c1401508041d4000e0106023011800542e980030020014014030494011a000c1c03144500288800e801d030100c020817100e501d904140c244480100c401d405204c51040002450f14494404c0b01c0701205200d0fa02415500c0b404103003410000003843e1000f84002014800015a40501c984680c881080d143c54444070318007014000f105450810080c8114008601210b4540381c4d40b003c203038080d0380a4402c4011801351194010300038000112202110010380820041002c1350340128241c0e4042e210355115559805c01c02c540d0103c403408010091003018292019811701038001d50300080c030040035030b4180304068641a1215203041d074203075401c2d0310001e4200843c1c101840704903081c0d660100d100c900c40ca050440901148628410001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 718436573 1250 718435323 718435331
    0x9040903050f040803031503060412140409060b0d0c0f020c15070f0807030318081b0c090703091a062805060a090302011704030f18030203010914070f0f09 68
    0x81003500c60001c4400d50300040c1001612642c56030102030f500d81080700c070b040c070489002c001c0c200d8615000034424032950f0f00900706120321079400c0702207403008042101c04460150030b02000c2085031042c01070303001500700384103e00e407030f5030307480441c5415988518070b8081400113400c110300311aa400b03e643d440600307040ea07101d40c1412421924800c944520180602a411202c1c490001c1088800044c21014020f503014401102c8000c031584103100c04000c0244280020000014104444c503964a00030510f007040d104852003040200d072550308201c1c2d0030781c0065a0780081c8020450300c207480e00c4501d1403400038032050f03251820208150300c00906128011915a100e5134800400320010800640780150035103441f81c8441c1c030b01801800c42808101c1c041000b4000c403181d44807030030012a01c140e8041e42c0c0c07441d008080d1007096680f1000e919090107039aa07040d6001c00035031000d00030161000c0c03060581d001c0d0f5690300e001c55410014150422030300c00043c0d90b010411902e03085481000c2c0c0704c41820000b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 718437823 1250 718436573 718436591
    0x19030509060901140a030207150e0a0201030f02120906100f21080d060b0310080a0b04031d091311030a081e040306151403030708120711030301080715140904 69
    0x21310744459802a00410140010b01c0405c41a8943c010305001885185000d0b40302114a18510a541c4480030000d1240e002000c03410156110ba00300105410043c2d01c0140b0306406107401c1e07a04200f04482c0d48000d94400707414400031852181d4941e009084140d6107000301c505140c003c4007025944070305007861482403401001404101c0f0b048070b00c03a01500500300807844d41c030804001d01d60070440d94810410402080003818400101e040c00c0f041e44e110f45d2100d02075483d0764042d1800c40205030015402d804120b0710b0740150f11500c00d103600170310343c410803625041607910300b52400b104240c5209000350041d40048000608420546030780c000a151891060120945807040a0040b940007400c0541450307804072408410b04118000e0303a882c46100380740e200d221424513a8921959400030050301c1c00700011f00703e0740814003209421034034038601500f4003900720140501d150003e800040d026042940c0c100f191120110102c040c0d0081800e1220010b0408480c03001c250298580d007900031a141c2c1005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 718439073 1250 718437823 718437827
    0x9030807140615010201060e010602030904050c0d0617010b1c080a141801030608070f1404093008040b04060507020a060f0e011d0c061e0d05040519030509060901 71
    0x14040400716503080320031915103966a00b141030140c0415074090352909501048601030803410740c2c165149600214500302c03014080c44020100103140d030000041c1481681548a22401400001c012007429190740682010095085031521100320b8400c020300c0c0060300f004201c80d5003103a603003504034190540ba4071141c0c03c2036640400b170340c1000c1081480080c00c1c154040305000e00040c0c1f04420b0360100f18903074032140c1b10344e03444849004001c107000c00040101f2203201032440079507840c0b40150011a007804103543d5543c0d603420000090030400c4018080c0b08002c60268049003a40307050380362040c240c0c1020b4271340016a0001400144c021074132400000d031454020482c0072515a41305104100ca0350140c4180f000410640400c400194280740221001e4941d07032885001c075082c950017400030300b15000c04000795076000300640c107020b664414004180c0d055140c040d0800319100c800c04a881d203058a0883d0030842d4440c441481e04040492030808268800b0070780b1003000d000e8034407560ba10004001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 718440323 1250 718439073 718439093
    0x61e0f04081c300f14040602070210020111090607030309050d02100c05180f0102100e01091106070c15090302030604060e0115060c0b0601141902100b0109030807 71
    0xc0e402d2103007062152154108103aa600a501203654060601021100401c40d2420858076140c44943d40c0905450f0006994040d81400010240000380d00100007000a54154100ca0988450303038080342c1c2405605041000300c1000d038061008004150000c0c1030105180240c207113042c0184070101d0140b0800d406070380001da280d42c11008a8044054001d4025514552044040da500d401c01011840c054058008e880030701505807040104860100d00340082e040307001d00103034110b100d10498815412540d1103001a60741d0381c2c100114401c41c00c1c5c102804c071194100c103100d000d900200220000b15022406a07816188908a0601da0f00740c068021103000f0701d10307040654503005443c1171008000383e80d403154201c914010001e2265140186000d1800402807195070007060344240e142e800601120b110030361141c1d05040500c8001400c031f1301007a56410908654104040462a1001c0c5c40d40401018140c43c0050f9400d2003800c032800700082c01d0244511006200c558081703004d404102480c21 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 718441573 1250 718440323 718440329
    0x19020f03271e031e0c060a0302040e0925121403042c010506070b0a0b0307030c080c0301050124080a090b070f090609030809091e0123061e0f04 63
    0xc90101080e2545000035203001c1ca141e94402d00c5001301ca12801d0300415030303100c1510f40100c0904440044030b81406040d41c0560340e1070080503402c1201082605d403200680e4001e03401c40c030051031040c12114590000707043c1446070701c45030a44ca0b1001c20441203105041a12184e21002c030007103000c12100540c0c41d6014a030043d104040060700440c840501040003c1e041c0210107281049503642c64040c88414883c10102800f0200342d500081d80c01d03170b195000000c20860113022070303d00c03d03980c2e25610031480c402d0304020041d40081030340007e90b103002d010301405041c2c1c81011402000c51403d04034800380c1880f483d0018402d1810000d880111554003500c00142c110040c003100d072a084000400e060038800381c42c1c020074145140480c4d5a4403921034842503e034401211443c0c001136800b0040c5014004200781d4221075494041410300c043c82c90a40d00a007907040002c000c100404080c190300741402c0324214010441030101c0428070720588140841c0e900d0500b0525a950503100249a152180d90 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 718442823 1250 718441573 718441579
    0x9060313210c0510050c0f0304030e060d0f0e061513020904240e09060f0408190201020405012604020f0604090e0703031e021c0908100219020f0327 65
    0x40050070350580c00c030001500c110321900c140d4241d11954004042241c00035159040461000c1c40b540e215260382034019a0031a00905082c9020b200410002c1c60560024001c00a21a11180b10100ca90f10314002c0c03180526846020b030010303180c0f4046122072440e86c65480c502c52103064400e0960030040d82d0440d007078a58041c000f4072059426400c000001c03200f0b07500d503254024540ca0001115130701000d5540c050018500541882e40350f0601201c40010080c200b913807225400c0200b00380c02801380c150001da01c0090b4001607107491070400090f04521058807240145240000e601000b40e044903591540164100c8194020f552100c000c04c0660140740c1000e11402c1c40d080500c40c0d000000219102200e10a42c0c54501603aa498a03d040c1c1c2c011120001c40943d00c0410400d640380d0300c2c0105004007480c2440c010300501d550340f640f075281034061640d11504581c00103e01c0440d4000150b010458022400185411011084155a40e209104801c0c000356401c03034004d4280c103000030001488070002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 718444073 1250 718442823 718442873
    0x5060c1e030108010c0905060f16110d0309090614150c0a020d06060312050f16020f030717070b0406020613020d080304061508011e05130b071205070509060313 70
    0x21120359000b42103485d4200041940454001100e00e4408101c0e05d4000d10340c5009401d0800c0513040b00d103504240b0000300c41050500e2415a215101c1d800505680c0740241c1c0c4007107c0c94540402101102c070260803005038444020004085c42e101c01c0290394420380c0b030031110390381c0340180151b060525224640c001c6d80041c10a80d20810f120321504001c040da03008174065100c1030340304042950a44140b003483c1d900c58206004907c8240c50b1025201c040d00e0000d000380819110600009041070b0481e000300c50705501c031045120024800f0092a0044c00c05800c8851a00e81803100107551010001c4c082d1404440c0e170100801151601d10500080c9030b07108116a4580c02c091074030001410440081c03040525101e00300141002c4140255007505c543c3d050500792240411402c40064280103002504540020543d4400514042505807044c642503807540d900c0e840448947e0141c0c1c0c1b005e0545030070058180410700d4282d0311441180e4100348030480300002c400d41440c0160301c800070b8070505000e080e0701d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 718445323 1250 718444073 718444079
    0xe040207061e060803251a040516150819050c070c050f03150c04030f080a0806040911130b0a03030201023016030e060702010203010807081501030b1b03090307031b05060c1e0301 78
    0x103021f503c180100d1040f01510005590054886101030903440ba0b561100340120368041894000c2c200c00350002c00e04101c0892812400f40304205660b02031783d056201c2c0300006804424408440d14580141c86d040713801058009281c00001d80c0e969107003c1d640080c0b0100f50114070790a240038122001181d000d41c0d420307800803403820940c4454111503e241d01068102d13001850074034062092011103940310840c117480d808420f0a1000c842030004040010b20382d62a035200240d03403146c2c3e072000107601c640d00141e9100c4c044447d89544004869001e900c088003550503031001071000758210b500404140c0d03e0700c01007615500880c090480106081d800d80203003014840829410340066041e43d0f80401200c4030b040e510071160341d50710800602a0389a005202c010b0000800509903903030031920710350400b210340b00d101a10030241e84c002d450041e007590001517030004050b000130140d00904155002c0940000c4551135594032014028a0a21000b10000e5000494007003407460b1048180c00015558403903031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 718446573 1250 718445323 718445363
    0xe04110907020708012906090a140f06040e0703060b030f0f150621010b0708041202011806030504170306090721091a01080d120902010e040207061e06080325 69
    0x3207040c01110000c00c0d4164441b04500701101100c403210005880118428a41040c0303881c070001181c1c2440c0d200c0305541c8400c06e15643c1d00c01800c0500103001c1000e1403400c000c00b01500300c03681544030b00401002402080584404c04072040c5d0302130041044180e80d03503a0001700280448221002d6940072001042030403400034441100140c2d07500d608046030059880b102009854083c0a03402401000101700034403040402940030440a44107040004c41c10080341c03080c0c1e110ba489900480b00181d40c070810481444500981442c11441d1a40e90300c1c40c1d41010340c0420050040104100c050011804620a01012090095008818640003000303c40c4041c5407407540030710300e0900f0402c071000010000c01e0080011642c1484200b99882300b80e80d810981e440c0c40007402040f082039040c412952a61845031329140000c01c42280f00701c50002d143c00be80c140801c003d00310b10100c3d40c1c0702031a1450610040000000310380040c1d2840c111890104050b400404e04e800701008000c241d84c1004071081c0740c00e9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 718447823 1250 718446573 718446611
    0x50406050c101410061b020f1f0f020c0d0309060f11010e0f011a010c0b0405071a0307120c051b010605030f030309060f06100f12091401060e0411090702070801 70
    0x255600c081354a1107581d500007214140c0d03c0e08001c0c0040701110266000602d0b00050308600c0350005003103000240603e1200d400e10004200751900800c070358001840005506100c41014462f04813403250155089440040076a6a54000c5009000600b403003845410700460207511030490380c5000f405152250f049031510788800000382c881c55820550980103d0342300044946841c0d0060352004081007598480340d4001c8405401501e0b503001d511130224000f6030703005414841080c610501d507564182024014240c1080c1000300250710301d0a220380c0b003425400b000b214460101107a2408890701450f05450041201c1c1e03002c907a2600c50282c01c0000108044051486401c1c038100303a8401c0c0e500e98002181d003800c100c40c0c0c1980034000901c502440c5020707046921255000c1e2a000400590207041300c0c0480d0029101540c4000d607009162000324000d000e902c001c0c0c01c0c8041046918241a92664041034001d2000d900c00c2454500082942d031082110400518450009000501c5412921484c4e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 718449073 1250 718447823 718447831
    0x6030f0106170d03090f060518010f06150503190b0f04050406060501030b0307031101080717090c090a0b060f07050f1b1305010b0304060e0c121609060303050406050c1014 75
    0xa070040301c40c410070f802d0281c4945503a85400c240455007240c401c0d0b60b800700074240101103c60300007000340c038000b040400344100d00b1a01c032995400240c285c1800c1c0ea82056201811442d41005005c208204810000c000e2942d203400c4503c4001c202100e5610014406180501515030042e01d442e0407c07080c0130854000a0480fa02030700c040018115102c241500d6803800d00011700414440c010b54a00c81d48075006d040e5002c00c05141000380e900e1803e103564511902a907150740c8a51224500c20302503d05501c50981002050004120108121000c034905000d50101c00d9105c4501050100074000c2c00e00c04c1d203006103000020350701d100da90b41e540307031404042c02c00d010380c0510074140c18030031000d98030310845040e00c86a049241c01c5548641d900b0000e8801d2000303d06840c003c0284641054540380000074801340900060494081c0400c0d500d00d41240c1d40e8069640c0f00c0c1003e07010804660058212030603101c1d249800360f9182c0f1505540b0789040f0b98030301450102c610b04000207401e074071001c00076805 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 718450323 1250 718449073 718449119
    0x1050405060d1a0114040b090f090117060a1815060e0f07020c0409110918120706050a0b0f060a09050a14090618060d0510090803100b0703140306030f0106 68
    0x101c004098011100500b50f802e05d22100c0e0350070070060050000100c09030203500c0d0003e2207a0200c4107980b011070200d200a900200055503052104000003c082c000c03103600c1a0b00e290100182c440c120382c003c1d01c80d00c0c40c4101604c480011003901ca00d03080300742c1000303001d44080c181c0d601e0035081003842105a0801120703480018090b510860505203802d0054016154104070310b00301221515082161200018001c480d801515042d02505000148804503055540d8400b2070340780c0034035007408030607603a009001110b05031a14402c000181e80d15500d50040c2c1805884541d10b50040d00410348120225420082d88007891240004a841000d91f034060500310685858040c0e40302e0906006440602c0341c42d10700007125400010300d460a0042c80e50b00500c0c091012508020f4081541070102c40e2a5041620400030010030007400d441d4070b0a419000f042c070826028035201c89031314001e040c0c81c030840380c00c211703444e00001080159a0402400d074291520900070001d041d5242c000c080d0100000083e420303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 718451573 1250 718450323 718450361
    0x180f0613050310020a0e060a0e04052d040f11130509030a030c02062710050f0108060c0f030703051803030f0103031407390b0307030b120a0f0201050405060d 69
    0x1003000041c000e60b0700c142d180703455a01d1b030310042c0070800085070405042c101c200003182d8404000c50792a402014010002006441281d200b5a0a44c0d001e1b419000d0030383c8400c0e0710301c1c030900002442c0d00348a0300400e500103215159140e51503001401d007180c07440e0043c84140c200000e021203a04080005d1002234032a407400c214200b0080340a9840341803c847d0300c0315840c00c0c01140c50740c0003071144150a04900450a98509034100b03048101101c0041e41c2d0031a001007404014002000d082040d10b41058800c5081800d00f90f503080302044a01c4018188001c150311a4045540c03410003800103c400f0380c00c6d000b41c1c0c0c1c49103440000300600907800d100540000d01400904071500c0c1100080390344582d0001080e015030501409260380c0d00c3c03149881c100d403000202d9400c0e070b004202045030202502e048908950340782415440201661100018584103004601c51843e90350310019941c2041944461103c2e03c0030518001a1400e004a07032100740c020380c1c001f99543e488207813075028100c60300c10b00064507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 718452823 1250 718451573 718451593
    0xd2102030d14011409070203130803090a05030729041206090201230409052e09060609060818010f0e0304170601031211010e010204030609050d080c180f06130503 71
    0x10003902c003803042442d014092840c031441030803d04592644940c050040789e16200d0b1428100b41080c0380e5510000464102086443c0c5900c1c202c0601c000902d001c030300419050381802d290080d84918074403181003c0708000001d40200d0203c1c1c042e0b400806241c003603020301015904005001c2d100501c0d0407800102601002d04074100300f040b210340140a52040715042c07500b4000040001c14000d080e07600c5000300c80b05001c03101542407031500741d5603002201c42c0d2002c500c0c000340882030320340300d4218405001b2512420321030316a1000352540d003d181007500c440e00e4007441c84081c1c01058100b03d080c150a04003062507101e124004000c200f01c807a92080b030101c20784500c0c1e80c0c0f5291802808028404000c40540c98445481449820344103848080002021841040350f0b0f0b00726030081c0d0003119081c1e101d0b282a018414180b0140c00158014105002c0d240340808011543e442450b0045541c1443d018440200d6220314500c840242c0000d007200341da4900040c074501401041e445424400c0c89280c00308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 718454073 1250 718452823 718452851
    0x3222a14030a050d031a030d09050102071d0a0207030c020a03060615080610030b03330c09030705041512080d11070c030308070e04051501080601020304060e0d2102030d 74
    0x1c1840503004005030440e601e0184c2c040300a07050450301c5060041000c00e1401d1141d8042c481130b40b80c1d00c600c0d00c854403064680030019042c100c0a6010360b2211f25414580d2600074a044107690f0b00c22072042c401a6110f0003032505507040520780c032001c1e4203d00801c5004c4200714865002c102503500c0300303011072050f103a00300080b84e2000b421140d103604617a0000074000b41500039009401b101c00001d09488108050610040200a003d0311080302250754070720f420426464016000e400100303a000086c6004581004aa078540c0184152030040d50358407600c04500c051000f800c4080c00c1400002c41c0402e404c1e04180c03006400c000000f12046103465601c0072008a15401c03600c0c03995121200c641c0883c5944c9017501d800100070300e2082131045128205003560b81c1d9126051055441100800d500d003a000001840c000300200414107542c0108014890150031011200190100b1540940c41c0005807400d8010580340560100340e181c2d5041000310650340101c0030b000031411100f07007002030b51040c07501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 718455323 1250 718454073 718454083
    0x109061502070302041a10030203060118050303030412200a06050105060a1407020105040b0712021519110f0403050d030b090103020d031101142a03222a1403 69
    0x140401681c082c1400704014202504071000c0c50320204401e0b2904803464000c02d0720101c2c143c030503100180c0d0010400c041076810440c1e00c81c2d4100c0c46103200c0c603014102404640d0341d11000c0c001400942c400c01b8440020340c8500d0200d039050300d0b281101082a4800340344940d4403c2082c004407400c41c1000300218550a01c9070940e006007145580f407031010031880c4034080b5a07501501e030a904009003003001003086001c02004105044c8a600070a80e100035544000781801d0100e040f03c00710380420700522440c071034140881058500c5121000801a00c0046541118414000404005100803c0000a000d00405c0000603001c658a003406002c4140e03080080520003408000d501400074940c21001c00e201d800803c0c0031203280320001500c61405030100074401401ca80c804558a10b1b8071075003041c90907050a889401400d4240a415428420460540b041d00140c01580c0722180380c400744140054240d184428100081124003041a81249546100c0e103e0007040000690700103c44010300340028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 718456573 1250 718455323 718455359
    0x15040608030a090e1003230604150f0605060307030c020a1e0b070c0521071704090c051207111501080114070f0c082a1b0d17210a05010906 61
    0x107282c0038060940d520b0a03c40d1147d00c8502c5440c03011000516800302c4e040000c0c41c000d5000c0c0c030904005080040342c1e501038036146088041c0031400d100d810090340e00c0d89426250086101c2c200450034032004402286800c0400e04003500440154082c00c2001040c3e4a40400c158042c030180e8055903502030060b00d02025100780100f10303522950000898260301303180c9180c400503240c000382c0b0f032000301c0c0c903404400690144030740564080041c0402243d101403050401441650030200e080c0407826100002c100360003000d02c8140101000c00041c003441c284011940d85842c070020181d81e5845080d0f80d03009101560110035140e010b00d02181072240607011600450103190386564014006564480494110a41104036884100c04101901000d03404ea1030b50020b1610040c26111013840504000761480f03a6054020300c030406d10301d00810b0880180c2904d5181205210707039581d18081141407000c00d44000d90100b00101b40c203001150f020b58100c6812a1401e08003408026220317a01d080c070140c0000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 718457823 1250 718456573 718456591
    0x60a0503061b07031403190c0903030804120309020319060c090b0d0c021c02012310060c020f0a140315070509150c0307030c0b09030405060d0515040608030a090e 71
    0x1c0002e410580401c1d00411050384246000c0044004d04030204103690030503128143d4000100036110b0864106120350240310043e0b1a001001e686140c41c0036145000160000d44100c03100400c1d100058040d4225400c426800740840b160070150020507000d04c1c09a003c01c4446a050081c0000100d10422508007039800e81038180f481d1000f1001004018420fa400481c01d43c00350b0fa4000c0f03502424607601402c14003141e00080707040241840c1d104c0b44110340305030f08421000751b00140529103140021400039122030703040c000311525240c00011a111900c2c44a60342c8500c0038600032420080e45075000c010040141d003100d1030b400c103800300349120703150451700d030000140180100e428a18101c444405e1405802842c0c078540b008234009141103038060001503020400f07200b00e227070070400b5200c1095444109503014604007070030000002c6944c45002141d648850b00c8802107415520984400c001084004204100d0f40d0703034520795a6141d070030640c107903030114034412000101c4070401845244260138503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 718459073 1250 718457823 718457851
    0x41104050c0a1107150909050c030c0a080912031602060a0504030509190503011b09230904060209101d011806051309020a0c1518060230060a050306 65
    0x44003101d0101d0690a11070303c52103681d800140c0464042d608018010641d612003451504019800c002c0c0e846c041c108183c03001d8100200000c680019040c0e40450b1954035003100341e5169104018038010010300f100e00d034030382c0000034091100b4800c803e400302c805103502500c003556941c040343c20498004072000b9010030000c204145045c07506005001300741c12040040c0e661181c072440804c1c211190342a00c0841d40740c0b41c003401400507400c40d0b2114000c20140800010070081c403030450707141c9005151024000c00c18003021034204003441d01541c10380c500c01743c0769608603445110000d002c0d2584d0305241e100c120310b0032043d002d0380d40326210442c500700b091001c030860549882c0084885a002404105075500301d030302c000c10300554900042080d04120754038060500001e00384404210840301c0c88204152034201c02602030892808807008460304120300580702c01c1c4c010101d180071403282d07a0040000c1c21f2078040e00ca19506100c040c50080c04141c440d410303c180c441d0107060b07540380141c0b2051100d01c1c207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 718460323 1250 718459073 718459087
    0x5100b180f01210b03150c1b0f100b04110c060109062102060703030e030403030c051e1b011101060320040612060203041a0c031605130302060c0114010e041104050c 72
    0x11500325120301c41c00a0708aa00041c0000c06c070350300d805802c0e5000d64420300c0c00510f142c28001d401070300100f940303c0800940f44c0c1002c0000c03129983c070b0351081c4403055152101e0294420340c0e0350390320130005580e040c60f11966072a910b1002548465007400ba00c5034881c607081c1c000ca1800304080072036841f150412029171441d80e244e002c000082d006440201c0030143c44e0346100303041440a2001d0802035200b9103810b01b0007070140c03400900f0170100d81503c800b070140010071029401c1c1c1c005440e17a00142e040030305110003e02800100c9440020b100b00001c0c540c02d0860000c1082000c0e000c062a0614607060500036913141d80400090700c2d12403180c5290450740c02e9810020905981c002d642103840746a13a0303015248042440d14038980300316a082d80301071011040145000b19000030040d101102d1400354503020034813000f00003141d66070201074000c42003c2100640d03040c3c258032410b030208240103035084d55a581c0c12071904005007110304444203601500c3d20b100504150060301c1c01650f082245c203040100d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 718461573 1250 718460323 718460387
    0x120e0a080c0109330207080d180c0b0d11070b0105210604030509011205090717070e09071701050105061c0b0a08010b04061e03030305100b180f01 64
    0xe480701d25215540e400703540e4001207004400364003069440c66503e188a0149500308815800d0080d031481c103a00400845001445000c12030f40c9030400c5c16400501f041d03d2032070b00c40e400080040c0050040003042000706000140300301602200c203c2d8401030114290b48080155580503013500184262007200051005241500182000124000c0c80003420203900c95000d24000041d941540071550000d2410203c2d41d012802e1900b00322003040c00c0c0290f0170800802981c8081030702c100d601c1d100ca8040b03000b07082c5000340a404010150288803001070304000d124162548440c2c41400110340016404504c42601802118100c0e14000c140a040103d80d50907403020030401c8014000080e43d800344e040d10f40d034524400c640600304a00000070340c1e541a809010490386c094200e0001c043c0790701a100010f05040001d401660341c0740c07402050945440a600648042c0d5400464040e5004150010590014400880340407000c90b040340341003600340015100c2121046114059480040e0201c0400c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 718462823 1250 718461573 718461577
    0x30706052a0909060f0a09050a0b03030c0c0a0e0106090501030b0135010b1e2101080c040f050f040204240303090807080606060319060f0312120e0a08 66
    0x1480703115012001030a030241030341002400c0108005040300104100c040c90519066650703110310150381d078644c040d4425001840c1c002c031030711585404a0712240081c1d504070554115002d108030140840c1e440c4c454140d02141c803821140401d6000346034202c000144042c580c0074040c125103068075040388041c1440011000f410071442000d05002c80320000e04444241014008203a01e002c13400503050741c064110740e414120041e406603207000014010455142d043c0300c070002c5902c0c030300d01060b136891249114280502d440003a550b00b00003004400043c00d0708000c101512030f140b00721001c0152050402c1d840049850a41d202d041e0820740600040041c10710364007200001c0318a5a400f9002d1051509030138041c0071302d800440c00102c0800041115030340c20081c4101070308402c1c014200c5441d020005ca403c50000a00d0300c010b0b8030404c1ca0300010740308254002c1025000703c04050f036016849041402c0443d600e0480078000600c05180c1100703a429910400045141510141070390340103984900d5826 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 718464073 1250 718462823 718462831
    0xc0306160c0f020d06020909090d0e0d06060e01060507050c01080103170306030a060501060f0311071a0a020d1d06090f060a0e030c060412110102031023150d150803070605 75
    0xe002e690100015a072266016900d03036124010140e81c8031494002c1c030000300d80181c2a401341d83d00c40c1002d00c10013500165038011a01c41503e0b00590011035080c8000a0070b02503002407001c1020740c002103609a0b11100604089000b00300f11401c0101c4280110355050091201808100f2031144107425601008000c0d600450001c0c1121141209a1101012210300fa807194000c501918200b0480039014003c0d00d81c0340308101e50243c242121610381688900704101050702103000c0d440051100340707195060756001c0c00040d204005170000c0925202c107100d030b051000860351251800181d900c440014040e80141e44080180c03509441d0341410102078081d0503402c031480e00081c840d01c8500139042200a115500480003507840d141c0400c030140c0321036601d55404149900400c00c02880760100784202c0c086038129202002a00b01405c4005010a500f110a59100014143d8441000550720140648082c02141002000141e20b451502c0000721320400003150018000d120225550b94030480c2c0c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 718465323 1250 718464073 718464083
    0x1a0f0417030d1415030a15050907090905011508030a020c130228260103030e060903100b1903050c040c03110a03090507062105060114120402030c0306160c 68
    0x91000440c4440152000440180514400c2408000d82030044c032084c2da4111318280c018201d4000e00c3d0f190030f42441082c100d0b084c0d0030398440020030800c0d941040004014000480200500543c0d4502a8040c08085c140b005401d01d0340440031480d008040121000c401c620380091500320a00420302c1015021511080501d035402e128000035500011460241605c40b41c85003400c03401603e0000e840c5540d6640e50707485034041401240ca40158290145054035010b0401180704441c90f000501d9a03c99048502c3d0140990614030007410003c5c3c01c2000307203501c12110b8210f20300800c08000c00c3c4e04035922010704a0340c0554012401802c150b070044000c2c1741d40b4903001c0b5110322628607102441d80010034010000c4c0e551240a0b007480000d1209070060101ca1828100082124103c8054000d1481c00c9449090f03840c0085600c0e80e00039035000c1182014044584c1d11105181000016001d0444080c0e0007802941020079061502007440340c0304900d10280080d40c01907035602150850107034902190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 718466573 1250 718465323 718465327
    0xf040204060b0d0501150302040305060f06190603050709080f0d03180c0e041a07090501260a0e25030807030e221803120216080403050102041a0f041703 67
    0x504150b0710001449258050030b40420b165140c030011040720014505001c003054814081400040d4010440c55005001e50041007000d85a407800124105000d40c0b0145640c049004005540b5405070002131103000c854807100c051964540000e134079664000301c1ca080640003045003007586802a8400d40c080000c02ca04982c0300d1415a48a61030882560040d008501d2980100004c0000425460780006440b0030b105459040018015250b5559806128140020340701c0070500003c0741c002800d5500c0c9088001f02c2c40341000f407915002031a00501c14a03031030088000400785041c0307100341c501c2000c0342516034640300c80c519101c000c82500b040e8004c4041001d000c8040c120b9a0311b050b0092140d1802ea40c10206080c7d0700818030044a81010001c40580c00001000c00400c1c0c11010008011006ca0000350f900d0040c403540102c2c0148990004004410124020040c40300550141081c3c0d4131900c81403108910819221100c0e0180c1142d60b241d102003080f080c0110540303400240c0300d0b0f10b40281264 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 718467823 1250 718466573 718466579
    0x1060e0315010614070609330c020703080309030c0105070906170603070302010f020f1005010f0e09100c0c0803010e04141c030207170d14070f0504051504030b0c030105030c0a0b030f04020406 84
    0xf003002d003004180171a154861000f641040c4423500400800d003545940204000030b440c1d10f01a440c0c0c4803511001c0c00203400800002d0301030030f043c401c07120f808038484001c01082c5000040980444464081d082c0010300303484100e511f00320034040d444e00565005006104440c55a401100d180d42c2003035010302140a800f01c1e14aa42204100d035040302190a6030200b950f4ac10b00c0c803450410001503100300c4610320301905118030454003290740c40d03118040031004110095104c4059400b00c402c2d02c00105486400400040d04282258610b40030740e20405140c00900295050781360307200c4025582c040003c4000c03502d01216070090780100840c911560100b04810f402c5256940b2a4210309445801c4c80d86403c80080c42d00c0300901201c0c1e1041007820300143c030a0080364001c20501490007014090f000d00310864803003170f48410a88004551106000d8201e00e410400007074244c2081c861180248101880307c400d070315090091500b40d0340c010381040e003560348545c0403250030349003e403080c1d810540d170b80c03004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 718469073 1250 718467823 718467833
    0x1050d060e0d020a15060506160c05060c15010f03030516050c0402270301051005060c070e2a09061801030b1201140a0b090408070312020301060e0315010614070609 72
    0x24418a40b51034016102410450400320071201010704170040b050f240810500107550750342c068406101e03001c2e40506c0e114140b45400d0718918000d802031644540080b800c800320030000102e400010b0744416800500d642d8501c49103000060710300006000c1138040c026410810540600207078002d00031021554038049040101d004c82c0c0c4140080c100355542e818454805001d0601000c050b00d5099008018514000c8024842c0d000540140c6118200010b000c01d0050700412141c0b0180c26201c3c40d801c0d00e404e00b80c480f04401440c491b0024880c80000700e039624000241d0095030800d050192101e8070b0142004401d4004101802c041c6051503034440390907039551600b05000510089d0b0300300029009030881c01c2e0081c980d80042c840c0852508000984a040e01da4008a136041588584c0c00394075943c492a0503106c3c103440b91620050148040b0001800039070003141d4400811040d0203503042051450f03d00e61136400c09000d04800b0850100d4104641103108000740b07203ca0191324001502d0207d5a03032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 718470323 1250 718469073 718469083
    0x801050603090c0d0b04050607020d02250b0414090c1905220b03010f050d150203102c16090302091f03060c0906110d05070c030609050105090105150901050d060e 71
    0x20035a01c0818405c20001005001c10050350086440e000401e07224407164002960b90032104c000d03c0303da01c180c20501c6005005059030201604000c60099140c64681d003581d41e442c00c000116501c9110000701007000b10034142c0842d10f80d901135040002800404940503074060b4420070381c800280303061300610140130803500c0920707015120024040d9620351411a841c07240034843e0700507910800c10340e6030310000100380c2900a848048030348000743c0c0766900c07000b4400d007140c00307a444400000c20201d484000304256203540603100d00c600214100035250b0302010204101034000a50202e44402c20500c05441d1503560942e1249007c1d6515100002001404031001c2c0a6441296031b103031280c042c2c0013503903000b181c68009000c2a01d0203100c43c5040c508600d603a480800c002d94103100e4001a020244140766900a0140d60001010320107219980344c158001c2804442003501d41d4a4040450b0302c1c40d03020301000c4c005c0ba00003015542c0760703405c0000300b12040003401800c035980c030740c0c03040300350000981804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 718471573 1250 718470323 718470349
    0x161b020405190b01090608040b0702030c030705010608060c210907090207200613140f0d0302030c06060a12020f18040506010303140f180109170304050a08010c0801050603090c 77
    0x2c1010901120341004025a04640c55950611071181c0051121686c0161619417090b0050b2100350710780c5840005900714450200480c0450000050304002d201054003d441220400d004440701c59031040c4011203680245681282120040c2a9a100c00511f0111a80e000110390080d1a0403a944e40756403400c9030301980d4201c80f070490100321140c03811141e00c0108a440700940342c580c900900003020007080ba0b400e005400180b102c074914580700f034890015402d940e14014260300844011420065920740092000c1c4078a480b8050004a0307904010700c81808845244030b00c8190941a942040741c800c030766082e00e070380010701d40e05240702442440c104c00b0301680c041c002610555045090050014140402c0340500003020050581c1c041424130444903218640c10315166000481001268030801c05c2d80300540c1f440143c01c00c0740c4000c0d404001001203580890341d05482c940d448000341d00707075520300081c0c6021a01c103900401c40d07400d01e40f0086a0014490b015903020080002c000f40d540c5030380c05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 718472823 1250 718471573 718471591
    0x2a01050106032702010206060d1a07030204150c1214270306151305060102100e0303101202060f21130b0f2406120924161b020405 57
    0x143c030010744075511a201c0c121041440c1c684401ca105500042d55494000c3e1081d0f0040003104075103000d129200d00c07102c541401d480e41203c030600305088018081c2d00140180800c0302404000001000c2c001d04400d401281d1100342c000c0c0c518820041580c5c10b0301c022448840703400c4100806840341103424001d060086140c00c4281c1c11900308000d1614080008200072003490039600c200070701d5030f0b4048200003268401200425503546d0038004078207240341100c4204103e820040110315050011010310311508048181c1081b0b29910b1098401c0e5611005020303421101c200103074003c0b203c01500500d95103480c2c98000b1040d040d012029030100c417040390380c030b542d0b01408060142045a52070115030000601c402c8000e046c102249203020103080040b1309072044651403500a5079032100b8050f101d941c1149002220a49040b117440b64980701c642041e10a01680b80701c2c100207000003000068064a83c03051300c8210051543c00549100c003e20281d841d4101000b010000142c3d91802003900c00c40c041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 718474073 1250 718472823 718472831
    0xf15290f0406080906011a0a1205240607080706020d1503080705011109030c041d0102070605010e0601020d05041401020a0c12110405070e010c020a092d112a0105010603 74
    0xb001000b4100b4401a02c21107280c0c110f10010414011a010340440d952480c0c0750842d602e110410302615002036114103091850b080c04104070f1009030301169a0428019614010850484001082080d10400000a01c003502c1409100041180c6d640a09280c0310541c034001480c0702e0480008c41c81c1d01b082d80c01224480d800050b240c08202c020301404014400d41203100b4248412000000e440c3c0710181440d500075503841200380d141d048201d5901e1101c0002074021540d5484a0414901511013402208040c5040c5000306d15194400100300511002c2565403d0030182802c04241d03265107a42e442504600c81c415900000c1200d0000540083c540c03112031210002d443e00e00454001c400235400307403046242c0810441d00680010f00509062024642203420b800a80b000440c9036510760418204e141c03070684995140c1c1070404095004000035048946480c54038102e001c1568415000610485014040c4504080020f404a02032080101f403404e14403181c8202e0b41e003101c1090b0b001000080e11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 718475323 1250 718474073 718474079
    0xc08161d0105060909060f0411130803030c12091f05061e150a030e01021614030c1b2101051f0828060f0b01030f15290f04 54
    0x848280103400346050000e8066940c908400109603016100c01c81e4059051100007030455624100e01100c0a4801001007140100601da580d11035000030300480401c0308501004549450b001003600c4c450301100803640c1c906045610501c0356a40c02030042c4070303103115114142d40c42c81400d034150f9074039041070640015030307140500c1003000060b8600280641501c11254081c2541c40300c1c0c00d44200640c104141c03d549085102e412002409070b01481d09042d4030201c0d0022814145401005505005403104130384110301d00d090075240c0c4940c100052040d0302440b00e0f032205000303641485481d544000c00000041c482040c03601d015a68074040c004059648008110141076604400040034030301e0b051107084681000c102641d40c05034601d0413190424424411101202c03480341d90160b06070711403000c3c0b20595540c14818060300d12203a407580400d01b4401c98059401036840b420718010f51404920900514020310761044110720300c060500c084a500c6800d0b62074040c02d005004041c142c03260743e95103c0c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 718476573 1250 718475323 718475339
    0x114210a080316051201260a05010e0106050a0f05040b01122408120d02070f1e06060909050d0c0201023a020606010c080f121306050c090d06090c0816 66
    0x1020100f03190900505010700207910500d8031105054603884007450a5155000302c6000c080000200325800e2071294211500803c001900030384803568180d4002c0c044552914204100d1a01d18003620b100e07461208001c0100d80b800c2c0c0c115201d1118107051556059805641e0742081d69140c1045442d070401540d07a104410080c001c1020092240c3c101072705450200244217412481030380810381282da0041039010030720410903d011802a44400c1d82084c8504600700400c0c0542100c034103442180c98100002546446400792449155208004e40310031681c1007400d5070450007441041c1d0461180c08203a414030704004000644c0000d00c07007242051040c0c42c0e00304d040801d501903205011500400140000c0e40d0700441201d941c2c1b540003600c140c64020b0070100c0c0109010303c5d81c00b40d00c3c44006006128070504204002e04410b07024500500085e903035060002040d2040c038600b15080380d118000e40020901603440f905c15544a07080c03514480e680c3c0c440e690300d0b144071030890755400c0e05031040800942c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 718477823 1250 718476573 718476601
    0x608030a080a0b0105070f08040801241d0703180212030417030a021f091509050c0f100e150d0b1c020105030703051f0306230114210a0803 61
    0xc0c2d1100248103814103100000d285004480340104007500300d1052004110114081e54042d01c5041c3c020845210309042c8808004d074140e5006004c2c01c0300d64000300341901d00c002d108112200b0001001a16103542c44114010102084841c1d2503015080160005a0700c20740c580781c400c40c0d60f400464a690030305a042062803150030108101c0d5200708a0000e40380d801068040074115410551042d008e07000c10301d00040e09040100030000d0f01c40c80200719291006602c9041c206004504998190f00c102080c0803200e42e01a8031250b00c00b44004004800c5842075004003603001010f054a40c1c002b100049280300f0f5001030040c2e0381c80c5034507165000c0b50340c2888000c0d4a031940070b11592090484050300040d01d03500c80034000d181055110000940106020320000001c1000c2c6198003064599a00f0300c40c0c02409a100c201c00d0303071402000d00e04a80c4441d0041076050f501d11007081d10011b60313008100405440c0c440e041164601c0c50b10381c1500c000c6d9003403000c1080c050044194580da40717080c20070301c0011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 718479073 1250 718477823 718477831
    0x1020c07080304142713060c17011d0c03090a050304080714060421060e0a11011412060d0507050604090f0605040e1911030a03030e0f060103050d030b01030b040608030a08 75
    0x96035521185c040a50340c582030700703a03906464840c0d10f04644600c0071504d00c05a00000240403a410034040364510f0350702075014800d1000049150110742d880e0b1822004806041c41e6040f082d2801d0008510101900c4000f141c01c6124107040300c00e152a42c0d41c0302810b580140c1e10001d60340e0803072241040107410414220020010888549240504040c1c600084181c03806418400420810a0790100101544103501c00b0044c9011a801e0300001d1420048000d000076005001590444882103107280e148165020000400400d501c16600c0c0014082c0d10307006a40161018031520100048945614004001070000b0300c00c00714a43d04880e058000352030302da61002c4c1c0a80e1401ea45c031203001201040b81001c00e11521000005038102c0e080081d0890044081c130356060040c0c0f4982403c040d09907211008080381c80095a02d4034640202407511200309100c007420036048025407441d160b109500402c2c8811f814100050102008c40104d0101c400a0b00210a81d600004d0746c0d00c140354100754450341c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 718480323 1250 718479073 718479079
    0xf2f0c0103090c0b070303090b0c0a02011a030a0b130c080604120c0308010b070f06050127050106140325090e090c1e0103140c130f0b04060f0201020c0708030414 71
    0x444407160382c0b41d000c0f10805110b21102180080f0b4000d007010700c60f03040050425048482044541001440c695031a8000801080598a480d18414880d6420b52120a02ca64001e010740002201d940ba900100480113200e1400c490b0329070303c1540094403141d46003014041c2c0d503000b00058075242c03500781d880c12091000581400740d4600340d0400030741c1c4401702a05440300955078940351016403030501520202c2c0305004001500341400407895000d80400e0301d10750380040c110803201ca00310811036000c07a0408e010300800501440c81c80009181c001c00203540054501c0301801d603c404100106445003240d58900c00010840380302046030f04440c404440c4c102c60018090885900075100158002041034603d0080d072105501d100c0d0543c0c020341c03003480c0e4042d021001c1041c918102c80b00c04890b51001007640b40352903070140040741c500000a60403040c1c901d241c04c02403600f802c20805450580414811408540d002c001d000e20740304060014a0082031007030002e64840341807182c01d038151004044881c1c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 718481573 1250 718480323 718480331
    0x30c08060f0f0112230106300906050a02130906180b010516030513150c121106010e0924040f1e0609200d02150f07050d0f1706010f2f0c0103 62
    0x1c0501e1003600141c010b5034441c0c0e044044200c140220002740841c90006003001d4a032104004095202c1c1d0001c2001c080351104003010540c80741c005c082140c00e07500901d00060010a00c13280714900f1139005440c400014104a0b05003408001d001e10f080c1b007851400c45c0084c0300070800300016580203c1710b1001e0540c440d0a03144005d4000d034020869141407001500075290150309040403030080e442d00348141c40f542d069844c03641c0c58140303855030742d07000760365106d11442030003010420700c0f0480e031145244d8110200f54803400e4645440345041680544d10550f601c84d001040e100c00301c0d0480554190721482028042100d074204e04100c4c0e508249124412080c0c00780141c001810760741d000c04640a941c2c1160022660420342c0c42c040c00c2409940c20906046070000350800034040e00080120a0b4095540d03462a4491b2481c81160340780441d100002031b80544030f012a02070340c042c40341884640350902d050300031114010aa03039101c01d00300390376240800740303804015a040002d2000780306150007820140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 718482823 1250 718481573 718481597
    0x70503010819030525050705090f04141903030510050901051503251106090d0801121416080106051f110102091003020a030c08060f0f0112230106 64
    0x41c1c482c610142c510080d01c940c850030302d04050240c010b40b07070445403041d103140c0901d03158004030f1700c1c0180f0101c1c199480e01c0b0314080010b062170510f25051080945e0941e584664a41e1f80e00e00d200126130503044903c1e400b4080411050a9540c560702c840f09020b69000300c0c59041086804860304229000365024241322130051026884a0042c09100304c881f14031280d4136a1040112404226034145440420071300d240503407032a55110a1a0840030025015101161a5070200700e5a80c40751102c00804100000010084c006048602007111401102100c01c10300c0823044541c1082d10340d02030045011005401880911424400d480142c2829210148a00c10310a40c0c01d6428000c0d510a0007040710b000c00c0312103154029019a002404003414086801241e9232001d00a90051600580000d02e0701206079262881780070101d0241d480a03080c00270400c54003040c400740322034038101c3c6414080d0b055a07407011640180303e0a404098168a8116125843c5050740d030340201c1030b4801400c00c4454281c3c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 718484073 1250 718482823 718482839
    0x501060206070e03030904050c04031b12080a0c0605040312060b070206090613030827040c120b06040506040308040609080f032a0a050c010207060f080c0904090f05010b010807050301 80
    0x4650850300c2400e2000c40c0c3c2d000c190000f4034610500c3c1c002600581401e042c003c429424002a006907440b0f11600080d100080d5001601c2d142e040c030070707000040403c071010740c04600c0400040c10303642085c0c0f804081003455522680107480043c0c03421400551085881d6850808030b104000203082e094010300e151907569000a6054014100507600c180c0b000503111002c00c1414030300000442d405041f0a486081907020550f200341c28014034020b00ca041c88542c0500c0c9807a104400068000b80c881c04899004000700c0001070803da198580c02150400c008a0180c0c1c8a0300607200551080000c1c0340e5560421500406020320b581c03084002d0b034003091140c0d1441101000f81d440f0041c0440740016811141282480c4070500386c041401a0b000d0300044100384540850301540d0341c0000e800b221702143d911542107501003103940200780050700c90004100c0310b404030001401c1c107a030005c2c0081803901c40c0d62120782005501071021201d5a664208200c4036503040445030fa8441e0050500c2070466240c0004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 718485323 1250 718484073 718484083
    0x405030309060922020a0e0109060c0f050111130302121908070503250615060507060b0d170d150e060409300212130b0c010905031603110105010602 65
    0x2003284a00400310f1030150b5600d42006a508a00304802c2d03c605403042c1c0a40c60000f0f6011403100c40000b407462091041c80d5000300054800c07510207a50b000200d40c4207840d1102c40030b2000404445654076180c1b50381c003000105020300405980c0c52070008507541b031841007040c9101d001150b403460360484924a504d11303156882c40c0c0300254001e08200d94a07481464200d086201d4070311180c201894401c80010064404e101134034200f84116410042d001149502004440440c450000010300401188000426540003800003450203000298103c0c0b04d9910a0b80c000c0d0313030b40040402c800020a03440c168842c01d016041400012130800d000d1141040c1c0000513901d4010a114000d94030741860204102e500c1c001480b0140007801498422102040c8503001d484007144d20343e00612444440b5002c10951a04030340d003440404a203440c002d49002411400e54020300000380d495581c4030298404240240014000c41e5520308102d0f001607020715003d40302c0300c4010707039401a0303070325040045c4051500050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 718486573 1250 718485323 718485337
    0x5070e101706070e130b04020d020921100f0605030303010b03160f05390f071e05010f021516080702030a09060e0d020307090f0c0c0b041211030316030b010504050303 73
    0x110f001e0380c05d60741516200500031428201d60040e100113886644d03020650b01402444400b103448080902c404c01500b1006e81c0b001e80707643ca26070802d142c2c0e450821500c1c1c0c002d1068140c001d201042c115640c600007411038009a120150018000003000b0303940c0c01a840807422481a82004030b4080130f00ea0000b080c60242d9000d1a020144040055030400e2441002110084104004058030a002c241041d15007100300c0100101d8414000041202e983c2e2201c040e50701019907900c100752a160000460b1051502c2c00850b00f035020f00000000b010140800c513620a101c8003605065452a02d0700c018220b2900900810440d003040c003681c1d0740b00b0760201e540c1080301c3c004c0c40c12403403441030800010349603a00740714025490321803084000359464485e00000700034a00f8800c100504080b14409903a00e19080354001d10b140500c2c00001c0010f48981c0ca80101429546451640c80d2140e880c403624540c000d50300300280c28264081c0c2e00180d40d150081034400c10003071812a04081c50100400c0d6607000d106 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 718487823 1250 718486573 718486579
    0xa120b04021003020f0304050109110307050609040209010c02090901091b03240605120f060c0c0604031b06020720010908030409050a2a2d080405070e101706070e 71
    0x152490b804184640c06451500000505581e62401c0618000340201000b0340d0840c0c41c800c42640440586c513000c00c06904886002e402c0d245480e41c403e003000700035440944d5007418010a21203504c05a1900c0b01e05611600030400009245051350800780d030b01c1900c0310304100c007031440e0380b006100041ca0075030038898402e4450541d02c1a01c1c3e86207050000f40c0680d401c2907030000441c01078543d41040008410210589400941d007464403038085000c441d01c5107c019a066510500114001903c13410b100883c2c4102041d00703c0814406592745020ba902c580c9042d81d0258489820000c246044001110401001d00b0303d00c04a034a0802c01c1c6450380520b11813020070a42d03400c00106102116005010f5500802114850091018098540d00000017030440d0001740c90300c1004c469100d034000700d2100e031481009020a50174200000b200d40d1140100104c8070780c017810400041c8881d903844418060649040d08082031070030804d0005030519401d15005140e0302c00303c01d0000c1142c0107100610203030015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 718489073 1250 718487823 718487839
    0x1119080901080721021c02040305031e040905040c0302040b01020a02012f01091b08030f07060504030c1208060102010e0303240105120705031806070f0503130c140a120b0402 76
    0x3110540f902251450070303130400d001c40e4080c140012140ea0040285000c140c1c3c0401d02d114131010b602d000c030701403800010240d60003003141500000280c1c91001a89440c2d03a003080c50f003511582103174103990003a00c0860714207034018424030071807626000b03444540100388003d122030308040c0c00080922030001c00200c1d0f4401010401e0b02a004036861b03500400000700003d212907500c038508106403600800f01154800c006080100d20300c0341c08811a25044401d4103650705054590b02c881c0014840070b00110140f0041214440c009074010720003114407411a03c44070b10030319008002909480c88042c0c0600c0d0b54004004001c202000d8000c4082c00d64100e81702d180c84400c290005076503600c12120560855003030700d4100240c8941c00001903114860300000c0c0d50b008e00d80644840d07640ca209540c0040410a603080103002240304070060350740103132420100e2001c0e2415444005400c007054002c01086070f00f00c0340c0d01d5020705064045070001c212054428104000f103445250343c1318800b400003882034101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 718490323 1250 718489073 718489081
    0xf090b090a1a04050c070501050c04080a080901090819020a120b0103061a03100608120703051c06170102030604050c09090c0c01090c15180803041e080706111908090108 74
    0xc1d2402e00c1d108540040c2080015060141d40240103030044081242c0660801c8001200101c003001586c1c11210b60000030301242d07026580b8440b0a80184400340e0411405003400521980200f09000c0713111202c0465489055540c018040060540d8118007461040c06040d0000500d0a031a4141103d400c094000b54581080000c101800c01c24140716500d4800d00342c452038200721580c403500448072480e0407950507400d250709030819400703405c0001c0e006c50024000010a15a152040240c02a552000069191b107d42001c047e4031406907801066a601104220312800c00c2d00c07078150003801140c9428100500304002941c0703000f0007040903511020108140520300c109400040f1072070f510581d07210203203884510601c200d05001a001d00042c000004040c44d1f130b0400040881542d04003c0503600c1c16080c41010007000c00744a1905080c41c040b14030009a4250034403504d00a000e82d0755613100d030f00700e4040c3c07080d20348002c1205145001d0440100840050a00d2088840400c000c1c2480c0e0347c1c645e9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 718491573 1250 718490323 718490351
    0x912030e2403041b081b0301380114070303150306020c1b0a032114040303030207120806150a020708030a05030618070903020f030a05010603230a0209280e070f090b090a 74
    0xb0b2081031030108403110040b8014107903924003852421424a0010f00407040000004441c00320111018bc5102139080294602092080c2c1003010041580008461000d94036a01c4004903408004901104c1d040030800300746410b072010091740b5041007204c456480505545038503120780c030301078034015103a06204581000030317004000500305041100310461b01c82d070750790034050080d6002c041c0840d5014541f1003c200304500a540c2030b4021b110144c405551780d00080090b40655021181c008254801d051001800300410002440000a99a00c50780c40741809820b1240c0040c60021084140c5180700400c4101a4030845140440e03804681420007030320124003190602c014038a0281095081000101c140108045c07401001c600307000001720b620141c0a1010344640b01000002c2d801a40a0041000000c0c0165014401786210404680b4504041c40b50710448103c201b0180090b000728034108030069115615400501200c46c06020f014000f0001480c0d003c4024440040caa43d14180d0410b015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 718492823 1250 718491573 718491581
    0xf06040f2d060f0905010503040c15030209090103200303180103050c04050303070303060e1509060607021906020c0118050d02010c031202070b0411010912030e2403041b081b0301 78
    0x10050300001c401c46a11040001e0a008071a400c507000b140301c01d1000074483d4801d0044a200300e41200300b41541504082d22000369081190f800004c01d034080c0321040c102d644131720340d4a000750b00c2140c0005031944201e40351004058540340d0540319800c24070071814241c00841d10300301240024170b07000070503a440400d410514001c0703802070368043c4000726064042581503809502521040c1c4134044890b40c540300001000783d041c1800c40d41285010001c00c1860410001500156100a08a003510014041c050044800d240c2c06040141c0c000000d20b0025600280380c501d0f0342c5008021220020f003081c1c0420380791410088000d0400038400101c400b807503c01c4064540c040ca100038250765035000c909000440c1902540d003960140c0d07059017880640d41c0121000c0e0704031902c2c2119840c0c03c26071610141d401307081000400e908402000c0f400003040d00d1210030350f0322442c0c19107400e5490b400d090506240b9048140e2440681e260403810503c4119000148100d21407004c82c0280306020b41180428054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 718494073 1250 718492823 718492889
    0x601051902010e210a0309062012060409020f0d0c180606120b0a03170c0601180b0307030203030301150201021603030b01080708012402011d0c0f06040f 67
    0x14500e00145814540e4103401c01001e0100807002c840ca590000c0c2600c40320301c54114010b4441d000100200f43d4500e0280d000403001d03034024900040c00f490644c002c40c8040c0a1111058011000051154024840b14100c04e401500940d0100a80a440d0703010a4120a00c105d2480c40781f4a91809001001000c0c01c2d00c402410b101e500b0303144ca2100d190032600240445016910115100454031034692070588103d2040d48802041e03503004501e540c0b51070000360b030440040c0349003010400c003003800e9082c2007010038002d00c1900e4011030b2040300d111718041100d5410381c0e0144a0740120340d0400140c0d0b800000c3c0e0341500c17104415522115000d11040e030080c0701d400c45000c032000401020b6810b0640591101c3c0c800982070702c0300b410742d540d1940701b150402d400f401b9078040d061114160525102c4c1140f0b01c1c8a09070072500001403100340400da00c202000858138140d002d5480112110110b040c840c1e20707000c048405654107400c2c00d0a190504160403c903005942d00e002d12801e03158441c10040300340320300c0303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 718495323 1250 718494073 718494097
    0x51c0915090b15031f0203040206041a1b0c03070e0a060e090a02030601150f030c05070f151b021203100308070501060e2409040c050a0b070b0a0221060105 68
    0x418003240361040c40c00074112840702c3e00101c2d0810f00505410045032892100091032180b0a2280c9038481200094001a02c1603070400800d01c1701051040c01003403000f506aa03c0102c1c0c5485113100501690040e0b031004103048150080e1506802c030351000100d0509440130a0079001c284da9a80814000420b4941d01821f01d624411050251250010031600c0d2514002e40c240c031030b10313070b00c40210081c1c8080d24100000080d00c1110050754040c8a5401140b10343d4042c549103107002259240e20b191810054010354a1540c94403075a07403c41c40d203101e111000c40702c919006417240071070180179454220013800800d03620300000c001080401c1c0d2070151405035a005a80c940c885a4a0034000d009203480e001d081882107190000c11012035868901401441000072020b80030744290040c84090071014204584c00300511102150903683c00100d0005010010415511840a400c0c8003844100c05804c05256030703c1088110560510300000009042c03611483c0d9034281c41b0b0700012a528418030095401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 718496573 1250 718495323 718495331
    0x2120a06060e1501090303051326010b030f0c0105030604020409020f030718150522150207120c030209220c030b090c10030c0302090303070609050d051c0915 69
    0x801003554806419240484040c800595410000c500501000b08140d404110001d104200007032092000b40801c603c815001102e00342c0d1103c0341540c401e00b8250b0f5420811070030f0007022a0382c909105200d40740104030b00400701e04d1001510582c46000024200d4100034000002070440d44441d0111001490300030400c42d40d440c0644814407850300262584000901d0611042e88090301980160060310f00143d007600718040034800c241c5150f0f000c000c452071600030032100d540603625590b03080ca004080103024111700d0083c03040d009003040025082030300380c00010304864000c600007203d04025aa030544c0d4010440d1140b0b0807030645055040040038001d100788aa80781040280b961600c00c6900c601d0108186e6120020300ca9140e20f0f51407a001e03000841c0c01c55501d8058400d8100861070946403c005251110701e80200703055a20106059500795100c168410810504002a4200034042e18110703040c9044080c0b084080310b1915900005181c0341c3d140401030260089000300003642c101030402c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 718497823 1250 718496573 718496593
    0x3090b03070e0111010903120f0f050c0415110622060221251b1416120f12170a0c080604020909040204091110050c06060d0b070c0212 59
    0x81102d0241ca05841c0000c5030f080718103101802c1401000c0d1016859290382c11004c180b40c1c040001020711040d003000740e070f0b01c070b5001070540e070901d110315805642040c401c665180d0812011200b40d1846403200020407041d6a0050b070840801b160180d08802c0030b05012800810450380d00802c511300c0340003c1d20142c400503092241841100728841c2c400c541e03a1724041c00e079848422810b5a060365038840109241c6003440d1506091194540c1c0c2c104c0d04800d0900d200078401516802800032940b104940c29600c00e000341c8040c400d00c010714078003c000d80044021401c08594568540389000b400082020b000d43c05000c100c0d0b802024080f0301c4a440c0300756040c0e285000002000944400c03440c110100b2150760100d0a04d04040c003c071000d82e01d0261813403026403559400d00c0020460300c40181c5119606521115690303403044c0300c100e0001c4660350741c0c40c0c481003501c86007420110090000e92180202d0140c0c50005100382e03540c980c1c4040c150401d41500c4119001103080c0d83c84840d980c0c045400341d03010070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 718499073 1250 718497823 718497827
    0x3070510020d0c111e07180b0405160212031e150f01021b15040b07051b1903080a0905041d0105130b130503160c0806100312050703090b0307 62
    0xd0b240800e0384020502c02c2c91000c21044d1a2000c8070020401a074100703001085108401020080d44888400100e9000f25600d03071116510005003821304001513114028952a8606030003120f41103102051841c15a00800901954404c4000c02c40203180e2400720008114200d6414040800c0f402000401c0306442e11030140220300081c090501e20807850444916503035440098205030683c2525612111494010304104440c85120481141d40404002c0810722180c00005007413068454402010303009031203403c565540004072102402000c0c07001c80e144507181c0c43c440c0d980072640c000d604240e039085100c03030403174190405800c101d8110f401e082c0240d109031044a10485903010304402040907454102880411403060070002e03040c1c05c402d00c040f54030800d400c8002052584108116031038580b03003c034200202100c10b10160b40d004030b207032810003002406000c05980f040910b80500c1c011801c6958104211441c200e00c03408000c0c011406004143c00b4010881c0a4010b5804c500d45a20345030f180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 718500323 1250 718499073 718499077
    0x250b2506020412030e120609030406030e03040b22080f0d03020c0a0b01030c06111b061615050604053301140408010e120a0909090213050a0501060e101d030307051002 73
    0x4841c6c02840c5102c003040584c00d010603014051038070000550724041c070b0700d081140074140c40030041001d400100070020341d0b1003029008224046900d49041a0b00d1501003011444076201d82c010314943d08505e403181312000000c10740186000041c20016220400310070000e2270031504e42c400800040030b0b0400402880303160035000c011504550703100d800c09840c0c50f80240d102c803a0344500781084190800b00002e80c0c0b40a00c0a821002c6207500350301e400340e00c25120520a00c0341016404902c039520b00a1000c6424140075080d0700c10041c1000300c048802a0034240d59102000703d44000d14042100106602d80c41030703568042000500d14110b4172103440b900102d000b0148620000f10742c0c0320710000c401c000c4d0650070646424803801d032100c240007480e15175100050503440030101c1c1e200c8544a420401441c842c85100c2c02000200f0300000c1d603604240028140012100c58a8400c84401c02c03007451140e84601c1691680c90b901140c40855044ca902003403860081c0c600041480c000c6e04180c20000080f40c4c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 718501573 1250 718500323 718500347
    0x30304110405070f090e09010b0603182109100e0d08030a060e1b0c1018030206010f121103100603050d08010e040b071d03250b250602041203 62
    0x20104510f8a03000c5041d140d158078070a292011a040820420aa0751031108075030380a1a00000800c541c024800003a41c1c40c0e00407124510001304120000079118020028401c1c0e6007190300b40c0311940490891101802e00501c21450712813800b050004007264414103240c407402030040d18200c07001d200b40c40c3c03080c25500102c0c1c2100c242840c1140000750010f0503180c01d03014411409100d0b052601c882103c14a96120b451506c4a81c440d041c1010034066a80c81001200386050710152404501480d00070705141060b0f1010005d0300b142403050190300c0307481c2e2a507481540e010315440c00542d40400802d041114010034034a00078a010000000d1020201e40c0e00c41158641c2c0c0d5201d40c1d41e8070b51022422800082d54040c100300c03648800900c105006400c140790501c0f114850324042c4640c4c80019180c04540650105c004003000e2812003525151894038001d4030014820600b4180516100400c0340d04c40081c9107a0041840b1349002130011b42d90480c0d000e003420b1111040b14003001c5c10060b02c0080040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 718502823 1250 718501573 718501579
    0x90510020f180d0b13210c0501050f07050f0a0c060603060b0108130b010509090a020411040f21110a030602030702010c110a02030a14011d0a020f060a02060f100803030411 75
    0x810711070918107110f1000c107055101c0281401610380300ca8418002c0032558003210308841346140e849030b01c040318001e002c43d2440c55aa0f4050103c3c2c030b14059007540e001078001d048484480c401e0200003034010707007a1403030781080d941c025031520100101219040c40740329001d800103240c0940802030000300e81107a4000c030b0083c0c980a2440d1aa640c0c0030543c1c443c0400040d01c1c40c0040c4005110900e0f088903000d401074910380403204e00c4400794000808807000f2441d03413090000e0008040107404a40d5481d080106220710460080001407050406602c6804200a0440300404440c2e1710f1580c401301228060342d00810211740700d2400e4000070f03009100c031955050100d83c0200d59100300e4440001d1002002c3d0b03000e0040c10400884c0d9403a030481e000711709038403c0c1c19520740205400d614007074000101520f01000c01080314443d0380c014030040c45503203034a00b401000100b0803100419000210103070040c01011044800341e0307c034000319208070001c2c1c00010480c04000b05010600c080c01000203c610003c0f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 718504073 1250 718502823 718502857
    0x306330303030b181f0504051e0106090b18010c0512120c09180928120201050c0f1e070b04060e0c0109090f0212070203040914070909090510020f 64
    0x80100410500ca0308032400c61048208001600f200300c800b0312042d010740400062451030b45460000d81614001c0f50312700b00740358288180054000c44520498010290740c00c08500060420180d60150320403200c4842a0b06461881900c4591160200075005a000010345815101e01c8400750919801001000e036000f20281c046540c0601076001c44e40314940c0102010320b810703450358125504071002002d08801d8011408080c000404080794000c6850b120074006002000500d04a0700d0400041502d000f10ba24000c00c10603074101071001c8503520f943c1501c0ca03c1e15016610b889101c034200d00e6040b503945c00b01c042a0401000b0200646500803841034806000443c2000286603652404010040c00200200d1040100700c105030300a000301a01b0ba80702601d4094960002e840360b01d02070782c0b080016440002c0c01c00c0074030020300c10520246154440c604560034800d05c02841c016150240c0350003140e40b0740d4210700300241005000100a606441503440c0c2c0c40c46c16210404d40c02056400d8004400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 718505323 1250 718504073 718504091
    0x30304030b25120504020f1f1d010801060818010603030e011d0303030c0f12090a051219080901150f051003060e04030c0c0f0306092901030633030303 66
    0x4192820b0318800c0e030a640d00e001103810f454040010b4000500160303000b82c0d020800e00c0305607da624120183c01d03980000c2002130b26052000401c40032654614241d400b4650007a14800c0ea07000700d041341110041e103040462900d501040100c0c1d061400c0701c50200303618041d00001016000581c0210701c9030241c9502c25003603428000312017007609481032280d050704100009110520058042e000780e150080b1807601305a41000c15040e5104180c540c000075038004003082007008810000c22502514200f07404e403e000c9402c89c2559514442c0010340d00340000d1500141e03603443c09501203c800c0c210903036030321800340d6595100f0f007483c1241c1c02024065071a401604810b14028000e0404440d25680d00020390754a5440071210750b000150221036141c0d088400081c01800c0d042041e010318080d1100090400040c030f844040c24030740030141c00b401482407864900d6002d0700500141141e81045010901e5041102c061320716002102e540d42420001c034801c0c80000c00c20390040c4050b24030075241007103040340c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 718506573 1250 718505323 718505371
    0x50310090902270f0c03040c030b070201180507050a050a0e15040239030705060a0b0d0506010f0918111e0d030c120302131406160b040b01090b0d110f030304030b 71
    0x100c200d1f0040c00301038010f0010400107449480440e8015500e100008058508200282010051300c4050320306070304c0350205004629103011403100800d02101c04000403407822101e029006002802021a0413000c00401e00744e46507501162450501d4215404c18040c1403504640358601c0001400310740204010300820b1450008103d4012981000091010307580d040d0801019140c4040101c0c6c00a075150385400004408001c07081c00303003810120501556050113110303011600e030700348000b180a030304e980300c40042001404010740203e000e07607078090322081c0180c1c25079500c050310b010b0f507421940c11400703138043c5580101c00703900070b0f8442c0301181036000e03101d0f0048051b030140b01401882400d0b21807042100719600340c10340201d4200902103e00b040c104903405030300c03000300410644682051070104400c0100c0592110b000d0100950100002c0d100040407a407400740584000340070742210b8401c100d8543c4c0c0c00c0c19491030040300030104d81c0d8031a20303490141d030300c001c09a03034041030b002024a01d20344c164 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 718507823 1250 718506573 718506577
    0x103051b030d2139020a020d0206070233070f03200609010c080c1e030a06181b0f080a0e0f0703030e0a0e070203030703020304060e0a2001050310090902270f0c 70
    0x81302ea6801800a004642c08014074140d00c0751040740e0160040100c0700050310b5940101242c0002c021038a50741071070b200c0d2850380d1601c41c0201c00c884070008025440000f90740e079403139000054141c81d00340108014804450648684440602004e1050008115110b101500842c001c085a40d03500360707003030305e48400000c3c45000301400c0341a0045008121801e070318114026541c00764100d100415030691350b0b001180c10003010000140e44070303250186612040b00f02d0100142034035452800c081d820354080301c010803030781014140700b8206849d00c1040e0522001002590070781c2000005070349031196079103400307050b410070748115030700131141c038500010b02100f0203030120f00c140e030f03181c029500c1c5540e4200300718000e5100034000c4031b51940c1c031444190241001c1081184682c800c6840c0d030020001b03850107440c0074050980c45070402504204103d03444103011410403c42e4060480455144a1440064100c03895018a0124000b40001c02d0041060040d0f1550250b0a4520110300c1a10740404081680c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 718509073 1250 718507823 718507931
    0x2a050901031e05032101050a29130306020315090f070906120924110903071505041d061305010e13170a05030103051b030d21 55
    0x4800700344082940c2c03400320204101052160094a01d4598405a00c0c1010707030154a148024440610042c0080c1c245080500007420003003481401d03807100c3d40c0ca8880640c910a030002e0000030082010240c818644142602555010744195101d140075080526050102446244100010400b0403040c0d03a40c006901d02506090b80c822444c00d0410605888600924114481e00c60b90b840c02d103004504a042c8140c401c00a541c4000940c149049400043d1a000f41000e80044030420024031280c0e40000d58004a44800d005440030760180203041e60a80650f5004900e540d104001c0070800d46254103000e03109940456207006201c840c094010308448003400307181402800100401d07404a10f01009442c09441000d03405c0036021070711510080fd8000c1590403012800110051041140034014804444141600400b9a42118000a0741c4148080d403100a000010b07007856407902c1c0c1c584c6101808510a00c0502c80c00d0f6005c0020213925200c0300d4101020448100c2c26854800140280305030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 718510323 1250 718509073 718509083
    0xf0605010e0d03031505150702031c09060e060f030711100203070c0602070627060e011a0d08091009050102010f0507091743030503180402072a05090103 67
    0x42220309030350503002040740102883d5240f40d001e030001450794400d03410104c00c818108602340c6031401131052602e4030a803c0011288100314203e0030191550000100d0308844051400744000300b02d00001c41e11900c200100c000d2814000001c1011054012007800d40c25001c00c002c485107046a410902d08034002074907024000b850075440f4801103085500941610b50040d100020034200840325904041c028000c02035805c251a0400f0f410312241303108003146405000000d2104800e040c51494140c2c0703411011071300c01c03400700260b4802e00c14840156015880302800070750024492101c0a13060000c0c0f03220306401582800d41c030303400721682e80c01118007c0714140c0340c0329803c6013403d68803140b010030021143c0291240041e0b0300c81210308611606108000304224a0070002c1115000c040030010140080d2602c14840c1d04200090002044409068418019280b0354100c00300040181c8104c0c80082e050390303000d10340400c2c14541c82d12500444010034080000b040d60b01d07418481486000d1102600c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 718511573 1250 718510323 718510339
    0x60121080a030e010e0a11040e010b03030a0f05040e0c30040311010f020d0e010b0a0b0909070e1f080a06050a0e0705040f08061e090c0f010207050d060f0605010e 71
    0x701060003508818002080300d0004103000114400440c90011041c0090b5a52011a00da1a038141003d115000c2c2004e0800000d026100000f00460740e00c0c032480e00e41c0c00030080004008158a8030400543c1c02403d150041c0d240075003010080d8029640105141414154550350703500c0700340e4200100e4004010400304101c44d0ba0355261400e4680440c0c1880484465480750281e60a03035203188014078604010020024182d15489906406c46400d43e03203103406003443e820306010a02000701a240c5284003201e2000b813541e5040412510203e02d1010241c000007079400c1141129014000c0002160b9140c0e6004030303039910540390100b039031107d204180e040030b0055030074004140707150700356036002c9504d0800c18985907650450300d140c01c00a900c00c0101e83c110f0800c5c0715289030000000c0d4506420720060346422300340504442c0d241c1d000c01c01000c0c0300d421103148820180c0d0080c0300c118001d120003003080c15000324608161004c0c0c01c2a04410703185500d020340108056000c0d0244207419100a02051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 718512823 1250 718511573 718511587
    0xa0f0f08040320191208090712023610060f030e0f16090609020f030c0c010906020d020705010510030b16030204030c090b18090606060a0e0a0806012108 67
    0x150f4601c50945158050543c3e40b40c46070035640c420880c0c0861551a1403505074031840c1420542060040c40d0a0001040109024002c0e0360400144500981d2501c0c20807402c00750341840002d0240f00c908030580700440c6200820a1510007000800180c5000410281c21075520303800d4150000c07046002d500d0114031440700c0100e038540700b6400076650b91070800856460098400c5502d280620402c407041e004101d5010601004089014540c020049481c042d410302c84071401130b6586000041407901c0c1e48001040341c1d42e006209410120000e60049411561482d89451030f0f4040e50107480c09840340d40c20b00d804114426541411001120b800c0a00d070700c03068071060918000408602c2404c810540c0070f10010011440c5640400b0040150050010750a8102014403544002c1c05a44c8044040c070030040090a62000c91620340c03001080b03131880d68031782d149082a203100c4244100b45405c01100040031a1070400002d01c681a20707440005084041c0e0126505118020110f2004218850500c104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 718514073 1250 718512823 718512827
    0x327150f0f0a0902101803020a0b0301050a08060106020307020609130501090b043911070602070f08030712030b0307030609060603170708181206040302060624070f06150b0a0f0f080403 81
    0x2000c1b0001d07441007040da00c96a20780004481d030040303030003195403481c1c0003004105510380019000010100f03c00605015031502c0d83c065140c0c0030b0040040c0c011800090b2603000d541d200a146816207900301400c00c01540c454140d10002c00031484840e00483c5000c0569400e10700f0074400490a801c1840c0f02c0403035441341c00f46110f800b801800d11109002411607420380703000b01481520040c2400c1d90081085515000e0a1207004640358050300d00c5810802c03410000c2400b00201c03c2946816041c08240b000704040440d05e4003025a00180c4034900d4400c25004115454200c0c1d02140d002f01010b80030041c100303042d00098800c4103402098400c0410412454081e1f2001d15025880c1c021321145034012510385203420000d04807001c40068200030100401031410380001d110251403145030640d482c11030403c004803480348240161140c641ca0f1405800c00c0041e0b0010f01600d804940c103880c0c582d07038420080c1101c0e00305c589043c02140280582214007403060300302100d41401d0390340f5011540c41d15201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 718515323 1250 718514073 718514087
    0xc0903051f09020d0f060b120c0111031b0109170f041202030709020c0a0c0608090a170d020c0303071409130b1306060f020709020327150f0f0a090210 66
    0x25101038607251400a009644c8446118500718061103c00001e2030042c6098000c075800740305214403560b80d40000c070b00e07913810014100403045400e0038400040d41000820314558010044a00c40000c0c001104100b00b21041d088485624444e0820f00665a80000c040c032440c002c40d50a24031011043c00204061a00100915181400501580d6840b61925803000c241e82c0039520010031540b14403a40780c01c1090203606240200540d1511052904041001603210011903002909141c1c401100c81e04950b032200c1200c4c18000440011075450b0661002d094881d0822076442012483c0c00550f861404095411603c48600c01041c03490a400c0c4c0c2d20740354000704070201a040c1c10859102c2c825604100c244140d0016180944518002014180e002403a100842e08116040f9005109003d80a09822a02d2004650854030481c6040010540d10314008413030546550148118040c043c035208240019405009041f1401102d0358414094406540e205880207402040800400b449a882800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 718516573 1250 718515323 718515373
    0xa0203091f09020603040803040b06010309020105030601201c0906180501030e0322140409020310050910110325020a0b060a0801141510140d020c010c020a02040c090305 74
    0x2000140c80c0700190041140707600f04031007c81f5840c80000030f01083c860403000c1154030074024a4240110491540001c090b4040030304040d040c40000710580b1041e101d44080030381383c00107520864031040b0303813030850313481d8541c0d40803054000c51f030079440c045105481007800080c541c01900856803400d245c040110300404403052800400e000900401c1114055030107081c005000c0e03852150031103410144155502601c6001c441c1c403545c5016602401a10081b070b0f40c0003095049040014155075200c122030a08451104c0500e01c03904e040815140d070180d00020754051807450030407000e01e181d400c040d0900007520b04160b80251b84800182400151030482565100f4009442107801c6540c0b00001400e462012400c000c0c0c04e113807031080000e4110b504020911091003222a003880d6041280c1c060400743c0610340e0b1400344080010b54000041f1103404646000619000821202c0144140252284040041280300f2410104940308407440f94100801b92030f0810064400e000211001c0021600300301c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 718517823 1250 718516573 718516633
    0x2032a030708330a0605040501150804060207020105040302100f020607091805060111030d0e010b2704081903090201021002040b090d17071a100f0504090c080609030408060a020309 79
    0x61511600340b29243c01402503100340300110f44182060200016220141c014079051351964100005540c3d001840c180c000343c10081c0141c2d6034610340012203c0b8845c03904069000501d020407058115413150808101500340d900b0340c2c603561110401180c0e00240761045444042840941d610a0342c0707140e20054100310141045000100034181260441c1c1041c4004548169510884011100c00703001c2c41d082818200d54220001030811429107288840b0410030960044200019041250750401c43d160003911035110138000c3d022400c0140a031461003803c0340103000b03a40703148403210054002e440030b0324169804141010040418003a04c82d1280030244c4420201c4840700c85282c010340010800b86000d401d01046643c201c0300010f518010241040f240d18049103020017000c0c50103008141600c4080340c01107020f05460500c981906180d4001110a0080d44c0030700110030400801081240c1b14041070b10b2566480400d03a104a000c03c039a100c0c2550041c0406021011250040d42c0d5080da2503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 718519073 1250 718517823 718517893
    0x3120612172209020a030b12031c0609050f070e220b0a0e0f010e0108031c18060606050a140c0a0f1505130c05040207020312031302032a030708 63
    0x42505001d820b20700da4805120b42c1c2e0b000440030b0500781e02d40542000c460b4103940301400751003c080126603900c91101c10340320240c545e181c1c0b60b40c010016000384004040a0700180484e00b041d540e0f18858100c00d452000215180780240354007801d1200d610905404c6051041d41801e13800c801140c0500850f2150541c0300c6108480824000b03031001e5a80c3c01044003c03510145581070110b01c10443d00c0c1a000304003164018070507014259103d81d44541030400c117038804514a0012400c90680c1d600c18031004048505204001c04c990340d20034042e140c2c0042c1e81c2c2d1428120105010b10410f603101d602c010260f2a04075020590200e402c2d80507503180144284015404166160300c5581100c0050fa01252109940c40c104400d00446841c1c00d405000300301c40452906100d41d001130750300c0300f401050504900d400b0000800c2c822805061101d2241c024040c3d400038104030900900c02c0400070701c52030240d1034503514012941400580001a1101c00300145440042c409030496507040d41c40341745c8049680c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 718520323 1250 718519073 718519117
    0xb070507052b051306031a04020c010e101a10020a080d0b010206100e16030605030708010618060501050d020c01060302040614040c181e0b03040312061217 68
    0x20401051400480c4415042c0b030311a280189001019105640c2008008050105000342060307003d0540c2159290b0a002a52040c041014000e25806002242d802407001c101c0000068064100101ca5403400d4140d43c400d845a0020b541101c00c01b0764460b08d40400c40c04504241c0c1400318641100810342d0040318240c0b0a5039175002c03820790007081603101c1c207070312550404101e5804104d226007007180101401c81160800c8000c0300402c0e03008214009401c4400c040c2560140264484400703400054240c0d40d6581d01c2d40025030181c2010300c20604800b0000c5c1c1c955461090a109400a03600c059495501e4560b44262a03000f0750003000042407195a12000040140e64900c1050000d0000d4600318000c58400d07401c010860b900d80300d6a87c00c0c8a6003400d03004440c1c850031007180c150350401800794642e62581820880d0b11000e500300c0c001070000002404280b50b00081029910140031509011081c4c44640450099020040c020b01c40d401a00b0b0308418295603030302400c54081d00f01004080302407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 718521573 1250 718520323 718520333
    0x30c04090b0609220e0606181e10050a08011104060c0c12030e01080a06050a1503021c27050a02040f0f05180c090f0a2c07060807030510030b070507 65
    0x20a16440984d4980f04c0164070801055001c0d41070340101c104090f0101c0c0c40c040d404a51141d904c48034040d40b8280b00000150290100070007040e441500a41c020403610302243c98000b0f00209000d80d5226101550000cc1c0141c0c05010714030f0a0034080ca1404c0c06c081c500340081d0b030751404c1d40c2e504403607010481c0030210b0303029503441811100500a0703680003040c1c8140c2001410211000c5c0003c480c0e03a0911005100c940ca90102c010200c501c001c40103902c42a02e0f00085000703001c1d0000004007050008040d180e4000941c0224110403283c48540c500c0400200d020400091403510003446500030004480162606a10501ca1818103c40201c1c41040b44c05405080722400c544104a6840904500c61001e0702085010300c580000e442c50001c40c2841021180e41600051251300c0b042c3e2134850f04030003050b0640700c1c2031000b480c80c8002e155803842c2d0340c000c90700c40c0030074007450700000c840f03c000500c018442d024640c014900708001c1d4454605544418000000082c8050140303c420003080c3e000170 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 718522823 1250 718521573 718521589
    0x12110c2b0f1a0a05090a1712310b060918011506031b082712190e010c0f02031c050d06090b060a12060e040807030206060105030c04090b0609 62
    0xa03100340b0542024114002690300b0440c0081c022180c0d5034601020001842c000068800b82140c02907284106284902100d00591207200c003d0140091250306111040030741d6410808903e600207800801c6025840140040001e541c6020b004d040b50b00c40800e005040c8103040b290400031480480b00f154140e8640507085d200c50101d00725100c00001402c020b240e42c140f18003055844821300160b090b51010324020520300b00542a40150940d005548117550b0000702a03801e03c8241c1d0303003030710095400814152490780100c98482c2e80d40303440b41031644206104038605500c0307030030507110344a0046054882610740c1880900c00c0b601442120701e8046c400185d4200401d0120103961102da4644a01d01031000340c4030b013903100300c8000d814504000b000d0355824003914450700c042c1c40e10040d84160f0020442c0540b641b580119000040300c4140401d004000000345400c500170313000c488d002e840700c000440d0300d80b01c22a440c2c0034004052100344030581c12074010400500c0c00400c0c103400c1c100003900181040e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 718524073 1250 718522823 718522853
    0x5040507090c05030907051f1d040e070305060f0f010e0604110301090b0f0406050d02090a3809090304090f020d180515100302060702130912110c2b 65
    0x21800101c10800201d508204200c043e0009a82c04008e100302100140005d0001e54040780030700c1085142e452003070007441464809100000c2050180012803181a51940780c1e5020903036a42c080d400c00134056a468030b41c15030069160145221813030307103441000000e0141c05052154082e4a0b04548074011480c0b501441c0030742000c5400040c60f40f00c031410441301d410420b200b0b50086041440800c200d9460384000c1410a405465020250f0b4800c104c2b00000c00e0742c070b2407040c3c440c01d029849035070710780c600d0b00320702d43c181e140032070162904a0200401a4184040f81d643c0321340da004010500115500350403012044040010260406030744440e80d500351003074664071000b5003180314012001d20100b002000c0c07403400743c60501d0a041c00d0001040000001c2d900019005802c00103c010841d00c40641842101c8060881040074440c640f50065442448500f0b8000060103d94050329102000c50240c204107001807000c41010358088201d0010803010007140c016255183c80840071501209940102d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 718525179 1106 718524073 718524077
    0x601090609030c0b09060d1803030608060f070f0309050a0b06012006040609020a05030d170106020d0c110f0303030a02130e06010c030c0503220302030601080610060305040507090c 79
    0x840c0c450220701f1808030f071615404022510080380781881d842d210b95030600081d0754400d0001c2d501c1a003903c003101c0036245c00011a1245004890141240c841401c02141c00700346034a0340c40c201004040d0581e0b03c54840420813050390380c0000f8000d195091014030702c0c018510987c25a60b212401000180b001d0b03601c1d100786055599001d44a002810024125081c080c4081001440122504403940e0340d0304420001080450000c2082200e502c1680e9800100381d14030345503202d070024290307001074210688070082086074500384020341c42804400005030303580f01c6417240c1081c11401648030004c445610014000e2681e40000d05011080e09480c0c440510911410214150310440e010103061141010021000da048055050222130007281994410389c8d03111070040d119001212065544500100e0500c65103000c0d41c051030304140940101c50446461f040020100c403809030750301d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 718345323 718525179 := by
  have h0 := BRFrame.cov_init 718345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 718345323 ≤ n) (h2 : n < 718525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
