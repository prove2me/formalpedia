-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0181
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:18:04.480932+00:00
-- url     : https://prove2.me/submissions/99e96e6b-453e-4008-b346-6fb68124f175

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 32374106 ≤ n < 32553962 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 32375356 1250 32374106 32374109
    0x806030c03031315030204032a05040e0a1104060302060405091e04120807080f0a0906020c0601031410020903030a050304061b120c0c170708130b1801020f0703060b0307 74
    0xc041c440003c6032110409044020300940d008240b00c1030080780000d801300d09900442c00f02900f02094404d034220291800d2070040317110038007107a40c1d841059443c1c2c0000d085801e01405148150080e8418408110f0740201d03080d981582110b08201c90750a607004240540240c0c09140c0c02418940c0200741d004454001c003054a1101c11900249881c041c9001e27408441c50500300c03004184c105c0d0104e6203141c05002000e200b030f6007901440e0126a1045224005000240029540960300b007100c8001d4450a125141c040e5000d0503621a1904201740007070b140c51100c40e43c1d040c890348103108114803a03501004036200b240341481d04d0358898035582000001170082c081d400115003c100c1c021000d41b50072607100a03808203c02010031a1440c480825610072183d82d000170032840a0a602e0f01c0583e2216002d410494008c06c085402d1020b05140c4040303401c2030740c0000c0e034008004a054030f4807111450002008641c00c0c4098000b06c2c6070095856030b9400c041c0002010795440b81c1d000001340d10308011090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 32376606 1250 32375356 32375359
    0x40314040b0408010b0f1e0f0a030501020d0207020f010804030c0215090607120318020105161a07110105060103060b09040f0b041404051516050a03061d150a080309010806030c 77
    0x956490341c410030f49000702003d0101a00410240c640500c41d071516643d44001c41c000b010f60311420456441c10810324182003460940d001c0c02080012020400c00d10181600c89110840140d4880303090041210103040715101504120880c4100301c0060390006146609a41c16600000590140040c4013541d000f50300c00960003200c0864840240311008500903800380240d01c5c01c0000c0c80154044143c0d034001c006000e1f0205200b0403402c0d07000c2d24035144c4c01007034030300645d14040110308803007840f08111400d0f1603110002c4c0e041c4600a610503000e21540d6000072007400d00b000054600300f02a8030034002c0a50003489151b58803c10f68003140c0d183c000c08032264009200b088a5444680a45440e0b0750036501030b10f01c0e02c10503101d081c40000078500c680c060b40781d60011224000d00d003081100e1036480b9502e84000c054503410001040000410001802821a61401c0c0b41d464007000040d15426004105c2d489070103201700400c000340000c411207101c3e080030b00c0d203402140d8400d008030785020b0150303a116 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 32377856 1250 32376606 32376629
    0x15020d06030602031518010620070509010f0305070e010e0403030e150a02070605090d050f03100f060309030f09150e010e130203090f0c03030d051e070f020111040e04031404 76
    0x31000c1c6001d41742404441c0e04aa10034a0810ba181403248048824054100400c02e162140d8505034918004203291982d02e0301190070058890700421070002e42a4440b0500644c182c6040c810000140001d03406442810700e404c2140d03141120b844803400010b00003909250340c81100c4002d444090020564801402c00041d1440c01c01c900124000d600205090304d00c1440e08010030320380000071544040d140d1301580c819040290044128401d03500180814100d880315280002c2c0f01d491030040640106140c0d1030002d40480d160902a00c5513003090150000c002d50141e05100094098070082d4103c0c03038610b40010a60352400041c2c0305420920032090348950b41e440c0039541c415103500210321a40e0400261415030b24181121641d5001c50203c0503031580003402085100c2038568401540b041414ad003800d210780020b11501131b071000c07e8400c04c000490005201c216203409014000c600c1801100f030360301d01032422119403558040a0001030400484880720527014040d07800340d40242c05c411041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 32379106 1250 32377856 32377861
    0x303040246050f0a08030a1407170a080609090703080d06090509030a170709030f060902040e070608071407060c02012a03050601080108150603030c0312060307090915020d0603060203 80
    0x10401d0009091266522800c1562038022050800740441000c40d403500e401542410202101039620390b2140303810440c8001c0501089010901207003114901c88a40128180d0395034070304500525611008240900615202080c040c0030840000d1903c2140d801c090501d03141c070541301d0928054491540b105888070b041c10b0500a802c0c1011005120400d51904d80d4a205102d80c0e9003151001c4085441d0f00c0860f040c2d00c4104081031285e002022010301c9940300190450a81d4009003c449130032241d085241d0052009001160b0080e4003190440b240c0d0500001c0d10700361280c4074003944a0f08078000c000b2902c4000301c04415000b5001030b05e0b0720900712644014030341c110294080064065420000180c03e200c0400c11550044182905940d240006071102c0540d0354981d010f586405800341350141700402601c80034280910207844a240c0328001d0381441e040020415150014541002d10060710700840c0000144a900f401c0f0180340a1000c09600c525492104000401b0f66a10103010107000208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 32380356 1250 32379106 32379229
    0x40908191814010804060b06070602040b120106030e19050109140604110a050a030222050117010f180308090a0f06020901030c1d15190c1403030402 65
    0x25010007000d00c0c000c841510303980c1d5210a400300c680881d01c01e0205031100085408034004e0340099407a0700d80501018036200081d0b481c01c0480c0c0c0194424482540c01041001c1d180400e080028010801850144000c211040d80151035031030090742040f6011005c00807100300982034100800003900110000c075001c01b120b900c642c0b1440c0c00c0b0303002c44441e0403074400000d49103498100d100640304043c00e0701040b0790540e0300f80102ea41200d00da440d0101c5000f000c6a5480e0482d001d518060004c00b07004226040d6400042820340704040b42c40090241084c07040003a80f48070b030004071005609483d04640a4a0b40300300503091420410026001040900560081c083c068000344850602130780d0400034403221040c00c0b6000040001034400d10804180350243c9843c141401e031944142404000d46400c1881441403130990b001401140411201300e420004c0c04100003c400070f0080b00e801442c5540342c00d41c0001c90f40402c145030745205c1c101411040c4a410324900f160034201e100503001d030783e05e0148040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 32381606 1250 32380356 32380367
    0x903070503030a21050906070f021f15081b040506150a020105010f0e060a0b0306060f0c010507021204030b070305070e10110606010507080405060c030721140a02030904090819 77
    0x1151144c418515080b24004100d5901c1520301c6600f0300f401a21840d281c00300c044407007a189101204c11071103400b40400541c0810030364501c41c2990910006480140007055601c0c14840341d016451075041103d42094844038040e809101600c00c4400140d903940e10000100b881e610401d81e050402d070049500c0410680552203103044e0303500d01c2104603100e5030398040a450303040201e405e190401480343d01089040c540502945e00040000c1040d401c1c18019003241150b50420503a0303101c0c40c0e4441060210b4150140090102c40502a800038030302400c5449043c441c030781c040c042200705642e40f0005140184218094803407070714001e00351081d001c0c0e50000242403810401c0c0801d00c600a160120390951f020343e04a03448103500160540c2802e14100400c605500301854030303c828001004001c1c0016080800600b24010810401520100b42d24005014440f002d54180711500200000044240c0000644080000c106c5021841030700600c2c0c9100d160055840b1512440d03030081c1c0240705241c010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 32382856 1250 32381606 32381627
    0xf0108011506020319030605101d03010204080d08070903080c030304060506010806131107061e050c070b010e04020a0314030406080903070c030305070f150204030201020c031c050903070503030a 85
    0x4802400098065a60454241164400d55026030300c10410400030000c10961041c540b00715040028507282d4542c00b0074106080f420005002075000303040d20441c1d0007150341c140e040c40000c2c1d0085003060704001c415035039610302c41c890b0400d01c5100d800081c40070f4800d42c0204059607120310360f039441300604514141e032a00199000c51b1403a092400003165948101c1c01548130744801811824003000d05c0103620001c140c001b90001c2c0c0403004005580218016000c1c180b10b00c15a0044034400c02c825081110450308042d0011175204410010030002c5203d09142c541503610b021142d46c055159440050b00440e49580300904000481c40e50001f080808005003007204c5071500d41c0c3c402ca0b528000640d480348141c40c002801c1150740031060000c80d200e20041d102543c80303512503c0c481019a102e03612051040d41100c0c05180c9c001a05008550f818414502c7c101e000780c0c000c1c2803101707040c68418030f14a480002d8200700b01012174601c40b82da8082110600030940602602d07514002140001c1c48038400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 32384106 1250 32382856 32382869
    0xe0703030807081504060603091103060411040207050c060703050a0906020a0209010306050601050d0e01020c0d0305060d0b0c0706020705060417071205030601170a0213080303040c03030f030b040e0a0302010c170c09180f01 97
    0x85c0401c8102b28100461000c3c8102c1c4d0042d440080041c0f80070030080203401464080d5141d00c80e201409103140c40c0c040c001d04201e4040e1300c07a10340307802e4044801072a1005a0b0040070454012502c1440140c072868041c41c10740394400340110b69a600c40340100c0e0a40038440309216001e041c002e40c204801e4044d401040b140754454291107600803094420303000d80e0001e4901079003202c1d500381c203040450f158254041e0803c0250080c9803a00c0019100e075000e83e0020b0b68156100d4000b4030600040000c5c41c0b0031803004d00d2445030310605201140d11801083c91408800500740b24000000070140d0707100d0760584110305841c055800c11410302c03078403c2d0000e4000d4440b250742c506242b50086244840001030301c1c03150b1b034400513802a09095a6044807003030f0f4048003080a060b15141240c6260f511400750180c40e0090000801c0d0f4402e01d07080003801d42d100d5104140030702c40f0a500d4203050400004406600c080084003280d0303114150301c04030b00450002c15032403003ca040306042c00310140035020003904030b552 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 32385356 1250 32384106 32384123
    0x614090309130b04060302090a0b01080a0902030607030c1202040e060a170d0c0303140c03041b0f05060f0705030406020a0516060504091503060204060f030e070303080708150406060309 81
    0x264840119641e00c522541e85500910207a09040c1c502c960303400c0003030b1420000e0008509690713a0340c00310318560002e0700c54002c0151650100c1540f03513405552075034011640701c4240014107070381e000702c0c0d1912406031207101056100c80115000c140190200e800c8810204411035803076030b80310450202c5a8040da21140b045c0c044180c0051000e401303056030080a1842800b600110480c890151010303030381caa504a040c56290a4110600c946c2000060302c207100c00784060b59070b4501403800c104008140400c00910007600007091140280c0050740b03205485c030680f070721a0341d00d40103048c001c46400b95074002031061200140c0401c0450340840c42c40c445900c508205c13505006202000120702803980501000540706000400c5404d40d207810100c0f1680c031220300400380036282e88528099902982001c00442c41c4d014821000715131522403000c03001c2803480940740f5113081da0790062071510080c180304d041256990114103100d42080f00030882480080c41000603590751400900508100b0405a55001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 32386606 1250 32385356 32385361
    0x30b130201180605030f1008010f0209010e04090507090207080c0105070c03140703081504090c09200909060402071b061715030706030c020304080102070b180f06040f030e0d0614 78
    0x12840c9a10b0140e601d030b40c81c1c0da81555184100381e007540100a050218004e0680760000e100f039006c2c0709407144840d640001607601c01e2030744009040d421044280c0d80c001c40c40d0060301c102150010650170705581c984031016035118001e0600d85000e000d54616040329521f010b0038052180c3d0080411310403540300743c40f00f1400031049500302c11203004180e000740208804400180d0207001444100302441e00003000010ac22140b03480390314550043d0b80180c404c06990780030038003001a8040e5141100d1a0804010f4581094040440c1ea00340d005012180120f401045800401c400c500d00070710203220200b00001d040303580e40e400130410584d5841c824401c03280304012070340c441c0140d0300c4142d092002400400758289000c03021001025240907076070840c00b0038000070820400a000511885009085218003420328a100f010742110311132010340340d5480244415000603004c070300e072644184c01c1203200151340300c1c505068862840310241070754080041614441003001c960302c20f5440312240c40d40004030ba0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 32387856 1250 32386606 32386637
    0x18170c01110a1a040f05010e010f0b0406060c2009071e0504230406180905070e0601021209030c04090506090c0103060b041206020c0303010f0e0907060509090709030b130201 76
    0x141c0120760043c0c00078881841d02c500a140c20600c99400c5803181c042c0d4029611581c682c10300312103808800c0115070751034656081580301140a4482c100c0c40840d800c0101a240c40006081c80024440c002c1c40d9010380e140801c0441000d00d10301c2448000075148441c2c42c0f87c069801005070f40e0003e00e940d2100c200464011300548103005640681c1e84801c0307110381c0e404903001d9401441e80300c0d500681d03025071501c002160082c689448ea1900401e124030120701d902c0c1300e241990030300406070881080300c6004000c210041e0380c0007a4540c94401450005940e41000d403010906180d101840950858188200401002030025840f40b084039468142e80302e003641da0004506440107485030510f501014401030002d00300408903000000e20400c001444c021005224a045030004d030302c40044403078014410402c40043d000c1c12035001728034901400c0d100303080640c054910b010701a0000d014a11000002e04414055030041d0061a00004181228541008601c8929610403001c80c0016a10345500460 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 32389106 1250 32387856 32387863
    0xd050304080d05040501090204020d060303081b03071b020d0b0604050a0507080a020a0302130609080607020705060412020f09010b040f0b0306030a02040b011e030203010603050c1918170c0111 84
    0xa141d20940042ca404800d604500c0a00300c05481580ca955a8010900042ea0303144000d041426100c4808504246103003009012030070001d0841c03550b0f407090000071504070440800c480e4048468100301600710209103030315403414240c1d48000c0d0040000b0311103805200c2c0120b08a0700c5042d0454092010342e071003104150680e00c4c2a107500e8080b8400754049001c01c1d00640190200200b40d02c0c0043c100801000300000340010356002c00c011949010003809441c50a00505502800d070380010b1110a01d000042640c2d88680d21502d0510301c1c41c10144411592851088013012200406500865031503100650b05070b070043c410050010706440c40015802449410b4074894072008000e4401e40045400307100180c000380710b429041105840c0c440c10750100d070114040400c0d245035001a101e42c10504050102d58001d40206442141070100b2030f00c4154485d22035404591078070700300110807810385200755800c2c440d40002c47d00c0d1039a0180d44104620008200038030000907aa954120070300c1044050307c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 32390356 1250 32389106 32389111
    0x7050702010c0b0711070b071e030e0d020d20040605040b1305090307020307150206070305010302100f02031606200a0504030807030e090703090b07080618060604030501090804080d0503 81
    0x400ca50004203004a190341c0c50003039020204d41400401c2c0781211700303082d040c00ca25070800c0142e05004184802845001d00d29402909200950400050010340780502200c005040c0c1512500f40541c10400315154104880c081940c084101740c0710b46821048184015104a038250189e40741c8800091540b0307080c000c0742200d00000d00702c40d41004000c2e90312006440c000300308114610080100c4030041c0c4007041100001c0c00d407004a0540b01c0f94409000b4100100900440101400d103401400907070341e0450484000350140c20203680035480171809a05500030780040c107a010000f00700c20340500c41d0303a401146584c40d900210900700d80280c0c0c500541801001391540c0004d40900043c40010101c00040c54614024205124550f00803c0021005001201d040000a441d026004100010120074540216039070a0110192405070301081e81401c0e200c049040d01c4c001c0d040807a0030750b1207140c00c0318003458000009000a2009082104407640984258030740c601c01e60510030710745440382080d00d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 32391606 1250 32390356 32390359
    0xb01020f0607050d050903092701081218120618011401080706050c100c030e010e0a020105031f08030301060c12020a1208040305120117010c03050f060910030807081207050702 77
    0x1030400400c0d00001009150007810a05c3c24881009000794950702c60781070740c07400d8442e04183d0808090f0a202701003090010f0f48900e041d135202c0c1008208980c0d200027a285103400f0060b00d80300c0d42c2c88240000305100c0d0078a5450050380140000d205910440e2031405180164032030081c031080312214801131042ca0244500b01503500004c0e014420940700d80001d20868612808451000000d1b8556008580c0c0b03005078000860380d00c0c803500c14085028003038604524183c00c050807001c01c0030303000030703007a840000c0881c84840704081c40380303140341030303004030701025103118000c480d00c03581c4078100070300b070302907030040030b8807803102a4003140b5901d4400100300c40c440e030b400400c0d42c0202a0a010a407241c000141084003400018000d00f601d07110202a000e000300111112920bca0500d4045038ac21034017654a42d204041c100400c120140036026640ea40020303050f40c030030300c203a641c52206000f090020f400090521a00207100e0b0300b8061000d0140000008810b95001076489104065615116500009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 32392856 1250 32391606 32391617
    0x803180609030c01080606120f070306140904020105030606040b03010311010908073f0606030201030e01020702010503040f0203030f03070801050a050901081f020405060406020102040e0c04080a060908070b0a0b01020f0607 97
    0x40000e520500805800006c090707c1e660815a44000e0060703001d50403500194203802c04820016415450f0207400c00038500140700d8807510103040c012070600400100064180007000010465940b105001c0714004c000d610f0707a45403203507182d250540210500c00c00c0700d40050364648010a0011010400204a0b103602c40105440c400c80d184c10144910502c142000c0c0294988000b003044040a90755004a8030451000074000c0c118030001d01211100c04034182168418010040180d8108040307940040c1c112100c8151a02140300182c950322030b084400c04419008000d101d800c80e000309496060301d50840d0003480c1140c503a0103100c17042c0c0007441124000d03401411104440024601140d42c91320007400b025191644450110325550702c282d20000c0140c1d4002070821400002c481c0c190b400c030706491440352404c0c1c0f52400b002c0d034a0b01d940d0741c081c1201d591280c81e9402c0007a41c0080380d00555200804076100d150011f500801480c4002440d03015008084141c0250840810301c1c42c030484040e00d61 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 32394106 1250 32392856 32392873
    0x11030108070e040807142506020712020307030210050d050a0207030c0605070903080f040305010b09010602030a050f0d090c030204050f04030816090314071707050303030105011d0901080318060903 86
    0x10310012010191041d079000c501003200ba800304013100b06c241000050280101450340082c200d65690001d5203596040215035101c09000e2030740c1c0070a80030308a809000900186075220300009040c1078542e0f0009501000b54075100280d69007000c05807101d01c44c00c0e1780400099482004070b2041c0c1c42907807001000200b420320b06000003401a40a240c102441c1c1c035040480c0d0707440c0d6403108165440012800c1d2a404086001c00400c1400d024032203803d0020340361186c2179450510040e41e00c2c000d180803041804000b00d48040c1c03002c5143e0540c0c240c540c0d1020148030030001030502000c0d0100a000583c01503040030006001001000b80742d40c041e60345665100c82c181c1d038090b00b680c0c218400762081b4080040c200400004541002c0d4199140b004603005070070b9079840c010b13110300a0940419014403d40040c0020481c0f130303801000b5a411540203003810340d248000b00034114841c820b01c20400d82e101a80000102d180305000000e0b102610314010060100b000705020030049002d2100c1480c0e044d84480d02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 32395356 1250 32394106 32394119
    0x501050304050f2505150d050919060615022b02070306050a020c010e0a0302030403030311070204020d050403030b0f1302250f020f0405010303050313050f0d0e041103010807 76
    0x310350060060050f6902103844807012401d080c01c81c65450041070560042d1064001c0c00c0d000c003001004100e4414240009440300c0f004540503040c050281c0300e40c0d03400080c040d5601840741a410345003511409019082516040004180c28007407000121011100094101e000049041e071801d20381d100400003032601c2eaa01c2001b801c00c0b030500707000c50142d0000000001c8042c0039050003104403480c0580c680548903a11401c4495115100985900030700b1000301280c1c0100032070382070300c1d0180f40106030020381800f100b005101d10a4025040f5100240320385902c3c000e030780b10a001d248a542c080c86904141e0040241c00281206141e5015803120804954404a81c1c010700600f40c01c14040a14030000c900302c403104040d00e080c01d6840c00c000026520451030300007029014100110760401c520350550318018140d010050988140d1640c142d4a40140f10082020745c0c10303a50307440b044602118402d40002d0410ba01e10041c01d00644c140070070403500c1e03061601a00d05980c2d98000504140c6e14090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 32396606 1250 32395356 32395367
    0x60815030705030106060804050f01020301060f030f090206030703020a02010f0b031b0f040204030c090c140403060903090e01080706022a0105030408040806010b030412020706020d0507150c020c0a0b0309070501 92
    0x49859240c41030020005140d1800c1c082c450050805446298191416007445404c1c00c0740641c4a1081d80d10402c014840300f0342101968103411202d00d00000e0b40ca12441d11480108042100658400340120401102903410303001003900383e601c1d0740240700602241c3c0b07c80058a841078115a410b8009414507290b10b0070108008103020002000004149034110110b41240d00c181c000303907011008160140030280740d9028001c11702c071a910300302010240c8000200318901803800700a00e001e4031044a0407d1520801c04d041c00742c00418079019203940d641824030798491079445550094000c0c1056504070203907a80064280d0800e403c00b0780c0e110b0100c0707001129170340d10081040703481040c10f00011030f80d24000c002c61030103000c19190303140d41c03130800b8140716203800707050172201c0115840210107201030303940031624044810003414219120002c600d000b840e0740c00d201a00355106441d042840c42006c2e0300007001c80340010b094450410700b40d00c80707880700d40d0381c0b20031141d40d14640d1029100704415489407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 32397856 1250 32396606 32396641
    0x1050415090303270209070804030c1205120901050a060f0b0f130b07030228110433030c0b03090606010507080903010504120908030c061303050903121309060608 71
    0x78540050f131002101000c0c007122200c144401c1001d10000324400c21030030f00d002d40c0c80c3c22000174180180a868103607802003080140d044000c061300c640700f00c1510864040c0d0143c4109180e40d0b060000b0380e140c0103000328000d10301107c40c504058209100010040c5100300c2e41d2041e01e03000f0013118508100d003001703c28560300009501000000c600c0c000550040c00002600101c1e12035030240c50603803803150801017046242e0082d40307072031580b0b801d514001546c0f41094480504050340c001c1410400c1d2a00d14a014401d800c0c0ac004006e4500a4207801200b501e00301004d59126000041e801c2c1d071075400314141404111600315290384650007042e0a0360007000039107101c500c611034440c5810900800702382942c106640c12600000d0041c050554650821400000b428180300210306000790b0079034039503481e0005080301c2a40d01034400c520060500c5071045072000342c00503045404102c603010580c0c642e03a006021170000c100c0c03a8140451005c1c1c2c58000d400464829969000702038071031030048610340d00c50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 32399106 1250 32397856 32397863
    0x6050f06040b01050721090f03050703120509130c030b04090803100b25020f04021207020c0103020c0a03031a0d03120c030216020f040912050a1d010804150e01020706020316020105041509 82
    0x318071f00002c1402d09000c0d090b010350300c100c001d4080545103141841d110400303164514240700d0140716a80c5140c803400010940300108a6020800040d588410f60041c034440d6003580c0c020707041122500510408900460192001c040d4400890303940d480e07084070700e0080030041007d800e104c404415407240144504015107000500c0306d40600240350000e01281d0040303245448441501e0100701103a601402100200382080c2025894206046d55494541c0140c100003002c0c140ea820440c00511040c26507140015006481f8040080c4942000f0f000070021281540d1014148402c81c54818840e00179210901e000e040e500c042000d103542040903540030401802d0b0031a5940c2941e0703001c01c1d980c1c0411a8402229160b059440100030f0008080600c20110041005180c000c00106230360f00642c51076202e50000a000b460f10003405115000e4074030f40421102035070010540d1401d0080541c001c5014035854412444012146e600580c01c1e40c07800c590242440915101042c444480c0350043c81d8107510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 32400356 1250 32399106 32399117
    0x5060306061c09060911090c1c0209040e160f0302060a030e011407090503100e07090213080607050a0306050405190b06070b0f0103050607051303110d06050f06040b01050721 76
    0x9902d11981101c1d1980000d50340b0f00e0f101e80400d014410740d0621200e15400a450380c0ba091700d06191445240e02c500400528000b0342e4803c042c00180c91503050352141d07000100280b0503503000c0f11f0920307a80c07070440c4400035100110040000f8110701c00c0c10050110b80d4050252402c0200c1600305070018143c20f20a00c0503552202c5208031101c8030380d1022441a05a0f46504600506040c02d0602d09989070921081140c03030200f04046145002030541e0803500345030b50260303a6081c3c283ca20b514a02080c0d1110302144160004c1c0041c9070340080242c8400ca259560410010b81d4444c10002034410a030b031010104052000813810b0110949c02c030046d0a0006420585800450383e941c1480f204210f0f12011840488001401007084c14000d46410041d1481c0450602128501c440c07004000752000500801c55100688171030b8481d101002000740d0400b00801052034124a05510311320101c070020f102d58034124040c600766000c0c1044c0c4541907003084109070301d2100010913001d1070301e060306002c05210 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 32401606 1250 32400356 32400397
    0x80906040b030412020f0f030d09110303070302060108010f0c080402040c03060b070510150608070e03150a0b0a050301020406050f070609020a1502070501030501030b13030e040203130c0f0506030606 87
    0x105600002c5000c0c0707110304406920001d01040080c200a0f081040c11041d41015840c00100e0100000743c0b0070410801e40c0004900c12035290442a002800a0003a098000400d0103414941c010030141c0c1291202c00007405182c00c010000801c403400d1007102400308402101140142c01c00c1e51002220715440e041c0002ca040d224032500c81c55803c5004125201e901007501c0a03070525950181d46120344540c10007590341070401002812084000b00400d0800020b440a140266010001d122051078100010041d90508050501c050039002d8886802110301100014181c18140300300c900301c80f042d5481c0c2d81084031417240c8090300e40c042d50080c1d4010b5195400400580c2d03500040d00000c0c14090880d00d8080e9060b00e019090100315071001e8140340c9013000400105d49035000995000d125004000b9a0004914041e070300b201092050981046c400b1081001003d00701c42104020781c05020f1065285540f01d00c054160f40c106d004440d003000d818400b00d04581804005040086007503010a103026 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 32402856 1250 32401606 32401619
    0x201110f0408150c070b090102120403030903021516030c0e0301180c090b09070c060e070f17120d0b030708010c08010e06100f051e040f031e03020a08090604 69
    0x2a0004880001080c0e0300103000c10001804000d4a002c1d5101100309005030310b001c0c59011014018140301400c0010014001007480b02c080d41180c44c60001111500c19905003400d00400504090108034050703c41c0c400e44440960b410f01002d88034040d000c148a440341d078481c000302c010b00781444400b01880b2142c212450f541da000e006031284c824090100c0c01d44082e05081c80c900280130343c0d01c07103c41c6c0780c64004280c0003912101a019070100550404010900315441d1080003401030607140b4401d4001c044c1c0200f10314400300f4003003003203400308401690420007840321035485a40c1911880743c44882003000c0d20824903250042c00803408020107544143c3c2d9640429420348007107442e032b64005010742c00140031800910f908a90042e02c1a51001c0010030a6400074101220031403100c4148200421402e0118660386429501608540300f03082d141d07680c5220f00c00496100d40000c540e1841001145855407106544130111650142e000307024a051a40340da02c281d03032124001607040f07101000046800f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 32404106 1250 32402856 32402891
    0x20f1e0c030f0d08070908031204080919030303050709050f0f0d050f0601090f0905030d09050111070807020301050603060c030c0703051b030c06070e0a0b09041b020a0506160815010201 81
    0x404220340042c0c039089941040060113040f0091142050010280042c4900b060020540300e551304d115001c03400035212420480b496006400002e54002a2813981c0c403407600000c5161000c503442a103060105841c2c1040580701c14820340290b0ba084204086401b01a01d07012078806001c030805001041c60390201e8803641d003081d8107007034001a035030f01240040100301c94922031101c0414010714101300d408030a07900c00c0c0d02c9210f01c1c0d01c900d007104d844403261018004c0a61208840800d40c2001c00e81d204581d1414207035581120310107a100e9464840091007038207001c00c12500c5a8403250040e4034590301c1d2461010300b5080301c18140e00b005001d000b6403202c0c20740102d50088552042008580b900c6542d07040601c0c0ca08001d00c40801c001c440314050764140c44041c0d03030f00e080c1c0300060b5405442d546a503010a0081082c0402c82000900d2104030842c403a402042c2100e01500a00c1503074100d540e41840c0c02c152243c0141c085c80041c542c04001847d41208074000307203143c41e0520020a144c0301c04e0300326054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 32405356 1250 32404106 32404123
    0x80a0612200a120308010501031506050318010507030c090e01031a090102040812070620030606070f0203060c0909010b030115260103290103050a0803040206070b010308040f06020f1e0c03 82
    0x8403407402c9028209045e004006640101340c24a006d211071038900081c1c01c560900b038803c41052040100201d26041051040e092084028800802071032800740030080140961042050100300341c108081a000d009001c880d041c0c03604086090400c2240a8000f26400030040181420303550900001c50400818021919021105800f02d9110714103804c10300225482c2d42c84c1d51601e60840e1440a001040e050b0549500c0001110950707180c0d07149080507941035210410095041c0a10010400c7c4580200d0240c18800030640c2c1c15112030b80c075401c000300c244c0301c00c0c01020320510700043c0c541c1c0c210744200450450030b2916100b01c005d0483c0120402c05003007007a081143c036080d00b40170f03030700002c0504007102c0380004003240904229403440c1c45540e16800400405004c12000000280035505c403081121070315036210801101a40c2d4030f080c142c1154005000e0001017208400000403000c2c40041e205203000341200207000780a64001540d4050018004010300c2401401c04940341542c06020011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 32406606 1250 32405356 32405369
    0x712140303070e010e041b18031e060b06040821040801020a080f1005010c0b0a1107032604030e0907110a0305040f05060705070b090109150c03080a0612200a 69
    0x2803950100364009003281c1c170405c0c403080c040e40ca482001c083c0c002e04a08640840300450805200c10300c50000806284c03c820382000e0065880200d00c410700d003502c503100c2c8010300d000d00e0382003102c0c400e40c4003042070354030440c40b914909507c450007481301045080c644d40030500004c0c84141c0382581e0b80495500b0790b00958090720100b210142002410001c02c40095031204040600745a41c5082800281c251030b05000042c00e00d011900004d061400e45034060000403840c2060540c8584032880d00800c001c11a0290400c43c14240011808811910010341d00556140d00c6002001d9800001e0284020000302260700300060700c020345402c220f052265000841c06940c0f416951030920264a14145c40c83d4010360056200700b1000d03001c103501044030800c0d80c4074004200c0c6d503078510308012141100c6079044040c00200340d41201c0442600003002e66021442510380003001da03034011012048910310b10800005102091100300060000040074100144845040c0c001440701030124884070850703041381 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 32407856 1250 32406606 32406617
    0x2090103080901090801020306060a1404170303070207150e04020c0705060d0204090b06030103111c050706080103060b010e0609150f0c01140c0c0312060d0219090c0e03071214030307 80
    0x82819684141d131400038001001c001d510350304000d030114020303100b4041482c0802940007007c422600194003241c0050915402c5481148041c0c0c031103d0700c82c1c0c4150740c503001504c51001d00207032880300940c0940103400c460711080d00c80b88601040c40082c1d4000060b07200703280101400800c0c55540c00000c1d280c8110090390060702ca5061480385030841e101e07070b50a01e03c181c1090004100086c1c107199542c600d42d4040c0d603040c40c103403892601284078404051000380f05010300c000200b02d065001030315030f040780d024a10901050000c1001501c086810000054011400f04001841814000084510002401882481c04100140100c4190040041894541d4440c4403600b00c0003445040c141d080304203180043d1405541d0309000d03617a44100c801c202d802d8507500000900559a015420010303d070090030320341180710491560303100315066005040e90207150040a00503144200300d41940200c015006041103814000c2005844205810032520f850b00d42c0e030091025101030028502860b0310380c50300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 32409106 1250 32407856 32407867
    0x80f04230d020601080f0705090105040908040306020c060604061203080601050c0f07090903020c151903020d0f0b03061602060a0f0605030f0c04050c12070c050c060406020c0a060c0317130209010308 87
    0x1d05d4100403080005518941c0541d0040c0302d50380d42c040846046400131a8000340d00c00a520340203516000f03d0740060404c40c4041007000c1039681c0410481c1c031441d0308560402400d52100000d00a01c45420800f60005400c4400104d403940200000d04444444904072034080024079000da140903625004400865254020381e81055010004642e024508442585c009960303060001e0840c0140300310444400041499480340c280650704803014802814000c0c007a5405580d9190041c2c94031014003402031240400040c1c1c01d6900301110b5070000c95a90240c440c136140c0400c03d402a10000740070280c120741c2c481c4006403d40c0c0400c007090902c04400080c00e43c5109441c104012140c2c000c14403418200e042103504060f00e08440150391001c201e052041c2d508220b810402e2411101c151401d801c1200040e0200e00301d034001402d111508022a904540103847d12821640b070040180c004012945040d0320441c01d289150006038001c140b8414008944587c0d000030305880000c0c0c1c02030300c8801e80000c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 32410356 1250 32409106 32409119
    0x111c0e010e1b041109090a0c0302070b0112050c04020913201207020106080601060e0405040302070e0a060f210f0503070204020f032406030a090201180f0510080f04230d020601 77
    0x40c3c0c603020041303420182c2002540d02c081000740b48014041081c0c203684608400300c050007681031351040340e002004000903607110f910080250301080420b88442c03141a5546034185014003c8455015014100f41924445001e1180203041030200c85190f801c3c103401c10462904000d030152041081003104400b1509020b03201908451081c0c0056071140c03c2800103126068100c1260311855400399000070b41e030b80e12401c04031b00300480e580010006100c41c1041c405034904503003024051342d80d0004450400340da11051102111400896905442d00204168010980031011110004d004800381c4e0302e0204290b0002e42240d01610759000040b40200c2405000e80c11206407000a20308801072013204200b81c4002889400300800c0d1282a980f10107035030085901c9131400400304080520564030f004c0e201c24440003e040103008840c0600160000e0740b403854480c106260240c4040350724940144c481e51070715401c3c25100004016504a403040003404500200061a0002502d03406003215505120 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 32411606 1250 32410356 32410361
    0xc020105040209010e04020f09040602090409030509040f060f1217070506160503070c06050a1d0d2604021e030607030509060c04060905090402030703080a03050a111c0e010e1b04 78
    0x80001c420000905c0412005880300c103503618900c0c60440b800c080c03e545038a4198003901c2440607403074001d4101540c81007050f8001c000340c541000216401d1100c101060a4001100e880d481280d0403080030050070060044811410450300d40180412100c500c0c602c8030740d200d03581c081c1c401100da0394000400c01090319048580b020a80701c1c140390041c41c40c2000d410007407840c0d1500704050100c0e6610380200b400c8038400da02a0b40c414100941c10501c0000c0207845d162115044045100420f0902100010070b4920f5161003012840716590350b92140c65a800f84425400010221004012441416191a5820400c2c14410440b66402080b5460450b00c01410f041c0003500001c00840284001d00c00c26400c0000101524400d44116602d541c440c00001d04c0d1900c182c0c000b038920710000a42c6401d10f603141e00907a1107030198040c14000101c403920180b4061081800b458a8001c4104144a43c0d4059400c8042900107040011030400c450070052410310340340001c81102c200c184030900e1018140350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 32412856 1250 32411606 32411609
    0x605010507050607080601181206050a051303080a18060218030f0d03110d020c0f0622061d0d0905090c03040b010e0c040b1801030e060405070b0d0905010c02010504020901 75
    0x386811400c000241d5500340e0307201005031141c1c040c0072429001502c0399204100d100c0c402041d04101110710360795001e0741c0e043e22803170540c15900241003400080b0b108802c1d028a9000715040f110381490441c03541c9080b01d007408040d040640c1c4035200d0804080f80761403000144030440c06044010f0b0fa0b0410b9100c2c3d81c02020032280e540f8083d41201c030b1440080c0b07002043c4214549200d00f00441d0030002d51101150f54072a00207000d040a1000c83e4030700350b0400000d100c0c1c22041c20359084031030a44400300d03016041c040780c0005c0c0c5001d000c0c00900c0c1000500e6500300c5800100700d042044078001c040a40b42d810301241481000001e4035181d010070251620300e410301d422000c0d00740100d1a600781380d00c0712046c44405000d600703102551000451010310b4200c0c200c60040c026003a1107511640c09014a40c0083d40070051240001c0c2001e016041c450004981e16003e1940880140045458600841c10f40d400c0310b94640705080d0342d00d41200203d0750a005020000c03400d40c0c000619443c0a104100c10948107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 32414106 1250 32412856 32412859
    0x60215010506030a0b01030f021803062203031d070312031406030a030c03020a05010c03091103010203150f01020f0703050109020405010b18090a090203010e070906080102180f0103060305150405010605 88
    0x2000042015484880842c0d0700800507407008100f0000c0000140c0290900908005040b4400034000ea00c4410b10510144801e00c12021340e5407903120070841c0e00100015001c078074603901c0c4140490300044d0095010104103540c614209205100341e544e9581044000c0d40180c410f00030019150003d01c3e85440392031466020040343c000c2c2800c0207004260349010b840802020f1000d810554030506008102505409902400900030b50052450040103030142c5501100c910980d0f01241c840c61a041c002d5a00c00e1064865289108008104020166a289a287c0d0541c051112524180c40c81840007c0145011710000700d49204e2500c14441113420503444080c0300441480300030640e0004c94018400e040f001c40d031000107910342c1201400100545c15000b0361540c41c2094800c17074218003080090880b281a00c0412120703a690007900d00384e11607124002e4a0500d1941c042d4407d15140b034070b00034841018900010202e840c2d5807014600b4005a03442500c559a0328100001c0100901810740074100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 32415356 1250 32414106 32414143
    0x70c06080106110a15060506030114040c083306040e0910020a0504060804150e06040506180a02090a11040f14040204180209040e060a0e01050105040b0603011208040e07090602 77
    0xf00780e0f9158082404003d204541c0480700c40c0d009061a0840005403000030b2540e17640b03594482c40080c11800c03c00c9980c0c002c500b028140e040280c0542600c0d0701c030b0540000701d409011035030080210584002804842c095642250401030b03600d030b00c00900301411541c1200b0f001424003190051803e00c2d440c00c1c0c03030f807103600400c13032551100c0e840000e440417078940d41800e0707000e80c8913882c108194401c048000c00042d8540501c0440b4000009000d5000d640180240c50054645412681481003444191034490380079113035070310050500d203c03a19031003c0020000034111125280103115903206512101145403501410310000350480141c806884040f10114a00752408140c0c03048420fa9000501304a68042041209500c1e10f40040003d07800b14015140c8610b400480c0c08001c000190106150703601c0e1900116060400380310340e082891b1300506180c03c5078030b044142d44443d6403a2030222860b41050000051350300d004030003180a040c0503140d84c0c65050070711708001e240c01300c0600403116006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 32416606 1250 32415356 32415377
    0xb06040b070b180a030e330906070203010903030606020d030e070603090203010f0f0c030e07030206031605190e100305190209030f060f0a0606090e070305060a0b070c06080106 77
    0x10040c20484051503841840070324a5501c41020403440d05809188403502c0c080d0041900405910012040b00030100701e914032050105040502c1c054124003005101000107801141980032211010b040b004200130141441c10303001e0340c00700f400d5070b40c0320340c00300d010036102d2100340001030b01413001488980c490f00c2d040013842c407038050480d600e426a1180c401410707501c0b24000c040d51405e4106c00e140d054400c0e000e10042d0020700c0c40500403c100e4601c8400603150070b03246041110041484403c0300c0c0c0041681c1c0c11030320307601d001c18002c10f40c5c3c4c02408240031007000f80d010100b61000c000140c201d203c3d110080d03041c62003400c1c80504c889a0040008051a240070040c101500b60f2103006600410017006803601e00d190007007841c0091240d6500200c1c41420200074582d072418a4040c0f01e03140403001446025a25241543ea01c9040e00550113414003030400591210320940c03000e548050001c00e003e2416076114079042850b0f0106c07100b52103d410703090040c801941c000c280540100f00500d0440442d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 32417856 1250 32416606 32416619
    0x1507020601031b080607080a06090603080f0a0e090108030406030b0402030906070f030e1005011a0c06010603020d02070f06020903010e0705010207090e010204080f0f0c0604030201090506030405210a02010b0604 92
    0x50300c05002c024560103610809a404a118510010150481d1320454199003400c410242a40c01c040b5514180700c3d00f403280c045281d460034054901203aa021f84000d041000306188454142c000c040d4481c00c100c41c07040901e4084da030311002680200f12000c003555456040010041c181c8490201d014051030041052001410001400c40c0d441203c0e07240400240d0030800381100503207410000e8180ac0d2245c1c42c07000c8181d51256001504880d2000303070b0503c1e2070b41c02240d410072601400115546c20381100c001080018017a80003028032004502c00107150401c036070b994010388829800306a68850f070202d141001070030248123034090b0020f0f041c000d140300c03448d00300000d65a0415001e180307151a2a0700e40310b074060609405650240030314200355516003001120080d07172801c00840c2c6c0180d9100b0100058517a082c4841102c00b03480d01a03480d000c05900b86024045658000341c811541449070300c1084424900c0204514001064041134030303074813280b000000f401c0d0f4110080780c0307126600c204810000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 32419106 1250 32417856 32417863
    0x51801091413090c06030b0108090f0712030e090103080d0b0d02030c060a030608070608062416031b0c140604050913031106090d0906030504030210020c030f0c030309150702 76
    0x71103030211200755101554200070006400c10040c014201442000d0109075203800d50801080750b5020380c2e842c100c540d2942045503491034506000c04082d0803580c400e001100c04900b03902c4005000341040001c600e1850042038020400b60b0065030101404540400003850b18082c99405400440c1c03d84107c1030140c00181e101c901d202c0e00c440c89224001504015103020b40c00140040070008169407081c0d0381d92802038000581140d07180c0c45882c0c1d100701120002c0c6091794000e0641e142d0754500c0d041014500301100103031400074054091081500d20090040c2c0b1000c03c5601d030740d210f01d102201e881c3c0b4044040d0300100001e210148503485c02e10050009071180c2505c20340c4000d003a90810740c90341582c1400e0f2465013410602c0d14a500800b010080d04240025412148113401d56500401607500c81c0200d040303902c1598000c0041e000040070190701000c980180000a0080c03042d80e1900040d107440b40d80c11342c48440182829000801005280d1105100e41080304055000500c00b501d0060340007502d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 32420356 1250 32419106 32419139
    0x708070f0806040b1302030901091a01030c060c03120f09060e01020a080a02030c090907020102090f0405090d120b040c110601060c03051b01060b0304060902030d090602030f0906071205180109 84
    0x61039607420341c41007683d1081000c458032640d298003151f682c206006200d018001030070050315040c1c0065802e1100c43c0c44040080d0403250408562810f0310300382170007182e41032041c0b14150f00f0444240e400307038135000c51441101810007007044005440704107407801d0001c2d0b07540306046582503441413040240080d0804100390740255600300041c2d43e0345c0e50103c0d9000d58000d110b0703a5038005490700c081101207a0154020708000004542034840d2940d140100425103004454410341c1da0800041000200d0090140318030181c2c1c0b1100c00308111000310080b804440d0001c1c10080000e1903551035001d03c46090004901401281c601003030710110944018200348181103a02070010313002680d4104414017035204070041c109900707034580d40b82454207083c40030706000c80050b07220340940d240e201011030007a000d80e030446980ba00a90f06000d0920110302c242d820800d07045401890800a4800158120000303580c5004581c444903161a00c4490001c0e89403d034801c80b50501008100901103c2c04030140c030360 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 32421606 1250 32420356 32420359
    0x1020307020d0c0813150e030303070509010c02030f06090309040e060907030314070803130221100b0d0c03060c0f05070510020913050406050a0b060304020609041508030f030708070f0806 82
    0xb43e1018900d8404c0c0365101d000c6140d0012076800301d02051103900d0144072550605d055640c10004d0728520105510380c4015130305500820403c110360109540519524078901d40003e094815400faa0340c605800c0c00022280903450340c01c0000c1e103071034910700741c400e41d100210544000c01407880c4c4040c202e03654007a2408060180000c0f000900282800141103c002a41c0462203a4483c1005040b20708000170741d220403403044507055400060100071018070030014940038014030302483d001c24400c0c010400101002d0304545032a030100d010440c2852100001d501c00c00c80061200c10740b00000b05100c048800b00000c2180c20098040410400611aa80702da00e2200060380e8044100c00600603c10524624000d070f410720b810007061010a610051052100b0390050101003041c200304800d070312003120000e51110707050042d2041401d01d94080c00c0c2d00c2e52500184891191201d1280707195800c007402d9451288070000802c225540d00c02c6615802402c0340c03d11440408150501826a620041c880d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 32422856 1250 32421606 32421617
    0x60f0105090405100c050403110d02090105120a050304240f0203070210170a090308070513030605060a24021c0816020309060a02060109051302030a030305040501020d180c0801020307020d 82
    0x1070511005110404000c4d030805010000520381d003202821680052100f40c9d91810384000c2400c4a0800b143e40c010065402081c40b28141c0c01c000c1080b0202041c040034156911030510943c000910400040c4007504418900c0c2d8110007201c3c50083c82c050303030078031500200a00f6821103400c003500001522440da50444800d2841c2d0b0040e8070413610203d48102800d00b54000c202480031400c84c5500240b0041d00969806ca19a950a5020384162281810b00700d22445c80250400110322240d00c080c0c0c010800505500b40240e80783e15036000035060004c08005200400700300d5180384c0c2c0412180c42d42140c6c04008e85100c004280e405820b540d0028503d101058404101ca83c02a20038003c07260091001010313079490b520030840017907440d00709000c1c150005180c0004241c810b450180c0801900e540280103000386640755400320040d0501502c1110559000c3c00000c014204e180a052108403415005c5459009241000840040355620010040e441002804070041c0c2c041a1407642c80c00c1030920 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 32424106 1250 32422856 32422861
    0xc09030d14160f0201030c0e030709020c031207080a060f120201050901020c1201020403030e0307300204050a020904141611100501030303021b0705030c10030f06030605090f060f010509 81
    0x40300e4180710308019541d4a071903405900c400c0004104010f4415030013030381e013042042e01460080c1c03aa1117540410780d61541c003c603410094100607800601a502400d02500d007040007403010320149000036118030b00032a450b0801c00002c1c205900c5403400604200e04c00d10349440c6040d000e25681904444080c0c10040d00040e400d203164020420908083c002410300351001907058806030003500240000c81c0040e81000d11340344545000140d50081e80c0a65041115103800e002c00b00ea075961050504a82c414158120640075940d2882058422059010090703500c051038010841100e419502d81e42d8049420070030f2040481f41f00c0c050b5150800241410340c02e640d0315118542c504003a50090340c000c5810f14001000301507068025221304c2000c5481040e4412001c0c56160312910b950142c1a0950b00c50321002d6002e242400c40d81c49080f496040c00140402281c580c2001e0303843c10780054030703e20b0f1160140040b21404101d0314030a0801e0601609188c1014a4000a00c51042c42010700c02d2040030007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 32425356 1250 32424106 32424137
    0x70609110a08100c02120405060a1107060207030b0c03130b09010f091a060d0503030703020d060315090b060a0b1603140403120206060d0302060703090606050301060303030b04050c09030d 82
    0x814129054008048201040d03449011680d56043d00c1c141549403800c2c2041000c80c41c0c000648803d00401c0c40c0b030721a080c1814001404140c0d0043c010007400c1150841082078107501c1030000d4005071040d0b60141002c642181445030b801040a401003144007000c0080000c07086603204041115039114901c41c0c034a072200f0035018003424054600301328170f03450540c446040000c441c60030740c00750f912000020035030395640040200603150030b000079009400030000105401d110f640104296000d070500040d40a442e5103600d40310118050b00345103041d503900140130a201e5002c1c0c2055100b8030440d203444134030f400d2182011a83c007030207601c002440c034103001071010580154407568032042c500c0041c0c0d440300e68905040d001683d1a0104002501403140860440e04010803040b814980540051603a500c58080443c001c0c14142001d841c0c01c0d503a501c021170079a8080c042c19001354000e6501041256401c400c0000b11100a0142c5982c10010840c4440b82d4501082200182001e410414800c261800b03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 32426606 1250 32425356 32425373
    0x70f14010f030609060e010302030d080105100807090e0a020c060a05100501030b04060b0705030406030c0302120f0709172109240702150703030e01090c1203020a050102030705030402150f070609 85
    0x10130950003581031204c01301d110004010301904880c002c90840d00c1e9003110200a80e4820340a00410742c0104a10101120150041d820160005081d00d0454242d569521080c1489002a03410701603198002601a040c0d0701e0400143c1c0c1c001d10202810030141c2841d0314156035140062065030305041c1c0301d402480555942ea8400b10040c4181070701a6502c09061921030b49a6025008940c003291030703c41c003141c490f4868401d55808100c86c01b43e2089684813010f0403a100c1030010081820051030312004180304681c0300d030404003262550000d00c2000b2901d0210f089441c02c004035611500c0c0306200800c602d54549110040f44c1c4c0c508880130341207a00344640c8018a101725003003e50401200400012030202c26801801c04c80e010380d50411074030350700d07840309800d8803d400c001610000711440244840c801d12140030445074883e00484030220001d54909080e6002150040d0100c1d002104120550034020591140b854203440314030f01e0481103900c000282d01411001070096941c584501c010015100b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 32427856 1250 32426606 32426609
    0x3090303040b040e0f04150509010b130e0d080603060a020913060f050103060b03040b01060509030a05010e07080c01050307141b0f01091401020a050403080f130b0c070f14010f0306 79
    0x140a880d6100d0701c1d411848143c0e44184110841c5640c0e43e00042c80c2c000750528164041e940c8540f010202c241030b401c00402401b00500301d11115540c441c0781800503664910021446140c000e40480d6001d400c0365114100396150301005d0500c4804003c0000580d0041007450f0700c51020100181c50340a00300200307420585440d1010311040c80c161011a0350840003400800700d0744240c1c0e0903c030003620358012180c01c0c00259402000340503180c2c0107110f107600940113003500c0c050160842d1001d20046d101e842c01c2d40e2527082d03034a41a4014130320a000b40c11041c44183d117150000c1c00c3c07007455410141e10040410345180d4120b91039000124042100402d9840c000d40c402100c20211040d010121090b01e001303100b07a500440d50850742c50f11014240c0c6041c000c8da090480c82d9203480b41000e241d500c0d072a072140d0041000c00300303818081140500020300f007001e01000c2c04980b50420340303803241c1c01c1038180303414002d821030f200130700a040d010040b8410740d02003400210000e20740803141402d0b1240540281116 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 32429106 1250 32427856 32427859
    0x60b0306010303080f0106030b0607030e062106100c03091203020703060f14010603060605040905040212030a020a0302060f060d02010e040e0717071403031b03090901090f1d03030601030e0309 84
    0x109000001819448043c1900602c45c44002e4805666603000030313002c440d0304c000140d400c604c0500180c40480c2c0151414802c1d110064030081c0b40070075400b208c2403601c08282c28003210f0000ea805005044c00c00e82d4800c9000360040c02c4c140b00c52202d688000c2c129000398800c1070741102c900704a0008142c4240486001164002c8040c462600d42da0813842c06030041451080080394543d00008541e0310a01980c000c4031115140c591400703041ca00c000d006490002d005a8000072a82d1030211080c2c1e0410007408010041c1d80a400389a00d1441e00900301440642084500021071050000342c0c0c4d030300302c601c80d64a542400c0c0b0429460446020030701400701a002003069020f0b080c400210400701c01c2800c1040c240032000e0b51401512008e68800c5101c8200800b40c0507882400380c000c050b03050480e2800d98808010441c2d051a11590001e81e00030000d0700500c80c0c040c2c48000110710056103020364030310780312251100c0c03101c515440055656030200800040c10191901c2040e04034070340a000315a00c0c50310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 32430356 1250 32429106 32429113
    0x14090f010b0711100e100e1509010203160b100911120403030b0d030305100f1d0603030715020a17131217010b0901080c16062a08180d080a020304060b03 67
    0x554940107024540d4070342002e401100791b401401c00d028415030000d041821b000780b45c0d01e940a2000c00a1343d0b07580001d09041d06600c0b0411108100c08110940b04241c07921440307140ba11850034401c0e4481d00a1544d0140800e04d08007000c00003a14080c200340c0b41408118000c0d0389166a55003000c501400e144010140c00001100d90f600c01d1540c035030800352080c1c02d2003400c141c415580b00a10070b00c0c080c01d0300c22043d851851008e00f1140d4200d00760010340042004089034200300c0315403181b041920500030204082c590021700b580e9603d4200b032842d60058003086040c882c5140900a02c0181705034200002e02d6540084098030600e40169040e444200c01d0484014107581c64581e440081e911028089010030340001c0000d0600c25041c08940503258000004101030741a5a01c0b1005858640512504003030750007040c000d2000f4030b51380d00c60455031951310020782c1e041c2150721040c03c00c5454250039a80c0c114000f003904480d080700302c894210841604c01a5242d03610b0400e00000c1c410210400d60500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 32431606 1250 32430356 32430379
    0x703061802180703051806040b040f17131203020c0d080c0f010f1401081b04020f0c010b040b031c0e030a0c030302030c0705091003020409031809020414090f010b0711 73
    0x34903203120b180c0705000e42e40301042070740c84902118880d64079002e6541c5441d8408000200000c03202162641c003c0c0c450300d10943c0311176242d039a410500c0100c0524850800001c207414201d080d40e0200c440042c0f90b58901c0015112442d2130007901ca902e10f5001e1801800250700030403c0209510487d8042d17020001039942441101148601034180852200d0f21282840d00d030ba02c81e01d084030f140904882010f402402001c0c0c1d010040740d040d0320181c000f0343c2c0c40383d0709000190f00400908014011001e04000001e40d80e000b201c1040200c030310382c4c0089806540124105a441d05c04c10484195081c1e203402c00c070f40481d1505001030318103600c0300c0008141c5c1295210010403d50000043d00400d0781010a5030503035502c400a100000204895840300ca04400b40208058105640680c3c10103000c1d2802a07080100c511010340d07800c0d2280c5c030240305541e001608100f03a0342d20314500c062102c41100d080c445030412010b0340c0b1510344103001d0307403243c01c4001a50f072040000f031f0500d4400f0540003030311084104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 32432856 1250 32431606 32431639
    0xb060f03030f0702151810030b0901060804030f0c080d0b04021b160b0a05030106120b04050c0406020f070503210d05040b060a06050306100815030304181103090703061802 75
    0x30f07040104101c0c01140c503408041070300114103061316805403181003601a1903081400b00001401d103d812901410343d220307504a10340d10703144401d9000c2c0a660f101c1c800103040c20300c0c00130803140140c04c100d010052100c08810000300507000b201c1140590580c0840c989450500140003485404111030700700c05502840e405450780400d00000d194003a1891060039980d40c05900020b104104000300080c6040005010140c020380c03829040f0340081c680060480c22200c0498100c5200359241c090010000c5410032045078104011404c4a5884000e055002c0c81c05001c669030341c0581034181c50ba0412070413211124104402074039071030380d4146801d00490601d8100740c04182c8081d01c490740900a20b44001c0b80d4580240c0c02c8038000c0001400143c60409895001c880071840940042c0741c0d58280102c4504554040000d8405003605040704e000704d044a041e0f110464401468000102c0c4040c01004013200c00030945004880c2c00c44004a110340104c021800103003401c450003548000c000c000101207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 32434106 1250 32432856 32432887
    0x10e011701030b150307060912170a02070e0901020c0601050609060f0a03060503070e040b04030e21030d0522030c060b04020c0f0601061805130605030a03020d0212030705070b060f0303 81
    0x54840e151a803000c0b403080001d040c3c4603c20b0b40910030100748a52400c0011010150b1100b9600b80203424013a40c0355200d45480c80ae9601400290005921059043c030031000725864254020b070001c0000c500e098902e4805603180c0e001407081c2441401c1c040344203441611807100301c1d003442040c101c05950314401840081c0c02007095005181c040e1082107408100c0051503001c0a004603040180f450250380c4940d001c5035804a820102c582024500d1001081c940c2c0001c040d80c1d51010303d4014589030b8403510140300071510020040c803d230440046211503850700fa241811000d541624011880c00f005060034405050600001070300b1600c0002c13040030029000c5030242600c14000255140350f41d031030b401101c031410384402c00c000c100c401e84020440303498030415030a60252066000300c1d9080d6508000b90900403291401e4001d070b01f0901c0810601503043c44500040e4503101e489508600304400c4c010001d0007a16402814100d40e500032031190341d640201e4142d86900181200c0d52059032501c6a6034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 32435356 1250 32434106 32434111
    0xf06080d020601060203130b07140304080109020f030c010903030f020a2102061006052a1009050d0908060402060c0a0b070239060a12090602090a05041a010e011701030b 74
    0x14060b40d40040340d0750b480842154100c14041582070a5581030004843c0d03290301541089038900384407100420142c10a00140c40104282800010240070f0790050100ca2512090010b01c01c2d0465808090542e80000b100c4081d0398040c80c000314150200c9100340d207401c0450030084c19031100a4100c0f400304001100c2e07203c00c94059400d450351074507074080c5480034183e0383c003419021131810b1020111001c240c0111404c0000040070124105464035480750401941450708400f07030391641041400c3c060104101c84c00c80c6110701d80583d21a180c500000c1d01e92070041c01c000d100701c10000301c80317204890400568290640101103c0d410f420801c0c0f0103966151420984107094070221601b6661110b2481c2c891400441114102c5207040d9000c1003100c07540c400d07800700080c07082001d4500641c207010300c160030b281e81c46040e005a80300c000e04100a000a003a41c010740c421800c02040300d426995105504070380c44401e090903d0340e0980000140c440207a003448000c0c04414080000003072042c8140c5150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 32436606 1250 32435356 32435383
    0x90b15010c0b010e061f231b030a09050907051606020417100605010c05030702040f140109060918020619020715030f05060612040b07050409110a02010c0306080a03080a0f0608 77
    0x340351142e071041c2481e134003c0390002480826140e803031f08880002c100c4900b4a100318018222031a103902107902024914141401c15135079800468144455600700c50040040c100c01c9a6100362031070061402403451060303000801d00c4880b60070800e81048200c5d0151400b801600c221020301c03020242600348c4d02c040d4004080e45035414440d0008041d4000c5285650058020018510b00001d41e024840540b141d6120b40604c26501c01c002d007030344413642140714003a046c41400440c08a1910420b1703c183d0341c0c005040c071a02c1c0761a189210050395103900b00c0303900708d00003d4080c41c4600c58280c240e0400c21582d1082410641c650301e000d0500f64540d00c000660a001c80c0200900e84401c41805840c0c01000d4082a5000e1944041404900b0b212007456100e034840c0f03440352030191103940c014144e82d4411803d264254000c0358643e403043c2c080c01520640040303450100409460302c0c0d0000d80d00c03d080a4050240030310180860b2440000340c00500d010038003070703000f44181c81ea2000c08544e2081d08100d0b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 32437856 1250 32436606 32436619
    0x914060a0b04080a08070203070302090f180d0f030b0a0b0a0917070803092806050a0206070f0207050d06020906030405031309050606040501030b01050c070f080f01090b15010c0b010e06 81
    0x70032054800310a540698501000411030040f0958603541640d100c81e0702682d0511810000000503518454014812400030020b84c0032810908040d050a400464815505401c03110b040c1d100a07501912481003115940b9010070080341000c02310b140000182c002441d121400620190055007200c81c1c201111240303e8106640c240814140381c580403079001c0c0c03840a80080109120510740303075002c60380701c10f941400d1080d241c4900301c0501010070641c0c030050205001090240c0402c1d014818207500c050303d4207007a0110b40841e000252518100d0140038440da1280069500b40001541615105038015206651380d04203400c00f180d40390005c40c481900d5400d2240c01180c16a07441c0900780c000c46020701038509142c184001980a00032903501941080418002808803403000c000d000d0081c008049241c0c1502d04009099040ca0103a0f500f0202580c1416072aa00083da1a03d00e198003c01240155600c02c04e2000121179103020010060500200e00001058192503500e901d8016a000c8070755 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 32439106 1250 32437856 32437859
    0x170f011401050c0a0602090307080703050a0b09011404080d0b0603010f080601050d030509041107050a0b04110a0605070b06011b11091509060f01031814060a05041707020a0914060a 79
    0x11151440b4030004503c607600310041800010f5450b4001c0c00481400070b06840000341c560354281d14110350341c4e00c241c4041c0e0101ea05101404120440e09801224000c02403099030518820702c0c04801d80500010401000000d1060290001d42d11070261204001c00712690b950b56200b001240800341d02846162340140e0000054510300003a40c0441d0300d03896100d0718142076582d030800c4002d00644c18480c40018041124a00050080c0110801188180010801410300341400c080d503403801c110140c000c080304501403000c107170000c0c281e03040f031680550103228942d10303080100e4031070380d803c40c1c4400100c8000104004022402ccc105181c2c41c48103941004007a82c0c1c0c003000c0700002d45d540e0b400d0358000f0805804150305081200442c642001d06050204080301a48074408401c1c505030b6080d01c01751075030401d0348450317202800803035003005681005001604254440415900204850444205001501c0400c54031048603000c010800c01c801041100068030f607080b1121000c403041880f03405800c60 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 32440356 1250 32439106 32439109
    0x9051005041706070801030807051c0507060501141c020f12031902070b0d09050724030f020c0c010c030207050402030c18010903050c04090602073c0f030f170f0114 72
    0x24840e200d071046035541c00f4180d19640b501e10319a40410702c103a840cbd015101580c2094104035144c0c2010614076074030350340c4d18500d40c20008106d4006130080300c41c1e18000070310300040b03075107009581c40030614105400b0052680c030310001e80110b002115140d04a004040b403401c08007004009000003440344280301c0350600f003841e012a00c4070258090701551803014490f5134844402580f080e40858031680881d100aa00e0344141c014615001da0350005074512a6012036880d54103004030815440b80001c25030601c1e440e0f6040546980421031041d0400160340110740915100708443c0303000342006002150741c1d08021480280c4d5078003040500d00d01510b0b1603401e0b5407952003001103504480d000400303002400480c0080201628035080196011602400320381c0100707004c005e0440d411190f8210354820140382e1603015008514081d18180240701d260005004981190b4a00f1031180e403520b0b26540c582c601c0042a5540d20007198401080b54041c0b042004141c480d02c51681607481c000c020f0780342280b0440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 32441606 1250 32440356 32440363
    0x507080c0d03050304080d0914011512080906040e1510080f0403051608040e0f0c0f1c09080d0b010206061005040e04060204030b040308040b06060405010c02010f090510050417 77
    0x14412500300c0c0c000c4501d440402d00c2030380515040751140016a00d0091518403110540328642d4050b40d025682c01c0c8140780400c400d00c1140507000164815406140c41c0c444600c03654609854058004140010520b0080c3e980004440140c00542d420b0500c3c0e003801101c000c44440300010b160300404141c4d2100c112207016032000741c030420b8003905007441e550340c40c0d40440c1e50750008020f0203480440c0c050b10b031001607455006880606114200b1480743d181c41c00a41c12060070240415080c142c4c00c000c40c003180c20040d402c603103038a85100200080c002c1c1c1c000366070000706803121001d00b500b0340200b41c002404100d40c118503032484090b03080715029140c40c420005410003000c030740004200200701c10408283c072407610f254018010900141882c1c4d4944074404000d5084804070009110311041000300862008055005001900c100e4241418840043c100320903000010f0f06000f030300e640180c500c500c00c106101c081e150142a0311501c2c0c0c2102d001a10320782242c0514004052040d10780d051240001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 32442856 1250 32441606 32441623
    0x405090309010f1416060b09060a0902070507121103010b0102030f04060315050306070207080d03020a09030b0a090606060c03020f0105071403070306241106010509010b0d09021c050708 81
    0x4a02851419807420010340303c0d00b14410300d14041c80011180c101d0400c00c0d204c0608001c0195000e0401141c0551070f100b8101e41c5400c82c118450b245e02000e1120307980703420810106648059000685d00c24680c140b0301d2030446e4a50108040c203910b800c0c201c0400c8101d2040c84040750041d002032010003110001680c0341d016807400e081d6007840070b1008000e014401c4d0000108100d111215000f40c03500c45000c681010720440700c0c0c0d03000d80c0c80380d03000f0000c00c8820005604055101d2a0450902c05140b4004265803082d00c4090013032180b1101194542e80039500c000700482e0302c03031000c00c050b958444016041412a58040d40940150110846894030601405208030550703500d54181c1001c10030394a03950b400161448041640e43c880c003144000c111042d00c0c4215226901d80805024090740c0241801e80d0040307590000c0d044540104025250502c0e07181c10344180d9140e4648400c249186035005240040001e0744c03001c00d010f13009607901340c11064502c100b40103e00340c03940d458a84e8a07140d60750402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 32444106 1250 32442856 32442871
    0x10f0903080a0903030b04020f03071106060a030b0702010b031c0207050105090306010e13051b0a08012003071413060e061603080402010c06090c0504060f081c02010e0607090806060405 81
    0x95000a040b4601c15400749000c18800e04001641070b0340e00001c078049030050011144100b030300005010920380c0140301d01c42000001c1004040516189000c1340311f070103d0384401001e084035074020403400e5000303401140c01c020f00901103900d401161181c00207080c0e5100802405409284008240c0f5445403040303c0d60307000080c0c001c28085e4038201e2031003040080100302206084c0e4269800c00052010310100d0342460240780121a02c21070b81c0108180c90a155008061503803406060060015415003082a2464421a80c0740c6a5035401400e460381c10100d1001c1442d4000000c05148140c070724812501a600503a43c0d130888180900c0a0216521404080c108031454440c9900b000911440743d060303110788185006022800b0a941d09000d0320b0f0400c80840b16100c107540c09210703c1c145886408000e0401c2e40aa13401140f030034090644070f60500c0404007443d500e034800100854003d4100a407034403400801c940041c684007800402d0451103000c0c0711094000c1001143c1a4600f9018086c080d10381d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 32445356 1250 32444106 32444117
    0x60b0607051c050f0301080307050705041806051b0406090e01080f030d0504110a030f0302160f060806060403140a12030207030504090b03010e010e010b0a0909111306050d060608010f0903 82
    0x160403540c641210b03040704114082110400c09046103064207000b030742c003c00d40b42d070046480d0485803911900341341c0c16812a40c0254940b0381d450142981c005404824940c00410000f1580c0301c1144c0c40340805c040e00c14400079682c00280002d41d050340509140200c03100000350344081e0b41c81700c0020780c035424803c440d04803da0083c481d440720403a490740010740107445040c68401c03900c50000425450603541d801a240c030401114040185a014001001e50400310007401081c94181541507401c081c45000d004100000440002c3d49a00c554084070080c5420441c4000169145101280c0c4c03000d000c44110f034921420329404911078040c1c000d40342020303416181c640c1014201803840c8020a00e00c40c80a9056403100c4e8000441c440a1040440c0603641000102d0801000c41c10302041c03044560201c00458600101d450100305240725aa08c0000b0403564482c3e03220541c01e4140103030a130f541050703a00032441181c0e0401c21040d036200e00100c030302800c000c0c05008003015034030044442d481e1011340842d0307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 32446606 1250 32445356 32445373
    0x30c031e09040c0801030312060e01090e0a0506090106050a0611030f03040203160f0519051c05030c070f0603111903020a020307060906050108150106020a0602070311060f04060b060705 81
    0xa0440000d031122040c0c0c0000e41084040400074003522496003403000440d1a031001402810340c401d01011018140d8013051092518010450340c2070303c41440780f072b8a0a0390718548802d080d00144100c0d09010342200c02c440c000d040c0310410600030207140c42240e2040b5041d400001c0c449001e401428014140907020754182030403019200050350000300100d0341400707030302840700d1010b2000074103030040e010300c3c0020b4008c241441c0a0114030f008440d003800340652041001c108a80c0d4200d031941803c00c24503001c07845505513103481c0340f850007905460700560140b403501080031040c0030840021240c82e07580900011929403031040b01480ba04859040000d10401d245000e58020f0b0010502c0090070320403a4900700d00fa441d81d00407594540d038100c85440d1a0401009103000801c144088400018a004495490694084d541c6c0d40803020040001c1c4e0040b81d00390901d40903030345c40d041c1036a101050300d129103001c0855021282c0211412140d00345400319005c0181050760544240720780c001e00400350507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 32447856 1250 32446606 32446627
    0x2030f0f040b0420060c0709061205030702040902040204030507090c020d0f020a020d0c0914060a170303040b060a09020d050402120d020322081603030327080c0a080f04090e030c03 79
    0x1440060300d90b413078071040540800c030301740c543d0b60040c2005289007000d80070423410118a0720680b01c1c030341c5c840100500078422110129a0110459608590440f00040d40c403980c3c0c0701080c0030340101d41c80038105000741c0e180000c180e001034100b6404008036230301762080c1e41082c0310140c403802e650006800061f8001c0d1142e0700181004c40240c00b040d030207282c800104558a112304800d85040301841c1c1c020103060000d220080c00c041e072445000d8003041140c40351882854406a50b240002070025040700503a002203001c54664442e0840074100d00c450940d550103610b0565800781000365403c0707000304065401e0b481c9415010800d0349030900c607640518948544000e88a80d030390001e090403010f20341c13180400142c442d42003180e024074203400011101c043d0319504000d01251100001c248840d0251b00138121640b0700a1324a1b80038560084800da111003448001610b000c200d02c1009203103001c009200341c01d83e080c030400f0348100c60503034100380800d001c44815503072a03010358010900305500900455004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 32449106 1250 32447856 32447873
    0x40f06140a0c030e0405011502070f0806060607030509040501091a030a0210030902030c0406031a0703020f0f0a020a020315061003200304020315010303120b041802010f020a0807050102030f0f040b04 87
    0x40c034041c4c07808084401008000508458003079000003209001c0d811710215041d0140400c5004106019200b01114901011151603500040000d032203140006135a40c1054019010350f000c6640c060000c01c22980c40e0300070390005000007001c1c00c084078102d2411046e03500e000501544a50f901900d034240d003460106064024100c42c0c03800b241d0500820b14406c1154031944240801140180c004030164804906150f0301d4110107407059040600400600b032004d10b800f400c5891100aa0381c50554490590808900f0503801c010007d61502480c0300110303070405500c15142c010f4201f10b4001244443c2c042c0154103e0300380a00101d18143d00903881c07500c60401801441d4014000340c159240303901500e42c074580110b0240c00450210340220455040301c4190720a2400d203c01c296000c111800350020b03100388440841c14000e0400901c1642c078030880d0720a0040082481d40844d0885d140c090741d28045005c1d4004036218940d9100400005400e00c3c046400ea40c000c9400400801d401c0e240ca84801e00c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 32450356 1250 32449106 32449127
    0x503030123010e1e0402070804060e0105070f0807080c01020c06071202040e061207030f080c060114090a0905030409020711030c010f080a0b01021f05040303110c0706030b040e030f040f06140a 84
    0x4c58481840c800c400940f1140000c1c00003610035404590f5980c2030032406006d41400c404e2050400c0307418000c080000354107840a4806c03a8010640030f413030707a4a510300b241c0d5a04c601548041c1c07950000c10190054040007074403900a00440d21407041007021151200d08038040d9105a0541e8180c41d40410341c14180001d01000890801c01900e184580366100c0c0d07190320f071030b06400301c8081e800050280d03581007050000d0b034054281001c5442000c066800040c00d5444064960400242d8a00040c02007042c100100d40003480c1c203290540d103990041c104481c404c151070783c01c0f60082c0101c1100441c1580319844907081820651541c24254030f07900162801000c07003142ca00d06610850303280303804652038400002c613040361140740490b6615003032400406543c0d0106410f840b40c0400d020b000b004040c04520403040d500245000907601440c200080d002d804521444000ca0000241610000c88803000801c00c0e9141c0c2a01030540d982c3c2c59a0484900b076503813200c1880e5500c1804406c1025205040d042c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 32451606 1250 32450356 32450389
    0x8030c1b040e010204120b0105040506060702040209031e030d050c0f07080c0304050306010308041805090c060a170405010c08070203030601090e04030309020a090507020d0512060d03110304030503030123010e 91
    0x10300342c0b903000182400c9900c1a00010780d06841c101c001010005002000b038003610f0b06543c00c1c055400d0140208181e8020b049009105607004501d000d1a80c904010103204690724105c4086680c21010319180c4a910418100100320b0901c0c000684d010f81a10072114510300106945180c03170f0b06600d54a5503034001c06071607116800200300c009a0f694003000001d02a50040c01e50b00da980c1d103417100b01c1b0090984001880030550400e000c02c8242000031400c8010010252049a038403c907459040350140c90b0a81d002050207007200900091002c1584101e021203034944502c0031035104c030b11060381d0303a0108031000c03400101010000d000122404d6001c0c0c0d04030380b10b4200820200c0003a800500c940b206038001c40c98050362a01045030065041004500380c11081c01c1a40c0b620355000c41c1c528000c03d00601c65400f54500c242050101351050009000c080071403015240c0321a00d030708e01140c80768030a1264508407a203a40694811009110801c44800700c1616135240003102c01d001e20405920102c03444 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 32452856 1250 32451606 32451611
    0x1050d080c010218040b1014030c0409050c030601030606080f04080a030219031a0f0a030b18030706020a0306060f0815011101060303050301180b09191b020606090108030c1b04 77
    0xe031003440309001a00c2000544c3c0e441d214821072030310501c400c4400150002e4440c1c072442c66000300441d0408805600072407540c90043e643d90314020002d41910403540140796452400d400c00800c04072544c0039500800d000d98050001d269a00030855480c10242c1d031600b1800c038640003040009003668000c0034000c07190f04000d800c0c540c00b03080f401c0e81d1401c0d200c5c2c800c02080e114002e41208030040300c21541082412188208151a030030301184016045020041058440d10045902c01200d03c0400f03080c2602802103e45d11a580e241240c06034002100c1c103c0841e040c010081022405078200300e645c155039988182442d40d803804100340b01040e0b0392649061000321240340507026000e0044d0f2016501980328240d80f5450100700c40d110312540070350b22200624112041c0d0481d41e03041302d182d800004064844a01000e4034500304010030302065402c0d24a401200084001074010508500c21001241c40c000141e0380c40c0340c403903124410f40e14001500e0f0451010454440e0081c5a2242180c2c00034100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 32454106 1250 32452856 32452867
    0x90506030322030606151808101508120d0e0105150d06110a0c0c0b04030515040c0b0d05010302090f090706030c02030906031503060903090109030b070315060305072601050d08 77
    0x42c14100c41568200042108240044c00d44840e0001d014107404c2c1900c07002521500d1800d0340341c1d51a0044009d005001c50340318096540c0801a070780c4240050710b034a5040c0c80702e01c1c01801c800101039000788017660985040c049500e680130303010f01c45c0a1080c0e00c0c5000c000100e6070030104010381c0316951101201c90076610300c011036207107850001800d0142903d0300d491142c42d62904220038106220b03400411114001c100038800107030040b8914a00c1c442c1002800311603152881c08035103816580d0001e018001010034102c141000b690003d9048070300a0b50030111545900041c0b210086088079030684961007290200030b9140b1079404400310406510641c3e040044410000f17440e0b9000303030348144e40302d10f040800381c8103450140102504000b04000841c0f400c0c034440d0010780280014400070340141704420014888074025000304000200401e81206600c1e01da800180c001c01c4180c540800141d0311714101001400f0141c050f1055041060612900368038003c10818440c841e00d10445991030180320 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 32455356 1250 32454106 32454113
    0x1090605010303030e010e01110a0809031b011401080a020a05190302030f06010317040608070302030a02040b070b0a0c090b070209090a0506040b160f05190e10020703060609050603032203 82
    0x90540030b14400e55010602d1044d9801d11820342d045c2013030b41810b5034540310a042c010741100007220031440315404e12604540d40c0c40192400e50096041e5110340d84182d41040c103090206610803400c0b820743e850100c3c075a03600e58010507541d4849501c000d4000340d090307030b0901062170128046000528003a200c450031035100d5007c64282110080b440b42540d12510051081084d404040900d0310b100c0ca48603400d091810398003e2030010040e080d0b4040c541d0010100340804c00d2078040f00d000c0c00307440c40c22039610070302d91030084d502100450300c43c0300c1d1a2501d040700c5001c038819010b00040b00d92031903081e8206462502041034100d4084d0042046100700348040000410070701034148160301402980e0168541002101c0700358070308042c4042044201550086001d806c070301900e03400400741c4103206088801300c01c00d941c5e07582d6440910f42d2056a04042e220400d074005152404e881c8240c4050003540d41e5032041c0016141c0a440340c1e40c1c142c01c107000001c00d90303580b034244501c003200554541e00700070765984 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 32456606 1250 32455356 32455361
    0x60501230903100e060705070206070303020a03111209120c0705010302090a0f031407050105130311030a08040b2d0307180b0703031a0306010e061009091404020117010303020a02060903010906 84
    0x1040808091320303041e2090302d140701404410b521071480d040c8280350001503400079a40e0720a44030000e00b4180d001c205056114403c4d0b10000c1d030f208a80c1e802950f65400c2200358584610101e0b0744810500c50000e106402c007800c501035603040d0341c52900400045081c0030040d0044d42021030001e41250520100281402420341d5480055004407030308007142940300d08590420f901a00914103000081181142e03851120081c0340c112904400c0c0702a41d041c49000082c18106200c1000d0304a120100b000301d0318011820040c260b24003054110440c00d0154100401e13000545100b00110007028000104060b001e659110b4a40091036840300480b601d4500381111078001804c207030300280e51500400d100d029201c1d0304849241084009102540c035182202112034002440717075026400c080d82c2c0d004800e0103082d140e0084d040220303080c002100c800480e20a4407070211003d0b4001038442c01128000701d07107001e801d41a20342550203000000d06603000d22041d9072200f1007054245d940c8614860100b940b40c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 32457856 1250 32456606 32456623
    0x80c01020406030b100f091505090d0803160905090a24080105070806040203090a020f01051b0105090d08070503070806010c080a09050915030705040f0605030a08090102060109060501230903 83
    0x94800203202200c0f4405c1c8000030b0751001c078004c20301c2a480c3c8420031440e0041c468004075420340c404441d018403201c50071030704e50144003e41600502c901c001201005041d070007039840b89a0110b54114542d501d840c1c04c0f50a4250381c81419000144680450f200200c1030300080d03401c21030115103108414622001c0000300202c2d9120001c1c0765074aa0621003180c0d4401d80403600210101c0b415411810304035881034641c110007000070b21580038108500f04a134080c00594103d141ca204201aa11800c113020502800c0200c481e0700640c062080c0110020b4020711420340078075002d5480740c3c155501c41c0415074903160302070300680c1403194141b1500d002070202d100500ca03a00095541c0350b1068501802c1c803607040300c0500320303040e2042640b5221483e510001a00c008840c801c40300810390b019914a0040107048a030001905402014003640c140a2010b00400c015002039013142c0881c0e030b031780c0306c94012598540680ea00003203506820f4840f0345410400c01200900907140e007442c01121500107480d00305803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 32459106 1250 32457856 32457869
    0x103080d050703110d0b1302070606080c0105070302030409150f080f0d020c0f0103180507060903120503010e151f020f190b01050909070801060308030a05090a021c080c010204 77
    0x1411400a1028000c8035004902c9040a0083d41c110b41410032150040100b0030b8203e590300d00e94855a5503440d0042c00701407a45510440d42c0c0d44003070070401e014001e140100c007160321480541010651282c0700300d0302602e4042c0d02442c1024200505403020781120806280316102860002c00d24904070207581004094800c02400a450510119800c0800c3c100c5440250342000500902c19210500d01c41c204050901e400142c00c8425031410400030843d080140042c800d9000100e6095005aa80d03803d1340e0141d01a05455040610115158402400744211249088020845c1c020301c400040f28034120080980f1014000300d007100b4103510701e04c1004c00041e481070044180313007002400681c14603031040d44075104102140c0c9031402d48071418414503000e00080c80c000380c1003503410b02010018104040080c015540d41c0c1c10003a445400640344000154500800308000f14000510356414030790103000300908106c0140302018140b000740003030303d007988104a2240148020710003080036121 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 32460356 1250 32459106 32459123
    0xc0910030207050607111c080c0906040312090302090a09120c051f05070905010201050c0901050a11060c0306010e1206010504050a0209120a0b090607080c130b070c0302040f0207030512040201090e0103 88
    0x105400b095280903080204500c00c840340c4c043c0f43c4100f55000d50708c180d2081071810303e280da46407403101040c49441180d002400021444810004595010388820300b140e00880e580e035543d8956084080441ba489400100340e4100c0d00e220340c060900070b45c000c42215015038161902d00a0000e400b0f44541004100c1c07000c800e80c0c03003042004c603682100105014140030b200807c00c500e012400b214072446100401410b00c40081940ca065520480544180303540c2c141c00e840c4c190070302400c1515160000d070340c054040340b015541d404103070074510076103400d0410080052640d6441c00c0144401450054490b480040c0c08210303911050712003007800500002c44d000144110394150070302d445035020103011507540783c00c29010320184ca07900c0321016070841b028040700c603505c02d810301d403185e1102c28131360011142c3c1d14041042005c2c041d4403160030f400c9034003d83d03040c0980320b4490015004c83c030608038020003240d028041d02c1004011600c20300d42c454810706280e0291602e6202100007001d09a000b1030703041c0c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 32461606 1250 32460356 32460377
    0x180308030f0a2d0b0f030d05040906050d12140c01060807050f09040b1b13081e0705030a1103120309030a0306050102010b1003051510020c0f06030c0910030207050607 73
    0x1a2240700d50181c0f6860000d030030304034590a0a401800300000e8402d016a80d480d0ba84180065441d80c111034603e440080c00c54061860440001e41130390014820010803900e46240000c076802d001d0002c0380d215a1141545804070144030043e140004407031080800014240807000390000c09126043c05080c0785001080340c10701e05401c1024002d01d0420050281a001c030501c000621315030b0030386030096203555000313102003d810b5040304980158180842c140c20807100004140d2070110307000b0690900070140c6c440c103d802e1252555034411a22a09030141d00c140c402101041c1007090f000040c0000400307803005242032915000f41c58005494411b1142c000040c00e90304a0381501c21000107180030b0009108032a8610005100000038894240c1450b80303c0000907400043d2074640082c040d0300600524002c0342c0c2c003000070f5540743c00316602030088248612a004615060054a103d0040c21342010701c1c01323054a050101c15800c1c000f0310340a160b001d1094400140b41408564440c1d0010341d2044142c1707 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 32462856 1250 32461606 32461621
    0x10b0307060e13090b010308030c1c06060f0c08160203100e0102130906050a09020a031b02071d010803041e030503030103030e0906010c03200703020d0501050f09030a0c03180308030f 80
    0x10701c1101c036007443c520701035080c0c001071a200c1e440750449400c40c0d1000e13120f80c1d4a1603082c9031485008c40d82c0408403078602c00060181c5456000c0b600f52440380d40c59604044034210309a80d901a039507009270000c00140101c00c80c002ea090210451244060705070707118030303610540380d20540d0502904201d05940200c0c58085044100a4090091002c8401030190314039000105543d82010300545112a40014142c06510f004c1d0300507450ba20444009180f802140c504002d486468174055004004860801c1881040510b10b906050398005d070301444c503051400000300704110706140c24949144807054004003040e42400603600860194581d003004000801c02c200c0d8504000b44020305004d4840707030100102354400c03170b926030502400c0e030725888001c00000c40500d81049680025840401e001c64481004019000540030300d1204608142546a022409440340a1410440000383c1c40421040200f4860311405010701c21301c640c042000c03074981d101c015169004036031034194000d40009101c0e10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 32464106 1250 32462856 32462869
    0xc01020912150411120a0606050108060604050114030421020a0203151e04140d050c01050a0501050d170d021801020d09060c0206031b030f0108060105090112030809010b0307060e 78
    0x2212088005032140200c0c42c07151180b0041c000e08040c00d403541c1400410190b403201c9044540c4282e80300d0403038407041d61038504032000d414207015050000300703400d022640a0038968241d6007a5881612803200300d0b002c49001114680004000b03682c0f1507441c920b1550f4400b5a034080e101108601e50161107850621b0051501e021103e61034081804d14520402400b400182011101502d0411014025494904001e0f40c0c00000c1f003503070b14050290003801d102c19a0098000d0403483c844400074442c5617518031a80044603400d00c121900b1482c1250001d0001d20025695600960045040380c103256040b03a6440c12a04041d650500380d10034400042d842e5030b010403244070714031106c0c68410f80190404d10300078011000480001d0190001001246014802d80e080860440350076290326140d1400d031043d20307813025013841000c5003405924000705240c1000b140c028140c9800d140128075403003040d50f08960154008046d8901075581d96010300e8140e40a000080061040fa0b60b48a030201016040180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 32465356 1250 32464106 32464129
    0x6090d03110601300201090f1508090606010203040506070807051506040e07050a0b0706020423090a0c08160e0d060f0e0102041a070807060e0a1104050403020709150302060c010209 79
    0x100032018150f0a07003c0c1e41d2144d0701c00e80c0d40400003c0d07441c80561403005940707515241c2c11104645450190200e0000d04c49590480a2101035941c02c1c8035032241d01e280c94444a081d227038a030060f0400c108c18401400c000d40205285845021150b00d803051507220241405c1690900c00d0080115406001045c5894003500000282c507030041d010091410000031413203a00f61003244421500416043c0034008103906440051028160b89035020101d0301c0c01c16105400c46440310700c58010040455448031061203020719510382c035180c2c040c0a885810309801b05025050411007040301000c511030260701d40b0000600050b22030a0041408421041c9480c00da56482200c42c125038414002006264003000d04101c40c10f1641d90000d85e10341e180d0800e08039512880001070061400c1103000c0001c140c001442c031319028000d0800c16042c004032410402580d5050320041c005901c8803800780316801603503104d100c0e0b0300501060402d41076038079404070350640c104c214aa241c030b9601151141c070718180325540c840c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 32466606 1250 32465356 32465369
    0x6070b2d060a03020108090709060807030203010e07060203160c05040f09030e0f0a0509100b030408090310090b040b0903190503150f0a030308060a090f021903060b0a0c0206090d03110601 82
    0x3903251400100e002000039220103810080d554000c0b070b0b0203a905103d80c1000d4107423400e0520641b40c43d030700a60740c1d0308040d12080340030750700e420450010031402003402c4058580c143c0c00340d840c041480700d200801c400f2144007500c04030346501c030004141c0d07258480e01030003016001300410110703614200030b440803d07200782d42070095015a05180580d80d40b0749141e0309441c0d08854520b880d488604081800d8401c542040c0f4404000000b0301082c49489000b0301a0320b1411011030f03030407000200441050701c1d00000e004203555401804200003640d4202e4582d800a54681103e08041c60311808040c5540013280c00c034003082000082c00020780301ea059071100154146c0d11000844d805102080041701c3c41e00c4040c0402c8406000300786d05684502911005000d01c40051080540004191000754000090305072900f060340c01070382d40c1b203002c0e01500f011281c0042d04641030541d141400c0c0c1e84c0f1010424101d0303015800300510109551080900043d0b80d0103603035429842402044124500001a042030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 32467856 1250 32466606 32466691
    0x90c021e1006080102030702030406110f0d02030c060106140405010f110106090b0307080706080403050309010b0907030c0f020604081602060412060501081e0d0f02100507030b031219030203040206070b 88
    0x1201f0a9000011141120114a011402100280d89003410885034150341901800703503164440105a000003e400070300004019106039913072f240019112130100405c41e0310030900030b00003006290b0241003c034141440600700020448080303c400c0d03003165016000040b2099075038000000c5810f00f00585006429280b004100d40c1c0c2c14140068004900140010100b14000001800140c000c0d00000b2078154050000c0e0840d041048020700549901c0c2490000250040b9514810740d01c0000e450f03001d5904140c90381d02c0c2403000400f0580c500a08001641c124030104000034941c0c0c001e0864842040c011507000565504004a03076003803803050506103414140100803c01c042002248042104025080c4081d040c00620026401d0040035800314410901d0f12040102030340d01a0024008d98808506a0f642402443d8402c4410700179405103c0004880f4280024800d000b6801140c1190004118504113100c9940c0c8403211807080382c004c4e0885071000f148900a80202502815020b100c3e99103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 32469106 1250 32467856 32467861
    0x80304090b04090503070b2203080708090a1a0901060509010b070323030604091109180c0102030a140307030914030405010e01030e03030708040618060b09010807030c090c021e100608010203 83
    0x2031642c5da0150620150003507200c80041200100d0644c0d540540d14a098401c4c80708103080d08001d00703119401ca8013100480c00700c0001549110000c580c07001541c0c1d0205681c0c1e100355800d294401010801000d4011541da500c00c04205036032500c8d10b40e0b00900b80016510343d00c0320503180061107014441e040c0380c441c2c64035200e02100154810306890344404159800141804507042410b0005230051150360401c0c014014002131000740324144444000100840751488922401282d5901c034696403400013482e00409c58050900c51310085400030386503e4013140c00d000b1a140c403460780032140315040e0154030001e0b00700b1041d604603149140c4c410f006d083c20400c00c5c806061a644038400140208100404000003074208000f0754004c4040c0d043c0c0c489405005802c07450034000414510b894180304084130b5000040c1c0030b40015802c0b040c0d80d44601030314041441c080c0020050021090550190301502c0c140681240040c3d041401080c2581e0042170003400050109c021130351290400341e240e9004004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 32470356 1250 32469106 32469113
    0x170301061209021329060f09040b0312040602070810050403090302040207030c20031b0307030308090304030b040c140a080601060f090e0403020102040e0f0105010806012106080304090b0409 83
    0x111070000c500050220b501803081c030009105506401c01101c0b5246070100c15020100c420020300003501c0c0c1001c106914504100c10840c0c603008410240390300b50010480090242065044440c40c00c101408580340f444408001c146907400c2a040800103902c590340030480c00c0030400541d1000b86601c10100070b141401e440c0106410120700029000d580c0002e50001054882c49030b0316026500079a0081030f90034903202c4012402417005855110303209484406501007941984000e034846c0040003010300b98a559010f480b0301a001300144c440340402d0100002041002103060b204030301c980c403144180c5003400000e4034015100e9038490301901403c4000d101d100400141c90341074440c42c0c20705078220300102c88100c4080605400c80c0d4128060201444100f44e0150054070070f03100600d00d130800d01c1d50741c00c1804003802824464140040c40a9020801d1940550400150244500c54000c1d03036280b607a25000544000f1b0380010402d9100260400507140c3c43d100762a607000301154140046c60441c1c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 32471606 1250 32470356 32470367
    0x7030b16090f05010c080d05010b0c0f011406040b010903080a050301030201090b130e09010f02041701270305090d02030d171602120c0307020306040303053c0402040609090503040317030106 83
    0xf81d90520096082c003109104148050790301e0300502032018452036071030303580550305a04001e90a54162290740c1c0c0456040d0018020001d10040441041403a695041d042001504415038042d0520924180200118404900416956106417940382e034070f501d14400102034078010361111054160a11403031440128030800700f01119a100620102900c0303e0200900500259058031141e910019001442000100c000c0a41c0c000b500d00812502c016100c12000700000445100d0000003000034040009001c1e801914044201400001000900d5804030345810031082c2c0744030104612480748443c03c0359241d1844d9020351154100e07101002070300c03006955044402d07502c8200715004100d00b2481031b010001d0b980c0b81c07034000303044039a182001e04000c0d000300340559406090f47d00e0360340c601510021078001e2100680d6a0341d5813243c410501400d0805000c1e0181089030b00ca034a034180040d11000d00d01510380118003e80c0034554640c558903204440d0750390105034144d10740b03060004009894000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 32472856 1250 32471606 32471609
    0xc05030702040f0b0310060807120c15090e0f0a06060201110a1b0c151202070206070f0c0504020a02010605030f01060302010206010e090a0b151c05030901110703020307030b16090f 79
    0x40c2c0340403482041d007680e4040540342010442d41c01d8400c64440c1007a55001d500540d04481118041d42d18036612021401288845810054402c00342c5207400c200c13600840e402121042680d180070703d401501d4a150b21203c0c0000d48400010303a100d0018080100c0c2c1c02e100c2c01005140900080101450481c01c409090007010801c4050041c03040c4038202144104030901e40c2c060380f01c071080c440e0a44070128415080710500501000420300c04000400098a100f11014a90002c00c00380c2880c0d1242d0315404501d40b4101c04541110001d04000381e552103d00280c54204215000800e1090a040070301d40b5100e420b1899488580c140081000584d80124989042d1503030907003900515078400c00164038042400000404400d0010100400301d80c040030700486080b411910900c40391801400481030100d02c04000e006904100400c02803507000355100a00c9a4103442a203081907900d0b00000d00304079041d4010380d1484041400c001e28400008940801c003030b040e082c40d83d006400d001202d001c40d41e80703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 32474106 1250 32472856 32472859
    0xf0f08150409020102030f0c030c0717060c0306030a0203010608010507020111040e040f021207030c0302090106180603020c071e090b030a050303060d02060909090c0109080f0a060b15030a0203010e01060c05030702 93
    0x750742c1c1010944e4824411903400305500c00b01103aa50742c0a0b20740550b02c0c1d004c001e81401502403608003180c00141c0300b0902c4000a490b0f0001c1070281c4850440d40c14541c4050500ba40c1440b841c04c00310010b8a003030107030f040100300e102c00014191600c40c1c006401c2d10110824510440d608100a000e41508211000d41140e0001e083c80c21161052010a80c943c9245d03100c2c4e0020b12980e0300010030043c4100c040000c4e6803003507801c45041d90f62003c090b038041480c02e5642c1540402d40c001402903600c00d5020700200d110000441d1107041d41d03842c80c607402c60214000c4045800218200b0311087c02c06004150301607400f68001c1c24000c0b41a102c550300c03404003422440c81074446410403000d655408050314003c41000f42002a02e040440c00c2c00c0d51814051006c03804101005d030f00103032040020850300451a54440030b00f11420440d50341d0300c000c1c900d40146507031184400d14001d45c6054003802071441851209001a038035414140c0c85202c03000b050344044100118040740c8400142e0110030364080715070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 32475356 1250 32474106 32474111
    0xf110f0304020103020702180106030b18060d030509060a0302041505090a030611040e16110102180607060e01050c0703020c0901050a0b130b0c010f06050301050c030408030a1103070f0f081504 84
    0xe861004034046d100c2c414001c0c0d4420038020b040c5010080100495049805945042105109090611003400e20302000811311295600014107103003440355a054009120340340a07854410610300180150300540c0d81440020340c0801e043c890030710040c01e80e41d02203056060140c184030755400021403003042400010310f0681c560b43c141072040c00c00c1060ba0050b00c0d5404500c0311928104003c10340e03036903540d088000040c0c2c200d07001140d8001706108850045001c0f0002e0035500239400c081c000c1a0303100302e00488a0350343d94184030054060a100703050041d1a0a1801c2d55500802d0400a1400e1403020758280704003407450040015a4540c20100700303e444105000d1f0b01c5a4058240d5408164254444280040005500d10750614107501c41c0015103074015041091584600903d4204d4800701d030420700306d010400109011820140242d54001d013a0364004c41d1090350111540440e0b0015a072110120b01980300b9200402e400142c070001040c200d180c101c02501e4140d0811170703040f0a001d001030042c1e9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 32476606 1250 32475356 32475361
    0x70210140c010603080304020102060f1501030b030f030307031506050c07050409050307060603050706030e0f0c010e0d0c080a0209010e0603060613060302180405240a02031305060f0106030f110f03 86
    0x80d40304055a094800303820080245aa4070300300031400f0390048070100c0c014010b000008035110b18010820340900c01c0703101418403c60640c3c006400814202d0185e40e4503100d803040d445020300d010001148604101d035404900c1e040041446c01040540c0e40001c402c1c48400c2c0100085414000340480480e1000c031070120300c03507025040281c01e5215031480509807178280b882c08810701c0000501c00046400c581e40800c095596480560344440012101d910341d90000380300d440c4650b2040c0400165210001c042d034602c1c12a03559a1580c490b59944520600d0700012001820b40c0707003604110740101586500060ba601d4610300103520341400612043c401d90642d1060b80340b00c0641e070b0149015541c05000d40402000b01c0c40c618608210407201180c59200b1401c2c8540380b2000d5401d10f81c1c09004030443d04410741c03210a914000394000400104844002c0514600480e40c1041414050084007042e10030f11f50410340b008003912207002d440d0100c2030a11000d0b5800030300d6203040318555110104513640380d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 32477856 1250 32476606 32476637
    0xb0402010903050a030e090a090201020c0d0318060903050105070801081c11010204080309040f060501080711031608030601080906070504030b0c1204081207021f090c0302061804050606070210 84
    0x1031040d00043c0c16449451400303010144c01c803144079228036088440e40e13142e655120080d01501d80783c2c10000d0041e0800103140030103041000603070031000d01c42d0400740561a1100010211600c0740d9206070001107224a042090010070703c6400e40001e62803603c14565030400340c0f010303941c1406046d481c4021041d04504194248580382c01e010b80002100255581c550302d4500300c0c0d4239000440b80e144968a00f01800703031081074500c07501d0212441a15165034a03034503070b2000c2d6405815141c2100c0240020082102090410b560003c0c859225040302d40d12810b00c00001080448001c290b14259481401841314240d04101a101240d42c00515103072a80c0e24103242c4d119a0051495490303165400c0810b00041104d0305001e890000c3c0f21490380030300ca544124003242e681070244080754040c000004800c070300c2805500170815082c06414201c048503625404128642c0c860100e000d40303294404d110050342d103000c1c0551500040225101c40c1064182e030001a10f1000100d07840b410b000d41c1c070b051403044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 32479106 1250 32477856 32477867
    0x3010e1602100c020c1503090c060c0106030f121b0308150105091c050f030a0815030316060605100509030303060904170a03020a080c03160f0201060b0705100b010212070b040201 78
    0x42407810080c400c81c01440c0001e56250140100d2600c1b9000c8481e1201c1c100135080140d03032090b101c00e0300804000e406041441000e500c00407070035440355200e4202101041c1c0e6100c10001e010f11492100c071004c424004020400000010b01104454060030b00d01c001c00c0d03010300400e03001881e45800010705155070005940c140300704601140c100704140c4814104441c00d0340c130008280d00481c162080a10000741701c036144e115807441640807480b0321021820032006100c1302c240c0c80310301601301d03850800107002204c204104600102c400b1074072100705100b035041202240040c0e405038100030f407c0c907520400298482c0401003a09000ba911900000d0501c02c22034801881c0711003400395a9aa910a410020003941c40503e2450204150700040f8100a6514084a12561498645104801c0c40180481754107040c030303007480215921940040351031120f0310020300d40a48540010a2041d0380d80c0e4110055401599040303055401035000e20042c0c030030036130450f480c05501c00054281c2d9513a03840141d50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 32480356 1250 32479106 32479123
    0x30302130302130501031b080a080f120907080d03060806130f020a0801050a15080d030e16090219030b0603040b0a1d0105070207050307050d080d021b060403031103010e1602 76
    0x5005900109000c0001829030046041ea40115a03070140c650358040e2107c170244061041501c0d40d0b00c41e00520300420f00038030181418080c0008080d10f80340310152003005003282171302d20100f0368015040401c0138000410080c1c10140761030174140041c601d0507888a8852400070482000401c540848604000c000c00e030032500140d00901c7e0315039154585818074003d00003111445441d0b071424030103da005009010b4001203c60100080c08800f0707024100b01d010301800c81c20a046072050a8070011007600c0c81c800071018000d0702c000103850740d8486031201000340c1c10310386040506140000c81191a150401120341c8190031542c1031055440e9040c400d4010034034007a41805100d0803152084883d003045d0000ca004030701c0ca500702e43c3c042c1e44501c00c01d03031998814414a0350240443d184a400644080094030385099035010043c1001f07400301c2d00d50064000a08802000d030002003c000c1010340505c5404680c01083c0440f87c11981089142d002c00c050280c40000054003500002500c58403c200019 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 32481606 1250 32480356 32480359
    0x609070e06030f0303070c0b0112080706020c0705091602060a0e2a060301061106070816030c0e030304090606090e060d0303050c090d080a030b030a0b130503041203050a0e010e010c030302130302 85
    0x1e81c0e86c901100000c0090a44101c12144215a00e0002812002c41502c18400c140c120b003d140c50322010ba5100002584a5003600c5240e0140540002d1141d072484c010300d108102d4015808240710540304002e05000004004620051401e40d0245203a1400244240c00030107100030b00e0061070483c0f035445004650200003560041c000070010407080d501482c4e001c082003204045072502c0c1ca400c1c0c000d840d29038040f544000c00000d41e24514400d42d200e41c1156100642508250305080c0e410300100b8110340c4076811030f850030354440a003044415804424000281008400e45c40c160501e080000c0c003550313a643d4003504064031030010440c1482c400003150304560004106645464052030720740e00d560054049200480d2426041e00f14038140480c8a030626540440320000559035044210040180d864041d10a44800d10010840c0a20200d04c003001601a440e515100c81300102c000b41012003140e0b0050410801601800b01399801401c0c421083c3c0d4075040158854400000b00190108103a1020303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 32482856 1250 32481606 32481613
    0xa180f020f01051207230c0607031e0204030b07020706020a0506060105131205010b120c0d020409060603021201021e04050d26070c03021003060305150402010c06060303020d09080609070e06030f 85
    0x1c4210303004410303540c6c02200140204a05040a9001c20707180c0140e507035035500e03030300010300050f0002d202c1e40c04841ea0f1032051040001c0c10b0045404202241c00c00c1d00100c0302902c160003400002a010010300307005280301d00c0101701400465440580b0f800c3c015165134144880403460f801d402e8010702c0c04901500301c602c1030316244052030500038080c00b55480304a000c1c10b00e2000020301100003182b090000d09001d400e07646c0c451095030034000200792031941580c03149e0780c0b1341011006903140e1a0002d04030301c5100003d0384410300b480a40348480003406020303000010401081115443d0404000c000c150001202c402140521401110514000103041e040301c1c400107510041002c00301070002034070300035109010302504858059049800c40c1c000a8131030381c03000d46100c0700e00c4a0400529403083c0306141c5102239070055602c0c1d0b41680c50070b8001f00e003d6008003d11418040e03001a80740000c0055000401d51800d240d40d070390b62146000c0c050b0100c00006d920001e02603450400000c140d08d92030340100e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 32484106 1250 32482856 32482861
    0xf0807020405160f030b0a061101110307051207020304120b1003050d0c03020f06010503030405060d110301090f140606090d05160306270507060c11030d03050a180f020f010512 77
    0x681980c2a40340c00c150b00813680c940d0038503c52910a20400d030300030702d01500c00c2d40742600306282600e500300d124101800541d00c0b9500341e00e00c14030541c080c5008420365220261a400d0310300038454080b00042039441194400d1008000c01011007001d0104150002c1c4102d409031070310541d040722850990806012481403419820540c1d40c0081d0009203140030368207a034a000c0200e00e0341c684802e801e200c1c60340d0540c0b091005110502d440d00091501c08480240003c04000a40703502c810340d0001d03807052038815074401c90407031041c0c0316000714815850507001d25816803410b040000c10038090f2401c0310b4010a0203d00d40c804000040120913980190b610117400c0c02070b43c0e4981344029203d6030a11440c3c0035401000340b000c00c2d90308094851425404009010898101481210001405241070b1821500d40d04030786984c1c1c03414003c200641c60255004a010310b0300000d44801d035405403e10714040815940d0843c040b5815140d40004145d0484010a0048032000121010700400300f1400070b02400c00b09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 32485356 1250 32484106 32484121
    0x2030c070609200906090115050c06010305160b090a0306180203030304080a020706050708040e0c09190e0c09150702030115060309051014071202040f030309031a01060c0f0807020405 80
    0x11002410143d40c00a408180840c50901150b04c405550607500040104018092895218801c030007035044c0346049410040841c0c044c518044003030344142d0301c0350042903c907400303a918aa04c10780900204100c461401e6840400f08006c8400340c800a000203950340f08100c1e03000813048003884125001400c42e51a41400d01707140c0b85c1c90f8005403c640240c072908000240c040c0c0110140c0344803d8204505030306003854010505120507008040007850f80c0200b1150a10ba82c400230440421074801022550490170b0618003402c203d0003a15440c190030007804400013035130b100341000b010080d010720426180c41d02440441d000d00444001010b01001c044408980d855140d400700c2c0700780e0b021768101d94401c0ca0f4a000728084a4050018090324001c500003c0c420600400c59244004060140180f6055542c1c44456400f00036400450014040d42e104109000d482c55001c0703408201585000383c59490700da00a03141555142c802001c1500a803200028081040b081c2d4241c0c603005841031115160119 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 32486606 1250 32485356 32485373
    0xc05010608030706050f06030c010530010e1005151606060302040e0a0b01060507120e0310020c030d0b03030414100c06020a03020a02010e0109050615042901020d0804051002030c070609 81
    0xd030a000e91b40d0301000040d80500e00014449200041030f1074070b510301500340c50604c40b09000d05809696400b0080764141103808915070240c0204040c80d803030341035401e15010780c2c1d01a60083d4001842508201c481040e0b408070442140e0303950710b003005281c25051017440c15030040d1001e40d1003c0d40c822318104819500000c0414041e48481c498801c1079916a240d41d820364950040344800341030300080480c004000c6000f40401030381041c0040c21107102c414100f80540aa80c0b00100d41000c41d000810303442f907404818082d412140718220061070400e410005ca91010314509131000b88100b0001040310b4055000d4112100300b00d80013071040d540d581380c440703000d806903104100301001513291495070200030302c041c4202c1c901903500901030012900c41c3e1070b025030060303010800240c0c065650115008044d0302c040828000740c1d0310250151441070014006410500d80c003034100c050024050402c00010800706942414800c072100c0141c4945422803603604902074540010915031030000c1040c04e000030308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 32487856 1250 32486606 32486611
    0x108070f1101060b1b010606050712020307020907030e0d0c02062506060e07080109090209190f021207020f1204150509060c07031e020a050f04150f0501021002030c03070c0501060803070605 83
    0x170080c0c1400c1c0c0c82c4104100c0c00c82d03140303100382400100d061061800144d201b40419880305160300c1202e041110580020740901c200f03962200200e0368030424078200311400c7c01451200d420900300900031050a0b00481c840c1e00c00c0c10488004140d2441e00d00c0c1d0180100745180030341503004001002213507126203085c000c0c000c0c02d80380d02d404522000000510312005018000340e03d503018100006a85a03445014000100d00441c402e880e0344070502080038003201d102816610030704000266182c14030f41d00181c10b010a08d0b1400300c1541105022010200a4101701c8007215211403241141c0c0c03c90800c1201d01e401a101c2e4568440c0c4d0018429005001c00198002607a0051100c500740311000c43d010185200c060800035000486100c2c100100e2429680c584620786004c0d10210b0301d00c4040c607200000410b1500401c8442080c42d10034040c55a04110940502c03510301011071840c1000c1006035820300006104004001000b80380c0c0003005005e400c600001c0048008590f02e0303110302d20302480031b003404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 32489106 1250 32487856 32487877
    0x30108010501050409020607062d02071202010c020604030c0219030605060f030c031906020c0601121202010902010e0d02040e1e0f0601030c3807020117060108070f1101060b 76
    0x20180080303001d240910417048102e9000700b045180208607030b6010060062000d442e928144604251180003012494881041c0009100180c0e12882440e01c0701049002900700380840e89020401c00c4502d400048954116805003041081c0c0c003150710009500119020181e00c007a401c070707000001080210b4000c98000c18080750898010889074081c10760781d007825080701d94140d0040c40c0c000b02421008265140c4240161000f618101099180c289000c801f80e1003991308a1082c41c80000340328100076003074102c9945200a208280307017a00002e0032081b00d84019841108000c066004650391170b400303460700703088140c01d07545c4c0c0194a101c80a01034150203c1045035000d20200400d6110300810028142ea911403200c0114a0520700300b43c0503540000e900c19203602050010311240b521528414507000c0c041c440300d6a6903100c41c40014412503880c0381141050a0344018404c0a81c0c024841d180c1c40702d41860011407002107020304070782c1c00440340040c0003503519040001c95800c0914008083c0c1c40a03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 32490356 1250 32489106 32489111
    0xa0806040c0806010504060e0112090f0209070504080c04020901030e0604030801150809030d02070305040803180a05091504050603010609110703031d1c0905030d27051c0302011107050303010801 85
    0xc203620903504000220f40341800184204400c1c4074841c0100c8135800d1110040c54486856070700100510120303105100d00765511016118404114504003400c1e9511850340d107032075401c003481c090085668081260a41d0700c550b802080711801640300b64844040c00c050f8004492460130f240c02c01401000d800e0040215081020441c00c80c4180140da0b1540503140761001076103031100f0700b034041c0001d420620f002c908002d0104000107111908201511039524190a4180310410f14810130020082540c0894040c0411400700f213201841d07829400035a40080d1008945a914140000c0c010b000d0740e041154522f10b488588001c02d90042c0203003481612a4030100200600124036228141c0e68603d07090842e40440300c1c000a412140903100c8082c0034506107020b00980703660000341014044a00400061199400402a000700e810404000702c82c1074080c411107420702c0045500c04001e1345110800c04600e05550081510035409840700070913030f034601d5441d00028580a03481758020b1082510725030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 32491606 1250 32490356 32490371
    0x29070201060812030a0b06070210030c02010b0409030f0c020604090608030306040b03030301030c0303051c050a020d0606050f0a051303060509060403020f01110301050d0510021606050c0301050d080c0309060a080604 94
    0x8000040404007543c40100c41415503441e4001d0301c000e070904c2240560840024084100180c44840a0412480c40f588000c190300f030160100908450030f002009214a08105041001c284c0100035107880a4446c90700d07003440029400864418030442e400410f28030f150410002d04404040041c3d4007880702181d043c020760101300e0402d6503c3c0802c0c0006005013900c03020400000f0301403401081f50581300c141d0904804048868181110000c40f095181990001125401151b0620580d4058215418010700700350031440d100442d8042c04003c2c0c3c050210018440b0368103610700300c15000655020b201445680b406002c900e0f1a29001c4d0780071800351103054208041c260040c0201029a0501e64405003940c1c0380000b00a0304a0000f042611a40103800c440d10b201503540c0000c00700c02003195416050111240340c41ca040321802410380800e510700f480140440c3c4e4170101302c01c6999411107595034542c4090001a4214462107150541c82840001c080c9289a00050154882c0008550810905 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 32492856 1250 32491606 32491619
    0x3060e0108072702070c1e0e0601050a030905010c0509090f130f030c12020f0d03050903030106030b03100213030209070206070e1e0303031f05010c03020a0f2907020106 74
    0x6100a014100340303034000b02e50070f0101e80c0b0381d070644032022111620701c10b541a1110a1040403a072010130140c81d00707001c810090000703401c802400c4056050003003500b680b16240442d21015100064103d81c100b1100050a002c3c25109800c0343c041e00760820001c119142407180d0141050b80120405401207106034002000004407102440c4900c144c80c8001da1f0b12041035071814010281c0f40303011018000c651159a0100702442c0310032000d2100394006149990034104002d10388070038050b0210805051004020512401005480c1111074074200820840303160000241008070500d038088680344041800c01359801041c0101c800c480c004e5400c1006a202d9550490719110100c03001004500c0c0c1144000407801c00e03403100c1120051082038000140e981c000001d0a503407094031106103000d0500005216011500d407054020482400e0102c01e4100c107a070081c5d07c078005000050400c403014100c200c1031141d54101c0074016600406c00381e9001e000000404000d00050b41c803100150302c1c148020894 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 32494106 1250 32492856 32492879
    0x90c060c0609070b040605220e0702060108100917090a170303071b021c0c050301020a030902132f130303020a0c080601060e0f120105040507170606100e040e0d050a0306 74
    0x146c41c0d941d555a40b03400314080380300380014003581d8929111081ca0400081075002d40720010300071240c1d68040c241035450462070514104104200407100ca240808000008400c0d1444101c0b84e0116a026034551036a44000b50007000250320410401e64000c20385003080001000a41c480c0c00d0b2910341100c3c0026803041e90818180c1c510009400030070a29109401c02c40c0980d0044d80d807441264408025a10380f404030303080e60001174006002c65142c841d82811840e19401320890040d0301441002200c41400c04040c0c18003400302401084491042d030405041c5100f000c0340c0890003100405000c1c03590304c0c50000d607607103089203054032042c20501d8040303508100801c0c0203041321407640c2c603041c01480300c804100748110445511603002040d564072280c1180c0a001d03541c0708a00803406402124544000b61800140d4003202103002c0e000075003081400e0340d9050321101c20060a160040410007030f9004100103002400000003a403041c0d100b504549940075008041341c1f82c40d81d07814010141d0342d8414052 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 32495356 1250 32494106 32494109
    0x40318060f030902150a03020a120908030105060304030c020315010e07030519020f040504060603050415050103080a030f20040603111804020a020a06060306060311030d0801050108090c060c0609070b04 88
    0xa8030012001d06041d11a41103502414002461040c004140340300c07031000c95010385400000300390041403400c9090307080400010700c00f00090007804150119aa54106e5200501605100301c01c0400410300b89441075102d04800d0b580502200d0101e02c031251054403c15091003202103c00070396000035138142c403900610f801000300810284060703000c8144c00010390041c40e05c4a070501014000028541e82ea1700542000b480991000129414582400002112010030007810f0a081c1001000040c1b4201d085404080c0340d450009140d170b002801c810081c0c00e8500c5a0610b40c0d0441a1082103c00c90307a00410032660651001c00c400c0c58028810312071805000035a111500224607068003d09284e001400720510750f01c1501c0b030f01110741d600c00044404942003501c640340c4c5c83c641441003100c803011146080304c08600401d0125a5040c0060080005000d04c0f8100b2007003030041401c07141c0c1000011404003000704040c0d1184045100c09550b4503046507603110900c03400c080003d0004c8141c040b2030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 32496606 1250 32495356 32495369
    0x510050c06160203070c09240e0a0504060b090405060f0106090f090203040c050d0507030b060411070609051c1d0909071a04030c0b0a08060603060303040603050405010b1008040318 79
    0x1406a4074140c84000504908000c1030950101700441c1c00000c2080030100c02030300004900044000035811140700c0e400469443c554030a503104024420280352904182c0e01c104614000708050350f4900e03092000d021480b01d002c1e0442071000502c4104803001c01c11602c54070916461b0015683c2c1c5a4044075a0200b510401801010b482401d00c40800d06800540c0d0107401842c140e4016643c07000840c0c210b4819103003d880d42d8000380d802380108202003205d580c0000302250140403400055440c1d0682c0c1c444c4540013449155158001d004019080c0041035060941d0386c408020b40d40003400143c42e400c00600042680b460350940c51041d440d201004a0041d901c84006141c51820811030b1059040003010300d00005109001c0080000c0d14180ea020150038114200382d1100f41940c0f01521510f40034028030b126100920400116450000aaa0840740c552402044580325424203038014240f0840c0b064003c0c250034110307030503070786c2001c1428000c1e0310036a40e80c4a030f481c5003580900030132190b00503031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 32497856 1250 32496606 32496613
    0x1706060d02090d0c03150c080601120b01030608060109060801050c030103051207030c080f0a0e0909031e1e07030f0302071101030507050d0c08160203070503121902130510050c 77
    0x80c040405074003030320310b22602808240411920791550b001803109540110342d641c541c1c1c0031100501302c0b14000d41c2403203002418000520304054001902045844442121041d03555404411340d078460b4002200600304501a240696103401d03141c000780640780501c42c07aa600701000f00310b15444d2041203904a940050141104035014040c101055200b1030068003005800d40136030000c610303d03600501e1802c1b07040c2d00c140c0d9100d40460020740180d01c110181480346e0300707007400c101d140c590101c115022440242400c4c0010340d00e551404889016080781c101d000c0388000d0015070307008218801803140d90b000340c0315040c5081c26550220240e115904000303224040440e422003842d4081d4001c00d400224608086090000910fa04411551a68030074000109042c01780004044c0240b60186203040620245240a40d41d8542035980c1c810301c084401002101c20000741c1005030b46100c220150b1030507009640c0c0d91a44a110310146c4024000d03280300750341c219001c1c02218082c10854110101c2080507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 32499106 1250 32497856 32497867
    0x110a0809010c020a09020d0510120f15020c0109200303071a070905030a0b011707060903140304080d11010b060c0a0311010b1809070b120a0506010302070f050c01170606 74
    0x1102c0d2590185012038005450441c0416a1103490001e80b1070b03058070306800103c0d80341003c0103400f91065584481c03103880484c0501804034000c0403951494503045209450351038802c52600000703110b20380ba0000194a005980c5013000808a000784c40003044d400c104190964050400d51644035080000b0f102d0444045800c41085500101c1075010310f2500300180920fa40b9000320b4101405410200c2d00074040344018000d4149000300301d0500540107004000c40c50503c407000c0c10018a030300028065459041e488114202c04108640143c44550161051080501405040380740f11684452182d420000c00e8000c0e8181002038540e00d160940060030303480002d40701560318001a6030004040d5413208210882600e0b400115a06015001d25120440c9803500720a424522181c00c09080300c0b50403c403501094800d00c40044e007003682d40500203026110440141c0091181d241d00400c1803550303004200a01c400070908400d5130394281c940c42c11900c4241140003590390111944c55008105000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 32500356 1250 32499106 32499109
    0x9060105090a0e12032d0106050a030213170304080105010905061e010212031501030e150609070c12110606010201140a09020109031e02010219170304020d2001110a0809 74
    0x181d20983d0030b9801e6841d01d24180d1075900c20381e401141c107000000311200743d0684404164118100850146101e881607505014005040b88603103000c90302003580100b03401615100c0090118000e1403000e404c0744108100b1900c540e101e811a02c00d1120a51030800001141030701e90203064410b5000626160a451483d5001500e1503000d205160440c0310310f81443c0d9176a201700000754043c000c000e0508114038800400102950103100c1400c041c0e4014128020040750801c54098010404603403c9810307075210710048030201c020304000340800e40215035078a6507541182c050031100c40c03d0025a812552000010790a0760318403413044100401481c001a4829103580c480c543e9030744141341240b600303540e170f0301c5000000903070010007040104402000c4045603010080fa0700c40e44c0801040300c01510284c0c6a045044407034284034550340d10000300240840d50350015002109500442c0c00c5620354001280440e0400d1000c0406e003c217201d041da40219000010f1540d04056210003503610b04400b560 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 32501606 1250 32500356 32500361
    0x105060a110607030209120a02060f0f07051002041d060a0306020d0b0a0308030708130b01120f020d03030903020d11060a0c1b060c12090b060d050c03010614040509060105090a 77
    0xe4100300964800c04006841003400041e01543d2590380140e100c0c4404001c010a001c0340b030400041691088800c48016100d020544801581c1401602d45903c4e0305402c0c0c0502c2d205108006003075025000b000c84000e001c0b80d0140040e10381d42c01e103141040c10040a248000c990030703100681e20210708280bc100080654000305030341194190007060817003070b20b0049510712100307400840d0103100110401c41c01a92040c1e0680e84550086014074101c030164030358003500001805124066a144007510090009444090003019805860001d5030f08050800030010803021004030018068400103034283c611805d000e00256212001031308154440c420b8060090181030162014407101818030b0ba41000d80d1000101e1540c007400e0041480154004010601c0d585840e905111078035001c1020041511268201d0340700c1c400381d0714035214040f1420803916012600c1a02d650642c00c00c0e10109251006a28800c5000d00542d01481151a2028200c3d16100240240c503040b004140004015802e60b4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 32502856 1250 32501606 32501617
    0x9031209010b0a12051011070f05030405060c0109030f0203030603070909140723040c05030c0a0909020d0b030105100e0601350105030c09070e04090204020409060e160314010506 78
    0x44000203040008040843d41d401155404020325801c05040c00003400f4080c0406128070101c0002004050050844e0f00ca45004403600640006001c04481c002c201041044401500c8010048c1c2e88840c1c00040c214041d00350020708500080480c0004070300f0070f0002054070300410700200600b0342da60420070500300800007404296070b01012102c8a02040c0410310183c00604000b42c0101100e19035101060094400e65070658001c2c4e161030071200885074080e0560f178100508611103a5107070185801110504001d030000100c040c400104080800074a60104074140b206500900543e5200391041400d404540320b01d92034440010700050743d9601c100c1c070340d00c0285c8002661401e90414404400300c40103a501c070800400600d0344c0140014a400c0054000780002162042018602180c0040c0910f0113000100d00403500c40c0e501d0b20071561581c040d02c2c05803a0008082115568440c0c00c40c001e100185c0e00c2c1c61030450341c001c84016840c401d01075039071036008a4100c90042d910f41383c148405a80b10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 32504106 1250 32502856 32502871
    0x20d020615060f0d050c2101030201020a15020c07140112060305100903110607090311220b010203070203010f050703060f08060c030a06050d030905030f031303150b061c060905090312 80
    0x8200001d4072104c50700c503841c0900c50301507070103481e0103280140d000314228042d143c01280e81141c0c01040142c1c0d00180031030755140c0c0151503d4901d81c0c00c20660029005890710310807980284030010408103103900c044d440100090380d40030040058000142e0440b80325000280184d00f110302801c0310807031144c000c03814452007071070010701c1c00202d0200720303081c0841662020006019010308205025095048080c5540100c8641030100c10b0081c0c44907818100304400b5a040f521421401c03103c0c0c1c024010344240a8019002744102007030810300c000100b20440d0b8100100b450844c000c035040006c14524019210f002c1c00604141d101d0003660644e540004042898072502d90101061036140c01c0c1100004c02d01c217031140c95409091004240c200b40c0c20300e4210005a0080c0200540f003040c0711a080112504103116100f8240c0030f2603200050b0040220351f9801c03100c0000e042c1444840721240c412041d0101c0c404001d1103803942d4000050341c0003507901b240c0359170043c400582c6590070041302076041440b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 32505356 1250 32504106 32504137
    0xa0b070807110607050102030403031d061803160303050105031903080403050d0603060204080604020907030c0e06070203120415030e0c0604050603060307090c02030903010605100801150e041b020d02061506 90
    0x102d100016100b507121000880c3c0c140d401100344010503402d40690030030034061968400c0c6c101030894229a4481c8002d02c011101d1076450340d13484116000f80200c4400d5940c0c82072060003c00c0c1403c019000d81000c1c0f0803075005e803040c1700c0d0880138075116503414081160b056031154000e8880703407000c1354640c00c6102c01c10030040d565140080040c01c5c0b44014401021031002a00442c5020300410220302c0d002814401454100080741c1c00259001c41054904135044a945484140c0340c00400c1c5449002200c85800100018010038102c03103084404608203200e030340911a04545d5443c0c540c440521005141d04424180300c00d020a1805201450748070304007038111030100d0394402410051b90319070703544500582c00000e000c0c5c030942020700501d4003510090315421340e03d44040800900d00f005c148224480d0180300044000a148105901d103003400d0001c1c0144034045400c900742100c480d00041c4400036205104400c08030500115a09110f0015100902c42d44c0445000340495548000c0d00c1050002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 32506606 1250 32505356 32505383
    0x2070e060334080a060501090b0909120705010207201504060210050601020f0a080301230d0209090a0c0b040603052410020705040609020903241609030506070c0506060a0b070807 78
    0x600c2040b028001c13500402c4041699454400500100c0b084048028000c0b071180040008445000440f6654106a0754503e40d580045080050090040c010000d0888000c0320040400300040844154125001c9608091009402c007000d4020321691003408050780040d40e080c2d800259907400a58040300600540d01c2052451000b1820041d00c09000c48078150040010300049103000683e00b5440682001c811001001e5400254580c4c2803d600920071310850001414018046c1305110380c203940540100102c503154001c0d9a1260050b000340c0c2c0000f0301d0000003800c0400440c03030120707005100440c2c1d1b01d0515105410310072107420b00600034042d481007550000c0c290f250391155100070100c0110040e21407920705c0c101405e04840c4d401348030465081700d030fa6010075103009908640107040d503070071042c1c0d2403520351003034036001e16036840604103000c1d400401c03080c19003180d5201d420612640c107461181c4da664040014a078102d00a4000000307042c03003220000744103900200001c034081d00641d521031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 32507856 1250 32506606 32506619
    0x50d02060f0a030623030616031103040b0603010c09031208040c0807080c0a0801090209130c03120503070e010f09060815030d050c16051f0905060a02070e060334 71
    0x6502c05044140043d5840c0c40401a80744002c01c030103440b41c54070700007510f46402500081e0380da07074015240707410f04058400c48a0300b1601aa11000c00c84074944083c0c1d48034a0242070242c10709000b110100d001e0350030070101c2000648149403160641e40d001c40b000f001c952074198200c40d1510003c00488034404903c6010519000412018000b4070800c0d00901e8010110000d002900780240d008080b5a070404040100584e0760322561580b249084400b0700454460341403e0380d031060503610103085d00c003060510001256200b0000c5208541540701c20b0384e4035614400444403001d5404450740003845102050201d103114002c4103400640c6520412290a40d00c0000ba0400c041405503001081300002d0301c01242205006546c0b0450040c0780c22542e81d45014040740a00c60703080307005100d500c414024003488a004800450161034090b0409455004410000e0341d540ca85000d030650503246400050014540042d40c50585003442d416004941c00f8940c0c032a14242e8a5404400001c2c02d00b000403a40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 32509106 1250 32507856 32507887
    0x90b180f07080a03020c040203041106030c0409020301030303020d150302060409240e01030210090f14032109040f02071a090f030c01020307080106020a02150c0a06050c0a020d02030310050d0206 85
    0x2a00b00d08014007203c0120b0700d806440c200c900e11945020f0340c0140104070100b4034010400c1d04104094a19960304d0361a181c224240d0711480d080500358501c08000031082c1030b403540c068a00c42200c0842082403580b1044c0c50414100300d80300c000d50080d0108001c0c0302401c40c58025940170700c3d5a2507500a1075040400901e18000190000c0a4120007040100154a049200e9540740701d8581030583c5c4517070401344103900400040c056000728081c5580484890b4908008503031041c01101210b00507200c000c0c0052091340c0c01030f0403407489a414a0101c1189030010f100322940719a00c545100422101502d8424403d9001860406103006102c00c150003140b003400101b541007a14030005a80c1e241000b0040e0500c601030300b0440855101210010050f211049914a0015000b01441c1c0311624400010315080314518000c10079400c02c1306125000007140050420403070540c080e10444035050100326036078001210452100d00c440746081080d41446c811403914140003900580c501100291030145 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 32510356 1250 32509106 32509109
    0x6030307170f07060614010e01050a020601290c010905070911090f04140103080702010210060b0702041508070f0e090309010801120206090411030703060b0a050a110a060e061504090b180f07 83
    0x10500da541001d10150f0723010a80303481c045c2d82401c0c11407c0c0025800c000b50303528814098111041c559850329081c2c6076131100001c24003000400995038608541c54001d02030201050101c0300b512910f8000704100d0614040e1351421381c04a1102803c1280e014204614400d032900042d4229071b40707440b0a07100c1c51110498a010b0343c000e003225640c600f144d1000900e0030103010015065503103429418058030080c0c00480b61002d4040710b02085d07180240c000100d40c08010350122180c0d104808002a0744031054142d14201c0e07640d0540ac04a99130380a4005071a482034030181400100c042c40188a01d022030480c644a050015090324102081c2101050803078800310510704c1c91030808010007040c03590500a400140406400c1c45052210301080a0f10786d01480300640180a2211000386803a9002c00034903003010340040d402c0c000f81e5401060281c0f0361801740e030030008140e1001c0d903104140c2007502501c6640c590000004155a40303d018003100200c00348030139192409250685d0b01c480004210440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 32511606 1250 32510356 32510369
    0x1080a0b03030a02061503010213030f02040f0510030201180b091003020409060e090f070b09130b1c0b070203160201030c02010b041b030c080f0a0507120c0201050f06030307170f070606 81
    0x10007402c1c400700082d51b03254550209440381c1c2c010040d02a50022059080c030469a01c0340041203100042d10005001e0444002061130040c1352400b0006984080c25100c01281d000b038850b424404201d1001645201060042e4a0b1200c01000013000a00b019085062400e070180b0300103003805c0e1200d4640040d03c08940c88000e03800c0f040421b020620909118002030300014800a003806850090317010305034011032510740d0bc00e81c00070780580e0074803549402c80a21803100078a0550b401105505051000c0d8900304261000b83c4280005074005000008803981100004c4110907500c40700d80c0110080c19400803036108654a601142046403280e00800300c003070100a4454600ea110000001c1c116114010001c04000c440c20600c0701030b82c0c2d0710303030b00313940000c0b01200100d0b455480100980e10b1103286403550901a191103550f0200c00e6040d0702c81400741d62512800d4046464074410141e407405510b2000d0060400c3c06450b40888040700024112002001a806c0c00c1c418107864400807140c0703542c4880d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 32512856 1250 32511606 32511613
    0x30c041809060f020a08040305130e09010203090c10090902070804050d0f030e0604050a0504020904090b09031305100215060307050a0303020304080601060309050607030e0c0d06231501080a0b03030a02 88
    0x9040003114020f0b030412441050301141040110080103017011400340016050010000380010702c9120310b04040c01521003d541c2d00310a04103251107500039401181c12a11502555a00d40f8803458000c585990070f4102d0341d03c3d10240e42c01c25903020004c1d84504c03400c80c0d860a04000010701516480170000b08180501d5000c03560b034a032414003034100200907403c01d201c0c040401040c001a0b90340c002035010b440c010740d40182c5681e601804500201095000079080e449000300300a9084000801440e0b5900003540d8640300540e2032007480707180b0b0001c5521358096004038186040201500306071503440f800081c11140c0311581d030800b051100c452a00140c0050308002414006034104100e8140100094a801c206d070040580314903488407005005d1008054803aa6003d49050701000700fa212101d00400c480610402403814400820500040140c141408044000340c46041c1e5810740c4151591900359610607072039001114a81402000d0490080d501c20607405140c0701023020703041e03c00054004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 32514106 1250 32512856 32512871
    0x13020405040312050c030108070306150f030c150206010e0c0313020a060f0e0910170102120c0403021809071205070b040602071a09010e040b0f030109030e042301050105030c0418 78
    0x3840291031380101111810301d41040100036000c0c0010f038120031070340c10004c00101a00f00d072104038000303401030307100d921524413019002c018400c05070340390b100702c0e000d00302c030b50390406880c1c0004c0c3d80311b180134820312503032840d82000100f0401003000116444044001d6210070400d01d580020b001d02c4150b08a14005030075607200510554120900748901c1904586c03015862511162140080542c0c0c02400c0400500d24007080b10130000b50151001c542c5c1c151043e03102e51404007104443c0d038026110a03440b0300d02240c506c2d04201c1d09441d0180c0609801c2015000c02c40c14002d9000c80d401000004943c144602100045c0e451010070240010f08403c2d800303040752526208a4040c02180e01c40c41790084101004422116030300b0025901d00c40c5815a0045131a200c0080000e45c1030822004458155080a040c0010554010324120350303200700303e804000940c0c03000c104090220400030412812101c0d08010f0001d50b02800145038001c0080200342c1c03401c1d459a02a0014101c0e440c4010f20b082d4681e41ca = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 32515356 1250 32514106 32514137
    0xb030d0503092409100605030c1215190c03050403080f0601170903090f030303091c030207050a030c03080709030b13020301020f04030605040c050d080a0e0a0f0f031b0806040605130204050403 84
    0x510f17503034114a000c2c2440707590b05203000240c90f201a201c40302c0c8520044094580124014032148a055520005074102454040e5006070114000312400d681680341c00404684a030091040b180a41c0d01962b07600e43c0c07507442566a10300300300c0280000d410720a4560b0700d008803002ca04400786c824a076800240d901c92002005216024019405062190b0002c0c030401c0340d0460001514254550404d130300c40c5020701d038880d0550080c07150010240c240e00030541c004003415007110009213854072039558498a40e0341c450f411140f15240d400000e00421482c4041484940c03290b03941048240000c00061600409000c220300c01d80c0594000c5800c2912503041100780041d408001000f48419107018241c410140e03074540040c815115007109100460481d0811612508031410160400004d0062102e460380e426905805892004880745d608248001c2155100362030300a0490b040c55004000a40722540c0311400707054000c200304010b683e08180007000d686d540c001d07540164040c0e159112421500350 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 32516606 1250 32515356 32515363
    0x4031112010204150c06150905041109070c030809160f1a070201090e041104060807050a0f0b0301260d0305040b0604150b07050a0c0602010509100b030d0503092409 72
    0x808418031070748180f0003089001056509281c82e0321003460640d840018070b2030510002c101d020000c442805c0c540002081512180c0e000c01d00641c090710070420b0780703c0404108840207208840b4000090903000c00307400020700820086411010020664081000070f040c4048841e0032540152007419012904008a03c1c2d468401d81c800d1080034a558030380b01c100d40000e40745000510034403d151149000160a002e0050180018454000c0051042ca5a19211156130b0409406020700c200241440010100c200248100c12100c0c1900004c1c1907a10742520b41529108030f44100400200111611002071410700c50401e002405880015441c145818403203018040200740e0346c0143d10f8000c04101c0a940c8001c0c00b81250450b5014507654500c6d0f203000da052289070403004000d10311100b004a1003a4040d0000e0784601c403010112002140950b4042e820b40304ca100310b05070140c200503001d40504d4031440003103905c492104122038905040c030380c1c1d01c0c85040302d051552040ca945081800740903a000d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 32517856 1250 32516606 32516629
    0x40e01090603081605031902010501050a240302031b130f090e100b0303130305010504020906090c03011503060b120406111809040311060103050c010906090e13050f03040311 76
    0xd00c0204540750550391000e442c0c0c0300321003019044918180384441008820000c890445459510081c5001420b4202034003070042805942d200b0b42c800301000c95060f0449038007080103000107203507041c0043c14030700030f82c000c0d170010f4500000740407c5003c0705030314591200207180811441c95282c0d682481d0154140c4115940d402040744a03040c888a003081180001f4064030003c02483c000461b4503a03000001e203148100c00140e00c055542500c00130130b0000651080744250300079100c1c7c0d4619914801013041c10b01c411500381e03144140504c010b210000007119041380018250030005a4192510900012a00b000d1a03030072413001c620040100300700075401880e20720118140c10605104002004207901d854502000b80138030090300002d018944104444940d2100b01c90035220196100e00b042c1d512001c0c05c1410601040e500c0d800050250301c90180c48045503540c480d02d201c0c903200c00c03104109500000750140c803030b071180030f0020511240502c001d10055204980000d100ca1580d0141700f1500c3c1c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 32519106 1250 32517856 32517869
    0x312010b040b090f0613030501020c01050901020304050d0f140c0d020f07050a09090204110301060203030a0b0a030209070c17030c0417070b120a11070602091807020c120102040812040e01 82
    0xd120800180e00600240c0b42061811590441d9400013000070170014080c500f40f8503c5060050000418403006600404004543c00001d2085982c0d48007043d00b40d00c400d850007000c1e03601c442107148040b40301d4106212000b10700e14084102807001403445040e504072000c8040315400100c1e04090080e010015200942040301c0600b60740c41c98080010190000c0c4d1040000d44e90f01c440000c0b085586a6010080550800c02401d0326541c41c1d4100039600c1e0003c9844001003880c0404a1529282071a681000c0780c0c0d00900841080e604c0110881e18a0f2685808455411240120070010502d0f074028602c80c1c0b441100c079581321454080380f14120b049040a40c2c429801001003442041111002c440328800b40c00101461602c070450003400404d40340c030641c0b04d0404017142050410000350014800200100c0b580800d003000b1410070083d800041c0e4407003025a00c500c1342a021402c0c52005204000381c0080018281540c82c0e94040c206503580c003041c207000300d00150034080074032007083c0c1c140503085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 32520356 1250 32519106 32519129
    0xc080601080a110c100b0a0f030c05060c03190e0a050105040807090b030a150504150b010905090c130b04030b01060212180a030515240310050a110a02031201 69
    0x804800103441000090701e00c00c0030503241c481c0049694084011500300340b44000881d074100381a4170403d402020b101414500c141014240007518204440c5104140d035000000d41c5c2100f8502010094143c4c44008840f1160009100e02c00944096040c0400350b142185c45041604c1a80030400c24204a90340045044c84010311040c0101c11000410000342c4a203000700003081c03c1030030002450169048401411228114548010380c401ca420041c012441150110b420041d4842c1c0902550081e841040c0091010384040282c4e00e00030011036000003030307881e140d4500b060a1403484514070464005016a403c002001c10130495600782190040c03043e031020781102500e01d261290a441101d0030080b5007000c003200e180c582d554504400004640c807004465a4009481424049040440d000c0144200c0c0d403400e11910140060600c400c03020080107040300c0380e8511003460003010003600049402d603942104810130700790b5200901743e600168000b141c4400b1200f40d8081b40302d105801105100c403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 32521606 1250 32520356 32520361
    0x606051201090b0102250f050402070302060a090212010207141002040312050c120a0c060605030c060a030203130b041518120503090c0301060b0d05160509061803010c030b040c08 78
    0x45054541075900e03400b00400c205542d030300103d140c05030f4115144050700d501d0000c070f82c082d60b41b1118803044580007041000140c1d40c5001300000c80c003071428041c01603003050700002c620f07403c0c650180300184d2001301540583c60841e0402e50898000e840121002440c0404030b00c0e251108000072450100507a0003075190900350fa0300c50301c540d20450000d0091200120f44414101c1e0140001d0048002c40c428060b100c03c1203085c014100b00b0840c2d0155000c9140c19404034141c100482c145480c030300c01400840c60103045070012070095000400001a01c0c1d041c4008400141a150001c0e0055000798410700d2075840e203c2c4030000700e610700d040d80c0c001c0041c0040070b14001041d00d16288100c010904149440799034100c05641801e500e880b4095055290500104900a04034083d141d0301c007641c0c60030015542c84802e0b5640304200710300c0c00d1020803401d229410301490410001c0810a021081c101000070000300805d007076540c2c0c0c13042e00021a44403500320106007818031808040c400d052800782c0890 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 32522856 1250 32521606 32521627
    0x7020306180706050a0302070501090f02130608070b07060207050102030f07090f0e060603070309020907021c0e0a03020f0a03060c030218010806010e0103020d06030507080d020106050d0312020315180604060605 92
    0x111620f1040209000b8049429400740f4082d5064034400e03a0030400a0040c0506442c29034501811050100c1c0304006c0041d40301e24502e9a8410003042c0c421060080120a0400c1024441d41d0090001211001c0e000c200010029100780007450040035090300c0c45d01a800c003080041c0080305540c100340b44000c509242000702c40c40188005400c4070301654603641e00e40300c2d00c8040f0058410944080c0d00b158000c41405411980041c1400e00484a00f8410004030380b49041202d01c0c070203815000e0740c448004003040c005450b040901008405001b480c482c0d14503520f030303507000a98100405020209601080315503481c3c1c50520351004216003484c01c11498900030b8006050250401ea00c02c0c101940070542d000e062403903038010b102450b081400c8880c01035403005034980d20300340110184010b50805c400003a1a081a80072485442d0380f43c0c803540b0820408201d0a80250801410058a99a00184184107403510300b0b02c202c003a00d409458400a1500b20148801d4a1181d8408000c00408009603541d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 32524106 1250 32522856 32522863
    0x5010806120a0201050d0204090203180613030e090702031c061a04031208041b0909060c030501080a06051e07050c0616050d0506061e03010305010506191404091401020702030618 78
    0x1c42d642403c1c400c0e1604c011045450007800b032038102d880d006100200f0b1040c00d03001028079124610244023100c90540d105405511107480c00000200031a40020104802d491701c0d0480d070307a00019600c11681002c0c4001804500c0460035025501c805d503551105200501001c1c107201505401d5120306480e140c6159a00700300380c9030740415441080300b990040f03010808076070040008901407540c40000c0d02d49900500004100030b00080b0b0b4094900007980300f43e14041e008160499000402520005900703840390b4010b02001840071800b0207840380e4151841200b10016401034240d580d41580740c0f851701c0844c51070a20f0150146000240040720146450350042c111200311421038000301b043d840303040114a0320f024010164080c0d400254100405040d110701442c100e0703006070000e0229848640c00e0000503c0c010142c41400840c5007804d02c4199845103140880d110054400111312a103625200c1c23441d00a200d0700040c0742d4002451205518040000c3c5400484007050039045110301d851155a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 32525356 1250 32524106 32524123
    0x3050f0c07030c081f060806010b0703020c0a06050408010e010e1b0a03020303032802030f06040203090f0f030d060603020c100b0621040b070e0d0201080903071b0501080612 76
    0x108820005116034980014080311005582c0200b903003c4054540c4680b94498903414034003014800c1e0348074a0084103049001d00b6084a5800340038005990034a80d44000c95400860203400b94441d04007911a1519000450801080c0c039039100794136903092803030740c13400c0d220702003c04049681460200002c1003030210b11115000030740c00e82940f4810100c1c003c501c41501e035a00196050001100b0440d044080000188805140451810100f41c403486800308074002a144610281103d600090303080c11700b07038020f60300004c1d44404c88580c0482c0000c040e20708181c54602c10a41c1d0000325401c00c0620141c01540d02502c10350a0640c100914407510950b036a014480c035070942a100c1001c810991180e204861580001141f05401c0c44018500140442016a42214003105a03c0041c81140c0f00f0100c00c80100d1004007001080a001d8004490020000d0540740a074042040f56800050b00008425021900c54220540d80c0740b402002620344c9100030401409000781d11900340c00b401d404154a030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 32526606 1250 32525356 32525377
    0x62304060f0f020918100803030f0403020c0d03050304110d020409150f060b0304060207140307030f0210110306090a110a1e0908030d050a0902060703020102030603011a1c06020f07030f080105030304030305 90
    0x245c40e6900c08035100c156202d02c0c3e2108080b804000217009110900100c50303841103009800300d030185e4210505010031142c100401500042d000e202080014401c0c60001c50f0218008101c165205a03540020307048455902044581d0050405402d80c2d080c9076000fa006a40440d140c01c100d02c600d02041080948402800203003926030000d501020492500c0301ca0070b01441c00d9045a0f26004103181c00340800b90801d0522016210b1001507a502e6913a038004c05c1460390a400039603056803120b406100b003c0300c0143c2400895a100d012001480b50780d08007030194101d4540e41e0160407007200c03030034480340654a0a14030070020044800c3c028030307000100701d880102447d00000303841da1302c2d03410317600080c090f4440003907201e400020000c041c143d0540146024440440080041e00880c48810307c00c58001c041d11500030903886207004038184441d0940340320901560000d407602101c4020411290310450f42207000c02c030303405a605142507000c0205030150800f0b400451605040d5207020700103010308007060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 32527856 1250 32526606 32526649
    0x12030a0f0309080c07030803010f091802060714060c1e0702030606100311040e0a0e06011401050f0702270f130b0c0d0c0207090b010c0f062304060f0f0209 68
    0x140c10000e54001302c4420700c002606840304162686444882d41c3d0003031107805e0145401101c08130765502c003481145072611200c3c140c00f84104690b030a003c400c3d042050180d46d02c681d8070800013078900c002c0c02401d104202c050442c40d56402210300c0303c90a508036903107070404258144090700058500141c03140d0084030845031800e48400035401107004c3d0481e04018032420be40498006040b0400c0e450643c080e120100f014080009001451992984244900100544040d14251341c550140005140140d44001e50a2510030b194011943c07102e00f4466100c200100307444070359000401c1d1810260026281611138140e414070052001c8200741e444005001304c004140071a040d489411b003101c40a00d60300030203011408524030003035220506031040c1003401d030811a80168542c81042c0c084a807035808091118000240d4a60200800f403803001540c04511025849502030070742c02c00180301d244110408202c500c1020245401d8480d41840c1f100d001d8018002e490b4566200ca40fa40b01c024199100c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 32529106 1250 32527856 32527871
    0x5031506151308120d0614030a02091906030c0905010f0b07060b0109090e070305120406050d0507051e0904060909080a0f02010f06091b110601060813020604080c12030a0f03 76
    0x4011440c0596109580f1841040c3d601865000ca81c0040c00308845d49490800090b42d031102001110703c0b9102056500d600300000c0d45006103408480c498102030460318810404407001001000c8a803203400035100907211200400054005002d018050aa50390040022500d011003010850294010081c0055214007030076103a40d1041c4540c2e40103012013a41400080301e03503118a0780311140c600003903030340c0e001d040018910380120204035402c582807036581c6403a00c8282c6441c080280782c058150000c1000030040c8940700c0825522016130902425050b0b03940c2c07641ca40800003202c0701944400c0416007082c1418010400c940169000c2d003081e81042103130b01e03001c2241240105528112412028540b14002c52403440c0c42e070142c510344030301c5110585d50040381642a40c89450a001c00300482c0e1081e40180300c0381e0703c00c1600035003003481003006003003120061740001c490f90050380150380954000500e076007040c50030412b880440304020010310f01d4044500310080074044840321402c18180c88140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 32530356 1250 32529106 32529127
    0x11404021215040f0209030a0206030a09080708041401140403030305040312150503070b0304081605070306060306050702010507030c090501051e030f07021b01080f060112060603060503150615 84
    0x101c407486115810008654036095118200e00302603090b10a0042d440c050003c030713042116100300c5030f00002c01402001e0002d00c6608100c2a54401060402c00e00d0311842e291000603181005000c040d0b00c01c0c1c0700c080d1602d042150f04040c9401c130404003410000c15158040e1505101e6044405490301072401140c0d5030355908098880885032084074490519245070072201c1904d0800078001d851b03049007581c0d8900e6032100710a003a80001ea5014082d10301c1080150314461003c8080f00000e84a0000d032165990340340c42d128112011380d8015603500742c407a420000103030b6084c450544d010010f41030800003000c40071401018850700340150b60500c40005007807980ca0100e602040320440300c072811150b43c1d181038070202010a500b85c03120b60141c401c04052003a29160070354160369540d010f07901c08a43e59a20443d00491180180600e414400c10100ca210728060030f000e000050406510003040c014504014145850802501c803507110222005200381d5a0310a1101343d003911201e01000c0e215005c084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 32531606 1250 32530356 32530361
    0x308041103060907060f1403010909141005060a080d0f081504090602040e07080f040312090203010e0105040b0c04030c17011b17130b04020405040507080a03120e0309010206011404 79
    0x900c955051181504000310810001020f0302503c0099031420070b9030b4600f01e800d44002d02c02c000750000e128824401441041000e41c02142c9450051940000e500311450b07919017008000e0b6400d0101688803820481141801101039008107400030003803541c901e40030001441e001541c2d50700700c108061100070a8103c107180c07a0100080000030810004170045107480d400941c41841a500002a00c0000a07065400f6604803485400c01d0109400195070b40d56040f10290030b0300300403040250b502c03039030003016803000d102c0e01d40c446070500300000d501d00301804d00307005400008198929911040100b84000380c42c007030f6844d088a21a5618034880748590040318050244100c0c0d00a04081c2d5421821400c1c1d80041c40050742c01c18840c840c3c0c0e02d6242c50640c040150034a07040a007224141c2404a8014206580041c0c0d005010300292884030392541c10242c01e0011041e016070000b074150405609640d240e101d07803d03070110300c0b500070361400360b07482e00103500c0307460520480c00c00d0a40c541c10206c0315160364 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 32532856 1250 32531606 32531633
    0x204060b0a03021306090b0a0c03050d0504081c0c05120402030a02032b020109080708070303060e070906020f070602060601080a0905010227040506130b0609040606020a0201110c0904030804 83
    0x16140752200035200d0014003d401441140012400c0070303500080c19800ba12440d001d555045038854600384030440c058402000780e00d000c9040000030401240c405e1100e21400340075a200c1ca0169030b0781d01d51306000d071a280c03141001004c119031602d802c40c5500d9410108032a031024a00c480e1000c2e0b540c413400000d04040e00c2c40400394043c00b4214501c1d06d011040c6010240c0c0c2c4503802e581e03207110b04040c0000ca00300c0b052000c0041614008114030404030365041d024000e1103102e4a40422200d440d0124241441c10950350900429107814040c0406901448408000003a07240104501441c110000755200c40141006041c000d01c90080b808005503600f01c00a0307240c1040c0203568902600105d008004c813440c01d505409600c01c1c00c000000e203061f000301030080000030100f1011034024105600104100e40e5510f51152041180c0c041d2074455002d80001402140c010700404e42c210300015102c0c0041460413002500801d0800e0071942d140d044480c0c2050301480d1144442d9514030348a0200c4128 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 32534106 1250 32532856 32532869
    0x14010e030d050a021603080406030f0f1b090902090303040b0a0212070b0105010f0c0c060f020309040609050a140c03010e060604032001090902090303040314070b030711011a0306040f020406 83
    0x941d2641d10015410400501e500c01003903080b41e45840314140000c4162610f40401080e582003044200302092098000f2540c2c80c80070300780051810255030480088401d425400d20214011086403994182c00c05282d00003800030388815443c0003840d200080d120f100354044c021b02d215011507003e04a9100b08110030340c8a4003642c0241e6907007020f041905210001744103190008000b0000907074042c0c0710300e5000e80082e1703014402404450a00300161020740ca15405001188420b00c07081000f507130b5a003d0800105210200060340f41040c0c0718840907183c50003110a6000c0c4039005000034121203d0840381185c0c83c000b50003800c4d03151440020030f01d102d613130300c081c0608400356000006440060b43e1a41c240744241c03114003865940d4101c1c0d4050780649a40f1a0381070300140b1040002c1981d007a498801d102520050321052500c4200950301900150f0711140024049202810f4681c003d104000c405965405041d41c00030744400000c0e981c240c002c000400180e4505038500071525160850405041e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 32535356 1250 32534106 32534113
    0x207050a08070302040c2105040318140f0d0503120406020906070b0906090706020a02091b130305010b09060a0302060c010b0a18141005100504150e01020c04060e0114010e03 76
    0x1a00c0c10681d0741c940d4540001d0703114514007500c03404020b0087c1c455222195401d0391a440d00c40c00010213100804004000b075050104481c5407502d03928036041c020010300205c80c00e0440101a410901076141d1465400300c0c0a40314400101c8086200041680c1d03408549006268450751640f03001c0c030290090410b01500a034020541ea01000031481710603100e00300704011030300380341d4070300020503540e41c10307441104056000416a000541480d55825607c038807481c00c00e900c000d000d02c40b002042d0f40b207400301400001c0103400c1401004002c0c05105003681085a00103503030300380140000d07030503000e81c407000b40704c0d20700002c40781c2c1d242e8001e40001c1c1401d2001808c0c403104a980b11000362040c48210809010340d854001d4408403d428141c031b50b401100c04036420030440d8103081c00d001c0c200d107150003d40309016041c080060002d2100003850100d071580e55412511070070b0b41001a280c10a0188d40510950410134148020304880c28018111200b0b10410048000c000c00182d0321070327000d000035541501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 32536606 1250 32535356 32535359
    0x2a040b07050123010506090402070c0602061902030411040e0c030a05030301051804050c010c1a090706120b0f040b010512010b1207050a05070f060e0d0306030308060105040b16030207050a 82
    0x1148000350812038000c4000f8070000c000c41c0d0000a80520304421a82c07200c1c1410014001810050301806101340d0243c4014680741241c2c444181c000c00c198040001613208a00b0001c42d90b1100c88450003d0310840401e49c00c5080039911101c16000084d8514020359440454601c450420020003078481800303000d031006206a810219100c0d4024003426028030400c51140765282c88504179207101f280c100c0b01400b4000d0f0864011196000140d0007a217101c218081e20302c00700500c11101754000c04660740100203452130800d010300380910703244000400c14944041c5a000f81c80d00001030015480031280000c0340c464020060b01e0500802c00b10b0912010b14038000309001e0039100040081f130140b080144001e071f80c2d59008427194480c0e1149031000135024010400080e0f8000140703005c941c425079021030882c450a80b5145000c0d820403d800000e13440c3d4804006040e0484540780c0c000317000f031819a2516040401c000d51138481c1441c0c62030074509514018042c03510030303c41d00014060050601d44070a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 32537856 1250 32536606 32536619
    0xc060905070f060c0b06101e02030405090a0203010602150402130c030608120c030a0806060f0a0509090105030d0917030903070b0705010c0309030e060307030b040c02070602071205062a04 82
    0x318003a004181d541049a0b10110f07940e03010f141c1e900c900c19070100c42c50a09aa40c007003405001405c0e54004030a02a8030328613212101ca4401c50030240107269801142c507a40f404041258916019010b80840781c410001402a20350204a42d0041b003c900d080100b42d448500c0424014202480880e00861a08036814810781e490340084045980700e070103c940d40c0400001c107007100e11444a402d44146c0c405c020034882540600803459100c1001094a400c00310400c440055982c00418044009800080d01000b18131f84046014090841640240f040003d084005031518146010380306600c440418a0301c04000200103c2d61010f00c017900307585601d6980c441054140c2c1003000c0850300b5500301420b07a04410300c40d109c6d1407400d5415649442c03151070044184132551740301500010416840c1e03c500ca13003e440318050098070800b03590003003568916020000b410801070f90030607915011495200808039100140b103030f81089030192070703119020100344107034851140b06035008410400402c0001d0348 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 32539106 1250 32537856 32537863
    0x20d0204090510020a020a141b090403030216060902040e010b01021002160c0305060603100203060306060d030c0b0709140303040302030a080a090e010e0403170709060806130509030a02010b060304080711010c060905 94
    0xd21580b4410b4048d0800410f60351142076001d4005016800080c481c070603882d1038414070b50024020300b4018686001c2e0f03042e004030744003040420303510f4548440d80002142054400d551b81c4d50381c42002001702175442c00000b0340710300400b914a08203a0300402d220804290480300c000340035900565641c2d0480d503e1a0039500c030381c01203444610901406200e007408030490300899101e050001c020b4102c0c2c0c0e0340d4204210098906030b9050f01046024000c03e8000f54081c61100e000380d485490704515070307251180d00c018041c0200c0e9064042e030424002000103840c0042d82400541e40040c2c40e58890341c001c1030840d0082115030004101089210000903280702c21070400380510b02070b0341c49103622030306500784070200c100685070b61002524000e0301b044400d202d0001c0b10340002001b403045904201c280080f100382c900a4600e068142c000251080031b150302440385408000060340d0660843c0b6064461000f0f500450710060403c2d56100485889603104102c7e03503140c80d030b100c6010802074101c0d0a00c5640c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 32540356 1250 32539106 32539123
    0x1810050a05090a0f0f03110d0305040c080d1205040206070b010303121514010305070302090d030519020604170d02070b0915060a080304060e030a06020a0c0302010612020d0204090510020a02 83
    0x4181d10340008540b030580c000c50342000e1a504030780383d0b88041d207555492a40d420480301040c0c0402901110034508080c052008100d0007500380d501103628181410500c0d16461168002845684002d80341d00d005600540c194030001903070b039400079040e921030020170850710079100c0013000809800004010960080309007040201c8440040000000b9070720f001c4a0b44440c0d000b00861001883e0340011103612a810546c1c2c003100d80c5c680035062a49580102c0c444050032102200403030300104002c9040744d05003a6160409420303100901d4039050588901c005241d10100565420000060a140c0308100307404030f1301041e6000d03010801078904504d00741d444a8260190002142d84000483d4144c90005444800d42c2d141c031028600d05440c110055896860640c505030309405850100000f04040d84084c0161341065110901c213942c492400a00311409038200424404054140d040541c83c0c0e180030410f407a41c191000103e01289082c998a044001d1074110301c01c5000149079042c0d240c2c00303d404403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 32541606 1250 32540356 32540371
    0x7080307170402090a0209240418020307090308072a03110a03050d1218060e0d030c020a060b06070b011502070812030a0b060f0304081314090106030203181005 70
    0x7a0502080341500d044088241c502960101813240484c0e40d03000203074000c06c440b007002810340880f4000000e142c0300c0085698070f203d5080314086010400c45640b8040c056030321005c0701d011491803606130070250001d09280409001e10402064100401480f00d10070700850301c141d120045240b0b80d45502a41e800d02500080f00c00c41083d006024444c01c1143e94482500d80c00005054140c1c0d14240072540018803007004415503868021803c0000c1c40e0b00400c0210601a08011134034055000e10340d840e225010181c0340c2014a4213080b03464882c3c3c041104210998070480205940740e400740080c809014402000d01510544000020703a141d981110111000458080d41c3c50155100b896640ba420321340800030250800b000001e10410841e40100e40d900030042c0030609001e414080003400d9042140d0845066100068919a00199410001c002c00303060100c800c099041e04045030900b4018400c2809154000c0085a480030340261200541400d05040302d2460440c1c3c469035014010035101c11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 32542856 1250 32541606 32541617
    0x1091a070c0506070f110406030b040b0901050603071401050a051b011401050102030405060315062101050109170312070207080307031d0904020a0b09040f06141008150d0203030c0307080307 83
    0xe45080000030ba404191700100031000019107901e600c41800766425030780b58015a5244040002a0080134050007075000726041e401c1850100c142030300b10344015110511940c48414204030602c0391603000003c6034028a00306850301380c071031410f48903406012a080003902c1c806608542a680542c88500180007808650415980c0c400040e612485540101c0340c100c00c041001608030108e401d00c040001101500880c46c00a265801d0000f41c0c05c007601020400001c14010401c540e030080d2108003030300c031502c2510704100a00d40003a40c3c0e803103211104450a4410400100c00720b009101715401814100d09583c0e0741d100910f8020440f40103168603000460790003c0d105010304011580600c03941d80504003042071070500720220307010313003110305074503442526002c0400c0308600d03d0045078020f0108260040c01d5001c4001004920310341400103504018040f01040100081c680e41c822801c402a00c00d80024a52400841c0c02d5101d05102d034003040c400010b046080240c14402144a049280c1e50b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 32544106 1250 32542856 32542859
    0x80a121a090a1b0309020a03020d14010606090b0307120b060301060201020703080a060501090e0406020403020d060e0c01031104120f020306090706020d020f0d03020a03020d0f051905040b010b070201091a070c 91
    0x9008035000c10070039140f85182d042400c0ca0703040c001d9015031141400140450a60359a981c001200c071099424116070030300001020341c1c00810240606d002038042828225078030350800701103d22902004008104100100e070b5428034456080d4056000315001030011f50f80c4e0340e140da101034040c0d0b119483c200c000500540000e0390b143c09601c1250203454050351130020351860010351000c0168064000d50300c0c95820031002005070365018441d2541841030501150107551644518188154022070368103240c00c10303640e07a603108000801c03103054542103072010303070f1829160418140c03410b4041d038025018890f00c020b0100402d00003500c030007196025170032201c030240300e4002261900381140c0501001c1c0d101940030b032401400ba8001c1c0c4030180f038034074005040080c40b201d840140ea040000c90703000203544105001d1a005401c51610005000c4c50050005003820b03134504000840501c524684554042104421a0b01c1502d8010080c02d04400041c1d0740100310000c01e1441d88501c10031600c00342c00000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 32545356 1250 32544106 32544121
    0x7090c2106030f0809240921100c170103110108010509280b030f0307020301050105030a0b07050313020d030903120e0a0306020903120d0606021009050c0f0109080d0503040b010504050c0304080a121a09 88
    0x102c5c8002180035001400c5005640d09d80b4001805d011f8540b04207001000314405500c5240000040c001c0d401550290144000d690002d084020103030007143c000c409040421080e00401860f1010341c039101031000402c2182d40500100511030780f0303e06540b41c011079040d0312040c00004060520b4034001c40080000740d03a030740c00b016034410384103200612040b0b8034800201054005d001450348981101a19003140c90541e00182000150f8074084000c01c41e401014802d000e21200701c84088401801c0848a145044000414030200c41c480282510f0300010240ba16440921224200c1c030140d0300c40710384030708040803194050b02c05c40c00384a0041c40f600144207404a001e0080d0f40707a040c1c100e0301900b01c00c07401c4024403c8098038070542c1c5061107120400040e0700030341004007401c001c02070f54071692079003003e240004440006904c40c40c0b0942c2001f080c0110001e500b0202c03034009a00c2180d0607540c1010500a507400795081805020725881c1c910150610000e20b540005100001c46800d90340d960360b900c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 32546606 1250 32545356 32545399
    0x903040303120c02010615020f0105090f030405190e13140309091f030b0712050610020303190e0d0e01030b04150b090307090c2106030f08092409 64
    0x100180000710040c80480703494825502403d21a52503100108485403515403005594081d03d80c4000182d104010803440d2042c00e2140a402072082d0f0064100c0c84583c9a50641e01d014a005031841100a4034450b284001d405c040800100b43d0421040d5052506810400d000c40d01d43d0b600b990000c3c6941e100d8101014080f08440003404020304000341d948944500720700040848900514000324101d011003c01c000c03400f5076100d99a80c3e07407154640400200c51405a03035020340f03c14000e01c088052030410680110030b403640004000105a441440281444040e10401401d2586801071102040345994860150320314103500381ca0a101c6c410003102808102c4110308903040d04603440903400d20950301c0d200010508040005e04a03881c80d0f4407100110b04550342540c0180210b1550350380a5200300c61458494520001d000303040201d10b01d15114010004a50480108854400226841c040d039984908a6180c0e40b48101c0d112461450b03980303c0544d52003000b20902c05c504480e010342040f045103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 32547856 1250 32546606 32546609
    0x705010f080c030a0e010b04050a05011a03090a031103041205010b01030c0810060509010212030f0403080702120d020a0507080a08060f0303070305120406201201061d0f040b130b09090304 82
    0x40c02c030915503582c6811010040806082088003035486c1d032115401c0d40d4960041500924020b071000500f0b501d01a45141301c0000341003421440d403c00d00800020301000b0651012954160500c041c0e0034482189003030a600c2590401e8a00321902c150140a001e4154840c400c038081c00e0320b00b008500014007080d103000e03400320b0719490140400302c014403001e8840d8010b8240700806004448450001c520400d0280d001242e5181145a419080000b8140e000088507008120fa0002d0030350301000e11800c2c1d50500c03c0640814032a50009420311200380b09a04076804a5006550580c880c1082c1c18000c20a40c01500c805218100212001c9007500d000300c200c0700400d032700d510f603207180028404402c1038064000b0f00c180c4426036100421103400340110900c4203c00d50014a241e41d136a8401411071080806800801c100105000c1f41818002c1d83e01c40c80b80f8002044860f1101c164035040000c000e00100005c0b140c000c51410210442018640c1001e0f09205003104d81c1ca0042e038a4041941e81c0340180d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 32549106 1250 32547856 32547871
    0x90b0a03050118090f020409051207050a020405060d05071521050711030a0c062c06010905092d0703141e0a03050406080a0204050a150f020a02010e040f0f05090705010f08 75
    0x405c00050010315141d030185000c9446002501e941c0b40583c2c0e024141c9030400d407002d90b19608200450021480d02e0320609500080847d0a41c50703400550b15070301d03500d10030790003030321012a0310012015869000707810110601c8000a03415001001042c3c180c4007a00b02510300e4404500041d0034034001c003002209039001e0b0890780e1780d00c2210b01d210f41c690750042d0140ca0f00c103c0309010791124162102e000a00140400e5030388500804507940340040300c0d070841d80010482c0d503c9403c00c19100303507075880c0174011040256210650380000c0c502030543d6030501c03030560700003000020040f03901d045004d00803c05645010180f200e1880381c2a0040105849107460350340200021820007040c0030560140c99034a0f08052001801814240c443c000701301d050307400f40c000440b6000c00440071400c2a502c124900e49404062020300980d4900d41d0001c4d00307204406d02158803854896400107680500740e4481d0204140e404001c0c081170800f41004e603210320171401038600041c900103202200a002e01c05c0c49020305034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 32550356 1250 32549106 32549123
    0xc09051f09030f0602071505060d0212010e1c2007060309170304030c0c0b0c0703140f070b040503010c0203131514070c050a08010b0619090b0a0305011809 68
    0x30055a060380d04006400c80c4107002000c10007001083d003440f280011039209600060313031034040e030404200c505801100000e0a40c00d1000700701c460b0300e0f042c0d072022025130305450416400f1440481c0c64050b003503008030a501e500c00d01c1c5114030039650716940790182c4901750b200c104800f4044e2034190080310202d090118580d00151080003080d110760312426542e40030f0803140140901c250007000303081d8020744054001414101c440020700c5805060b07103000708451542c65160001e0141c5e0b4a07191801c42c0f0014041c13801004035243c04010500515032962a10020b41d07601c1516181c1110351501701d80110b078082e41c03800c0d141c40c413140e0001084401108080e6900c400c0d41e80307009003950344d204482d000507081265200c855005066a00042e15003a0311850005000d641804107200750700034194080c2c25582c1c18000600160707101d0104480c4142c4007406102b0390160402016614130156500005903d100020341841c2d480e4107030301a078142e5201d401d004005c0d1031500358400a4130000000900b8584 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 32551606 1250 32550356 32550379
    0x31003030f0e06121e0108010b090109062103120213030b0604090b0c0d0906050108011d010612020d210512010501030c0e100909020d06080c09010f05091003120f030c0905 75
    0x3513400003240e10890a424144008004c42c04d90204040e007079210021507912003c0303c908900c0c0600c2101e000d464415810481c1e00d01c0c2c16000c8400c5112030907074900310640c503034421041c544500401e41d41003910140942d03030b4000000b42c00b58090550301c81601d04c2103200c0301062241c40e00d030140c040d007181c000800005545840c26540c04c25400030700c588400d07945c1c520381c0c18001a8280201d9009000721000050030840326020001400490b61a0001c0c0da4582003007800003a43c1c3d07200d0740541913015105010610420f140c051000000e288c9141072002403d280312051690242c000c0549003581c1c0c00b0192241d80e0741d0019800c1da1040300e80540841d2440a000c4240e0404400100c0c150300d1a203000094185d4a03040c02007242d04c130300381082041e03071246820b000c0080104926400c000d8240d44c510415031404c100c0e82c2b65a00c90b80038140c46461801c001c1208021001000c6014507004117651000c450303072503005480034074040b404402083c24410300d00e00b102c0c0036041c2c0c4806c41d140a4544074405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 32552856 1250 32551606 32551627
    0x3040209041509060603030c0201020f0703120c03030209090a02270306010b0304060906060602030903070b03010b030408070302070305010c260405060411180408070311070803090904020411031003030f0e06 90
    0xb0400c2c85440b50310340c0d8080c01c2c800300e8524000c5a0040d8040e44440003c40c4140c0002401d02507100030b81e5249500c80301c410800a60070f0407580c2d060005a1130442011620b602d000c801911402c0091a44103502800303010100c5c0c0e40d0b6006150107240c82601d113880c2c1103c4c02c200141c0d0b10400103060390541002c401001201507a500650388a4424a0f0008551005581e840101c3e0039913041440140c0c80800c0b4484c1505082143c20081c00c02942c90a0030342d13140080000542c8401040100100004114030302098002c000907006903a104000b480300700030550340104600c55a990558242c5003541d00f0a00b45144aa0950300403500030f0302600403560703940c8502c08030b81051407195030413600c5100030510f00581e40c1c0501d4002c038410701000ea581d1061b4140246034240350b105404d100c4e00220340030419a50000115440c0340b400340d5502040790394900008004000042901b54040c00000800c88000728104c1c000040da0300c40c6d140c1801c0c0080c40e070001c80300007402c0e41c4929040142004108085e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 32553962 1106 32552856 32552873
    0x90f0f070e030a02060a02070e090318060403081e090a0e1806010e0106110c04050403170c040f0b130b070f0506010b030f0a0f0605030d0f0201050c0304020904 70
    0x81407400000240c60f00982e4100900c62100000e0030100f96000380005c1000f0444503040c602d6520f17018030341c20349035030000c502e280c00400700b038010524a00d400c8083d6004d07a500040100d050401125505100c158442074400700c030542804405c81503074601c0c0c203a02c00707400c511440305210308002006e05a240c000d14240c01654104030014480c03001c241c903071941194000e180c100800b8030070440941c1003030244184107401c40e0500041209154000030021181880c02c880300e50241d88111404009015a0144a03a00507030700d601007010358900d202074075803075982d401d55201895460455460380da1120508407584010340480c0000d00209004c11401003d1350307041e40d4a189040e04a050a8480c0208482a01d46d651441001d6150039540550042c0001804031990f904854402820407158802807400560030400054104900070b41a24001c2c0d6000e0200856900c0c0d541d1542078 = true := by decide +kernel

theorem cover : BRFrame.Cov 32374106 32553962 := by
  have h0 := BRFrame.cov_init 32374106
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32374106 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 32374106 ≤ n) (h2 : n < 32553962) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
