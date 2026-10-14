-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0721
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:21:53.895983+00:00
-- url     : https://prove2.me/submissions/d830ffce-7d54-4f5a-afa5-3325cf6025b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 129496402 ≤ n < 129676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 129497652 1250 129496402 129496427
    0x908030610030209060328020414011d030118061b0804080702060708030c180108060d030e030705150a030b1912060b060c01021818060108040503040b07030306090c030b03030a 77
    0xb001801c02c102880065542da2040e1580d240c031249003213031400e1414042d40c2c4403450f03000c01030301103140914104e1501001d00b005100181440034a41609140418060303105220040080081020724010911000d002d21100800d071101403411855010804400880c3c0c080311206486a11013940c0d9a40e0751101030b402040e040780c201e402880851b0005100802660103a80e841450581381c2144118601648100da0011410800302509100c240e40b5820a0840402c5c0c26107085102d442c441800304e8075006841d40030782c0e081016810595008940030f00900706d070740943e50b0148030f008001d004000f194081501900600e01c40d030300007040351031014548070b1195840384601180030700d840800110b0750703080b202000c2d21503500002c41c2c040c0744010b1421050091412580c1440e04210400d1044038800001c00c01e50610012001040a1000402c20350700141415490305548003030602d00140034000c20712914141c103081c400e488103407034043c2c000c0c81114100a0001c3d03080005003081200c82480010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 129498902 1250 129497652 129497657
    0xb0a1d07110d0509040b101407050a02120c030706030b15030a150303200604200102070306020d061406032511010204030c150c050307020f011e0c050d030908030610 72
    0x1201d0300107051149020b0500e00d621036588a94541d0107010981d01121004e038400d2011180c090492a004034010300c0d0710b11792a040d0754071405680f601c149421004c4002030f41c881e100c0030a0b03210314100018607410400c825000e40310955540d02c01035059502d81003949600c212003130000e40040d20810702550713001007150f00100b56148600206108084160416800909445400344025440580342042d80c020080105041e10b00341c0c641070170900811103105034025000410440340e03072003080700e4005580c020300c0840d0344034000019580108107600c1800341d042100d0a55280500d4080309a0303205110800c041245280105200072030000040c11441c18442c0e414028241c03540c003480644003941c1b0400c00301c00101e050240a0071083c000001c41c404000c290b004010009401005030740c0803a50643d03400744080704800041e12000402100d0902c0b50130308251007564503502c1040b00000d24000d05c00d403202c0031441c99080f0181c03804c006018013003a0b01000803800e2070500c034402c090b4100c1c1d03e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 129500152 1250 129498902 129498917
    0xd0305060a030f0f061b0219030e100e040b10050712180603140c1612030212130b070203030601020d1b020405042006130311011e02010c030b0a1d07 65
    0x240e41d001d518002c280720540304d620322000380c102048524824400c078441460042c0c10040358000e030007540c1d001e85d840307421020b0100c8142501058020000788500e800c00030840203017451131480083c00e2040d402e1020b8070503820100c44850b40d090628841240343d0450f92643e2400c2d00c56191f6501d99210003080c6010845100c03c5403401200300503e40b4090089954040303032000e03e82420100c030703d002800c1c01400c0d882c10080080d00d025892810142e080d0b002210808000c0082e00690003802035013003200956441a04128402c2c042c2040e0b04010391180c00f50300381c0c94542a00890350f9010484071680507a1050307401901d400c0c080c102100102c0c2201c5940030301603031181d001c10141d1b1801d03039088a09604400902c1c2d03030450b50400550007181d081e60950305040d906038402d00b078498103100140444111002e103002d0350b48940103000d04101d2185c0e040e14280010b14000780209056115180000e140c01c1f0302480500d0034a5801c4115280440c80c484840300740c5031703030aa41100c013420000500120 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 129501402 1250 129500152 129500159
    0x1081509010603020a030f0c0806190503060a06030210080f011205031b0706080106080601120c030e0a0803160306050603013302010c0e0405041a06010201091b0303030b0d050d0305060a 81
    0x21482414060100d03683c0150700c0d040d1444000e41601c00b1180b620030b004c0d00300845040d080d40d2210100741c0c0a6400c4a0f42603034541e8130f00302e04d0b20100c5940c00c22a0580900b6041006000071a0031580840f8425501c2890680442408840d800d43c1540e4400542d503096004006024000c010008003a0084007a6860481c6400515804070000084005160841e0034200512500650313881c0c0100618241038905103084400203040040101526a219940d0400007020900c60362104682c00100d400712803a6540c2030404003100e4000300c800fa00c2c904034602050080038401d0042ca8203c4801528044c1141d00308601e071168841051220324a144401c495130060a6030807900041c2d06a03542c000080c10b02230b509004040c0703500a103031b5a01030f03410942071000203002401150303441c9107201c00f02c155549550700102c3c050108400064a00307011508441890640c0300702030b0040b0b900c00c0d1020040e40760500f00f4000340b4901007001503c0354203c0b24811003030a000b07070441540442c0041641c24035544 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 129502652 1250 129501402 129501409
    0x1a100504110405130b040b09090a02010503180604150509010b010914030a080d051009020723030415031512030210090204060b0403050c031005060d021c050f060703200405010815 78
    0x401340c1000c400c0c00c1e190048601c080c1814812a8045602a1507071f0715035142842c0520390f03070407079000000d041000010010b28902640c12070302e0051800e1005551081c205424a486d400306084041920145408003140b0613050520425450441c180c5484410603e84080c401d4806504005241c00d400780020503000502d4240007885a10210000001c05040200b182c081c40c290030b400c541d50720f902c1040410b01040c0300709042001001442405840d104c0340001841c21030040c4d5100e500003014a0080c241047c0d0181c124002c100000040d64650559441d402e1500046051b005030240c1c01070036000d4064400d682144900900240c008140b040d5280f9140300d01e07510643c0f040d1000d03000b19400880902c0d01340061403290f00050f500303001c0ca082840004580061350301009208880d082d4030300070b400030171181d140c0140ea00101501e40c140c501070081e82d06e602c1c040301c074400002d1521004403a0510030714004541615600c10340c0d070519040400640341240c0250000d095041003401702d040c6a603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 129503902 1250 129502652 129502669
    0x82508120d0b0109050d08090102010f0c03060e0603030406080c2512021e0c0d0213020301090615020f030409050405210405180103050a030509180c03041a100504110405 74
    0x240009050703645a19078090342046926000c1003a0400038004020015617694114071807180350800c0c00b1503947d424020050703004204004c1035408160a00c008444416003542c032010071200c80e0700e5003161541c0c8a900b003503120300c46c0b1f008060228491002140030440c858000d4484110701e1040d8403868001a06100d50050040c6012200c1d147c0040341c3c111082e60612422806c087d040d070351400c80001d16179030f040e12111108181405483e0010b0f440c82555200c1d1420300b22080f040d40119500d50715081800054034450060144026507004404000c910015090050980c00c130051406d0500784100c000140601502c241c480c0d104460b0f4940202c51448030110300600c840a038035940d90324007824007801c6807400218018455403040100041080810052907a960510700950759000707020010f11407000750100243c10a292804000303003440048000d602903402600100d44054420001d0380f036000c1c0850700340d801a841d07203108000c14100368110004d440d07001204181810385840200b941c85 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 129505152 1250 129503902 129503923
    0x51e070c030c09150b031311030132010b0a020a240e010b120c030303010b03100f0e0402040f02090d030c030306180204140102011407050c0106050405090f0c0109082508 74
    0x141d84413003400c035201c01007070000c000b001000c0e01c507810352130440740c1105000088080a0031000c03000360b103101181c1d030a50104825044001d40d0000700014441060391000350b03800400616951880080f8101e1428029250150281c0e4020300c6403040c590307543c245922850070610b110766081c1c038000801c40c1c0c0c41d000711051725030210000a140e400010800c50101800f54007022030707030800c07a0600c11949002c8200c90640d01600d100c80d0742d81d12040300b40f9906961036030001c4400c86092801044500f500540c85018a000315024404d29812200c941c0480c401d064505d644001080c4043d00000e00030307800300251a0107030030b00044890b07072001c4441c4a88640d0b074000000710b40c002400d1240340c2160b440381e0b020001c280300800641c51000100c0000e08000b500300c005011012401a403000f409400500142c280034005018138200720086654643c0440e120030080d02402ca0010040c1d440380b075a41040f9070305800101154500d1081c04180002400c910741248000031a001c01c0440c070070040103028 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 129506402 1250 129505152 129505169
    0x12080d090812010f15050c1216050111031302040e1509011409010c0206010608040c030c0603090b0a0902010f0e13060b0405010f0e010e01030e0c040903110c01051e070c030c 76
    0x480c0c0d03800703402d51640c60b0160000c1d2060a00e42206025196803491721100038551814442d0341e4098080c1841c1c64084004907100301d114001455907980c1e000d901044420a02c0b940083c01003507109400610315000843e01040d179182d801074114050b14041d08000101e6009005540d50001d1400350000d0140040f00d0313070781c8680c2d1a0900305400d02502c038042980440c81100070051100701d01c6000752103031411701c00c0004210720200480d084c03200c2c107006180111360111101c0c1c44559a040003501810b8030003000d07190720000d00006030301540c03603001c1c00b28080ea0581d87c070015220343c00b100f51014018111145e030007800b016204921131007140301d05c0d4080c2c50740c1c0c2c0380952034516000004090000041100c1c0070019011503d010b143d8001c0100c2046d203000b401c0c003007030144003486032903d808291014a507103e410010110300b81500700c1200e404066540c8152041c80b440d1600560751841160100d0300c2200c88440540341da118000d025160407803050094180c807903681d8441c3d04000c2119001000c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 129507652 1250 129506402 129506407
    0xa032315030105040803060907110303091005070c0f02040c0c1401060503010c050a17130b0a050402010e040b01140708120c0a0912021c030201020f0403060f0608061012080d0908 78
    0x84480a0890403821040210000e110b1481c02e69500301302400090700c1e65004a65150201308094000c4044044514028080740e8a038940107003110f9a81400e03840100b5a68a0440841c0d8003070320074004a851036800c00c4403228032012560900c0001c120030b2940e00d0411040d50840c500051004141038808452180081203aa0404040600f1a40c101480c40c00303102c030400035807613401e420001c0d0b81c21070b03402c9071358103980c0c1c0e079a20005a9240312100d10045c001c1008000f00b010200060b4801802207000ba45c0300200c044045080c0000c8238001740c242e60224601d510141c0d84511031100030100d55109501003070401c66180015415140f080c4da00080c00000440c0d4902803e40c00071102008080d100b0400c07840d0001d0386c0108019030044541c0381c0c0d240b03e4455401c0d09050003501102d03a003401c00031201b03071307950303a641407000042020221100c2075900f040c100240700301e40054030234091054070240c1443c0e603152685021a800b0800400c5800312028420b02d0060951841032040143c010703507600e0b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 129508902 1250 129507652 129507661
    0x1902010b030d090e0711011103090d09090501080c0d050c030604030c0b0c0f04120c230102070e0c270414011401020604030e0d050703080708120c0304050c060a0323 72
    0x142020078001d00d400c20440756550401071548220086a017001c22820700c000700d0001c040b4110301400d42000c95080b80e09002040c0240f60800003101007441800381d0b00c58500b65114440d032025070342c0a10a500b255030049000282a1400741d480f10a802d100300c086802144085002c40d00306042107405030081440207100106000d0152501540701100c40c41c224940203860407001c499001e940151100310b00b544884804200030355101c04042d00c2e00d1541c00c0001c0d0f40c0d032690554010300e03541c00d0900600a518000a00104001c28140911008600c030f0b41030050640e9402c544034841003074003001c004521010b148940f039500c40c0c002194040c1d10040206c1d81000b100070810303103040c00c0742e504641c001d00400020940c0700c403000040302c07002c40b541d03402c16030f0b6814440e02c0d1400c0b581001d01141c1c1c002452104020007075000345409401c4043c1c00603955110807000c0440e0208441c050074503001000f409085141650040002e14240d050008000c250804003512014180c80315a0b50084045d0611 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 129510152 1250 129508902 129508909
    0x30601021c090603020a11010515040b030102070b1302060409060806070f02060906220c0b03180f060f0c250308010f180c050c030703030203270307171902010b 70
    0x5440100e000c01105000d101007200203000c1c070300034440c000803d80d0115071941d96900c202102020f42c0c005800a00ca9401c2c1308e40316480306034290120520031454007210921030b0606000392100340380c00c03143c14041d40e540d0300c10410440500b41e00899226204000c046600c84103481601d0103840e1140042400f40780c4244050000b1602c1d0890701e040d5441038040014504000a1050340410080040c0c0c0000c40d200321040a02c885070000145200071a040101e090462440511300c0b41c103a50b0702c01e00c500758200724890744038560140d40a200b40c005100141031003003c0000c031500304009043c205c0c501200e24400d404070b515031203031400c7e00c80104c0301510305043c2d001126601416444007041c0ca583d150010741641c00030780c14a24418071f07440f081400e0789103001307800f80e903101200c103825641c1c0ca01d15480e008009500031520071211400d00343c003c80f042b0300c0780c00200035001c03036070802949403071200d8031105541040142c4202d5025401c00011440c2103c1c24501507041600790004a511302c40e401c01c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 129511402 1250 129510152 129510163
    0x501140c040312030b01090506040801021c020c070915050405040506072007050409060f02130f0801111204240606030b04020711010c08270102252c0702010203060102 73
    0x415000150a20052001c181c0c440400f80d2840040d04000401058204c01600c040c2c0051f4010303640800f0120700080d8080d4103400418054800d105450000c290304442c2c0d00480c000c1a500080d9a0310180c414032070403001d903020080c1901415034800d84543c1d03540005042d200c0c2210100c4841c1c11940a100e07015070031558208048803050310180285140c0b282ca5941c400c12442800d1043d5110046042807102e07560020440e0065994295960380c1d204101c03a410424a100300091415950400181010180b159428088a01024501d003051904026507450380203402a18a04040300545c41c9007410240c1407000c007450542c0103d2243e1400d5005000c48030b03801f0f01c03140a1401003241000140c002c9007c010907940034204810f020302c281c1032903210750150480f1807101b038045001155030013407407680c000e5142809908407140f204c0448400103440003120f01c00c05002d40305001c02c0c401d80344500c03e000c030304180601d4180307410f0005402e0b56100d01001d480000140c0d40c0081401000c0d68140300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 129512652 1250 129511402 129511411
    0x1706010801030302120d200c071202030a03030506190603050601020115050906190902070813050117010311060d02120105040b0909031207110f0c03010b01230304140a050114 76
    0x3040c0169600d5901d0294403035801207800c001400c0c0025400b194094990310090b01c2407007224080018400080741c8880a502502454080e88240d10000807005540000560301c281e019002c0d24045500303503015000f4040180030203900c0303118100240004082514071030001d1002d80d1b804103403410302100190031102032242da862a40140f04042c009510b0fa11990b0703820210035210104222000715420301034043c11703000381401d280005a8001030000000242000085000c40032075225900c031300540700c0160402105520040020040004c955440c090351041900546100c1c03030119442c3c0c0d10b8040ba8814039070503e405245c40300600517401c15100303505880720252082801030500c4808140e40b80200102560150100070000d0182c51040c121180c0d07000690007181c580c585c3d0030082c1904d410486c040c1070700a41c6400ea46000c40d43c80b580c6030175900140c81780e82c103858042d0303842000d600f64002070050b507d09900e0460403445110402600b000b640c0581c0001608048180084451040180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 129513902 1250 129512652 129512657
    0x61009051501020c060f04052101060f150f030e07030b040b0a140f04030201150303050c0d091815210519020117040203150108070602060c2b0e0a03170601 68
    0x1030316041c2598001400c0b030b10b0000e003212101d03245c05070300558a0261203550485500321286400c100420200401d90780000500c00b4024001c0700e841ba0764a0f201c40c90513106540c9068805c0d250b4407a03130740c00740e04a0000d50040d490085500000900c605160440325402154031400c40c50400013400f0080c00140c0e00b25401d072b0000c3c005000c0d08000c03210300103000741181940404442c00f00f001c040c000d41c888101d007058103118606d010717075a0a000c0c3c07040d00005024415401540c5156020502c24503130981640d074021084002103016206100c000c204600204e03076007003000ea002087d201d480f82110030240b038000114260041c81707803401c50b0810142c0038100c11580e15291010300140e811071181501c81c0c414041d0b080056984d40002441c0c000620102ea0685004c80c1c0040782105020a1a000340c403055001ca070790540b41c036402c941c01d0344501c0e8034602c3c40a100c1e83d0004c10aa9240c0420103248921500104061894003101c80c200700c1100c0c001c0b00030401c0050340050709081404e019034890000d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 129515152 1250 129513902 129513931
    0x90e0c0d0206030a0f050a090312060609060309052b090f05060304150f0e010c0e0607050d0e0604181e05060a06030c110703061406091506070303060806100905 70
    0x60116048a0442200034401c18000c00002d038180201d40c084800c8011241081c441400c00d50401402403140400c20740000d800305958810440b840c1c010302d0111001540c405e00d810f0b1514000300c00420440d64122940d0282070501c0314500c4510700102c0402c45540c440c00454074800d8005005c0703404030b61000e00e4000c0ea07034070100302580e502d100782d0b5402a08a0940c14000d505501054000e0030511101100303145444c640e500e001c01c055105840396010364540440d1034000c7e01c2045000e00510400900d503900a03030160400c14880c240c0342c000c402001e00031901705078450301901802c1650021442d05983d40e500d088c0d803419400550407101c8110b03100c00b0481810410007207196031800d4044c540515850301c2c040f18916114402d502c1e901c6142d18140c0308017980300d03d0940c0240095080070b00d00c0c0480407010a001d8a04903030407a02944031b0b40040b0700da901121050004580101c0c0055085c10703501e02c00000e054100707006003442110845d00a26041c1c0c1002c0200c1c084500180401c0210350701c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 129516402 1250 129515152 129515173
    0xb0c09090c0a110f0715030207120309110102010605090c070201020712051501062d09171c030b10080615120a0e0304060203040302090612010c050a02150708010501050a1103040f090e 80
    0x2041c0c00c0146c5448902030070704d03001d05078000d6019100e1900002d102070304d29107483e203403960b055000c1c0008074414102d104640d0006401207081c1c40c0b05006541e48080c1c05c0f0701140d514507000c0000e045007032060064410442d81c3e5114030f501c111600b08182c5058218944240e0000400c944e02400b400150800140b442001203400095000c100c05540700d440c12046c880311064080c8014400810407603030200d1586924800107525030b078103207a081070000c005110302c1035154003902a64038030040c0588107002840c0480411138960b103010b06000c5d0410380b0001c011340c0302c01c1a0030040400075020b5044040509001c00c07078000303c9072880c1e0041030940060105110169020080b0b8048070f804880f50307602078541c08001020320803042000400c1c1d42c40c1c03814403412240c028014154061181d026510b00741d00055194642c2581254814009400500103101795030080c00540001c00291800401e0304203003142d0185154465000505c1000b1030b020100500c0b115170103104c00c44c00f550701c094103440c2103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 129517652 1250 129516402 129516433
    0xa0c060201110306040c09180204050310061415040503010911120703120e03030c030a090503060f010b09130e010c031b170f04031e0f080a020a08040b0c09090c0a11 72
    0x601300070b00c510b448902c4000310768411070718200609424801c0801d60460060541c00035402440707014003c1c004c2e00c110136412500c03449450112251411f910003d2140c160410074200f07098864181e090209010103c0c198800348542e020007441041100d64101450341042484440c003068514542d0018006100144203200d0000c116421400e001c0e030805001400a820b500130f820000c1d039180700c0801e4900c0744551000c03441003126002d0f4141c07141034503000250303e9400000d0094000b1120104044422802c000d904404055000b000000f241060495864251524900610000fa0311080310b45482c024040c01d146020305c29003440314210068000c000b03080e00780100503100006200c00054181401103104007030345010500c2c1c501400c50481c1001d4050f50a03000382900080811001a160b05218821030389450700540b43e02d0071541e103030380d62451103c0e0010003044041c4001e010888142c0c0f40c400056018070b82c032201c81038031a4190100140312000300740b03460307a250703011241241c0c2012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 129518902 1250 129517652 129517657
    0x2012102070c1202100f0306120821010b19090b07050705040e0109021f020a2109050105040e0f0403090801020c0601030203060a060f0b070503040e1611030310140d02120a0c06020111 80
    0x102031b06202c0180c4140c400c0030343c000c00321540101842c241d030300180000c004409004096102100e4841c2104006081480d20594030074040c04011810030013500ba50303d403220680070158601883c0c0031b03e1981e02d58511b600300d42c1149070200d40940c04010b09104901e01405551404d003440d2000b0040c031107940d00007603014a60b0380d5211082088003243c0c40803452003404911843c64000300290310400048108180c02250b05880d00d000904120020071150b1140007141c08686044150780e090740c8682d020342c01c443c1400751044042c000c80203030009000000303002418107654014003410740da600d14014141003071b500070301c041c41c1179150010034000596520012000c1e02c80c1003540a441c0c90036450220b107140301d541c20000f02001c502c410068041d840c5405007610800716a9007003a0a55080221a40c0780010b807a0682811705c4024203020400419284441f454001000101407850f542c001c0b40da901c3c0e8285000c8400e403c1120b1400c00d000401e40403034001c10a81c8000c101c1d803080780b41c7c0c0000c50b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 129520152 1250 129518902 129518929
    0x51c1101021f0b04091205070b07050a17060a03050d03140f040c03080c010908041211010c12050a09050a0906170303040506011403010f0e030306010f080c1602012102070c1202 77
    0x85944140d00c40300f41c0c0f142e0f4031101003186e200d03071a0140c400b0111400340c19034012440440386401800006011a03100303600351484040769445010f6918070307082e00e0302c2c2100c02c020b00c8a80c0000364480f002000c41c1382000990801c40580d1070002d000481201a40345020000303040d401c0c402000b50501001444218800d02105c0c0c1094015884403c0d0b046140d02401c40b140c0054100c001c08200400e07030b04080504034400e184500061609054041c0040d119500000405080300058061400e01a07000e00d004080c03c06d070610780004000c3d11000001d10344181c60304003545980e51805c0034406c40c01c1d0455800c0403a4110740045095103020356a80c0d5940c4014060120111502c400e4070b1200d8809411400d51071007030b10804e00260711200c114a40d41c1d042228002c0c000b030a81c140568905020703038104c07030054001482c46031a105c1300800344080d00440a4040703042000000d915400c000ca50b480f009480000b5400242c2e6514040c1003510780380c80280c00140764191a1a005001a5243c03c00d4401c807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 129521402 1250 129520152 129520213
    0x120905040b13020f120906070e0301180209060a050604030c080d11031c0e0a120f050c060402150f042c01060f18170a020a0e04150e07051c110102 64
    0x4e41e9100380c2c030221103002d1050007441e2528040305120401e800400c203a4800d04455880c48200e03021034042600b61021480d10304000c1610b030403083c0160a000440c1f039400080641002050b598410100c2c00305d030b01c16801500d0141742c00c00c082c85a400140048a0328500710314044a0003980088141d442c1e11504807042000c0c1011001c0b808001d2f826008144980104002c0d00c0c00c4070100c0c1058030b11410740950580008003150401880180540f080d24130309505040140b1240d80c603a820300510305d201c41c1025000c09000e220031424100c11701d0007400645120102c09040644100300d001035200c0345c3c40e1441d03000c1e20600050000039403010318141c076080e0030b281c2050f102007440311302c1002c10242e401c811150a102c005640e20f842e000204506c00500c29210011900d64074408001d883c0d6060342c00400d403122400d5941104a0260400300d0780c10348102c280c40d14030381e03118001045003d07248a1008800c1c0000161018017169500104900300b080c0041d02100e01c0c440700d030301c20009448900880 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 129522652 1250 129521402 129521407
    0x51201270e160e010f0909080909130507050607080d0504030e06041e08011104051216260609030d0c1403131b030b0a090311060103120905040b1302 65
    0x9103498180e00300c10803100104010400c200110804a07115040410010a1256001000250300e00c07080ca03014129040440b50a050340d0522071080050302c5070410580300504e060001c1802e556400c81708500803144040d040c0781404141ca441c81c2810750b1507002d40d118007800e210442c0401d003004225440c1c1203010100184c107039148e00d0251048401c0003200c5130410300204002c1118050044034280c055000383d03421002c1603445098a003a03814165010049120034041045541044000b48800f088000c0603108407011301c101800c0c200945900c040700c2c001042034038035440443c130f00500c51621004c0000d05001c0ca010300c0e10959911a00c0c4440403011354079501c4d0100c240c0303c1c452041c18a902c0700c0e1445e40d01e01340401c0c8050a5402024151110701d00c60b4041c17118400c172201076400b2654061400143d55840c00c01078002070a804100f9401e100c245051143c0481e130901200c1d02071442000100b014440c6584014882007150f00824000d916100780c1c135241d981d506d141e410500078180300150303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 129523902 1250 129522652 129522689
    0xb09030f250f0305041a090d02040506060d14010302040b0d0b0403051605060c031005090403020607080a062d050f1c0303060b07080405041a0d0f050f0a0308040204060501051201 78
    0x705400411080034200e5070700440030000b015480801401154800c07918502501d00e0080c00e1110741c4202c03c0415449415070340914010b00309034201c40c1c3d0210b4010001e90910503035008443c02d595100c0c2d0820b10010b1140b005004610309440349081940301650103030030740c000503503032600c0c40e0303030040c1c00502130007008100c440212401410152405a100c02541c03024281420361004540003503500c41d200e10214400800c00b0b0406802071407186403d0b600030310203501d40600507a15040d01a1082d0113068880c440440c002e107100700c807490340c14101c1410800740c094021107109002e8094003c1c51140400100c625401c0d540c81c41c0c48403a2030b06204d0590014500b524080d80140883c0c0c2c49503401500100c0e0802c2401071840240003101e10580781803108152024010380e415840c001c2c00ea0f440540190a08040b03424070011801e800d02c10402c48400307000b6240060b1906c40509411000503115a0801003142000d008005c0140b000382030070390419081c80d0810070210014001c11882d180c3e007503a401c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 129525152 1250 129523902 129523957
    0x50c03060928150801050709090911060307020a06140c18040f1e05100506070f1403031503010605060301030f0308090a080f071e030f0302070c0f080106030b09030f 72
    0x1e4100104541003524900b40d80204500604000341a0784000200082e0010b070400042c0180341c032810316076540800c003e00708240c0d8801880c440c078040c0d03082840388140240d00e8854000447c040c0390316800510b0460751903e04001511503244c248403030a034002061107084001002a0350140a462540345200015100030400a02e1a0555542c0325070620f03183e041c50074071034000002a4000c2840030310907981c0305030456003050a60700c43e55421400030822000468504404001d41b03500c5010b0005400d03806090161030354001b925052aa590301802030b141c2c0f8074091290500609040c5c0d5098211f41c5151900301e5440782c8040f002d81480207140000314503003800e0190701e0f602c81d4824500343e00e5542d808101c03500da802644044440700041c1d0078045140301204404c0d4201039050390340c012100c00005080b00603403c1444125001c0e581480c011500001d96141d0030040c0858000004146281d41821103800102038030048c2290004c10001000c290040c080303501e15001181c1d40c2d0101d92034501e14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 129526402 1250 129525152 129525181
    0xf0c020d0606030303020c0f0a02150f0c060f06011d0f0d05100606080403081503060a02130503030313170307050706090c0302060309010507140918061f050304050d03050c030609 78
    0x400c241c1c58042c0100825030158003420070350312014103c5000382448410280e03509031120000c1e600a4564501c00802e40b1114014403013080c401210505140c01c0740b0340e1a25154090780c8581a0714200003c11a065904c006041d488c0c1c0c29001110a0203030000001c20542e01c41011054060003032144000b007401001c1119100300000c400d0208055a66400c00400780350080c1d5048000481c1c1c14040f0300b5881103401c030034a00c1c010040241000d600d5404240d07000b98000c540d07086114141110001d190354051004e18803c01c810107441500300b04924180c16410310304150100c10600c14014001e0b04e642c428280d03990241e0011000032041170301c2c1401c4680150581c0025030101c000400c210001343e064100e035000c0c4c10161500b0a041000c807500070000c2c098042019001000c140403929030511170304141c0d420600203020000409680c1150500384001040d43c000814400400d00003045010403100141e0130350ba01d01005141098002e00d0300038400540082c0c8105034950109080b04200d07840c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 129527652 1250 129526402 129526429
    0x9070b0d0c140a0c060f020a020606121905030408010c230d0b0a03060911040c020a02040b0d050f030301060e010305070c06090203071e1a090a150c080a0503010503061302010f0c02 79
    0x1d00703d40b01d000008000381340c044060320403a801424039021b072407006050b0081d5440021a90064001d80c0d07034000c00e12202d400916106013143c4038007019200d03000c51014205214600032406559181c0c217292510b800c1da16034407240001c004c5c4003041c51003103030300034800408100a5241c0c0983d90310442c0c102c410160052010aa5000303000860010401c00e2503444810080d100c5c80030300c032900600b00e01704022030301400c1c654005a08034240100052070242d0081c0c00001c0d0003418603074500d1040c0caa03203103008807080d036482140d400000140025904404d00300300ca500709280a1000c1d2810103401001c14000c050010255074981403080e04550f820b0001c0c001410340242141c90820f0b4403480c40504100300d2044025020001c12440303414400d0004440c6550350203441c41000398a0305154a4669258066041c100002e0881e11000909003400405142e0150340d40c150316075040a0802d0300b04480a8400d500c00080b10380c0c00c10050b6046101c0e490141d980d410074642006642c004102800205607 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 129528902 1250 129527652 129527687
    0x21040501020d20011a1003050114151308030703080124050c0f060702011b081e0601020a061406011b170a02070b0c0303010303140322020f03031b0609070b0d0c 70
    0x508121170382121034203452100d074040301c0800e401c00046030207400319003080c0668144c10303c0816a404c4036007440d42c4803a18a40c0804212031402c150540d40361410a0706410040c03485e000050b1070300506a1200c0700901500d540c96107000d88028140400719210100e19629081c40004501603050341d2051120005101941003034808902e850b5070028020045a000590f203d00760714191948944220b034087c0c8100000074140c551080c01d40300e03406a109004080c00d0440c4608800d00d40020b030a801070311175000e43d00017190040c2c00d1030380000d440b0b42001803184050348201c51003500070035031401031001d00320b0648610a44c0e0b510941ca040f07003840d034950040114240005002000900c00000441c101ca0096413100d0300d8031003000e0792076190705c8152246242d035400a801e41f041c1214001d000d01da010b200401c02650700700321102090075030b00201146030b0015090706518004081c10b102c40c95200c5c3c0c405000c1c1407290705102c3d0060341d502604841c0c0340d65a546503180721800e030013908041010309209 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 129530152 1250 129528902 129528911
    0x5090405090705211902030f0d030911010c020102030306130605101214040203120f1204080703111c030e030c2515090501051309020a0221040501020d2001 68
    0x1e40880756110054032596008002e03020740d03140081c400030036010481c10450040e00c10310300141c6252000035803c100c1668075000e08404000140b43c01c11001401000c40d4501040341ca58a0420b061140050b54200f418070426031a01c80050381e002c800c882d80900201c4100803401e55222081c5e0003044140c200a41114207403040901550b00039100380f0079609803036000d0200704219902c4105655064400035015031081a25074a00070010002c0c1100c403100e4008642031003d080c07641103801000741c4060304c90b5280010420b0a144c2c0c01942500d1420001005010031071400c0e02c2414141d00c45c0701181c0c00c01d9512000102001814801c42e06100310074012152258065521105030b100f1558804001c035840c56400a0b02d4030308607100302e40b405290307114440c40340c0c5000b006540c0303503122108000807030303403900740c0803801070802e01c06001d000d104d56006006c07488500030584201c01c04040b146030300000c00e000130010360381d00286480400d0b00500c0d15081c504480c0500200908191281100035402d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 129531402 1250 129530152 129530161
    0x15030c0302011b06022a071203050703020c1c0203010e28151a0102150f0c03060d060606020601080d05040b192c010e01110601060509010207080610050f120304031205090405 76
    0x210952031b009840100c81c29412141d42c40c09141da504c0c101e100ba01d003201049410b19010901071805482e2850007130042d6101c0045000004200a0004504c0301d0300000a08008095050074884d0000803000321005103810040514010b41c04651617001103908805665182c0c108244811240900034500c1c1c01441415500e000c0070f406c0340400c080c0e003030040c800c0242c00b840d070111840c0d26500580001c513200c0c0954691044480007684020201500555090700318000200390b8440c150051155a0190444d5410301d0311060800c0492000d6030104002488240300e240c00f108100c2d0140480c00c00800303d55081c06200f56200c0040c803440402400b038843d4070215180e0340d04004234140c4401d07130303420085943d41001540c45510441605150391720403001801124000d0300144180c403070500485411681e02c4200710318004080310907209030590180e08020300e0824000759000303e03c0441d001c40740c403040c1300b403a1541d86c020b911015160b00e4040c800304401d81d005c0c10494943d44000384c0140f001d880c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 129532652 1250 129531402 129531427
    0x9090f01030b0601021203190912020d08010b1305040504050c090c0a120c05070b0402061306020709050108120f09010306090c0309112403090f010507020604050115030c0302011b0602 80
    0xd20058500c09000b10016115610100b011410218a50070050558a40415640b81211b44c0c5110401c915035410004004c030b00ca81d40c101c5402001a801000105568880186100c4041c0c2c401c54600905010000c28201842050000e50720305890004080d611403c01070310704540340740080e0704400b0031014040c09182600051542c10016240d0340120000701003084212181d840703004001600900c46000050000004d19800074001801d030350510300e0304404080d000b543d50748504003507401103c04221050050081d42c1c01045504003918500c0c40b0f003810030080d80301d0381301c0c0300d8180040020700c501203070f0080d0300140c05001440d404000c0181c1d80240a40104846c000070780b00c2d40400b212420440c5418500400103055144d00045c107004076000760307003190300098400c59072406a1004120cc12409102e01072007900d00e40e000301301c01e003170a040003402c4420020b81c04a900514560034800716002c0041201180d5080c6001140304000001114826030300d03101c02052030b800000c00c46a54032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 129533902 1250 129532652 129532681
    0x90405011d060607020a180905011e050108060105010203120702120403110906040915111b0a261204030513080705010e040614060705070e01151202030f01090b03030909 74
    0x9550207038100ca40b80c08040100c14003a45400a5100c09010028040c0b101c504440205405003500c1c0800c5400c0603944640c03d45010744a61151104c080030b0101030700c081402420b00428801c40a40712950420000030f440e841003d041c1c00c8581828408194039500c01c003e070340c50092070600c1e51600c90780c0303a1400f0307032071001501601d42c0308281c8040803074098036140c480d090b5002e83c806000001c03044140c2921000d80440360080854550521000800c2055a00100b1503401202c010707002c0b181c02850402e03040d01d00048030b18166038851b0500c54062003a0000ca5580ca00384007c08200c980e01d80c03808850600c42d0400380d0f000c100040c1c40004080300d00244004c241c0d03901341c88956601000c4010b010440341e20b0300c58034121042c205180da11a0400348010040c59000c1c1e41074510298403018000d200f03110a0b444451802c138000b050011040e030010032904000d8007070310158a0b500b40458522100ca40601804442d641d45000203102583e04004544800d080a0202480c2d464502400180741 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 129535152 1250 129533902 129533939
    0x60507031407091514030405010903080c0a0e09060d080a09090f0911060f07020a1d07051614070906060806100e01050a031e020c03090120030403061109040501 70
    0x1d04200600041c00d07074504600e48a82d00329599400c0c200c0c074140503c0f640b0f110b14501d410911200503940c0149192041c02107100c0e6002e04004100114a0315000b0684000100360341c200042c14840300c445203a1140069013108001c40e80c1d800c07191074074000200c80311a0504000e2481000058210b90150090012000c5800901e4204280602040008240c41020704020700406040081d68040d20300340000d403104c1003102e1100da00304a542e0740400c40b05105a08007640003c20710034140c20b5140d58100c1f40b68442800c1c64411f00b8087d90102c1a4400541c8010040c1455071522120341c44000802286c002051400340600040b542d81c0409400c00400f900c040f03024404103829111170303a01444074001900d50684d595417418140c040102d004140d08002143e0840d00400c01c2050102d047c005005030b80310a40207190380d600140000b401000c4a200c0c1a1042003d140c4204d41040011041e1030403685c0003540856103504c070600c04422841003505050f4400e15060001c500d0f1000d1010044030f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 129536402 1250 129535152 129535157
    0x501050a1d0a1502090a0f03050106060c0b0609091222050306040b130302030c0607030b090906061018150c0510021c0b1201050f2205030d15080307060507 68
    0x75560001208055079070100e403000495201642d1540050040e440000c8815010300c0c3c01030805005400040384c1912962040c00c0d150300301340c01441030000030b2042000402c1a07082290030761030075a07500c40381a9401000640706882d003000040510505116201d00f00303582c03014080e41e5644014501010503004a800d06829100520120700d81c140020f0b56030040390091100340c41d40c0c0d44e03c0181c0070f1031301041e401141140800c2c881d10011403410440b00e401060107072001304490701c3c084288400d20400404080c02644403905000742074451103c10f1060605619241d06602c5c0d4525410b070300400a6481049558100c0340c8a00c0e0456222030b410071005d100c7d80990700f0043c103039800c0800341e010b1803400da1401c800c00b004030000301c1c0c850352011040d0203001e411a42c0b0b800034411107074212203040381d031031488140903000c00038400c41520380300c0c44110b070f40030201041405d02e444441c0e580c0202410010041c1e0750b0541c42d07003800303100e000100081c2501400c0781d941d881c1510b0705c0c0740500341c00d80d0341201 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 129537652 1250 129536402 129536411
    0x2209050126060609040201020703050a080405090c071101050306060405090c03070f020a0c0e040201030e060f090f030a08010504020d0921091a2d04060509150403031205041e0501050a 80
    0x1401c00c1d00118820a00100308020400b035102e210811100d181c010b0812030551142d42400400128103210b01480719000301c001035186c40c94041404481900181070000c1aa02009894002601d10715107528100007840c040743c4a90710480401c03240d00c103079000a68021081c4c01007140d44400c184c011442040568cc503140044000e03142a82da60101ca031005256240c41c44051162104400115501074014035000c205280041582400d2040513100303292300c0c0700c8100c04c204590000304031b90003803400030200861038988a140010020b603018064180700f190002100024449150800307a1803c2c0c00480100c060030400b036004089020079601d810220f0050300c0c0001c1d0b051107440e075403441301c0070442c14075140c0f83c61486a0304550700321412104d0048818081d00980000c0c3c04044e101518407070319582e030340d2118401045400350000f07540c00b0511b24200402c2c80043d50081e03820040940201c00841c29485a2801002c20825992a1051032447e403001c0001d20805400940c003c1da4400c50400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 129538902 1250 129537652 129537689
    0x2707050301140109110c0319030f020301030b040c15090909060b0a0e1902040621060911070209011a16030504030f0309030605060f03030a260916150e010522090501 72
    0x125501400d91b611609801c14400050b1400698000113148811032800244420342901060200d07042a002540c1004010040104003c070b00759120010303019051700e996051090141c018680c0f9031034080c4815298581820004011603504941e001c554014145402240c4038110503903459000c42d0300505000c607400d80034006400e2482100e043e20b4040d074401c10001203002c4501c580c501c1342107103c160503681d50310001c0c1d154154400c042412480070781480c0c3c1c0c0c203d240100848141c0c1030f0480711190105070b15070418410100204c5a180c040102102084142401c00303445500480d032020f00a1a9104000c00805900c20f201500b0349214030002c0000341c403000140403043e80540c00c0c40e40c169000b045804030182c086c65060f003189400507801803e20b00c84100403100d04405444070902c5510022a03a82007160b0888540c1c05842102c1104d412803030207480007442034960796107681c1030080024070000350760032400e400759000c17200780c00801105640741e454000502d824030406181440034803008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 129540152 1250 129538902 129538931
    0x50c09030d030905060a05040f0c0308030105040c0206130210050c030a02030409060b090a05120709180203010c140f030c090d03020a051b0904150b130603020a0e2707050301140109 79
    0xe003140d5400c02c4c0200b4180e41c2d1030340100002d08010f0030a80e810341001000c000003410034140100a0352080c450b481d00c1c1c2d4544000e0006a666042c07a94003036400c08420414034a01c00e103840107070303203070101d41d00362000c28129420f8038240301d64010071403580070014224201039000001082180e402810400c86503035180044600d41c0034505070302c0ea1050030a03000304414502100751201080306401540c3e0070941e42e0b1a200c0484101107040c0f0910301700410500b080d80703020320507401c0c41000c50400c0042d580511100100c50300c503001c1c00900002000c404500c0d252100b1054850f0000090041b6030448074a04000e565800c0622089540c5d110b4074408282c1003018130040c8035a0b0342c0180000c071a0b900c3d61780e81e290303048041d10740d0010102d40c0c600050455540f14110800f5100d000400041c07554150f0044c0300019000b90005142d1041101c05c0c0040e8083c0c405c040c211081d0301c1040c0c03942d1104420310352400c002c21036120aa0560a155503c82d0052890346076904031030710030a08000d8001c214548 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 129541402 1250 129540152 129540161
    0xc01120e030a030e0106080a05010902120106030f06020c010204030b04030e0a2103140708040315060f05060304020d06150602010f0f051b16080d0507030b0d12110a0204050c09030d03 80
    0x801025801c18080c1081e22402034014062841c074490012481c262030301c030641d2804a42e00e01c240c1d01e9a460f412034009505100402540c948070031030080c408603056848001c0c101c545100300400701070340005d40480194003903054901030741d4400780f5007000e420300b801c0042103a1080c0c003040b446460007000004034a00d07415100039826a0b001c08a00071280592420f0b60401360f4a090280d448008002e80000589080700074800b8510070302da02001d09003412180707001c0b1359054000d41c038070f00c402001c00c1c0302d195600b00690b0350265048450001c00c0c030262824a000d048481280c0341441d036020b0010811580640050300078019260081002d50120658941605c4040c1c5044400000d1407240d0781d04100214001c0a80541400d0301240c031081a0342c4824240e402142181c002c16030340c01c188500150300d4028204104812608070101400341c3c0c450001085629a408080c0240b0300c0300320561131400e01c4041d92694004104125600d800d401c89200c690080106a20038028240700c200b01e94001c0c410f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 129542652 1250 129541402 129541421
    0x1031514040b0403020d02060423160f210507050f060c070e160810030b1b041409090604020a050f1c0b0402090105100503070e060c0a03090602100209130203041a090c0112 75
    0x55030810400c48100405240e0000c02c0c6c001c8090044a1012401100e00c0144900808950f03001000061402403401d03110052030442c031784203a001c11184008a8070000b200c006403481110007004470750a00000603183d204482c400070b40703805044000507075101e00c00f40051054403070070026100d2034035501049825580c21101d0020b468503041060010800340107641e980306684036000402e00d5008050b00080d40c110364070203c040c04c891f41542ca503d00346401c081d60000f81001c020301c8641050350020300c00d0121030281d140112201481503a1070342c3c601d40310818940d8118040c191034501d90a00c01e0705200101e606030301500c0188000101400e101240000182455a0b20390554a51980c200c0300c540c1424581507010b5818852202c00c850103000c0125024441d80726180d0042c50480c0180c00c100d001445902a00e10600c10310b10390ba207507040c490034580e6140764016541c2e035403417800b038802da0744416a5240040540301000882e54000850b603088807801d0300c1d4002400c05042c0010b064900300035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 129543902 1250 129542652 129542663
    0x909061a0304080412050601030c090203010501120e0c0d0b010e0f040b04030f140c010e0d080702030a030509030d11070c080118060e07050301021305010801050a050901031514040b0403020d020604 86
    0x800100384800903038091070300035118600c0c20346055030750301203100131400150f4181c0e1242c0250300100200100205000d000340580c0e5811b50941d850301c00040e00548a41e0010009951100d00c44010f50303d0900000c1d014044c01401e005e024580c6052106654100340500c414891891000c81ca03404100017026200303e80c07050a000d41d41d91240c3c1e0807520012131010580c24042c520b4007a07290f403000c401c06040c40301d17561800028550700040c440362801c0700350703010001849400018020015408411500001e400342404141501c420790035a142d032145244106940d4600084460004000001002c03254021107040d11101d4903100054201c40000c1c165503c60b04100741a140015010303000040c1c0d00490409480005507113030041f1b401da07401020418070030281190244415a003001c0c10f64050141560110442814580821031041c410b0001514125a0507a201c0941c0c0c07960300030040248066405034124281460300c2c4003088010784044016000c1c418505640c0d41c40042c145105a0300308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 129545152 1250 129543902 129543929
    0x207150501031205130315020c06100305031e040e010902040501020609010b0108061002030d0f0b04180b0403140f1201060f050306030606010f0314010e0403080108070e1902070b0405070501090906 86
    0x40003c4d1625404024041900040d0000020110b05440000f6a04801030680035035204503000e0b015080400c01009000e803024080c3d42800414000410f035100001900b00344210000c5013514810b0034041c41e03021455100341400041801101600508202c0b0020380855810317448102610b426101a102d501d07000865160020b00d851804002e28240c80d02e441c01980d151804e6a401801135948000201000d2621521180418146446102e05121074228500450034807561400e04900000d0006002c0003004c0c1da686005900d42e8003219070380390072818415a41e0b0070400303074021041000d10a0002040380140070680142c0140101d0344501c2c8000e0107484160b03a210015200b04103903903001010140d0780c0c1c0c4c0340c11500001d8800e29001c1e280510707024826140900e0010200310050f00300e0b50203600b00303032000c1108841d0106a0354005581400c20302d001408000c089000340124a03003e40f0342c41030001800144600410701c407040e6a0280d840404541c1c80da2041810354801d0712030b85052242c031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 129546402 1250 129545152 129545183
    0x1a12071707050f09031b0306010503120d0e0f060708150d050309100315080106090605010e0d0f030c02060d05180c01050414120a140f011b0e0a18020715050103 70
    0x480c0140381840102019504200751314000c245402d1582a0300940f0031204214010355181c00c000e55401400110020030196034a0314429806004085c200110103031169003ea10385030051110010341400d00046913020b00d03008100401a120136540c0070b4402e000500f19060f18103100408120701e5030004025454111040705002c5480015015001090703500c002030350207006040b51140c014140382c4000718070b09040821000c12641c4552141d0305001daa03c51103030072503c0702c0c000d04040c030b6008044c00c044c5d03a44509050f1a20700000c2402940542c000482c6a02c40f0990341c0002d0040f4964038800c1c0d10b810180910070780d51241103848502082c0f0500c01000402c802c02c0d00608030700b01c0500030000001c801041c00b40703419192641180e81060040d46000841000c0142400202e9400700138000c4010103e103d05500f41084056001c100c12421a0b40541d12100c0040005101344000d844c41101c2100f1001b000790088401295462810030381e40480310514004c8174180c1e500009041e01c510003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 129547652 1250 129546402 129546407
    0x318080105040c180b040615030f02091f0c05011404110a0602031801020304030f06051915140d120815040203090c0d030908061f0509040507030204151a12071707 71
    0x108115042c44c650f8a480900b111070702c031805072400904000719440b245507030100c0e0103000d03102c2281049514520610040d11603580c4c0000401021405c0140e111000c00140011104040c082801a110b03600700003070009000c18113618030740b2031070140788011503490124080001110a622a50005a0092013140440041018184d441800c14011a4a0503940c2c0d60303201980543e240c4c003510704590354010090000700da244144203008140750200201c100d01c070144c0307441c401c0c2d5004081c0c1c0e000040034041c1c403079103407903044001a40e00107a0340080f0f0429550000c0c0600412600d60b50890708007420100c240c10103000341c034098001180034081006c0000213028802c1c401c07103020ba040264105001600202c01e00006000d5840310304040088042c21070100302c1910140d211b80e008800b4001040046000030824034287c0f681201d011402c481c0d2a04601030000e49504070011501340032100e1800b02402400134992284482c203002070340d5807a40c00558191840d82034070403200c2c00140c0084d200b1403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 129548902 1250 129547652 129547679
    0x1080d020c09090705030601080106030b07020307150f021c0603171201030b0c040b0417070f03080d090204020f0c07030209060405060d1e0c06030507021002040b09061b06040318080105040c 83
    0x90030704200c0707945545d9800080c0c54000e0030791180300c083e59208000e00500200b100c8055003c100e41c001146002025520400e0a690205e46c0200d155511074054108544a804550a980749001d05011880c005240c9500819203403104403058088040d4940a0346480000c0e9080c80d001a85505096031a5484411210500034101c00309032000f008085404a00c4a002d00058404160820036070b0390740025483c50b21171940c01400c41411554030400c001201c0604a03040d2f10031941001c01c1d4002c607840400c010307000c0c403641a580c15102107442420510001100d02c2101e008035403a4031a0b48805043c4021101c06407100d54011004000d00404240441c1c05403032040c4178070389944a05e64103515500301c036100f16040301000039100d406000e140ca038104444120f0300310080085250a162a095004610400d940c1c130b40070309000700c0c4c980000d19403c10307189a05020202641c400c1c1c500b61600400308804039403240d403071455041021460420510480d4410741e0301001c1d5200305030400104030480f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 129550152 1250 129548902 129548911
    0xe0a0902180301020304120207050a1203030b010e100c03030b04050610080403120f0e1501060e0d1502030a05062806050903010209031f14060d030c02011e051201080d020c09 76
    0x420181c0686285440910045126900405292460050242009040c40000c1c1d00482c840e4844180c24400e15518010003a905603040c18000360b1411701c2c000686400c04610300b8290f001407101c1c0710082c0f0720f80201e06070082d503111756000c1000c0200c000800080344c0c410b88927903401a40c08031007842d045000b201c40b543c000d400f0341010110694045400c0003942e500e403420404254903403110030030201c420002c1c00c1421208020306501503040c410001d040e080100d00c0b030380c481c480c964003510070700840c4109580c100268020665892a054031024080c00094410074080c1c0d00041b0320701c550342d1403018020290310701010f409807540d15102007151039410108516030705540c00c000c400342030365040201c01a915071640300403403555012481c1c84100e680e0382c000c40c01284142c1041120356550703075000c411001d6050a013904502c1c44c034001207071081801501040014955800c1c0c0d840c00341c01001808100c000703c10741c40740341d83e22000d10a407100e200e60404c001580c040341c102d0341030b07103003400081740d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 129551402 1250 129550152 129550177
    0x70b0703090b03011e0506030618060d0b090d09050a0803040b030a0e061315090209040f0515010803090a090605010804141c050c070f05280504020307170105010e0a0902 74
    0x201c90b2105003903180755100380e001c4030304094000004041d160281e20703480000d02c000c0706c0140c118508440403038003c190450385800c1400c055000500340b503941407114143d440d0401c915031580d1825154255031000f142c0a0500824206880003c192810003503010964400402860a0500d000706030b140642000e41a002d4203a15100300d04501c110410005105080c2d007540300c0c1404005041c8105802c0c00e20717034a064120b0415031400c0160f1100940717150826401280c5d00c07440c24450038000d0070046110120708220f0204000001c0c18940000a0440344400300c40c1c05038615a100c07641400c9800c184100c1e404104140000742c00725105003120003204842406403142444d40c00041105520005200b0010034000304103200c4090080000c0005000701500b08401d0030704000010303a41100380c407000d00c4070005000240d85e141020010000080c070000e0001c0d52207080c0395a01070300f1910015039582460a5003000010150b100d6550340e1280c03032014044050b064100028a0003030b62048055810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 129552652 1250 129551402 129551417
    0x60909050702100221010603020f0405060f130806090d020105041e0c09020f0a090f03080304120201060906061e090605160609080409050603120307020d2601080706030f0608070b0703 80
    0x8403000f900081c010b01c1124003907100b0001039000220180076040e0841c80c20140306010076415940d44408650a40f202102c00e141c5a03120001c40201c640320380c014140c505111144009200c14001030182c0c09842e2040c29600c040b0b2081c5822401c90703900301c8000d402480b41e143c0c0c500201200e80010170302d59018004803446141c03201d03030502c140da0246003108800c0d400080e0f007410035507121040301e014004510183c80030714a5030300d410b0301500020308080c1c40e1108020b29480560300075485000241613a10090100b10b07510032010f0441c540c10466088100d40c03107818060b1113840303a6422030a40d00592119410308881200504d0942c0c280941111950780d507950040108458030040d000804c4d070b642c00454585001d00c1414141443e40c148046602c4c401d105102d00c141d008107103004452441d14007205100140b40003c0f482045100a00c3d03101c522800000c101c0c00800300300b6805450142d141400842c286c6400d51007150141e100d6035120b030700f1400082c0300d10303c00c2030000d18000c1e010303150066 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 129553902 1250 129552652 129552673
    0xa0302061302012c040b060f040e130f050106060f02060f040b0604110d051803130b070f021f030b0d030c0b31031713060e120c0f0c0307060909050702 66
    0x402601c215016130141c40c0b001c0c818103030342d40b40a0103001d109000543d08141003050003000ca10580c080c0307002e80744628904000284200501980c6211481d0700400000c0c044c4902c0c1c24903030300078101809003c00007480740c0d00540130b0350300001c0d8041c003c0ca041000e8a0f01039a403920750304229a0045c0c0101d83c041c0d110b4600c0b02c0010780581c060720016800c00c1001801d420000e040e840504000c94100405400034400d218003d091000030f8821a50101c2c2003580c3c0d0540b900e0180b44246500da0000d503c281070400c4a98101d0003d914080e101d00c40f40c80c10003d02d5003c10030410043d0112000500280c00d0501c5000026101c0c80a1a00220012076890320070400c0b61103001e00c0e2144403940c4c0c03210075007101c002040c03550100020006982030540e803891802c00203030b005017400d20000064070060702e42c0c2d035203008690104500c0160407070585449803122401c00b09143c880c4681507603001d907403203000403c1e03506140c003051000441d4120f884454016181c40c440001500000f17004900350300074484140c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 129555152 1250 129553902 129553937
    0xd08070201030b0102030c03070507081516050702040b0904030c061d030403020411070b0702162916120e1224070e0303030112122102090d14031201080a030206130201 73
    0x740300840c400d9000e4144bc0d8108000785150119040545100402d42c034240200b20180114640c071203070051900565540060002c100a081880611a0054070140c01c02c0107056000e00181c080c0385c4a1002407154440240c00b071140d05403400408105078108100400051070141d115503020540f564000b4104902c0341c8400c0303c480c40803610100903030081d26103508000300030060600684040d0310300c0442820041e4448048100700100c0306442800001d401c0d61a07040d0240c04820203510400c4680400c50044006052001d07059000d030041e00e03500c850440110010034491130401d000711160000000e0084400c010513400f40180341072103100c4072000c0c0c840d00c007400214040c102c0742d8004c5c2d070f44040d40d10b40b100104143c1026003081100144240e4201d10f401405229040d482000150315046000d0001d07460014a00d401803104414031164140301d040030018140c11103030b81504c1c0003243c0e41c5038006920303104451700040050700020700064034a4801d44120302c0460043c9003440d900b06c0c440a00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 129556402 1250 129555152 129555157
    0x20310020a1416031101060324020d15050406060306120b100906060203030402130e0d12020d05090f0c0607081219051003021e0108041401021903020705010b0d08070201030b0102030c03 81
    0x43d44015405102803414150054018610510034100800c115841c6440b506104a81e40304000c55261002042c1e240106454060b6a0031088196040100c0720024204c0b1705201034520845000c1c40c2000b200084c1180030b84200c504442c08000f030240000f401d0354429604600081504001c503c1c00c0780c001c01d40b04d140d031003460041d042a800035680c03801e050042200d40c901c00841c0d49101410202c41201844020403c0c10b030001d81c90030215540203000c5180d0000e40a14907802540601d840100301821100042d0290842002d00031703211480344201c280000c5205243d400b409510040010340241d090856000d94440031400c0302c0031a16900c40c80520644209035252a031481407040207005503d021004d50850035280201d03690750300280c44c0068200040104040c00089001c0059441c5080039011200602d00c6600c03003050400401c50090300a42201c542540e4941c030b89440c0180c20700b0303d282c411900039048040300741411b2181d40110054a11220070904500003803010100317220b0200003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 129557652 1250 129556402 129556417
    0x118261815040603060608180a0609032007170106150c110a030809030609061e09010902030f061e06130207020a0506043c060c03110d0801090c0c020310020a14 70
    0x1e011454a14210000380191405401030803e032354046181181d0501c00560140310540c840760200d00c801090605494410300c018454242c61002100c0042c0d500d00410894117070b0311142d151660140d03540310a64200c0c2c8031809201a02c2a8800b00b5035501802018030003404c038030070000b9400c111249030109a80e404581c1c0115010314001c60100010b2405000290340074004030b00a040300d1802421800c2082c50109000141c90445808612003140039000001200d4004d4101c170b40303580c0810700c0d040da52030048883c2c1c01d42c80d40e1a09a00038850040d0aa503024a6000b40b80408101c940c4503280000d51000300100e0b440004a140010503480303c20182004200d1810600418242c440b03102c00c141e00d01c4010002c06010b1031a56807071043c407001040c0305407401071800440f54842450141c500b4220b9442000503440f502201d0203240e075001c0600c0741600c5e0703d8001880000340c0c11105403600c000282d00258550000b05035205500940d5014180f400a6460010180050034244c0400b9901803103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 129558902 1250 129557652 129557657
    0x15010e0105010c141501090c0804020a180e1507021b01140d0e07080102090f010516060c09081009020103180201080c160c0b040f0b040e07030c030e01182618150406 72
    0x300400c50340f45548123042641a4504000c0b510703260940c00a1001c10440c00f5400c07008052a41070406a8525400701c041e04000d0400c4500c0311238200001105003404031400380044c030505035998111819a600e070b205034841a10b42040209102a105101d80c00414460a00603580d944401d0361801c20080c5400030300d00c40000503901c0b0000c2d403e01000d6024001801c0c1400000c03c001102120b040ca61740c1403054001c3d50004101e00c039110300b200d40360165440750340741340714401440720340e0610740e804210081e200b62020000d12203c16100400c500341c0703c1d0007a01051642c4002220210000004d0010004e0030550011204181d038a403500000e00380c0000e9443c07030780424184000300300300c00307200c016003181c42c002ca041c545030440c0440b008074000c10b00020075403240502580ca500981180a203108250f0081c00744d041c001c2c0e003056601d2220241560b05918584102100249200c80b580c000500b07004001d00e007596102130700c0030085601c0325107a0007040450140f4500500a0050009082103a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 129560152 1250 129558902 129558943
    0x1406030a0b1e0907020f0a0f020d0c0303030e070e0c07030804050c030f010203010801050a110414030c0d06050610030e0a020103091712010e061804121403100815010e0105010c14 78
    0x1201400f09608005200106540c08224805025040022603808a944c1b001c10782d4040980d900c04a0714103280c1a50050842d4001180482007603050703004012030807110000c445545070744101c1c5940c5c0c40320a4891a102c10001c011172400700340325a02c115413140c0120110781c0c80710034a0000c00d10700040c0f201c0fa40800d960201c014010081e0038021150011100c0b1030603c502c0d080c0040c1078401d0302c91480350211120200c08250250b440078816000e100e03800401140100184d130900c14081c09040318454803407600881a569864041c0c030540160f0b0350300600800703505016078010340040000a1082e1406141032490201e040b66000c006c01c12580c800e00820421352501601e0300d000d81026003d24401e00502c0613060820078980f0309140e021390000d00b0b01c41403101004080c0c2d42c21000c010032a01d0300320000104041414101c0300c540c105c800d50421101d4030001d01c141414445020b0044103c04200400100a590721943ca5104100d01071944008007000c1031040d14501443c0d400501001f160700b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 129561402 1250 129560152 129560209
    0x308042f0108010816050d03020f070b0a03050906010f17100504030509010206011a07230106090204080d1803060903180608010e010501050315060c1f0902191406030a0b 74
    0x1550382e50040c14800300038010803c400030f0203804071743c046c0500c90142c19024034500c00c1c54405c000001503503648a060354501500c5088142440d070008000002081c28a0080380c2010300005075681280d980755501d454150400d0354100c004050204170845034800c0b0b0003100f1600c0310318031403540200c4c400c0d1102d45e580c4d00004000380c20300805038801859525000c0310440702042d07040480d146554000e540306050039900c0d90305c0c4122150480711a04641c81e00b00049103c0b600366004200340c40724a01240c074004441502110340e20703003d00720705d001c1d81031041c41080020899004924118400c5c2051500c007082c14443ca4040e56907070307021000080f640d0004000448440c20a1409000286061461450071210504507000d060102c0c42c0100b4000603040510b58090001d00403141740e5a603090001d5121100c00c01c081c00540300c0a0b480740c403a81c03058440e0421801000710403904c00340d8144c4048000482040030302e4000a00c41c1c042582c440616196581e80c5101b1000e10030516424901d01207603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 129562652 1250 129561402 129561407
    0x20d030e39090103050606090406110d0501080106050d02181003020d0c05040c0503040201020307111f0216080102070302061501090b030406020c0c0108070905090c07051219020d05070308042f01 85
    0xc0c6403a5642c0240a40401070000c5180840d107180e221800340c81420103500c9518211004015034501d2171007403040441e46150903241c5800481c100c5d88554000d11602e61074104025101c100d41d079000754002412a1a84158140c03600b0895000301c144094201030390381c035000f02d04411280102294a820402070a1005240a20034106e451410b4a4440d00b1072926a0001c0d690340b140c020003510100340b9041c4016981e40d88411031054000c0b0340e070f030741e200a00c9001001c1d644e603030310750f0300401401f80842c07012860900501c2038490f107a40550040c155a22509040950001d10520f40d504000f1515008140703111048011030269108240c0160744000326001c003414042802010760402c0700403c01c0c0162141e1200052043e100b04480c03000c0281c5a5842911451091050041c002c0c001d84c41e00d000480c00340b1016050400b0503004010081e80030a8080340c85101525070840410800c0c040480030031700c01c0c030046602030f1051188801201c101c4113103800300340070154818a000c520a40c0c0361410f59 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 129563902 1250 129562652 129562753
    0xe0106050a17071403060a090e0c09090c010c03050c010e160e0a110306011d0a0e0106080106080f01170a0f0809011d0604140a09053301020d030e 64
    0xb0500480d00c16582410742c0010a0050380c0c03081080700e0380000c408900503590721380141c8000d0548503010481c601103100541c2d04d600800490707503c5440d000c0000340220070301058034080024141d44a0201c400995400d035141d0704100713040707141c82d941d6404546020030104135080030318041d82801c088503072900e480070030181c000a0a004201c3d04025050b010403525100350303500200c0c24200344007010100035402d07076a0034209003201d81c854898240041c018040040c014181c0b4002d82d1400041e03038980a040c0d0340c10304240d520300d60303072000000108002002115818210707480e1405581d40308502e0348074800c0743c5000841c01e9500800016031140c1a41e04004003089103030182070003107180301107c00010b200c0e0150707100f8000c0d0007540c1c030107200130fa03900e0007600006400200c1b01041030f810168069200d46a8102003085445e0034210203038120020346034a2481888141d004050884a0301001c030050980420b002e00280f0451304100500c0741d042c2101e444070b4521403040e844e54a51156010303640c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 129565152 1250 129563902 129563927
    0x312080406180f02040c030212040803060a0806040b0109150801020d0e0d030b06030610050c03030a06051e10110708030a050702040b09221b0e06030d020609250e0106050a 75
    0x3106070b20880000c0d400043c44400542c040b00c00160410b9141d505034084d00c80c0d2400d41c5020f50002c42004100306544015500448056600c041c0c1c290702e4900c2c840e6122410389000d0858003a441c0104150007458204003400e05410b240f0540c03040d030b00c260180c02da07004144040e20807900e4074000c02070b40008210104440c48103207801c1c072401e800403000c1007041c84003620b02c034004c41c85581c1c0d0032400c6000e44121550b5488081c202e1382e880c506158900c3c010f1200b4050a40f00380d103240d0309040c114000031813002c0307807460003072100700d1400c1108001d0300c82140d41c641000242c01402d000113942c003024001381c41d0100c0983c892540d0780280d44104012030302c101002c036119480e50818401c1d05c2a418039964010808500400c10704561402c0080900340c4242c1f19400aa0b03811401050124220b09000c2c001c8a047d01120f51400040f4004e0b621200201e800b4006680a240c182010745801210300c000c80c0d0324400c16498080d02c3d903000c0251f0079400d0b0800000300d18009003c06486900840d140c062 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 129566402 1250 129565152 129565181
    0x317090d1a150a09020c030723060a150e04030e100903050c04020a0807110705040501060e0103180201020d0c0606050405040308100b0301080303010b0d0209210c030109050d05130312080406 83
    0x815040006451a4014041d41c41360650100d04444103403010400c840e10150004030040c40b034413105402450f03003130000211b1301c03407406408042082e80e46140644036064802d4000c40380031900b4505000c00c080347c010801e070b040120100c5003e03041e481b0043c0c401d603240860307134070b02502d6825401c0c25031400007040d6030540140c1c0304102400c1c4103235100704d61a030408e11b5454009446041c45e41120301d0200035410075070b8814a0440005a0303581c2202810421403001c1c2c90901256950744506850910441406805131b0041d01c4000201c0b8865450725121511510b80010125101c1010800b110300407182103003c078040400f4080000280e82c2404c000744003603601e5624541c100b1038030a4030b0340410b100713852271214042910568002243c0640d003841d40b01904150041900020b280c480304c45220046d1601e004249808400c3d08040c0120249541c20400904034800c580104803215030110900c006120001480030000440d0903007188604a416581d841a600301800c0c01d101300d61081101604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 129567652 1250 129566402 129566431
    0x50f070608060a05040c050c0d031a040903090501210e0322060e060a170709031704060c0f020a120b090106050a03050c1002030c160e060d0c0317090d1a 67
    0x70b00b0340d00e0411640a5440c05c2d00d000c00c0644410006983d2801141ca0005035405001c0301160715070b50541c44600c1842e4004c0640350840008001c0c842229003c00c0b02078001501d405040c0042d5000d42685445039005110401c0c0940d5645080d04c121038003079901c103446800000e03c955082851501c1640550503010f040c110301854550081c10403a84100a54056030f40804c4910303205001e6002c0c841280b00c603070241c4406281440008006611701d001c1120210f000e4410010300ca2555800e440a4580585514081c0d400c42d444601c1d0f0161403060491307000c807032400f0205200010303255050718075103d848015241c0c00c0400c052800e41e100c0d9008140192140344041020070390004006c4551003007500c41714600d000341441241103100b00741a45442e403003014880c00a13207e100107107204840101c5030394422030700c51500b08440514020401b6089881e2400300307001282810510101381c1e00c811144600c0c18428101040515607001c900f03542100100c507a840842c6481c00d80d5546c808454072000da0f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 129568902 1250 129567652 129567661
    0x5090108071206020f04031202060130020f0402210109050c030106121407180e0c03041202030706050c040305060604060b030a090606030b0c0406090f0609060e0f0d050f070608 77
    0x281da07851103201d1600c0107040800308909012840c0d048a0105030a5040e43c1c0d51580c41741410701404840c8c1084000500c500e00000900300c22006c5034a43c00c200b0046000314448510096014107034031024160b030701045816850341555100c1c80240007024070115229540d5400c0c5c0549243c00310140e2020400d9030405080041c011482c0084078192440c40c10840121408154203100401c007032130f1100301c220b10b03150500841d10341101c084181c8410802c00c125845840c1c19440110580030384255214580600104e00081d020f4140425080345500c11a401d15030562541800d488040d5800b040300c10000a0a005201041c400268030401c00c3d034040c040315192940040c16840000d0000c3d01c0300d595804440c080014135000b030001107410040342c4420b03003440409e494440c0e04c42d10030a40400c5c2000e83c0000d0041e000c0d00c2e0081121403d4a90b40a00303483c01000340c4d5001803903018180d200484004210140d50303030b6841d4203d428081e000821010384002c620714906102900f0003070a01c2004010007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 129570152 1250 129568902 129568919
    0x15020c030303010905041e030905030c1903030e060d0203070806010e040e060604050a0902030f2803050307031d030d0c0809010204140d051903030b030c18041b051002030c07050901 79
    0x200c1c111096041e00240303d075128100b140741e04203404907403007c2400301110041810360160515007510300c12070588211995000400c20010079000f031000403851541b4042021a000d10100380c420301025014134504075a20f5039200403a4001c64106012402210500503a540c2c01810600d800030305480c2046003002d0303d5042540c1d903c2c01801c062045440d40c00241440e640c60b0000207034181d014040b5103032820742486258480002e0389080360100789100c04c0b64800103103d00211b800390380680b90b551840c0c44a00088010303100d4502c142028050107004803449907410402002082c640c8040000c1c07007108000d0052254502904084860380144414004006010002d00c80c03010111380590a50140385481e80c2040003020b000703440041c5c2c4042c40780525816800640c00c080c4114165001620048100010007000d81010755a076a11040001d00007404807201280c541c22170640c014020b6a140005204a0641000c000043c1c001042c1490b490004222040290804643d648042e44c140a4803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 129571402 1250 129570152 129570157
    0x31b080c0318070b040602010f05060d0803011505071a0907090606120b040e030a0804061104060e0913050f0d030501080a1a1302040f0605010e010f080a0903051306080115020c0303 79
    0x440070199080000180c00b22000c00c0410002c000100303441d07444540d5040068020700c01010140394550810000800b0b5240c40c0b8080d030071031a4010130941c00e590806081c3c2c18250300401c004020b00000300807100101d0a4039108a01c1c080403c03800030010f103400d1000d00d0806041e40e12004000307061031010b0180540014082d80002000e0030b00080d403001c0c000019003d003004080c81c3c886030000041c04400240d0100050b44282d001c0e0109002c02444075070550014800c0e8030030b400005031001d4620995103481007160f500213000001c0080030070603d0701c1d0715003406c984102d110256131208038000600b03601809464010902c0f440075200d0764906072a2181b0440d00c1c45044202e40328603800152840c40c480d540603c0c010f030080d00400c03c075580105081c00404140c01101c0c041880e5009542c00d81d03105081044c000c502075698900e0540b92a103804001c0c0c03882084c01c03418424284100c031004007180860800030003166642560551600d000301c4ca4199500c3d05103c00c43d04403440c600c1b960f4030300008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 129572652 1250 129571402 129571411
    0x4090c030e0601210218100302100504060f080c0c061611010902030a0308071106010b04060909050403120e030f03090d09080f06040b0703020903010f09170705100b01031506031b080c03 81
    0x2003a080030074251000440c0c01d14801101b040da20045014003188950b0758104109030303071007500c04c2051000c12a5081d10726014500c41d441c0014070319501020110b2080e40311980014400c0b4109080900c1140d0075800c0100444802011420050010301e10a07031142000c006036100400821018000703402281c0c60350300c403103c05014800d1301804501124451a48055000303456001e45680d9611019500000e42c0644a60740010343c0c0c000300400c03c2c151900c1744030f0049501d07489144c0700f4a84403103644050300c481300403072003280418000c1e108030880c0880110310804601024100f402a010809008040303e0381061100380d00c1100c00c92411240011714a4010b42c000700d0100d2140c1c1c034023908501a01c074450302e15805500701441c91520f400c0d02e8210031941441500c80c0900d0b02e0f00c46241e8416400ba0040c05401039010352445030385100186d001c01a10407042c0340108055504030758080311514940c0c000000603076102e050a50341601200c0d80580400c2c5894840400d06140c00c08034030720b000151 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 129573902 1250 129572652 129572699
    0x12030909230114090a020f030a0f060506040e060406090204060203070305161406040b0714090603092805060601051207030c0c060f20070804032604090c030e0601 71
    0x1010908295503224114003100d41c40c040075102c2da1514a6208520705203030b0301c0c0c0d0003000000702180f0056568001d4407140300c0c51030400d605503524401001d0140c046032010b82c84040c1e0b80d140c0802d05848400082000e49001021511141403075410b0004944030b55102005a91040c4000d0000380d6000c0100c401c0d03580c0503d000364494091100102c0c0c9005001e4005004200d02c880701480c07401c000c41c03001c1c401c50262518110513540d00d0400d135441a4060100c29040c6803c1115502518040002d15006400481141d144507480c61005044000b00080605044041c000701d00c03c010041141950040082c80d01c03d00301840c00d285d02d2103101c80607101e08140360300c1303d1100d0750041c810100c07500c0e5a80c0098050011040d06241c44d0001c1040c101000c1011840c10b80c070105490815044651165014103c50310f0646152a4014480c440c5883c140c4280040303008001c5882a44000c0d0000e8808080300003170300424400081c00312010401d8600e100d4118100400c000040a1200c1e04961440c0c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 129575152 1250 129573902 129573911
    0x1506140903031c140414010b01020d02060c0a0e0303030907031502071a1801050c040906060e0310050c041a0901030c08090d030c02030f121008070f0614071401050402090112030909 79
    0x61070843c05012946850b1141c90007410800040c403892480f488401e20000d0020440d40e8529001240c40307100b1060804003503440707000401c02d0020140b0042004402c1d0b803030b0929007540a00c0020342143c2c003e9a40c049564041c3d0b8050042c84050701c480c0100032054241145800f4031170340c65141c80d48010f100030b82c080b05698000381c012284160f8400000600344005c120500d46014a4103440d0080c2c091721845a1a1800101d281402003082ca03940c2080140103024411880110001074280107007905044602800002000050700310580b0a0b103654071041d0b41c959484400050490340202c140c041004084810b11201c0f06000c00c901d0442480361502003111006280140e2071741c0320749814503130200b030009030b00c8041258440c01035000d86a0030100400040d51a020580d03612038500a0f0f80c0100c0c1c4505080040c40d001e0b50300800a86000111141002203e0b280e048412450000e0510140d464030b041204501e001100306014058243c0308103490000d40e00c0040c060510781c00384c070036000e80e00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 129576402 1250 129575152 129575197
    0x604020d0309181b020106050f0409020a0312080915060112090501110708031801110a08060f120606040b03030f0a12060b0406020a0302011107110f0d0501150614090303 74
    0x141c8080000f0b070941910040c500000802c94030300424280381104c0105846864a00788548103001311021240010020a0440e00920070031004020300001203910282c0c0e0742c0c0000000742854009280082c140d241d209240c50b25025040c02e000045544d200d1040300182000000d03a040400c11112031820800096005490b10f4014010044008840c0a125000c500b000400c161400210312440105401c40602070b96150b95500361448050403038a440024001d41000f40c0c400c0112a51000f4024003a11100305041c0200f8440d03000121070500c6604208104401400c05000e02d405d0504190300662900700000c960503e180580680305d000c01820300114602c0c5806904030070081d010135002d41d9601c40e580e2202070740e00c04240c0740032009035003010320384034096800500f139031107250700421041c0c1042c0b1441d04000361b19042c03050643c0e200706c0d0310300b06c0e1010400910800d05280651082011014140003028040945000b4840c0d40e02d882040746420359140841039450840c41c0e14040c08141c2d4a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 129577652 1250 129576402 129576407
    0x73203040813091a0a0b04030308011211090c0301030203060709030206030106030213031a040c09060e28050108060612070b0a0c0503041a07060605100f140903160603110c0604020d03 80
    0x4856004074215400c0c80307113100c080c0e100c0e41150307004001c00700c0b07041c108266150b0040300707140034901c005030200384413200401c030842c034081da0044114458001e0710810038840000400c0300c442560380c2491140040014000c50600300020750700000381f42401c0c1384403031865002810502c0140504000c06401140d500388003100c0020700030186510001310b1007440381d0943e007035500800440e8162101d00d0740e0741000400c0183e500c901d006980140c05800e0050f540c0b00a808441103180342880101080e40803d00390a850a2140e41e01810b4080f025142500300b800030010004840ba0b504003c41d04801c004220001c04481203c01300b41050501c10305103074a03800c00760305500a541c001e0208464200d80d94540c1d0b41c030f003c010071030340d0300c130b03030810013616444034240310110f41142145004921044e400a80050249501c0703200d094883d1441e5141001d9180442c4c10300300040150058041c00079001d10060b03415028024041014000180c141b00511095030380d200c00103040a8021000103071060241071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 129578902 1250 129577652 129577687
    0x1206082a031e0a0303050c07080d110d02070c0303080105100207120201181707090b13050c0c0a14060609060d0f03090e0f100f051302090310050732030408 68
    0x1e01d03101d010802c58504000703e48030441c00740c0440010f850000000d070170740d403070000b6108056000340200742400409070300070000f070110b440440794440d801c0c00100e642c0c02060000741780007841000d500710494075500d00581001010380100380714140b02829a00000c1e03000508404444c290000d06035031116a00050701c06904a0f0000d246000004c100400c004a00c2c1c2c0302c1e0701c4029101c000b150492680e444511007120110005150b1246410f01c0036160b03220701d038020542040484001c40c0c6850030030075890b4039201c1108021510502d00004d8600c0042d002d02000754030010540e102d001c0b0b860300c00300007158030600c44c80c001d000c0d600c1d0341591014503104282c21740141403540d41f441c1035030034078808058800f00b003140c1c03003181c0c44604070010603030030720810491b030071601d0181c88404c024400401c0440079401c01d42c601d940605c21988169410605802414000e841503150562101380c0c5408441d2010700422001014050308040c55507004001821250300607003104600780c584130f1132892011200d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 129580152 1250 129578902 129578923
    0x612040c05030607050a112103070306050a180f140f0a0f0207060501140301060311040f020c1b011206030206030a0e010905070b03010f06080105090c0a09030507061206082a03 77
    0x510a0300f007000041500003004010607210307910740103c402d00e4010056a24046a086d83c80780107502619405a08000c0e4007442d00080c240c127022560940307030800301d03100c41d03400c1e48000907103920405a4042400300c0c1c03280c01c6203154a08414884007003000d803410b180c80e4001d844081c075084280006980c0c0a00c40d40402e503d50440003041d592241e603414113001902d000e00960f0702400303805d042d000181ca0305208540480740d200050507080825001004001c040b41002502e009408100b9803504101c148800c7d040e400c0703821010200b580210000401141d00042d031400400d00c0c0c010240056614002500d03881040d0140205200d584440c00d01d024001d100790041862140300b00204812111a01440c160341440442040d0140e5602c422101082c00384503280d0000240d070301050410b03084800512500344142407861203a5980d64410345004260350110b000544040b54050700c4100714003d44d030091100100a00b1813003100007440f0b80c100c483e00c9820003403420298520800b51070078420450302 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 129581402 1250 129580152 129580159
    0x803071e0f06020d0b090a0b100e060706060905101e1406070209150f0d0c1a1b0a050c0607080a21020f071407030b04080307090f08011b08060612040c05 67
    0x240c0f400d8130b4201019024540086214000502c001610010380d0710808010101c010041c4480611022065514044d10b00c03001f500078000700401c20120343e06016040007084030301e0002610386170800499251a03111740080c454141c1c04004410a100c101c280c0005542c8050f50311007078112603900003400c600c40c40d88029000b4400f00c08012541c2012240c9001424003603900c20302c1200740104000c50540c102c04000d107100450030050081c9003205ca540045000c42c50401071400c010f5140c903440e00980c1e44c0300990681c1c001c841c00401c10000380407100311883c003a100141403031a19902d605590050003000000c0002c0b104000c0001c40000703003048505e040c5a80215903c00b01000000c042e81c2c052030056403c00040e8a561b45a40000101c04003200d400c628581004c3e01e0300da48500e143d13800034101d002001040007020891003201e0403950000e00080c40006001400000f0481c40c074032003d490801841030386002c01c00581c50300700c201e407020302940c00001110b030790324035080791440c1803500103640 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 129582652 1250 129581402 129581407
    0x7030c09150f0e060405030a110310090c0f06090f06080603010b060327030c0706140405031603030201050a0b0105040611030f030a02030f09010506300609010609060803071e0f0602 79
    0x195107400072150540c603a036036503640c683c480c145030034058248224454a50154040005000030512030b40380c2d075080c500c0003015600c100301e0344103c05040d230b0304061301680c0030031414104105000c09041030340001c00d210f003400c03043e551602854410303840c424441e1030207200d40c02002440315075003035102500d00b0000401064a03802c2000030703a079170200410700b180c0c0d010a140b48080c00c0308600000340c030242c0071080000d126540c00d14004580c151001012000401c1b0240000300c0d4a036800d008071504030303d41032170b820304540c0345050090a59101800c1205441c0c5421080c40151340d002d8201d40c1074407114200035110203074404d103c614600c600c5104490640c008824020341140c1c1d50001d50044a2400c023540c0940c0700c51034268200c2d0760136126164403000007100041002c442c041c105000505a03400c030b6030f81d90a002c050506006044a20307100c42d0f5034070780341803251000300d1080030080c1503030100550400c00642d03140701c0c2009409000603070440c88540d07a07208008c040b00d404d0410746e522040564 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 129583902 1250 129582652 129582689
    0xd08070809060f06010c1203050a0b010c08030601050a1e0206162c0d0812090c06040803091302091804050106141c0c0b040303020a060605060a1704051e0601030c0e04050607030c09 79
    0x8002700b03015103040c0e001c035040c03001d540b5566124005102c00d4681100744c0c6403441d140c000040d19240e02c00703c041010b04c86070041d0403440c911800020026003100760040c244515201c44030036820350f07101c43d0440501c1005d852a51082d020b55140c081807810140200005084500000d02c41c900320200050110b10000341c4680c814144a4900f4040c41c084000c8a80344001c210420056002d10301031601107600034416503103189070900340f1200040094100518001e4041d01103420220310414241e40604024184420001c00740303e00c000500440310050302d085040c100089155401640301381c00724490720890414402c00c040014002c0411440031a07449940b03103030181d2140044042590054540b0100007618182441240d1400b500da580c0d81031503407140040100100b00103001514288903440d566180000d507240103c0321181d9200080c0015031662805103c01c100582000030174449580600000130700004085801080c1402c004c6000010400b0480300410281d220825a1840764241e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 129585152 1250 129583902 129583907
    0x9010c020f04061202180118020715050708040c0e010b041202120a0c080105010b0f0a1b0b1005040b0f0105091309080403080d0e010b060a0e06070804080d08070809060f06010c12 78
    0x12403a0350310a45101b60114900f21320303203c1c401400d2058043c8884000307030b1001e06a80d04d900030704800340319802a01c051151400300c04100c0300111a16800f144060b028071091058401e840c1000f048402c40041c0103605003010020940140d10030b03442010181c4068508541d2540d50340c02c1f02c03071041030403100b840020742400341d284401e0380303d1403030316518000020070001485000c8503440d202e02c440140c50104103a0048408050480405242900c1c2c00d20500024454000c200c0c0a0740c504007541200074200300c00c202c22104008901882029103209954850341c2190940c0c010031700c101d0f1144189451442c0c20b1010f060344201c0204400e0740007401104020540d0040d02c0c103102d10201c00c10900e41c520992600701c85c02c1c52071940d446103062010040c468410800c4512100e4042d0000b4100000c9650382d80040e081500821080c0d0042c078800041c0c0c035448418503510032001e1801c80304908142400c15141c0b20301915003003c0e4100d01c0d00103441d0389d0160b01e0042d28aa40201d100707240c4418443c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 129586402 1250 129585152 129585179
    0x170a030b030102181005031014220203072a060e07080109061508060621011e020705010b01021f050a02040503030a0e01021b01080c0d060b04030b0403030606110309010c020f0406 78
    0xb0b01c02c0707081052102c5c1040c42182641d101d0358410f50070710031071418010340180c000008440c540c1e12103101b4007490044550b20100d040124070103103015840e41400780f00681341c2c111050104540803622201044a80d00020b180f5402a810680008030009201050b504014003500040100d6082c1000d040030020f4a030702c10f090360000d00200000c41529481c8032034507204140c13002940032071294440c01003249101254090b07544d001c4000200142034201134058004000e4a40701400d6010070b0b064103015007070181019040ac2403014051075544403110504820b4000400ba036121b53b80c5000480092595046901500c070080440782c440090400061030071704160240e43c014000c1c104841034081e98201140d01c5084140c40d1804640d6680144c1380c23082d0003110070003001c41c0d11403000044500e42e10008001440c00b5101003289403401d400c003e420780f14603502c1a010000f01c144501103084000c000d55005003030074a4074008104140c00007659101600c0d51807607000785021000911882580301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 129587652 1250 129586402 129586447
    0x70207030b15220608070f0302100305060a090e1504060e010e071401050711150a0314060105040b130b0c030a0201060e040308010e070203070b0705040e060409170a030b030102 77
    0x78100322940d10074000c8103640044142c03031500401d0310314444500510ba2220458561104900002c8080e07a420b0701a02e040f080350301c007040c0c006045409009600701b0400541e180030290400b8030007400c00c00040303541c000981c49800411551503414000d0710708c0030b100c40442d5259500442c2c0312424142044001030800d071420060541c03a040d030f680d10310240415050102c40030000c00c41c649202640c015507095100e920704642c11840a00307408159654001c01050007890340340f010f0740300c04c02180090101c40c900d01c21140116003210401120b45e9018080b107080c2c803a418152500c0301090400190f03c4141604102003100300440c0340b650111001014050301300150740240902c1e541d824a40381000c1013982c0c0900000ca8a60040c0000c0d00700741d00c003d402074404d1044a1410080ea15420032a05040d181c10000900005013003124103080340d1080e401c24000c4800300003880d11661602c4200b295480b0110f82002c01181207400c0c070b1700aa00c003000a00c0060000d554a82880c428250413044168 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 129588902 1250 129587652 129587663
    0x803070801080c01080403020309040e101a210604022e050a03060b120f1b07050106051039020a08010603052406041a060703030903121109090a09050607020703 70
    0x2643e81c20310343c07040d00c91500070354164010703502c1c00d051081407001400d00c51034505428811040460701008051185840042240d050003080764004410000b600c0280b410b208404240034089a238000e2002c41e602c2d41044c0e040301d40c032074035461414012041c407000710541c0b0010184440801c0050b41c1000080c101001d40c2d5908000850700e941070f441803070084940d201d811100400019182081018074280c003d500381c245a601542c0144c04c1c4080c030b6000c40000c40341e5035102c0034108290704140c18400500800c0b4144141e0b400707070850300400006002158820700042c046c1881c6040b8801040d90151a9006851011183d4444044502815147c07108407030310320841d04000c10345018240304003d041c5920784c1c0245191211803c003c003510414481a1070307070b036000d6550340d441c1c4d4805000702041403094801080c079202138103010700640a01e44c0c1c0700c82c1b0700b810304080414080403034084680c0c2c1c41e01111207940c603446c2c2c540d6041c01400e01c22802480c61040105103d001034001940318101c134401d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 129590152 1250 129588902 129588913
    0xa12050f01050a081218010e03030313170304020102060402010f1e11070503010b0303180103020f071109010801051504051009090c0e01090b1f030e06011701050903130b070609080307080108 83
    0x18404e07542d0b02c041030580c4111440050142c007021000070342c0c1001c0041c0051404002e59809a000203066600a40e10540e074004008449c40c10040310411030ae01c20406100e0503401c2d482c1940000c0d40700c180050000b41042421000514101c1c01344e40c00e4018890300c4400d1840c81702c1d41038009070851849032400c1c1980e01c03528000142d0707450305004d01a00c03c070000e0040c60a145c0c0101d0b80d6a20b080e402201281815000d201207560900e5880203809494081d031040c10780c1401c00740074000462070680000036a81d0415080120410142c00320700841c80041d03600041940d20103d044101001c150840d00c0d1707580c203016402040c4942240ca000941d1031144001020382d988100b900126440c02845a4100101580070121003859011000040000d0708001c554855040662403c0107426006038603c94941161091181e42c244070341c40e80701108600031850300c950030ba1100c01641140c403800034640780028244080240c02e0700f1800645178815282510380c100000090481842401206028890b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 129591402 1250 129590152 129590159
    0x5090a061d030f0d0f0c03060e07090b090f010903140124080709020a1e050d0f09020d02060306030f15070806010302070308150105090612010f051f050a12050f01050a 73
    0x1000d9002440301c034060040d03142c0002104072082c103410242d01280c1081d61082c519002c40120700030016800d58950300042c003603040000340c2c1065231015051600700405100c00380b04480600d402c49101180c12501c981c21003000300c00403281003c0c075400c01011079180200500d1041d0381500515a6042c0d130041181403000b26000308002001d00307120740c0802c1d0744000c0c0f04100314946a070013041e02c035180d0b185c0074141c2c0b80f8850240d400e02c030a1805800000304002007480034500c491040c9500b013224181d003441540d805800094040402800c003a120340000004540980d404122000540fa088000c0e203100b5410101039891400003100c0180224000c0070000380380798800d100302e40900f645602d40c02403e490710805c58001d401c001944a040c080c08209101450f0b843c04040e0440d1035900041c0600741d03041c00001850749916901c100d006403060021f00386150407a20b91807c0c050064038126484004c1311070120f07840c502c0e01d40300b43c504e18a014140018008080c90442c161502541c9180a2556 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 129592652 1250 129591402 129591431
    0x3060903030f0f13020306040309090b0d020a05040509160b07020a060c021f051314270f06060d0603030e0f03030c0a080c07030618061a1503100905090a06 68
    0x2040710703500c06600300c000020740b0f030700b405180a9401102228001007010a564046441e011041c0d03400c0c3c003c00c03019507042050140502448241d024282c82c182c0111030140c0c0440c100c40054001c40d8803c549600001c2c2a8500c104070f040d80c0041407030321212079550750341701740c100c140c2c4100010b034040d5296850100b8284d01030300b041031a203940034058010308801c10551503008040b15003120108041000b0307501356852000c203223001410900707000c00383c0501d10104011a0141c40034204100c2c0d08140300c510000030f003001c4c1c074541c002d4140c2003440003a503074400080d2035442140e50b4610384c0c6281042c040141a0701484c0d044548030f043d1171a40441000f40d003015502e001d214200301d4140c1c0300105100008001d0005443c0a5074140110f5444a03145d50b601c6081d101021700170300d803001d400344c100024040603000f001130545e80d1040581705440c201001c118140303940041d01c13420060000104010001d10281d08008064500341003119041418505446550b40c8030141c0e4041d0800300e08042c4502c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 129593902 1250 129592652 129592657
    0x6130315110d0f0608030a02070609050d0210080a0f020d060302090a0e0705010e04021b0d0f05070507090c0e030a0503090103242705100e0109020a08180708031803060903 75
    0x50380700301c0c241022070a1039100c01800b542c8030b0840e94251601c01c00101c3c4041000508000c2269401520340f0908124000f8400070190b0310403485510008075000168848810100258000c0d1030464041d42d40d111101c03002d001030416901d4507030b100088003220710350a1350041007640e00c212400f4019441d610003440565620400010080c0c00c00c4404008560244140302c0d0190000b07003000d0b0500c040c10031041c980d1040c20b810a0740540010030203011095202403211180125400c1103428038030315858890341c13100c4c540201da55141d55a406140914006c401881880000a0880f4203200c01c6251454590300501a56800329041c40e000c2c407091049000f0105040300d03d02c0e01031401a2070300d004159840d001090000400c1d00f9107000f548164110301405200380d14113040114000c0c0351091109505030164003e12103d031060003a80303d04c50740800d01310381080511418a5610307591134080c030b003044a80d034071058003440b0000d0300c01320301031a2010042d6250b00444c15500300d907907540c60b40c646070f1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 129595152 1250 129593902 129593921
    0x902180102030a02070b031302061206031216031b05010c03140a0612020910030c0b09030c09060906100909020a02010b1002010203040215030a0f0603031205070f0c081806130315 78
    0x181c100c0d50b406c3c00900d2102001d10b81c4080250090752200d2240e80109403683d10100154660011880c00c0080b603007006c0007084440740c404001686824088504da5080244115000b0b040089441c0c03a60500c442c441c96600c11560000020800c001c407041018005080c00e01410703840344c11010019a000f10588145403c60303420a4450888142c83d508001041100502c0158107070440d01011021a605c11440c401902ca8000100c0e9500080c1040501e4118030303040341481000400c04100761900e409030316603003151041d10f000586204850007030318066881d07041000680d20104500181c95815042110444c2040c0d031040541d543d00e8034224241e10044134069001045039100050703140b1504011907008010220009100c0c1c0700804020036248180d00c2500050791010100b407590107188603c58110601d411304400d901071580000c0c0011300441400342140303502040700c0485441c0108440b80d10300c0020011641d0700800b00003e1521040e42c0000d40758001c91004810b4243c071030741703d5084030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 129596402 1250 129595152 129595157
    0x507140f0d030e030c030714062a031305010f23070e24030406091407150e01030902040507080103051b0d12270510020102030103080306010f0908070902180102030a 72
    0xc203490381d90141c2c064540c07515000360a00c41017008800651091002d0032030701e48580d0038101d4400c03c3c3e40403a454000c1c06041801c0c030200340c511250b0380202c101c059400344801032140c603442e40d540540c1320012803800310005d0031035400c00c802601448103550240e2010040b0035284d100000d0b02e051071000000c822a00720000c10400003c64050b031030100305160b0140100c4080f84096290115560382d00d800588045401c04c0c5c403250040308112810100ca074490700010020401145007015000d42d00c11100b82500502080d540c1300c10b80360341f003900030100b02500900188031b40d0911440040080800340b00a4580340645210300ca9054130324554690401002440803800802035111040c9004034000804280081c1680542c4036500c040e012060f85003c088a424086180105002e4403103081d640810071a441000103000156a0f101034913004002071814100510240c0703020f550310b86480e009070350140b00e05880040c3e0120150010100701c0d0302801303e000f500d0040380041e43e8034040c04524401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 129597652 1250 129596402 129596413
    0xa06050c0a23120307030e0307030206010b0f0405030105011202090610170703060306050a0c09050d020604090e0f120a0e0109050f090c16030504080609060f0103060b01140a0507140f 80
    0x10408202000c0c44091469090102c9a49000166850049200c15203449090f001c41008800303a007502c10901540081030103940f070320800b07650003521201d0500940000c0440401d001140780c20050656002d400b000c1d000304820750f1070b4100c0711100c00b03003034400300d118aa01c0000a0702034181141c8039400c0803103a4581c4070708445041c20030b94440300000e01c0941019510f05000011824500a880c000d840c0140002030210181b140204210201d0700a04e001d016541401e00042c0c5031441128200d4001c030500043d061240c0c1183e500300101c010a822141c0303d03000c900c00810748054000d10b480e01090b15000813080100c4015107007130006205141d0701c0010b0042050f490304100d60b21603407207000801010324140003e0014001c0c8018030b00250002200400c0c14032035900c00f00174007a00f2101c20001001c080c68580742a11080302c1c1404014955902c2e501d4441c001e901440720203806840154542d074688400d860700070001d402c403090035109030340210b001c001c0030100895180207805042000e0b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 129598902 1250 129597652 129597673
    0x129061303030516300801080309010302090423100503010b18060a090e070608010914010303050d020903010f09120f1e09080307060501060801090b0d020d03020c1503060a06050c 78
    0x2c0301500002e80c040310244485981030001001260058007142d600c40c0040594400d6042c1d20b030b1201c400142d00300038801b6510050040139000425241c07000307403d00e40542e65401c15400b040180038411403107400140c100c036030924a2800000d84610501d620107000384000e6607207040509841c3e0b000c0ca415003010418203d8040703681d400c2c40c0c4903484440608207071403255603818010200c8030004003c05075074010031710521500ba800301c0607074018554500180312504428005540d414010721004040c03110000300452801a2070701590000c40009008004074008500f11101910b000402200e120440e654215a6640229044030411141e80d84018082d400406048181c2030480003180a0002404001901d007204000501e00507124030004159545005c5001d0b2000106810003500c0c1400c1c03092401d065141c03a0105015950105d038041014015420260b00b085070034031010b500558034140700309109034068010b5000c1c1d0f0b07040d80c582c01c1702961030804482e1741c0140032444416401105154 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 129600152 1250 129598902 129598907
    0x20c0f04020f1b0d0314090d05160803010e0402010311070525052709061303050d02041203020d020c01020d0e0405090c0d0506040501140408030a05090f012906130303 73
    0x241100248070400620b401121810030044550218200f00141d0020702e1018039a9814000c0b0b1142101401c0c0007003041c10103889090b212010b51038401304103d000b007105611040e004a000400c01e400070741842e96540c561606201030501164203a02081c10410302c100c00820f04000c90706c21035001340c0940841d61661000c0d04424482c0c88020f6030300000e25001048035a1060a0b4035a49c84603241003040700100404030000e00306000300264070640100742000258a402c0c0507000102c0c3c0d00d890043d42d90329111100070000d001d6a000114044000e00052013019000681e0345424400c45c0c003202c070740901e60401269241640b091200008030800016411418141c01c501e40105540007a50f0083c0001d0b8007049241c008a8019260b5510078410b001c180042841070704844908603401910915154440c501244409050042d0007640c07a000503418201c1032001880707001e0001d000b07004400d6600710340001e5081c000704800f032800381e61080c9150342c50104100e90220940007000f199052030764606 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 129601402 1250 129600152 129600157
    0x30816050406050a0e0a080708060a050907031a0402041b050702040e0d0906230f120105091b0309070e0c1c0209011b06090b010b03160c0804090905070509040819020c0f0402 76
    0x846d0084d0742d0000100700b034201031080324050562240202a940b4200d03250f042a690080c0a00d542a003210005101040b222590302982440380940040c80307490303600c00315008124608200550009440071403001c2d56010f001000c0d414000c88042c0090740c15184c2454880a940d1b180c00d0100e00c420600304406801003e480c5e03a20302d85100c1042031806104001541540151107078031081f10001607128000018401581c09071400b9292910385103820480d500c0c401002c100c0b1641ca690740400041e4544c101003020002520350040920010b0a290b69103103141d401c07410601002102c13041c18510385000c1882a110310f04d00503511503461008244c154140c074500e52405444240d2900c022002043c11a0300c1c0600034611480e850380d0f0380c41d200d44654094841401030001f0403c1020300074004c80c603108156403c0c2c400070100054210715030700e403003031404025600194210304d4501c100014028004061300c00c141a001090300e0700c1004441c22600d0f200c81620665111101400700c1c411420194007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 129602652 1250 129601402 129601427
    0x60e010c02060706020f0a0207120309170c0a030501020327070501051c050c0702040c02011503080901111509060f101a04170105060a0b070804030611120103030816050406050a 77
    0x24041c0f030b100d550344070030081e43e03c0410040340780217000910710310743ca904001c520014810303100c0c2d00f02005566580207151040303603c00e01000908030903031400044400d000707100309000000c02c000308040d60b92070030314040d410807256007507628251080c1c28003041101880c50814014030b800350500e9410400195456004200005010040c5d816a9003400d2044d101d0540034811420308613441d000079104110507034040d8a0b0039000c59050080714584620300c11208025640d00c50310583c2c68103a0074004a490307a11908890866101d40c20303032000109401c99150703004d06900c1068034415580e10105841e203802c15078038a2103101103200300b088400e0310a02010b010a4111420f546055542c40101c041d1400560f10b000d09a5541c1050181620f8034100304001803240d0104075040c01a03d0301d540d91a4081e40c80b01600280e2124141400c6a208504a44204468400b0f1030110b50310780c18010150034040300d0034a500e000641940d091280103405450403a52507a0799207161807000b01013110000e80100c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 129603902 1250 129602652 129602659
    0x325090603020f0d053f040b1605010b0a0f05041a0607140703080703020f0c1c02060c03070c0b0307080609060607020d020f03010e03130b12060d030c020301050a0f15060e010c02 78
    0x28001070b005122090082099001c40101600b1642a03a02c01c0106d2070106011001464200810049000e0782000d8580d040304142c02500100326a0070301901410850440c2c9a0010324443c0101d070421100c4007003001d4402c1502c08101d8120308003100c001c1c5010400c1e0165000000b03000300c40001d001440c4607001c0707441c0802910f412a5599440c9034090b0080002140503810003038252395061810410300a80c60300840c0d2480c01c2078612140c0b002889030984003c0c0c052140003800302d0310842c2c02c0088170044c541c4205023910039603803500691219003003030315004009401e0340080b64062a00500490041b04028513a034903001d140d40c00c00000414281c0d0403038000c080b188103100665000e1180c940b200089402550303403010807995400c0c1c1d280042d007010000183c14400d428141c4400100d25a105c036043d119004640780b241030642d0385d8444100d00a40c9582407004112140700680c200c1a0810b188650a000f414140c210100384070003d805003100040b094202480b4a41c03140c1d100c3d60103a030000d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 129605152 1250 129603902 129603913
    0x3071206021c0203160e010f050c0c2106100b03060d1509060b010e06030412030507021009050a0c140d06050c090d060c080c0c0303010b090f0325090603020f0d05 71
    0xb00c4240c0040c8000350084800c66012003000440c14080314100944502e41c41c00206090300710001038003103a50342105404011010480180b9141c04104e10000d5501c0100840120300c8040c8400f016a540c071030310256603004200110301911811801607041d02c03c1442e41c2c5007503550b20002d11184008a50342a1034a0551581c10042030810340705410044d801a140424a00111400034228140362200e02c1c0c0034000030020040401c4030649810402c0780285404189a210a08200d14140d000700d0b000c14100d24000d5200104500000d04101991045080380541c6503201e002c0e01c00c0388441801c84ae0030443c404407805c0003c1d000c0d40400ea1100d603c0001c2410f11600201180800742c050b41c088071b217203682c1c0b050f004045130070258544d405404105400e241004568426840380011f115407203001002142c07084055039540850a001800078044403104200b02001d0310f02480309012603580002c0045001c92207002c0c0c0d000303100949801409090f440c50961041c4102056038560580d124080c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 129606402 1250 129605152 129605167
    0x1d04020901031b0e120703030c0f0c0b160605070504150804021909050a0e03070525091103420d0507030c180903090e040606080303130501060902090307120602 70
    0x100c883c05403a5000e40e84c0301018642d0840c14411010329a01001a41d0341c81407130304000003940400c02e4034109921520310714004900c2d20b01102c0420b015006100c0002000c074038081403030b04240c65240b115000702d80a100b0703070300c6032001640e1611890103078414091900e680010821300a5403a80d4015201404101c00d0a41d4606082c3e00845503802500c080d0307881d501400400c0e42a402011466040100610300c1c000e15566456035032502581c04c03503c0000382543d203101161a124840d030003000f007200141300c60500c02c404120668030403034010303441c120100201034104440d40e4055049881d446140711071540d00521900710007810186442e0b02c1000480a600040d1041c8401d000443c4102c042140b1603051100c050381c42c10f080540381050610b0f061800012130f40c4800918120b80541d5882c5085440d1820090081c06050708a090b0300d200c0002480190090300c0400c02d021030180c1d000f04105a07c40d4400c0099201d2100c4481e45940059014030029401c0082040303524854a0300600d07101c1c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 129607652 1250 129606402 129606431
    0x10b030403260c07050f060c07120509090a0c02010510080709110c0102070303061505030910020f07020307060806030706033b01051e0105040b01021506032b0f1d0402090103 76
    0x1250b03c1050039034042026010085e0030040009184246809054036181142090071103012305140603115050b1364807404001f501403021901c4400010780300901c00d10340b801029000d4841420058015840c0500294a10200c0c103807a0703040d00d1620b03020b400c83c10b2070885040c01501042c00b10b40f98680b4100400d84821000744018001d8602c40d480101d0383c24138001201149001081032941402420010080844000720f03020085030b440c518016180e002c000100d4046000b00f12000b90580704010012070b003a41c005840a11943e000c400300c0d00c0c903035180c040841c265061002c0c0c2c2c803e1000a848440b5480c13517412004940c2002101408180140590246095071419261980c0b81c50350b00621403003440d41c9010b07040c00b4100940f401d1103000700000000795519942c0c0210b0381440c1120b804141076581c14400071a90155840c0402c110520031640d0868003141c039080c40c00401c0c030380c114000b200750040300d0450007100706101001401c96510144400303980050f510604041d41c410b0312142e40070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 129608902 1250 129607652 129607727
    0x609040b0a1205070509011203081003291302010206040f03170403030b0907030b03032a030706050105030f0123040c09180606060e030c011206030204090b0f060108010b030403 77
    0x60b03010800b07503088035282491820100d0a40100c0d0040d00228018000314500c3d50381c901440b945441d01e00455611601c01c0303401d605060304020003600b401419001d800200540c44811411900f11401203626504408400110040300081c0980c00c004000381c00304120b802001c3d4498000d0503c041c4150340780f6116040c0030401c40342140443d584011820f10b504008443c160b00c94458101080054804e0000a03907034043c070b00604090814164030400e40c030b6003a04009100110031000c80392190b5080c603111000d0482400b03112b000744070b1001d101c01c4000050050070503080204088502942120310118054507000300250390150802c40006240902d601c9680410018014042c400640034605a0300b50344030703540f00008001024054265507a40802e01410602013420f15030540d100d0740100d44044c2c0940d90001c1c0d0b200d071501c81c80c0c0c410711100140c2c1b0740c0300e600310f05428a0300b41e88800065030418020300440709001424000240028010140352404c0010040c50042c0499552343c81c91424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 129610152 1250 129608902 129608909
    0xd080f1207050d05060108041502032e0305060c09090c071110030c020d02060405030414220203061206010b0703030b0609040519060b040806070f050705070909150504020f0609040b0a 80
    0x502c0010304030350400024843d5640008003443c1940e01401c181d2101d220060b080c15040c085d607503001010174100010f412039a143e656428074140340d03690802c0c13025582040b2a101c19035103070242000059100c0d010500311900c011000b07004007040d03141c030501c61520f0f0f009000222030060031060b90807826a502004d510340c0c1502e07941c002c02c07041200c420003800c0003c421200b900355400b600500001a4001c4240c03400d17200041d0744c0f9500010058001001480f04400081e804403001d16060950510b58004501c6040166000120f01b60780546603a5620424421880c12510a00125002a111390007121040c4001448282406c000b0390000c0c003140e20135101c0340e1018101403401140c02e03000b03000b00c1004041030712646050600c1d2186150701d070f040040c050000c01082c0c0d08880c060902910030786180716008800c881041c2e455804800052020070002c0e290201031a00f004003407000c900640c4c0c41240d010741042c1c0743c0c900c00414011345411118404c0d500275100d100b2005a82c80340c030a5400113 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 129611402 1250 129610152 129610157
    0x60f120103120e01081605090402030a0c0f0c08090114040302060d051501030e0a0807020d0503030a020a021509031b1c0806131104030803070207090603110a0806060d080f1207 77
    0x2154034500d802c21402146006000c00d002c00030b201e4151507030300000320359407040ca603041e101c4240c00e001008540714824803d403154481d102000b445410441c9620500d410190f503101d003107000c400582d09440101c804e0300d0080c0343c0d10007008190a10b52085400581c0034060b118203900b030a03100d40c0024030a03000704584035175565030345040000d20440c2081e098158002030a0400c800c540c0c0120541e120100d07450043e01c10303400080c06500f10340710700004880031500b2006aa489040940c0804065070003c10b00c0401440360316603031079807410106001d501030309444c0300540c0b0300140030401c0c42c644611021402c500c0e0080254208043d1444112070104c0507a40c0d0312460300d841e1290401c0058680c940070b120710503245c40102c030910040c1d40201e9045d0707500401c2241e10383d41c0d440f13001c07480c007419900049401418840004101b04411000c950407580840e100344255440d43e0003103507180c400300c2e40f8940c41040a04400041240c800040c2103c07503582d400c0310301d814034043d22b502c036205040d5040f100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 129612652 1250 129611402 129611437
    0xa0f09141f0605061602030a020301060815100b0d050a061502151e010302011815210c020c04020a09120c030c0909081902010e070303050c15011d06060f 67
    0x4480311101582800281450041044a043c030010641d10f0040e002d803003400b6660100d8810956800b00102c10b64154004c009000264031001899155180d03c080e05401c01000c0c00844d04868032901c0e0142035560b850041820041c0e5450805d028102c05846c4071212542c444000c00d00c132000d60070801640340b20703030000c10b0f4035044405201d210100043c621000700503c14491400010a844000c1c1100e4091070b186803441c1c010103450071082082c0c1d2240c1d03c4088020304122040c2e13080385c4900d000484100040c0083c00208005c04159180c2d00c070f2010042e0440e111100c41803134a0350151010700700524001c20390b01d40b1084132407040c0803031400c1600c0c0c50301c00c2101002003100ca41c52150240c5109641402101c0441d5200711050103288810608801b4030014942641d10035441222143c442804a40c1640da990030054080e42c09031080d2503140c01044400380c501034070712400c141254070482d48002001282c0e00340101c0400c01521407580071008008940040810038090071b8005020003030a134 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 129613902 1250 129612652 129612673
    0x80904050c0c0f01090c0302011412070c0212031905030a0f0e0c1f0c020f040b1c06051803090405150918012d0f02160809030d090506030a0f0914 64
    0x14038003c019840d866050f1705100709600041d09107a035010840e6420308086480030706e1401f00e01c3e00d0340200000c0c1002da424240400040ca540081000c00a6000f07445102c01c0c0520ba210868a034490004000311191640f241090700b6440348000f143e002c0c02c64600004c20001055040c029075204681d840701c0c075840100d806003649031480324a4400b055510078000c200b004180003a10303954817002d010748640308201a60400ba1142c1c5c0000c243c505006002c65001e43d8140b418880280300d0000603110249440001001c0c0d150107086104201c404000460500110500300006408024601184281940180321b556160440740901450366441640e48054020078000c1c00c441110004503072611100e0180c90000300c1d0701c80500c502c0b0054420100304c09407a0040180a8030411020003290b4460003c084207100004018291541c82102980d40d10044d150341145c0f244124040c05600000030004100c283e0744541c084030310000f010b000400c0c02411074440c0c6c5912002c4802c03130b0499800088454 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 129615152 1250 129613902 129613927
    0x1b1204030f0b010b03010305100908090d08031008010501060c1b050909070305060c04180b0d200a05040905250302030d031e060f06030c05091c0c062a080904050c 71
    0xb405464203000085c02c640c51a1900c2c0e0351100c0e00d40180d5613055440c600c076410720039514229907501b10080d1150000404518001c0d819600031140c05042032102c64004c00c1c40a01030180d54103d4445640380807202c03045480b299484030000d403003e0381c02d5120401c006802c2d220b036074040e880707a001c2d00040c00400d869818a1418050018030072003454800704400d03c8001140d41180303004130303101500010340074000e0003c0364108000d804054200350380140c0194442180b50711840900301c090f62101302c15582c900912054904401c0002c102e60051401100713041240b0180070f9940c00c0322400030701140d0f503940119090140c801e502400090b04d03040790a80b5035030394200c1c440065904600030820945082e42224042a40d40210401c064a4135071500000e84140c040d43c0030001c0041142103c2c500c0040d10700c0704001c50b4002100d03812034080e000600c16001d94004440407d4a2181985a0043c001001d00c00c604150080380e03060b00a100080e03c54a40b803007000d00c196802007400780e4522010004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 129616402 1250 129615152 129615173
    0xa0308190c030c031116080303150103050609011703040f0e04060c0e010f05031f090c030e030307050f030601030f180507150507080901090333111b1204030f 69
    0x2154203110407031050398006944864100107064140c500f41d5591391a4100341400c0c01d00480c0300c0c12407489103a00100c1c1d503000100c001e601440c181c607107401d402550a0015020303a00c0032078031280d102c000c16004109090450400d080600e40c110b043e20718044d00c2c2c2c01d0700c0d80703c19840c0d04200c225404c45810441040303000e214260f400f503181d0a11481d1002c42c040000d04008425006100308000403000c900302c40604181d82c811065501c1c040c2c8003103515140e110740244241101e0302c001900b030035982d020f01c0b40f011040302d00590b410f07500c85c1e18000794400464407a0340f000d80011304142d074032840000c0c04103d80c4242c40340b000d4102c0091040880c1c50030401e1904189821040041e0080c99801c01c2082d08502110001e6134010b4205803152401c0700180c0e915001d80c2e101800305940e10840b0b01903070340800c1400d2005800308203510a403081040c01007080324031141c00b20400c66002c004e40050750707003c41151001280700c0703421a401c0c1058082c1c4022680c210b548102c0e01c01110108200400541220 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 129617652 1250 129616402 129616447
    0x7060605130b09190e0d080f0f06060f0a02190605090106062f0c090c0309010614010c110409020604080c150a0e01110309040524040b24090a0308 64
    0x10203108040071400020300108004d045803c80354440c0039136402245450b048003c00c0a56942660380440c807215010b85000c078100d5001405150501c0007036000c007036010500e409100d0107003066090100000000380b0316841643c0003c00d522440c000b410040c00f190028201c071520a542c086250f04207207a0381c5082d122207421910900c001c411020020100d03460540080c81d143d0040880020b901c040c101c0d042c120051006500054083c0400030f1442c0180d0042d8000c90000c0c00070003d9680c1d5418078449041e210701321a002809401e06170010816280201c040604000c2001903841c030740743c4c00540b465001d64001c01c6107070065501c507802444d0404000c40411f10034180645418012036006203455200c80129051000090b410303c00c011040090380d1901c8005041041541001e41142c50203007440304005228080440d0151921308140c01500803182000c2c0c0940c400c80603135603010090200303260490340310040600050314030303940300481440190300905109c0c1d0764a05070030b4440940d440da0708 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 129618902 1250 129617652 129617689
    0xa0911040506030303070c060e030c0309010f09030302120a030e2a03070f150207081006090e030c06071d18060906010908060a02090609090a0c080a0c0206151507060605 74
    0x8102c41520040201c0758050f4040c5080c078908007071860820b00a00d10104020aa0b11001c9000161104000000d04051a003600c41c40203140b80c510341107501000a0200400681141110600e070b2520f440250002031003506020500d5080001d040c0c3c0b40641030509009800e4542008a6155001c0807030b03084110f0065014140b0142058100c8801e096144a48000240034020840000c1e1007031000d40003034000b60f0244c51400004228640c050415800740c882640d00e05600e90445200003c1117506041d40d0310060b102d50b5031882401c1e19091500305000840c0d491403011001981d80c0d14074010744078000e20700b81c1d405508020051000c291002080c1e0703030510802c050280052900000c0030b9520000f445409a6143d80d900d010a10070700490b490aa000780038132040c444842c2054220303c41d04640b69580303d0059030364100802c1078540c6100c506015070090b10129a180e0401c040c000440c010140004260b1344400c819003c0d0750303002103826184140d5a1105111724600305c81060180301006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 129620152 1250 129618902 129618911
    0x204050a18060b041202030601050f03060609100b04030609120201090305040315090f06050411150702040506030304050d0b0f07090f1e030602030a0f1104081c05120a091104 76
    0x10494244003402000c0745030318108041e071480703021900540c016240039450951200ea0780c04d01e50000d2100c003481207109005880011859040c15020b1030754500c001030080c2072640b076010a11149090140000c08200d20030070000c146681c0e440001e000940c4142e80005200c852820030f035544413803c03d484e2086904000d8074502180e4000305880680c1d03003203e048000040c0d5000d4450003410751460003030403c65500e034020140541c59021520950140d2803444285c0300000801100705110009004c902e00240031301000f40c10b044d070005500c20f1001d01202c0c90140c0342c1c0d0008610030000c0e0400c5a00d1007410703080104400034132800c10381202c9507080070500d260401d400c204130505a4082d020f1600c030240d660740d850700c002e040580c0007150400d004540d241001501d040140c6920401503021038189030700c1e1104503181004840444441801900b8106112204046802011405e490410805200340410410a00507003030094042840c005000e040d6441d00182114004800c6c81c03140780790 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 129621402 1250 129620152 129620159
    0x80108070503070b0c010212010909030f02120d0b0307080a0b0717010312080a1803020106060207140306010603020702030307051b0f04020703120509030f0f040611030a0e04020a170423010204 84
    0x5a0102620500004c00d0f488401206001d8028064009184200c02000c80009007504480d800414454003940d42c80d40000700b0b8503401e0360341c1c5100482040c2c40314002c12030030a05961f12361181501070b80013030680e001296114401803410210481c2550700384681c50a001c03101d60014041c050025070341d80c0c4007426601d5a11103103800182c00b1002c0051100307a80000b8041c08140e844500c5602c04000168840011810300900900da6030244102502c184880482d0380e0070740500c2203e422000900902ca26070034100120069044402c08030703010f10083c0016000034406001000150450f400766500f500e210100304400110703403010175405540304004410104e0b511550540c1d08103808400440c1903201c440b03649145110343d8038544840c0c400450200456208000200125402131b0b4406100c840281001c680b40c0c40360402c52008981071801e0304090381440d8001e00017059035030408510207031211034440c083c01c00440e400c68104c0d1040070355400d2801c5c4203120f007820010003002142001d08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 129622652 1250 129621402 129621409
    0x106080106050d090606030f05060115020f120703030b0d050c040c03020a0e010806060d020d0218041103240a0e1f05010e010c2111071e05190510020a030801080705 72
    0x1c3e5141080c009486112100500c0500d4108000444d4081200e012810340d9041507500d990b000c1c00f03580000003182c0030960189100183c22290013611038044c0c007004805c0000c00f5503070b5000342c00440c1450b03154506090385a84494082c14194000c40142440402c11020442210401d540740000d26105001c040d0342c0e254882d0050704806003c2c24510b82c00d0301d440b800507085010301c590f9511100c0c0009543c40e00010300781c001c0c000c5c4400095228241ca4881400c00c001e8850314421000600c0b000c1c000228a0b41403020340007a01209440004041450130000c18403480007508003904044101c404e11182d029001c0b18504401907844007065450705000000380040700309200c403810401003c8105080c095004840c054501c85c500c00c28100b00c9601c10082c10b403881d1541c040d0401e0240d0380d80022079003100c030110f101c844071104e183c032512402c0a0800085544800e01104061441c1d80f000c9080c0e00d88204d1035407010790980040c111681c152500070712201058000922a0b00030315010802502c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 129623902 1250 129622652 129622657
    0x10052101111209011a0d152f070302060c0f040306060b04030b13050304090c030f02160317010303020d0302030916090225020303070602071401090c06090902090a06180902070602030f010608010605 86
    0x172011102c0320403c1c051418260b0a4100881000304094070300100c4640f000300a04050b03410b01294540701d03250310311a403408101e60003941c0014001d40c000710300148d18500d110700201306207408004200e040588984038142207501c01e801005100d14001028814090070003c1c1550001c2905151952240f407903031090f03103034011485030180c036985421040d55a28000d4020142c4010702a800315202d544112200501540f1100c00790301184a030604014000c0404a1550603207406400421083c4c020210880007507000514070b031898050a8144060f41c807074005800c004003c401000b5886400c216050b50840118040841052802c48140c500603180482540d140b543c00c07060050b00e5202c0c60505480421403104003400c02d501e41018081007005002c100f00940d8210b9030755840517501c0d105010100d01c80c001c500c6501510500c0b04104d0144141c00c6024003014011042c1081950385083c4030598101810031620941c0200c20801501020703d2464010042c81c41e240fa00c0d07502d0142c0c0038002e403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 129625152 1250 129623902 129623951
    0x2706030b0d110f01090e150907020312011208160c1401030b0a230604060f0201140144071509120f08120f07020c091005210111120901 59
    0x30f44100003a0034041c0e0081c20100001c20500300c203020540392031414000741da10f02d8581584106a1040401e105510000a503903251104440c182c0d181d9083c0002c5811703129604508603600e05040152803140f001889080981c244194081c40c00079041880b1140f000c44800d40050416240c03003130452490703661030301c2a400c441c40c09940d042d5440ba080c0c440003904070040e040c643c00c440c00050020700d444d48114100b5901100368000c000c8009207000c0991910401c1c440d2072070111014450302929039030021194038840b580065071881140d403822405031025800c501c0f200d6500710b01000c03c6921918050130b001d50b100392800415060400550131506c4000ba40b01400a03201019214208080c0071308848074004080b40034102c80c41c0c60285140100c50448118005005d10343d11500355040104020b0b0160018101010241e4100400c1c000c0c1c0040c000c491003841c0c0310440308100040420701c00c5520b0413103a08850750391503455031205520448080d00b9040740d80e00d41b0300b00c1e1018100700039402d100d6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 129626402 1250 129625152 129625159
    0xc101103120603070504020c06090106120c1809021e01020f0a0503030f100302030102030c09011107030201120b06040905010e041403090906100c05010c091d190c2706030b0d11 77
    0x340c2d10b855002ca46400780300d400c02d0342c010340700086640000a0005071075110302090f034000e01c030040d281d0700c00b0748203240710980049c15001d0061050040c500900003034a8180030101c00003640d00340304c0e000511001031000864103441e0304031413400ba140d60306000c040c001c180200003c0c2034001ea141d41d960741d030f40f1008001c00700c5103c00b02d0100b030f40c0643c01c2051100550b0020020364680c200003031209980d07408402140e0108180034010303d89820f001c954202180e8050311503a000c0320359446520080d00c4405030b00303076002c1810070020440310440e01c900ca0203405803507201e00031480c00386080070010300c9060032803120354401c0c000ba82c0aa40c500c440e855000e0000d444540400341040c2d020f4696942070003008029500f020440349803951300244200841d50460208004040800c480c56003040702902c92443c1082a52980041d107405c0390061082c03c1410324051104003c0024075039445171440715808001d03003039000c3c01c20805d64075014080f1044002c070f0389500c0241040e1b40d01106d4004020a0500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 129627652 1250 129626402 129626437
    0x8091804110f0a182c0a17090301060906030209060d0506040219090c030e010b010c020102060c03100e04030e01170702030a030507030e0a03020705090106050901081b0f0a020c101103 80
    0x3103840d8158001c00402e0000e00b1107159600b4000e0718030181800440700024110701501000d051000c1c5d04051840e0100c0c080503003902d405584401144d41010396403002056000c020420080d1000d00c11301001b03007410a40040c50a05501c10480d2114024003482c0c0324502e501c50000110307901191070341d00716504845031849003005010690010700c080c0e1082404d280b9040f500001950190040b00d40803502a0080001c070840c1c80065845280009001c0d00582c0440009062001004d009640180c0c41136064140030303548102281e1a050106c4040b40001c405c0240c101555801500e281000d10016200c0491440c05510080d624000c04006c02e04041e29103012580b80c40c060340c0702c2d0080050718030546065050600f0003941d9102c10748181c5008403480000080c070700348a641504d500780e030305070b542d903a107a2500c0c0310003c40c00c061a09401c0404004112056507002d824005201072001a0042c00c003000c140c2082003079485460444c00c09000b0754020400d2401c0000c4204c428404226403100c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 129628902 1250 129627652 129627679
    0x1504060c0e0918010902091612061d0a02070203030f1c0204060c112b0c0e090307021905060d0b09060312090103021b030a0512012304090203030d0501030809180411 72
    0xc0c0517025403c8043e403c029140244050320800003440040300041e0b132641051108070391100021150716100c1c01c44100c038000084040581c0c01c1c0e182541155002002506015160b00003d04550008104a61a50002646241300c124001d000d4118000010341141007901d054805805400740000041c8076411074044110a0f6441ca440e243c5091503240481c5000f8245070192152009594401e4803103207140a40010349840303034a1a82e00c100d441c4070156003001100d5080c4600f4a444401d050780030319202102003215121320010344107034811071a000c00c407002c0c4007090002c0210301503c4640a50003801e103406c645002c6600f00c40280c0e0080c0b0303005a42c1c2e040c000070517581c40b1580162142500001484500c11944030b0f018144406807040200e8031a40d0710501000c1c800104d100c400707071003c1c0c0300001a000d4030b4141d1000034024000f80c141c07460305606100c0382007107903000d8104a4001401003a841c1c1c075800c1c40c6203c201103a000d100104000d040503162074101882300080706e8481c1c502601c518 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 129630152 1250 129628902 129628951
    0x1d060108040602070c091e02070c14010c050102030708070e060711061309021b01180309120c08062e060507110f03030d141302010816030e1504060c0e09 67
    0x100c0d05580c201171044407413620303104e940000e0010300741d0a80c0c10f01ea0407007082c1b84801c0e4a100301c0d81c002e40e22007038000125207464100c0181540c000e500506000f00c81103004045503080c00150311944480d5216412440e06280207050061041401e0707000b80000d00003000040d54405000c0b0400d0301c22501d850f21514255100a1007084607080400c0345800818840030044078130841c1200707541840002e00443d140c24250041c0e2801050300540060100c0c6010043c00007114401c010050052004601071034448202a161038025500241e480e20740110741a1480c80300040c4e401400300b040d41d840101c5182c45002002d40c028424060001d0320302e203811038400d03070340c88000e54407401c005015203841d6a0f8030004240140f401d00100075003941208002060301d00862601040d165058580481c2c5071500d81d0300285103600c185281c070500d544c2e1095541c0309002041180c00041408440c6040c0d032a09185c48410f03201d602d4401d1b02880b1a0300c0480c0321940d2500d00d503d90220f10bc1c21090301e21a180d072600e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 129631402 1250 129630152 129630157
    0x20c0103050c1c09170901050f07050102040f0b070c0605040602070b090307080d080108100c0c080903010605090901020d060504060f060f02150c07200307140f0310050108071d060108040602 83
    0x15229a400c40f101c4603140501e40d40095000501405880349146081d05c07003190144102e050440c0012410401c00c3c44040816001c0c3ca801c0d80144001801c2c03d4640c03a52481d42001600802c0c0360410110303d070410030200d080f158014001c01e00d802802e05281000c044c0da11003090181030150080891140f00503101007002c80e00802c01e6a089a0320106000e00150140b8030a00492240d8096841003105050301e40c06119105142940d61003070f07100003501c0b90966034000c3c440066155480320000115a03440c440302a000b0411074000580e941c0d42c807078400003211110350101d802281040403c12024a2020b20841141c1e081d0074441e024800c4103808900b010040604021150a40d02c24010003805150190403d18803494501e0740ca10305a0192580440c40500e81c9a07050741b00580500c00c60103120320b08082c0035070103846520b4035040b00b8006801c1400c039038200c80417240c0c0c0b1801000010780c100007880040c508180e10f45c030710720307011100304012000c0100100c0c10301200300042010000705604 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 129632652 1250 129631402 129631417
    0x10e090129060c10060314010c0801060e060d050901150906080606060f1201060504030204051f0b0d0b060c01050a05011703070b13021e030105072d14030114031507020c0103050c 78
    0x29208240c0c01c4c59507400040081c0d01050f035010507601600e0401e207505108030510001c441d22000320740d0f8a0311004841c090825140f83c0e8000c48180b20148145400b80602c0380103039441000032402c04840c0e07000104440c090360242000d01d080c6041000100000304051b6008a0203548040da45c008446408005102c2c2148556812040c10000940103034010007500644e442200c5c2481641c5801c0c1030f0f8154601591144080080c040c5020446500c48200910300e103001041e01203034071707120100081c4040d00051042801d80e5111010000c1c0c007022442014050448030f007032901c250902501040d80c1e03002d402000fc008101c09400304420b0f03140b0303000d00103d007a40100300c1071000880b6858641c1a0198901d030034003d60a18010134280781c01840306041441d406c098124000030307031401414607240021541400e102103003070344540b461300725030045000e4201518003000309840c50040c0744ca0000710180e080300d410000750034020881d0380402c06044441d02483d0205198841030120100e40c8203414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 129633902 1250 129632652 129632677
    0x5070b070512040b01092313020f0a180501060309120e0f120114070201020f07060504020a1205030301230f2107080d030605060a0c03080403030e070b03010e09012906 73
    0x80004002076010042e0681e0440941440521f2003a2070304104400c0e0324542d5801900c07018002410612100e60000c0401e00042012420300c0d2104040740200c42035400241c0b95103140d0102c11941000790203818010403a914041280c0043d940321b403a016104200c401b410040e070b1030364558990b600c104c941107421038020002032040d41e250350340c28001c0c01510020305520280c02c000402090044c4292420320425480e100d2600c1c031540c1c2c80d00c0043c400100308a911540c110b50210300294481c4506007400e20031002507940b94100b140c0d041000c1495050118080c1c84041500090340300c2c0303000031407207034420b0301d900041341e0340456420003510604011400354802c54000150022000804205101c00d41d1400c0014030b0302c940070700055102d0541e08c140131500724001d44e00080d00c0b86000941c001e00034980003400790380d164001d505240c82d6600c00c0045000c0440140320a0202402c41c82e004500c1c90020046070703c6d9000e501c1c2c114060020640c121101e007003c0c0c1000d540310f00040317a110b0480d81 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 129635152 1250 129633902 129633937
    0x10f08090c100305151f111507110709020f07080705010b0409060606090b03010806041704080d020601051005120411060f0705010507090501020703030e06090a030803070305060f0a050105070b0705 86
    0x45800030f00900088514001c903030160303201804142403030070381080110007242c0301c0340c100c196a40054030803141241400e0300620074500f10340c0000d54440300c001d026540954402000040310401c052070508140c1000006500c104100e491482c0d070081180c076210342c0300c0f034a141c40340301030b08060740102248603681d42c1107400c10f0071a2082140e80d0740140f0554030305440300308001c0c0d155072400649002c24000d031941030340b20750007003000700f94840304c24a850403182c62900d16242e1a14070150504080003d201c01681c8035500501c01490f1003094510b856585281082c00d1801e0300b8520400490043c00c00340544c0c00a009070f0741c507919120100c3e82c201c100c0744000c80c5d42e40003a25001d4000d0a003102c81d040004d064050100d4158408521442140c0c2c0541c0d0341c102c40d50140042148035400a18101d43c4494010f900000003505140990f12440d4a51000100d910705075091105282044108610510358441e09115580c0c10005031010319070008150100c95545400c1030701d02e40710780500990000c15a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 129636402 1250 129635152 129635179
    0xa3c0602090301090b1006030209130905120409020703080c0f07060908040b120604060503060609070f120e03120601090b12040206040509010e16030902012a06060603060305010b0906010f08090c 85
    0x5c90118034083d032011115800010386d550b800300c00324000e040a540e4403406041da482241011504901035550040c015030340c240b0300c580340904442d03000340c0c04210841d4010a4807010f040d00641034130350266486004c0c40c5880c84003208542035205000c0c0003000183e690010000f80324154040d54042c042501c0c1301d42d0f44041e900c05003850102c0c1190304d140300724180b05012565040109030746005030405844450035440c0e1b01420f07512818903c842e0000c021b04203406411140745402000212400c0070040c0d039131880c3c141c106030342500c0020880c03030622039480401c110680018044410324040c0382900d0149817241d2001541a00c40c2e0303800598003c5085002184500045110303d018182118000c140851070000a9091744c600c81030290105441c5a45007034242268400d1384c9044030343c00d40311025000144c2d1031100310760054002c800069510f820520810100344248090044100d40410041c40e000d00002c00c00302c00314214404010800000c41d000381d80420041121460040c50907965400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 129637652 1250 129636402 129636413
    0x6180a0321060e01120203101503080f0f030408030405060709030203061f03050f1507031b050c010e010507081506032413020406050304020f0d0c0b0c0316050a3c060209030109 77
    0x301001e099200340940c00c0420010a149d1040c40c42c0a9448016007102c0c0d8555116035440b40c104d00c0c0c1003490980e0401013101004d120b44021482180f1449140f82c036410141000341c50140001c05140074050034071030600141e41c002900c7c0754804e13201c0f140394150314003041148100800d40d42c8002d10310320641004154080c0301160500e1040d08907140010300e955401d00c11820b4460b549100e4003059000d01d903007400b09104c0d40062078811041c0c4008100c0c0c0d1188070040313003151422600c100006119009006522140210525111404850060a504003888054103120001b40d40d01c00181c802c0070808540d44569041d8421003004030011501e0b2651008050030700c2e44111012886140010000b8081e403520b2a1481ca200d03401c200300070038070360801440f000554802c0860300300a101c2441ba07500c1186000004040c0036100750054540011a840c044000181c0d650f2624030b489204082c01c0c440b100740b8450b0707507507882c1c01030550101d920a0b0704040c0700a11031120525019400c1000360014441c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 129638902 1250 129637652 129637679
    0x2010902060f04080f030f0403021003140406050a110c07050409050a05070314060a060b091009090204030c08060c0301080a1b03150b010e04050c0d090c09060806180a0321060e01 78
    0x441c4d034800d480c0f151094100310382d00ca10680090464400c0180024000b44c00c15220b28428942182400103017402c0d05410780d640200100c038110f410302d0311a41007003c26004d50150241041610200d07500b002c030b141a01d95100c1d00c083c0101030240340d4440f46c0c8024848100840c00815030403c00391058140c8130300340120305810030015202c3c24440d240c00300c0c81c0d100c0705108880489811400d5141002404010002c000d2640f02c2d81c18100031003d41e01080e402c07490310080c07000350302c00e400755514180740140316404d11800900703026900d0024801008180030105003101c46a80c0b014040f2018542242200d80500c41900041c140c580c2c115040c0000d6003480d03202d001802c00c00d8032040803001d103001c00c000c1924400c90b4003545054042c4109030000d640e40d0424642e251081c4074036a000c0d07449814941c1100c40070f07445903030740350300002c10b105c903011407080c01e600307442007c0e07014242c58103068502030a080c1e20b00c1d071000d4000440309251149589254400d0000c1c110062085040d540c1d00c41000383c101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 129640152 1250 129638902 129638909
    0x307050c030303040206220302040e0322030b060607170423030f07050d0201050f0304030c02090c030105031b030f010501030c0504270305210406230402090a050702010902060f04 78
    0xe100e50414040149000020f40340700e694024030807440c1002500c009004c9021941c0302d801031008450000c0010307926402440b5410559000840e2603078504030f40c101e504182d00d82038040d00350822000b400462003505481e0703400001a5446030b62480340c0d00e804c419822a4040520602502003404200c04000d40c0d4010380c503001a00840d1103c1004808041d220304540da48001c076580160001c010905080114814a0703005040c10760a003d0b51a28840d411f61003264202c00242202d44d03124118649001402c1d00000c088201506541c144400b1a99845800c515034100704c003452082c82d02030b078041081070300320f0b0307074a0b0001d11955940345080d603101c400324020300d407043c1c4c200b550707000860070f500301048140141c00c40042483c4081c7c3d1400d0740e295101001074140c80115199003440080d81c5103406000d180310701c00004050b40b050306c0021a200c0042d4070392420104600c140000760b039511020030380083d035160000480c0c3c0c4407204240c0c01490b1504000350880804181000e0205c0401c001d4001c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 129641402 1250 129640152 129640163
    0x9030702010818060402010e010207091b0206010f030b010918060c080f060d1703270303060117160e0a0504061d010501030605010203041a13080307020111120409051b0307020307 78
    0x41e5142c2c982112a01484400f5100c00756004000003070256200362020700e05000c040c0140c40001e0f444030b45040070307100214032107000e4000709107420100c0303a41000060300401414109000c1e45080d641c8001c201e41d8107205500d0300079219500e01c440b04076000940a9502c2d40010301b00b040545000c03015000107422524044c0c180b402c00c002a07898180282000340440e80700e020102e09014400306512070390400381c241420102c4d001c0585c1e4403908a020707080300c1600300e50000c40d1a0720300a000181071241002c802c0c51548804c0c01444240e44010702d0450340072120b801d0038203050041d10301003080c0940c6903018960090402900040c4c40f01c4001102c0340003071030f03036003205038a81e01d4000640075103400d44501c0740103900401081200b403480c9181c0441d000484031506150407016945040c40b140160000441a00006012000c660700102e50380500d44290000d07250045082d400d40d01c3c2030007076105210f03096807180d000a0070800c4080b9482201c4102c55a050b40709c1c01c2c1050000d603a0380105404981 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 129642652 1250 129641402 129641417
    0x3030507031d0a0201120b06040b03040602160b0115023c070902040501110606030604080a0201090614010612050f1501050403050a080c070b04080c0625151404020d02010e06070b0903070201 83
    0x2c00340c40d00e0082406c04100074048c0c40c03030103241440c001c000743e0004006688090f070a000e080210055100500036042c0607c0d2080c0065040c4140d4802d20b401c00351443d01594032091221038907542b62240180780e1a0501d20141e518102e0451280301111300d0606c07590300d4052441d010541e8200d40e030161095803000e03039035480121070b000e24842d6507000a494032036055100400140000303d209000b80020459071001280d8409030350b80d80030a844a000341d11103425039100042c4040c0d94081d4030000031554400040c807150614001c1c00e8812031015045096515660080c5062640100c0844000390792050032140d450407541490702d400d80041c040b045550140d442c0004941c841c620941c0c040d2a404400380000c44508020000e4076444044890301d81d40d0001404080f002581d0012105d90b405090b051013a040f1844038002250303046507110081c00080028000035032550451300d00030a5083c00e248103a4181c190004107207009081c40180348503000401c2264001c00400a8182d840c400c0c4c98044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 129643902 1250 129642652 129642677
    0x120618100608031207180e0a0f02070b070503130503030c04140603093d0507080603190b0406020913090303050708010b09100905040c031505030601060c03030507031d0a0201 76
    0x406440c40c42c8580005644103000c400f034030070003042810760000207034204408081943c105a800c4d0707403078603403122550111070340400080d11558065801c4004448104620742400c0d5500da100140d4060044400c0080c0480090f222004841e81c1d0000d440d000011a83c4900e06070707010000561040c01206003601601d4840c280500304235058134020079414000d0700150514411302065203800707041641c454403d10044003418440140d40c42c0c1340000380c42001c00e00f407402400140030014082c150034002e6121f004004000200000001c1c241a0301c00c1d4004a240c5550525001901910380056840344c00c3c051200316481c043c0c0e0241e0201e82c820385040c80a50360b502c4060341d09410920850614a501304020212440c0404000150615a04102c0340302c036290b0001c41e04852000c1032403004242e0301d8400300e42345189040703038000030213049000340113540c1012801080161201801020f142d101c9012410050107608903412030f0208400c50208100300c084580c0d45c4281c2200240e000c101c864282d40d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 129645152 1250 129643902 129643933
    0x60504020f0307060807050306030a0b1e2202040209060403061805280303200307090806060d0f021002150a0c080906012106090206030a0506100201020310090b120618 73
    0x20f0f02110043d484402c040c1c1d54201060740d19900052035150306000781c820540c0003e107100d18031409002c0c000e61018004d10440142a007008000d08003d540c0801d003102d030b91007130380303007600300b03600e0a50540c0d0243e00c41c020203000c81e285000b144c100902c1107050141045181181d5104141c19601907000c40e901708003540303030002000c0d10031111000e640c0b65003004d00e40442e0081d0000541c0d8801411001070100314507481445036001501c6504c009219044208aa40c2040240ca41c1000c01221440081e5089071385061407a601880f0080c020401c058191b605903000f030240c24448903100c0380600704c1d4900030707440900400041480401003402100407440c604e6000820314140d403400a002019940c00c42c6e041010024111030032a016a11420b040005807546005140904a100d00c003041e41d04007001040b41604115050004680c41441004404550107205800b100d012810006da60b288420119900901c2000104540d105500070311981c2480c01d0708c0060460007440a071104029080010f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 129646402 1250 129645152 129645163
    0x1802130e06010b09010c050d031b1805010324030b04120804050a0b100506040b0406020106121707030302160c03020114070803041203180302060f070306030f0f0816060504020f03 78
    0xc0503031680c0150014009514002c00a01c443e40c414140881c10b410746a440c18501703c00301c11220000390302e039031050300000c1d4001045040c0d11034a007002d0060111100247c0e00c0d00c0210b00c030341c504050720b038503018800301100f014040707410542c0c2c50700220264680c1800311030b41d58113680c1152944598008024510f01c601c3d01c0074025544040913004454081c1c4440e82c0c07241000c0d18000c4070320b94034400040ca1b59141001000140025540203481e20b10385a0042c0c21213105500800328080145052000103106074041c01c0f010000e600c0b90364403904542001c400074001e0030100700310025005542030030700c1340c103400f808101c910036a5869048105642041054082c0090082450710188082000180c410303007200c4a0111514000400d660750000c042003e0500e020f054001d40c2280080c804e84010900860354800d0040c141402242e14580d9200311140001102410102d0395030307008020818800c00315a2940c03000303010024885400d081190003840165400ca1190500d180c0f0a030365400e01207003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 129647652 1250 129646402 129646421
    0x50604270507021c050c0f100c030e210904090308090606010311090f0316230114070807020310060b0a11010b0d1202070902030703060603051b0415050c01180213 71
    0x44c1c0310440d41d05000700090342a801c11003040c0311050281c1a60140304002c02c84070380c140400148015181210200304480a010108080500b4800c0100c5613210005010a10b150080c09100445103a84851003840c0a4550141d901604001485041c554040c40039401800364009544090322890019030807100340560700c08400005002d0f2810038035081c00f1442030844098150b1b1802000000e2810ba150394a40102e500c1c058a40d51603000704d240f080205500c110207003400706c0c01c100e00c0d00410b0401e01464030028031504000030740c04215141408200031180f8050000c3c03040c0c0352100034000c404c1d0020103268000540c0084090b000e20014012600016400703084000b804000c1e0f1610792039a80002a101c0a603c0f40d1000098400b40e9440118818130380e80d980000c80c00d0a250b0028103450700500100f1115080315045810f0700c180608880481c1d03508032111010001d80355040d034860044d450715404551030030b200d1b9240300c4844003202c80341a04c00c9030b100848005651030401124030905 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 129648902 1250 129647652 129647657
    0x109060f1d01290f0909010c0f080408040b03150a090c0e0103020913052203020102030411030c010906111207060e011107110904080702040203091c0c080f030709050604270507 77
    0x44440003c800c07240d01e0020030203014221200300c00510011411407203061b14024920781d5206c0d650b401103540300e000144661b0003454410310608007500d404a0602842c01600048080040803c5541100d03950b800300ca40c02c00b07000d905080744d4940c807080041210401d02c1c2c4c08226544003064080d8468400c030362071800020519801d1031412001c030781c02000d005103810046440340c2c1c4002c0088400d06060600b152013075001503a68070300b91030300b01081204030311514081d43c02103404011603a0484c0d41c410a48089140003415180100c107403a2902810754201c0364030300d034001823020500130150010b041d020150341c0240189003501084203103a1043c110080d14500c100302c900c40c1c9a1030700e280303080d80141c05a12160300b0318850b030300002c040f03900a4420420980c05280d105820940501c0c0000c00303a125414046500050340d10f4140380e51058003401180718a0000014155500503034880000c1e20000d483c8a48681d00c070340301c05040e10021281d02e88881507458160f82c40391483d000f000c1c840e03481039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 129650152 1250 129648902 129648941
    0x20c060a090804050a0909110105090d060c091203030f050606160f03020c0a23060c25090903020d1119020603060d050609010f0b03070501200109060f1d01 68
    0x180d0000d006181205088401010811002900b030340d030b0741c1d000340161031300500010300064a803403c1c803024114145103a041c031005000e0803000ba0380f0200070031203040e0002804a030300300c0c500c0c0c411070b807181c01c03600039041070701e00401c41105145d40f5900c14507546007004d404009a84070b4104210460094144121441d00e18880100000700d4100366004d1003403083c01111080c41ca0700780001d00c0e4003000d03042140c0600030b01c4881c820f001c04088010051680a5403207a01d0328140c450000c0e29404948070303004004800101e80c0718220703800345580b030003860543c904010a51040c60003d4582c482c070038031480000c244c50f210f4031490b04085140700305001100c040125001117035003804801d410042c02540d0120a0b0031000e808950240141e500c59600700c000042e14500e030700901020ac803001da64880c003e0344100010b00c691b0340c000aa0b02185101341c0f100b01100c2010031101405008502c02c001c0c0658200300030004520503a0b0000502003900594100c41c141c0540e07006c0d0b080703c04d0388a04181d4404107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 129651402 1250 129650152 129650161
    0x1509100608070533040611010f05040b1b0d02030403030c110304080d03050c160b0703140f0601050318030c070501080a05091b01090308040b040303030501050612310308010f0603020c06 81
    0xc0d4000044c0075031504d55019110550440004025041940550b020460001d11580300100a00c070304501220351040400283c02c00e07031141c55190a00801d01103c210760818070b003070000d040c0703c03c1e9104124071036410b56482c13401d4640100030f0b1031465460404500c00500701c07034100c1e20201c20341d020b4031110801040d40c1080300004030064040988a8501200c0402c4142038003810004000384040c0039020b0880c250408000c010216114000c01d4a0390740310410034049440030888845402c01c00900e00603449854503450f042c0e030281c10031000f184070f1000140016201802040c01d1044400903200c92030583d175030f00e0041c0240c0d0760031155170044c0e030030403403520f961120b8021032802d10307120602d000c0212a480e40e0f00c92066070320940242440302c00c081810003c06a26000e001e014040603111a03040405800420808080291228038003001052401c5e41d00949058814035a0003038180a17031a601c81400c2c05400c1e0300003800350207a210800c00022889600038002c880301e0391070705c00007000d0740e555 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 129652652 1250 129651402 129651439
    0x603010b09040522030215070c030c0f020f090a060608220303050919030207080c011103030f0a11030a0b01021b030c060f0d02270406030305030103080c15091006080705 74
    0xc00070705950841e1a4902c0311115403030f28480d2004c1491098000b004d00300e04e40c01929008a40040074030003000341c04401000026480007a01e558103510071400d20b40100303580b0000c0c6100e0002013035103800901c40410801c000d4103542000046039040c0d104c3d81010f4603154104407010a00b505e104102c2d213800e102c25000203119034440395208403020190f031540d40c4030b040c1e0034800b114a0383d402d80041c0e208030818420306c8810322541c0f2169109085c0045030400b1021101d48a0100600340e00f41e00c010003000810b81d003019001141601c00b01d11030369589250103841301004001460001d401840365240314900c01c0060701d080d4810701c000600500c81c0c503201400f088102c0d80314031480c2100d0f0809001800800d400750019024400701c040302e64081484400c0d010b00f04810000e28144541c1c18400d0801c0400e40000c01c0b030741541c2d00312004075510511500c019240c40b0507000700b00c0040c001c001c10009944404940e9451000340da803001d210540ea617940c0070780c1d0740c403180c084e0340d5014040b242c0e811035451 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 129653902 1250 129652652 129652661
    0x4051612060b03011e090c2a1713081e06070809030f07020607020306070905090f1012050309030709020a14071101030905070f0b030709060219081b0303010f03020f0603010b0904 78
    0x48002501605580c5851000c0180e0702c3da03100b0080410043d1101c811030762508403101c140401500700390234128071151201c812502200c640084019400501c11ba51800f0042c00070014200c520308450f100011061043c800b509443ca041d0b80c68018030008c81c102074802c2c50310300d000d6100000210f0401a00c2d14962180d40d006100c104d902c00810002e800041c0c805008951103140540c071901d01c800d28100920a1a45000f0814480300725000c04000c1c02e0305035448840292200502c1031400c24055240452440c0300c0c7c42e00c03041c2d0510585500041c1e0f10001d130003c00d5640500da5440c0c41c00d0310310110810842c000e60400506641c0c4005481c0040c1d44213900c02070406015100f1035081d03135620326900c0d00c503e03e1500a099103070710010400c10100e1300045400020020b910040100d4003d440d0301303041034545000001e040620018405d150205108400d690007241c00e0180c940d2540d48038501800d00c9030510040b0300404c03600c580e119482c03421030203490403500004400d500d400441404c100080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 129655152 1250 129653902 129653939
    0xa1a040c180612060e07080d352505040602030405061305090f01090b06120708070201060902040b03060307050603091207020409060204090b0a0510020a031d04051612060b0301 77
    0x180e9a02d90009070100d5007035003950918000c2c07600040103c3d044410030308003030441d00445811307444038605040b2560b1101403002c2008200042c480d0480c1038419010809030035000400f24043d445d800e01c00b0190340e10030002803004000110798841c3c4044a1305a50b207000c2d81c403450000d40c205010403c0300381458401000f4a030030000c055144542c407900044e000c580150340302805091203030b0052004074214410791540c00400c4038503508000100b800120383d500002c0202d41000341c40404511002d00035000704d00504000d0006640707403a10341400ca6510f0f001250828400d10980d40001801e0030300400300c074051070400c8054100d0325010041d620484d400250304030f03045070f03039160500c0c0824413620160000d00360542020601401d1101048003000c86070300024441c0e04d0500384040c200b90000f0b000195541d141c240b41e036038156031400346968402901d4000e5049410700d400c01210b09903480d24804010030030345646044800782071100040300d907207001d1980e01d840200014422915140c3d10800304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 129656402 1250 129655152 129655199
    0x6091503050901090807150b0f0f012d0c050606120601150207050307090b040e011109120c09010b12160c140a0f03050c0c01020c0d03051e0403050a1a040c 68
    0x4036000c0340c1c0c46000651180c070060ba00309041031084690a01c4502800012403412507403104c92766281e50000e60800e25024405041c0400521046a10901c600301c420062441d03d684081c8a20f0100c405481c00b0341100084035140101e6000424915140c040c40000340d00c030710000d081d90fa081c950390310001110003c0e032406611900000065a41d401c00185c030240c441c8a201140900c10001404143c55084068440990411110b4014150b2640985101d480700300e801c2c008800f03440703154600b00b8616030b40301e50300010341900110f2118114030003012940100c0603800c1d020740d02e0100342240c1810030050000052135040c4d603c004144030281e1401c4000c170440942d440c5138003c0c0c1d556007030407030316034003c40111f40081101c00c0101d40520003220000c0b4203001a1840c60035040005030b81c0720149800605120f40443c104010240410a100300b0061601c0115540d94407030030101d41e104581234044421a0010084821101c0e400103c0b13401580d014a807003000a00f458202100d01e021003112804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 129657652 1250 129656402 129656411
    0x110a0e01020313060201150b1603031a120c0111060f15040e100e07060e0a1806030209070810060e06030601030515030d0306050306010e0c0417070b070501140106091503050901 77
    0x400f080208002c008100b5030700006a298000c5c4043d5205400542c081010071074144651945082802110411580c0c14500082c42d02c0c610801050915031007280d135030300110014610201d1250005404c08400c0090300c8603c00e14084035207150351040101c603900e0005901c103002c5a6600c03a01025030402190007040402c40c034100301189403601186441c85603d240c0c850490300f10b084024040c50010302030b145098002070045c8070224031504079500c2101c00502c0da110513404040543c2e80f1460185500401c014002d080c1048010072100c425151640342984641e800500a4000c4900c4501d124000d016541503039100c400540052500070200c88100d6a15a25050304c0e94041c4001c00f00b40d005901c0020b40c04e404c00040c1480d140058000d4203821880d01c0601c1164a00c040c161001c0390800740d03107400005c401e043e402d4241380d450b5104203103010000c66044104481904102e003003a00d0240700039801da903940400c960030441482034018929942d98007402d140d1013904800d9202409400119 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 129658902 1250 129657652 129657667
    0x20705162c0712020c1c0807050f030604090f0b07080f010e07050901120606020a050105010e01050a050d06020903030403240603110105070302010b0306010f080f061b1804090503041701110a0e010203 87
    0x2826640442c00030403246d00328000b010310010541c00320f032905010502d8581180e203402200a0124442e600c0305036594000440001c3c00e0341e5442c0c1050000c2a408499280d02c0d00c1c280c5031481c0d86507000d4a404000c01d01c0300000900100b441c42080d070423659800c00b5403445480b50101a90b1319070229114504100c00082c0030709019406009140086c06558000c10400c01c450070043c0c00c542060700301b882004c0800004000c00e03500c28a0311806d580c82214041800f4245142850080c859901801e8040c0404100001403101044610070a03081315800a0041580780c4000c40403502a804001d00d8007400000300103095204202030078255109000016290714144006460304109920190916040307040a005c04d00c0c041c4900c000c500d0341d01703000740036174100710748800d2501c203100b603601d500e000021800c1c07c02003034480c2c2c0d1030741e2615009c0c6c010010a0728505100b0740720f50107401818500841f4800c0d8401c41e050511564540c00c05d0703091041d09001240c0320443c0c0782c0c48032000481c1180300a100d81d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 129660152 1250 129658902 129658937
    0xa02070308071a0c09010212030103020d11061b100b0f010804060506041d0a02030106080d0806010c031b05070302041104030809130207120e1005070308040303050613020705162c07 79
    0x11130082000c10707401070315820400002454203101d4900b414004106100410041c0ca40f0103030f5080099110219510303c0507000089440d5026404a04030a0012404100e08140300481c01040c140076140e030501120b04a001808801c141800c482c41c0041c3d1043c0c001000316156a100d180c0101c002440850000710342d4084200e44a0040900101c0350810103003a0110f240900c02c0c540103000c0880500b440701c2c05c0c850041e10460b0024007080c18400941c2d41e2108143c803500004000307000c170918040525015040c410f0341ca4600380802c82c0243d244c00154401c00c00c00d2800d0700c00f1070390301919862804003880244400c618605d40c00c0d119480d024008100026811b90010821211a80d59120ba000302034007041000c0e1180c40f030243c1405420009031001c40d0b8800c3c0403e62158050501140359140d84003c548440c04404669007194404102001046008501c11042070307030b00d13034442c810140c40300e12000005000380d007542041d00e0400c0c40c00024800d500081d5a0001e82c0342880e43d403010710020b21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 129661402 1250 129660152 129660203
    0x5091c030b04110301051207060207090902030c180702011d07050d050309270a09020607060e0a020a120b100501020d1112031303030e06040c05120c030114100602030a0207030807 78
    0x10070f100c0a0044014085814080c0100c1030f101c29070001002c2461070840081d44460843c01504d80311602c902480081d91410030038101001070140096840e42d407a2284480070070400e540c0e500040d42816a840c6280c08c101120303035030105841000c0c0ca2603030701c5c0200300402e4882a800c1210540003e12854001d0f544e8031a441c1c0d18030104440c0c4402810581d00368007140c040040c445c8030303c5440d2422000158a4803c144c90010303a0080c000500ca03420030544901d02819224002d50001010034003040040d8004901d2003107520a4030b071040302c1c2c0c03209040184402d115000d40c500503031291001e8040380d4440e1420b806504060801d40d41710859040c990030303007944116040903849507402d00c4002090b5062151030381c50542e950290140c0d0401d50707540f0580c000140700f00d520070481585030b60358100c403e220501a800c070040c000c02100315803601452000307004880440700034501070000900702e40040300f03d603000d05003030340a0241142156101c0700c032a04840c4050300c0071113050940da5080780280b01d9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 129662652 1250 129661402 129661421
    0x60705090103060e0702070f06030509030307030e2d071217030c0d02040b09010807230a0e0d060903020105010b0f04030605150d060f060504090209180f070608160305091c030b04 78
    0x60a034423030030101c4000031280707142d000c0c41c20146001c0030040003c1c3c0120660b0340000d85440c002c078800292030b01251503e804403682800182000c4044c0002040482c02c509035060342600f41e4142c90b80c3c0340b0783c1000c0d40c50030080180c00c5060648002ca0242d404400469018101c400218104100280c013881260040e8005031440f03480007a480d0b4040d0f0b0080c000f13543c410140c1c40e0a0046038040a04840001030188041000c000d0205030201841c0c02455035101130440503001240a0f200303801c3c400301500200005401552a200003c40c4160703503001210289103104ca60945400d1945d5030b05001890700509083c0d5010445000d0349155441c01c0502c401389005080200f0b2840003107041e1012203415a204a10852800181c0e0b0b0050b250306421030b51001005c05000e061010000c8041d042144154170300c0b2241c001d003180400e030300d078000c2000c074001c500c1074002d8065144c2410058007283c1050f2089000303a8002044000144511840414540d0442c07030007080c00d0320b500020070705491000700f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 129663902 1250 129662652 129662657
    0x7060f2903010501211202010b1302030a050c04061e0e090f0f01080304051003020c0a0f2004050421090314010c02010b06120c0f0906070b1611060705090103060e07 72
    0x61014040c50709000e01805481080640640d503d0402102003001c01040001071803019a1150801c84178000e512194808402034401526141c0040410380254011680080c681c1d20f45030104108108802c16030742900c106440d010700e800785484c2d120107001c003c5030400c0e0400042d940410600d441d0311201c42e000b109046035803207090400c581c0508284505070132618003507005100070041503480a07440030842c02c9500b80181d4402c2c0c840041414007480d0140505815458228881080707032903084ea80b90f102e8000c00c000281c108460801042c0c400980b80a03240c00c070036508984840d403d404007000d0200c41400d080600c644d69035101101c0e82501c1c50703600e855940d20080c1011480d02802514203c85040b0b44041ca008075003050303101140c001800c0f4120800740411001d0280140000f25142800001c1080717884034424a860030805804840880020410bc801c8d008640d0203552003441100c1c0090140c903e0750b0311340070110798a070000c00c13034941003549500c800920700d43c070005110b01507070703455 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 129665152 1250 129663902 129663971
    0x40501091a07030c0e0108270a0f03110c010504031101020102090310061e08070303110a1407090b010c05060103060513020a140907021c23030709140f0607060f 70
    0x2c0c400a002c6441020307070f10b0148803a5981c14426603900ca940d0b69484020501e06a4044030003071500c145e040c084084c107814922441003244c0034840e144001c0d0604510a5a1b454010a01c2508040d2655003145005021403000d01051001420450312080181810700c001401c0070180e1000910341401b0788040c409455070b0790800e0041920604581100c000f09591004299190096035aa501c11904c409801c000b800200d6400007001401609a01034010071b00c103400c095500003c603240d055a1003840089490310074207500c1075025401a240c13803a080006444560320b551541000b130000241801a0780c00843e0540c4c0042e6240720464014224011400c14802d40d0141030203070110010303140b04150752080c4003619807a4540840c3c440e05100a02e07203210b04040561140c400c074180e081d581035442e01c000c400c10105650054500088440e18812003900d05520300c14018510058034589801583c1008a4008a440c44d007010740c480e1098000003580d042081d0a05000e400781604005400505 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 129666402 1250 129665152 129665161
    0x809010b0607150507021c05040e0f060f010e040b0d080423030607030c020a061e1104060c02061821010507030b0f0d020d0c09022107050909040501091a 67
    0x910a0030440c04094407901d10300b58003a201c102407075803c0740700d1000380380e01c542c0094006403003401501c0c50750564103882c69081050319005001ea070070901070613019010381d00000c0c11441c41005020300403800034011034800fa40c1768004660103d40e2040d283c2c1c0258581d03002d0380c0702e9143d0b9050b20109602a01c0f44640b1541400d02d0901440703001c1903030b07030204145804e038600d0035075002c5101c580252150a00182c076038005442a410140ba61f4000750032185000322581c22502104107030070102102c0d807001c0021090f1403550540a0040d03000b203000280c1c0307a42101005007080c10040000d41c21282c004920104640e001402203c40b049800f02c14001c0b80300c0040320500c003409041d0700503941d41030a100a80c648004260001c0c91070070340074411150418410207549a9000e2940269048203040c103106450b030503508082d51244486e0860408540c441080030070000c2d0308180a2100350303440901d403008100421060580c06003041d41d15550b2100080d001452446828034000c2d04549402514a003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 129667652 1250 129666402 129666421
    0x30901090212011103010e07030915050103050f060115111f0603030f0c05060c0d0b030d031d03120703090510150611010e060609090a0212031e160821040308 69
    0x141c80c2e55030040d680c100011810800714180070789043d038281c03241c01c0c4990b6070f5041c42113000d0034100710003500c00c44030054403149044641e04158140c900a1f000c4402e00914007401b247d50368801d10603032000c0080780444840c001d100c0c4071140202012081150006110141100e0030784a0520700901e115941d07000400402d5040010403203541820700304200c100c0542e40320b89032502d10080074419403040c0001c4001030565183d1042c00c12807000340454006180c81030001c0d0060a40e40c807000c0c0f2200708a44010020080002142e10050340f8601c9528152200c14041d00644201c0c07500711514000d102003481c64503514402d8104100e02ca00040504078600320020780710101e010b61061050741010303100800751400060041d04400c00f030303c4410441d51782a4089040000e041c4000b58000c0e040031080305040d000201401d03d08014480c10400651406a80080c070300c07803602400c1d0201c000c40b42d583c0c08588201c010380720121150064000030044a1444101e125040345c0880220b541c0c001801030180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 129668902 1250 129667652 129667669
    0x40c090509090f150709050904080409020310061b1a04050c0613150c08070f020609030f0102071101030c0c0b040f0b0901020a0207050603150d0c080d110c150304260309010902 77
    0x504c0440616241c2485e00005000e00c10901a8500404094010070100006401240d0061207014800c40d00c03802c02101020300c01a142c4280c50004860201c241c0c1c198510b40741081c50242d0003048411180810224800b07811b4000f030080d500c6d4017a540751725010380c58400003481c9110400100c40304980c205100381d031900c1c0e50081100d080240c00302c02c000000c0d0035207084400700c5400807440800d4604500c009240c80c0301d150309090f058011808030082c4108150058a041031141c90a00400c00c01c9400440440e10402c1766000010003038200480032600c42d5030010781180c05960125070420980d1216201c1b05010f554040c0380d41c2d4000394415000703605102d9030000d403404440040c80c40c10aa642860504030240829101c1c964140002c020040c82c900c1a200608200080d41c80c2184030810103084075003640040d4000d03014030411030710140303003d18854144449210880e41152030716124082079640c0c03005480aa00e00e9400c1014401e901c070405980708a040d80c00204d80c0c4041ca01c1032000c00d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 129670152 1250 129668902 129668923
    0x60923030a021204380a121109060f03180a0308070215090c01031d060c13091808030406020933041406070203150f06040b100e040c090509090f 63
    0x502400103004110100820008280300021111a030190070071540300d01c0740c1400342c001c010540006006c1403030390304a81d419600001e824010407070340e404890960050300c11000060351001040228030800e041e0342d03000d15001002203241c403038000c0c2051030307080c500741d00c40c0701c1036001c54000390420090341c3c0c0c1089008452854002d5840040c1000072041e56643d240038070701d074140f5850f040c1803042c210210110b90641d20068080314800d0911805101e85e65024a40c0e41803001c2003010046150709580c040c61406034288550402c02c03810740d0300d07202034a4101903c00c440f000c1c1c0802c000961a034a901d103c01e0217070100c2510300f61081e080e041c440c01141d51408041104c0c4401d004c2001031030521050f0142048050364500c0d590354562001a0402040400d101801d50a100502400725059503415100321002d903410402803009408000e0342c0d50b89426407200146000d1505903080c20a030300140a608071a00b0900d251540f200c1c0015412401203a4903501984041c1d40a4200102007000d207019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 129671402 1250 129670152 129670183
    0x609050327010c0b0705070c1409070c12120b090f01060f020f071401090807142d01030b03010b031002091c0305030115020709110702090601030203070c060923030a02 73
    0xc1c10800c0d000608051845640507050300101000107580c01c1c000c104542c0007613880082c07800901d88880119180e44104270410740580710b0f110005d01140c0c02003180c0c81c01190408880841d0002d0000119208101e1004a40d41d064450701001c2e407940b251307036065004201c050180d880030340c10082d00510482c0c031801d41c182103501030780c04064084004a000016030f01081180e602d6904800010f0320f02a015502040a62140000010300b00060030120517160710115244e030380d003c00030262044900712504080404c2144003041204540c06540018540c0d0005400452002103080005e800d1000c4a01c1c5283d00507000a01c000041c540092800365041d880b440481d01040c55450040030307400140a0300c0095525619100d0041d4002c000d002b00501d261a000d02c400501d003140c0395144c3c3c110701400ca005107a45000300d003996029000f80c80c0300c1e0115076102213030ba9145481d88400703081000c40a0b10185c0030440b40c1c01d03050f01c00c202c02e40b1000021400442d5201800d600003490040f0800307c4c03025 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 129672652 1250 129671402 129671467
    0x180109050a122a0909020f030a03020d0f08010e0106032a020c090a02070f0f0804030209040f03030f0b1f030e0118050f0f0334050609010608060903071202070306090503 74
    0x203202d0300c0c2e003810f0701c00c1d54481c402c001075814042c40829120a9410030055151259601c201c0403d80e0004000f4144440c5545520702d08091000075603c1180c00e0140d80c1400d01004010f002c500d2090340f000d80320400190b5404140400000b044400c0c0102c0402b00006070401401200d107070802d000c419810001b450021803400040d40c031040f03c140c1039084c00400c25032000c0e04031028400d01c0c01c01d40700a99001000c2d00c400d802c051924400005040a0450100341402031201d03220520b07214000310000040c0c8641107242d500010584d40d90000c601640c03d2580c2e8014140700d6007400d20034804030200e510004c021100d40b60901d54a000816514244e4680c01903107521221180802500d840c0c00080841d0007000e802c0d004010100840f071400f004d4050110240d18080c4000004d050740200d5880008024041c1c0b24100e180e00c078182252006895401000a00c00040b291301c030b040d4041c111441a81d0b01d040c1c80ba664142a100341180944040d4804115030180c0f0031030b4400c03e5110981d0075503661 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 129673902 1250 129672652 129672713
    0x30b09160b0f0901120c0203090906060313032f01060501020c10020a06110d02032e0f0b03100b04030501090b07052506061503020310060503010308180109050a12 71
    0x34040c401d107142020070701004034480342e083c0d0248601c01011170700020240516000544001d60701d41000040364417902d107032400702d03541d42000310403030f805040011a80036068169480a8400b40000d41c6122614480e14078110110030302240c038140018030181c0007141c0c0c1441d01000900c1d202c00110302ca0b1260381c244a284820940000715030307000c50343c88040400c0500d0040c4591415010341c12403041586e000004110016003001480c10140c1d1a845a1580c41c0d84030242c0b02d400c1001d24020300c0900031043c88140303c0c6410400245612a40c1c42c03c2180350141c850000b4001500315610403945c1342c0d11416100100000d100116a101c00b2624000f1b08020300c00e602c0740726400080d44260980c074121b001d48018800c854001d503025181195600a85500ca00001802548100c03041d0304101182580895414454000c40c1e049a4000c9100341c00c2420394001800c04664014034035040c006000c4001449443d0402840000c2110100940d460115410302c1c44181e0744401d00c00752003811128020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 129675152 1250 129673902 129673919
    0x50601200a050f070f090b04110412031404060c0b0c210106171603020703020f03030c09040609060308090910080a12020616090b16060911030f01050403090501080c07020a030b0916 79
    0x220201c0318241d2007c10105c0040c07012400800031641015101da000190210780501e8007050400e5480c802d030744424810b680c00c040c80d415030041d4094440042c1c030a03802203012411540701d10307410640e1407401d54684440740c1e50b2039041d001450700702d40b480c800c0314004011150300b000008140700c000010388446403130403070800c2c4043c020703018a1409040d4040340410506100f000708000382200103003280d95901b000702c3c5c003c07990303000410454803480c10047e0128101c2c0c0c1c24007a0390112503021075102c4c28080000104055018000d11460140c0c0f108074000849040c1004180781c1280120041051115030500080c21b02c0340041c001e5109a4951748503865895200044070205c4000e403d0594507130010b85042a0303224034070417001d01954240b5400d0301c1808003485c544103065804800701c60b0300318028031000e030a9490448020300801c1e5412010401e0703501941b8003d5201d80c011046510380138840d400940002c1c0340d0340080d074000044001300300b00f48900b04070990341060000807034900305103041000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 129676258 1106 129675152 129675179
    0x70206100504020f0d0203130506010303030c0905041406040e01060e010f1403070311100905120a140f06150d0c0b0c01050601090305030a03050601200a050f07 70
    0x905180902c01c440202400d007136800d041c00360200350301d0002e400c018505c002041e000d1000400091050100328061751081d01e001a201e0710440e001411800319800441c01140392004031480012202801c5901000486000c1500000307655524058503c039405014a0b4010600100e2020840e0a510342607031038401d02042503040c17440030141c0d80c001c18400589801d000d40c03c40301c07903800c10344c4581d13140da001402d2602c1415507403404607490710242c1e03484d6491900040030740cac010800c0d5401c121804541c04d50083c0040130203007940f1502d900028155001504105036020712507111548140201da80007503208051035505c002240159100c189566031039480c19000450f15070148210f00242c0e07070000300441c00e14050795401e030000e00c0054002c07414081a1580102d510b1421400344a4800c0f01c5806010950800d143c81031134a0100389030700910740c1003040140903078100d0401 = true := by decide +kernel

theorem cover : BRFrame.Cov 129496402 129676258 := by
  have h0 := BRFrame.cov_init 129496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 129496402 ≤ n) (h2 : n < 129676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
