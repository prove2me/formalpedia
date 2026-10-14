-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0522
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:14:45.627337+00:00
-- url     : https://prove2.me/submissions/6bb31048-0273-4354-8670-d04b5179a2fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 93705036 ≤ n < 93884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 93706286 1250 93705036 93705083
    0x503060d0302070f08071815060c0201090f06080f15010c0807020d080c0304060306061d0118210c050d0507030b0a02040509010303030f05070c230f10150806060d 71
    0x510806030004c801c680800c000c40302281c00001c99840e00010002ca11480407544152000d88003422401081040100701041c4981001003409006050404680f51580c02b042c0d1101d209822030008900090f083c4041c0e21240d51410f035208003011121881d075a05a40002c000740040c8101901481000c50750006540d10f0416020155078400ea0155584509020312030700c07038105100d140080382c0340501c0000c099008104c8142c5021070b40c0319100345002d0100043d00c450081480c024600c08844c3c501081d2050f0b15141102c600080b010325402c001c15602d010241001190096809850304101071130000b0300005004007034941c4078a210040795200a00c43c0028040c13503121640c00f841c21800041419095844a40c8030f01d05558188843c0d59590000d42d5100ca0107400244016503041e030b840c2040500038a805892a09141901c805d013818a030204c0c07070502102c10300345001e0340e200080345a00810f18102001484102c02400d644d160600000360350300021070000e0035000c441840d4100018400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 93707536 1250 93706286 93706289
    0xc09220303020c0d02071505070b24040509030d11040b0f0708190c0201090806070801050f04090804090e0d0906020a030507060b060a0207080105092a010513090f050c0702010503060d030207 83
    0x4c445804081500c003d54540292090f01003000961560052043c85202100c08450b005400c0f007084d2b480b5100f80c42074006d9418400808080e061003000d58696842c01024040d400c03a0005548405e02481c100084a4611400c419a850104004c00a1041980c1510a09801d10400980302c5020341452007951042c41c2001c26031022081e14080119000081d10b030f03001d4002c1e80c56114154440721802d640e00d000f9038841c0c012404070307001008189840c41e0300210401c000351000c615642c250352041e01176007240d08004625903c0f0400c1d1003040000300182040380142e403038030320022860450040e460314040c0002404005001035164103004035500103040d04a006001c103540c8082e001d00080d01d83c0c03150f020f42c40055003080c0c0841d40000c40058000385489200e800300000b450580e81d00500c2812140900b41804000d2101c4918041901e0340b403401820182c9000c690343d41501c0307081044400c024020b0803010814850000540d07446400d49921032025181c0d511403001700c0c2001e91030025079 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 93708786 1250 93707536 93707557
    0x3021c2a020f060a030509011b02060609061f0507021009061b0219090c020c011107090207060608030f071704060c08160506090706081b0703050d0209030312090c0922030302 76
    0x12010301300f5926a0002e40b240c0440c1d8002c11201002001c050349042407031003c5070041c2c5c880c5011480701c1c0b03040c2404940101d0000c00c041800401e411000101b11001c20711400450380200d207002c10344c1803200b00000440481c0c0f070308540550409802070040301c49145420510909520340702d0031901d07048808245035925001e03941c1401e41d188c0c0560f01401c14040c48600600525001768203650144010403200209280035024a03400c0644200083d08000400e41e2407070340f903000026001400744000c10312000c18920f11603481c021070030411152040e10b8064101d40f041040100138603948202c1c3c2400c00b80c0d000400d107035a00f071a2200c0c6061282c25034009003013070190b03800340440010300180c04003c03160350b5100c511166842c1d155808104180c505503501c0da0000300100c4000038419401030111004142c0700504009642002c02d196070072240c444225000444140940c40408200c2d95942c8d080480382c01d0700c245029031144800740f0a400300c13446102c0c8481000400c16000780c0664120108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 93710036 1250 93708786 93708799
    0x702030601140118052103040f080609121602060a0e0307061d0604140108090703080a02060f16020d081308030c1809040305180a03050a03021c2a020f 66
    0x8540411030020b49807891074502150300d85401e806002e032200b25980840e040100141a06980503407008005400f40580007030b20b020401010400780203c0c2c03001707005041600020b004610b4607083d02403410f01180707084c4645800c10701c43c174902402c000c10b107850000e43c1540c0981c0c0b0350100c1740c41680c110b80386440c0143d250084401c0070400642c401100c2d810003120207001621041a58188643c0e48076500450070209405650500303654051403605411901d07050407294696600d4441042c503421181c020b20040e0060f070107100070b801c0ba03520901c2d0004400340f80a40c40d0207140704065902e01e2016844d00a22440f24002181a82c040181e86017407174105440581d82d107004200640715500c4403c1c680c102422031a030300320107070401000035031040d5419101d140c0341c81b022910700300c0c1b03400402e04510340c0070440245c08000144280700c6c02503607a00c26001030407403120715410481d03600410060130080025a00e2104009445400865070680349a562802c02e00001d001182c0101c009030101a00140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 93711286 1250 93710036 93710039
    0x5150403050f0607020c15180a030f0302010e01050a0501120204050403051603020304030218060d330c09061107060e06090d03050304030e06040b0d050a0b0306010f0806010e09190302030702030601 86
    0x716140e413081d401c903426a28414a550104402100d208812003c000ca09001881d1a10b60140700c030145981d00819008e43c039581e80e51401c0d0750600840e4200c0041c1d4484248221600c000d00507550081601ca4043c4265810310b5141d1845d0b8010200c0a80f141d61a480800c00f80750144007110010805d0441e0308200e110799040203952035220344012800352224001010107a03010740c0210b4003a80c0010070b104615099a240c131040d096101150010341000420030907461285424102c1403c04145404615401d441c08050300c045807907404030090002c0c0448000c288080419141c09907103450400e80c000d5908003000c030710607008410829400100440540b81450f40001c003640c4a1480b07696961440301d01030080c44090302440c405e50700b40d103000f401000896082a0415684258201c0c0002070321901900002c1ca485400e9100d0000d00003602d1003881201384c18040c1601400e903914503020355050620700b1942e22400d0300c820710041300200a0403c1010f00c00c1c0100c8001382c1d002411500c565 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 93712536 1250 93711286 93711313
    0x312022214180105060f0a0212072a2409180203040b1b1e1201180b090402061b03130b0405040e0a20060408030301031104050f0f010515040305 63
    0xa0501c0c2084900c1250320201c0e00e142d1080002400f4166007010308010f080c0136641000c1c00851300305000d00c0f015030040002d01c403640000240034040d514060a05001480801200c0c00e00f40c0c041042c1c09603d10302140303030034020714680c003103e07a05000b400c1042030860b204410f0101c640e560a030b0402807122046c0b1007034202c1c804180d00075501860007400a000903840340e000b440403100301005c0d60800500c0900c840c1000101c209000f9445050201480b071030102003011130410400260082c40d545441008100880440c520961000040503517122605091540000d4240e01072001c1c0d0f910004040c0141c070030300d0001401682c182141c10b4150fa0b00054440b0318814030b0f03030024098213020b03500c6c1403414a0300c108005100420290400e00c505807000c015007d103c0059681c206940c0c2080b810000041c0f42407040004500841c02a0000300c1458075000401c0181c1c2c070003400e48241e50509205000c002e83c5100030f0a0304440c412222034250140c5c004040c10903004541c03010700240100b42c8840d64030b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 93713786 1250 93712536 93712559
    0x901020a0e1804021005161505150f09060102030412030806030d080c27030d03051b040509131509050c03100e0c0405060d0b090304030b0a0903120222 66
    0x100440d500ca2541c4445040144002d006803001904031881003040410050708010050700480741c0360345801494110102c0c0508601c0c5803401d411901250f625545900b0030215108135038004440c40001114080c4040005202c4412001030705c1c4103000315401700b450380c0e0007001100d0040100c0c940307500c00541c40d4180904050011035080c1c3c0640114914000800d1141c413102c0e02c14907000f41c10350701308200303d41c3c402000c0001c2070006002c4c221454250103255410409030305c450a403907402040c0390bd04600c40000c402c1d07000f0b60100344190140070920031662044441d6074004080c0e1100b1282002c241804101c5007041520305241ca85405440750034880c000c20000d0000c0419030440303140c40c40812201c3e00312805131200e41d20b60741010304c00f21110719103a005160408801400d04003c5182d580b1142c100031000d848008041e400090200300f0401c00c0068079a10912500303041006201c0c0b43c402914041d2030140701140568006000303c1c0d9040300c4000340f0100000109005410703030311515030104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 93715036 1250 93713786 93713797
    0x903070909150f0204030816020a03080c03040f09021305010809010f05160e03061012050c031b0a0f0501080703050406091410180203070b03040309080303190c02190b0606040905090102 81
    0x10390305000341015582654002c0f85e0850b540907813070030b19221084178411703689105582c0490344621983c00000c0403c04000150011855060207983e85a01c0c01444142a00f1180c0c01013030303a0b0703005006004041d928800200226482070800b00c5081e0350f00e603d124010304800020100d07440c500010b0080c0081220700c05203010680b0303161034803071080385020103035101412110f1808115441d80c051003040480b81e041c1c20424806e10440d8561040302d170010381400094100e12009040b0740c00e250a0320f01e407060400c00184400e4a5101c074440c06c1500080030285c00404100070f064a03080403800b040310310341c4402e00e401e0b0407207481c06403408621448e42d00e40c3c00021001c42d0080c1086007034100f0022400014035101d070700a0003020458a0102c05a0041d04010020740a0120038000040c06100c01c0c8011442207400e08241140203820303414810454582001c0041150300c41810001ca8680300c0b00c03040c2089401c001c0d508025590580003030103e10030b0740c1102800504200900c0b80c02c0700f05401410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 93716286 1250 93715036 93715073
    0xf010603030306060f2c030c03100203040209060a03030807031508030c0c0a0b040e040224030f0906010603050c031b0405061c11030402031513061b030e120d020903070909 75
    0x280d142c05c075a001202d504c1c003001c01c4460000204054800301703030718030440d002c18008080c0a80d0429500c860000f414503001c44009411541c0020820045145c010851a4030900442c1d10040c80c50a50b1001085054003c00860516a8400d142810a00511181e43c010402c0004896503988843c200e207894094280c807003401a0a450360114910142c0f10036581598922840102d00b6a605c0e0200702801c24400c40e45102c2c41e1040d000c800801c60300307500951181d0084000000c1c40d04103070801526005050740190100352401c000d02442450a4080701d4000400d804880408203e60343c0e1051144502d170300c0706c0e030301c00c0000400407003c800a144a81c080d00341b90344104403111030f030042041684400c84000307526400442c1007004880b17418481541005180f100c3c041c0303880d5a580e90300120b42004002d4080c1e90740b002610b21013103506010300c05009001e10098072882550902c0f07001306002d401031030801c040d008145082d90761000c0010100801d19840300f0f0000c0344103800c185804040742007008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 93717536 1250 93716286 93716297
    0x1060e0106030f0c0504060e060f0d090b010303020d050304030807030911060c070906050d02010c0b071214041101030c0816021f0c18050109050f0d0c060e040f060806040b07020f01060303030606 85
    0x11340d49000d031090310300b01c503841e4641c18100304111040040c41d600080b080020344005100c0200c604217280300d81d0a030248111000c16042d419414041d1906c003042500c801006010010000000d074040d10f1980c2240c6c9904001c101c003181e519168a1001c1a60a803d410200204024402d503900213010011180c45a404002d034a8a64082c008084944000a4007181d0001c01d0400061400c440b4503505c0f074203030b24104044100740250401079841c4a000742e06c4444501c07091000780321640041d04d01040003403c080103420074110f0301900d000802021850345074960030405045600078811580e0b0300d2040030520411058124040000380074030040300000805002c0e0a00c1070000020740e207001e81d01c050711200705091500d0204200c0d84800143d031500b100ca880410400203101c41000700c094512910b03400c40601210043c017084403140b4284003000350805404004203140400c405412039041926000742e075803490030582c90005480d18881156107066400014107505500090075a105580d80703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 93718786 1250 93717536 93717551
    0xd0804050f060403020607080309070803130e010603050f0402040e03070605010f0e0105062b02040503060405010506011112071101091e060215061003090c050604120b01050405040506150301060e0106030f 89
    0x10b221241c003c50000a411003c2005100041092000916803000444046824460f1280c41c80f50441c0c00c00740103000d1007034889a0521605041e0460303c0d024140e5442c0412007071034aa0030280700c48802a0001e07008682c2e0700c203030880304201441101c1c0b910790040c600344810350351540c1c01601d4441c0c0e80314080c80c050200002080d20b00c0c0000440301c59407440c6c07200300303c403124030b03042c400e41300400d0044803d019500b00030000d00754405000d042d00c0b0b00d002d078000040301d142a2001400c0001d032505054401c1e00044410a190f01c0584161500a07402ca58914050120f100040e5610081500030f806440d07029101d81c00e035204030812030420b5410903402d460500054091320b41d000340e400c1d541507500000c840c0054001c01d00c254040c5485500560000540c00d964002042e000d41c002d410080b800d0a80103051018020710264107401440181c40801c8103280a88400340c903184040d04840c03041a08050590a46d40c00b500302e0344c064107003020111480e5948203000340003071042400c80d0001c142880d0a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 93720036 1250 93718786 93718789
    0x40b0909060409050304090b0a09050906090715050f07020f04020705071d060d2402030a020c01061403070e040f06020f0304021207030305040b0d1509090302100c140c010b0d0804050f 80
    0x1d034603034880d800700085042c07600f0103003800042d040c6800031075048043c1c42710020384002c07680035850050710318001404040c10000542030611089400000b01742c1c020305441002030741e018003195500c081e8803580e00d441d6401440080c0b2850300341c0014a07030107400841c0d1401400408120b00d0112441c2c42c0506035020b10713000d0303800e01c0362408482c0c4030361101804030520701003580f00006403e1007940e80610401140111600e4080fa001540c0c0c00c810720354081400c054039000ad1003183c01030000030300d0450000c52802d000942d0790380c1d20f0066250300025403012800b04000fa11030701c20000c0c1c0c480400d54490000b00d415141c4e58208a030180d10500d1188601111840c0c0801c84805076601a0380780c0d440c007401c5c0341c4941030540c080440d0401040c0d690740c211005c030350380205440c040d20314840041248240d41c00c00a01e07280c05140011821443c0001c034065454010301c011200410b240a4503489141041c071140c0100703222a02d481d005020b586c1d00c4820406060b00810039101c1c00c4031507401a030b46120 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 93721286 1250 93720036 93720041
    0x60519020109020607052d060403081905010f170604051b0604090e010f1406010210020901110111071b14100306031a060a080d050d051f03150b040b01120b03030d02040b09090604 78
    0x21f00100303a4100c0f40104012a20500c1d502c1c5e80181d8000d82d000c01d0000d200b28240440e0000d900050000000110901a0100211422141c904d162004040900b8103071039283c0c07151555189108101070f203064100c06030715004160740c01840c06550402031010600d0040d400780c0410307102c0358030f006d15000420212003505507a043c0a40c9060f80245442c00c01242014020350241000f141400204190030b6040d0b03100340070340401279800c2045141c80c4d05480c40c00b25420803907203c4e0142050304032041808806544030600304101000c540103020141c0074a001da004008980010b42281c0d03910480c496624000000c15029510645d001c0142d117554100300c507110f00f4924041700c0001d804001700c49000800390486130700b00d00f620894a101d80c6014210090010f211b610441d035242000038042d0351303200c0714410500e00100c244e6060103001d0081c80002c2ca500150023066400342d07035411818805450400a0711581f0900d10000c40d5034540750941d48440750004802544229194000200c107410a0b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 93722536 1250 93721286 93721363
    0x621030c10110a0c060f1109100c0f03080a0213270203010f0306020c070e01080f0105010e01050d02011805090a0b03070f0f030b0a0209040908090f01020706051902010902060705 78
    0x101c042e42081160441200c001d12810801d480c06504c1d64001211003005102d2035a51401e400c050a40d25041441072016440c1071800990521480e81e82c1280481c0d1011a2000c1144d80340c84d0075503507a41d409042e10024080c1e01500b45400458940102e40c184001c88e11000013892448401546e81a000c0000d05070300c400d004184a000807200100300098542d000323020a103c1c8901900c803460f803141d042d0507401e60309900050035540500308165100ca0203114003801742820341e4401d0706560600340407a01c00303e182c0a000341001701151400310403078154038010028100007000380c2e00a0604043d4407010300000c1185511034021604005003800b0601c001c1c100f180c4400702c41829023461516030000e2405c000300b00c0d5040c1c039003c203c000d00d2030381d56100b0030b0701d440d01c03402c035041d100e414203410b11181c02007000c107035415584660400e01c120381d009170988080c9031301e2101200300c0030040003007203015064580000390041381c003040050400c40040307941d0b68080000340d9200c4107a0f40d281d03110050003d11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 93723786 1250 93722536 93722561
    0x1060801060e0a08030a0c020402040509090102030402150c07050f040905010e0708100b030a03180902070803102c092e05070906090618030b090d08070c05030d050621030c10 76
    0x800070000b00d80d006020303107e0181c2c0003c1005040603500e502042c1e910504030f84441140c0d50000422045162000d61034101c105218010750070401d501e107070b807a91581ca5019082c417600d02c101596081d5540c5411007440c1d075070320100900034528118416035683c80c06029000d264050703940429203d0850344284101204000c0c0103203940b40494909542040079980580d04180340700c440402d07691800e00041003000c1c80360002513520301c0c200403040804181a0403250361120100c2d0810710070041c14200d42190581e23400b51286039110100c07818640940c43d414083c4070742c0080d55061541e80c4d060f4141405e15600602800700c0d82d00c101c800c80e0034100501900d40410a140000e11a19101c1c0010800d5000381210031a080c41c2c590302c035860110003c4510702840d40c021450702e2074481e030101c14a81c01800b241800e82d8002d106644881d10b9010f002a960724061b99440061a150741e40298242400030401c4210b507480c0455640c6a200d80c011001030046204582050502400307600c034182d5003c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 93725036 1250 93723786 93723793
    0x120f0606011107180207140a05010b0907020a0209090f010903050903150601020a290c13140a0509040620030a150609060e1906090518040f0f081201060801060e0a08 72
    0x14a1403002c0c450845611884c0215402c0c800d010004407001c0400426000d1100180150790841c5481400c3d552500d840c28091005041070003100c507000600c0c0c10200b44e040310a8400b65840d000700324070f44982d041c41d0064a600f090526018507400030020022236409074140c90075440459880041c141003034590078016030092941802040c42c07220072091400c07910103c449032010007104c04461410544194446100021f0815100a01d2401c400c005001114918098820220024840c1d850610405008490080c001401c0014903445444070180b41590562443e0303c0040407030283e0012280560342500c0c2100a00513a010424074400300e49007a0f589072107150418808460040c2c0c510500d035049050054012004d200503030988001d03110310358800c14003030b146c1004c02003403620140390050781e02000000c3c0b2000c204645982c012080c7c02a034980a803031400d240c038960b80e10403140848201c510b01d44c00441c0c400c1d84546514100c0d0500e0341c4100c5410110005c00040e12a144944c40c1c4a91 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 93726286 1250 93725036 93725039
    0xa0b041704050306151206010b0904020a090302100503180703080906160b010905070906030504050a03050a0c062a0305060a06030c020307060e010e0d05040b0a0302090609120f0606011107 82
    0xc0c045032006820048805035182403903039400c0400d19042041c1d50150000030203000002d2a800c0105801e00c94086090040210b945040c0d809007052180c2082d43c1e0180760006801d011541c0514190b000a40e40940b1114504480c1c1a004000e41c0058800745c0c400d03000c650740c16810010001d844010350760000c00705494408500c0400c61130340d10030320354504c1c040800d11449000c0ba5140b0119802000702040c082080d2401000040440596400c1442414542400d005c0801d00005201981e0b03075240c00c10715901d0f00720010a54141418000c000c03d03d6003402ca1440340408105613040000307022445610710240320500036004d0340d038100d45458010601c0d82c2e080103494820381000d41c0400e240d0050328a890101c0c2c071204183c40305000c04900981d11341d003000800c28003c12110454070507a2414509190034200400c1240c030801c222041055000300316805641d0b01c00c42154a2141c00030101d03441c0704d1110041030b0310395034642030040440c0100320000f041c03940540c0706598040001c0e0301510005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 93727536 1250 93726286 93726293
    0xc030a0812040f02030607020a02030f120405040f060e0c0c010501060f080a05180111090901051507150b040e0a0b070306141203070f05070e011a12040f0602030a0c09080a0b04 77
    0x11000502c140c1e51070804660f0403015032030510003180030b0801507001c0c1c0054401c50051600d4070455900c0c1010940c0304c02c01e401c41c0d0b8900c12055500380d030701c1150082100c6480d888031201900458001c081c00303030000814400c0c0140050010040c60400f00c0080c031043e80e80d040181d50002035480260080b5014a00051044c81940d004580c01a09590300c02e0b0303a46e81c030038550f90031075400290303049420700002000c410364540076150900410302102c00b41803000c0034654500450250b100024520710810703402c885007007800d0300113403034190025204010540c510001e0307a41e03500301401c0a0354010302d070360080b441d44c40c840d020b03900a8170412070500e8100081941445040e0440e44d2000140740400d000c1e8400292403d801203078502d000328000d05d0804c0c1401e80348015072006070b11211111401120401e0801130b65015500f041203d154003052a607581e0070300c001410b000c164000c04440c800000c1081d0f80c2c28582c03103e54001c1180c1d4a80d203410392620000f0350398650071400500801c24140c00200003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 93728786 1250 93727536 93727567
    0x306090f16121b0305030d0915020a0203070b0403020106030519060c08150f010201060504020d051605180103050402060d11030702070b12010902031b0a020304180218010f03110f0c0c030a08 83
    0x103d45480d07182102a6a03a403a4242035410a0003003180c0182c85015602c1481100300084035500040d880440c58440b40310380c040c1d524414008014240c000c2040000c080c18001c0d40090015a00f0600b40c900d040803072204e40c0b070030103460702c01180d0f000c4c6003050b5040d0301413260f0029441221400201200218500100480b0800200c0c2080c1150740743d0704003140a40b0f590002d04109007600c1c1d4046242d00789140c505018403145440d05040150034080c40c00312803062001206048420700300000c40351681c3c00032528034814503516041550514015149540010004600c0742105901381c0f001c16807140b850001f03a04c541c002c20140c00260300014010703807100b9402103400121700071544400c203660304c100c55403030f0b0440c91654026800c045000c00441d01825842407400340100e40840c640042031110300b9891441d50b250780c1c100304a00041070103480c041d41c0441284003054122644a03807080507081c1c6c0c41d43c0300054901090240b0031090200d81000107500200c0e80d8800d00c0d440c01c1a417810300300c814 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 93730036 1250 93728786 93728813
    0x6040e1902310903030e0607050f090d0f030206010510050a0203190507020a061205060619030c050c150411010503041e030302090a080a03031103060d02040b030304050306090f1612 79
    0x88505440400b11100c441d01c00d907258403268031a03000c100c0000506003c0c00b240e8820003d02140d40021040004846c3e0040031550072020480340180c554182a0104d03140094105000313003001461300c1e080d0203040e00014124100c034401c441c10300c1080200c0e241192203010390b200d0580540d106100302010042c05040c9900f803109545081c5040c507865070005001f0070603c1c0d02c11004a000000c608541d060f15001c2c00e5031251040d070780145040c0a4030340c5d0b0b540151300c92904a04150350760489181c0b041c0b01e8070455090641490890380a6094400d802180c0c1c0002e4030202c8010046d80c2e120354295002e8402d4034440d80d00421000729050b000e80d0817070400510250704504241d0300300192200d9035100240c41c00a80004402000e058401d0b11700902258644e2608090007a400c2c27040048a503130712200d14240d02ea0680d008504c0310b0403a00880d10314001d54000e40e44c5801140d0030040000030000c0d203014000b4a1038115410469108030000d000e0f0480e004d540c140750b4503004900d0125031304000051 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 93731286 1250 93730036 93730069
    0x70f0b0f160519110109210309050a0b0d0b10090e040c0312030204080d0306030b0c0d110a020102120708090604030c02011e1d01050412020103110f1206040e1902 71
    0x507503041665070386070b0401100315103201d001041d03141c119041c000361036110700802e60213003040c200d01c41c1082c40c0c0b000003c095041c884100c07c0072441003010140725a803080d00a0038050600681e03e901c13a14a100d60b5005090364034a5549401140a43d0b442c0102104800c04c0280c0c58200c101070a0580d141d00f01c01e40100709a654240c40000000003601e040e0908000011540e40103031078508202000e401c0211142410081504001083c00811141c400d402c0d0080039245900d6901c0d801c0d8a4058042c0084000d051441100416420031403074041d0020b2000394a1103a490405650703004068407040f17000c0c0c50010180e031040d00001c0002e8060024000833a005040c0380450400100051112031000401200085c02c108040d003000020340b440c4100f10502405c00c1410300d03040c210921080a900500a0704168607103a0064100703440508031051004850300c1140d0b500c84040c41501c9452055404c0d41c000d40c030b0000010400803010400382041111a607075040c18404a800b0098681400414803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 93732536 1250 93731286 93731317
    0xd0b0402011b050d0e091b09010306030606090b030d09181d0a11011101090b0c0f04050612040b0105060406020d0c0302010b10020a0203010507170c0706020702060a0c05070f0b0f 78
    0xe18540c0e40c04040400002c3c4224010000d003001c01c60300600d01e01e4070607981401003a0704414052005144948282c10202e01144203881c0c91070000100d000d8141644050016858124041024102c43d04411a034041c00d40498040b00b040003000c0700c0c1c0e08003920558840001c00d001c4041c101c40e140d0080b1110f206100c110011009002c01c1c0c1c1030401c20514000c94806500c10710507a007558119440004c02d81c416802000130100c03e445000c00607400078501d2444050005a560004200c0c1c003c0e1307005048044c040640322504120f03640210741060700d05440008041c1c00000b17036071620b00211425141154054810b0100b80701d801d82d942001d8031030450a55407072b103808006603118141101c1804800358018103640302c050040c1030842e4005801c21040240864443c000300c1c50010000d41c02030000500d5654402081c249a00280142c4100a5009d400005d16a4049611000c12441c05005805803a091a607541e08036559960a100e081014142440041c1d00714803400042c100c000650a100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 93733786 1250 93732536 93732557
    0xd03140f1207030507050309151308040b120105100504030b071101020c1e0303040b010510090e010b1b0706020c0402161403130f0503061305011e061e050d0b040201 72
    0x302015089201009040391041d002c102d07096034503010f001e07046843c0b410014a1810a41d200c0c03621000030007141c1c1700f42180d132404121140c114083d02d207401900150456113a548a5100d05200d91040081c0315122016500114003413402075060308403805180c07510ba1601d8a0356880c0c5a01c03200003007072002808148034a0f220b04450078001007985094500240c048400d072041c06001351045032614000540c403e204100018081c00c0c04181035420440f41c1c0f4101c5407070034000711140704240d040104a40c4d190400095142c1d080005881c4d6164400c100c0024540c9240300307965112407a205020040e44006451840b904246d801013081a41581c14105c00401607202c00509200d03503104040c05620005c0e400e0b0a10f070000d40044003510541024840240c1781c18002551000007a01c44880032048c205010300b0000254460650780380c5c18001e5000c410b070001c0740c41008001b00c2c4283c2d4030300f0110030f0700d182192090550031015140d00034803070309000d030704c0d619840310103240148120305000801c1403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 93735036 1250 93733786 93733807
    0x706110109210210051306020319020406020a0309050103020705151302030f0a03170103030906030b0612040b16050f0418090c090b180105030a0308061f03020d0b010903020d0314 78
    0x2e080b1032412081c102da424064074070400034030780414100594101454001804640320582e12030740c1480ba0401c1d00513031640c58403200c424624440300700317008001e07200003800194a43c021440c40002c501030b44030b0604441e5158015816072044540c006c0441d00600481d0b03201841000d0440d130400205400d1070800c1840340c1c081f81c581020714601c00e1a42d800a01c203902010750014020b440c0b04250140080c95500d165000b61212085005032400e050301d070664a0150b0715250705070b4084645030030180c0748904060400d1444070005444200c007904001800400540c0548106c81410540c82002850545005503042c0712080304002c001a842d250611100482c001c1040c16018001c42e05000429800d4002006041492103445030320342030110004001c503a901103554482c3c1c40d01800d080581e076a07001c0000d0034102e42d29102002c207442581d20b465109905030301800d40040c001c102009990314090040d1102206480700039800f08205e040140080d02c10303c1c01c0c00340110b0180c82c10341800318502 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 93736286 1250 93735036 93735053
    0x4050f0601120c21140106030e070e06041e0f050c03130305070c150906020106080607120b03010b030f0c040e1c050a030f0501031104050a05101208160c0503060c04080706110109 78
    0x2000310140e41c840c5c0f41031440700014190a8010291810200100860703510102d0301c4616174070a40030041c10500020f0043e840b42d400c200f02c4002c0201d42d41c1800c5040003420070043c40ca44074090030b130611300000100c1c0d002a80702100e01501c0000c0d02e02800c01640e5400703c402d070f0f120038009c48040b12044c0c000102a1486c0304200700300c2d400341c2c8610b29003a06200c0001d08465542d480f03081c5a071b0000c01400869600041c1034003809402c90004214030503102c01090241c0b41c0d05110310781610400158103498000803135041501541284e090155038114800305944201c1030310f54030044010b071454007407010f02800003000c8844aa08010481d0b50080e410b0b0350454a09034000c0d1078440c5040076010031841d061184a60200d61180200000e0030300707084510021046000d2006030039038030006401886a01c0058400340f00b00413130401c1700c4400519005100c1c484900ca09400303480b0300004240350035540025101a101d04400030080d09150010440c1d414094100b0040d1a55070f90030364001040482 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 93737536 1250 93736286 93736337
    0x2031b0a020306070c0804060503180703050c1905030304060e01020f0109030206100e10050631091407020c091b120403090b090f09061503041104050f0601120c 70
    0x90040c0480c48814014182031400003403400f801c0006124000b0000b503061800c0e54252006803070440e40300d50380c1c0009240c081c182500f07081131901c00d80000004209000520f1a122001699240030701800c0e41c071560340300ca4150194a5040d00280001e2009074070901d11004000414811900e4a050360074200b0708560f54a0001e03401a0081d03030800610000a25000c0300134000400da41c07059140240b007412054007280074030780c800c21000402d941c007100c88110420f9001d602a0390340c044010684071050155920b03203d808900740c200044125003450045000d84542c1c3d198000e0804204250704221380034000038621440140b0540510051504540182c06030030118411050789003800e0401620365105036000101d07000040007000d003a0b4840f000200c106a0080d14424404d0f141e4000007a41c0300c0c0644030401140401004000910801c08041c1e203a00c101507030300708815281c04100d810098801ca0300345000c1104c490f480e003041081913105403403540d400d00d415501c00000c20035042c001d2070038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 93738786 1250 93737536 93737587
    0xf02040c03021c05061008040506040201080a0e031602130b060406030b04090f0303020306010801090606170c0c0d0c140703080702060d0f0507090918020325030f0b040302061b190203 80
    0x840013008000d0030940640c6c00d40c0040c5040c1006d5a2419503100ca94a001c0100000e04000c44c50020a052031001e0f00720110040281c070a0740d4a580b8141d01c1c0380300c403885103031059100710b146107170389a99100d692140f582c15a0740074090a02c0e25091650660191001982d015009551242d890001c1041c0440f1030180c2c07803180ea800340e9641031041c0014040001a004911054900141005003641000341c000400c0c04045607c0655955604155000d004241a2170194003c05a14084040e030024030604110711800d107002480800140caa551000e042c000102158030030000e140c0545448400b03401980500e407800304410040d1101d000c1500c4059840c1e01c0403c02414052042c042c0e14003452034407048030346403031902c01e6494001035a10140b81f128043c11901b5451800a040ca02c07170402400b954200c0c0d04c80d0a08203039441c2c001c0168908403810780050048201003100c82030102c07001015884460321040c102600340d1000410226243c80c0c1c5415031008010f488a01b505015440c40309000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 93740036 1250 93738786 93738791
    0x6040b040501030e0c0310090503091810090203100501201002091806130507090b0708040f060f020a08160c12120212030a0c05090904060b01020f01090f02040c03021c 73
    0x5071900140a4403500002d0b00d40c1d13a04038010039411905c001509440c02c1c42d418802251400d19401c00504502c071f805002c50704401d19494180080c035000e10114001e140305400103001076501d62a0600301c0c0800d903443c1501c411849001c119562017424000d501401403140d0840204407441c60306d00d082101c0e64602501500840c5100c01c9142003500380c800d6445040e11008540380940003e0960042c1136070420070565158003040035103114541800c00303000e0324120a65524070f94140f14445420500c12800348031810000070421512682a004000c0055002010a50207940c2d500143d500442d1221411101000301c1c88085030004544a006110034900540555980c2c2800078a541410141e482994810000520107d0000088a038410100900000c11480101013100d040c81101907040d482101c580a00040c042554000c1142c07200907000c81d540101c0c41031409081e608248005080204540604e00141c2402e0b0050301c0016001e1500502c1c0a03100d0006c05810a402002c4460899 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 93741286 1250 93740036 93740039
    0x503180610081009050709020708070503030901091e02300304090204080d1b0b0712020d050906060907090905061906090609060e1c050c0604171507020606090405070506040b04 77
    0x81d00380620f0002c9003081c24107200004650700d0b2140c3d50b0000340b060034001c035400a980000c0c40103110070303580036952150a0302d0307590500c0c8505902030011000300307a0710308172807224010b50381e1240c1031109403099005c4c10100c42440070401c50241080e0240c1202211000c00e81140074200c400d00040003e1700043c907005883c1c50420b020382d4a0094401c001c9814400300702d05078110038681c218401c0c8025409502e5204558074410205d801032204c94107c980a030012030856650401034000c54440d2280d2400c840c15a502d00040011950301a40d0050108603584805d2003034000541006a104102425a152035060000303400fa006c0816440200043e220003000e200740c0c1c0d0301c50b4504000b00000e150017450341a81c8000a0800760b01ca0341d6400000c0241010001000001c3c0130301e00b2043c0c0d00034446501e4a0b5a004a40d004500c0c07690500181d01504518940c440c00c24140113004214907070080102e980c68009002c131240001c0c10075038a40c0b007510390000e42d6958040c000c04c0036100c1c801000303854a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 93742536 1250 93741286 93741299
    0x10605040611070506042c04031214040b06010f110a030201091403040f06050705160b090109060804080d090f06090501140a021204110a050d0b090d0c030e010503180610 74
    0x807541c402d03031006600291000c00c6156100000d66050b280203400f25120740070120400054142e4105000c0c030010400010001455003102c2c13030010400e50f12005000680008444034144103046400500d8070044c0e00104002e07511840c0c800c0b161601504249514444e80c1c1001491b01802000440050f9160f6140104000e41c1401e010342018a440c02107041c2030511041132001c4516000780d000700315000c80c90006100d010021a80946401c00380c144000f42c4401401c010f542c05034078207601007007010b0310005601c2d110381c1e06248510342291415007480c0c01080c80320003601c4019019036006060000e02c40128201d4424160304500c1403000050514101c084018901801030001004900c14403105a001b80c0c2090344580c45030b07100d000034800301d41c80313070002d41e0030030f05508016001901c0000041c204100c800185005280010490f10112103103241202c0d200d00809000b00001c06e1100c140b429540180083c40d007000c1060410b0a0b9035996082140c41c0c07401c102d8a00c1042c400606003000b60 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 93743786 1250 93742536 93742547
    0x2120c0414010b0702040207170705070e090a0201140a030e06090a030906050901020307030f02030409020c0609070b0c030406080705300106050301060512100305240f130b090106030b0106050406 85
    0x2440d000800c000c490b602d0b21690401d280100080a40204c0d00002c20208004ea1416080350b080c10304080a500d0703488034108240d548245001e2604101c11030408030780741d0070001840071015035050791101c01d42d040024281600382c0081c2c000070281034941c000034a000d0b4040c00800c1c4216481c0c030083c0000c5aa90500034421120307603106a042c090100281e4550ba6404411503039081e41500386804039448100c0304918510680c0c1c07100610a1000c90708103150040480c04a0140400c502218141d68a54a00f0341492144148036806648200010824203000d40061a44010b40c0e051060a205c0030380070740ca40d0b070303030000c0040c140c14952650304046e0941a074149901501551914508660400802078030700d100c1c22a0548503d9440d2002a0920302c003c00168040c40c2e0150944450a10342668482c6204c1c44c800f61454460405002601c08002c0c2c80341d40c0d204000c801508803c441c5c040d180e07a028500007400d420025501c4610100200304200d00d070718004c040b0380d0364a070303529441c10000410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 93745036 1250 93743786 93743801
    0x18050601050405010807051317070f0807080c01120b06070807060516120b0d1209060f03090201080105090a0e0a05100c0203030f04120c0b07030b0f040b010818030702120c04 76
    0x40c00703814001401141d0b03004003035544c0292642030544da502c45d01032101944800b154000e5084824042d05130040c0c0e02d003c90248110346842d0804400e07140c07201d03416030b1164083d01130200b80381e001d92180c106541c0708414a204002801200182407030b5a500030802943c02240c09503800d850019605042001c01d01c6a160f100c88020010406090014001407071030780d00081903c01c04d601c0c0c1703a02c41100e5940300c0e400807046c0c1d03003c0d803042c14480e140240a0a02d0f0074903c100b0000c1820b441010124501070700507100504d50503950300306540e0824040003440380d005003a1204517541c401040000c0e950801002034507034083c070010724105014241045c162403640c1280001c6401c1482440350511060072200d81107540010281d0000c60007010480e2814070420015048245520030310103d650544d0000d100c5003000d40360500b85c0710b0305105100654040c400d5480c001035510001030001075010b18007030200b03000281901e1400d0410b40004007200700e41c03080f00044e90000c0303450500502d040d202c1c034036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 93746286 1250 93745036 93745039
    0x4b010801090c03120e03061f0e01080a06050703020903030c16050a0503060a0504030c120c0b160f0c02010203090411130905010305030a0807050d050f060310110403030c1a01180506 79
    0x2108540d60710110046650310005004d0300444201070040d50103107041d10355440006c0c0032590a443d15004040c101d0110707400c1080202a09880401d001811914a5060718030380c0f002048486040d03581c010080200400d41400c0513800d2254207990359061001f005c82910341c034018030a8603046d1000d4101c04a10354415840360400b04001c00903a01e0100b81690700800030b46000420350b0f10b508003902c1c2c804a8000040410b00380642c43c00080350492100d1a1040c007415080600c0c1d030710040d4a41304403182d4181d65000c10009c0202c484503902c16055485054070603c1070b20f080405140204060310b880d003c91390382c1620040f030340c10b10f01001001280000c021900c401d000c25491074032060340700e01c1201d04260400101c0000070700501d0043c0300715203018080d0002000349240010110f0300100054070390612034041d82220340880c8029014000050b803441e04103d1a0518580d029540703100d00f21000c8030603100f9130340c4420003403980700c01c0113000340180840b22a210808901440c120b420042c10345 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 93747536 1250 93746286 93746291
    0x110f01020c070506030408040b04030c031502180d050c03011e050c04151b12050a0f0c031d130e06040c080f030304060902060705120a0e01080f4b010801 67
    0x4281104000b80140840b02c05a030010b07640d0301c0d6401d0080c1c0c503104a81200f4440a000103000003085052004074003204d009075031020301030110248a41c10b038030035a80d05031514000003614100500c2c24174100041c4034460802c58402c1d107140d00100317003550314039543c02025a1069500c03807100929401000e5001c0c00c030034540380c80c6c541480e4a01c424109804944401c21000d11112801d2214400303072007030043c2d0800d4040007070540140d4002c14036030204481200203010000140c8802e03015946c0c0322046a8113071922803001c0c84d268148024080c014403415401400480c1c4552007100038414007208100c0f6201600652405042c07038901e2010325840580542e01062091000c0c00340407054a4116900c500c0c08101c0102c070f03000090aa004081c4c1c003511a02030300c2d0940c2000c0c00d180300101546407151f11140e81c02c0000790f00660704001d085034000c400d04443d400040e50b0300c0c40924a00c8041c440f101e8a512440c0c401001900968480c05441048103817240990b0102c10a6182c1706004000c41d100a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 93748786 1250 93747536 93747547
    0xb030f0a0b09240114040b0a09020a0201020d060806010503150106090902030403051b1005060f03070e25050a0201152301140a03020318030703020604111c03110f0102 73
    0x10280d44165892000c1c04000c2500d02140c803102050155820510400300c071002d80003000b48601c10100828821548015a5075250103c0d601302405008182c01d0004c0100003564a4003000001030740c4060346910465500b0041c0e03402415041c030400c8081c2c4000c40c01015036604007410306141444904d541c281100c1110010001d0701e41c0450907800703503103504001580381d40722480c0560700780c0500c28908092507540c6ca90181d4030100010180403500c4050300502c1780d40c807010103001050700c415508a8058104a00c00c0c00281c12004a20b0303002107041c001c982c2400401c034130100e400341c00500c00000103080002c0030310300568240202201c50b005212840c0007549400d500001520030301c01304800078158030042d101d1581c01228459402030425082507a02c1606540044c003d60088500c0c00c0d000b80b5251280100400000666204075490b0700148065207894035405451081e034045168000b03d03c103010384012001444401c0c3c924402d444a09000781c0c1c003150b850070710000300001b00c03c2d81e205100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 93750036 1250 93748786 93748813
    0x1803060a05100312050403140c031b030d08100e010605040612051501120e0607030b03011a0d08031306020403030c1e0b06120309040207080406080708040c15020a05100c02010b03 78
    0x280c0b0202d80d44aa480c030a10503030b40d1000d82e2940a00e038005001d000300c041002034410f102103240ea588400440a0f43c4060411b590710210014080d60060307016440003d00200d03003030145007020740145905c1c5803503003840d50341c0030903191141c170076005080010400300e800c000582d000807210340f2a200c1420248410328002044840710b15040d02c03500d040112000c40300c0001c0c1210b500010100180c0c2040c0c80d8281b614840141c01b42c0406698940298600030002915001d1011928440c0c68010240000314103203440e0505d1940020b4035a21000e28009021030006503980300a10046100c1d84480551201d42e080c03210b24284410aa111a11059020180000c44040e151544100c0442d03031560f11400b8034504a10718042c219060750014070019810003800402e00c080c00480740c06550320151940c855508480c03501c0181c0b0000e080c24800402030041c005086980c0784115054030450f2400d02e0242c942030f2030f104580b202240900d075120444908a9420f010b0414800b0058008004000b800e91 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 93751286 1250 93750036 93750061
    0x106090315020f0d24060c0507050409050f0109050a0b0109090b040b0c070c08070f0b0a0203030103030e040b03101d010c02030304020907360608090316080f1803060a05 74
    0x210815001640000da5409882883d41528039804140d0020403044042404600c81c0301c98084816030f801003940b00c00103420b4400c03500c41184c194048090302000d4036003010701000d8140403100325500c2c040d00e001070b04035040910425100c0c0d4064001810300d4034035410001c106d000181c001c038100c0760802285002103075040030038580050b4805100c103955514000380521170301510000402c1600058030010742d0080c00240c0000b0340d00c0c20380b04084900c5c2e4440340c0c800148a40502d4401680091004002090090300c00c00c80c944809040454518908800241003000b0307081c40b011482d40d034448070b5506541501d84520000800d00080203000881c41020b5601c0c08000e000034822520003000031992031054007100300ca002c0034404004021b403200010350f180450034940c060240c100320030000d01507120780c02c81402810b10002851404c201d4444613424414202402c0d50031800811481c0e81c1010103034028080c0c881180d01c500e0008102c00c1c00c25040c0340003d000640b80e98140f4052203042001d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 93752536 1250 93751286 93751313
    0x5030f130b0f062d1e180c0d020a02030c070803130b0d02070602040308031f0b0d020307140301060314011a0f0a030b03030d060509070f050301140109080d0509030601060903 76
    0x50107030b40c1d89503941c0c0c0001403003907040042525031805508907401401001000c0c100c40b0301c1040ba04070030801507000c22801c00c0e1045100f07030b5501c0b01080d4110741701c2c018030344001900701c400c450104d403030038032441e84500c203a92001e00051300503031001542d0400c02c4020b000b41d2000c1c100b040040c6103020020b101c040c1943c541400341c0c00039400009017060340808140c1c101d8194560080d0155126652410400306940080f203604460701b5a001110409403203104059054071480c0ea0600e08144040d140d850094000510306801c2c003d40600d4000407a120700f018600030b090039030380440d032004011024801c0c4241a48030850030402c59800c9034042c030700e54094821080d035240d121910303101c481000310080c0000038040c1d5054000003031541c070140c1041e0480010340754143c41e810200d0315560360491f000b01c120200c441c00990f0601c010f001c83c02c014510400c500c00140742c020440c5840342e44141c24000800e01d501e0100c2c00c001510a09400d092000900404181c02c044204510790385489200c02c152 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 93753786 1250 93752536 93752551
    0x9060e030f060a0209040b0a0303091703040e16050702120619020c0c15070602210c1614280314030403021903140309070302040605040b0109050d0c08030a05030f130b 73
    0x105c0c8409050b2113542c09100c000800421203980c059807401c01800380d0005020b40350858010440201003c0030000484080740e41022062031540e951500003000c180c030b2000b0680412904100c1803004d07035502c51424428ac0440c002500c01402d25010581c210121413030b000710030714014090240c8018000c030350403c0c0c4110030b8600401203030680001801921482200030f1609101240320101c00c1159043386250b01c0c2c9510b1074141c01d44a990000c030140c020180890f50a0316524140350018420007100c06040340004212400304822001c807915010b13100022241c071200c02100c8109040e48580301c1401100090000c918505141d00c0c002c2d00c0d440140c50324428610040640070405220b00345c403110b2035488403540c80d10307401c001c107100b6140e000034402644614145000401c20746031612070400e4002058442c020b8440c500781c24855101500321082d86c840142a6002504a005100500c101074041d501c242d80da144c0340d00c0030300c00c24001602c540a6010040310003070008038034407a001d410088 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 93755036 1250 93753786 93753791
    0x1140304030216080c01030f0b0607060f060b07050307050d03060609061103040b07030f030b010f0e131d03130b0a08010b0d0e07080102040905010e040206040e18010c09060e030f060a 80
    0xd4904050b443c1038098030004082041d1450000360484d40410350025801090381d0504c0050b00d0310a4880c21755051007280d1782d006000700038800002d4255840080e24103807020001c100c9035a00d034003030f03542a04603080940d0a60000101d82c02000020f010304100305000f81400c00000381409c0000380201c106004900500c00c00e181c0c16003c00c45c04006450080186a10141e5951100d1070010881810164000d01007030410400710702e25800380800c580c2c804200e03514101e02044881c100842400d4610803203091a80e5078081c094081c559045984605c01c40100955850b50701a82c404032500182c0e000403040802030100d403805a40c1f00888a046445003000e850700c600d0f1090a1100800d80030741c00765140d204189001801c6171064002d0011501620410415a030340c802032918000d50480c0d009501c080c04000a0040b0203c0d1450290441d942980f1380d0111070905800c0380c01c44005200e42004210000300c00c000c075135404400c01508460503009041402c0c0dd146000d543c4620140455030000c0c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 93756286 1250 93755036 93755041
    0x30f021314060432030a0c050108070801060e150904050c0301080d0504120b1e09010e0115031104020a0210140f01090b09070e0d05010906150b12010501050711030102070b0702060702010b011403 85
    0x28000409070760030700090a840c1b0780314991074200d80c80c007210301c1850301080715040014865405851003034105c5100f500c0d0303100c82c1c07040f200070402d54400c400805281d100043c40665159126842010720804110131076550f00e5051285443c03a110075215180100a010403060288589840a004da19030b40140706401d140c07100040582e0b0445642141031041080b41c0401c422204150000302c84024010000c1181310340b16003506109034039a00002e41803000410000e02c99040560082070259060710544107141c3c04001a041900c0c402c0e020300300c00d034000c4414041d0701030000040b10700405a80e4402c02c10b2951200c04100d803002d00800c11400e102040040200a841c2e04a60815131503019000b04072034122403603c5e030000c00744180304442e00320b007a25002c605011403000b00e031400c800c81c0071000b045070b107000011a140ea00c583c0301112540c1040c2c0b240c5020751000d0000d04001071080200c0b402919240a0091800200a05035400c680c184181c00301266003140122a500340041c160a40e40c1e0f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 93757536 1250 93756286 93756359
    0x90e0307050c01140c011811040e0a08030702030c100c030b0406121b050d03020a060b03030a140a03110a030903031406130905120c160b120105040b01030f0213140604 73
    0x24040d08080b02459400c000031840300c47c00e110f80c251003141c8180750070158001c10800b884200e030892446500c0707650200484c032b008503901d00007640c0c4c03124161048038078001c0c0203055075050401407003491040644520000900c241c15025030200d40c103064504201031841d10500103814001144050040c041140300380c140780c6201044180a010054202c50118181c0c1c60000e65508456000ba500c091415842505d035150102c12268031480f240d403000e01c2d00307515408580040d40800801000d050b40c03412010640c40079000546404103c41d28000303080462401c0c0a020384906a400320094414001000344c540d07200e010100c07480d000640300289d035949030b242c07051501071140d0041412a4010809040d000030010300f50381c024400c084550f40c115602e44180a403402201001051004081c00600440c10b00ba0302103454080149404a80083d10345031400899000d408113482d070b00c03030040041c04904503030309000030904004d4607080d2405141c40f21a9044689009140881d9a411141001c12 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 93758786 1250 93757536 93757577
    0xe0d0201020c0603070e130501060f1107050a171009020303180103110309031b0105040203060a0c020a020d030906020c010203070f0206070314030f0406051e06060a0302040b0310090e0307050c01 85
    0x410000d0b1800e076a908003610050710000310481e4031b03407040b1000114907030680c2ca28040c4604948080d00c070303580000f0030381509864032060088800e806100b505000141941d40c03c10b0310000700800201c0560034a041aa5541084807141c601c0e408541410400c90042e140082100c00b91300e05244002280c02070807004030003500d0030055074801624041309001a11602100a0004001c40d030160540810350074141800d80780304842c06940364000d800011805025600031222035034503441a101c0010065002440b480c001407800d400040d59424240102030301000154a8808240000c42c2400c0301c42e41c0359101e007821044000c5c0601400306041c802c042c081d00d000d01342a482c10340999101e240c105081c801301801143d0070340e401411b0002240b00a08910541c00d0824801002d0b154950f40304c0042c03105507400300089000300340c3d003080009035415a0502840c01551090180c140707291a19030b5990564072050001e2000d5042003205200060002031041941002800c2451031081c90803200100f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 93760036 1250 93758786 93758803
    0x30305240f100e0406330c110105040306020a0c02090c12041709120606040c14031b0906040306050108070609061e020307060204080102090a1410050702041506230a0e0d020102 77
    0x10440d04116011030800d480c0c2c241c00f9200003a860b94459140712255042d0740614014071b81c030010540f01204000840d41c00c111070301c03c0d084d040c100740d40747c680c0e60340d42e4908a90000700440001061102544114540182c45503040118400c0c620304007550149a600000c80141004101c101d9070810a01c0c0c00882c4800c0d90f9009400811201c0034116040d05c05d9100c00045039400e2059240c2a440d8007454007441c10341c1e00034a010075000c0d045658980500c0c4001d072020614a81e6448103101000315592030317600602c0554820040800c4c0c070f500d040c900720f10b82601500514103002048200b40141e9a1002160a0481c96040744140c0389030151400e0f810351281c2d4078080c041c0b900015000c91015015001441c042400b941c03600c4083e507071000300604c645401810568030069402c0c0a0400358440c50240c44c203240000c00c00546031098a20381034401030954030000125010300c080780314a002010900f45041d40d04030406142004a1500034808940710392102d2044448489080079a48204031110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 93761286 1250 93760036 93760039
    0x160302160b010f0603050a02031909030309150f0b06093601061d01030b06040b0d0617010504030f0f08010509040302240a0e010e1009050316030305240f100e 69
    0xa0032541c446459440c28049030140f107000c28104001f00c2c80c448020b1003200d229042e414503021004000c4d81040307001c0c05c2c18010940400d603c0d0211035010070740749281d240082d5050f10300054130381d105e07814a00540b400c90f83d000e4452441400340c66600e0300c44140405040b816403c42040700018130801c41f421005511901c0d60079081c110011038843d400444050110f1880700701000c6440000300118241d0f500003014980000c3c0034003080101c06200400341521050260012030400c1d118515200c041c4550030603815241e44840602c818190005850080008645400100c8000c607001c080c081302810701c00d8502a03a000400901898800d200c0400005c904030301550030030701c82d0408040320030025591111903a1801c130b0500d140d02c005100d0050301c1700c1c0d614042c001e0020b060929200800052500795454003080100e1400c414405480401c000d1090728001003e0902c80307a00109000d2000a022004000a007030801c1030395006a9580200f400300d90700c100c0000555808c540f038070b0f031104031306 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 93762536 1250 93761286 93761303
    0x90f0509180a06020706140403090905090c04020c0705090f0c09131e1407030e07090203040c031203091505070e0d03030b0d050c030105070f05030411030703020622060816030216 78
    0x10002c11a15800500301c441c0186410b000d003040c3c2c0d44207c0303400d50040e42c0082c04915602801c128003607c036001550300c141c82105a0f40a4900000803409070b234410040302d03a403604a880103100520707000c40c0310390308601c1d02c142030501c91400d1007001c07400340300d052500e52289400c0e121150f160f020070703002020480c09028881c41a0740d140703019600030b401c030000e02c2011000f140d0000b6180c1e82c4288210090300346040004d0a002d860b10101c1c0c4000d60001c2e00c26503040c11010408000701c2c3c05406085080515075800040c00f030f01c1800c01c520445840703480600b0683c2824180100076a0140c14580883c00071038070318040100901d003e4000b130800b400101e8101c036852185000340103011440e5403100c0d6051f0000e200c00e0343c417500c0403580143c29141e5000844c00a102040c0400c0c0c5000c5002e400c1d00c1d0103400c03140c460781c8980008000745c0120910081103503000b44d540500c0c00c030001806009210300d040142403070901c0d1072520190b07825407850b03100b01075010035100300d40c0025502e6080002c0d04506403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 93763786 1250 93762536 93762553
    0x4030605250f08270313080316230706020709051501050406120912030e060901020c0a0318030501060906050f03120301060509040906050106020f2506030c0210060b04060f090f050918 80
    0x3c01780c8982010010000402c0360f40000a03c1c0c100100441d1032410055603100c034414810780c2c404040b041601d0076409044c070700d065034030003030b010801101028213205c0c0c00030b2800c07602d80500d13a01a83d0b030003440084803052000c141c0d00c075640c00c0400d48003503075910f040004441c07104443c0368004202c0300c1c4001e002c002d0b0500100c500d158166204461034102e000c1610801e9885108403401d0303108400c0101203e034080d20040020a00c120058441380b1324012002d138049540b03444060035541990064041195210340c100038074581445060303d9031100380c0c040e028041c000c03642c414190105100d00c406100000450040c3c075038582d400030480540c07028080103507503102d00c002540e850308042104840d00c01d100d611042c5d00c607010b42501070014940d070791200311420a1000c4024005079402601584142c40c224004035445001c0d14010784104900e064031540313800d90007842c6030000000e04c0103210040505002c1400e4001c0d00000380c0300242d0707440305151103408040481100d40a544615806903484 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 93765036 1250 93763786 93763861
    0xa020d0605010f0b0403081605120d0501060e03061e09070b030c090103140c070204150e090d0906030b09040f0c0f0e0f0105010807020615030c030304030605250f08 72
    0x741d8140c8000b80c0303162184684551540070700340b060340000f8004d0101804a80c10f01c0c0450640000c017127110364161001035403804c620090a42003540401d00700c9495900601040f580a06c0c03504c500e0740304400400c03003400c250001590000000990000070307000341001034600e0710100005c9000b00310b0b848003180d40e4504141040b50380d070043d04400340002d04081800c0c4c1780036980d840c014001d4040e0207403a071404810358200002085104151919950045000a445030784064076520824580c0d01904002821003002000301116400c8807080c0342c50030321071000d0741d00c42d0355030580e000d0340c405c0101c1c000c1e0842d414002080c0c8165800f00c0710502c112034010440320440380101e40250400c000c41d084070b980350300041d20f854208444080c01a4040740c0045c044165650550800d03d40190070766948021480109003158030580042e85e0858681c002d000b60404015a05501c2e0303d4042c080010001258100500d103109091000e8200200040821010200f9480303003c0c1e0050003001c0000c04240910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 93766286 1250 93765036 93765041
    0x150a03050f060103090206121f060c02040c080907030312110a050c10090b22020402040b09030618070302060d0e0d0903060b0a06051b03070605040309050306090c010203030406020307020a020d06 85
    0x2100841c1440700c020106410354000c0c0039280010360700900403420617103444403810207035000424211490200e02c20001c2504401070000000d0701c41940c6030074108010b40148410b85015540e62410480d07204104840810041151000e41e40c3c10300d0007038011800d04042038094003a21030309000b01d2000055521201e6081070050a5071803c10342995040700112140320100d6074204005440c1903007541c00110381103180c00e00841c07154081c1d806c5030f040c1107003a004501285c03c13981003030112101c00180c0707110a01e420080b280d80201140414500740b10304070072442c0c580c006448001e008074004100c01d07a00002981052000000d50000c9a942030307800c0c103008010b15010b02c0195242450701d804030215042071214078064035401d031103481c41e143c0300b1130fa02e81c14030780c00902c0c00126020500c0440001b410130301403d401240640e40d0310200d40c1c281010141031a0f40030b071403030703805a0000d18660070998012058940c000c0d000300d00180c0301d903a03041d07080e0708000c10840001c1d40100c0721105d034410007000b40d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 93767536 1250 93766286 93766291
    0x3021c0c08010803070c060c1e0809120a020a03080a050c0f03040504060b130515040f1205010b1e09130b0708070f0c02010903080904062c0604020901050304030e150a0305 75
    0xd41e18020140d9a50300d000751280300d00340000c0c04140c1c024105016543c0645d0f4560744280c4201b1206100c103800038400318841c0c4400c44100c1d090140040d5054503498560042d41040000802900d06a1a1540010382c1c40c0c11600c4010f101e0040807500304035050254060320480904502a207845190401079261030703034820b015081c451444d010000c54540300d4a420385100386c4150641e020905c1c00d16040040d209000304005048010030070010801007092031b08280241410b1140186a45461401c1c0b800e42e04c000c44000c1c0104c29000701500d40f04601c10050034804001e5407194402d45404245000d01085050081e0590100070280611182d100ca43e03144a60b04039540d14111000741401110603d404440203030029000381011f00100e051400180801b60707008100040d01135840c210940d00f09410351605603840c1c0c0c0b25070a01d0401810040c840d50040e011031f030840c508074402c40040c010b400040c00181c100501c071044058035880300e04118018892652241d82c4400b01c844c00100a01000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 93768786 1250 93767536 93767561
    0x1d0d0210050105011b052e0b0103020304031209020402120f04030206070201111b0309040e1005060904020a030f050705090a06050109080304050303070b07021f052706060607020103021c 81
    0x6100c4403080d0042244101c9050382c10503550a00007041c65108280d2440043d00240e6140c0140c00b103010101070b1000520f1b40406001c05105501e0a40d20b80b050200d84640307820038145030041041000013030b402101d0a2a4441361040080c0c0007000380045070090082080d0008180c50070340910540c04250a003d600c154420740c210b0701640d4030076000701c0c2680e401c000800103c4000740010f4000314024004458840760217004c817030034105401c0000702554615160110340b0341042c4185695603039680103032513100304151002e1007642425400f181054000b4400504140c0e031050014007003042c1880b42000610740107010f00001d080001101d0018200e82c400c050111340701420001f841c810100c00c2e81d00319a00113014608004054a405900003c003c1020301103004529007040301301203100d00703090f5008000000084510301070f415022500c00c201c00003203500000030500d43c2030100000300f1507408242540d50a4a510562005801074003601c0300c0c050080b0f110301c01c0c0900502c02c2c0d5002005001e903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 93770036 1250 93768786 93768793
    0x1b0703030b09091b061c050c0403050f2e14010b0904060608090c06030711030406020313080a051f0f090609050c06030405030d11070209041218060801090f1d0d02 71
    0x7210024196a0100d02c041c0d1410900804030913600c61070000041e11000c2d0070300407200c00c02801d603142502103890482e0405180304001c2014002d0110412003078107000140c100a04a942003260981c2a40c0c140034000340010502040580510090307410034140c01d042101d441301c117961610205450b42e0441380e00540110710740b140000f903052084c918180a50811005800a08403120038001580d00080049082c0071101c0c0b040b48d1006420402040109030580c0036646449000d103403169104111b41c40104190b002d0030540703012940102d800c2c0b810403101c02100c4000740b44010008050954180c1c4440031900c1c1503000400c0c00203a802c43d0000034400c40554031044448010001d13940800e0307902074119402400340c01140502607003c031055140c110310705c41c01d010159000070010075084800f200d101c00f038500c01411058110b014035602d40204800da24010f41817400080c141c10051055001054481c10800c2c1a80c08551007030150034000d010310b00b01800340ca0051942c408520004000521 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 93771286 1250 93770036 93770041
    0x2060f0a1112070219080f0306030f1009050d0309081b0f010f0b030705060a120903050d020c01020c0f1c080c0c030c0a1b030c1205160f06080a0516081b0703030b09 72
    0x340c1724406003455682c40a0a0303420800c9004185d00700d0780000b441d1641504c1003440500c140d546c1004011000300c4551030104e841412071030b01c541422094811182414200801d50001940c64020359100704450710550104055003460503240c48070b0b100103042c465107803199860501c0407a401c0460801c030700f503003110100c1d59580280106482104d1808000609540f40c4040c1030300b290b00b040d1380a0780030303181c06418100c051a003c400c0742d00156503042c49030343c00249031442603018000d640b21102d000002d0040d203000070389030402054980c40140e0411110200151500841c84240c4803180480021684c480b141681116600c070001d03513060b120100c0354801103840141d0141c1000070b483d071140c803030b0105914001280f9004d501903101258130b40500341c1607182c2540d1301100741c0c00620a401d07084a0701860f118026081100203082c18031a1418041000f000355a200700e9800103180c02e140400d2299580c1a0000c003d0418049801140c10300003802030a040c1c0c150012200e14000300c840b403180340c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 93772536 1250 93771286 93771313
    0x10020703031e0503011e09050f091903050f09030f240108161503140a060f050111061302060d090809041d06060105090a05030307050f01140702060f0a11120702 70
    0x402c04500c07002070410001071280c800500b041c0740801b015100001d0103580c80d12000d0050742c03822a2915010039101e420441c5000040180303569003410480c5040c011015510006c25504c1101b0340f00400107800160744409803020800e89201a00300416a00d40082c001e800d1292404801c200c2c400f0b64001000121701c2c3d1501044000104038100000c00f000c501c2d101011000718001e109201c00e1681d40d1401001001e01042264447d0008110010b5943d082c880d51b9070006101360407060420841c00c00b15040e0306000900c26800480001c1c0300e200070001c03480014900c2c440c80155100180c14a1403c0003000200c0e8060845480c0032034042c0b154a40001880f010320b0030b00035407181c283c1e001c41b0203e5101c0d4010002441c80c07100c00340c000c804240d01c48000c00d00c0c40d481200100c0c0c86501c9100000c82c00802840f03450700c400f004800342d00f018101110002e6071624050b00d007443d450199008500070120592100b010801c0c0242a2074846d59011203071018407100301c4050025005000c00720648 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 93773786 1250 93772536 93772577
    0x1170708010515090714030f1005060a090302040e03070809060306150d15060e0d150609060e0105150306030a0602090301020706050103060507140f040b0c0115120c15090902181002070303 82
    0x10b188024694112340c0d4030b60744031001d9000030307040c00c01c10002d5210204841d1102401014086542e4903400f0849180d803042c402140c0c2203007080d00032900144816400100c0310070031604000021103120f0344a45440700050400902c424414401c40300010300c20300360912903000400380b20084140b60700703115600c0101b80c814841e2010701645c0b1600040603d00010040a14a1946004041d0000f4015110450b40c1c080340c1d00d0b600402070b550f041800400061400c0000e180142d0041000c25085d07041100119541d0741c01c038040205200d80204050100303032130940c152030700702c0c1d0480010321965960341010001003005888810006100c1d49802140c505010f045031414a0a000302e94601480c8c21101038007500300c1003114200e075407a0107540c80f01140304505a0080d100b0510311841ca42400d261010900b2141d6200c001903400ca482c219050700d41010103a411946902000340c0d45040d541042c50085071811081d0740e00c41280c8005008030b076400118042640e10030707142c1400000f110340300c1104c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 93775036 1250 93773786 93773807
    0x605060406060f083c06030d0f0f0c0602070b071d0f010309170a0e1207060c020913060e011a060405091308070c0602060406060617011707080105150907 67
    0xc03e21080710110458450b0007801ea0200060b14181c5103000003074000d444040000110070002c1c4d8403007580310442c40c950203010384c0200c021001402c030000d00c0c140103000301107400040820f101d26100005003103406100041171079980058119650b44e094501024801c4050310742c1c0c2e000816038000c800c0b00d5148411100c5071440001c082c1c840d000d90450045000d88040301c0201c5070895070f1071501c103000c11400d0150030000625204d03070001e003c0c43c1040c4041c4030410b400032016136004403810840c803034205148004517501a240c800740f076951440d08642c07a03c50b044000703061600c1c01040c14580034041d407082000700e1001403240c842c45401d004000080c029409141e40c040d0802d0b000c12101d01c540100800c42c42e101d401402d04100317040d15000ea01004aa000c44090b8100c1c60400c0100b019501c01e41000d00b4031802c0c400c0385151908034401410105005180c40040e6041410745203060801000009224283c003e0100d85003004052107442d20103403142d405082402d000c030b00b0250140214a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 93776286 1250 93775036 93775049
    0x51005060303160b07030e1b120d080714070210090510090b12040f020a230d030e0d1704120c050904020303191709060711190204090204020d06120605060406 69
    0x40c443c4940e1a2800688400341a0106040c1d0303405290414a4043c005114400e1018190030a81501c0c9814003180b6030f00c0412210781c5810444001343d0042c1c100d0340313142d0010303c1e52402410408816a0015444c8a40b49001c0e501c040d1000c611120180e1081408050b5030f002d8412002d602142d60f0107903290759041c0241e070b05604050100c4a5220300c54810181d00030b018008014048502d0340124595801d250000000c00c61f0311400031140c00f49c0d07aa12501c20305420b8491507040c03c42920000c00800c803d410092044462490020034440e2080143d460722040341344071a9101d9940d40082d4202600000844669074010b100040602d800c004c03151203943c02030b025600e0901e080c103442c1da40008184159007030060701c1c1707041503c092694410f5440f400c4090300600650601580140c4030039171a100401465201d429401450202d101030808440e6041d2030100c3c61030344510010f80030380201c01c420341c8958a00203000985c96202040b0300440c034021841044551502070500040e1a01c174020003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 93777536 1250 93776286 93776317
    0x121051005030637090c03050606011e0e15030106021e03070c030b0c040b030a020301030b1003020a0b070309031505011a3a0c030c02150603060601050307021207051005060303 77
    0x142e0124109103510084822014400425a001d44d0104011039012440588803290440800e008002c000c12001d50000400d00f02600d085c0000b40528404542d0441c2e2001046640c01400001e5210400c102300f4420074180c00a40713a684036078000b0340d41c00550181201841000c200c80c0100300707021044401983e00300c04042296410b40e21005d45d01c05001c3c0a5952081041000240340c60f0800d004d10300400d0042c00c0584d0f01d51550074944200d21001c1d0048410740400c10041006a84211002d000c843c016203500752180ca40d802d056541c0c05440d4405070034003000d02d1342d80140d0300499220714180c0300e2000703804410440402c10b41d20280211400c20150810721000706001c2200340b849185083c04d505d0340302040061140c0c8103400d8403580210800440e8070303250070003075054050002d1040ea200b60350084296107410310000780d54210251040e81401070000115600501c02c0c440803060044035407400e5a03440d031615140d80d8812a130070000e6072491900010440c14607011080f034070001c0510103039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 93778786 1250 93777536 93777571
    0x20306100c260c1002070b0105090f0f0603030702120106170a030f1d030d030c0306050f0307170c15040305060c03010509041103031e130f03030c1101210510050306 72
    0x8a0200c1c2c98404001c0720000041c85000381e48241000755103450081428056194101850440c40c076600c107800091151000c1000c005440c2840e41155a011a500410f07486c40c0d100c8001180c110b00c50745002a401c8550030003800480c04054100c0c1d000c030399a4012081e1161020640103449400b4940c008002580e0f00b0f540e040054800c0c074044000012307814542010b481e006001902d01307a051a50a004030752a00d03101c1d07100c00d07094401d110040078180c4c1e20250101d80080040d031600c0d070f280030780303402c43e88004400301038600c04201c000c840000180070390000c0c41c1c170800b0002c1c81e9000f500c4101d070644900000601420782260a0780c1c12540003901654407031f00c50760755507040350200045071501031000b8030155040d141a650100c0c0e80c1c42c03d14811079074075800c03048203c550700d07400e0f00140241080301c0c0e010400a0303480351f60807084640002d10724050001d5480121203081803030300ba0910021100c003807044201e03040d6005a004004240c80740490603901d10900d82c850344103ca04d16480703440f01e0203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 93780036 1250 93778786 93778823
    0x30909090821040506012907060c0807020708121303020301020301060c170a08062107120c0e040203030f130f0308030a0c02070b03010513060504020f0715021314060c0f01020306100c 80
    0x400e645044807a0340740c078600c42c1c7e24110881c0d680d00710300004d0b07441d03d03110300c501204241c0004040c2d403c5002c030700c041c080d1241404641683c03480744680380c0d00641c50004500e014884d040d1090303005158010029903072947d58000090072802c0003841505e015525150100c241480c0f0030032121003c025880c0d901d42c0d42d40743e5080281c2042c20b8941d0880e0008021965481c49100340010301c003500da8078240e01150501d5080800300c071402900001009040c1c1018000540e90010a0750107200c1d440390358a0341c03401c8814400c020b005195014409142d850315010080100c0200a1032145101aa00f006243d101c0181241d030f91900307100384402c04604000502527800c1c0108150380b1007148840104281d0b0303071807000c142242c8c0482e0491084040200f82c0100300580100555601c4201c52030a500740a081c4175808003003400d6100d821051991f2588503041030316008103480c032180c0761030192940c080300d49040c603001c1e600c22580320303100781d21007100302e01c0340c6004139070046903160407107a5035000040303601 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 93781286 1250 93780036 93780059
    0x3040c03081b0109050d020c030303010806010b0307050712021b030604020906010503090a140f011d0705040b010c0b070306080d2a050109080714010c05071e03090909082104050601 79
    0x1101c1c60b182c0070102107002c41c0d0409003e000c07001c6205a0041821b40b1014200074200b9081001c00380c0302e40c00c00c00040005080001d84c10741903800c10a0341941e01d80b905441902c0e1885079180040c85421150190217030a90041403555040d4413100c00d000c0f0a032800da04054807040106c5000f9400041740c4080307107155201c2d00c09954042494021200f403400252100c0c01490f10020180340e866003c4036200085840030b0061408005540d001801c400c40b920070b480d51102d07038a01416029136600c2d500c80380d03ea8413450010519a82290f030b50320140c2011007004024000c40d000707445003441102c80301d80d803a6208003100300320241a0440c1e2001e00c0d0380d168000c15203061f000c4050740e081d0f40790311104011034884002400c40740d1080c0c00d440c2289469082050a58003840d841c0c2090160621070f40c0d000c03610355510704c0e50b0782c0c201180c42c0c04080114903050350170101503040000f105280403000f4003007000c944000e09070707000511024003c05541709541400e48804683c02000d039007080c00104561001403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 93782536 1250 93781286 93781297
    0x507030c0c0503030f090f01030204030c030f050a06020c1c0503070504060507140d120e0111070b10150c0203011b0c261305040b010c05060c09010c140609100203040c0308 75
    0x29a8100400760381c48000030301c0d580103588079420003500010050040d19100d500c07064101020309043d2305080c59031320303007500010a9107c09401078410810b601c007040710520000e1280c943c07005085494003070312644076680e42012145c110342c246d11100402c0700c0301c0c012820380344245956070b41c003480c1c44e007000001c0300c03d42c00100084940d00c600c0710315188444018410983d45041d9503a03811072488140714494191000114003600b07691404101c0d8940c1d52403e0200c500d01034001c121071090340c03200c4000481100072944070044480804200401050348041d01d50181e9008900074001007110300608004116050704441c045400c06d20a58002400d15540c0c890302d1220425195807401955001202d56121109250790070414000522a504e0244603407000d0080a18091140110590301c8580da000068170300c035000403012408000680c859040701c4d42c101c1d8003030951000c4040c140c00740f6a03940c01c161142403240c0601c90652442c0c286510075240b0840e007204443c842d140c5941c607040101e42c0306 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 93783786 1250 93782536 93782543
    0x12031b030b18041a0a020c0606060903100507080726060f060f0403060204051804032a140a032c0d0602270424150203040806070504080705060a0507030c 67
    0x1550700c2c9010280d07074403030070743c441c602410210303800310b140020345000808014034942607684144008269610300041550b030101040e04c22503070b101c044c3c40010307241034040341c2100c0000d8180f400300884035601604041c01095661110003006107168200e01910480c1e04945102d080308a000034610324000310600c084c07400184c10140340000c060200b40c210343c46900160f0703429800007000c1000f803c0a0020089840c0000609a51402c040e50020901c59010041100440d403644104900301c0c524080305580c181e21a64043d41a0403040001e900e50651032400d402040818494804c0c60351400c2e5441040c0c0896a100c02c840c9680c2c608100310050054000e896180c0c0c28860107140c1520050002003130384a03610f06e00c3c0000c0401c4104415604501c0b03546110308003081380700840c0c8104e000c491080e43e03200441c1f010102000001240703540a60303400555184541000d000c1e60940000040054480d04801d80d00c00c070f034541062003220b210390520240043c108210000c08039200c0d07034001140714030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 93785036 1250 93783786 93783799
    0xc2102120a030905070603020309071208030a0509010209030f0c0a1e0e04111203090405060a0b040902030c0f0f040e090c131509020c030a080a091e0602070803040f12031b030b 77
    0x203284d21843d00d0032160b80c04c03c4020960000c14809100400c004820060003000c1c1d20120440d12555100418040642084141611980400c0c2d444a0a4064411114001c0e00b21030480c141a03542d696525104442e25011b01d009403804030b04010080310440088070556101e5040c5480e1910b054420b0400410588071000c52039140d11a030395030309074005049001200210b86801d01842000701320b850161110f8440c6030307404410049110040d080e1000c0301c3c03070f00c000140c59a440f2074262103144140c401c0380440700e03070004101c64044610f202a10584446062480b000c4d951286400e50394030b42c940381c0c075034410400c50088052030000c2c3c018010810000030103020302541d07044510301b41c1e0441d0b0310340d01c01604041040380083d0b81c841c9096030f015480030410b00c50038034030ba19055030704000841d04c4100c0c050a031241c08180000742d0126800c0f141c3c031822003940c80c07405050066a85440d400c00300c403100c6017801030245051103800b8012002c3c040d01242e40d407008070000140d00070440d50a6058002c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 93786286 1250 93785036 93785051
    0xc0302030903070b0706232706070302070c0906031505040302011506020f15011a09220504060501050d21090803030a02040806010503190201030203190504030c2102120a03 75
    0x4505200e000c004041d84ca03041502c95900f03140000503981e128100a00302401501c1c054100031105060603082006842e14000407840700089a0941214628400c214401c1c603061080c01c2d036242d40244810750285c1d02da1048141c42d1003846090311954070024041c0400c1c042206003001c05a0b2095030018070038000000c2d0169101d0818482e035143c0d6104a015070010b0b10b4541d0320072820b12040c0443c0103048203106c0c0c3c4d0360410190305c8010a01180e1900080303004280b8040780d4a80e500496070b101d00e00d00d04e41116071308a1152001401d0200c1d0100e03085400d200c000030707650402a010071a200c1d404060b9410004c406006e49240b68504400d0404000e0782e0131001480d054280b000714081c00340e00001590315400c0c842d045150581c1a84028000c3d4811003480e2107150020364040002982442c000d80e403522058a001412610701c0702148460b0701c0c2000b40401c141d0000007034401684607070300003005506401c680d80c1251184900250258009807c1100e050003030900400c00e8501c01e040019100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 93787536 1250 93786286 93786289
    0x3151404030810091413060b060d060810110318070b0d0e120705060118091502070203100204050609010c060207060203040507030b01121a06030a0605100f05090903030402010c03020309 81
    0x18140c40c20360214504500b40318440c41d011107500c0c082e15190b24140103841003a0382c2d91060890041214050301c80c082144407c010883e000030080b000700400c1c650700d400200c07070080300900040c0f1031010140701d2000780480b003503003a010b410400c102004030141503aa451440162003041900901441d000708240030035058000c00141c1403003d0450340008030a95402c1805140510200810500780d0b400c2c000d6100007100081c8203415114008144004d611002040c0b80140c040d52400030010210361981032000c2282d41d010300459402201261058242c1c1c0c42a00c0c02c0f03206600800b500300d4020486440f00d54000c800802d001442040010315004607500d400c0201d81003610304582c1908182c004109010414040d40d02400702401100718444840c0e6941d102c888000ca034012040100724000746d4281e80c144121001c0d00c1d0009010301c0305141c014110a202da803913004000d50810f800390041043c0c14500b42c2c0d20b204035100c0004500d0368956400640f10700f403041008404503c000c04c07140c42103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 93788786 1250 93787536 93787571
    0x20706140702041d070f050301060807081c1b0303020315090118020c0a060e07050108010e070207030f030c05070305060105210c010c0206040f12020f062d0705010e07060e0a0f0315 79
    0x10010006c05084080c02c0000309030a640d00fa5002c214258003600090111542c0450086a4079000e0405440080100401900c4040d001c01004100d00c207075480c103106058260b002140f250610004c0d40c4040c124010800026482c2030040ea0010b203001c3d004e40c40d001e20b0303550040c14015600c0049602400c403a40d80d0406a4030400101c20b81600500000c00983d60403003085400b4101408000c55a0700e0250402517550a0350303c80900b0a5045103454010305008190100c40799030041c094a411644a00b408c41e9210028452140105d282c504a4070880300610300e150800703010078020f800321103005401114010f01d18001a40d2254041100044800d40d003200e0000034240c4003110055111180100b01c041101c2c2d04805000f003404001c18000d000c0c01c01c1960314600481c3c400040141d200300b000e00710a0140c0301004005601e0200003c036124030000702c0c40304950303895407601001f110400612903442c1d13051040107105038044405000203040e281d1400c104511211f000600b59480d800010740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 93790036 1250 93788786 93788789
    0x12110705030703080c0f0f07080c0105090105040b150303031b220806060909030702010f02031b01060e01050a060f0e0409320303070f03050604061212020706140702041d07 75
    0x122503000154210405404c868250b901441c800121403c0c180c0b034816092007480780c14205142c8000005918081114000030f0341d004048070350082080740760104440f8000c0c11305642c155983c4009000003403091000d5203000807103080c040d000d13505644400101801400c1030080d040744024040c050f00e00702100000f1a000071402040d03404516510304056a800c01401070700d89070091083c60204004500c3c0002120f00c080e07420f1030541200603203840100d09501400c01161800601c840320301210410540010381620700d04000c1e0703c01d03a61784d2000c2044046940c40f8040201784140814a0350600610b07040c020b1003009400422100c0031996030a1480c0d050016131468114040c180c0c096112400a4008002c0718440c001d5180d820302d4a4042c0c044d100444d224420140c484000139115215030700160014072401400410300700303040c54084004203550662000621904a0005407240f080510400f0f0600c0d40d4000c1e498100700f9024000074090f2041d440700b2250500c02c2c2c91000758800c020140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 93791286 1250 93790036 93790043
    0x901020d032c070e090706050a12200c0717061b190305070f02010b060301140d0b010e07020d180b0d0e0d020c100806060d09052112070807080601121107 67
    0x81000e0400c030100d14013903030242003014251b214072000d20040d0340050441e017132401a42400403000368030841c0e840103040a1402d050141000ca001c2d41c81e81d45811018010103c900b000703840c81540c41c1c1503541031080318003000310315170380c031890204200080000c1584520404010365620b40660301038905e501d0700300644040002503a8504210085900026110071844c0c5840280070031544031000a00d00d00040c02281000641c00c0c440c3c14160b034420100029444d480b4010304943d40e07403000c202e81c0e024001c0700e82001600a01c03420903c3d59110303411190340c01000000c0f19810074105040b036940c6400c15401c09144550b500f1680400da4420049004130820f694010440c80c6078100c14091490594000c400a1003005414051a07030346080a607061030b4050000041c40b25510b00340340d0300c0d20014912020788400c0a2100340941219203005100c0040e080c0b07040e489030b44a601c02107680305c0003100d01c100060312f02400320303506601c2140592140c0307500d000040307100c1e081c2070b0000302c40780d101c460200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 93792536 1250 93791286 93791293
    0x3061f05070309122a12050a0308130f0f020621090709020a080109020f09060f0d060509041a0903091008010503010e0f03030a090515010311030f030901020d032c 71
    0x10003050b80c8455000013502c07003001a541e00b20190798520000c0381c3d01c40d02401c48465060802a80000361a031201c00a041002e00180c0484032410007035214021118180e00290480001420200d5001e803c00c0c0c0c620740c0f001c4a100400f42544448440364801c0400301c0e40103000f00b10426005800c94840c50311b01c0704001140145043c224109440c008296201c0b400070b40c018042012035035005042c00c0d044900c07920300540d0b00d003100c4c10b40d4501440340b03c181da42e0241000c40c10411200c08440507040c01c402505040000c00d48490802031800804c5a000b8180c0508546540b181d80e1004441e03034100c640712040343d041c0302c0e0308000158800c080e041c1c5100000c200f980104001e00e424003528000c0181c540140000c0c04954000540301c0c0b0006081c1084c480d194a0401c0070060308014014508500c0300c440603d5503101c1c038000c000c0d085002000c502c60700c1200c000a450100201c100d0f440704505800400e0982d07100c11080c1c0180419043e800b10808040740c0490941e41340b00c841072614040700d8040d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 93793786 1250 93792536 93792547
    0x5040c0e0a11040815060907020c010e030c12070906061d0d02010c050d050d0b0406121b03080d0515010201051504180503071211120706050405190c08071406040b03061f05 75
    0x922480d038030014981d6101f401c8501c28846080d40109800908600a103003005e049024000070078917180d0300c3d1495507044101e544110004901c003041c1c480a5402c1208140840759440004407043c807030074000141145000c911065283c40c2100c0940415441030600b0201d88007170351a22030a01e203202c080c038004100c000580c891440214420b182e90340004076820043d8038101640c46130402c5510070000d1242503604c4207004d445c1d81500c1040011513110700300c29a112102115240580070079580d6410011442500710101e40c010b000d014420405c9003523604d18403820004010281942c181d8010368080c00a2400e0007082c41030000b05000345c000d031900d07000c04440c004000c2c00308040c50302503e425007140ba800d102407408281240c2c0807981012004c00c503500e9604005003044940002650b4a1200b07000d21010420503a0029080303440380b1040c3d0b080280e9403181030117104940426194004410801400081d0131800a181c1202014100030310a1001c210700920760a9007411001c00721703070080f80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 93795036 1250 93793786 93793813
    0x210c09060807170615060c070915060206070e060a030605040204030804050910140103020306120615010201050709051c060e0a060209040518060628090e0d0305040c0e0a110408 77
    0x35007002020070400c500f8100c48445800b039200c1e8005019903102c1e2551200c804125600e039000c1e110120042803d8401e10b5a44820b014024204030003080010f1075801000a180c03800030524a1051000740c9a101c1100d012204126169006c25140818140c2d51500481c0d81d0b182c520260001e584107500c02039a4500704010464040030044c24801c4e0414038000a0142d0705101e03a80c1207001c2401c0c00d0240c0c0b01d481d000c0018403901d0070000c901502e44529800c1125801d0500b0728251180c500b83c0081240d03480701d120880d01c0105030701425030028443d80c00c0040d6a031031070418064030ba0088500150102c420b18100307040200707450003524401d4010840700303118506407140642107942020411429807082d00b949480b55001061a440f40010045900048001101e01c094071a00c04420700320940e2288864401024107c80c0b001032803080d1803600285c10300902c62580201d4000c1405010540b608108000e0603200901030201540c842c9030341a641c1d04604c0c040d0021384205030181031034084002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 93796286 1250 93795036 93795043
    0x30e150a021506040b031b1c03052a0a020105030a02040b0f030702160609030303021b10021b01090b0402100e03030a050414031b190305100c0807020601030c210c090608 74
    0x1480030b03201e2490720300504101c1d030700000d80b007541249034018400d9080e0580c0014105894140710404212900c500c8c074810540e201000b4840b6042c1580640004a802c8481c0203605081d0400d00ca03442d40920b103240f01641c040c2003d19403101c00c118000d81f500da207d00f0308001c641c1260104030030800e400302c203000c18a83c0500090754000441c00e440310041c3c0c981a030040c8482c42174400603090590028a90425000b1040768039601041041100d05948403a031008009502c02400d01c1c84544007081c15164581040c09010a420303004642408541c40d0380d0200081c040868130080240b20290120042d50b440c18405080310341034079141c0b5601c0d00e103010380e60344861040448051094110800c0203161040181242140e54420b8411f8801036144240001221a07070b5000500030f4400c00300b000e8140e9956030880906130015540d5028661600e89060340e4981b0203000082540b104003a0074000c000350340207010000b05c002c16078000c4500032611a980b8030705103600088403e80d11084184032401c03040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 93797536 1250 93796286 93796291
    0x206010611030f16111801050f030703050a060513060e060402040f14070302090a0302220c14030609040c0b03070807180b161716050601090e0307030e150a0215 70
    0x1600a5072502d46011000e2055100d03014660000d120204c102c003041c4580c141000e0a9040040c1a5015028400800d001600b0003449030380d2007140080c841d0003d504010545a040b00d50100042510f9442c40e0740705005418000d084011040080ca10180460b2081c042c803804040244060100303820305005210603101e0460305110b0043c10101220303001280d07000f84542c810300510300140c480500100041c643c10032a071001e0350200d000000c8a001030310300b00b0544079070564050308210200d4051002d0f03901d03800e409102c511040b000e00c0055480c5c2099018154001d03c03442c54520b19948070070005480390015682040028520800c200000f038003c110040c823004040c49415900f0310300295010340d40315030140d144c030b081055000401001424140da01020b07070590002500c540560f0840380034159100c40944180c030412000285081441c4205940c0384141009189800010748066030202d11040c4040d4103d0500d03a00383c800c0a28040241510008942c05415684a005081e04003078802 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 93798786 1250 93797536 93797567
    0x70c020315060102010b06040302010c0f0c0f0605091003110d150902190809010b0f210106121b030b040209070207050916020f0613031d030106120201080703051b16060c02060106 78
    0x401080c00580c0e00500188001c3e03600c250701d101805037500d010102c0c2141c2d0b03030180708008201c1502184207904a8042c2840c0d120984204881e02c02d007004c1141920320380e01214407403100402168500041940114040340360002400341216551548502243c0c891072812880c1a5a00c4500304419440124950410300f000000e001103028003000861030350504502c10700c00c039451889100c03103c5c03014000d01044042c8100810549944046c11080302c54120003c03500c45000803082101c0c403a403034484034203072070302b00084484030b42e0340340c0c244050050060110300030b42c820000001103555800c14401e00c101c109401e4010081a8100301910700710546003600c104d0b0704403d0400081100b035030b41664840790980f501030380c45030940181c081159505011540c00d5401c02802140e212041001680503600c00c1e40d0320000e55440766400c40441d1810b0b1512507088420000e04400c010a2001600300740c01417241a001c0001d5580d240011141001c07036050158004000402049421501032500041c0c0e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 93800036 1250 93798786 93798799
    0x16211d01060e07050706151d09031213050c0a03110a0b03010b0a0509010915020604140606030a030e010302090a030605010f0e0c0306010c030504080f0601090605040c0215070c020315060102010b 85
    0x2c096844015120090420007040f0f800f1401c2000e2010b550044203502076105450001c2ca07444940031241d04004030402d005646072000800c43d058000401c440e200e0859158080b103170b1700c5d042604c042001c00e81005969a10400d00d0b143c000b80d5440046400451160b128040300c6103000082c80f07281812030f800442c10b00e1052004001804c03000088807903900a42c0f40c4540c0e146c0107400143d4146105811140038203411b0015000225000070b8818010703802000119501e82d03952030942ea507014100d8138682c16400982c810030000c1d002c2e056180b002d9405040250924450101140c41c1e114954010b03034182c0d441d0b030300400000764041e8103080075206441c009260b510f8000900d400901c0701804450412442d4899a41494411000d68002e424400c09a654040e10040c06a503506c2080c01a158110300e008000a51803820303126a0000d8022500501220150f90741002c1c2c4080c4010a950300340886c1000044c0140e405100071100c072a8640426100741c00c007003000a003120240c041c007030b00918 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 93801286 1250 93800036 93800039
    0xa2303070b04030c0e0c0c10051906030302030d11040803070c03110306010b0f0703050706090f020f060301061d03010e010c020706020705010903082b02160b091516211d0106 76
    0x204c401919100b03645414030403144903142c1180d09030aa101d11110311946005107030b0001c88035001500098000c070896103c0c40b20010340303010704034100d91040c8001800b6034020028002a1100c2e5004400d0800074135001c5401c160307882020605503403015000322844911034500340304101c002c01059455484c2503009220a40c144881549a48141c0092070122980880c4410030544100104d03035000f54050000c0c0074040d003501d001c021034103001750102e1290340e0340340d2254014107140c41968101d0b0340540e0344000c0b1000800d403403c00700a81c0442d05406549a00000140d807100340076000b840561607000b00545881c02c04020306200d000d81245042000748803041020801c09015140c0207440f40001d60004800c40b010354066203000c45da11070b402030000c500e6400083c1114018018a4001c000c010115941e402c0c0c4507440e903038094006403c520100c0d0100d1320500070341d1441142c0144604000c403420216149203002e00c83c84032041c4180940b00c64010090700c103071080641c0c1c4406044024080d6a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 93802536 1250 93801286 93801293
    0x210051303110304030f030509040531051203010303020312010f06051c02130e070f080405100b010c05010e06060406090b180a020f03040501021b0a03020a0b060a2303070b0403 77
    0x100d003a4006001c000340c5102107070031400140704580003158040d0900d0514540c0b0f1502030b02c550420a40c4600c61498040083e400004911400700f44a10320b01c40b040d5a40d0300c135400b102c0320440b807030390540d60f0344a84042c44ca0240202030045001e14080e170000c546903140c14206130000b4a058026076075004440c04104645078118081e6491b1400c40b400700901c100035617800b07000074060442c02200b03083d2080800180e085045100740d02404644e5140c1c004c20700f81c9441550b240405440080c6554016031400c22000e110390720040700c0a805160603900385030207484240c00e64403400c181c1b4616400001c05d000d8240350922460000348070140c0144840400480051440b684104180800041a600040010031254129501300c00c2000e10261642080d00f440b80c007e401402c202c0940360710503a0311001f803500015800c42ca550341a8000d20f841030940d41c409406200292074035401c04d51a040200d482400200c100c1c0e1071440f14460342c030500d00300800300741c60400141e00441c00742d2800c00c42171011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 93803786 1250 93802536 93802561
    0x209180c031501030b07111f06050604230102070b0a0801080118080d1d010603030c0204060f15050c031b0105040b010611070e0910060806070e0f011b030903020301060b040501021005 80
    0x44942005c032100c0d0903030380c08100740c54000400d60808075901605581204503180301001000008480d0410001c0e50b840e44c00740300580c410b030300074800300d03410f901145927101c204d2410100301d00b02c06106a40c807881c0d840507010415008420520042000704c03005001c80075003407048400010300c2002d0240703e8891500c6042c80391007009594800207440300084091601519050070700003224000803c0704907501c0c14000d0402ca49100c04911403402c020001694580c20a4104141c44200a1404200803841c0d07085c0d03015800807810816a000038400480031441c0d24044041c0210044004a0146418580f00001600507040b80b414091507040c030744245000000c1010076924a8040414a91500616180b9050058401803c818245003010a1610380800c1590040e2070b980c60f85070387c00f4940b00400242c806044490360001c0c2e4500310b00c00580c070488040225142c007034180b45601688079004a825110550082004203400060801080d6410080075403440c1c07040e1720402c5a8200f101340c8020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 93805036 1250 93803786 93803789
    0x207060503070c050106030210030905060903040b12100302091302101e030903110307050c010f09140d020d0b0c0319020421030915030614030c01020d18030209180c031501 75
    0x4003d640b840c0740382000001d601c070001868005000c0300215008410040140402050840d0a8010100813402161001041d86d00343c50000d9032072030609035052100c3d841d24000a281c01c007890300c4800d0000260300d900c8034260050708c0d42403101130811402e0052120495840d0030301c408104407505241510310185034181c1d8200340520b80460000c0c00d5050450b01c0310340d01d0154084602000440108101c0d00003031480c111703042a210101c1860724481c00343c842603d941305050172a0703080f12101503185030a4212150483c8018048050200c00391281b5107030440850f000d400c040700c000144036a0b85062042c0d401e202c00c5000c070a40c82c3c241407403030404410480da0114100c4040400a000401d80103400f11005007032078880c1c450302c0148500005001d015203100c0d8032042d803280c2c4800100b5050224181c9030008040c1c0041411030041c41007210442e8035115490f0070407151403004001603441380d600500a44450210150b0fa09402090a00301800032444a00c43c3d4010322007400c401030325807551070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 93806286 1250 93805036 93805051
    0x11090c070b0a05060f031002030a0c0908030415110f0a150e0304142b020108101d0703150807050f0d0f080306030c09010602030d060611071703070615150207060503 72
    0x80f152180c2d4040340440010001751649809056000d075250340749a40990b108040406051282075030302c12047d40c01032802d008091aa8108110074042d41c203014040200402640c5401c1c07444101201c2c1d000e050664000f0148840d17082039104505012107041c0c580e4860820150807c160b10f4021450f5a0341d00c21781c40340020b070004168074881c0c07a544080d04200c28442c1d4480c4030801c800c01e04480c40300300000030310490214000790041100385070500d00440c01d0300c5000e81c5d00d800d14802c1040000d42400014129820180c0301c98450480c0032101e0214001418a6001848c1450a04040080e800d004050060044200b110002e004c82da81c0228a08003c0d0010707009036498841c68046810403a00d100501d07007188000000044403940040103040c45062107004021032515901c1c12903002c8140c43c0b0f81000351f8492803003844554081c031340c0050380d421008101e074034124080d56400281c4444850104000507a00c0c41003002d00c0544030701c40109951403010f01250b50404801500b1400040c0c240e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 93807536 1250 93806286 93806291
    0x312020901020d030b0402160c08060114060409090f06060f081e070e040602090603040b07030c0309051c230703090807030201050703030f0e10021b0a02211203010311090c070b0a 78
    0x7000340d00c42c2c3d41103408c110030001015400441606005032661107920840605100b0710000082c01d42100c0e200140402000300701d245450310701855180503002d010030a40c0d00c129001a1540040c0c2680b26140080c881150304404191411040c1070500c14100c05190b0340e0003448140c2c4150a10208042c0c094542c0b4880060b440d8440b41401002802000001d640216000050100340900284c07482c2c032030340aa54040c408890445801c0301070351400300008020340d0241200750307504492541c84203c40318441c9044540d1061400880700c03080d200130b07403842c240c840004601d4207060340302c000503010b000c14400400300745141d03500081051080443c06000c0650b901c0c044202c04489402c039680010700a01207070b411903216500000258001118184600c5901e100020070010100711074035001c0c0c0083c0100d42100400c004ca40c011400e003100c44880780241c1e01c07041c900e161980051400786020340a5040341d40380c42c805000700004042d0082d80102800d00015000401007801c0603032241c0c101c1c201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 93808786 1250 93807536 93807551
    0x702060a050c070f09020319020c0604080d0b0405040b040c0e010e060d03030e0f0d031d0304050d030216030b01060906030204140f0102010605130506040f060503030712020715020102070312020901020d03 89
    0x60b00d081401c02c0d08441e03540d840c4800f00080020301ca070040d500030b01d00803013100080b92003403080408030710803000484901d4200400080110300031001602c85540612400320303180e450780700020121001203500f2248041c030141400244a00c031030000b009011404e540d11402d506120b840c1c0803680b0b00400880c455841000301804041c80f03500281c614038400012125403902d4203900f04d442d00000c81004001030b01d41011000414640d4034038171141c181e60000345107803905090500c0080340d00800181c05521078901d071100c881e1124801c6a00460055141e03c20319410402e000b0b000c0c07500c40e401a01010b005000511030303e00b40c9603603070902e60802c031a800401098080140d001d0031961380060b41c003480790003100c621040241c000501c501c03406c1302d040204240d1030b0301540440c4c026008803034040c0d100344241c4000030031031075000e010000680111a2011341d81c40c0002e0400038034803400401030750041a48400c150f00030756001030384448400254104614000000d50ba0388070a408241055141c850 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 93810036 1250 93808786 93808807
    0x10203010e0106080709170a1709040b19090203041416080105060307151107090c03020a02120a020c06030c0d090f110a050102030924040311010f030504110d022709070b0702060a05 79
    0x118103108c1c6d0300031440d661806412183d200c60750050b482550142e0304106032500280b40c51580038008207500403550300315905000100c0000d40002740111100001e05142361294001003041d08010811740300070a403490b00301170026081d524044c0070075000707034850356080c08015401810f02c4400138651070919001200011228074007903c4e1b61000960a2170308600d0400300ba8140c00400c01d18a81e502103a0040381e0410380c1d400c0078403811800710010b1300215401c00e024540706e03005540100500c00f001d81820b403654044001c65940403021100c21291226000410013000d1405444c01c0c003c40b200540d051030540081e4407072258200c0c680c0b003041ca0805070400b000190601b02441818140800d4507030742c681c07420191700130040403010f02040c2030411081102d8070902500f481030307a01180c2d03108050003407000c1c004001c824460481e0300140c500c00e0040e030701102d0044202590685c000155103802c051400b5030802c90190804c03082140308006003809a19290200e0f1a03c980b1481c245039100c80400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 93811286 1250 93810036 93810043
    0xf020f0f040507031d0a11010e150d150b09031e010626060108030316050a0908060a06030b01050301020703140304050c060307030c091401020c010c11040905010203010e010608070917 80
    0x51120354001c2c0b810081c0300c10294540d110006030320901440080045014801c1569100381c01d40017024506114510340b042c0d48600c1010032510805003185c0020f121803404412681c200c00b55103c080e82e91038420007401135000e5002c000501007000d003240b40200105c0801e440c2d014a0815032922920000090142e10003544420014044401d000c0c0c0020a100c052086015480701010b0342486090004034550102100300d03401444030807845026444100c0703041d580c1e500400c2d44c9006020941200145401003030224034807608401e1750020b0b00c1d60841c90602c01845041c0c22650080e803040c0003240000e0b40165680000d049806036980e1a0380c0c039483d01c94500550b1a11290704074a0100512201c3ca425400406e98140d0035116542c00c2c54640b501000d01840c2c4440650042c1c2c06256403d00d02e50194210031181c500545100f940c40712004081801d880a0950807920381c0e6001004110094541010070701501c854038014a05040941c4010710030380060154a42040e812054055501c0041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 93812536 1250 93811286 93811309
    0x80c04090c080d1101050a0203010806041106040306050c0316090807213002010506090402060310080d0e01030b0402030403140a0e03010c0503060306090c10030f020d0204030605100608040f020f 85
    0x800c2120003142c800b900050801303c4102c00c0d904158200702c04a21085014020340c1c4c141d414442c000c125554a5840760285038100042c40c54202404102c01302c04540b040c004c0038413a032021002c3c2652401d100c80c03020240745c598502c2e2010071070850b909200310000880c2001c1160820000c1600c3c07403420000d2801e084124441c020400c90203220040742c80085240c04400b22501d078503001c2841c450708070080c0d00782ea034102c0b640340e4444050300c0000e00515066006e160032035400d010b03001200d07465041742c500d4420304000a00120301c4450034407050b50b0303040c010403a441c0b01c02e071019070450030030340d034040c0009494480c0120200b5001c902901d4261059008020145000f00240072100004902070110ba10940700c45029000b0880050030001002600e41c291540217056001d031070b070b200c1204030014906d940c101801c2d603800b0008014080d0300c038005800514011400050715040842500d61880c603181e0100c5e0901c83d00f0010000030800394003800300b0382c41c0c0503070308014000b92840004203182c3c041c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 93813786 1250 93812536 93812549
    0x20c0c0604090507110606030a0b090c0406030c1715010302010c0f05070902030609070816031d0601080d0807020607090603050604020405120601030b06010219060c1701060509030d09080c04090c 85
    0x3280001d49514250011805011075480d203503005c02e01c29071003903183ea00448074035400d030388810341001c0082c0c0d20560641c3d003c04a20142c62050744450b0008040c1c1d00140e0040d0744100c2c07440c0060000c800343d1f561001c0061006401170055211100c0754002003001440301a040c400d4100e1980140099000c240a030700d544330b030503900213546a403180802074005a072442d020318184000640021701403805280940211054240d2000b0744040c120090030329200c042c0c019030782141c0c002d000044100300043c083d010300b40c00361000030280b68000b461814010000d80466100300b0a20580e2a08000c528054851918010136503070740f04000701c0c0c083e10466100c180c114100c5500d200c004c80000c03c0701c03810b8074415400d00c1080e4951100490f9203404c03c070480620340018422240c000b0b11250301202000300c03203050514900808180101032030009a010501041000900320791524090080040e01903032030404401550500c00000c0e55803565003100fa024503036504494040c03001240410000f480c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 93815036 1250 93813786 93813799
    0x13090b13061a01081f0801060e0f07020d200312070c0201080705030114040b03010605090405030a0201142503090804080a1707170a03090206030103030306050310060b0904020c0c 78
    0x62031002100820540c110503107540d86002600180d8815041200c5290441690341600a4503402c800400d032298640700f03070030300b070414403c000b908100c01c0c01920300924a403120300070203140c030305803c00103298010840000c40d0458081c543d109504140c04c80382941a1120092403154842c0c50325103184140c8551920340305e03c05080010b0107500c81085401c59100323a0b69104240c903115025100c0e40800e01900304443c401c10482e6005003025480000c89070350007000401c0d51a9580e0125403030300c2d030544003513800303400c00255410040e4090040160703116494100c051030b032400c0640e14040101c0050301000101e0030041182089200e500a038468581190f51207560b9030f61522869952800f2550440c0d1034000c2c056200c81d00c02000c01070300c0f009900660350401d1800c0001c100354499020403070000a2503694000200035880f00c0300030b18040c61007600c000400c02c4c01c00d0201860b04c070b00c1d18101c05010307046c9072041c0030842c8001d0a840101c82c041e00e000d6124020011102c0c2002c4281417a40c0c0c0100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 93816286 1250 93815036 93815041
    0x40614160b010611011116020d0f06060509010608010305120703020a05061612020c0703031809020724090c03020f0604051302040501030605030a0b1303030207050d0818011a13090b 79
    0x36002094121602612130850070707019030311403d00380c1d1204d10042128100911180090049100c003074101c05100030541c4000c1100d641e28081000c02070b89007951050f645000131721890030300c82c2d42c0034050801c0741400c102540c034660380c10b569410405140320386100302240160405d030003040b10f10346031907200058810903d8804000c4c00820750034282c080c0051150307114420840040e1007113541c0c00750f4080203060040d083d52001d85e00f81c0002c2e400203110f1006c84c41c0014036031001c2d202504042e445000004002c40c5205900c80c10300c00340350050500319152015150000b501032300c444044950565403441c0c8000003200150140c01140e02550b0446960030b2040c40700c0c1d116074001c10640d2000d0700d0400c01c0e69111002e05941d12524180140284800c10101300200b4007130741c1340f1900b80c0c40b030b140141c580116550341c5410101d8050300755010071030b2030050185c0c01001c400ea01d41040c1960000b00b10b07800041107400900b000d0301281074050b440450300d200980d031044d004440038581000c012901c50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 93817536 1250 93816286 93816293
    0x70605070305071e0c0206030903040509040624050d0b1504020d270201140d0603080c06070212190302160f03111c0801090e07030b090a020f060a020304061416 70
    0x3080e0032070f49140010f5201e0024a50010342c030040c00070660459481000242c0140d00313024043c1d0001e800002e0600c01400000361994a5118443c0300f14410303080400d410380301a00103c19007000aa03800503000105009100c540c13120704000400c0350300400306401b0340d00e860303a8600781082c4060805030810300004080001084d1500461041c010034103d0304401d46a080a51400b4007101c2c000900103a203c02c000c4650100c2c0340054000300c003c00c4c1000030810b540b560b0f2111240e01000f902030303440d08a0820807801d00d405110400e5410720900040346800c002d200c2d80b8914160200d614400e240c2c0c0400e105c9480303151000131000155101c1c007000d01801e6181006460203200c0301d00904141301c2c441103072420b54250b981c3c0b94810009512006003590038200000050040b14603e292240301c1c180d00000443c2d451005031303000f00802c80290040c8281030040c815a007c5404086008000c100f0011350700e0341c3e000044400f214080e290503202c0580c0404000c000b842039494840b0750742c1c0740c03158800a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 93818786 1250 93817536 93817541
    0x1110a03180b27070302060f0a0215040b040b06090103030905040e100f1407050c0303060d02031507030c0306050102010b090106180e010605042c1b0c07080601030c050d0503030403030f020706050703 87
    0x208120055289450103d881c8010f03541c01d00c9010080d0001424040c2d403001000390307809001c00ca843e074015a14000486da945240b5008200d80c152038261001e8148170034003c44c80034842c0c0001e800d495100c038940c103644001d02900039620455001d0707a03a802000b4003107241844500c0510b42c40030814000d404180900342d000e007a40c41c03500c401c00106040820207a60269003114020202c50019504507500c0300108000e0b015003a0007079070140607075061070001f010032070300e014070611980c1c400080481040c00000d086400d075401140c1960316024041c0c40a82da54030b00b02c2e044900b24a001c112240007081c0b4a800b90240780e00c10781d0405114000420001d4018011b40255555481c0002455440301042584c10791030a0407880d4201a41005c200e2580280c540200e480418080c090303d0206078100852520b4038541c04032800d60030842c0107208100030020340a0048c00704440c4036640210989420b5201d200c040c1000703060607038039045101034412540640f0080340d005841000f00c0e103000d0601902 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 93820036 1250 93818786 93818821
    0x190618050108030a0804060c0c050a0c080f070e04060b010c0c0305010b1306031e11030f210a0206150a0b03040503090a0b0406050405040f0b0312070303060801110a03180b 75
    0x211034203110000c00d4102000003980d40c410810313900c9242c03644441d25420000c0c9070080040007081403441350040407620401400b4141c5100b1345108500618111005082c40e8101907034448641100310f00700314031052031100c190080d07080140003500c00b0244005903482c00c03501d1801460b0484415000052200641c0040d0003241d0541751340145041460040c000c032342113408010200b045e209038001c450480c40458426079481800e000e500388007014000707031510346801e8110009070301c1740410449412000d080c800e140202c0350891424003021220294884500610304d2203a0080d40c003c0c0307003035070761100e481800502c1d248141039600c0c203150030160340b240d103e000c040e8028980743d040000d080c00c2c058101c3d4201e60b03059495600f0300c0e00340001c000142064910b00c3d00c006458484c4100c060b98140042010071044040242d611038140c60301409031000e640c040f08150340b40001c50192005031104070382c1408410310b0000740ea590000420b01c81400c10041c064115225481001203900c00408000c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 93821286 1250 93820036 93820079
    0x901080a1202031c02090d020a151e0e2403040305040603051e0109180501020f07031107140d05010e1b040b0901080309090408160302030d0b04090203070e1906 70
    0x564200d104078050740d0f60300c0303803090000741000301100d80b002d0180c06501410010320014400e050303110355078002500361700c065048012641d0600440290b5240c00040c14009004000700c0701c0e030f80001240c0064144810a40140c1c00f076100407a10180f010203054040030301c0c10071020000d4403400d141c14001e005d50014000c00c000300b441e103400302d07550451040400c1c1d00c82c0d903820300d142c80c00c3e0b08181020000c0c041e15103030240e041454040d07000c0000d80a0000d4500002c0d038440d02601c032a403904000f40300041d01d40e10304c04140c02003207042c8580700c001003224440751400d645a050055240c60154010100190707844079900402665002003c800071014010f00c00c1180c2c140100030149040088044082c031035182194000c108001d8107082c68404103a00c98000c891041c18600190007201a40d902c544085005800000310044514038901c03ca100012044c0d40c00c0084211550200e5039075007103400740b40d00101035100002e25140d0b201c0b68014954202d241c040c405d42e5a80c0d0030000c5058080301d07568 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 93822536 1250 93821286 93821303
    0x60d060e0a021c022107030501060305030a09060504120605060d0503160c06110c1207080d0201020a031406100804080d0c0804060f050c0706020f04090207140606091e150901080a 78
    0x4850200f00030800941d80c9400070a207204001600403c40c015180301c10300c40c2c00c0b502030301d0380004c00b00700b0a2140a0045000700091036482080e030400a260041c02d070022030a010080c0400c3c080416240010340d012a44000c00240c107450300300c00158000032005004009120021310450610030348460000384900c1000801e84680e00d5040c00d8900741020304c80b08441d40e0255a503507075245004941d000b10f07150b06800ba2458907459440320f50900c4185880c01c3c000d41c0d0001030b00c0240c039625108207035110040c03441c1c19440d414030100082c241c0080741c591900708400703a000700f4280055102114054190030408004080c00c201000e8481c860484003503e046103014200700303c80d07541d405080e00c121a151525458000710307030345a070000e40101e40340503040e9a05000c04501c1c80c0b4148001c010f40d900400b000c2c8544240141c02e280307400401800240500001d1050040d041d5520030440001c528298100317040e5076510b40050304030b11480c0d4a56911142407030001468420201d030036042d00f402a4480d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 93823786 1250 93822536 93822559
    0x109020a0806030303093004080706120c050304080a120e28020a03081303060218130905120d2003071d03030906072f04060e1e060d060e0a02 62
    0x20184c59000480c0da00545400207040380c0c0c40699228012504501e15880701e805120901c80d0f12940c54205811683c125804510103004083d0840345c103506c2e40084807024841070440000c02851030102600080200001042880342140210718290004082e60710400182680e20003541c1d0310202c0440440620508501002002d0b042c29030b030307400c0c8a0700500b51110302480c5560b403030004c2d44000c41c2d060740001c0841012000808900003019404107810714202040c84c20001c100c103a03000c041501c00200d10b00b481090000720042a010b1030060288102c0d510303041003001c42c00c0940300310180900e0340c41004603e10107245500d8040c0d4010025036030381030031040002c0d0710401150061303e031081d4190310502416641c0e02d0094001c1164074402d050751400f0303801482a044405004072a1b018580240101d91000c07820036102e8000102002c5100801500746208180c1c0d4848885800c4e10304500c83c2da002400945940c008030448540c0000d042100c400ca4000307040d151108420104c7c03040900101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 93825036 1250 93823786 93823789
    0xb04050108060c0702030f0d08040c060c05120307020708121305240304020109090c020d020607050909010b0703110613050613030e04050a0605031e0c01020303070212031504050109020a0806 83
    0x14a81a03400820042002e502c0b070f00400344071074106020481e4588110060301029080c2400582084a403a45680450341081c1c9000d0a0508243d080102000105d8101701c001ca20000340148282000081c01e076540c0d240c14504078104001c58010084602c030303030400c0c80000780e114402020380440302250b4560703030f64685041105124090410b8120b00e40c410880180b0f1800d0b0500440e0000c0c41410030450340ca941f0050101516039104011015070000d00a400070160140260340e031001e45441d09a01e0240b5800000f104907006009110300d030701c80400e2003010103004400c20440440d071002164200d180180c11000c5140010710203c039280135540100d4030302806a010380e186650726854404582d100c0c00e0610008007070050410600f580c0b168000211a00c05000c2402d800c0c245035541454881d418544511300450500640c3c115030040040003020b80e1b01042400c130240e401c0100b00e6407901c5083c002400001c003c42e500d58031510303000000641900e90307402400598080e0b166800c1c0f60380c8200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 93826286 1250 93825036 93825041
    0x916031a010803040f150c02100c060f0204051503130b0c030a0605030a0b040f06060506030901090b060d1e0c090f1b020111031306140a02090909030c1f020c010c020c01030b04 77
    0x845d40c0720342118500e060262030006940702c0402909490903189146154000480e840e00d001c0f0341c2c0002c20001c00004081c4101805186040002c40e5401d519040c90200400c02c40c86044040e02c429410110100c1e41c50001550301500705504036104c1c10307250624004400c0181d0013a1440b2022614111001a00e402c01240181c021500601425039590301e13074a80307050300c50000c441190259a1040c01180315541d00001d0344c0103656000001803039114900c1d20116404011380f443d48601c070301e112143c00240c441c41c03204422000340150080c400c000362500404444c0701c0d40100301110f042c155405a103452690201c500300340c0b905c1050b084c000803020181c0c201c92400c00c0380402140d0810008560701103000c4425605441528001441c03140d00d000071481030f009841100809400141c034030182d2500d86040d68100130b002d009989406281b074001c540c2e0300c03404241081003010001c0d202c40c4110301c0394143e4045c904180c0090102064222001392107041251086000c00c1c0f400442000c54100740c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 93827536 1250 93826286 93826289
    0x10801060e0606091207060e011706060915040306050408030613200a090f0e010f1a0d0b0406030f0303050a0f090c090209030102040323060705070206120916031a01080304 75
    0xd030035150003602c840c0240326195200742001504410b1600104203040c1c000c1101d5801055540d440340010005600010800d50855021036004543c28050141c07503501c0c0801c41e8108101104d0074402e000906e03004000038000c9901c05040c1526210800091149041c02141305020031104503da01810740d03000011a945440c445004080d02000c1400d5181120002c000b10041402c186400d03950702c03444038120218580043d007040c1c018100402c1800e070ba8440030409807441d8401304080e081294941c0752240115080c9180542e01da004c0c182850300c1d6a44002c1c080c50700000d85051030940d07810054040c1070140c030302d01c0c0c04503c3d20038128440b0100e4420000382990200d13044020320700c2e04050101a42007000003d9055500b04000070004100b40c4040d001419418010807540301c14140190801c0e00041c40a4148001005403200503502d071001c07179a01c030002d84642102c0c0c1d1181c0400c1441c0c0500905148450b0b00c484a0120070f011040201400c000000c9200482d2a078940c44c0b81e076100e0046 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 93828786 1250 93827536 93827549
    0x30705100513050c0906010216080a020301110c03070305090a0302090406090209180703031107080316110d020105390c03010501050621070e10030218040b0a060c0f050f01060e01080106 81
    0x4102131003540782078007901d41c1158052040354181d1070100c5445102c84020352162410f548920100e070118182801555135076103025180e81d04082d60b10216589900c1a0907000382040800201910346a8940804901664002c1c213a640e040c0380170718180d40200200300e002d0b481245034100082c01050200201c2d0542e610034030241002501c0e595090b1141990f0000c0c803c42405038071404641e01c44100064643c01e0100c21690168001e5424042110031180071010300940101c040300d00541d81100c00c036029400c520440a403440280c51002c801000c00844804260b01c8007422007421901c005284100244120001c000e1a40d0380c0b02042654400c9001c07940c5050400c04c40400d40181d2407120740e40c1300460342003070101c5d48078080000e082d48041e45100310100c1e034003203030b4040101503d1104901d818810303941006041240700004d50f2601c042c3c820b540c100a62030ba114402c0000300140f0482c00c946c4282200ca001c0d481002d8103001e04410f00407001c07606003544c000103404c1c905000780e10803602c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 93830036 1250 93828786 93828793
    0x3050f0a090203031603030b15031f05030715260603161a07210807030c0f020a020603060604050a0306050117060403050403290a0c02190c05100c0503070510051305 72
    0x9030179226801285a030601030b000e2564400c80503007540c40b10300d2952a05903403500c42a80c0c0e403401946500b5140c0000413a0f880b0b501807520144415100007a5440c02d0711760700c007035818542442c2e400c11164100610326800000d402c1d802040e07070302d030311a130840342c0107150490568110040c900b124041080345849000d66101000307501016840031fa40042c8002c074040d001d1003010910f400d01403007040d0040500c0100103595181040f00c416414807628844c10503514180c500a241c003d0020740d610b41c0307151f001c0c0c030076000000403402650381e04084800804014000c0342c1240e80d80c0c00d010000382001d04c11454060058850b560010001088842c07085078152a4942081c0c1143c8a070301c1c6c0c00e0300038803c80d410307180d0360000d66600e95041e010840c482c50b070031400420070f500c0d100402404c204030000a102080f40d9808240001051401e10034155034059401141d180c050980c00ca9210fa00482c0c050414007001640b0014040042900c0c003030100b0300b1205000d2515251441c880301d00707014201400540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 93831286 1250 93830036 93830047
    0x906070605061914010f0908030307030c1107090614030304050901090218040518010624030f0603140609070e0c09010503040203010b09010807050306010b030f01120302030c0d03050f0a09020303 85
    0xd40940c41242c00042c00b07010034100e158000c1d40c0c84a520300325000390316034a50313102c07040300d103580d0116491500401510340079424518000c80c265803400302501003010b164690080c81e6281c0d00c00c19003a8849a80442102c2629548010000081500340a0380c180c440c000c4540006178200001260111034025100c800f03143c1c07900004d01c0081d08180c004041ca40400402c02802d507940f03001340d0740138001e401820301c0c0394036060201500319100d542c00008a00905034544040c0282107401203420321341828042000101034400000800b041e41000307100b01c00c1e501c0e00085185000812602c1803000c001280c2c0d46c0d5840301524000100100e55000c000003003084484080d51041d8095038100b071020b000810128200c00000390032580907040070300281e20207007080255140030814140140440100f2914605144001081d02c900501461804403200b40559003058400c00072110440e95850589041900015000700500701c183c4000b4030000000020031a81191445421103440e4028019850714 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 93832536 1250 93831286 93831293
    0xc060e06100303172511060c040806070c0809040b010306030b0c12090c030316020118080619050603060f040c03120e0108060121150807090c2d0c02060c150402011202090607 76
    0x1390385c40c5090200f08031201080c1d0074000703810405240608440c03140e907034441c0e0802e59003900c9c00d40010001d10070000038006034000325004208498900c0d10079500481c484480030010b0f8003400b000d40c0006c100d04500e0041001ca600620003404a00c0d4100703203070340160b4440300d0700030790340c0c50940542640c9600104296080072400880d40c903e03580c0b040c184803900c0b00010000d4501e4140592010020307410400420001c00442c982900c03003103c8044081181d41001ca001c20768512004000a90241c170040100d81400b843c10a40e4008591000c1441d8501035444c500030100d104040c0300741d02080700c143c0490010b43c006d0420103610196144540341c0c82d442c415088010b041050000780c800700340c1b03680104007860b06001c000701400e410500810050b0007080c00404415030700d101e0203041c04507440c1d4034200610800300e2a501d40e440f80740c100300703501c03180c00084c1c60341c4a0056000c3c080c0c852214249035540a00100500c20b038005d881d48101c40c404030700310505a200d5502c0440d8810402c01021001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 93833786 1250 93832536 93832591
    0x40504050a060b190f02010606050708030901182108010b070b060604090207050604050c01030204030213020f21060108070201020a02031c090c030804091503030801060c060e0610030317 81
    0xd00c062404121943c0d180111010342e0301160040c580005203140c100308a81c1c103c031141600c0e04030752000b080502e240c020010503034010700100401c480c0000011480b056025000340d507040c540100e5040020200b45001031000c242000c2050108603100e21418080b03009000700c0707040341c2e100c2d0155807610403140c2e00d18100740d4000b0310407907202d03405100200720300300c441c0302030003069124038001d000e941490f040c0701e0f25210480b054581050b004000030300050b200d06040d0740c0c1c0b0003018200980c58101e0701b10104c484c1c0c0101044108011684030111202c0f4294000c020302849082c0c172040c0d62505c481d10100c0c243d210300d00d502c1e409a401004105061181d80c40040303220302c001c01c0001005007080e5501104841640c0c000e030784089000c03406100d40b10517845078031030421440e402910b5192655901030304280052040c0c00504c0050445c00341486a190003004500320034000b910414a40015414402d0780b50b4003045e000201d00c040c01800c0619034510b294040c074001070324002452078801200300b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 93835036 1250 93833786 93833791
    0x306090f090a0b010801090302010e010903200703060f09020f01020a1e02241902030702010f0c08120a0c030e1917071b0311090f0609090a020607110907110304050405 73
    0x801d88200380c0c0d08804240c0003980c05002e01490000803801c0f01803410002d00352a00301c42000e407164901018580001c0e085850045184040402d0403110308240380002e0504aa0341e0000c1c1c25541400a0300c0b441e03c0169002104051007219440095501e0400481e514041c4141c024882c002061240da20a14121021a6844c1c0300506060a0012034000f0b0003a0400300d94280d01002000310384010915000b11104c040e00c2d2185c4001c1d81880c8803900000d000314003840505003032140407201042444107580803205901d1801d0109505414003a440c000200803021450b0006440e040c2203098040d408100c104120448a0029541c1e4400b40c03510482d1040320740c511500348004200e0100050f036060285c4a82441c10b441100ca40b0385142413500e0030001000e801886911400200108201c2d9021020780045040c1d4613054580e56003ca40c031f00e88a00c0441c06076020388081035202c200301028000c1001a00103643e0756015440381740782901e044100c0100e0407010b802c207100c00e011a003000d40c040c5c0ea = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 93836286 1250 93835036 93835051
    0x60903081501090918140703030e030f250902130501181d070302090d0c050108010e01080d03050c0c03120a0b092512050403120c050a020d0c06060f180608030306090f 73
    0x1240014246d840080034011301c940300c3d10503040048100107058102d03486810104041d00a41001e100710440070f502c0300e032498414a0000d9034034500d0f0b16040c80e039404620290404500455032407d4461200c40c1d900124801c540c00201e200d0b0383c981070010085246400c541180c41d0b00341c280707601c00001c4c1e404840000d00c0e40c41015400d0080c41140c0d81c1340e008055406008288180c041e5080038001445500160810b90260148a0041240e11b01c00210764100c2a407a25001810b604c0b06000100c4500c100ca61801c0d03c0e21011900c5d009403d1400006801504000401c1010101c0c0400340610118200c540c1c28145a80a0f181140700510422a02c01c05c0b58502d40a905086003615240440d1404c2d5019030004002e000310922a204600c105000c000e1a403e1013030600c521154000d50700c0a50603410401c01214003012170401800d07401c00d40161100e0404185050b4071a005041b070703400b8020500381e840e4201040080c0700140481280e00400c00070702090368a683d00002d11041c00405040d21 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 93837536 1250 93836286 93836321
    0x9170c070f05181509130b0a090308070c050a06060b0c01051605090112090b011202040b0307030512160503120405150f01050d150507050912010b060d09031b0609030815010909 77
    0x303200d642d03800c126900c03446c1d00380340e1300743d02035254101203c801e24010100c03254540351092140c0400e4001481e650300c003941e85859280307034010b4940141400740300400240700b9030607e540818101405d001803d0900c000c00020040c5075111034898640c6802c0a416802044007001915803c3d4410170906284030801c2d00041006000c681d44d20141c500701348d01844040d941d656801045107054050300210500460003050001c2c11529401d4651043c4120444807280001d00065144e42d010075680481d034006098948504848540d011400300c00c41d821245400341c00720b0f04c1814160800c000e40508902c400a0170700740c0c01c2c40244000794010704419145419009032071000341c01c0c0303402100c1c42403840f541c0340da40f03a40540c003c0c012085001e01510045904040b150106c0e512104280c030004215160042254000b40c14261225108030504000740c159000410701808803e4010f40002c070711903680e81101c0e036140040c10f0216140d1141441c00906088030812028800e41c01c00045c440c0c086481 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 93838786 1250 93837536 93837571
    0xc1a07021e031c050a14090f04050702010902030106031a0f0f010911090316050f06180409021903030503041203060b0a110309060a080f0a0b0603070f020109170c070f0518 75
    0x300c2009080f00d0010f400282000919091880d4064050302c4056070260f041c9003002da101700003400c01c452840c101c90281d69503000040d51350f8400d4110041d81600038008021840e180d081c080782c00c50f9007a50724440e41c410040031554004107a590a84184502d0025003100e07400c006c42a000f40c0078010380d50404120074440850036a50a0110088121800c601030041a1403c401c0c4010400c400150520907503080c01840b0909111044060300403030100c400080884c1240300141b00d280344c0c00701c0f00e0390481000d040882019000001180114003e0a003210500e0480c0c20031025a006030242e00000603080c80095080e0303001300d840c070410303d991200390313424190b500d408507a868202d5150303400091740d4101800b03035565217000d40341d820031079903241482000c6100c000320b502c5110240c202005c110300718204d210390340e01c01c1d0b00401031684e00c81035041e914403070660300c180c1350340050034a820503025816000804180108411381216400340150302c1505018003070b0200c41d90000c042c1481d40041e00348 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 93840036 1250 93838786 93838813
    0x1020307150507080604020a0f0509040f060b0408010e010603020a290c03040f090207020d03050c1218011707090603020d02120a060303080106022d0102160c1a07021e03 74
    0x8003038041d100e0303450300154a15190400820742030380505074074046d40c810055000d1960740b11f65400d0b4201190700701155030b01c0c04100410000e0134904c5a01004a02e410b0010580c0d5a0392002401201c1c94000284241c0841d0341003542207a6941c403009520000c1c2c0703641040300000c82c0c1c40c0c043c0c1c0741c403481e04003403001070004a130325806030b1150305507503100e03000044e0600520858003c8240070789610b407821030418a01d030f40845c80c01f01f003529004e0140800480c03400b0459100304004901400c40700700040e158124070030328401d031817018039255011441c800111503501c3c01d40c00c84180306503819501c4031541341c45c04400743d00940c490701c20240081d400b00411840000000c642c140034007043d400000703500d49141070048c8103c0c81a0080f00c1150801e6006070804074191401c940301052184217142c030b00028600c850300a115004140b1100fa0801c04164180000b80603070300c048601c0c1203440180e40320781401400c45481002c200030350040c000c20a10300b1408440f9864020b501015003100d4a4102e101c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 93841286 1250 93840036 93840053
    0x302070b0702071d1501031503060e07090b0f0306010513020903060103120f1b0809040b03100b0a080706020604060b0f031509100c02100906060f080c0901051005120601020307 77
    0x6032401c0159204480c1013001c40e03980480d4000c1d82810b070441ea6003608101000c20200140301c29124109611048504000800300c4007001c004c5d50700050030000107115060964a803240c2d4441d071202140f8055a5070054140b07881000da501100901030708050703003800300704943d6040b408000c200203035091002e1980c4d81c83c04c0000901860166001094640c41603a0082050141380f003113804005554581c641b2010403600300c115007a900009698480340700d040420010b2900e1188280d16110b20501500060701a03070007505c560005403a040d20858a81c283c4580c1e441c900d10030007006921660000d40410920b500c00c0b9803030000100a65404c0541c2000207181800b00c040e840d10b911035000a00039034000803c0a0030140d05024414070894864200180d1034650068811074210b485003840c0c4100200c5034003100c050410851440015502c80941c103a0300c0c0d0102505900400b190000404c080c034111042c51400c00142d070742c0b00e00d48807680c1480c820400020300150b0643c40140300741d500258901 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 93842536 1250 93841286 93841291
    0x7031b080d0216140a05070605070206120a0b0a050306070e1e090108030a090504110a050c0708030d0c09080303010b090d05070306050c0703021905060705130518040c0b0f0403120302070b 82
    0x24400c103103c0d11024203003600d4240c04840e0f1003405500801074000007030808942c1400700c0f40e00742440707901c0320140d0011810034807035240034000c110040701c10070120800541c08162660300540b5070300082c13a1640c042c9071341d603003060b90490042500307021102104e140c0307900d004514a05403440300303030f4051001000c00d05c030034070a0b088007070380380c001169101040d80d1008621004200485040c0301c0c010340c80f0f00c120140d10812408408001000820b00902141048004024403008044a546440c445401d400410801c01c1210000e00480000a0b51000001c00d59058a554051042c030303140b0b01208000d0340385c84015003180c0c41e009101000010400038030a00c1e03c0303000c003c01c1080d0b0711540c1d0b240c009d04180b0070f00700c0292403450103003071b16020800c0000c40c10341c000c0701e17400c000395101740070081e40803802e02d07540c4141d50000140400d4002035080c0c034840c602480c0b0400d1014616512a0903450705801083c2c0c0c1c40e901188140402c00100d03120b0140c0107403140841c10018035001a0b41c84078403410404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 93843786 1250 93842536 93842557
    0x2070c060f02070f0504200f070213060605030a09050c1210060f0509070315090f021c0c08060f0f12070305070e01140d0305040b070515011505031f0e090607030605010507031b080d02 80
    0x2c00c0342c1c822b60400c035034100e403030304003001c0201300d0241040000350190101500e10040c01350350384c051408100b0100302107694190018410600b505014142070365580040d8a01c60400c0e0401d000018170289112008041d5440201000f401c1e55030300070110014540428282e0541e42480400510520a07201d5800c00c0170010501584c3d400001c00784cc4010320030f407940001c00d686011806403800e540b182ca410741110b0100c801c03011105440340002d000c01410a03405038841d1040e8179400c420440045c00380100c13032003901980c2c15150b03035030098854110300748101109402014001401403806100c51305249110b41070840c1030540303a00100c11030303800515007150240d00c003460725642a6032134a1214010030212906140f07164001400408600001d45101101041d00e150300b1200d21900c1c10f400d01821559213100140d180030400c2c0d541d00c00e81900c020000ca8540840030800354446ca003140c2c8101e4058075444840b00944a1071000b101d010740098504050510822242d100c05000a190300c110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 93845036 1250 93843786 93843817
    0x1a1e0d0c0609062a030806030f0d05031e0708010902070c09050103030522050a0b0913050c030f0f010b0a18030c060c030206060a030519080d02070c060f02070f050420 73
    0x6083c0c019080d0a9000408800780d16940c400c0085103910a0410201d90340c140303000c65141e01c034900460701c2c1013182606030b0040c0c000e00c0c080d000302d2503115020b0b620a04080003c0108080200c40103011094142c0d60300c03001500440050003580016001080124032030a02e50114503600c2c200707103003107900130f8100310000380c0700259154007018000400150751a490600000ca986031000044529a07184100210400c001c0b40079422681d0710350f031540d20040340c0c0c1010f00c0145415800c0594039441200c4041507188190f01282816110341a168180c070303442c1c00d0007480d00348403110544d02d40800c05500000c200c041c80000c00006c5541e440c000081541e030319034040b58010f038075020b404c240c0b0081c0194011906100100041000013400ea2002007060507040c9107410705091110301c501c1049150b080740c1b800003450704108214440d40c201105c0050759915172091207818205d0303c1e070b62a4440c1d0400e080399a4424811407501c0d620085009545005c081600340d9240d8280702d0a403c04006042c0f0a1f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 93846286 1250 93845036 93845039
    0xf02031005060a061b051b0909060601021207061805071706060a050103020c15090307140a150b1908010209010306050315150607020d0f0203011a1e0d0c0609 69
    0x1410050104103000a00c03041c040c0d8904100480c801c42c02c0d07031003008200503119a509560300c0421400400c81ea40050645509410145075440503034034400420303004034011000030b9918580132960394090b01050307002d031440c0a0b0004002059401c80b00040d00c0481d602c0ae0b40c08640490384036980d0302103118a0240c00d81070f24000807010725241101543c2e03200d40022040142d950f5420300640c0546030309090050f1184480d64281b4600209025031240d0f11001d0800c0c00020000000540f48140c416180407050000110426494510629004010071070007400000115166040542d03100d03c0035008811801c50b041c11452011500d9004807070031395001482c4441c0703590500880025150603401811003d982e00c01c01e07460904002e201086101801c07603000e01e25504c9400301d484c041d8008203481c003400a181400c0455074040c40040b4401d610344154114482d101000a00311210001c11100c0544250341c03c5134503400420105550140100c1c0c12080090356002c0550040c108960b070756800c1ca03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 93847536 1250 93846286 93846289
    0xc0303010915210204061a0405131103090304080606010e1c060b0d06050105180601020604110301090611030702060a060b180303070f0b0412090b1801021204230f09010b13030507030f02 81
    0x11015600712542200d10305100114250a87c02210b007122000d0b03501c80401c3c1502e1410800421000c4c50054070322400100344404104000080c3c07041d2a0300e002501d4541d00d030311b001501c0511a180032035410400450081600c2c070b550703101005103140181d401081180104001682002e50340004032031850f030307440c01481541480c801c0e4840d659078085017101d1a081c00c100103952a80300800042056034034801c00c1c0160349084d041080b650f50b20100034802d002c02c1c0085600341d600100c610b2401031213404009030442c0720754007801d01140c281d4251a49858030403c50384403004610070071203401d8070081041c03d001504800580011500034410380031542014504406c04503002184c0600300881c007003040c01410b8402c42221500552142e0482d00d88451f030340141d0600000014980b2030103000b003400a91005004201040c0b0424546000c80d0400c904041180b000c2002c1592904820940018001140a00010201d603d04d02d801000c030356959560392850079110f07400480342140305078620404c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 93848786 1250 93847536 93847541
    0x5090a060317181c0c06030608010b1021061701020703080a05040b06091f061211120a02070f0c030c090f0b01020a080d09081602150c0303010915210204 67
    0xc040d184050034948100380501030120301807000403d20620034400d080340c106040800c19071050740d015512041103546d4420240c000c0c81141301e118819420850b00ca01a07292455442c001c2d08800d17200d41420078078136004041c880c1c0c2020070740700a265807a00d022582ea9041010400c20a41d408009661422240790080209030050000d408403801d10061100203607000040540c0900c0640f00c0300300e00c0da41c0c0118601121600c4084800b054600350004c1121a40f041c000f00e14002c261800b40800f00d0542c411110920461764014511038414010030b14642041d0001d081c01c601030f02074544090083d444001c2043c3c034941c02100d0000c04024100103220043c007603c0b8400c42001c1c0104200c0d130703130200080e454101d06c10004140000c00a1409040b003400ea111100703803500715070000d49883c1c0221802c0505002d8080982c498581c040e01290404400c408440050800e54040e40c1180d2905020304081d10003411840e50556241c6000706244180404462a6403420454031192400c5030042c40304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 93850036 1250 93848786 93848813
    0xb0915160e150706050703090f05070602010606020309060d0c050c120d05100b072a03050703020f030303010f060c020310020a0201090605010806060d0201110102090415030b0f010e0109090c05090a0603 88
    0xc0d550306411001c880c0c220b0010b9641080c0c00c2070000c00d03203030f80b808011402401c0522004224441d9450560180000001c0c0c801c02e444094000b003001c10f03140c110036030350f0b0b00866001c10b500400822116008903c250001c8200b01c0c002e0800d00d04069081000d0760810a01d6482c96045410100d9400e18685441c06015080b100c49110a0182030408601150700c3c8107810005d4500da0042540b200024030f81e180d494650b42c0c0701160068a81c0c4c40b450100e44800552005902c00c0304203070200c01c07040c0343c0481128100c41d008101901154503186041e80d1300c2000400a0368140243c1000f512044118001001c004180b07500004001358149051012101c040c0c1010700d040e40210308000c01e40c1c58123140030740b0140d02402c0401d403441c000700585019200e20a152a0003a0900c054180c1e8100c59442200540e03200f140b202540e5500c0105404400303000344a180c0b0a580c0d8172004001925960380b00400c0c1342d0003182a20f21341600c42c0b003c03a0f02e501c41a5005000155100c0d410018810a2141d81c103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 93851286 1250 93850036 93850039
    0x5070c060f05090616140f0f010b090601081b12190b0303031512011b0f0c0b01060e1206180c030327030709050a09020a050d050a0b0915160e 62
    0x840640290740200a070040c1101c1c00e00550303000441360243c0ca484680b021407030390301c15142c115185d054003420b1f484022115001815101c3e03a0003480500c2e0741801008008940901000e009948160045a1840c800b9000c54095418580710140c40d48614000b49448800c41c60459000e0030403070398644c09081d0140b1120040d514246140000c2c0e40d01004480e005080000550f642d496030300c00003041042c0154007005150f01e0040b4a4030300811001402a41d107409494082d02040d0340c1c038041e01d5007910080020a1002510f006126690242180301504400a40f0041070400304100051a10380203490700c40c145952003600c12200d034010021007407805002d4000c2d40c18a0310321074400240b8a843c0c01401102200030000840725141040a031008000b00c0000744410b04001d04041c0082410880c1a0f0140c044140041501d0605240780e9120701c2d0301100230003031078a00f51201034410340058003030302090060f101091440703280f00f01624090030500d4481100150920b01c06411100084e540b00d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 93852536 1250 93851286 93851297
    0x3010f1509091e0906050a0b06130603050a021204030e0909070f0e07020111040f0501081501020a0308060a080d05030f0106090501051602030c06030f0a050c0315190f0605070c06 78
    0x8203149075000940300d04540c0b6082d808214001c000c5911000e0055002400d01c82c01e240a084070240a1070f900901c0c064149080c041140469140c14880b1034420841e4440d1156441c0c0300c2044504c1c40303980145d5000700e01c03620060801d00f8032882d14407641004c2c0c500f40c00103500c400750000d86d8605050020b030044403c40051202c90316100342001c4582c1c0380d101d1411002800000205618000c0d0800703010368010001c0c0c6a41c031a04c48402030300c080105d000e0140000c02c99000101a0040c105003040c048030142c00400a150b4680c5e02180d44800007080190000b94468000808210421280750800d4441e140c290300d91805c40c3c000c01d16000168040010441ea02ca0204120b0360400210340c034070300c4808070421100d10036001080c41c142d144800d66802000000c100004000001509801907c0340007060000b52a07410001b03945000a581000144041c0c8202010343c0c50f040382020120006111143c1000d640d9a20366100c2c141715a0049000c50000a4514100000c0c1c003030040c003801860400c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 93853786 1250 93852536 93852569
    0x70b040327030303050903090a081e12073201060e1e06060a0207031506140405280b03010501030308090f070608010501030507020c03010903050c010b0306060607060209010908030d0203010f 83
    0x200004010701d4070018040c560350380b000c9243e5402c18800c40320000009000b614403560780758038180c3e445840150502002d1050540c00380100c80100b1540123440514503c40d04007100741c3c0301c201c1c0c0307041500b00e0504a03420034209088840884174200d081e01e20204000140301c2c0c517001640300e00580084c1440b1806202d000e0070140803805161642c0c0140c000d1310810785400c03040a09a20704015604042c1c0101c3c0c04100c1403503100c0146c0c200c40d0a50b00240603a6201104840030300c03007960b50503509001c4105050210450f128407001020086c000600404100070b040c0f40086401c4038006e81066000481280401403000c0c0c1c03c00003401005500e5004140d07480c40c200004101d01d4041c01580d0400d5100c030042503600c0d01c2003001e5400410010020000303c0e2542c82c0180266004c80071102003542000c0c004141072070701080c41c9205000103441c041c17030050729642e104000d50000002c01c3c10302503280804202800f081000e41f4076000300100c016a00d50412400c0369110003142e10070302060071203046 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 93855036 1250 93853786 93853847
    0x60609030b011502150a0c0f050c06060402090409060f02090a050618061c15030b0c0c03030a02090a0305120711041b0f1112120105010c0309030312020708070b0403 72
    0x415504507140203c00204425161001300d003040080c00060b150780c11140705000b003040d0281e00c040c20f140762548402900c2c000d04842030b2258001e450601d80107402503000a02c040c117094000380f080c144020300001e85400e590b43e4000448144003030095070039078007207004602402c0c8101074078040c1c4402c5909600f01102c1c00000c114488a282389107000380d0700070500f01034400442056100f1456618410b008545541005110608207407105441100407200881c1c25441100c00311810b010148004e94a96940c9100100103076214181940d00042c043d20004080b50701403190b154004202c900740e81e61281c0c507080c41300e080d2201d43c1809105a10b8100700c2d9071501c03004e01d4840ca0400b21428013010800c200c00081d140700000708184043c0380100c5000100c90b42401e8014503e01c084281e0940d80e030790304c40c0011562142141e5008011400390602807000c2405001e148400a207001405894280b003941c6019640d040244222019900740301440100f64208203504030b00340480c144034810001014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 93856286 1250 93855036 93855053
    0x30f1e061e0a0f020d020c0c01080a05131b090e0f0d02010c0903020d021f0f0305090705030601171216020f03010504020a1503111308060c0f0706050c070609031206060903 75
    0x51282e15010782d00e00c2e50564100c03a54040d0740d000b0800c64000c54558846910040d169036407401d9050005021100040c1001224880e02e4014440c18031801e40060907035960112070306c3e1031007480b000861806e44c0083d01c4e011601803641e4422801c405803002941201486182621320a180b00542e4141030201524640c0a40711a00f1290119036580e042841800400d0001a841c212800240140c10741040d50300c1e004504000c1c03c40d0159801c102640c1c41d1400991241520b0141903415005200108001802d10420045206681c0e0aa0f029058a600d040c81e40d54491a9442d000c0011000c07401c09500e070041d14030009020a5000303000c035181580c0000d4464800c1d0140c2035009111081c005080c510a0303000e104040d00c00f2844503a039900406048940e0840380c0b20350301080c8201b0000400f0007441005a8070054601c41080f41005001c1ea035290103020010601203400c4420b20201000c6000c501074521124025128802c9010f04158460107031141e03500400140059590200300148228 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 93857536 1250 93856286 93856291
    0x303060114071202010203102907020a150c0c140a0b0a0903230d0c08030c0306010e0303070b0f01120c0306020c12030f0105010e0f0108060f030f1e061e 67
    0x9203071981501125082031549401849006040c8078002201c9441c416015401036006500c450a04107110791344040c540356217600c00b5a001d4004107905000e403030b1074442c2c1001c1c0c80990b01c028606040780352100014142e01214600b850f0005003a1440d090600184d08540340203411240c1030085103850702004100464918070402d0903502c400105201010320481c0040041c6610010641c41c400301d4000c2000d0380c84809007200f030700c1c0c040d4007410000c46001c4e0705080780c82c5510404140c00e664403089440e016400052100e410320050103010b540310756080c07008010032071159a0000450401040d401c2d002c00050704030001180100c20040e020034280f0134040122036200340c0159450040140c242d0a00d001d204080c0e811400200602c100411106090b9050b80c20a0381c5d0091181c00c00c5040104007004224084d0100d00b02d500815aa81011559410300030f002608031001c01002840541c607211540d040c0c049400c080901c0221005014070142e40c0100b0342c042240e1010b03040c0c042101610a01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 93858786 1250 93857536 93857539
    0x8070c0201020f1b0a0f061713080c0d0207060311070b0c04050a0b0705011b200124030605060a080d050307020c031504030f08090c060708070506070f170405030306 72
    0x2044000841e0310800040c01c6604055058404890300a000800b90711906a1490301c0344100100101c0d0410802c150a0200c030165540d0b4507402c2d000305244d80d0a1400509002c5410f220180101c0200f42030000030007603080b4400061140d9580001c0c000d09140c55900b19404043c22701c1e02d500300d0320b40542c05880c44150000381015040c0c4942c1900c6116200e00c0e0301290b00074242000008800560401500c1c0341b0740514020f10000c1d900c81030700000c4101d44e18040012030020103000100c44e0a01c0710510044904000006810300c1413840d0301001c4400701000c0000d100c429205000b00601d82c0030f11500400140d498485042c18018103540700c80d2115204010000081300180341a0701c00c00c1043c00c0140050306a507102e20382c24905c1d54840c0c0c4111419400b007100164908010b40c400d4603503d20070409940501009a641010481070740d000a03000d90301c1c2030703051001d40049402030142600680c031548131702e2450400402d01820488400d006240c600381008100b00200300d010080b05e600140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 93860036 1250 93858786 93858797
    0x61008010b0a11010c0801061409010903080a05072f0603220317010f170f0a03120204180501030201020d0c110910091a0a08070501090e0403050405060c0309090c07030807 75
    0x2450300044881c2e07949514803068940c00c0201401c8020f4020742c6c0e00d03058444d80c2d6650b13a4290100b148210301845134480345070000d101c00c0300c100301007140744010f45071b45d107030a1604130314010894035212203d10040094034218014112036000c500343c420010400c15400b903c51a06502c0e0450011100070340030171170f10202844e54020700c0201403081c060300031590800c8103407203020750712607003004840c1c2164001c0c540b507500740100d42c8128940004d111405500f404006201000490780c040740c18007003442c00740c841c031138082c040822040b8000c0a920f200e50400300e000a503a42c5540002454004048828414002d1903c050300c0400c2c2c0c804601d844425054078060910341341c2450b0328146840719802500b6082c540180c04c80d580340f060a1108400c4000c4a91440729521000038a40f03400d52840f5060105078600070402252000340c0f0006da00034003a00b070003400c00381d0341c00101b01103078482c0c40d4100c4039400000f4402941c2c5082001c03a9082704070000614103100d002d0350086c0c0040c10140c4414180b00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 93861286 1250 93860036 93860047
    0xb0702060705030a0309060605040504052104081009060c0503012603070b07020f01060b0405010c0b2706040303060915050f040b1003060e060613060507140304060801050108061008010b 81
    0x121900120348a00b40c2c01811240d81d4800c03000020300806601c0001c842a90a044002411b13181a029032030042e40c12202622056488030380300043c01e4610300300e080340c003039080c40b000980f008140520741d002280000003294152941c90a44100c940703034442c035070a004040c0014051084490048840144003000b103900d5950540c01c85407841c09104c0340100302c606403104000c0038982c042207903110b01030701c00000c0c011642c9516082c0d61070b00490141c0350005904d0010b2101142c200c501c41034112034088241070303450080e410040001600742000300c4559100d04180000c050749840784200030031003881d00304a58a0400d402c0d0070346120511486104420501c811030381541c0d5584400451040201080881107140501801030546840ad8041d42d0f0314940c000b40d1903061107403c5920140000c10301a5a503800c1203c25152500b0840c8207131602000d0300c12042a4407401c0004001500c466182c41c00343d5031429000419000008000c035014103217943c065111182c220380180d05460b00c0429480d202c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 93862536 1250 93861286 93861289
    0x1a01050a02190602070506060d05030306010c060b0604080304060f03050709060c02030118151808040e0705041502070504241a07080415080609130816060e0c0f0117010b0702 76
    0x320b01064241c502c0c829818500401c402e0f580100301c1c4034400c3c0f05941e410399508080000c00b4590743d0b80a40307140c10400002d40c4030740c0300d080380940f0300f0f225110014170007640002240c400e801c81d0f0488881a800050140300168112112074a0402d651409200c1403400890040c60400580f0808050220400e001011075500390081d03c1c40f10f0107a102039102040c03d0a00320040020485800e003054640024142d00850341154060f01581003400c0ca49860b24148400188400003803050003000418071000c51021199100c1600952481e8000c1c407800c0d0601040204a0701c01c0002030f25803001601c0020785a1010159080480d1201c4500340d02c0c515903220701700407074030030150b00504021002801280c0000b40b00001c503942803441e51102401d42c2c4c1c5c20188402c003d000e80704482030161009890700000d605d88014807461842c0070800b1043d440720350790107081da0b43c5c0307a45a05440e045603044c02c3c03107800d01031194074040d1002d10304200140340007200001150300600a95001074000103120702036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 93863786 1250 93862536 93862543
    0x5100f0f06052b1410050a0b0a050f0304050105060a050603070c06110405150d0b090405070b0a05090405090a0302100c0e04020d0617030a141206010503070908010c0f0801091a01050a02 81
    0x907103006008040d02820100074000a059584d015030340c0211440c042a040440310b00040141c48014100a210751b040c0700c008141078010070046000c1250411443c0101e02d002d001a41c00740340b14600101d0141003120421002103004c0d0895802144240300708104254000f518602880d049580000c5020802c00d0401d02d40c400c80d00901c0d04004000901d0f5200e2000d07800130100c40407907580800c0010100c808002080c00203940c00b0300f07640e02c0030105105103140744009205051344e0b41440342c0340000d103a000c00e056500c21035043c1d9983e084182100189034050214840003100208204024030756403034003509029810300e42030b01842c0d0200e0f64920005195000a003d4604001c03180d610701074001103a5901e40c01f24240e000040c03920025141c03100c0004003610402e10003054905d905541c0c0c200111250b80006143d4400c01425583c00074090400380300c1e2441d00c1103103642e0a45009003007080540100d00c1a880704141910b07001d1115042004c0100040b060002440c00f25920003c81d0003c07485c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 93865036 1250 93863786 93863827
    0xa0c110d08043804051002030403060609090605090607050415050705030c07080d050408060a090f020907030c0e061303030e030f0f0c0103180302151b0d05100f0f0605 73
    0x12620002e03010501070684800c181c41d64000014048036074010801c034140c948101c410303400b82030005001c1801646098a619081d640481c0304032030600d60340f41c83e040c1c25030310f8541c031582407582d48206540900445000e80399004c8200c500814090400107801059803040707200302000c0c07440c0e212241e14950f20031003c45456a400104503511090016540c640302e14484c403d8407040d104402c0880360f0103001c0c1003540d00f11204440500a00d68540001c60050800b640080303c001d040c84003081e005942d8a1002c6000383c4075542e0001d580380800d83d014004010508103036101d2a01840100082d10711101c0c00d40a40c5d5051810b10001ca41e41c501291501d0741e508600c0ca528000c1000d0001102000a20114400e400340c0c3c0138442211040c58014900c40e110074080c005800078002c4440404031030303420681100e1100c102e80e080b002d03242e11884564214102038640b00343c540040c452002c3c0360100210140405c00c04840006142132004400041d8510030f500c1442307004140762000f10408484501c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 93866286 1250 93865036 93865043
    0x6030703050a0c05010e010c030c171c050615180402070302010b060403030f02060708091b13021c05011a030a0903050403060e030d0c230d0e070308130b0a0c110d 71
    0x8240070b4403032070102c00a46241c0502c900203a0b0b010415103140d0720883c0500d0505400d621028010030060310342402c81462004e40d4000180100a1000c0d40d40340038501401d811012030300007400307003000710401102c4070008014019002003802142c6040c8050300003600084000c03140144e4489961905a000d0305808d000319611034400f041c00400c0c150409011380c001135107542500c01d01d59810409403041c40060314a050584d10441070888840107a86c5101030350b800c010001d81000c0c01e102041800e03a44040414000700d5010f07080e82e50a950140a0313140909036200380b540e066804101c0a0016000080660306065210080c6105141c0500111005140c00c8035090140b046e00644250340c96000c440c0e40310482c0d1a00180008592043c042149000d06240c10034055400307501c01d00070150050074200e009107a480c1030654960307108102c1d10009500c2200902d440754031445400c0d1050380141c0c090304023100c0421030350600e5540035612946940d4401c0207410044030b80c20210b8a68440410000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 93867536 1250 93866286 93866293
    0x312070b0106091a160201021029030a0b0613020f030117150103020906010c020103020c011503050d090b0901030515090403020c040b0d0206041a0f03040807021314010e0603070305 79
    0x441485038120090307068840300c3e00c441a50325643e650395006681d00d018128100c1406000d081a0022100c007400c040c20300510498110900c007940e810110343c0c100d84079215452141c0c00058210400002d8800500011800740c002440d0949450961840081446108201142d8a210380203407a80c1550840c008103c16a505c0f9a150507a805540c400380710300321024400c17407441403001d40e04048101d0680741e0161070b0030303030319142c2030015200000c14035400ca06164007803012207014a42482250443c0b0200c8550744800392940c18403c0c10118203403140341c1004110003060181c5014542203a402110071b182c005002c0d580e000c00070400c070a44948482d48004a4810700081c503a0010b24035644a0048400f0052030101004010f40b642c0e164000030341080051000700700c41d00c0405000314030004d100f400c503443c0944c00d4030310000b5070b442140c0441b001e600c04580340041d0b0034002c1d020a040b214404080141c1401c01c046440360420500c81d9143c0701e41d4446c0026003d407414064000113541c040201c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 93868786 1250 93867536 93867547
    0x3100906060909060b0313060c0201110d050115020d0206070c0606054b0f0303040e040f030305010f050d110102070801090311100204120305030402010219150501050f0604060e0312 79
    0x18101e00141c4a041d560f50709200001c1076a105403011240500f11022245032400c0240e81c1e1728000c1c11140385080255583c5080c1e01003a50111030040c1005c05080d41c0000f85907050205002021043c0c1820200315030119101642903600002c481d60091104e0500c51900007462030180c014002c59040a80c119010000d5600f42c840030a402242850030b9006c07040710010217070002c1c88040d4881004404400078601d0b40d0170541440340c201407624a01071306680c42d094840c0032202254100382d4003100c1028104186e0403d040c1d26100c1c4601420540300d0400d0841d107010700054100c82146806001c1d410014109441a8020007420005050b024001d029003c01c0d400d001c1c11a014220320003032180908865a03022908500c200c506848101d1045000d450703003606c048400ea00014030481c150701c240031014000203100410421000c2c800c01c4144040c91440041c039007502d038184d020600520141c88640c0d8560390750390588080c1c949500d0880e01c0c000380f00300001c2c1f80145240c290883c3c2c0c0d00000300c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 93870036 1250 93868786 93868799
    0xa110702060d05060405070212040b0f1b0607020f06060a0b0309010905010f0e0709050903031b0f04090f0f0c080106110c09071812030c0b131a1b070203060c03100906 73
    0x3c070500c9600119010411030382c40b8201a611059801c40c80040174404100500600d0200740190241001c01c031380f42420042da0302c2c0c84145501c0c100080803850361110702000210388e410801d402e050302d0a0009083c0324102031000c00d41205860088481060740440007c4609100354000003a803604070000384401500640050300500d603055542455000300d09002c84c0d40840c5000303035402010303481c0085280d50b451040b4600c071000c9040300400c204004124000f415816140508050304e00314800060b02c260b81c1500104a4124106209460b03060000018002d5008605641110b419041030402100c0c10420a810032168100150b403002c988070600500603448040c00140b110412810071285442d01410170603140b54290060008410380c458200040e003100b01980c0015408090541014056075460080c0603201c85494601d141201000020308001150070900613030384540ca46060226004a41c0b0342100030450341c1c80180020202e400380c85204140001029001d00411403a601c502 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 93871286 1250 93870036 93870041
    0x909030e1810050301091a040c08060403170901150302040e030408060f0402010305010602070806060d081c0b04050a140408180604060206090c060a020a02221a12010e060a110702060d 80
    0x2c1e205185034808040214190805115280103075030450311211a00c01c1e6080880705180b4010310446141c400a540085c1e0a9410800740340a2407180e140d240f00100565101c5449000040c182d101680c100f580d00c001c0c048a89140d40103a035015100402e01c0360741038450911314070942d8004003040c0315050800c085160900d294901403407013680c082c41aa40d07074009c104d80e00d260601504426800400100d0018034150001c10912440b503090305060070440c801d040c10150010082d480560780b91401c0c42120310b800e1040c036500000c039540400014905140c40c00761020018002800302c140040e4500b043ea40d00c1da4001c0c49054010800c940d5681c0b070300002512030405a910303004da03201c2c01420800600e040d000b0748440c0718081e40100b82c103401d56020070225000e00b110a05000c84602c402451aa500e80500400000a040540300060100c070034070030f103505801540c01059241038050490902c0108007260030201114002c1a090500041c03080f00b4420248002d43c0050002544030003404940c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 93872536 1250 93871286 93871291
    0x40b0a0207050f04020a09061b12020f0d03020307050f0306060706051609050a061202070c170d020708010204030f021005040b0706050a0507020616050c030c0703080705160b040909030e18 82
    0x1e46400f141c460349101444268010180401d002c541034480a100d10f81c4904103070080303010f00d0380c001004816a511540c10074466030101400680100388030014041c01001080d01000079813508508e90310b4a02c500070014000c090440104103000000f02e03191396620001e5a86d2503400820400190900c0075900c9080d034a00b4803103201061040781e001505160170305011085420760749402910002c2402101c2c020760094004407041002c1405c00f080f00242c040303122404600c05001010004c080c05800f905d001c405d5804503e9607801004240b00068125292500c060381c1610000f062068100095620303010359089a030060401069034000d0018640089003d010a02d204000d140c0b1001412a1502402c640388492400041d0b080c001c094442d40080c820321010714190f03800c00d185c07010b4a90800080d68000c1da040c203130110392201485828404039001c00940090341c0300d0549031003000041c90203940b08400308595203440203410b02d8028450b0f020700e5007004014940f00c52031020001c81c43d0009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 93873786 1250 93872536 93872539
    0x1260d05120a0209090106260907080f120d0b0607121d0405040f081b03030a0e010b0a03051b0d08030415050702190f0302070302030a05060f0622050a02040b0a020705 73
    0x400102d034090409100f1610240e20141c02d0a0303160b03080a40a039070911060220002e00f5401680300741d907001d1004a038038041e0708540080d000d042e107003208442c580202e0042c41202904880b00714621001e1070021595038206440012410140500000b000340c018250050320074005280b2048440758400a800c004114040c0c0c0000d8400d00d86041c0011248200d400400c1c400f82e00c40d6030404180000d024254402602d0706644603400d1303164045080d60003d039190340c5000d0303d40b8114100c2d0301003030142d1038085d0000d448500c0c115240d901c44560f10800107200007400020710000e502a03844500c44002c0c002c0d0014011a60f80c1490b10340a01940e070820395455069240101041c4040c0c80450b091805a0a01261240c2402d550b2540b0b003540c3c0800c242141903100d69600080181c03424802041c20a0083c0094070341c1e464680b2071301d001c02e6401082d9900c80c410b814880959802c08080a01e034555852030000340316660024a2402071003260003c0c40103410218865071002d50000c0e0080c180c820 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 93875036 1250 93873786 93873817
    0x201060810050609070311040b0c0c03190b0c03040615060c1a012304020d0e0a031106040308070302180301060b040504110304120c051603030903020108180601260d05 73
    0x141c40c11090407070b1420b072160b40c0d03c816010f0100700914420740000c444001487c260324545551500703901c230745500801104a25401c100e280000300d01c5d050006800140d080f0740303030180301612681d90441d450801800070f0020030000c0041400c0c40460781c4510303041445040c0c1c0a41041c0c507030b003024146042c000070440c0c40d5003898055009507052038440c41c3c100c441c01020700030940b42000c040000e80d080d080c101c07a0010780c00e010b002034030700b1140039013031154421034080c001001103802c1c0102101150000380a09134041414000002d9100c402039500002c18600140c69240c450f0700071001da0b5502450715455030078084c01003a2400c0386000ad0040b5007040354104504c42202c9920240b85c042103c2c041c0207941048892242c0c0d0b8081e040c0c08500e40e1141c810f40301480b040c80414020072800b60000d40000b00005410710031035801c010b076207402c001e0010302d032403411507614505662403405005940450300c1c50003c0c031100d040c0e03071034403884144400b4050f80c80c50100600001d001d5081400125100300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 93876286 1250 93875036 93875053
    0x10030b0c030402040f200d020c060106050304140c01052505070b0c010b0102010506031005040c0320040605030a020916120e010c0206010b0703020705101403090f010b040e25080d02010608 82
    0x9a0610a2411141c046c01c001300f42440346a8040740103400c0307100700d0940c00f0307001c00075140765407828040c05001e80b00e561a031326128203090a1501804281c210303030380d10a5201074803100040e82c00c1819202482d41c0c00e500000321003001d03c11602c40c0828104001d0252003000d01c049030040e080c1014007400e28184000b0001e102800d001203003614019079055806030007a200742d90b42c5841640201d03a02c20b00503903500c4072941e034a41c0d410301d40603083e12103220f400480b40a5a00c8500d0076004507401048111b00408600b61613400240382d221001e805035030403041c80180241402e0003204140f01080354900c040040c4074800084d00d01030407502caa0380006005181c00800c0408910060f02c40107a0198000c1c007485060005100b9a504910042c5090046418509002200d40380085104540c0c02002e0280410340748052400d5804621109100c0d9042841482c105440098a000813000c00780c0785082d44404100190042c030129003181005014074500041e1058054020038204c6503108200c86001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 93877536 1250 93876286 93876311
    0xf09010908030a0908090901090c0e27100909060b0f2e050f041419080a020906040905010203091b0a0b030a05040309051207050411040f030b10030b0c03040204 70
    0x2691100030081941c8002d0002c52190281c540c092004103104210192810500d00002401c0c54026403003407818584917600c07a40c103903521419024801c03000b82d07810010403412040703001c0040c0c070780d000349042e1001c00c40c0005d0441c10b04500210040030084000c0105207480c3c28108094244a8a8a03020390221480c40150341811114480711a8003000710b01c85481a112032440044415207030041000f00600896008102c0c410003400284520404025202c0b0600240400c400c05a202c1c0500c501c81060308001c4100e0100e40b2024081d030444916903996140380c0010014455200c01400b90761001c0104210f051340015403602910700d4000000002c2c685134100804203029010b681381680041c40820100001504859041442030401d20003464844001ca124010340d03002403d240d52082008201f40e080c10310a030051b2448100045252504050210310390b00d40c1403100030b102142280002d404e00c200c011030b58014551041b004480c5091800a03141e0030741041d24284d1065203410344a8008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 93878786 1250 93877536 93877541
    0x31506030b06120d0c0c0807090c0809062505040e01030605011a03060a03141504060b040c02010207050a0209060111030403050106150c03020a0308070c14031e04030b06060d06090c03050f0901 84
    0x75050f10000502d07a50640010403200c040c81803c003295517102034000482c00007000d001d040060300e01000001021808880002c1075030001512500c10390f04003000740302e03d0540e0032a100703110181491548840f80040c0358111010b2013640e006240c0c5540b0b9400120800000d504002e04030703002203070b0725040401202c00100307480c481a5260b95020140c0c0c54100006031a03061540001c4509405841d640ea0740090007100002088800700c80541d510803980d00c0d1442c0601c18420791a070144003c5040805903a11155142d0082c1c2c4040c2c0319003161070001e81c45a05c148900400c0e442da110960340c64030754a1030410302900107030264607000b21401541a80300b500c50601030407182d8155008000c001d503203403001e5481507000b0307104908120200c40e4a03000709403244070f544040007240c0c00840c3e4030045a6045600318040115824000a04100c104081016250b2070754100d90100c4601d680e890010110a00400480e0700a0300034a0034282245081505980071a10980c401010140165180d01003a0b08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 93880036 1250 93878786 93878809
    0x108010b040b1206010e060d0f0606090302011d040b0a0b07050c060c0d140c07030c05120601061e020102040905090a020f040b0a090b040e06091c030b0f010e0a031506030b06 76
    0x4100c201030040c00c20140c141041503420220604002c0b10141d1b046c40426081c0d400101805041921403c400030316909620603107005201c01c3c50120b08003811980000c200100140041c1e450581001c48410300d030352180c1c4403d5030f03032100038294013100b550307134500e548180c0104000b070b1014000d188100e074440c20400b04032400d582c048800384c0034914001b2010b40f15010280f02809074a0700a0003004808101041140e0286003d41e4044080c1454a010002c81d812414100662604900010070009412a09a43c1d0204604145550502002800301e009000301e40c0803850382c0b41003405010071580003003810344144c1d00a40720170b04030450030400d2100381c503200306070701d904008020420480d8420301c0d848081c02600c000c10100340510191400d500e00001640c1d9a440c680180d0039085802600d0f5039218600c815504043c81600d070136200060240c48070003905414040100f214103c19924610f0000180d5800b103445400301e13181414090042070303940130440e02c40301d8500100f449407030200d15402 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 93881286 1250 93880036 93880049
    0x30b04031e05070b040c09060909050606101709150414060a06032604050409050f06070e0d020906010210050a0c0e0108061003020c0a0812220209161403090c0108010b04 74
    0x180b4000035584c0700b8a440000030010748804d0180c0341c011500c01c42e203000c3c034001810a442e02044840c0a03041640c10003502510a501c5001c01c2c0c5d400b0030b081500104908141401c0e0340c0c0c3c40a082e61103200c4203042a5101c00d0451038000c9601c01c202c00c100c4201c80641e0a4036090048800380e99032030060f0b0f01120304900025159a2682004880302036000704440c86001428804608082d91000071900f65402640110307011381003030440d04000c2a04100b01907011000b85008081d841d10000880d8640300c0284000c1d0040d9500c1d8006105640200301101e40c1c40354480c2e081080b032074941e0300c403001042103030f865100141040d8400c4000358404c03444d450240d480140004035103030903854242c00950140000c0c0243d80641250304010894010241c1034108690001c1102483c0c001e03501480300c0044d05007410041e080075424400340e11051001980010b91401002c00d0004aa9040c0c58606040e906a001c0490020410400c0c41b008580c0901d411000e8a554000f80d88844003600907004034004c0b42d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 93882536 1250 93881286 93881297
    0x50705010c020a030f05030621070915030b240103050406020708030a090201091e09051302060d05041106070308060118080a140d021c03090602040509070503160905010c0609170301030b04031e 84
    0x2140c980b045015480481c69005044425680d078bd4210035003909c4040081c0c1e010048407801c10018032400d052610f500c0050314074071104841030241004d0700555030111841c10036a4a0740000c0800c0b40c990b0449201d29005680c482e140e2425601031406031401d201c0417030000703840c103400041800910b464942103000030403a908141d070a1005140041030300400080328134a40340c40d10320168650000800c11204100d202091502d850f0030a0700d0100c0845080b80d001d800c0800108011980c01a40e154001109181c856030800c00e20111842c00f541c60741010002d4000c5080d800100f00b048400b001d0320039500d105607801602c0000090742c803240c1c040c0c03082c02e03903540740d000c00d030041ca200794030040038039100718801800d01d074581c8040f8004510171185e0b00007140000050104d45c2450300c044007160074640c6030a2401606120008100074940000204260348920f252070401010f04c10700300c46640b0701c0710015100d42c0d503410001c4d0b29034020384007500899145402807040c1354104940240c0b40300951140d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 93883786 1250 93882536 93882559
    0x3090c140f0910210204091208010b070206040e0714030903090f0604060e150c030307090303020f060601050a03150909081209060c03040b091906150602011416050705010c020a030f050306 82
    0x8840b0b803502894840448801314054880181e480d4032803802a6801050450220301c29120701038050113041e0800301c2000c50a010b00001a5204c004680030b4070f0031182c10365056104c0480c256648403118003504110440801000456000007002d0251410700300c2d82144200381c0b0b142842960311440c0141400501a005019a00e0400c00f48052b035861041d81c00a14000c0380340055402c642007a00c0c910000f4519200800c01d0544c100181010200180003400da28100f42c00040e015125030180ca2090580717440180c41221640c2010a0044c000b820041c42040158604052541c2c040d03207881e5950000040440c1c0d80003000158144550020304080e85951144d07141d51080a80081080708035125500550300845c0502c40c0107084548100c03000300308414034400125100e003294104000b168540038840000d4080d62107065000400d10540a408035420241140c140c40b030184058200d601340404078202d25070006807610014000e030341b40340480b600841c089039544000e580076684403004030031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 93884892 1106 93883786 93883799
    0x105150f04021318020c030409050708010e010f0b031003050a05100f021c0906090b070507050c010507030816030e0a03021c0e0303040b090103090c140f0910 69
    0x1810b500340721056599402c02141031081c007008180c506200d00740442c040c0e04031420040341c00c060b44c1d80c0326194040100501000d4480c0000190000d00000711507030031084e2070707060f40c1003d0a00550300703180c402c10b51110380020381080c610610050380000040d2040140c1c443c15481079001e0070840403040600d904840c1960809583c4500400c1144980081d800c214801d00713a4400002079403005900f0010700802940000401d1480b00d00d0a004c003040c1c1050141c030103180f0507411214240501c0004441900600740000c0100342140c000c1503030079092055440c0d41208619000441c1640c50a410b4030b040c0d0454025005a08078609001c410185d019008680094905180e80182c10003800700c0c0c0d07284214400e0518240001c038807070980703a100390060342d001500300c1e0312100740b43e45980c00079404480342c0107524411040c5500007800c40c00c000d440103105a0048201007142031801d0b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 93705036 93884892 := by
  have h0 := BRFrame.cov_init 93705036
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93705036 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 93705036 ≤ n) (h2 : n < 93884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
