-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0655
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:57:54.003576+00:00
-- url     : https://prove2.me/submissions/b17c1afc-4365-449e-920b-22a314e3f74a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 117625899 ≤ n < 117805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 117627149 1250 117625899 117625909
    0x503031608120106080f01060f171e0a090309080604030212070602070219090509030a09090905120706060f0f030b1303030b0d030905030607230702011e020f010b040e0d1d 75
    0x4000e20040e05c41009608000600103120300050b00840200f0140d480c0142a282c1d0000078240c000c00d45040b440c4107a15803c3c03240104040c4c0f0082e5006540d2114140038a101c0c650f07100319000344c02940d404803050745440c2c040b40c90b900141e401600680c08407084019070700c0848001c0282c2e40c49824010301c2c1000c0d0754080380000d0701100d8541c000311018201080040c01c1030041985c000040c03c06580740211844d0080c1c020790080c046c0c25142e5a40b010810b01300b00081180040b40d000132a00d064840b0410718200d4007406a0b8022005d030b02071a5100002c900d070140c00b03d5816a03520440c0a9465a14160303010141c0b85802801e038205622001854400d88400229030a460b01980c1c8811000d403c06080c58030b0300302c01401c00c000700b10030300203040070050900041ca40e56040b0024a181c1d68451400100c856100d0304080283d00380c00020080320351a00010b0203411140f240d8000d1090502c0842000104c44014040407071503003000e007040210718483c000e039081f400301440c80e9090852508020030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 117628399 1250 117627149 117627151
    0x40306050c09040903050d0b1c080c0a050303160f0804030906030c020c04111201140d1214040609051003050c04050d0c030b0106022505010509090411220e0106050303160812 76
    0x10b40880e0000442c1f00c24101c1600030000400e00c2984d9122000210310790080030400210340140942130049007401542d80d0034421507103070f20f070000d045a442c0d09088200c4140884004c100380d011510303810b400503410b4000d6104911032030f0507840744580c0390b00e4800140c020b040f941d420b0f00210301902c01522001c0d03455116502e0050340d40c8003601c0d1112103038001ca0f8002c07070701038200d01c0305181d40c1072084100f03a5a01c10f03901c018075448915100c078501c041009071119802d01c80541c00c09800400c2c041800e95011100d241100d0303084820a0000040e100258100c0d030003500c0c01c00122004000501090410885204000c2d01c25891030820940e01d8469100c0c26100307800050043e080892902058410080d9102014607001410040ba602e0940003800d0b611039038134503501803006140001c0c1402001070845c0100100030340113100e00f10000c3c5410b40781c908c80103101d1084a103840c150386002d08052080000792200030b401507241901109180c1c031140b0a030a000c0b601d8200800c07014840d68195440e40d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 117629649 1250 117628399 117628403
    0x60f13050a061a0402070203030a050c0a0606150e010503060a03020f1203030c0d0e0d0210110705030c010605121605131b020a020f0111030307140c07080a0203061605040306050c090409 81
    0x62488601d10f4603003a185007500d80b03144240c1c0181300c507401503075001c41181c00c2d0740124106203685080910805050509011f400340c0407900d070090002d6000d8031012410302e2007071540c0d00c6c1603102c0c1d03000c8010b4072030f40801c1e00d945400222001d4248014148500e460080460040048940f8112001d045155034400c41d90702030b01c1e880c08600e50414440d540100c0c0c030b14905e0813028022244050900a5987c0c650808000c4119140c8030188d200c00600300894401c550010252540c641440e101d20340600300d1480740f0b502400132803807000461200070907490b070203446800341000010300d407400700405007c5503c5580c900d50340d40c156002407041e400042507180070b02c64002e040911103d004200a9000007100207042c480303201001c00d0341910101c212640003500d0b0508603c01c81c0f145010600f0b0340103050350062030384502c070b81c040b84090300064500503030b84c801c274101d03001661240d48290b0803041210008003c100e0520007880000c1203500701507846550603840d0707410410b40c14006000da54000f081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 117630899 1250 117629649 117629651
    0x50d090302010b0a060504060503240d0807021509060901030e03160b0f0609010e0601030f0603020303030703020418020c1c050702032d12030a02090103020d0606090f0602010608060f13050a06 84
    0x1118902e06240c44c0e040c00078085800c1107424940740c030002906510009000c00100301664802c0074400e61802403030003a808014006021660841c60400c0f10b83d400aa000e038810703941680000308010001003110500d1740050050b6092410250040d4045d050007446c1c280daa000c180290005450030416402405008282600382400c0c40d0203207451028028100d123001d880c0c8840180a01002d00c0790301d40d0030000a103400030b20f00300c4540c00400100b105410003503042c007000088c0410315a05801070310548803925510a9010303a41c003815030891042c1407503000b4642020030102c0c1c0d1221104980c05042d8500d042c951f2071b2594580c00241000b0500184031a83d60100c112899609000c180100c554821180100800c20848000124074003009154008168000134841483d074800e8056821011300940140f16036a00e400004d030004101d401050803540c4040000191380d40305008001c102c64440c03000d03004a0f203500191214181c0c0080c000120fa41c2d50030340303100000c1c0080025580903402410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 117632149 1250 117630899 117630911
    0xc0516080714030918340201060b0403050c01050f0c0f07150c260c01050a061d0408040509040c03021305090106150206060904060e0d030b030d08040f060903050d09030201 75
    0x703407103404900c2c0300d2040384042e8018443d0f0241d64441d0b180b425002a0f14000c084516910a0404a12501714100b0301c0c5c07030301100d900c842c401609000f20381444030b140b54001388841c42e12800345015901480c0300c090000ea100d00d824407080d50041000300180b4401b0345041e854080000100f500e40480c8a299980a9204c58400c20003040f0100031408401d600740741c04080c800090311411440c00f05920b444d40e82c11030200105101111060407100da00707070350000a00840c60041070702c80080a44c1e103d03140d0188078100010381e540c4909035406208591000c01070b81082d00b00424010401d5000300300302c618807081e05020000d0303a6221040817101e2400380b40881d1501c0d11038001803e5982c140e2004e960f030420440390070305041c0c0101d07040d0740c4800282c90f08242ca0f919814118058050030600c0b5181d4001c1c1c01d41209260f80c15000180444801c2e070403a079507003000380c008480040e81142c02a2444042e6881600050f606411503881d050007480c0060402c0308008240c02250328112085001d40e640785 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 117633399 1250 117632149 117632153
    0x121309020f041e080d0306080d081f030303060f080a0308010e040809040203010b0a090506040501022e0c0206070f0509010e130f051e01050301020315191212200d030c05160807 77
    0x800e60317562854144880c900d4200c02c0c4d40c0e180d5185000c481440006000510103540c0b40c07428021024a5222100000d40e480c00c5c0500103000c0c60043c01682620040042040803000079021703c100e50560b503030440c0da031801100392124440070300100c56000c0b08001c0107020359100d0010714042d09101e20703002ea9a8010001c040d10000b500d03801140105030034001000f0726a008640c1c030758000a003010a004e0781480c2903c80040540a030310035401c061401000341d0660382d000420511500c4191103c21149804040a46aa0185e14601c40c0020300308500c0900504100c06805d401c9120640046440130400080405444c0b08a8001800c400d600741c00602c86030074001141c0c010310083d4000c600c1c6081c4075560710065a69040c02078005d00742240c2c80c06880403491351000051a00400004540da450325001408002c404031010004054800446038451040d10440d40020004020002802d08800a401408507514ac88040c02414415101e00440e0340140340c0504d071044503410740c0c40400d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 117634649 1250 117633399 117633403
    0x11b0506010315051803030a0c0507060c021c020f120a020f120901030b0d05030d09080705390d02040c02032206020f070b040e0415020c0708121309020f041e08 70
    0x1084500805000c1c2c1001752580c0001c07003180c2d0031007070744100032440103c1c044042c4c0703082c49034000080109240c1580c084c3c2840e404540909004018100c0390480c15450100b240d4403000940410507580001ca034000d218101d0703000904140c64580141c076100d10000101d1414900c0281110a440d400003c08010a6034188115440d06200f1a42c005105070181c035459070340d000345286400001e641e03104071414000c5000594800d10b5005049071045054038151248004642449070122104c1c254800807840207441c81815029002e0081c034809a100c1d001c00001d0060f4038401c2c402e5000800002c010880120300780100034608880003d260b910304000245030aa00110b00035941c0c010354410b10030501400101c40807205403040c003103003030b85660030106200071300005000034940c80040c101d4071036000440c0c0d850441d4103040a80390000c0c0565041c100030f104401580e10212804001488140300c81da020708041d0107095101414a915500c641d08803030004030030804150381c55141080303031b4841 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 117635899 1250 117634649 117634651
    0x103140102040b03010b090105040f03030309031202070305160819081602010b010819020f031305070503120906130e0103050a0b060a0b180f060f120a050402030c011b050601031505 79
    0x980000c600c0c1601d00b103d241028041030140c2c0e8001d61000402c0381d241da110314282d034080c0903c811000c000c02c0d41c92401400506071b001c400c80100d400f1152101184500e8802c0d10b10b90760301915141c1c030b010b070f40212414003a10058012582100c0501004002c206030000e803603001043c607211104582807648501d080e1005240c10581103a04001c1400e40a0740c1c4041019000110000c1d0342d60101c0f00d00c2c4060700a4014048032669401020040000600024020801032405031040d107210f0340c4c5460605031984000d900c2d1145801007001950601d0a100d0004c202102640040f00d40c04c580703c40020081c60002e034010340e5203a004818070020300041821468000f007040342e042040f0352803c01200c0c454042c034070860700e10f0744030518004000d40740c0180154520400a11041c0d954042c0480c0902da038000114103c03c0552400c00212010032910503a40034940081c001e0080c2c0070144011198102201c1c0b0240e009180c03080d03032100003a810002c0c0b0b0b000c0c5100304144521940043e02c840c0403290 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 117637149 1250 117635899 117635933
    0xe0f0706110303060d080a02030d0f091202010b010801060518030f0a02090f07093309080d18050409022805090702060f0a0209030102310e10060c0213140103 69
    0x400910405980301d030340c0b18a005e64850384840e2610b00480d01a03066004540c10366801608200c005940c0354800c0d4080c0e021540704030407100b90030301241c0c1c0807400c171403d13200c40740c4c0460034600041c006075001e40064a00c240000d5841030402143c800842c0c180301c0c107405240d0007503006030381e25000c52400b000d0b5035900c0010340100d214585840f0700c004007403004074402d50201021601149111514140156105000711800ca00b070b00e61903d40c0003000020f10740300e00002d60003480d0880624a1081440303c140b0080b90300c0f5050a9130a0804100041441c1803049070b0080400911800d103100701402c11002c201c241008980d003514040130701c104124024110011500007808020140d40154131243c0c003c03608840040c3c484480c50013007402031094503040f0000c2c056040320081085400000d100d0904003134035081c11656610186240c20300c000f40c4100440d80281c000501c07069110f910150f030250b0005041d481030000d0002580101c2e05a0190300b10458903400040c070031301402c4580220120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 117638399 1250 117637149 117637153
    0x1050f06161a0c1201031e051f0501080c0303031b120f090c0f13050709120f060b0301050126010b04020f0702120309061b070801060e010611010209010c02010c060e0f070611 76
    0xc0c1800e440e100141c41305010040070542401d40071844401c440030380d81c03909075024040302c2c80a64001d1002030484000e1030400c00c030324100400410b0304400416a042c0c42c01c4050015825512902081400303602c96042c2c00084150600c4490700d404e164000380c1d401203101c0303191725519050181c0040e04050080900c03d004210003070100c3c000307440d06808040c02c503a044100192503140d4650403900b00da6180c0c0004801009900c14a003488035601891a4941c030030b5104000103122072080c5820380700d09108616601080403006807600d0407d200045011300442d000280c00d220340b800040481e017103442c0400150001050030740031401d2040212a8003d03a140040d81050258800680d081c8540c020030020551255a01117490104104010203494040001c0c8240394032580400148102403050600254504841c0501e0341d0f0b0610071034160300810394403141508810b40065411480d1a6411100b6a0380c40700306040d00481400742c043c06410f010081c000d0075141c5000105650b810114012246d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 117639649 1250 117638399 117638407
    0x614071d030105070f050306040f0c050a030623060a050408070902090f04200c01090605090105040308010b090a061b061104050307060e0310090807050714151201050f06161a0c 77
    0xc15000013010b0700c40c3c0002e24045640e56501004200902014580c10744049e0801282cbd01e5a20f4020010705046c40071aa01007190703c2d0b4469081344015034140409003410f46d00320880905003801d100515200029040091500c1e0b034400c1c0702c61402c0d40e0341e0300c050f02155000c9810100b52500f03906906410b4000c48041c4800360f00b0302c00090118910500701030100c000003841d00502d4034290001001c0e950010000c115918048406138080c0034201c2f070850014a28400103e4848680000c1d034001c3c80016011152490038a4000d40e24402c100708200c0c1400c2c103030350300c0e00f001802502468180d001070395486601c40b807418061500e444141d80140003841248040005a5240001d49980d44020080c0100f4035214505005685116901d00070341240600600466000500c01c203107001c1050680c2c010810340c00604860000d401440f07075181840e00701d0341c0100a140780c003484150881c0c13002428a4030340b5441040b04640010080c00031200843d203001c8441d0f091b10d1040e22140d220504a010b50320f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 117640899 1250 117639649 117639661
    0x6092a0e190b0a03063303140406020304020a0f080a020904170c0d03050c04061704060902120106080c041a010309110303040906050a080106080703062d050f06030d090308070614071d030105 83
    0x154041d50898801e0164061181c004103a219800031036510500784c0145600327041505001000c1d40c82121300368007400c82c5d400b00040c074401010300402201c0c40200500107481076039007006004400904103682c001c0c5655442c045c0c00607030750018a0540c040e02c0061a5200c035400c40642139810041540c044960240802c1050b03e81009141d040000030702019480e660b101c0c03030440d005101110020303400c02580030440c45114015440082038420310011a10400c40200c104002e0350b86020b000000340944040701b01e0a54003079000505054801c4c3d105c40300c00b96106010900d99000b590142c5403e41e1500c90400c034078288801000c000c3c1034180001d001c41400c00110311303920007091100030081550740f01714240c80c085826501c03028086a00b060810780006110000c00750005072905003000744080041540d5140000780c1925110040e1261983c0c03030300d0350b200d08035240c2140d075060b605561550403000b480310309420380901c21020b6844c0e03d80b0309008520015007130448003080718080ea140109001c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 117642149 1250 117640899 117640949
    0x18070905060315190e0f010608060403050f1c0c0309020a0506030408040b0a030905070321090f0510020a021804030219030e1002011d0106092a0e190b0a0306 69
    0x224140c1c40e284540901e441d04041c01c031348040002e0b002580d052801310b503450800f4010840c2040d4a0030440203100076601c0d40d041a03102d410568008021980c01c01c2007441180c442000b03442600013003100482e95030b10320342c0d800c410f40b02110120400660b45000e82c0c0c086141644c00400a881c00307407105811490a952182454840c034000d203130380b10754041002d03c1841d10a8209100c0316501c4020f450b05c290b668030b0300364500720710b141c400686829080c143c480c40c984920321000403266012518101140b815080c420101582e0102d0011405900d210001580707503510101c040707103081e007180300c451326003070070300070f042103004004900384880107440132011aa02840c141c001e4030044130649184103409600341d004000b4001c0104445d2090b2400c80300300d19040d88500201d40134440103020f244840c038064141880750301148040004800700c01d90181c0d218103446001c0b40c4000d41544c200903001d101030813883c6030b81d60026040300c3c000070f21145000c0e4140a02030082c0007140d0b480a03181c010242000d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 117643399 1250 117642149 117642163
    0xf02130f0305151b120a0614010e010302090102010204270b0d0309052205070807111f0203130b0907180207120e150a030603110909060109050c0909180709050603 71
    0x2d0950f0709010485049081c248034212040404041369038a04884000400c050202e0b5803150191030190000344e02c0c80d02040e0804403060581d2501003140303d14005400a40100c00c04c0e130704541d402c1c8000314194030800d1820040704a03040d42c61861001c012115010b541010c100c0038000d003041c183c00800650442c0354482030303810403680000e6a00c480d010711160b09090700030b0844a54241814804150781001b21240110402c0e6a0450501d0018010550302c1081d41d108484140c0102d80c4510311803040d50246400c9001640501d005140c15102c1e4007000c402914a43d07010b0708610b5041003000d099540241c0b00c0c0030246c6003981890810b03141c03010717140401d49840d401c1c0054690000b03465607410085c9154407100e540c1d1140c4462010354024020302003800101e4114403200b0400016240c012400d41c80f0740c0c011001001540e0800d00382e00003615024042c21290301080c06a5049940c03407034100c510501510f800300301443c8403004064030307284107a4407040d8031502c3c010611240c0e032800b042c0c076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 117644649 1250 117643399 117643423
    0x90312020702011202030c03040506070e01122f0a0206060915060901021f0e0f03041a180d0609030e04050919020109080a030504081b1003090201120f02130f0305 71
    0x1611080a0300068605842560310321141e10f01c000104061f01181c0e0020314000c40c003850032241d0f5952100303002c0c0d400c455030395074442c042020001241010522038006d40c80c41c080c00003101141080c5543c2d500410310300c1d406c01030050700010400203c6258100700b00d6501282c00c4500c5001414555004c2c4c0884044025a034010040050260b549034020021011071264840380a01c94520b0423140f48010b1941081d401c406000d0318040b01007000000060710103840303a500d82c00f000c13001c0704a0341070150360020000a840711000b84000516644000c200c80201d40039100105445044c1d02d402014107114601c0584510310300010b120b81c6000c002002610a0010b01c0c42007140e80141c001039802252651100440303218400e21030040682c000301510466160740c2c12a1000c0001254801500200c805440d400544488007a17420a11036000b180c0080e0040c104119003600c0903a0074002d5848000d00440b031540c0000d07010301c1041a5240003001001c40401c2058417030f081d651480d40b41c040603903030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 117645899 1250 117644649 117644651
    0xc02010509031906050621070e18060403080a0c031a06030a0905100b0f060c06060d02040e010e061501050f0d050a02040b070b040203070501110c12071701020913090312 74
    0x1141c01a407020400c0c407400703041c568440168542c59240207409004100c40d4a0701900405404617108290610110607050100010b80000c41c2050240b5280207001009504000c041d03c0e4804035401e0b0900100d400f507806a80c0d1281c00785804640101601c603101340c1002010b140c200260b01d00741d420401e800c1d403568101c0b1469525101c041c07004000d045d049402600a000f024240d685000940e480b191402c2820b94414110f000070b40104101030040050104045c0c20041c0051200d140403d00c0c08500c83c80140005100582c0306981c0342100c60b0381c1503032000303940003c2c01d216444200748021001408240380030351828682d400707c59058000c01003103e444586410100d5003d4000f0303011b45001c0c10040b000c89855101c1410040c003040402c0e5010307801307401010b05c041825441855910240314600d40200b00020840c8140318150300741c03462401460123581d40c0031945164491980c0f0b85614014005a01e9040742410404145024854480c40780c1c07070300700040c0000ea00041c1d0441c42c5d44142c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 117647149 1250 117645899 117645907
    0xc090d120315051e0310062919030207050307060603060b0312040f050409020a05040e1609021312050f010501080a0314030709050d05030f0d06090b120c040b0d140102030106110d0c020105 82
    0x10030f1a1408400c001d000c9103051807800b08940140d002e4081c00341c88c6410350400301d580c00c10380e400f25910a142d80c0e0342582c6c3d12548014561070290f001400402d20820440f41303000c1c00f5840d858110f0302c880d0403c40f6040c2d1100c91901c450300d000c104641d00441c00c0c0c3e10107880d183c40d0291035917a00070755206642c002d94a4405460640d5a65000f0000500f00500148184045c8100c000e4540a052b50000e1000042c02008107600d20030388282c5500825101910060ba41803218041d040311580c04101d500c0d1103807030810b40c0b01c2d4400303004950080024200030103280d0810b01e0094091000e807aa21280300a061003003000f0584d001141d0400c4820556080c96000e009081c5581188034440002840b404d00040c03501c4602e840350300c203004503840000e040040e01c000c00c4c1009510b05050024032407030307032150380c040300c652034150700c004080d241c0205544414a10341e940c0c41ca11a681c4862030005035404001000783c43c2d0444c8403400c500c03103018040c010840c1520340240280c41d071210042d04000d4041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 117648399 1250 117647149 117647209
    0x1e06040902011103070602041a0901080705160c0b0417190b070507120e15031603020c030c010509030a0206091203010e07090e04050106080106080d080402090c090d12031505 76
    0xe0b42803c05483e0520030740b035581440e030030801c0107580701340b040c9000100d6010513000995800e400340c4400500583d168030840c0c035015422115504600107001010090700721030000212008001001450103c24540e2142d10b03061260740c018503884035501c00e6800505020000e81c28441c18030f000264440288001500c8100003240c1601520800034941c20358802000034454000b920320389540c0341283c0c001c0720000090141150350100ba03644000136500d00045d0100d1034001e401600040e4000f508a070309050f55408a94252501611601c003640c1002804226123035040c0091640030182c070b0004d00c1341f408030344080f10240c0701c14440c0721419004030001c21055840340410340014150320030180428280f500740745008140038070451202c1d610706800040c840501081449001c03e0b85d84940503d580c5907004c0c4040840005c001c9030202034100300039030942d40c44612100c1114060a592944040070301000740482d03024031020069401007520800042c6d03101c40404050400e0746040c0c5484640e08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 117649649 1250 117648399 117648407
    0x181003020c0a0c03020916020d080a1e0b090a021204031103040302100503070201050f060312090433050306060f0f04110a0c0c0902030408090d15020315091e0604090201 74
    0x21810036107030b00800c9141ca0034002518079400550303000310b0300d41c04a6203540008503c074010b02c503030075009a007200c1c0041e85c58601881c641540302e0907503000810011205c205510030303508441e0121006a54407003c000c2d20781403903042154000c04c4544114030b001d03004000040c1500d00100001e040003810401c40d01c032074105005540055078007902c0d01e140d01b10300e000060195081154040b00540c0380c0b030700140c00071080030451809448050041c024007240700700102c5180d80080c402c0c5070015100c04c1c4e84488881d250070420349030384842c03694102100e50002c85d410075001540c400c0f4480c0d0300c03c1080c0007050307480c000320280002c1e045520047c100d103000003081c054003201c070030544881c1c4041a88041c0b181c021118101d45440b41e910350103240e0711260554100c0c00b0550b00584030050912076641c0c0c60a060240c0e4070b106002e4032010b4101d041d00c0050800340c0c0c0c02201d4440700c003d00c0242e400800c1c204410042d030804284020071400c40042411031440241c01811140700c2e64440c1c610005590007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 117650899 1250 117649649 117649657
    0x11406060f071e05010603030f0e030106061407062703090b0405090f0622020310050301060b091002030c07060903110405190507120e070806060102070303170a0609090506090d0518100302 82
    0x101c0130081c0b0040c1e030f60341406000a0a00c06215001c2860b014920600d8030341840b400080d0f800b40d442e861040c842800315842250090700c0111400c96a40402c52403010000c241140d82541c08a124181d448252074010a041200d50003400d210780c080c4028040c680c0c80e0307a205540010290b45001140d615403000130700801190704580d500820000d18100c01c2c1d5001c0c0c00551048180e56400d140b2030355640141070899201c1d03c00d104c05030f80c05205211003407404403620700424005104803400d015104514509016450b03100700701299400004008001c45980502d840d0700c000c4404210a20f440c01881c8400040c4442f64a80d0300e0b0b5480c00260171502480c03007400364a2200f50f013000380340e0f1003104041d82c03110507015003601c40c8500e40c0001d110b903100041120680360306544802e8040100c040720f8400500c050980701c00d032a215100803580403401d102d2143c0700c074026001004507040111401e07041a00701038003502000380401c4444050f0f011000581c0b0b03c0300054a1103d8402084e040032030090013 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 117652149 1250 117650899 117650903
    0x5070602120a0b03070b0316020309090c070204110910030f270605010801090f0605040614280b0a0b0d0204050909030a0801060216120f050d02011406060f071e 70
    0x21021518407440c04107002400c1c440c0081590410404005108056072030341d4903c20040c140204000140e5961281c8040c00381112440c01100c1c01c10881d00000b40044004950a007401d010102c1c0c00400d40c54580030b00d40058038006500d500c2c00d0990400304280b0183c84120801b415141c0c184586c4680c3e80d54012009503a150304a041c41c02d000c480b50780c8000089840c140c0b40315040030000b24801e4018410031402941c02a10b141c0000c0d40390307865201419004000b1b030b8003d556071044c4d42c07a8481c0881e00b1481400c541d640b01c0801c078041c180c042742c3d8002c21141708507281d10f488800740e0382351a60401141560312640100e03854845000240000e8070864200700d40040600090000300c00000020704040d6515481d040c1d080e81c0c0350345041b40d0701d5000c0125400b640200000400148505000210020740518100c205040d500d89445107003207100800600181e54881e03007040310f00d040c40700454101c141190550718002511818145500030302c400940001c00d040380d800004032a046480418030307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 117653399 1250 117652149 117652151
    0x3011404060c0804020d1b031401060302041d0303180a08030a021b0703050c04020c101a10030c0503040204050402040b0306160f0908070b1b070303020a030801060309050615010507020613080d020a0b16050706 91
    0xb80c4427035240d01900503880100e001d541801c2195204000f00d106041441c03940320000c5095607038402030022400020b45050140703000c2c01c5c900101048049000b1071244202d9400969658004049030b00c21145e10412071f01700307807c407082c1400050b0010400c4880007104650240c0c881840300b0150b41800c2d90602d1240402d481c010b4504851505290503c901e04821100c4407040030b41e0700f4096040d10070300740395407000034020800076005151a03404641c1203400603000203128070600011924198050307070541d82c00e1000c031003814121544203002008420b4103244c400155498940602e9440a040c05031116000011171481e0030301b41c031110344034000d248200c00c40d00300a64a01b80070703440d0221000181c000844200005c144980640680f012040d0720500410a55813010607a10031125050449810004108031800240c2c2d80c02c400352940007480d112030380100d40b82801c400c2c03800c3c103d080220b00755085004501c010420015210307034040c1260180e0b010b401c40303212040781c4501c18640001d01c21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 117654649 1250 117653399 117653423
    0x90a080703120f09060c0f02130f05070309230c090106031401050d1113020d020f03010801050f061e010219030203090f040e070b07020f03011404060c0804020d1b03 72
    0x1521000592004490184294003100e4120003011201c24441418540104110b030398208a81845a00f6410005d4002c200d000b1011043e540080c03104984079440302790041d00c482040c0c00c0b0080700e21441e900444141000c0003c500d059540c0070303408100f410075003041215a94190b08a00c1c0502105c240c640c030061a109180d07850b258098001c2801d00031400340c8940c1000049524140300c0f412200040d04021b010419603111000c0140c1e044c0303c0700e141c40c0701a40900203103840c0fa4150014240c9642e050b6901a02c03581000c4960f421610002c01c9048a0100b4038140402030700d42c1500e04550003017510000c215441c0840c0144e281c410140004807440425504080c14140e0100140592442c1100c03c0a001c145003801c01054403180015181030b500990010401003410100400e801440640401411616200084d085503a0f101100441c0a120b200f080704000e90341c41088082102400e20804606103038001c06e4056600440080c19403158044040e000003052032500009d44e0300c900702c2171030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 117655899 1250 117654649 117654659
    0x60a080114070210050103030509060c01060503070f0801050a090f08070303060b0d141008030f090103090507090615050c0601060305060112052a0403080a030c140403060204051f091a090a 82
    0x28107401100d00c180140100195a510740d0380030b009440c100da0b016a90a420090280c04000071070f03101142001c420740d600c510001d95a14103206400007000c5015143d0f050524001e050b5094980003019402450f107850ba822000540c2c03070b060300d4079003500321720416100c081c0703854150000c0082c6d401c60445550040340a10305500300f034000401110080030f40c00469214681e0505001050707010b9240a50001d100780d91265a130301000e00301c015414500455010742c151129414802c1c02d40261038540d4640d4001e01880710344019804501c04149000740c038166060341601d0b141d40040c0900c808143d06c800208400340c0c80707035425a0364500c03514402c00c10303401d011421010000c014850011824140740700003500ba85184140c0c1c040700d4000d0422881c090b20307034500b20001c10007001c1000900500340744004286031982d019002031751045000590b11030801c010007030410b2004811000b0300c0012100329100755400b40019003164a00030140c600d48000c2c0c0120440380c01881035040d00324803803400000f5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 117657149 1250 117655899 117655931
    0x160b0a02180f0904030e0a0302090103060606110d020d0305100e090604020109090902010206010509060a0f080312100b090f120109030302030f0c070203120a020a060c0519030204120b060a0801 84
    0x41500020014140354a0707081e8240311242d1546002140e10940a00015012a0081c940b0741e00411004001844858882d0300242c103401d002e0300207558403903680d035090200a41111401d40c0354900280100300f88629020025580c0c1c001c0030b9032004143d00ca10100721240f0005002001500100303000d02d029103403203050541c1d5100c0489040c2d001405070000042c031074030b2a00c58840100e4060703025104603800d000900406060190505070402c0c060000050001160503490000d4100c1a0117540c0e101e1880401460f5210050400141c1c18074808003000b00b81000030031580407440a4840400d68000000000c000008900d8040195403c0c1480c24041503032660082d8482c0f6290040d0790284d4407a0006c0281c00c0c000d0101c020b4060340b0880c01140308041032005809240d04a20440301d030f5040c9540c0d0350081d1030000c1400d10210700c0100310b19040d040c0307030260350b820185641b03030440c01d00746040c2441a0703c6001d030101900f0002640003240a588850540c01c000e407034120000d015000f039040c0100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 117658399 1250 117657149 117657157
    0x4060303050d140105010504030f051c080a060501080609010312091a120f04050307080c011b1e2a02030c0303030f01051503100e190603150c0212030c160b0a02 70
    0xc20b5841c5002c50b110b5000c910240494140c94041c1e41e040d0600e41036503121100a0340d0b4070402d80300f500c0380a01c05640300d090301e18841c200c00b45076511600c0710b040582160041da049038100605200c80001001031507203421220350704403604418002951808210141c034900300700d030004140d04506212400c01c41c0e5100e0700404030011944400900307940c03944203140510005842c01021a0810401140803e00382c8006d840d514402500000e007031900e0780101041c208004070f030750700070401080d1820342002840121a00f10682170400c03c06032031300301d12054581140c2d0612303134000522000c03c501c25074600b00181c10440b03a01a044a9580c2800801c0c030000b60001d10520348900700e5102c00280400384941070741d000701800c2048a145a040c0000e140745540001e0590280c8200d14240d071466500b00d0240038001c5005102e4075100203000e9618509603100b0700030002c159880601000400c02002003103d501035a402031590301d83d15900c0d22001d5981c603010001c0c04890012052100036403071903000b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 117659649 1250 117658399 117658417
    0xf18040b0709080303060609060a1205090a021503070207060807170103110a060c0506070f0302070b13120c030804021507050d050a0e0f030d030e030408120c010606110703120e0406030305 82
    0x32144150f540d402d0b45649100445000380c10407818400f00c001414441c018080c44003190a05440301c0c840c03002c01030708446c42126407a03182d80c00b2000840030741c10220071403c0745900300d0f2907003443d40ca03024101070f603240d905111741810051442c0001e9403c0d880340c0107421382e842d025540d40040303594030b082200394502c07880402407241c200301c180050b400c1d0244030034009142e80700000d40a00e540700c14040c0d80c8207403101c9100041c541c00b00a0b4800181c00609154810781e590740020005050078100308101c588884030034014815026890008240c0014109621640c100c0c3c0940070280300540381e00b160b020b0300c0300c02010f85c4034003281d0018041d080030241c061090140d40d0400401500c0c41003015420620442030f415400444441c1d440740d02c00d40004c02201e203203c007140d00c0c1594510042d460300401d5030807401e0300000444d40c51443d0f0750a0140c00d008200c0c5207030200e840135144505c01d850702c013140320040846030360740420700c8241d008005d00011618010070030440242d03203040140c1103601c14114 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 117660899 1250 117659649 117659657
    0x408030a0c0228030311100e03030a0f1811190303020a1403071703060316090209010801150905010807030f090b090114010f090b01020f0a03230304110f18040b07 71
    0x1c0c1d002d4483c0f1800c1c400c000e07a280301c1941e0a460714648080e518281c0c10050f040042c0a40058408500c9850150fa04600c42c10390003103541740f07410750300c10b002c840101d40e921800e203003401a40c5a001d0b001c00d80384144990410780c0750030402d031500d0008525040300741e40c0c1d841d02c0c0800e6000109164020603082a494024071000b0411070740908030710389031b02c80c0c04c8008101c4041d61900b410080740074006140e02c0b0001404645d894034041418040540d0198441518243c000803920f056583c041c0340e941c01003410340501645002c2c4004040c2c00881107006081c10400745000190a051081c1c108040c081e040d854104101030b02400d2450711028103c2c3d0b480042e6003050b2103110340c0006102c3c03880c121400500da100741a800c1c411880041e11518628604522070b0000503031140e0b0050041c094954442d0701c030000c040d050542080c1e0581c010109084443d48240100b2010403c150902c0ca41f04030100e07025809064007100182000700c3d404450951844070000300f00c1045100074070140180c03000d0715 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 117662149 1250 117660899 117660919
    0x1b0b0a05010501080a05090601030f020d02130e070603060b070807030c0f060c030e0a0b0408030601050c100501080c060f0406030f0608010c110609070f09050a0b0303030910051006051b030408030a0c02 88
    0x8417080c10741b001960198103c0c2e00c62001000850300e000e80700200306200808c100d440000c01e80002d40140070b4000e02600f500d43d20b010440c0400d0081184c1802080c2d18141408500d140c00c80004448c00380324405055080c000030b4034010140b20b0740c41c107810642d00500d0071230380049a0519000410400038400003081c41c00c100712881c6180080e403800c1c40d40c7e000e11900031603070b191b9641c194607070000340515046c04820f0042c420503000a01065460500010002805600d0300300c80303d203003050813011180107220800040002072034100c212400d03118182004280c0714086400725000381600e0307016100c1c80d4a403500d0903031100c0d40403100c0301440b0380e0388080300c80c3c94950f688265141e481c180f00304102000410300c2000b1440c00c5422070f82d44203011b506c00248a501c1d1001280c1594011101406207410a200700301011802d032180700d07040583c00510803070480c00c001001d450b03881818200c0305a940f049001c1d4100802c02c00c1210090b000c004152303508c4400040e4043c2c01e20340b442000b01c2c0300d01d02c980b0f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 117663399 1250 117662149 117662161
    0xb03060f060f01110c042405040c020303010911040e040318150f110a021801080d140304060905010605040f021b0d0c03120b0a0e04141b011b0b0a0501050108 69
    0x8540602403900180700740a210742d100300654010401815034070180c01000000840c2eaa550310500c0c25620004041403060200403016513074584d8940c000307501c0b5510f051010841180c2c0002a2819200d01d14000a0131113281c040000550040b03501c0710300a04030322401c10007050f920080c0d40c20480c800d0f290305030031291201e0300545810090000840012000c0501040d0f4031300c82c02c480c0b0b080107681801e80b2024200c680116002500384900d84910031517900041100310303410425503c1444007450304040117140b00304030002c50f120207403001e0019074482e400d00301804001c1d8072840c01040300903c1080542c0000f00e00c070000e034100814a060002d00100680c0704a20085140040072240d65900c403000d040654044d20350301d8220444040259a80c0d603081c0158540180802c060301c0c1c5150302d171107240303880c1c038000c10401030225604620742c0081c801111051908100c0c0028814242001c42c0400c105d418010b03410b207006000907141219840c10300c4485c42482d0300c8103040c0c40c400c2ea5440390300e6440f1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 117664649 1250 117663399 117663421
    0x9051003030f0513090c05030403020607030509120703021c08060102010e1908131a0d180c0603021c020712080603160302061308030a0e0a15050f032205010b0306 71
    0x16100160202c0d0641030003201c2c0724441d03002400089500d9040010f4a6101e20f2441c0898407000f0404010a900000b484145a010042c00758040501d1400307102e01d00d4000b42550300c50800107048007444c8000325030681054000d102c0e420b462210380c088030f625940c2842d4000d01c01c210a5900c00c0c055460190fa2954000c40410070b4420300e0b500e620110b100315084e03601e215156001c81c03c2c40d801c12103120300101d511103c58400400500d00800e01d99214001c140d042001c84440d0400035588041c52000e0200013481c1076107050440340350b41401a1510b8000519064154107180c2500b2290700c0004c1000400c09048940204142583d4034130740241d13940d201b815655044a41814240058054200010f14089000300f000120380b014030045203540e5200b541c50340d0480c1c52140040303010b020411810341810144d44008190301180b0082c0b81c028400702501d0b0703115448890710580070000008481c900310710307031860410a4855a80510218a0410714024141391864511038001e400c04101c0a01c59 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 117665899 1250 117664649 117664681
    0x3030d05010f062d020a0b04060b0f2b02032812020304080a080f120109050a0c21050a060308040608100b0f1602030c090c0a02010b120c011d090a060905 67
    0x340c810000c01110b04c0301004000080d2600080c007140b0401281d80d0000303401040a0740114403e12001c10750a01c44d6040000c500d016070b0b20140240c4c00f407410808207501d60403181401803101c80c000c0c442141180046403c3c103e05007000079031500800d0905c40c095200c48050340c142ca00902c045488100c8080081340c591050b440b03124160340c820700034000400c04e120014007110300d00d08841817611098030107010b0820400d034440500310750750340c080210300900350103000c5142401d440d24403642030700156170411112078030034801d41e019602c00c001541c29030aa80540041d60b0045030701902c1d42d0352014000d041c1074084403083c6035a0b06002000590030100c1094aa40e5400358a1803070611701c0240f54880201404801a030b0315108440614002d5110200741602803210385520303030b41d6001c05440207425104116036841c011002c0004204a07040c010507610700c0e0f180c092078402c400d0800c200c82038040410a99405a1103502082840b11024441c0d0001701103c2000b44140b2990755074845031600306035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 117667149 1250 117665899 117665927
    0x60f04150e1003020f060f04030605070509040e210c010905010204090b011d0303070b04111002160b0f190c060c0e040c050a120c03020705030c01050a11030c04060f03020903030d05010f06 82
    0x10b48551715a010346440c40c040c0200d0310103010442d051503969112002565815500c840100d000082c1c204010308150080c1e25035407031210b00134164940c00310340c8582d1404501110500c0c424004c034900d1040340c42901320841603500400290740b141d4890046600800342002000e000c14403001e10b40226000d40b44501c068540d00802031401c002003500c030340a01410080c001c807245004c0c0b1096110654483c01401e006001c940c0c01480020300f500007012071091143c10449c90020305203c200c01c1c2d080b80d0400c840f4807040ca8001000c3e0460344030310603240400614801041c42d03013007240c40d80c4003550008140880c1030085405000d0115120b20685503442607071003901c00200d9504041b80b488803d600082041c864915006280034801c0d140d45040d60401c600c0c121480e51110140248280540619040c0050030345400303141d0b0a280c0489140c5d842580300354000c0c00000001c0300f88040c041c1e4192049003d015084e2980c8800070300800380102803d020f003180c80c036034110f07010800c28404e031b40d8409030038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 117668399 1250 117667149 117667159
    0x608010509070c0602070204021b0708102d0204030503040308070203150f1302011b050304081005010b04031712010311030d110a061d0106030c0e01090b0a060503060f04150e100302 79
    0xc07055444501c086d602045090383c120340c00b00090040c0041021a27056182054000b4204450400300c81e5800c0400d0b1402e5a90164249103c13901d00071030021402d8504040745140440e80210f8400d6240030780181d41c009001780c0004640003003030040980c02072a02071300c21402c1d10307205141070a656440c00c20683e1039000c118140c3c40081c0c0c114102e00d0b240011540141031080c60409107040840301d610110204441c103070400705003000f000504104884021003a54400e0005604140c40012240914480070b040c2d0340d40340c4443c0202c14940340c11111511583c4849038025a12030414440d0700340041e01d29070091183c083c400030514801c9245226409240c4068000340702240c0303a03440031744030601c0000f00340102c44a40340c107400e900348100c2d0700552090301401040c1786851010149188141d12545140e4103240c5100b009607100c0440900381c604604003151240c456402160000106038480f41c0c11a242000c0c81c0d41c8007581001d03400172a10f015450720100d90310424094440c07802884025006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 117669649 1250 117668399 117668417
    0x703050307050c010609020a03021b2e06051905030f01050402091305100e0708061807030803070509030f1b150702010c021c03090f060c0c05060903010f0510060801050907 75
    0x1032042c030081c0300d44007494002144c2c0307a84512000089a20003404080401d42c001840300483d0844c0d880342007282c5a04029143c0d2269949824900d40745070784c800060401d500c50012000d49650381304801501b8054600c00b03050300400345250080c80240140b80c031034840c11365000144c08050158a110342e038064146402600c0c1d0b41c0ca403c41c103100442084806000f4030481202d9200c151050076082100c120050414070318003295941040f101816108043c015411400d10b5020b0010780c04048a50041c1d03807507030340d5440110465950140e002102e0b41801603103c41021404000350311000d0201d03100304540075031103100800408040d10100b41062a03414030420700558025101d449403240054040c41c0e40780e1290480e00607031440c00c102240403850214060009522106a000140c480c03410310034002038140d1a8a00440c145100c0e09210383e2001034101c441f81c9003900810401c803414036081c001400d00c042c440754010583c0c0120313000030350310300000206840e01c07184590049102c1c4c0c84140c08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 117670899 1250 117669649 117669661
    0x123060c070302060d06031b031a04021c060c021006120f02181311040b0303070209040311030d0516030209100810050603010e0f0907080d0e030a080f0403031407030503 74
    0x264114880648003401020380010150302d6142c0100000d490440c40042d0300e5045181c054403103001001a07445100d2014428000144520070481c00d2400302d406410030381d9100d10000d140c45600003440100a902c807007010302080401d411141500c0002e409a8200940e191802070840320140303c0c038420104050000383c0030604500c10110942e00107400200611030809a20104540c280c0340704550b4000b09484105205605801000e0408120340c00d1069000b0740740000c0d5280144003000e072060001101050805010b110b820000131118410b40fa2a401410043c00042408646811040c1c000b881c1200780c141c4603100301c0302042c60081c4565440d20000d40c080300c103000300810410140c4084c2c0c5000ca8280c1d01e410244d4020284900d11038035611341a24540d5043c58040c002d001d0551000c03005210400740403440e040305106500d80141e640d00c400300000e140400000c000707800301070300050108000300d00034010015640643c8400d84004540e0016151600c076000380503000030020b002080d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 117672149 1250 117670899 117670909
    0xc12120705070503010204060f020d0207031a090f12180a06140d150306050106030f14070c020d12030b030d0503160c050c09010902040501030b0301060302090f190c020309090123 78
    0x404240140101c0e0b24440c1c940c00800d00f20f91081e0401c0000c81c011800c2c0402c101c0e410040741c01041c074588050030a20385035070f84a2064000350011201009140d1001600440040100c400c54114903401c42d0344c580b00b1241980d4582d808941c682031030a058001d1400d05080030182c800840d02e49507030314001e401c20440044040c1c2c11400360207010913180e458406124201448090117107004a20009840d454080007134100e5105280c816962814200707205c690b07132150b040581d0700c8051800d10500320043c41c40021500e03204048002c0c48031021002d0f03611201e90580c40902218030a42c122000840e4001060340e06003c11682a14907104000220030114441d13543d082c1031a00c0313002201c113050403038000035180c280d09802c4030410b19400320301040250390500400d1006d4500740d00030003d944c2180c020031300645004000d84081c40803400855802101440c4005c20141c0d00b10041144900c5a240203440340c2c0889005440754910a00200d18a41c221250040105041d10494003c14245050003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 117673399 1250 117672149 117672157
    0x1003060311060918041208060906131a0a0e0405070e0907051c080a0807030b04150509061f030c02011104120f0303020c070807090f0203060108040b04060b0612090c1212 74
    0x44d801c040401c071800d8180200c59180c50040d0b20603802c41240d4410381400410071480203100a11450307100303052000d107444504208810490407440440c1d20704482c00d001c1c0c0c2011400c405950080350b181e10010f00c0e00382d403084071070299120360309036200d5075542c450401502c84c09941c880b00350341181c203081140e45403248000c010880e000d03c1c1e0850205050320340300c40079001400c804002ca0785032820070070881e906120b40030004030300b01c80c10082010f844100d01c450030554016540220851004603404d681c03a0a28415010704092480190780070700c2c0c0c0024060802c134001500558200607612580004d000103840a42c0d00c03c1d85420068002a1141c0310b180c203402e902078003819803c01c80c521045c0030601800b0040d1081c840100285880d00f6603140c12190b030b01c413094001074814814407004c0ea80c400e00f41504182c20103c840041e4803142070000c01000f0340e101080c0d001d00000b400409111034415150305c1400c1c08010340e114840d070b050038007070f10002c001046105274003c181102c402240c1c0f90050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 117674649 1250 117673399 117673417
    0x911010201020f300702010209102609010207080c030d060b09180406110c0717030f0a0c14010203010905040b09070501020316030314010b03040203070801020408030307110a05070b0306100306031106 87
    0x141103121446030a044c807130380a880d1840141d4000659007042e0030841c110800c200c40520b02003002c0e80e05c0c5901c0c01d2055803401842001c02d010310340032426028094041e188016040340e030b9156180a40000640c0e43d9204401e41441c0d1405d0034800140b00c5060425110744040c0a410035451036005081351440d10001001103407041d039039003110714031000d820340509800b540d80d030b0082c011941444000e5450400c000b480803003a40c01004010352040824040d41c009880c0c80c1006144018586000c030180c219003854400590310210001030000400e03006180038600a03e02e02d481510f520342481d4543d8860b028460159104016a8111000c50b92649034124040d03e0000394580403c1c9200d10058421391098003101c00120501042d49030520440c8001e120610086140900d40003243e070700c1e07010041460051141291521a50600030300c280c05090780d104017580c2d0303000d803100ca00d8000d80d04140d80240c021840d22100d4585240240b08203000c0d070350000404a605504d600811441c0d0f4400380e85 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 117675899 1250 117674649 117674707
    0x6040203030f0a21060f1406071103070b030901050a060512151b0c01020702011103030432010f06032906090c090a030506060f0a05010e01180f0303030911010201020f 73
    0x28030624074985131000420003500364022581510f031104454101100b90000b12800704240d115810b2990303541c2c2110011a400902c50082c0d14105c00020704040d00c6510040b1103c100004202c024041075122901c1401800e004102103a121001d103e00960b4407050310100780d005000c000025030071348a00c641c0c4040900841400710649003103400d502d400c42c0316032418903900424100119a0004212135006e10038000640c15403500d5280c82c2d15006c6c01d00c2201606007512400072500b10080c1c084015190142402405103401500c55000101700070f200c2a100405840b00c0d220024003616407150b00c07a80c04c0c0d6195003107901c601b0100a401600a015442203420402c1150100e80340c505c520030040d80100d015100701e1038a1030a10142160280000d4400c0f0000601440140c2e00449184200745003807800d40940c907895180d443d8025110b411404003102e114100008041d455000501d80900c036240101c040d0b444500103a09070b004110f911116030720140103840d25412054000f20700d250b40d40304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 117677149 1250 117675899 117675917
    0x80a1d0a030305030a1a0d0b070210050411130501080d0e030a02190609050402121603060806130501060e06060906070c030c14040e06010513020c0a0b13050d0206040203030f0a 77
    0x1400c408099802100840d001004026000e582c0340705100c0c0306013100e0300c0000041d082400003100142c01c9000100001241e8010072903981c07003040001032207803400c00c081200d410325040c4503885003d00a0010b21612a08010b02c55170f01d903e000701030481d06110000c1810316040f480030786d250b25011005a806105504124015035039011018401e004081c3c0030b1060300b82401d0000300000b0091b0000760166004224001c010000351000981c0809048030041c0a0307034503540d007200a040355611410700c1b03110300c10a00070b104d44075103007000900344502c0003040515a00c9119070070000c0d007268015031108040c0100d0409040c601e00914100344a141e4010740c503601ca40d41c01810f4079031504052005180c06041064604061003481840080c0000500b200d42c5800001511494003072205a038050300440d0301380c0c0b101d4080065410184c2d100300d100c40d851602507441000b84000c0788040d03130107110300d07400858214004955a802540c0240156141c42090202c0005681c0016071680030050102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 117678399 1250 117677149 117677207
    0xa2009042103091e02150d20040f06052506020301060e04050f01050907050408030d050412111e07090f0c0813050304050603070e040c1806051c05130b15040c0903080a 73
    0x94010319400b1100b800008966515550902501d00c4000c5239070300180b0204010302606290b079a01d44201c07002c2d441e203036551f0030046100510614030b1109a00c502c03601e08030440d01300003107070b0041d43c140c500d01c0d51602e10302c440d000c0400c400e582c400d44541754400f400c0d100600150401c80e006a03030108045c00c00c03a107008e542d401c1d81e501d103a0080e000c4496803559101404108048012101c0031170712249020920040550044d0f5118140030b04900b040c0e044400c0d010503001c000b4026880100b40401c02040300790308941541018045810507480080c009000081040c004484006900780e000001141042d0030700701800103d600103410102030100340c0401c08095a039900500c0792a4405684404507102d1030032416042c00ca0940001082c000144202e082a200d1b100c7c074000510b05058003c9130030b84405010020b24808903001806c07011a0030300b00b1140e41c44030b01664014400030b803020400026002800c131240e11076404001c101c4041004010710300c031711600105982041d41790501d500b0b91a00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 117679649 1250 117678399 117678439
    0x301030f1b080105062e080a0605130203011a0a05070b10050a03110406150f0c0f0611180603060d060c0e0604080a11120a2009042103091e02 62
    0x20303920056003603449004000717480c24032505800c002c00c002d00c10745c1c40c1c0034407180d0b10980c482a5242c0c41020410005c0020b03007045003981190005040140a44844a0f00f96400c14081d5109006507800d041c1003420014a4a480d882105c505105030380d0344a04102503a5120001590081c214440d00302c2c0610b80400d13140d8642205a00541c405c5600544041c0140280010b40e603407940200c460424449010400c10b400c180204119160303840c00f0402c405481c90640c442d0440c840c00a0041440d040b0408284e580302c10085c5a5800c8400d0111023a1049008000141c403003140c3e140c0e001104403c0400009005410085020031682030881c1c10421080c0400d18036000360b404505680d01009101043c4020180000600d540949400703840d2030543d00e803503503101000100241555000440032282c00b41c02540301c61208001440f4840c44e040c603044c0141400300601c07031440a641c03a040207403640c9000f4421500001e038043c0031100c0c901f42001c0c412921440c0d8100030707a0000c81c3c00da0440c48000740c0d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 117680899 1250 117679649 117679703
    0xa081b01020417150708010501120f181e0809220905030a11010506061603021e01140108060403200a020402030c070302010608070b030c0906040902160204050a0b060301030f 76
    0x240c0f50040b4040710140700c42441c06402c985034606601c265814031564560081e01c4a064840c2030800d041000100744482d00103003840103510042c1d034074054002007041507040750b082060780181c048200804401510700c85072059260024000c90080110003102e00f40108000500c0d00555807005808100c0d2080105036010301e4811503150300001908101c058111001019140341d10000f005a0300d01040411998811240d141c4110146a0850401c252013003111010040e21240a5003004e8a0660150301a00d000101030317508a41c1c10b000455400000900c00348542d801d0783c1c5426500313080300b0192220b414080d0807945140180c1b00b655001d82c540740029401240344c0c1c0d085594070031290500030300b100c01ca030704000c5164101000401c641c50258050b40d4200300480d00f015500c0302547d00050161050340d000068403800071a01c6a0340b50800083d0411050082e00c040c04182d4400201404950296a08640c01203040c030050011948602d142c04115104959494400218034812406100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 117682149 1250 117680899 117680909
    0xa0c0c030b0a060306050a060305060408132102040c0f0509040f020d090308040b010f03030807051305100c060b04020a1d0402072102010c0f080708070c060c05180f030a081b010204 79
    0x500d90300101304110641c45010f41c401a402800c200305400c6035602a203400019101a14074a070104100540d800030091086c001c1820401c462403c0015100141100b401a03005038441c500c1c010155100e640950080481c0c60741c0344ea512032a181c80c0c041000020498a6018072a565092001c0105440705128590b03d80303001c0d0700e45285a140610f002d02800f032058214030400400d040f01040041d170011000ca0300400769081c26925048040c0701034001c0d200c1540420343c002c80c9402c0d0f0303401c983c0c2c03c00c11340c08407d8010481800480c1c0b00c84c0a000a0740314068102c030014402c29040c0c807071844800489030051900600c094a0f0511f96151030a003294405100c5d0851b101645010032540d03024406c09079211000e041400420110540180840e1030080a07001800741d004000740c1c6d214491841d200405a1184040154203689840104280c0010400000507040d454814450380ba00d0300e043c01402c00014010500701c40c0760b07070351b005240d00020350303240c03024800c0c00400108850030300103000502 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 117683399 1250 117682149 117682151
    0x1605030408100608120a053403030c02011a1005040503061618050f0d020609030a081e070213110d020c03120a0b1807110a05010b09060111030a0c0c030b0a 68
    0x940140c80032003c480e1942e1100704554000294059002e0f45070054444941a030304000ea103500390480100100c0c4050891032400004c81003594580300013200300e101b03d09009a1342040047c90b0024180c0c200c45070b03080e00c0d9818241d90141c1c48120725183c030211590406514200d400c2c16a0392010a18141e8142c84c140040741d0a4100c00040c80e0744851146040e0f41600d450f10b1100d4a46008280c030001d02480d100d00039901c1c100c0b00c07802d40d2251170444400b520054222030320404281040d19a90700000d0982000d00141e4114982210780b90050b103070790381c0d00201501c4001c001591540d0061043e0010f41c0031a040a104184c2100018400743c4090700000c07000d1a0380d01d0301000d03050511741001f080c1d490742501d009070400700764440c1c1d403d0001c5024810450ba1003500d07460000e440145020500c005c1c030f031151b03105a008010040d041229440f0b002c0e1052292354489000540b06001c1112000030b00f0f603c28004204d100c3d1017030a040446c1800b41100c049941d03140e444162076040100c548903062 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 117684649 1250 117683399 117683413
    0x8030403021519020f040e130204061403030f03040f0c03030918050112060504020418060b0a0602060c03160917010c021b011d04022a06150d03051605030408 69
    0x1154040c001c1ca4201012142c031281640b03003041500e0a8510018081e9040c1540450558100b00c0031710111400b5001408807400700c2d140031004044140c0c0e0240c0b00b24001c904150340080d120000348200350440707000601440c02d02030124190b40d00b5420040c025a9140c240548000200c3c45038500d940155010b540d8840c1000d050003042500b07510032980c0502107a18150040050005502443d0070b080e50017600841e846d1141d000003405890110102c0d100c00070000f40c46420004140d01006040400380c4008428a9490409a0700c504084400c4c0c1d00e41c2c2c1d801c000007401031306041218500d00304541071400340d0b2600c5100a000e040b601215401e134030ba542d405a440d0043d01003005811500d1104100e03c002c00702c000c002000740541210303880b01381d45038a445100980d15038060300c00003604024070019a510340c100380382d8500f00f861034030754490080c0d102051030580ca01038009801c0c1c4015000b6442d000c0156800c07110b95024400004014144000070800584240014001040180018012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 117685899 1250 117684649 117684653
    0x10b060d0e010f1d0f0601030f020603150a06030209120105010b12040501111c0b0f0102100b030a050a05070e070305090d0c0303020d0f051605070507090c020a0602070c0f08010510050f010c020d080304 88
    0x94410351080600c00355000100402c0000d0701c081e12740c2c590301e5064817996125290248600d035151251031042d50300008400000c03030041d42c50741c058100c54504442104549540c1450f003400c0321002e001c0c03007802003800c000806050752907603280740c0c010780b26600000788040121200e0708147c00210000c181c41c03007207061142011016020f1510503141c1140c2c040511050040041c0d680d800d4444e4018031152607821103019643e0522483c884c0c01d4010f802d07914201c41514000b51142120b004114102900d4800328010f0391081c880c25104400002c01009035980000007602c0c1e51080c04001c03802c0640070001e000701081c0c1402440041c1d0461a0081101e00b000031007118580ca044443d4010003030b041c080c54020803000a0484215402540002100c10035918101c0c1403200d00c4202911250000809004000e2900940300c1101c20101d42444581d85031052542655000d50380070154140c20102840140303010a042070f89a0030505041d241000ad41d0301103a408170518606440061000c810042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 117687149 1250 117685899 117685903
    0x1a0c0d0506010e1e0f0a17070e0106091a0708070c03021003180b0c04050604030804050901141e01110a06021806040e2d09060a0608010b060d0e010f1d 66
    0x240100003420010030340b0030343c4404184503d91000c10080948448a0280100c0e211000c01c2c41d510040076140126641d11007842d00d006804c0603900a0302c0d4407031408001100c0c030102e210310b810f07503c3c2c0d0f46d941402c9a1800d10118038489400001004500c030401101000401d00f900a04040d4883d5040021141c618010000720030480d003a600d00b81810222807176aa014645d5101c0101d5621112281c2592a10100c0109900498014642080d4001004401d000d084400340044600c126212a0141e0f00d400c00c40081e0f00e03140880541000241c441c80103184240b5031400c034a000c040c58002070000103101321918180700744105661341340e030000c0d0001110020802130a89903105803076291a244c941300000d611400010440081c43c1c5109050002180e001451014000380c1214150b00c9800d111820f107444003010340b0720018040ca018030000e03140e14107006840c48a50000e210b503041200c6000300d034007e001003c1418040d55030b50648410000024814030300c0d05d600b100030046000320020880340c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 117688399 1250 117687149 117687151
    0x10f05160807050f091c060e1005012126040f030320070b0309030c03070c0e0f070f030b0102070906090603030908160530061905010503191a0c0d05 65
    0x1010041d0810602d07940d40b5618044501d682e03002e944110320b24010450243e40010507a500034015414101d400e008c41000213541c40d00c4400e541c07820401640c0e01d81c3c0e10038090512400903000a150b410015001c11500a8401e260018003081c12500140c01c03080688a0340c0300c0d4021744038071645101c4c10310900d1b83c00400c04040322801c0302c03000072a445c1d030039170265a01e9281c810105c08110010001e184440140300740e4415868075822030351071b0710480c13500140b0702889001d20300242441c040001e204400032a4558054101d584603805c2c0c04110010403000780c03c0032000c0710305601c20300d0340001d0092840d1152900400c206100011068114640200303090f41c140d00c0041264001d00341c4021320490710100c281283e00403906004e0308817030450014854980400c455001005808042c050601c000c0380c0144920005418421205500c55100c030403600203004443d00340c0d00c00c8800b10750008049004244460140511511044c00710b208402c0e90a021034540505076030115148201490034003490b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 117689649 1250 117688399 117688411
    0x41a0106050a09080637020f030a051f1703040512100e07060906030b0d0605090a03020c010215041e050d0905030d08060607111518030c010e01080703020309010f051608 74
    0x50b11050034020742e0050385400e2540030600c2d0f2501d010302c0d2001102800f03455901540c5c0d51b00d080d526118080303c0c007011908101d9802c4101c1d0300301000200c2d07142002d085d41c1112080d040744181c80900b03100c01244c44a400005059041c031003000041044d6807000441c039900b00e018001444000f90400070a41940c00c4e46c07280704581d07404001b0034480b5030307040404a0b01b5111680307030009a8000900c0003c800700013072036000d040d951401062100942c0e0100781540c0c142d00075002c0b1820401d140c00126a0340080c2020384031150100381c0071070002150400e0b00340c0503114011148804040b261115424400016440c3c0c020038a00e2104001c0d82c1024082d91551071003030b0070401c0142c076010002c00c003240705a01c0028a41c0d1510122407072070fa80da00d0004400210000350064640301e5507040314210324868400c16109200c0c41040c96070350741c403c011920240c94180e440348482c0c1c0798400150080c0d007000d0820249952111510754440825101b128460680c0e004500140740c000da2001e030540b40c014000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 117690899 1250 117689649 117689653
    0xc0c0102030f0d0e0c040c05030906010501050f12060607020307061706100f0806030f0718050901020906070b040804080a080301050103150b0a110c0306010e041209031a041a0106050a0908 82
    0x2418030114841a14240030f0b40480209100d490b40c140281020000255203500515080c15004030580c00b101652040e04000202c4204e6620f0f0390055805006d01080101c505000b040301c25507462041c0281600038401500382c43c14107400d07500080c04c0480c030f6000721000402c9000900b0401c026029a140c0100084da50520841001039004090304200303640c1c03c00380001d20004c6a00c030b45007045058525040c1000742d0316455101c125803158000c4803008003000a0910020a0130640c1c18030881d5a0800010101407a01e0b2050740d450b0885240100181c80b604070605c40000c00c3e0b5800c1c48103000c0c040c0704182841c0d40350704060015003142c00b03000d40119010b070002d13800d01c1000c1307840c0c00b03c0344660154103100d40e031180f02035004c500c0e01401741034240d0140603640c0000b500840038111540994400c505030f00c10600350060032224501a0301c40034142c40e4030101c00007070340044c01100719027240c02600641c40c80040b034680141d42040a034464400036000250f0083c9082d40605114090401800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 117692149 1250 117690899 117690907
    0x216051c05160b04080c0a0b1b0f030103030c021c0f031704020f0f040608100c141c020d021207181205031e0405090901090605070306050916030e120c0c010203 70
    0x400c542c0715480c00c40340248004444008102403000700401d4032000132050f0229540a08181781100309030340c1c1900c9120f003141c1009808452614400300741d40d070341d0580034076183c1183e2035910212100b0790071010582e0400c84800602d4040002401030b00401c2d0f002d0b41a807921070b0b5040c50010000d503103040951034110028014040143d40782103040044400444a01d0380490844d4002402881b155222154501c0741a103d1000f40c4c201e60444400301c0078948442416002c012610310403403194910340c040440401c1d00800c131009140c0d0182c880409101001410031000c1c004400c040b4105651440106410304d0f01c2401e0f2000400342e21000c2c00e8400c0740d51903000d030ba90b500c2641d079000c0c511118881c01c070f00501e145001600b240940c0d008000c010b029940c90305000c0695402040c0b281c4003a954282428001407115019000c0c500c110b46015000080356a40ca280052200c0002120030007010344458403203244640c02c11810011030071410701c2c0e03a40c2d450541403040c504445140c1450543d08248 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 117693399 1250 117692149 117692167
    0x9030d0503130b0601020c06040305060f2503020c0307060204260d090e06030a02040501060c170f0706020c0109060c03060807050f0f01080a0e0706111b061605010216051c05 76
    0x2000010b0402c1e4030440c11099034448000503402c05c50700d0074603103030040f1001c10b00006004000900e80d004d1030841403050140e44070140407078040300c04885464500042015100041c910990051003406440010b6a0801050f5a00c06090764400c0d4000140e10a51141c2c0c5034642c2c0440c55240e0041040200400c1500070003034010f4109450741c494221602a09030004240b0348003409410704155005104001a42c0c4804018001c503034083c0095648020943d0501e141101100c2210f01001c0300c03400c40f9040205940c0c070807000c4c0d0700c40c4250602d01d5403158804000202c240c0500c0c1781000c842e881c003003041410030a00515014895000320300c122070112410f185611240d00c06103050714207107070102c6250b9400140c44041c2001c2d40030000c0c60704c035466002a0b002c1c0d100722000b01b00c0d03040390140c2d2004043c018103084522500100503511440c10031600c500764410704004e00101748910009800c0182200c0320b605030004407403054604c0d070024564503100d059945201d01180106042c9a410084a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 117694649 1250 117693399 117693421
    0x1b1908060103151a040b0d0903080a05070c020d05030c010c020c0111060c0409020c0f06090307150b03070605030a0e100603020906010206040809040c09030b040f211e030b06040b09030d0503 83
    0x1803041094044202a40000e0120031404840240000a001b11f076101608004030004140d50b800940000d404080841d00e2110b0b68050980280e0941d541c240c680c03200f03502040410203150f042210030748801c01c01e45204503028010364411aa2a40141031440c6058002418482e0300b00b2100880b9000081041a86010f817000d83e410750b0084031005031a0700c0c00c001e0882c585400b00f00c0216641c415101003024000f40040100303102c034860310034864010429540302055460032910313a50b054201d10814403c080c805c00285502643c00c2e04080340c00000d480c1541d0800c8081c0004070065601d0741001d0007035060000e440c80e000542031004041030300c0c2c1911116158050049a648a143c0f1098801c50861082c400f2001843d0410400c9080341014a03242100c0095003508940080c1100810350466411160108804582d40c4400200d44094070b0b015070020070032404002030641d2201c41c12401d40301e200c00343c0301400c4190a460b95452051003018074203a118050b010030843d0402c00c100c00e047d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 117695899 1250 117694649 117694691
    0x6040b0d051911042702061201030b1f03021309050106150503010e0c0a02030a0e0123030603060109060b07020f120a050a06060504020733050c0703030e01140f1b1908060103 76
    0xc0c1704596402e0200788001009442920104005000b408002106000c15a109140610f0400b0410082a40303410030b81c1c0510011440041d5000441c180f14140c003600304e4004013100342c41070000007149900c40140c2071200784015401800550044014006030b0b0241504a0300702c13060503001f60a014010390000e690348602c00002080290502ca03110107030740078100e1000c030507640c69100d0000c0390980345c80d10400d0b0401c4078054881d02c500c40000a1580c0203102d08010b0f50103045086292001075000e2010b0640f03410a0250407200c24540304685007c140200c6100c0c83c42280a0480015035003020000e071421508a00e220b42d2040100c580081d82c400ca4103030711035203104040010a1488000840200320604041d040a800c10f8100300342004110018200c00d4404d440421100c0d004600752802c03120390b40c8015070740c0c20b00b000108050605102c001640880d6014038039455004462070311015403c091503052810310240c0010200b16000070311558080c4003840c0402c904400140d8004040740 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 117697149 1250 117695899 117695951
    0xb09031305060708130b0705010b0a0f052707030504020a0905010501090303030903030b0301090534122609120a05060a1806020f0a02010605120606040b0d05191104 72
    0x60000707000f0200140351060b14668031150b03e180c2d0310182c3d01c042e28040c540c490305003141c20b54a040a841014600710f070324602526900300f070744000796041c4001e10582e0b1031641d102c64505600c07031440326011507520b00564130030a4030381c1e804603581c1018418880c071030750140c124200c15402c0c000140182d90b88805e019044903010b107008104d0003500d00b000d500410748844e44503055401c000c0f00400388100021070340070450346001e89100000d40001e2811041c0624030f132180c01000860000c201180700b06901100c8030b405041401e4034000d448815040301c4400080070708401c1c0b40482c2d201e85500c0c0410111181191000c09421100080da89a50304c4241c0186402c903038031707a1400e0340402030301480702800130b05900c4401190764072242c0380050a01d4204680c080015800d0000218590078000c28060165448078004c0495403a00410000906200e129035500a0f02241108012502c2000301d110b008400c40f140414140c0241003072450400b580003882d002c0d42c10b100d08003a0f02c0d60065041c030722401d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 117698399 1250 117697149 117697159
    0x60103030e01080c071406060a0b09011407030905060a09080106061412090705120307060605030c182a0c01060608100e040218011805091b01030f0b0901120b09031305 73
    0x44e0f1444c0000300c150040310b0014218800082440d01c1803040080d00720f008010880711020314540d90303801c140c2d40d071140081c0a07001036561044540005c01c0c03400078042842c46420309200d866124000715255812a05a000028000440400410400303100f070001400741d034600b00301100306e080b52140e8030348030b10340c1c00b040300500c03c5c0d00007200302c8814044040039003801041c541c092087c4005d02540c81c2c000320801d448980c60400300098901c0c00045029081e0805400c1c0411211520025188403c4c02444442184c10580a00c505107052180841007089084485510b039503500520b9402c480d980c1e00300c1410302c1a10b4043c040030403ca4241401100d5000120300700e1999580f0200d2817040031180311003d400c00820010440c24481e05100c0d15005609100b000301e1340e18429501d0b070700d2549900b400d03106922051490159486038012000050180e00007103019158100481c0c0d141000740d0002800f0400c0311b500d202001003103000a5004a4101d00031f50401501d40b00c1036040307421601c40c2c18410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 117699649 1250 117698399 117698401
    0xe0a031409150c0c090a0c0c0b04060e070308071505151504050301020705010606020d020c011e03150803030a0b04050411040209130c09051203030f010501031104170a03080108060103030e0108 84
    0x55615806809102c00301410081d880e444855082580c1c2e1074001c1e92280b060340f10100040380800c2ca44103500d20145140d640d1099001d29483e00c0080b141b0241c4240e0303000381c9940054aa02c1002c211941c011446018099a02c4039107040440000081140c440130b03042c05d08050000f24000c0d001d120864020032200c4d004200e140c81c00d800503c0c403079a40410341550011030000c06005065008004407820741d000d81d0030003043e00c03070120b0300d500c07111742d082c2d0110b4288072030250340740c0300c4040ca2080e000b46400c0005010342c407846c1d10154180c45912141c61399000004000c1025100d0140c06290340003500c0600007810207656a4565805980da503034003c5501044486c45075541c03207041146056000303000c118030f4440300001400480c241c05002c0c01584c0d01e2040030010840003040f0381c844c510b50040d100e0582d003004011800740030742d0b43c1d2942d0901e001303100110305811a0741d01c06070007844040080154036014034010b40301d201c0503400104160850030042020175004004015448024a00b500e55 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 117700899 1250 117699649 117699667
    0x40209010c0f0602040311010203190305070e120d0e06070c050d0611070c0311100507060c090b0c060105100203040e220b010303030b01080606040f06050708070b0c07060e0a0314 78
    0x1400c0c611000c0e00481d002030240e410f102c1e1a40c02801a80d0040030004040c01102c170042e40d0328464080c0358410030140c5040c1d401c3c41d42c8a54001130b0002e90b07900d0402000304025000603280c80c041204600140c0040d03108400d410740000300340150f220300f611401d041603032030340310350b19003900520695024200b48030740807042100a5102c00d481007030030f81c6080e40742c90603405c0c00120002c0500081703407441c002071000e8102e40b401074001d1503104100c0d9206480d18000b5a10b220180c0114442042401412400411280124800b62065030349800050011b580340108004100b2442e01d00e64065402c2040b05008031042c00c03040992200c54158800f681050a4401440311001d440024112158040c004810150705070411120004241c1c0c0d14111612140308000301031195124912070042580c0d02088001e006101400310b0500946619041880c2c40d00c0310031520004a03604080000000740400800246101e0300c0445003520000348603c4e02150b501600724200d4201e003a002a01c08114110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 117702149 1250 117700899 117700907
    0x190b0a0915050a030c0614070206090d05010b12030a08060904050607110304032118150e01030e0f0f06010602010e030f0d0b120c27041e0b040b0a0606080709030204020901 75
    0x1c0c0b1000d00b0b201c2d20580d0f6401c090303041c1e48050240b20001070070190601449100c0d641907610550b00104464908880308040240503054520300310741035500d030020242107030398110803d14640e0b442c00285995440072100100701440007064540319601c10000d100100303100142351584200c01d41000705005450010076803070360203103500041a0070068071300c100c00c1940c00c0164061148051f10368010350000303c051701d41d81d0043e50182c411114100030750516424031130a0114000041810002034100e15a4031070b5060806020354901181d005202104030800c080100e13034010840d500c003c0090000441d000c075140d00c9226139140c203900b4041005646035020341e21030a0100001003041c1800100d01d040c60b5151558400014442e20f0000c00600251500c889080d106d00c207a07001140095403a0750756101489891280d5594480c0025008000120b0030b01c541c0340242d0080e4682209880c004550344140d40ca980c0002040251580c2485800c58000310014280c0b80e04950158541c01d038134004072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 117703399 1250 117702149 117702191
    0x90303070c020a030803070302040f06050a23070f05011b0c0c12031101050405061f0513090309030c0b091e01021518010c03020d060609081b2403190b0a09 68
    0x145c00c01030000306002682c0d41642c01042115181d4640d01102640c1c2c00301520540140c05821001c82c600c010103100f41501021810450300464440303d003801042e0302d51040855020310700301c6082c4c0d5034820030a1601c0180418030314504461030541e02c10b664960f50030407400886e103c0d81440c601c01d1040302c001c26004000e60000032400d94000c001c00e00d03190410a665080c142d41c190a841e4000450924000c40c0c2d4082509588015262104a20a80c0d106500900c403803c41502040000040480040c1408006400410b90105100c0d01e0310b002c2d2041080305214102c45e081c10214002503200d040e6000b00c0d55502c2d0440c50411b41810b540e50514100c83c040540c48400659440e0581d02040c66130994050491540c0ea68801c10001c1c0d01e80f201a528181d00f80160600d50f4803440440084c0b140c509001c490884c03025001d2000200c080700c1c041c4c2040600d94041c03003100004010000c00c078210f44103002d08104114404d121240c4090049418004c40d4001c081c00c41383c0301c90f03900040204d403070b90780 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 117704649 1250 117703399 117703403
    0x10513050a110c060402010905060901091404181a0708010315050402030c0a08150903040305061303030f0f0204031a041e030207050d050a050708030c06012c0109020c15090303070c020a03 82
    0x1a98520000e0301d43c6494420440c1c00328003089011202261a04001d0151143d034241a1183e680c01820001440705600c0318034007042d4420740710715270080e4440202032031006080c41120100d104c407000060f68014608028030100412507800f00400100d146010031103518155014005190344a90011034102410440d0040d040310a00320700040615000500989245805d50f11042540310210480d441c0d20440c440600f1907031115011442145a4404e03002c640741c03181c01c00061607030f4281030140075680c18041006d607182e8082020028041c00031078050148a0307101c2407100500d403035612101740c044400c00c0d00481007026030340502098000c001070001350600811600c11840c491400d29a00d204554085501e802020302c000395042c00007003500c200002d01c034060010707a070038041e000c46d02d00c002c01d82d04d42d2100190941108040d407020a80e45c040e0049100169035401c1103000245408a40745264001100b05010805856004016030340c02241c1d03450480680d5a2900014502100f03075000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 117705899 1250 117704649 117704681
    0xf09130b0f150301050421020a0f1214070506040b0606040503030c060402040b190b0d02070602030702060115090605030609100512060a0b0a0b070b0c041502010204030c090203010513050a 82
    0x180000003180c544240c0c03195940c00020b22450790401d0a25080c0c4c3c10540e0b0081030768a10302d000c52590042001d481da2103d002d48121285480c1030b8556401148006100f036910482040f154140150b02600b8409410030301140f140ca0b260075907031202d5075210018006046840c0f4074001c6101a07603200100d4008000c001c048a8841000030704180d00c1c0c15050b141248a907103000100451820200c054a040910210024082a1404001c8540c95000304a1034070740682c00c001a200280c0f0500c055070140b8840e900910035581040d2003013800310f4400c4010401d0141d4102c00700520b96005044130361103141900d40c0103264988030710b447c0d40c058281c0c00803503003c0140201c460040d14002031540c841e80c5001e0050000030b410f04184184041140140071801104110500203e610b006036143c1000b806030704680340c903682e440840c90b0741c410005103000603500010f081091002d42c5082001600c20f10310110b146524000014610381070f0003040b40b6103261542c0028401e50720b258010350803d503007405 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 117707149 1250 117705899 117705901
    0x3040f0b060a051e0f0406030213020f13030501050f011a09240c031c050412081003060c05043002011d10030204150806102d0309120206060f09130b 65
    0x803240d0f003040641c003400d4000c02d08804175803038603d043d018200807640c01401d0200c1c0c00004118010180d0b01c4404d494000e01402c1011540500840e00b01c0d00085000f48000140c900f44030444200454040e40726501e00c1e0861080008110504811030f04c1c6150708032246104103041994046c01000200c43e86941c4801c0811410391070200400141202c070801d0f405100c0c01340107403840100302e42c0141d6010b010b07203c84038420b505442c09400095007140c2c83d4410700190503503d9403040c0a981c0c00d24042d000080f40403404020380c2101e01c04e0800303034080040c00884189030b502c007408100d6080090180c10400e1328400323203114480540900442e218003620340400026130000180180d400307442a560032417134051400003024843c0640c14041c03034004090f43c0c8483d603207a40c00c40c0d944c0880752131901c001e00c1c6500400804000b26012000d1200c0f9030300c02084220080c2080d014500d14814502c2c01c1d07402880030003031103556002015080490032104066640c46090a0011460300e4900092078194494 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 117708399 1250 117707149 117707179
    0x6030114150a3906090204091b061713030521010902070c080313170f010603060f05100f120303020c030a0e040608010903120c0509150d05010b03040f0b060a05 70
    0x10310103402c0315441a00680501d4041c04051400e1100c00800c0100104568244001401341d00320a400d90300040000c102c40b00c1944482a500304401e0400c1205c03040c2140400ca200d8001040350506030090a40404510340781e80c02d0302229106038402000c02a00103290b000c2d10307054071131860000e41254140c1d142580c584591000a42c03192509075819840014006048140041101c2d40010481c00f1201500e1814a84000d2000b20315038468090095004881c0e804800344038001c0114040d4070003041d108040c2d00d00340d04171407000d0281001b1006034441404082c1c9407820503003c84580e00035507031000d40d00303050460003400b4162070300c4507a000004245030354940c041450164000d00312030400c00255104449402c890034000000c0120300881c4910865003529409050b8940b402e04240b40307040c4c405000512842d20200360071404007070101d902200c5100d80d1090601400510200350311b1420140c43c1e50300d40f0302c1d88860050031035224a00184e0140c491800070300081c48090f02040401d1244 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 117709649 1250 117708399 117708407
    0x501090c121a0103031d0a0512070512060105031e0109060911031605030c190806040f06152d030203120a02010b030c0109032607080c0c0405040206030114150a 70
    0x94040c2c03000c5080e00351200000c03031030400c003d040302d60640355101c80310780300c4001391b40041000c03a159920040318000080c05440e4901780990541450028109142c103160422071400b0500c3c06443c2558080001806662030001d05040c1589241103c0c809610786440d0235400b6003802c1350300400090400414004028488901c615040412402d0345d400c06a40d900040740e0324500d128540d455030207850700784a1030414001c0300507241c100150802c6001d44030f480039490700030145d508407201c1711180594000c0c071040d8401c003041c180b0140142d03e00c4c5444c2a1101d0750b940001e41e03031300002c00c10340e4156149140ca0312843d08000c42c2c1c00340960b030844860318200c0c1d82c59041040c1c00c101550916822400e50300c0d021442c140031607030503160030340341a080d5110b400c4500e0f01e0b50b41040c801c100c1c9460b01c07002d04034880302400380f040c070603c40140d85074101c18883d8240903a0031121801036040c80140300050f55400c05680c155110064030000c02149a4005031548210301504203541e000014400055640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 117710899 1250 117709649 117709679
    0x90a02070611030f09061012080d05010b1909030f030305060402070c0b0a03060f030506011715090d09120c03081e07210c0506240301140708011202090c03040501090c 73
    0xf105940d2007035170382e404841c1912150110341024035040c20341002c2c0815940e03a24201745450003641541d050650180d0a40c0480c3d0003030700304d210031305e0010506040355280c00403490140c26082c64423800341d6245695215103210580c84c0101071644800000318942c541d0b50503114002c0d00300d00810005641c0c0e61070216282d10088542c00001c4c2040c80c0030400c02c079411000e1040b42d5020f030090045131304e480072420212040d040480b426001e0900b45070303101807403010b00d58000c144801c080c00c4000118640517214500d01d41c0810820304880d180030740401e80c000e241300e0440350040c903e9940e403010380303001c80011504140210705a00020628a0520002040b0b28401c1c0903410b5081c450b0314031502094803203003612000204250f10960010710090300c07101e44000702040b130001da140c0700204180002e0030345410182000b0000b045c6010481000c0c0e205800e140180703e000c02e00d60040c20f440e00810300c001c100415004c11958008041000c1281c00d504c099245504000d0720881c1903100d03401c004142c90 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 117712149 1250 117710899 117710911
    0x6231603080121050705060c07030210050430030f09080a0b010f05120d2303180c010e06070209041e0b10080312180c0310020a080109060302010509090a0207061103 72
    0x7101c0e00b1105041d80c0c1c2e200030700d203c0e80c0c0110040083c2c5180c4810054558000500d00751640030300c03800080141c840820041c0f02c8641c03502d030140c5982c102070300c0004007498079401000d81d1541058412182460901c80341107107825280c043d06680703040c0f0b0f06032450701c960742c8084060b01c18080702c0000e120352183c20314140d6055034070300b41d02030356284108950070082082140580c0c0007039500c059028003810300c605030044400203481040340305a00188103a003003211414899040c0f1130b9900c489030014000e0300301c284002d08107a02d1001000000c950f541c002c90340c0c000d00880c0480089001d1240725810a540303040030002c181061116131030324003000c0b40d00360f40c1c0b1801c2c0420f02d8808101080302000351a10343c00782d403055034001d60b54a201c0422541000980d8995401800180c41c82e40c0c07030501c80d00ba0040840c0340d0141e41e900005200405800050b4440814945030200520061b82d11000720340e24400202c400c40c90395110100010b001b4403402034001c282d41c1c50007103c5480d03151054040e603c600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 117713399 1250 117712149 117712169
    0x50303190608010204060f0819051608130b0627040302030c0f0714060a0c02031c020d02071a090102070b070605160815150c071d060a062316030801 65
    0x5942d950154240d004600405001c44d48905ca5036820a100b503890541c803110b001c891801c0e4001d9070025000302c41040d18074030443c240c03050920605503000100c1c039401076203604450700400000e80301c2c43c54481000c0d19003072045a00b01c02c1c2c0d040102c0c1a00c200380c04105444070a0b50300d0700346031074041c1d03070303503114002500c1740e4003031440854255a00401d0380f40449080031001400742084200300181c41e800700444c1402d0000440c800c03005038500304180030301c420403410f565103000f10b10b200107450700000d140b4000455100c59002e0248500b2052a2401105d004040e00e444500c01c0740140c1c14842c081e049145120004034072141400042e41003070740629103154001c21f000ba0052000c6070343c0d52088803842c2945411500e8030410b0b05100c07a50080880c0034412050603c620701c880b413402c00c90b15600c402480d00403824401c0a41d2140100030b50099012180c18180c0380c500a0080c00c4480c044009060005107040c8980c0c03072402d0300d411103620400880c1a040004134614002d042d464003801040910 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 117714649 1250 117713399 117713411
    0x90906071713020103020d1b09050f0a180e0f060702070e06010318030c080f04030602090301050a15030b0c07060e03120105010e0612060a03081b010b1c030c03020a05030319 76
    0x1c40c09080025020300692020050000001d80054010398410004880c10a540340b0003407203850880c402410103140c20396644220700d40780204021600c481c10000758032035007803000b00704588104240c9241c1a807031280780100c0c1540340c0e503001c1c3d070038825038000101650241030200080b01b64003040da0703000d8820091a0f000380352075100044040360603c210103140038025200b02030120780030720a02d004052160075454540002807480c112660881c0d44104d40c840d401050040d164034007806a25030141224500f0051014031030300038080502184805842d0560803404251821030351401c4840031500907030148980300707000b00103554940c807200c0a10400030700c1000104880d0300c500c010306250240203040d1401e0000026804048501c00f07050f00b5031000d5889000000160500003401003a4010070889002e00c000b000080e00355034081e0720151103600b1001e80e4101250a8044907220b41d501440c201c24140b806281c1030740380c502c54042c0903020384404410000401c4182c0071022919110760300078014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 117715899 1250 117714649 117714677
    0x801020f03071e053702010608070509040f0f150c0905040b01020d020303070f030e07030302071a07020307090b011b06060f0b0708090603101206020a0905060307090311040b09090607 80
    0x1103c0318504900000383c0100b0242e000a00300000c0c8104411000f0303a00650307031607414841c0c4403c95248140a0141c6d464000811112406205550040c101600c41c4141440c00b5600e030300c03004400365030007429502201c2512050009800000c40d003000344035810440c03080380800152031418503120b15407055081000403a4a5480842d915064030f0740c1d5002141540c951038000c0c1c2c4c90741c0c01c1c0100c4c041056640c01c030f0318000d010200410741c000c600a40280107150705145039101a18401c01040038005001c100020058800050300c1e411030f000c1010000f048951500101d039424a094003418140d0a42150b2005009080d840241100e45c2c00101c0848199034404199003401040005480c080043c044405d05040030342c01140d00a042c8000847c02036102c3c10348290f41c0740600c006035420f0f0b80c00702d02d5803c0d054026488170050304040f40c0ca2415440c003140020f15508080c000104200503680c82ea00082d12241c204e91003070180209046024238088481c10394500046800200280c40c0d8003003804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 117717149 1250 117715899 117715937
    0x1b0b041a06010c02150d090203100c02010c05030705040501080709090e060601020c010e06250f05010b0301110c0606010f03020d0e0a020f04061a030403050d022a0102030105010c06150801020f0307 86
    0x2a143c0c2c090485e82e901040010150625004080c248040b03e8485001800503a010f210710a807841d2400c20008801031002d60082c215400e4000c0c0c2d1042c044100180b20311903400c0340a85080340c10910305038003941c2c7c44800c01c507501042540b00d18a0746040c40201400c4c0c0001188a61081000381e0865a200c560f10004444820010308941e41180e020044000261480b07101c2d00758103600c0001020540e422a52003640a07031040c0b8064a040c1d40d11030081096190138082c00c43c102070040506820120002035181e216900038003414140b040019254025500070b0701540c003d00e4241504006407002900300e60303200c0104c0d40e0b04a200b140038405000c0e0a103854881c03a000da414012000d000742c620f002c100d04182d41301a100341c0c1813040600032a0b04852490005015403075800c00410340800e106100c40170341c03480420392914241d006100600590f6401140c00d02c00d0703500b0030b001041c8030040b0400c0900d000300d150070181c16540005851a003101404001314040c240c09e03030360301c1c0281c012610300c80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 117718399 1250 117717149 117717167
    0x6160624030f1a0708010e0c04030305041707051201020a0311031003020d11030d0f08070822020a09020403050a02150c071401170f0907060e0f011b0b041a0601 70
    0x190030000002000e0020411542d50356100c0b502c00c20a40710401e40c034141054080400702ca081000801c0360005101480003111402e07004500365803d0340c1850300315600586180035a0254540c00d03003030390b40b1050340300d00108529002000b0281506080a8540d509107000c0d50050361124082804d0040e03502c01200ca50044900c144148004204050700319820003100c00c201402c181c0d601011b101344400700399403c2c0201c161111013030700c0c0c0c903c03038800720140904a444001c0c030282c01d0004210420015107502c1101c1c2240d03010540d103035031004d00c052000a00d120b00c0341d0042d0300040d101180100403c44009640d4204a000300c481d42d0300004030114100b40c500c1402184850b5810103102008529010580d48209040506000c400081d4603544111040422500b0700754003020202400504001803143c08090025840c01030201200c40300442d4000106100d0641004000b48600c00800785906184010740d0703001035685000e08203030178a8a003400d8007540b990346103265000400c1c0e4540c000c00c075003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 117719649 1250 117718399 117718451
    0xf031530070521030f03010b030a0b0103020712030b06070807080c1e120a140313150605010215060a030c0e0a0c0e1e03120a110f0d090b1305061606 65
    0xb2200070f440d82000761801d004283d50155880300340202d10303121311020007550290045280d12900ca00c0c02d212080c0503510800186c9040c54030412907940450400010b0b0314142c500c600340840ea003590300000c100c07948600103001d00b070807a000c1407460130013a200c401040780c103272074000b15400780a8030758103800c401c3d09031020aa8107510220794206518001c4018002000407800c004809011865404806070302c112286070a1003c480b00100810916000c0380300042442c200420241c4d0070000080d56034070300d45420300c0305020800001200396807005040005107130300c4495446042d60340c011040d10580142d8403c815142003660030308109104a0400421110090503c80c000c80c8415405141d60040f9440a405000e01d44c0c0d40c0c08808080c03002880c0200702d40e500c056031243c400b211036040a180f0700c6c0e1004c0740e030854035000907401d0b03200801da02521151001241d40714884d004028400c03099a004036000400443e03101008012801041000c90041034184840c035895400d1a040082c80f15074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 117720899 1250 117719649 117719659
    0x4062d2307020d1809020a05030a0f0e0307200d1b060f1b060603080a020a06061203080103021504031b08010c02211309090803101403030f0315300705 66
    0x80e00c001c9200e1300e0b81d012003501c1881c1864000e0b868100301000e80e4480d070392032008036070f000003404440b58241c410b1003026420000104240d80b000540640c0728460802c020b00307102030444201c0d00300b8a892000d141d80a200401e03002e41e8122500d4604501d00d032216010b188021043c40004807030f80142d0706680100b85503904c402c0c2c1429803007221050302e102c0c0312043d140d0f60782d03800b000f02c001030400c402454483c0c8190024010355150345011020785040350002c21910b41002103107000241c02a801c10305480d4103c4241e98503020800c113012150055610183c4226419480d0400c0c1a182210380826141840002d001580111009076680c01c2c074040c01c01341c2c11041c400c0c03c0140085440281694902c40c48000b000b45d0365910010b02511200c60080d6200000081800254044004107000507c8500321101005031800006a10380c010a0344941d0850f0300000080c903451100d5000c038441080080c54070384030610000e80c04140c07004680119840e03114400900003040300000300e5108950b00141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 117722149 1250 117720899 117720913
    0x120b06090a0f031e030f11240a11040f03030806180703020711040c0c0201050d09150b030d09030507030308041406040f060507020106050607060e030910020a05010506010e060304062d230702 83
    0x2500300d41190007001c81f4500e0b030080a10540495020f0086451480189504032300300c3d0400801920894006a1108940020408c000c201120320001a0403c0f02d4042c06e18214503031b01c42c03003ca0307100c2110941d00e001d0f001c3c0030b46c00c0098642c1c140c0d014061260282d001c90100b0130564007030000715415001175101195151030017500640c8500010942440441000f052959085d51408928180003c10452468403030801c65120f0804100c1c0700c2c0220300615003000a28036549406480c0c00c1c02d400f0180c100001c83c00045c080c4002400174900c40c00e907a5044170500e2038070f400d141c000c039042e200003103440d5401c002c0410036280c8140918815184020720061808820b66223120081c540303041080c20900062024100503075801c107840000d84260340181200050514010f4210b6078003c000f20b050245c1644a140951079850a480e40b00c0d1b40000300207400f685d111001440030f00e480700341c00034003405020011500280742d000b014031a820100200c3d025200c007100e40740c41d06000c40b104030040e4001d003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 117723399 1250 117722149 117722177
    0x6090f04230708010506100302040b030a0c02030f04080a06110f09010806041b0203120a05131101110102030c0c100203060d0f11030a060c0809010b01120b06090a0f031e03 75
    0x410320414814582000200e90400d0016441c1850842e51003100144d541740304000803400d00507402c250099540c6011444c0504004800d6014040038000e202e4203580c0d2691460024020011680c548440e543c081d5200c4c1e030759140c030780d44da03000000c401c031981c1d800c00100c80e0381400e09800f034a181001d040d8825042c24642001101c21a5004044681c050303125000d05000101050b220700c01d00c0c0341b503405583d950714403806480343d1807400341c84171846614010401ca540d0b14018001340c202c0e40e001514a41228201c0e0040301c0030901000c1210b0554400400d200c21105540024881601000192009506021107010480c00110f0708146c001040740b202c0c1002904029031a0700641c0f00d001e840640b400000e000c00c0ca4601080012500c00d03982d0b0f1011048541c04c00302c115404160b2000900040c0524400240702c2c45440341c0c1d91051039112084002c6035521390003601e140d45405402e0101c0d0a5075840207c3d0300300f02030b103c155008607002d10b210345c0e100100c40e03404d6030064054a0b0911514800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 117724649 1250 117723399 117723413
    0xa15050115030b100f2304031e0b0402060702041b080105030d110c040b030703060903031401080c0f100201110d0207030806180c0906071a0103060b12100e0304080a080304060506090f04 81
    0x80d2000b0000c0010841c0341c01180105611b401443c095101c8002d40c640d41076103020500313501d8400019061800e060003030000a850b290782c0c10b6000e0340c181c48050b10f8803203600c00f00700500b00c940e403100c0389000d2a4180a190541c0088498100c4004070100d9140c47c0d0822015603542c50b500e5803950560300700c000013483c14280364201c90300c141c07800b404494106699445a84c2104c40d40d54080f00026200c02e5004101240340201c980500306400140c555842c0144c0040d070141c1c495080c980c0100e00300400c1e507840d54000e5002d136030a802c480f1203141e5140c6101d15824020b40c45241c00702c000c10201000b08040f410f243c0ea032b09062008c120700c1c1c0540ca07211180c0042560308818a495402031040140400041c0003940e40c0d0308240c0704408110840d41146040b505807056040494040c800c0c40e10303e2502100e0000341d0104480710581c001907515040c070030203070031485503411030450b500c05c003425802009400c0d03004610480c00703942c040040e61141c0040000228003950754800c030b21302190202d00410b0007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 117725899 1250 117724649 117724667
    0x50c12090f030303070e0f041803030b130c0c020a0b0a08010b090609060a0503040b01140117090115080a0b060312070303050702100e01090311060702030406110a15050115030b10 78
    0x801000c0384803032050792000900e1940215501c000050a01140c00014100b25440c0f801080d8116011700c19100c0c01d02c091420079107540009001c040d20f6521181c1191075212200d00458105a802d000c0c03104035100243c00e42c42410804c9014250f8000005044006403041c5c5e64505610394403100780d6480c2004080454005918007a4010400c100d90b20140d61404011300c00d0b420551620b944910f06801d01c6401c0c412305074041a42d0454640c9240c20f960f81c400002078641c2c20350300780f520454694580320b13401485603481d9202445100313800410100380000d00a42a01e00c5036280b044940d603100c09240e00e5401d10140c0340910302c03051101c10000380c000c4c2c0195500a5682c411601070780a440e0700c801c20b446120302c48450300e9644801440505500a0001c0880344e81e0bc00104407030b042c2040d00941d04e02c02c0384290b40800c500d40d02c482800607005d001030480c160700042603c0024405240e80e4000785000c5c4200304500f02d120303085082ea98080d0040350f80c0c0e108010500141c181d8980c0041c0e9403140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 117727149 1250 117725899 117725917
    0x15070b0610050d051305010b030c060d0e0705040608031b0a020604030f060b1302040f060804080d0504020d060203090114070206060307060f030b0a1e210f170c010c0f050c12 76
    0x4284070031640792540748100b600c2009105e0a201c001c00c0035040c00307400c4962001e56640a6000a86240c0d0700391103000440d40c10f101d00d6a030001d504036101e0404c509084040d04440d5000b400c1900000d494000000036000000510440c600c1454000301c5450707884500c0d58000b5041070303044c00104040b6518959452115000b0040030404014100c0003442c401180c02480702c0c09540811b01780f04000030041d1544c0038201600b012040c0d420151074120320340c007030b80188440950312507000604648500d00d488280c02d500000139922401c100b60054080c0c014000071108020208000440180c80010340d68061000a001780560b9810240f00b15403002c0e80c00340d00c5003850b4564581c1040c0303464011202008020030151000c0504c04022243d80c104440d41c444171407a580c0740c0214001d40c903007142043d8110b9115074094020300c018a00303000003000082035502e048002040c41250782c0b006400c4440090f015950f04918448040c3c1309a88070b0003004000149030340640e001d1004106100020403c0c85 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 117728399 1250 117727149 117727157
    0x626010e061309030c05010501090c0804021207030c0e0f06092206060f0306051f0308040909020f120c040e0303070c020d14011b0201050c0f07020405040f05061515070b0610 76
    0x50b2421014820f99400300d4044000030035505510301446070a1090718090540300380300b031000d000801001014081c000c4d10192041c054034411700003c48082207600f00a5a02c140080b1079241c0e584895482c04804640031200941c9403000150ba52804482091160030700201e19581400414903400c8112001841222400d40c2d9070404034901600020f81d10045114010200711803070090034000d160f400000f44120940342c02c070418800598800c0581c0d042c3c40c44d1090009004801d40005055100e000540c40d8000385190945207030752001083c9400102403c0d501803180c0c04280390042c0c0c2c1c0f8401110b108000800200702c40e00107282041031076824a00660303414044850407000d66013112900544c8003842040c02c207002c1c20090b020702503140c0c464800d00c0050b04100d04d041c0500340520079460003c1c4280c0c0d1b15400141003001480d84003250319000380031980c09150943c03440d40e0802100c15072a03c03400c0155604400c0503140000c8a010715885000480c91391a6881400581c25159a04901384 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 117729649 1250 117728399 117728419
    0xc08060d080c070b0c0109060b0d080304030503090102090604090b030f21090f18010e070f0801030b060607060903030507091202100e03100e0d090803030702150601020f0a0803010626010e06 83
    0x913a06100182000c48904e4000140b8065240f07401c800f1039420b504400d00400da00810080400e0818094030350142c1c00d4100650350380e443c59002c500a20403154210b90120004c42c000c40c443d11076074004220f00d00305a04550f0b000301501160707940d89070301441e9440e2482c8511100d1080c0402c05028020840000d42a0000c0c0d0301d4030000138074409000b00851a070021854010032440780241c0c1d010b500210907050480303108282c0100204051014040900140c0942000c0b41907502c1c2e26044400e803640204003040b41418500e0018050300d4152580380010740281e00c04603d8140c0305022480c541d50042181000c034041400c282e074540220031105605014211020b0510320361401440103d000b040c000d010303c0c00d05070801614104403900140d0707a5034000d10800c81c0032500001d1103441e80c0d4921a000b04255a0800100d1804803181e844040a0080c2c3da180020000c010780514140c0e81c0c2c3e521440e18106894015000346242d46901c0c007400b000c641c00401107204051540758004502824070701c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 117730899 1250 117729649 117729659
    0x928050307090f15060f08070c0203190b06040c120e011104030501020d0609050402012c1203030a1d0d030c03090f141b0d140a060c0f030c08060d080c07 67
    0x500007942d201401c0c1d01d840340703820300d81c2110354440c4030b00c0307805040e02240c6580c0c1403e00040c02c0c5000c000d401001c1c0049403022522250003170100c1131017668000c2c2110680141c0b40c1d00d0100c07070704000780c0440e92144450042400c038070381030144400741111907940170010f2a042c0c01d01c1001d01000c1d80e11070015541c66950440300b903e00c030f001b8000f4500640025075588412095070301140c18a43c41607000c540340c00b05000041c2c5e03212022212098903c0100c0f80701046084240600c00801c03040350760b0004100c60100214880440558410740398000704001e040e016492240c10580c00103019501c9030007061040e40d996010768001040401a441d00044018103a600c64251090100e01901c4659a1903810340c1c001d501044200e400b004c0c2846149013511032000400c00d40715a0390801440c000c5514000880d2100821500701890b42140d000c1c05200101000640400015040329000a0405d50a810707914000c0e2100c501681000d880c0c43c401e00d42c5138840f03940913001041d12901c0e500801d400052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 117732149 1250 117730899 117730903
    0xd090b0f031005030a08040608090102070201080103020405090111031614070209160507060606030e0c04110a030207110301020711090c13050f19030302070f0807080745050a0209280503 81
    0x405c0c0ca100b04640c0350350f1070030407501802070100206902072684c010010800140da22111581c1140e0f81900c000c202c40c0c50745882c0354054040340c008001c0b00c00000c0204804054000301614450b07126403500032544d04072014000551084020107500000a0800300e00100a2840d901e0740d000f0140c60038500f042d040e43e80e0442901c6681d4851800240c0340e1002c80a014004e00001059000840d801c0207504141078484000340104842c0710145540460044140305410300100b1101000500840d81e4083c50700d0440c05070b100000149000c0ea42000018600080101c11603040c401100f10317004e4481d280008004c0d901c100744910395040a401008145941c80d4480310002440c400d4000d8140035007004482e12038040c2c50b074030007660790340807400c2000300c40e0000c03c0400a85403503c03501188410f40c0801c2c060240040d02c2d01a180c41d10300800b844641c02d2000802c0901951074500f4440c42d10389590010a9001d14581903501094240b44810f040b41c06c880701d2006100740054210002d61b40d440085c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 117733399 1250 117732149 117732163
    0x810080a080706050105030f070b0d2409051e0a090c0e180c0a050d08030a02040b0c0303010305150601081602240108010f2c010f0903020c030d090b0f03100503 70
    0x41d500c010100e40402041030f40d0041c24050072095004100210544000c1599000e6078842c1c49211800000c1e08003145010303810072000500d240140c6207034441001e0600144c01081c0c8a004002450040840c407803c12058100c00e180d0006036400c0003a44030280204000d158481088603228450100000c901d285941e480c2d104884900d45006c034000074001d154145000b10220511581703404c507041c091070b540c0014070160725800c030340c610703440c1c0e50344e000c1c1e03400284201e80010032142d00c00f081e0710319691400401941624812020f4840303001c80d22444242c4000306440c003601250303100001501d0308144221b0504040c142d4812a005184802e01803a541400c26000c0c43e01c800c400f100606c0b0500342409004000300700e082e000c0041d521002001c24289000c1a000e20004454441c9402e20200942150040840090040181d80c507946030203951003200c000498003a00800b250f14121a000c1d2039542c0482d24014941c2d0300e450900e10b06485d00d940018580740c0d1860400d9000700302500c00304512 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 117734649 1250 117733399 117733403
    0xf170705130203070e030d02032704020c030a090902030f01090c02010b040e070e010509010b031b04050a09140a0e03030a09020a031a0103030914060711030c040c0909060603020301030f02010810080a 87
    0x590760700b448034004100e0f40317034102c4080c000d6000c0210400e031170344d00004441e288501c00c0b41041862030b554204004041002c03012a03480350012400c803400c030002100a19403000321303803101100c9a681d8103080f41a0b000c102d0b00e80101418500041291048a40000060075140e20001410100d030000040841d8070501e049072840e0301003801400003202480e451405031404607000a4658542001c21a07640f1001b480c01c0c42044040805846407600b10303040d50f01402c8000c000314060354981010200802d03c2030314600c03000380e0800205100040502c906191800c0b890050341c61596006400c5018080b000781c1260415034030300d000130200e284c0c940c0c1c3c0078641c908008000000d52640c10300038070f020b000e0b4020811580141c3c424400c02d070344107021100029800341118a025403a140042d007030040e02034006402ca8108000550100d9001002009440c00300d04200311558881c0c2c400c80403030000f40802800c9503039410085004d98040d00b2515032048210080641860712191903d06200102c081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 117735899 1250 117734649 117734651
    0xa0c0f090605040509060106030c0c0c1d06060703080622060803030403030506010f02060403081e0708010f061b0f110a1e0501210c0504050409051011040f17070513 72
    0x24800040c1a0207040c0041c0b00864090245007400444c01c2e444510610400d000d01d40d403207483d0030a841c0138900120300c69802040c07005426654640030f02e03860382064821146040c121002803a1841e02d003080d075011036015aa045510355420080c80350a0b1000100e103036102d4460480c80c4825141802164094007032040a1510f904061034041c098172805484035050140716000c0c403c01543c001203403a4410b0b0145000809a241d280300c00c0300c0d214045030741d40703222401e000422102c15004540b00e4104d4003000c1d46d01e03490300c0e030300c0400316502921802d148c04150012180480410005100e00e01a580503030110100c46080c800002c08039242c0d035101e0b96a110450110307824048681c8070190042c07a080c02d20808020844184c20b1b10b0140824500c140142d5550558160792320880644001d020090030410803a00c0e141003090381c44241241004a03641480203042c1c02598110a680031911484070200c143c1e130404280c1442240340796608003680c0300340607002586541d401943c0d44c6c15854900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 117737149 1250 117735899 117735929
    0x1b120e030f0a020a1104090203150c0702040504060c0e090702190503040b04182003071206080607090801060b180112021e03160c052d03040605031f030f0201030b030a0c 74
    0x5800c1c01c00c03048804031107100790f242c800507d02586000c00d400d2198490700d152440d403640e0f042d0004981d8000e141000c0d40083c40d00c010403040105913800000e0840c181e49941c80154211070800943c160110f0b84031005030801014908102d82e04460035020034072403816642020340301e010b8402d1a0b0031540c000c8240e2060003c035211615010310070442440c0408000181c030341100344006400e0b00c4003401c07540401c00b0b0100d0014552400c1e40c03003030b0081e28412050702e005007400d4500400c5c8410034080c0c500e0030b51805800080c1d0000003000c4640168044c050642030082507401583c0788640c010180c020345400708002c42c4452248000d0084840104256030303100e08144d0290000010ac02c0b82034000e0090860030400400c000040b215040051600c0303031252076a0380c02c0310000300020b09402c01d030071344001705000c58400d401c07801442c03050924242c0030341c4a649100344511a89a14840a40214820002080554402e0b00110340308800501240e4080b100307640c81c1181031135582d00100c04050515 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 117738399 1250 117737149 117737153
    0x20304050c09150f09041103010e010f0b0f09010b0a090b0408030a0f0c051015030c0b12060904030503070f090b0d0603031209030e0607051507050d1b120e030f0a020a 73
    0x41c500a820480400c580c2c049546140d0104466100d0640490302c00c114002c00034080000c0311f03c0156401a0141c000d00c400e5401e4003810380a0110002503020080c2440a840201d0618260301c400c2900d00819548603640780c0890411580c2c410a281020080100e0300442c55405060081c0020001400115a01c203080180202600c101910741420842d208140b280400c20004071a0b581c240c042c030340021903c00f0b070a6244210344075680000e081c58401500040e00d8541480541000c0c540c0310711001e410f90300c8500300700350300780f0480e0000c0c00305200740040b03a41148102100301c102d00943c14215140d03a203172014102c140d0064410122550744401e81801010f50100003803840d072055040600920880e580e000d002c081044031103a000d4400440c143e000d0000800800c480c0d0b4440c0004407849060201c0004e01c90780c400390041244604103080181e680c01d100d0102c0302c0710101542e80d0002d0741161074040000d089503a042d0510361100340415280c43c1c80c0b81005016003481c0e43c00500e14070300d5034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 117739649 1250 117738399 117738409
    0x601080c0a090507120e03130e010302040f1803050306010917060414120a11070302090408040e0606090f040209030a05102a0c0816150920030c22020304050c 69
    0xd50000044a4240000c4c00320076a08840c0122440070b0302d20000c501c5141240c403552850060800840c04964400000108441c5200300241079078020785050107942c041009800594501745000e40da00c052400c1d6803800300e44503201035900003205240040009503a40301001100c2151144005140c018200b84002c00c4400440d680c0300d0f0410740050556095101079140460141d0103240090203500459511800e00602142020b076a0050190740740d400c05081682c01034000d4050320109080c11004144246002000d4841c8140002d0180d400c0c800c00c1020b00000e500312001d101c1c0c06204001034080014030038001c02030b8880c800c81c00001c0104841200041e4480341580414000040954080c1ea036035100030060707102a0070040080d035542460312800c40380c0806580140680c10000b015100c404040d81000c0e0b09280aa0b4009030442400d140c040d0710400c086242c95031562005480c0a8182400c0c6a00c1020341d1505901240501d5841040c1041c0e03802103904641300d800040007601c01d0310741 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 117740899 1250 117739649 117739669
    0xe06120a050906010303021f0e060a0c020f070b0703030207020418050309040627090c0b0c0c01080f0f01030b090f10140903030403090306050a0f0213050a0611060109020307020f0601080c 82
    0x290314018030b155417450300c0194495500c09180e008410039000304580000264026454a00700031084410324074104c0c207218000d16507181c0e4500103005180e918001c002c03000541c03070281c0c1c20801d1007030b00d070088030382c0d0590095120480072a0041d840301c0384250b02d194018901c0140d6801100503540e100c030200104803c49100e500102d01c84485004902010032880300300f21290340c9030210004460065081002c42858141e00011284100042c04d03c608140800e03401ca1540c801c0e2200075044d00c80b07899844a0340021285080e04211250040001c80c60960700c80703406c00c889800350740d005201061410b003806594002612000d440d41c1010f007092010141a50740844101d024508505150f64000d00c10f080768400a0003054540c0c01064203400c0691151041103038000d0301711354403202142080c00e1100300d4070038648508109540010070501800c181081c20138204064215a800c0100100c02500098022411442030800703c1161820400400303010b400f0042c020140206403108210940807 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 117742149 1250 117740899 117740911
    0xc0c0605100e0a150b0a110d090501020105011a0304020f010306050301021b0c04180602090f1f090b18090405010f0603051005090d0c020f031f060509100f150e06120a05 74
    0x841c040350603408002943d0013209580c08044442e60f1031401032021944411300b01c401100701d000f000c1080901641203500b1504031031003078000b88000daa8842007004402058000f0b0390152808100103801483c0000700c006480070141070020300399454401185c2240c01c1449900d4545e95000c0003c100b0920401c48400d00d00f50807a03003400390b190003e80e4000745c844034a4000780389580110790701c07405542d12110302c86c5284018003a040e01407080c04410403004102d848010204100b20340200754081e40d04111141c10003041f400840400010051040f0090002c105a60340d550b10103940381c0c02181c0313010b80c1004601600041099400e030b0030b43e02e811944041c0524007983d0112002c0d02215420a4041c00800d030100c1e070341c0c3c030303440510300c0820f003066240b80c807086c000c240034146659840300341d03070003081668400d54881901da80c038034242d040001c510b405a500084000340f41042500c0e030f001f081800b0302d000b07481c1103d0300810510104803d5008002d03041d1a0300c807a034003080b4203001144102c1794405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 117743399 1250 117742149 117742151
    0xa030306150f08041113050f09070b090d0302030904020f0403020907090303201507120e120f030c071e02010e041a06030a0e10060e0702060709090c0c0605100e0a 71
    0x1581c4080c02a040b80405a0050144168400058180700c2406010080c242018010780c14140403111010300903d0221b406114164014011890f0018000780c090709a90004c03001e05d20b04403150042142030524a41c00300c00318401000400b01680300c1d400946801100005810f46070741c2540704010022a0040503c01044a01b220810100f0350094801441185664140d9240d111448080d820705004242c0d6101e60880701d018401c03400d9200c4030781403c04c66040000c000307001c1c82c0c1c0310150301c2c0e8025100703911b00340d181031009407501d0312034500a6030403d80d4105d0591034003030b5517170b03492814006000b0142905429903002e14190b5810074450500a00d00321000c12500a240000024140703940b03441c1402041c002c00051184140c170760261030741d460034908490750040c5600210001d06040e00544144c0e06407600481c02d0a0300002d00305001e061240c03500321070300381040d40030070040010004041c200318406d080c580c086a8030b8420140510500e102408003070303082c201d801c0591360b405082400303d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 117744649 1250 117743399 117743429
    0x30c0f151407080a1215090506010c1110020106080607090f060e18040302030405060f1308010e1b0105090a0311010e1c0807080904181713030206070303060b03090a030306 75
    0x5461074078219040d4a40c801c00241d198000e43c2000c90721090b10b81d402081084c50080c1300d03140c0425008840d012602e400000b070041c3ea44070702c0111101e6410b00402040202c103240781000d540342c0700e001048422002c0c4000a003d030f0341c0b0f10f40307580f030240e0076a07080000c668041c0060003c0c4421040d000050480342c10400b2040d840100455800104298042e03041e001800206040506c240704a60040a00502c3c03192203070060761842400340e01c00416030307802c142c003030780000703401203040c0100d0002e0b0401c0303000341a5100c3c1c0300d030107402d8610214110b14100142041484c80c56503130011403801450045030020b0121458500140c05030246400007403140f0780756520321602c0d8503d60b0760300300b015503c0001c040e11660709203803400c4140542d0899980c09030500045c4584004849284800303d0300803540c0c10404042110000c04c40d204001c041141c0c6c841000c010b00c007604145004006180c4a441d0000303015595039814100c0e40c10035501e98009800c2441d81500b810740c9400ba150191110001c19000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 117745899 1250 117744649 117744677
    0x708030c1305010207140d03030b1e1f050715090605070905010810030c2d030b040510050c0d110c01090605011503060f0905091002161a070f0e0406030c0f15 69
    0xc4000c1d11b52510b4443d408199022040600ca50480020040003818240c00e040d4442062035908280c05042e41c0101e034035010006850400300c5102128031441d07100c0ea89803503140cbc0c90b41c2040301290700356180c140e81c03603080c41e0000901c01d101c2d540c0b1849140e603446d2880ca0030040010040302003c2c20790000d54070074850a10214a445078004103c9030701520000104078455031413040c12440c0b9103210041840242c2c00000d20408024041c411845172094580c080c0401c400c1c02c00301c032020f0304c111102c2c1d5424404005800c1c0b26501c084211840054514201082c80c1640e070f00b074802e082011103078640c4500040026000c100d074401000d0f0200d041c1441103d0501c9904071000e803591082e00b03500340c2c41d03501054158a083c401030092240c040d0080d5174810680e2a00703c241c4484040407907a004880c402803503a0b480201e0300e140039600a55032144103a000090407954008407a504c660b00680d42d80d0000005090181844018100d814065080a2030281c0c0307606034849500000050110304401007403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 117747149 1250 117745899 117745919
    0x6050915100302091903050109060e0703050c010c08090d1101031a0f090705040308040306050f01050103020f12060a050d030c0b0c16030c080708030c030a0608010618050c0708030c1305010207 84
    0xd041c20502d40140c454001000180c40030369504007840f20000c54450100501806410035405140245001c1c070003d9503800d41c0c0c1c0d980704004c2c032018015402030390b1b80c8503480d88214201480c5501a4030704500b02a0b1103800184ca050494804460200c0c00d140244259605801440c2c60403c11480c003010819881012401030321586071424801c1c400000011700c0140288142c802860300480caa603181c603124034011000740802d4424511180544d800000d0b250b2003030003121fa102451000380740c18034172104a5240d0103032000d0050381e40041c40000c08601500c0305030112240c2070207903541641d0182e06040c01d142c4500b0240c49641c60010800c4001807180c1c1100c2c45003055a414030b001e014070790040c100100c00780680c5000512002c030000c2071052000c0418040c601030201c2d083c041050b0360b0f46146090884215201301d106401c4c80744205030020081d070307203c4d50b0300c00c21803040c4d10700d41442541d07000c54a41c0200c0d07180030b10300000f141075000d1440f038508a0300034107000e0008010481c10f00607480 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 117748399 1250 117747149 117747169
    0x3061505092209051b030a032a061104060e061306080405030d0507030603050f0708060c180a0605041d0601021002090f0d111206060d1b0e0a06050915 66
    0xa4092100890b0004071242141000021001c0c8514100440d001601e8600d4039000410280e400c3c2500794007007100c00e80780114040040310780c141c40e1080d12031400c91001d06a89005104061031000e0310f074450700410918081d4280400d0714418250707942d0300b0030f04040c1218060640d9503010300c00921a40e8200c00b8081d448a040e1011403e111140e0b5803645072603440d500c22484004d60090902d030074411244c0d0180c0203002501d00c00c0e415580340c00780d981051541c6030030710301c240b5090313a01900114960107089001019462425111601c20103018404110301074001e50200d80010300008040000042c07824032034480712a04902e42c85581810ba00003561750016a10980c0c0c0a81e001408500d51303a184024412501409040b2403070092560605000c10702c034150807907000c2c2d0750304483c0c0d0301c040c3d6000c2160307446a440103054410b00d817440d455800c4004952000d0304030210b0042804030300c08503a01070f028400c0c81500008294541031809000d042a4003500f080304180e9030544080065490700140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 117749649 1250 117748399 117748417
    0x210d0c0e03152a030f0708070215060f0d050601080c01050f0a0302030618040b06011b030801140102010e06311a0c0d060806091b0604063c03061505 65
    0x801140d2200014104070f03060382d010324410340c0644500c440110300c10401540c4900d45250f4100d8142c0d071000c200384c0d02c2020840d64200183c01481ca4460100b140c086030a801c4000602508021724004010808604c0c80c250b003910030b58482401000800420040000108030a103000d50800404c6115440301c0e0058640480030b0540200c005003468803104c41c82541c6413800c04481c3d1f840c1c02c040c1442c0e080c500c0300343d41583c00a90300305404c0103626020042c0c909456856560044c041c1e103000a803801c0b018240326018110754884000c0c207443d04082000e04d002d05a810b6100740a8a46625100b4801840c0c1c00200820440219003002180c2e401d070080c44c03032640145421070743d41d4a02483c100c0b580b24040110030f210b880d040c004501c6410010b000703440307021404200c3d04c0c2c085c1c001d031a06038090241300d61550300004c2000f00b13200c00d030310601042d1840081c0035001c20408060703140d003240030748034603603411030760510300740000455949030103950001c01054800165038629044024a903128901d48 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 117750899 1250 117749649 117749683
    0x2060d050a0921021513020114121006020606031b0105031803030108070609050406030b01120609020301090807030305101401050f040e010603091203020c06060f03210d0c0e03 77
    0x6003405001c0d0042c2e040950300411414071610102100002040342428801c0148110051110b540740003090343d034000c0c40601518404d508180c0d004464000003100a40d099480a11010340e0f0021025a128025034122000c032580500388140207290850050010744264001c1c9016090241c1d400b40c1096074040c02e1030004e13940c0c4d441c03150f5125021400c403000c01c00c9100000002a481c0d4010640c1c00544600386c4d90280d800b80c1d15800c00050b10403e01025207048140750041101382d1a03d0341a100c41e030b104004c00b15031340c1482c0c1c000070f003190080d0106450400c000182c0c0070415501d40300c0c095000c0b80b00c100030725200c0d00300380490500d040140081c0b8140040080d522404c40e2090f02505e0085c40710804400c0d603503071a003800402a003045c4004507115140160a040c0e079502034025141060138140080c0a030307946540401113580580100c0507098087c50085400742d44030b40030002640d0440d400000e54031841c02011904a801424905080264014090580740c3e00458140000016165 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 117752149 1250 117750899 117750901
    0xc09040504030e150a020729031905040c09050604021e090d051002070c0f0b03190609020a02011d0c0d0b0a0212010603060501180b03271009020f060702060d05 70
    0xe0b0035103004498110743c07a8820016008100c092480d0301c001c10209050741d090741d05083c2c0d070340760005910401c10300c1200104060307180076001940d8032000d9513102c1c5c1581c40441000000012841c100c400940c2c0a407a403280890302803041086034014143c0182e420b071703011850030906039009041019010003960b0b00c00000191004140e480c10030340140c240e0824150798000001190303d0000b903100040031a8a103070340840004440342c4000700101150b09102c01c00346143e440011110304825524086050596240c00c0400c215101d031010304050026600009415210700b450800c4120780a000c02180d030b0b1080c0340c01049600d450107a40322203030f8040d4104030b0700e846100d00007002e409541107030310003010007200002d419030340354006004444007a01c0f1403044000420709520801d0302401007c401c5602040400c0509458402c171043d038500307450000019040707031040c503400e01561003000c1d00d0443d00c5116005c198503006038400c003000383c2194140d1402c82140d000c100e4501400340c026015aa440b8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 117753399 1250 117752149 117752153
    0x8032a0a02010e191a07021203130b0a060602030405011d030604050a0b010b03060a06050703030f0c030608100605101107030b07050304051c022112040c05030d0201050c09040504 78
    0x10042080041410006466000040c0001e0007421207400651140c07055901154820400b140c2c00302e04560013010310000310758109820404075001038840000c600c1144c080503843c0c4d0400f0051801440080d88803510f070700b0942024029a803020b0709141c0b0980c0350034020400650008100c500b00d078400e092451020400110110058011842417600350080e50300b00400c00c0f00200340c840c1124450000e0180301d0342c82c0c45030405036000449895070000c4201d501402410301600c09096568801d15000c92039118107070141041d502888206408a03444007030a0081e55424001615004e414070410000145401e001503842212461100203010441b030246100210134040040550380210044c100c50030b00041c010801d41c4100d81c05d42d500d00075407004881c44a41d40c007000d042c0c0d0321a6801480b404100c0251032004401c6800c00034004107081013002d07110b070003150b01b8510039070017107802c2c2000c0c1d4505820f06040c4800c546498045903d06010090202d6115081d54061941514002020b90b81c80c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 117754649 1250 117753399 117753451
    0xc0c082a03011e110705030a02061801180311010f06060908010e190303050c0d05010e1e0601090603020c1513030801050925050906160606060c0f0605220501020304030215040803 78
    0xc002c041c6c007901000644003046500050498010341016243c1d0400c200603d0b041c81c00c841c1e00c014409414149158040040383c810303400c5000d0351034024000100380f102803006904644c0c6a60154002c601081401c100004080c41032001e03443e000c0001e0000e850020100d41050304010700001d050695580202e03040156190030746031a884c61540070440c82d43c47d0410b5099012007190f80040e00004611a501443c06a40c40c030f600482e0182c540725101420041c0170f40c041c1d0440222200148034903403000b003118549800741809101c14002c0c0b00d0b03a003090360800500e03146050300401c2c0202280018003124504a200a41c6840101c08280ba00d0042403201265940301b090820703a800200454000749071030307018408041c082d1044904000840e03951900b52194078028034040d1280c0e1900041e00701060560704480c0c0c0c00741c600406401c1070544051030b00d280384030084090300c8aa41c00300411040603010000040c500c103064050105a103040d80d01c0300c880d884010903000113041c0d042c01070304c008800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 117755899 1250 117754649 117754657
    0x150b070b01050d1a0103080301051e03031b240a0609021903020904110d0b040b1212070606050a06112107030e030a0816020f0d02030d0c0c082a03011e11 67
    0x3804d01048081e5940b420200c131207410030301595124551511302042224102c07901d4403003040020b00030703506240600a4129580741a505c034028140203e02c428107100052150043e81c840c0300b0314403a001d50030708021882c1110f443d90000c12095104110204ea19411180d41c42c447e520070b481e000d40c1d0340c81d0100202d03001c0c0070807288181e04107070082050303100c0d920b0503004409001c1c000e5504100b01e030700b408200406081070740c1c101c020a401c080040021010003000800b2814010000031450300c0c0d60701c01144440c06c05074400030005500c108401c850680034803510041d000000140d0100032003075900c22401e88680f40c0010280310805445600c01c1d03e083c0102c081d00c9400110042d10707104081c1c07c21300d600c0d1484108070301c0f5140f0f040e401c032828640300900407081c540140c02090500c0c00c7c40003d4609469030b12068815068445d40001c040e00c0812200c1004580b001040310001110150310344e000c01010f030514071a904040b01130715034180102086011036034151011510000d8000070020506c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 117757149 1250 117755899 117755933
    0x30f140702070339080c04060b040501030908070f0f0302070f080c061c0614012a080319050903120f190209010309053c0a150b060a03150b070b01050d 66
    0xe007407120f01389461500c070307a40085440c01015a25956264020001101c0150040c4245100180424052940310394000d001d40c83c801e02c01149803001c80e072a034508030800c000e021902c12152603580001c255061024034020a10810500a20b03410114140c0e10380030f8604a4070301a050200d07040c0131803100034283c0f503102d444c0800c04101d400e031074000c140800b41058030b80e40d0204417044040400f03c40402c0001c62400401c600421501d201a41c030340c01c0dc1d90002d06000125a8861880e016003500c510400d80034614140045690b00144c0720009a6030400034400e58610310003008205101e2180071250076125131403840143c2e101d00f0100103030014001110301805030b02c00c921000b800242d48209440349000341c0e0260710b40101411804920f20030b8007400c0d000181e04031044400010302c1400d00102c904a030070300041649440032002c28400e40100d0820400a519040a000b107401454400d202904240c1c6c0203c2c60011651035040320064180300300340c021500740300c0ca0014000c0202003040140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 117758399 1250 117757149 117757223
    0x10302280504051909150507021204090e030c030a0c0611070209060d24020409050105060f0409020f09090901050a05070e01021506130204080304061b0308070509010c12030f1407020703 81
    0x11035608040000e00325141314210420720301000714403009d0000621402484d074150407145041c0c24141650058600031080c070140348024003c4210402050010301200881b0b5666022800407508101090380c0210071020205281000a0b002507100c0d02d4905038400415500044001001e15010441c0403001002e0100100c01d5540d90100c0500c6030001c100300c0f5403407c0c090140f6602d8600300042e03440740c50603004804100300810000a4020b03005407003a11001c0c811241002601c8002c100f1807070b0120340c49076050755150301b040f403000c001e41702d129000022881c02840c0e04402100103035982c0d40100f18001644118400607045a0300e0181711402018200000c4d0f48442d580d846075540c98105000d900301050045504401c06002d03d90303849a00f9415558172031b195100d503103095995602c00d5000b1410051100740c03440c0496401d03120480c102500e0b60300054410403547d80d1348115055104a171003402d11807002d1040c1c4560000f2003000b66508100d12144800700c03001159045480150b41405032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 117759649 1250 117758399 117758411
    0x130b070c0501050f0105010503160306090603060209011707210b180f07080705030a0e100603051006050d260c070806040309090c090e1803030408030103022805040519 73
    0x169122440444940c0704500030301c041d072a10300041d40012400d0103030030700240d014070004e0b000c0c440301205500042c0036424005072503030700e8000810656aa54106a0720b840d00098018140d50307100244003007035510606d600480b03042c09440201541c00400704c107072951414001c010030340002580110440e0800030400c021201240c0141d02c20b00c3c500f114038080d920400000594180c0c01065018450302c01d170f90780d85240da40c0301d40c130040080c60715200e10361a5100c0c04003500709660b590f1088a01540c05513000f0700fa800018482d090503241260006d500030405400c0348000a45486905c102c180c0b0411203c180c44c42248100380c40a01410781c5150251042c0b090000300c464010408ca030007140a80e594140c1e140c2c03514043c40548000c0e014500000e009540c08000030355074070300c0c03150b0880d4100da004003200d00c0c1c0c0e070007803442c0d034005440075078032480008010000c602d80318006c4082c89484101540168000000c41410034520348141070103580c48030001441c03c1701c82007070040758400c12081040300b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 117760899 1250 117759649 117759661
    0x3050c030c010f050a14010b030c03070915020105190b0607020609181003050606040e0d030c051909180902030312040201140408030d050c040f03020f040906051f0902030106080f130b 80
    0x28050688a1380310184c5003040c10014480806d816505841d1040001c03455502d601c600e41a15900081998040141130030001c502c640c00024103a500c00107503400072586041085a02c140c10400c4140707000c5da10300c0d1003001440303500ca07981a1a0003a404580442d20342982c0d0020a94070301030181150441c9040c00d04028102200c04140816207010381304a40c0c00303030b5940b001e100455142400b01130b099400344c0320b1200c4041c8680c10031101480320f85012403d0403620180e00200302e00e080010004158003010900c07032624210820590000601070502599255802007900d81c421408060f40d1030b200100000e0659010312051038111400300c040541d04c43e035a05403580c80750080c07904070031412f042074041525110440c050300d059407107000501007614030355406c0080e0a50070502c0b654100d0703100c2c0e8400022074400d1050520a040488002c1c20131405014041c80011058003c807201510600c014003055034000c501e60746c400b105508000c419201c860803280464a10400104011000c000b0030030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 117762149 1250 117760899 117760901
    0xe01200109051c020102130b1b060a0605010e0f0a0b0c1204091406012d020a080d06080f0a080f03071106010915080f0a080f22061707080403050c030c010f 68
    0x10034080741c1a100100c0401c03d40d402c034241c1c894242c0440c012260640c0c103110802e01e0344004c040640306080b98031582c4450707281142c10410110740c540a00b550b940030801c001c0d40c02c8854070201030320445664509030240c0c0300181500c14039025041281c00c0214596822171001c00112303680000e09445240c031655170b940c0d41800f0b4400c10003c0c0641c60b0440002c00c0c404d5009500542c0c0c0c0450b0020f03070800908144c000950454640580b6808503ca0444401c02217012a0014000e9880e40b04010404c1c608015095140180c00e44141c803484e40001154000b15504e4416601d1990b41402d407541c0e20b40320b000301110801c00001841d882d9020701d00000030a4096548103000d00c52125004800c2241d450302400e441d540b40d00c2202d005500314009017000140d407040100640800d20100d28101131b03207040424003519100305030900003480840c1c2400560b42002da0449020b00002070721a50f403400ca00e0050030250043c00040600c680410131010603601070003510341081d50403000704203d01003160510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 117763399 1250 117762149 117762163
    0x1b1501060306080a0201020705011b02040509030c07060f05070b0c0403021f1d0105031f1205061b0711010c080c150114030c0102030403080f040302130c08160e0120010905 75
    0x100407074039201c4002041070f00803e000b203542c1d03016000f40030414a0324005541d100498000e14600c40b51403001140141e4070752044c24000c0415100442d107076603054559601d051050f402103403c0c40710030b000480fa495846030403504a039a201c50811007684440403604454045c0c2d0700300035800541004110780d20703002114041c4031901e00385c1e208140c0d40d680d030010b1400b041104000301c0c0002c00410000d6a42c1410051803415a0b00b1018041200c0d82e075527642070181c00c00c106044549800c10f8090220f0304466901903500000801811307450150150358030003580240300401418000780c90400010b01c100c50050360480b03e103450680d0030001103040c001a40c0c40e0240076050302401c0501c0801d2a904001800020824041e0001d42c81c06040d901c0340c06141d0003200558142800070400407005803100c01c0070300c03d044c400368000328100e104200007400c0c0013401440606d4041802c0000c0300190790045584140580a0a00b104080380c00180507502c2c8500e10b20800c06903086c144030204000c0006400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 117764649 1250 117763399 117763409
    0x150e0a08120405070b130905060a09020c0a0c0605120109092102070305160308091203090a03060c110115050f0301060306090b07020f01060602030a0f05090405010e0114090402060f1b1501 82
    0x62049517132141180d000600901c0041000c0c1c008a4200340a0301c00c9030b910050300980000c00d40c174541c41d0b94442e1401a80e0140031181910740050040c2020041c125101401412045c201141032407410310200310392078014483c00d89043e848100f4036060001082841e0001c41c0d08800d0505883c0c0d83c1100a540c9104034401221148942c1110350701e42080c0e00001d00560342c2c0030940c0b601c0c00c075800d810840d845040c941050028001003100005641d5100c031520011480380350049007a0480d8003010f81f0826100e01d000304141d05201460082c15560b00c00c180940d40b00321400001080d01001003070040142d03800c01824a854490020180403191110301d10842d8158200c130115454000d29600381d840ba0710034000945c5c0140320b507140290181d076004085045030318045007002c001c000000c003501c80070b80c0200d03803840070800184083c640c1d6841e540d83d90101510b64018a00742503011451500c581e1000b810750380004250540514407042d0100219154a1f0486069449000303e40200c28001e1080c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 117765899 1250 117764649 117764653
    0x70c150f02120a030b0111010c030510080f0a0210090902030a202104060e06100510030908180a050a0303030c030f050402030c1e0301090f0507060903150e0a08120405 73
    0x11991200c0c4001541e042d200e4442000070705141d100c000981c050610515080d05100b11102403500040b005d11444010141d00d0350041146e041141003002c1003501500000c2d07241d08511140c0c068900009941e00380706170f050301d80f101d112080b2001103840202c2900440982c1b400002486490004c0350052290380300310340c900072032810140030b4410561003401502c2191903800100d241415a902403550f80c4280501400b066601e4a04006401d122080310b5995008240140a00a50a000301d443c10511141d082c1000358800e55242c4000c14040c07032911107508198062503005c4c035100c59080b00000c1002600da9003180362640340180203400c00c1c940702c40000e440c008118034800c0050144500070707500500904401d480d59002d00050403501500c49002c0d0400140180b45c984007445030f500200e004071503114007034105250941c03c00505901c04010005808024404140c0340843c1c0100c40209041c00108030a426401720709040359900080d00340240454041103e071411a0014861880f03142 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 117767149 1250 117765899 117765917
    0xc19051c090b010605130902030402030c0d05010e06010602010213050d05070305011803080604020307050f131509030201090e07200c03030304030c05010c090e070c020f0607060204030c06050712050a05070c15 91
    0x30105c070140500d0048101e0001c40300070401403050298001d603049030020b4143c030f4000131008003207141030001c14000c6407503a42d245a8600c503403e0070712405025024501c000c0d0720b010b201003604034038070045006c0c040c8a0b440b10764100c0200034040040c1c2c03004541c80710003800300a40c07440101441d44044c0c44141c0c041041c840020b61f41c0d117441d2086a208114070b44495040901c0d81c1d4000403d60010b005980c1100051200851a4104ca8006800712907840d42d40c1211b040c11840010002007142e4445400c0079150414080890307003201400203002901c2002c030580d41303144003266180201c1342d10803d41500000051006159000b141560014002c1d402407003450b1020310102d9100c03a80d88903480d41e4000d2540401c60141c440c29004c051030740002c002c01060ba0030400002c0c8140d0008500326521303940041c08104202c0000c890780c0040020f4141142003040c55241d54409809070702007102040000a401d400c952b009106640000760003030b40003410240c50b400842c45966a0788808408601b07141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 117768399 1250 117767149 117767159
    0x30c06100e0c0307110703050607030f02090a03110303270406060f080109021b0712211209170a091a040b1803240601080105090c19051c090b01 63
    0x10100e030003100d1491020004940d10700003002e06580000d032003c800c10074001c4040700c402d0010403949010f18044c1c40074103007904003a8809003c403500c80c200c0240c2071b030060150b00040d075a198940341c210781d0460110f882e42d02031800028298401d1924605450044040301c02511040c51012016800256000c001d100d80f00c6000b41c90300e0302d00d15001030000d01e01200512960070203402401410b0008a04684486010f41d00981404140d802265a0003100c0180d05c0a005802010028036404200070b80c040070800d460042c50b1140c03801e80c0b001a19203620040040040000e941658000482e14654030b6061040c8001c020080c075204020f9000d2200794080c44510b1444100c604941002010710300d4250490b883c0706006117a080c00d03941c1400307581c6015a1403904039070031000c0340551806265542c13a1120003d0074200c1c040c1c011134001c0c0310340c83c10400da1028100072100d0484080c0703500b800070311300c2d03600458003403050001c81040c500201d444882a003900c2d4000b00b15280c490700300705240d83e89503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 117769649 1250 117768399 117768421
    0x1e0105040e0d0e1306330503070c150903120f18061104050301020301030c030506100e13320f0627010b0a2309060f1917030c06 56
    0x151801e6225008660014069406098505007000c0003a1262801c1c4141d81011000c5462541c0465005051881c4942c00030a03030b014100d00700c1c00c10b070f12007502580a4100040c00f83c00010200020320403400250414000c51100c1c1e0003c03545c030154140090745107440c00900c900c0340090100b00c41da08048140229002c6401103800340d017045940b18001c0c1209031281006400780160002039030360200408503080e102800210f0182d8040c1d4405040380345503281161400c00001d00c0001404158081480030100d00c2040c69040301c960301c080c100d00b00c001c2c104100a181204a42c0c1c2c2c06040c0c80c000e480800c0c0c03000349034890041591003904d00450005401039211a400c8036013460106050b400810801302c6814842c1c006076003e000001c031600b050700890054851a04181c0700d580d00708850441c2d45005c1c2d0744410010b103042c0c0752056a8100400400c40d0108c90009079441940503080281d0440c480080700c000408143d9142e004040a410609840e44e10141d07860300b41c1d008080000e1860054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 117770899 1250 117769649 117769661
    0x308091e010f0c030c05010c03050603071202060702040e030d0e010b120708060402061b01060803091309030806040c030207060504080403110108040506010b030709031209060906170a0203060411031e010504 90
    0x40c0c403818142c56440004035604200c0b00401c9003800f51340c4011001148007446140c240070181d840008550811000b01440c1c504107510031211103500314107000058940310107840c1903960503940840c10300e402c03100150a5005c0c1c4000c03914114500316200308a04415080b08902c00800d885a080e101410000d46440350098000e03140250700c900d0114006047c400020304811103034142e01052101c2c0308030240e0940d0180c0c1d01c071041310f03400810102040c0c50030650720f2807180140e2204001421a40d0781c050300c20400106010b1040340da41c0b900e80c3c8460300940403940000c2d4401010000303407a040c984044d25822a00060390a03400c140c05102465004984940c003c0d40c1110080076140e19101c0090010361005010034100054610004009802c40c8901c0c0500c00305511640031060500b00010b001150983c0302000f041610780b0b80d004014544e4050b1340d0004000a800360741c9684080c0490301a012208541e0681e51000040007404035444464510300650b0600544d0aa41d0780c00800064803d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 117772149 1250 117770899 117770959
    0x711070302030c090702010204150809010c1b200307030803100503190b04050c06070305030403140a050906071a0c04060201050903090907081b0307030e07081902090709080304030809 80
    0x202002c03900200345807140c135040d40060184000352829031505500c0f02221152410180440d5041c02171217040702083c080d070340e0300c1c1007940380140c8410106904962051b0410300b028100b159070b410200c1c0d00000408c0784000c0300502408031040d0640c0d03498980c50719130040382c1d002900514444041084c0c0750204259814016049001102c503006440300d20f0201c0d00a08200c806101719804e112158644a000d000000e0003515826141e03d400e04014007414074259190602c81300c04c020407079981d80c0207030540b0b00100054800390f49401e45071602200d001c002c104100214032040c810004501c9030b01c4000c3c0265900b5600038011502c414044a0317590180e141c0041e4800b1504000400191250b600164450a180034105074920200081205a80250b84240001703494036090041183c082004500420a5200900340c4890b007000310000ba01070004001e2040c000440070030354041c8154800701c003402d44074065950ba11355a10b4446032aa10804400340590003001c41d200d05002c2020340803140c54 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 117773399 1250 117772149 117772153
    0x40218100b0c25060e01050c01020403021305060f041b111002161a0c04210b10080c01050903071502030708040801060306110c07181103160206010b07080f090406120b071107030203 79
    0x17400703900055405802c0040d41410a40d424800000580d07201410302e01d41e2491142d00003150b0501b042848840c0311066815030080b4106901c540b603146a641e81f01c1d151440038030b414000307180340d20100d03400e110741011050355003800802c565030182c0c540c00198010a00c5192002e1411800c0019404040002c41d0b01c20404101030208001c480c952988003d6030511810380b03405400004c1e0741c0c000366044165082440447d403803509210490082094000c0901d0908203d4204410640002c0d503401c220b00540358981c0d003840501c144107000700251580c65038056000c548894a921a40e40240018070040d641e15041c1440d0a01c9802e030901228070b0b520782c0c40c002d049840d090064508060344d5040c1d01046141d910442e5035142140e54000e1070281400c0c01d011100b00b041e604000f0314001c410313084079413211710802c0100700140700c0305c1c01c0313580421103000c00648618100c00010300411076980120031450000305d0810030407840d01001c41c8110000c0c0c56148070161903403011036603000e503400025019 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 117774649 1250 117773399 117773417
    0x803060a060936020a0e090702011109040e010e0601080f01060608060303070605040503090a030b0f0f0c030f041a0103080d05090c06070602070c090c020a1406040218100b0c2506 78
    0x464981141c0e0f95214518040100c500041c8000c1035003280d2010912000007602c02455400074604402066044240c0e84001c1c442125403d400c00514810301b42d0041c40340c1e40c4c032040411000000e4015014100070070094413001d6a40712600364461005184142d0300b546003200c045440e83c000d03081e45009a01c086d005500381080b59070742d076009203009001980d0500c000e01c844546542d5606502c40510320455000c4d1103401c060b00d001006c0d0401030442c0102098450400500e0207281c2c0a50380c0c80030b60700c1a260b10a803a03900740141407031041381555541c024014004414000220b00401401001510800507a07541058154075100101540c59204404205034804205560040d200300f1b07025000d09074420307030313200703041030854140c60080f10240c5c0225144500384940340185e8061140c9000203010289441c1e40014482c24420940b201ea103182e000101d4a0140c03400d450401134400c82103020364422840e04d0302035403003180407051410300c80d08129404144008400800845410780c44007420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 117775899 1250 117774649 117774689
    0x10216090515040501060c051b060f1b010903050901020f06010303020616050d0c09050a0e0609010306090609020a06020f070909110105030403051c0207060f020c0717010b04090803060a0609 83
    0x14100180003035150350b030b4004100342103996501c19180208203540780d44c0c09a030024035110b402c040c50321200c17010360400c440b0a12040d8507050210380714150b450311103c1d5105814003207620010860114504598a0070065a04141c1c01c04010507142009800320b61081c035282049543d142c001340401401600184041602020709498800d440300c03881c20300504003101c0c0d9802c01d040310300031a8900300040f041c410801c100d091000030300004d4580b00007202e84615044020510a420620001304503664a000d2401401540d50100040ca60b0083c40f20154680d541d04c000c3d550121407240740110702400710002010142445034600755640b021805404101c01001512240c00043c415810310908010890796014104003115007030421010060f10f03030030b90b400c040044a0903e03089003101f9104001445640f4400642c11040b5907007164204003403070448043c01c0c050b100c4840780b05d0b040b50800c61140100401c80b000f452103010151a02041d05a48040c125103815030307446601c1c1e0381e40c3c08030003940d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 117777149 1250 117775899 117775901
    0x6050105150a1718031303120f0507111c05060a060b0a020a02240d0f1d100b0a1505030109050601090e010605160803090c0102070f0b0f030a090f030f02010b01021609 73
    0x16000142d00581c00c4d0600c5420728103421940031031154481c5940c1c15030144100f01c00d400c5491030503921454035141d00e03981128041d065103d8900c01820950314800c208126507500c49100c00c018110300001a0008060319203c6c0e5100ea09540c0b91070340c00e04020002c181003240c1000c0c0c40d4595510780c000c0041203200d4090000390841e00440300741d090403147c98040010f4500004005103500c0500c00180002c10050010494842d00030003c04c29030b0218514800480010b1407080c01c150301500050321140f50f1000807440d279500d0b8000102030080c6c0107000301040d00308001d18100d4444007410300c000d9480c0c00045810003507074002c0001848070200180b00316441103000d06820041003e00b546a4203040d03e9510311501b040381c02005643c40840303030302420b50341400503000410121100a1303509003000c09400b4240079080f0801200e150110008000c0161600604c040e0354000a49001ea00c0280c203005200381d4406110b180907600300541040d540d40f0000e0076107660072001e20300c90f010a0400340210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 117778399 1250 117777149 117777151
    0xc02150906071b0905040c0303020d0905090a050601030f0608070e061c0b0a0b0303030f01050f010305010e06040c0302070209150a0e0f0606030a09060e031c05090703080f04090906050105150a17 85
    0xa100c1816403100400d210b4214030456020394040d21015851238514a00245404045081c01c0d0801240c103c0420250b1148001542c01544000c0041170696072600101c004000d00c0f80d49a201505000000644080c041030840940b8586044803200d50384100a1100f400210441e0420300040465a44e02040c00070300d4494000e0481200807907044201c400092031900f040c1c3d40c2980400f48100100801e24000d48541cad50f0030000c3c01c00b805650715091402d128060000c101ca4011a220b0030102c034042e20030f50450760881e90003041c02d81c0f5402c2c0590281102140030359100d000e0109020049500b0681d02000d62107260a0442000c1c207988000501005401c0504104085911340400600064a9001e81d1191084c00c6004544807515640407600c034915800c400d00ca01c52501040c0040f00601003042c1c001e40e900f0a20b4613680301ca41001c40400b610840e0b10500a0914220503c402c020b83c6402c42e030f04aa80444502c0000301000c901d01c4c4451242c2000d09001c40c0c2404044125242d441c4141 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 117779649 1250 117778399 117778433
    0x5090307030503070207181a030105040f030e1804080a0807050c0c010e0a080105161b0b0621070f08010f110d0b0f0307080c0a0807030f0602070503040f03030c0215090607 75
    0x20f100308958031240c0d180c847d90b80030203010260303072601030748a81e1481c5902203041c445130440080c0310b9400c044d151081c101c1851030001e410042183c61a01c8181c82d0481450001402c450640c07190380307014100785c52190429008000010341030f00c00304550034401c50944410034100c0c0007070442903481c031b00156800e20f0901c5909410600490000811100038403c60b44181200040705410611014004001048101c80e11001c81500d030010702c042000050fa541e0f010405030f903901c2c021000340001e4250345500c4800980305115041740031842c00d410840c03800c21100c00c40002e010008102d41013400703450012038603008190061018100c16090381e0041e489108014100554011003000031a0510348260403003180380c0d109020382c1190b41884a04440101980c41c00f40c60b0440c11aa107103820480411070141941d030300895040180b2a0520482e0024403030807036060040d65603464050001c1e142c0c0c40003a4030401840c001d0440c20310080c4101c507161807004061618100c81540c81d62000d401c84911 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 117780899 1250 117779649 117779653
    0x110102060903040b2b0f0b0a0b09060d0e060403020a030207090c08060405130b0a02041406040b04050d05100c08190606050409091e030302040e090102120604022503120f050903070305030702 83
    0x1e00c0c0b041c10082c60300d14170f0032040150100d0485207452a51050311125445507000d00c400383c0c02040341e001c410041e166440400c440041e9680b416220000151072800d821210740d001d190140810580c000403c0102c8621035021745803065a00d0380400115032155101d480400d02410000d0b02c02d160640c8000da00c85240720280c24020800e84600c080e16404030344000300c403580006c0c1400fa903d201240880b0b0f480c411140246000e0804280340c1d0f87d800b541c81610300440c07044c901074003084000d102040500151040030130282c00c0710300005001000580e504101040e241e50440300c00c1d003c5010381e03001d03a50242c131020700d42440c0030007040080842d9038080e283d18410f109200944c0090820080d8904e019a030050b86580c00c00c858a400c6550140050b0304981c8100000700011110080140e030100c0200c0e80161101e070711350480c0300d070308540c140c165038145114841f03d4100745e00600144203003001640108110030f1000409000c550b42980c1480c0d85034020700c14200060310500c010b55003c581d600c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 117782149 1250 117780899 117780937
    0x1803040923040605060415050607080708070b09060f06030f1c02010e01020301090e0c0d0b130809063108070314010e0307050124050609090601020c1309110102060903040b 75
    0x6a141440401030350b040755195142c4040c03040303614090048254480c68100070410451612002801501c030340500100101e034082480010f20404200707903044141c000c1c0008810b0b01d4020010351301c4000482e071001448521030003091044c01d00181148007800039030028084034a070b801c00c1030014407800910604564a035040d544c07103e08280090350081c00e4801003c20a071190b0503026050a00f40c0c15154003488603c1c2d510004510103000341a00305020051800d101030b07132401c0800b481c0c0300c1c0e5040584c11144c0010100c46002c003031040b2400045004007086455150455428991110741c0326451a690261100b072022640980c40000c54202c110000501c003109486440d045400c200400d6500e0303503407000c124800c0d5400421480500c6110500d03010074905100000d00d03640541c0e01254001d4190400048041e4001c00c1040407458000303202c03003410b085485d0a4009004140c1e0304440c03c18040c0c0b4420115400007a034680100d94540146040500f407003403510b080c5d0803503001300d4a0290024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 117783399 1250 117782149 117782201
    0x101202090a060207081203070f080a021b0a03080a020a020a0303050604090c0b0a030501061e031a040527030a0e06070303090b010902070b0603070303050906090d060e0106060818030409 81
    0x11004000c24083d0041c0c24004d1400d01400d04080c0d0740c400c0e84088030403c004010311940d01c042400b41c1046941440792036900d60b804400000c1c011118035000074076908107115258213000600c0402d03e4030a5580c1c2c030702581c032100e6003410781c0212084c840240e8484c451120000c4d0280c0c100c0b691040010b8000140c40a41da00c9903600311105500006441e00e0020340b01d1640c80d410300449000d80441c0c205500301c0380408018071868201c003440d00f030415549440310000180401e8a019403400014400c1c0300d241000104000b001c1c08841125030b1415502c030403022800e00200507120020f81c070b6121004001140401c0c4030044c1d006030411020155103105410015900b40c8402d80079100b00440107842e0701d198a85541804030203007046100c2d0344611001c00c0002c0c0d10108031307a13101c001590060f480b0135600c00420391103050901e0040580d404d11511100c028415404901100d14a0361a51b013075442d143e0401040345044021039070660010082070020101a4004034851810940c4105000c0700391 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 117784649 1250 117783399 117783409
    0x40f0203040803070f050412080304020d15020c1905060a020c150403020307030908010525090504020c0c010f0516061a030607030903110304050d140a050a05030c1b10120209 76
    0x101e400b00c4038510040280154154014407100821401d81412807a041c10704a907059005100300006000c23820020018045445480307182c0300f01303503211a400c20b4051030082194080d420441d281145403140d42001445a51142415071855402001038a41070b1541000a8083d5118100c0102144501e08921500103a00405230b88070b00c0c0264055a02c5035001e05d002024ae2940d40e22590840c1c0c1040284155408541940b007011000c00d80c444210301c10240d0180e0342c054140c2c1c001ca031301c10300c00b1a0f940600c403c0130134400780c5606e00b60b8950041c402030035800d03955030280c10000e11110059101c0440002c1345948212a00440607880c64011411140060300d002800c840c11030000303845920300300425801c1b403106209101804003071030410b42006e0220742c0700180d0500141401303e20b03200d0300803122810b000203031a0301d4000d0155034140d2120300b4103942d01d900150310750245110f6a6140c200768080c5417100c050002008200301d0000d8626401282d1011a02d28000b011950800903803049a4039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 117785899 1250 117784649 117784651
    0x1e0d0b0a09060302090a02030405031801120c020303010e0f0129040f03030c06061a0715090f0c080c040605060d050709090216060b04020901050304030c030905030106030b250e0d02040f0203 83
    0x107203070010502c0740c21403041c407040c401c0c0580440c000c140180305000000d10040150342900b290780401162100c07200c40100c4c0c030713849902031100105151014007165158040b0086050700d0300c51182102c9030325281a4032003e03070803d01c11482c02080d2440c80d407030340410000600c1c0d0089402b4400c0390070a9110440c80c1d00c2e603581c9034000c4000ca22003c100f00b0400401f40280c07001041a180f5100c012445134503001c0442c842c6400041680398000d66440e1125029802000c1481c4c012801078000040303440e10401660460148540d00c1c421700b91008443d01d080d000c0c0b8825204042c03c018107011041c0c1c450780180401820000c1031052903070300030030880704074809030000092008030940610040d00b021001c445c0701c03004541c015030040040d2040740c0d0300801103a402c1545850462040e2216040031584141ca6800080d855400c0000007c18442d01c0c1100a0141030b10b6072a44060082160080300740d40e4010081001050400b9005040391420010f074000160019001181101038141160100d0340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 117787149 1250 117785899 117785909
    0xb0f0a091a0414010615031e091a0115020d0309081204061a010203120103080a020f060a060515070203070306021b0a1202060601050313020d1a040308060f04021e0d0b0a 74
    0xe2001c100700612112458690116000e90f008100d09420040c0c001d2001c008500b01e5020306031203004418506540b600000501c2e051404200000b5101e450520000700c0600ca803010750541c0600003240603001820364000e85007068008040c1c0c05252101a00030f8034860b2002d480007042402548510322200c040340d4403851140c40b00099003e40d40b04010401d00800101c68110741c003d200c041c03041c0840d0310185040d40d070090f008645903071204400700c5c40d00090300c000703032818069182802826910780c1c000d041a6601159440600a0240f0021340035004400700a54144d220240130000301d0181d40c014002c00111150401482003024002ca00d13180d000301d41118508419030f05d40302101c0e4148503858210109283c41480c41c200340c0800079900d5a80d0501074802c480015900040140c0d601a007540e000a81c801e0100345e141c14100601040411900709019102d491a003103000d1800c0d00c215080545030f1010340e0042c1200c54105100c0d0340041c2c401240280d80c5140c0c100032607854608101c000e01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 117788399 1250 117787149 117787193
    0x6051f0c0f060c0207050307060306060203030408090d17030609011203021005061504060203040807080601031502160204060e06040605040209100c0c0801020708031005040b10050901090b1b0f0a0b0f0a09 89
    0x500c2d003010f041c48c004d0980d02c08820146081c00c28080d541c1e002c8110ba80154002ca1801d4803000d1680c0001c0e034040e1004c1005000900240e0407a090f076001101941c0325050807a00d44074260790f03503051044e00036a4446c0040c01038110700c0b8083c00b5a01981d1040790403079000340c960001e03440f80d608a903c0d40e81c400d40111001d80e2010800308800c0350208841c0f405032041c80042c10441d40b4680d07038842405040072070003c40c5500410788245040c840d24000e0b60658001f00140480b40d40c0305e0075601e00d45001c0d1040b50140d41000d1011440307003041c0c02110040000900740b41e1018100c00d03411100807909840072199608a0200015000000d0001d054a1402880d62964908001c041c25880d460a940410302950a2070042e00d02c55498201c00c21801c01203042c42e41c3d554000a00494403602e80383c01001c00500c0205000c4000c80600c804569101400c600301e400f680900c401c1580d40d10300c1e01c1e0004001120104c005140d04030700d0136005400200d014401704030400142d4a05000e4042101e81044075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 117789649 1250 117788399 117788413
    0xf0109050106080d0507030f0201020f0a050904050f0f060d030c020d0302032a0a14011506030e0c0d020604140102030c030a020114010e040c050108060f060f0301050406051f0c0f060c02 81
    0x8031500780b1514004000210040c403488502000107080750040c02009418440221403032520a4001e40444100c0001076400f01d42d60f64811401030039903004419000e000f140750030002550704400f450b1990244a0000001d4080ea59003000c00102d1016072000324100042c0c07001c900010f8071402e11640030360348aa000b9544500f44881200400c1c1c19036811200c0c13a400c1c00d415a40520382c04210761704510741084102540310340c2d01c5100d5000d403891030742030005403d01b4080081c0c1c0a0b856804007440440d0402560440b00305030041009020081101a5018104100030841b001d0581c403e5964040706005403801e20460621071821f68002501c8030f80540d450f0030381d800d0105600c0b12401d0150508022012050134942c4504800040c0e90060506101c4500d000c100d0580c0c8070114503101003c0240030a07914030099500c000740e500700303200741c0c0d00440c2081000700f040c0c03420001e03280300d522800d4200403001d89101c40031900040d00c44000d42e4a2401d00c035481e004101c25008115090200d50000c0c00c02c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 117790899 1250 117789649 117789653
    0x60301090504140304061e09080a0506040507091515090e1608070f1d0609030a110a0501020a02030a0303090204090f03081e09151f080f0706050315010507050c030f0109 74
    0x7140b6050400c124050300f0400003841b52941001c0803124203070a83d881400503040c0da6905440c1c4524940103290644126071408080106c005910703449544120b0944903501e40d162500c1d0300360391420145022104581c481401034842c042130260206000d494200d414540c1c401e110341c000e42d001d944000c04202d40c6107106960380d411040068001d420b6151900c00c448070a10014500c3c007244041e20f4982d40459a503404640e20749054a01c0104000c0c2541c0110710b56142c4902d841205460150056034214000101d0f58004101c920031180c0260152400f1046ca940890050000e010100da1003503654103503201141c8100550895140f003600d5442050501d41411044c02c01c194080d6401410a002045010301c0e000c644403407000050450890700751164a0602042d82c90b20b43d004c0c0300e4a180c400001444d14001903840340305110342c020f0b04c0343c543d04e0f90b5044070244001c54160701e02d20288900c400032544507000074070560b801681601c0c440d076001000030303040803d200b81c00f280d88e82d107803403190301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 117792149 1250 117790899 117790913
    0x5031b160608070909150512070918020a0312021903030507020606040504081e0c03072402040b041a12040b0a06050f2404080a0503070b01082d0c060301090504 70
    0x140900d41444607283c80c18150007044c4941034004d241c017141e190050003203078500d4806040040c0c5002000d416100300300c0d140850740d4042038400c1c2d114040c1001300b4071140301051034414107416005401090b109040d034841c2820000c00010601c1144916120b00ea140d521609065103070501c00d95004c500d84c00e2041c4000d251000240000780729502e0038041c080000c503260112080380c002100680c1300a800f580462400b0700035404015000e0100040340c1c02003004140c5000f41951344d501c000d8101c407a6411100049010b1b500420464010810060280c401c90300900e0038a1400503483e50f180804944541014800964084900085500c24802d0a0318180903510160400b41c441e080250174080c0041c0303041c0e600b1716040098100001c0c9510841e040700d41250040d140c05c100311040f1900920b0400e81d40d602884007900d4020745400049910140407030a028640200140d14074400c5100f01c050703161703018180002c44c00c5d102c1c035500401c454580c0d101031030081074844000260742c03a0034207001d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 117793399 1250 117792149 117792193
    0x1605030303070e2b05060405060108030f07021c020301020a02010b0102010b150412020d0f0822030b06012d05031f0605030a1e050a090309060801060203040b0705031b 73
    0x15100350828801c0201d1190701101088400700112018910154045001940c40b88410296540b42455007401c50038490000380c0e043c01a8410411141d40e03030703070f14502c20b42c40b0b004030b241d03a0b100342a0402c9190098580641c00320024200d0819402c61030790700703a00203801c80e406094440090303510b0f21030602d025030302841024190081903803110520781152103102d08030f205078001e2001c10240c40c0780400554032092411000325070300c640706015030b0003203080145143d04528110300780405585444a450180001904101c9601c50152080b50700d4101c01035505c17001c200d0321141513000c1707100641108a1407035010b640c40016034a64030390300d04044011042001c110540a400401c81e000d041001c80c0c3d02c5011250b214000b04400a940c2d500e40200079101100a400108020700344030601800384569404410018825101c42c0500c81d40c40174180d507035043c01d00c00d09004d81c006001c01c00000703840100408607070784a002924546072802c1e940b0755424443c04080b134140d43c0011141e51080c0f030380701184 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 117794649 1250 117793399 117793409
    0x40f0b010f08070c03030e03070203010c210b060403030c0212010f06080c0405040b2202090c09010e0a050109090e070519060f0503090a08070809030d050903070e0c090402070218040516 81
    0x40b0303061409020207080d0421401008080541d6551a030360700500034425501d0681d4010004c0c0107103a000c00300113162990320309141c041c04051042c120610f4525204200c0404400703886103051034a03689060380c140300d040c40d069030444050400e1030855842841410352503806440c000130190709101e002460080c445003d01d010302e00d048140701c00b0590187c0c10301c1c0d1050101114401000000e40521140c11904600941001d085018418000c0ea43d80151076000004c0e640c0c1111180800108a03031002c2601c10140801d03000c00307050100c3c0c0c02c10342007482c44141442c1102c0340c40c1d54400105995241880c501c0c120602e80c02c4044c80020340c050035070845400030345486415414a200342c42c2d2a069085002003401800280c203104122031103040d19038200c00201600c40c1c3d099400e00182056100b12821403082c00ba21502103510451501e540340118000c80b081402c010f401030511000f90f0101c44140e9011005400442105d190340c54600d05c102c0c4910083e020001d4060b2003403003000050340107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 117795899 1250 117794649 117794657
    0x702190b01090e070b030a060905071803120e09010308030906090304030c1203030609020a120b060717090f030d03151703120c0904091b0501031413050c040f0b010f 72
    0x1000c2441141800d040d103038400070000380f800f03044400502c0c1150340d500200f0202800300811200d1040c690082081747c810314000d200e542d4501508039000d629100724140134403c030541c18000719803c0354200c00342c4940c0381403a2403ca20120001001c84409920446141c680041045403050b800c2c0701460304030b0441b400035800c2c641507076614014032140c0e000d01885100720500c810140742c820f4025030b009200c040000c56031100e0f00003004016a803820340c50780105080592030b90b0b29007424011541c0b15030300840200d0481c1460019000c550b4003000010750310604010300308a041e038041c001d070046561661000284641003101c2c40c010300c0c002d41d200310002d022454044078002404400c45000c85e5070f208010800360390f940701404840c01403042a079046480d0100e000c0c00c00040403034514a040295680390307403a581d101700450542c1c01408000c41300900c4a004520288007030403d2207800b6110350150b941030450940071504075860300c6041200592200c0600c852560052102e0b0244086450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 117797149 1250 117795899 117795943
    0x3060c030e07031716110f0a08070608090a0b071d060703170703091209090e0d02030901050a0c05010507050316030b0303030705070c0e0c0c0706090501020a0212031c050702 76
    0x69071150100c0c0700241121a1881c0c403504135040060440d0b2010001d5411075010042d1828210f8040c440c91010501800312100100a1440d00c0d40b40d100c00c890601005040c11400c20900315850003020309400d01c0342c2704182a42c0d0002c0e032401c03699441840b442c1e990800b19020f44131a03108510610b0212401414100564800309502c0640e61140d41444c3c900707640d9580b59210110700a1580080282403600d4180318032502c181d011403660102c0c1c9040106102998440300016103e50b0500c0030328015034005c1041c2c8446501803030203405c148019060021608009444290039250704072a00743c0003030000010811400c4251b00c0c011030303c0c2c400c0e150810200c40300401180d88c034400a04164180a40030070704004000500e40a58003a0000c1140c511082c1842520020310380c000e000d03500035500461030003150031440752883ea0210f90050380100500c0d42145c09004242d0301070b441a440c2804204032412100188900302400001c802000203080c0c500713000c2c0203007070410039605850b0180b0442 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 117798399 1250 117797149 117797171
    0x90507030602030c1905120c0906070507081f0501080604020f12010606030207060f0506010f14040b07150b0d05030706050a061509061d1e0607120f0806060f0307080603070909080403060c03 83
    0x4641581c440c4c0323219201507075107404e40d00044d003074022281d00404a00ca801c0000c03404080109041e09030842d2101d0b116100c20b007003103902e02a64024043e00c80303164030150000f00589004468a0401107005d80160320701071085502c02e00f5288141c101e42c01294001a400041000c42e00c609103a00f41000d20401642c10000c0000b407454030310445503810002c41c40e96151301d10800c80c04940c000c0817580d007000d41e503003c180342c02165020700c686d02086e42441d10a5188140c02d00421a140f03103a807103809549080c24596500001f003001070a450400350740d030140400e881200400c0c0e003085540d46d840d02c912403440c145008191250800500c1d24081d0b80d800100130f245c0714000300405881003403011807030b00c6003080003164181c0605c0d00c0c05803500c0781c43d01d054900740d600034490340c4e00403401da501e450307182c2c0d50001031107140e20030344010100f4001c04000013500d552281c40340a070821001016918a142d49519a9054400c00c0000307440d0010005807c0003000224803800034407130715504041c0441e960302 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 117799649 1250 117798399 117798427
    0x11e05030a05090f03040620070308071403091806040f110904022503080a0e0a120c060e1e0105130c05150702090c030603010b0f060a03090507030602030c1905 70
    0x103441c803080076407a00d000c200c40303003014480041619500812a52075941e10f00e80240b60800440d103829140069800315104503c003c01c04000b41d070340113138010b8508145075032400035103420803807040720600082c08080503503550307440c18400395a00c64643c0540c40c20301100b08000c0358055a602c00e03156140010159105521400352003404204407001a220500000f1303142091003980034030000c1c1d03800319401c6402c1681081d1602e000d1070708500200081100041c065680d0401e120004d841050340048128200d441426034a804511a0310041511502c154002d807500f50f00240001c0000301900800b4035803442480b072964441007441581c8801100350712074541c14030450103458041c02c01603030b20107940140c00f0700300c40d640c0382e020703100000502d8244065140b503001980c035180329500700384148505103401b003190241980000c00d0f051802c3e500c0c00d010b4004020545084800d8050541c000012448a03c003451007030401303804981d9139800403c2c0700d030305414240c0036400c02d00c001880091801041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 117800899 1250 117799649 117799651
    0xa0b030f060c07020103060315060314030f1204050c030a060b040c0e0f01050304031b0302010605040b0607020919090602120105030105010e010609090506060405210c0a05030a08090409150b011e0503 87
    0x3030300d08000e43e03805a80c0012000f500c125000500069820041003e5028495110301b08903401400343d642582108841d0719124401c0c5585803100c128140030301c40400c0c4081c010135820500c54011100b0f802d1045c00824140380c015501a504142d88621f145002d00309409100e07121002c518241583c03000701c000080d00c4062400129040020110005007054041c9244000d041c441c001c0081111318103260090107805507001d07443c01036060204101d81070400000742d80b25140e00400d4014a941c4c0e501100034850381c1c91440314903680c0c5440d081c20114120344010200040040a122803a604001c18582501c206074064020036143e000100180c07540f10001d00b0035617584183c0400d40703489050000e212806550001034bc44482e07100e00c1610a0a1408085074450440040d1200c1801580070000c03a0400b9110303840d00f540091000d40001076021004000c0280018400100604162580f01d82e02c0c60b4101084080f41ea9035403880c0c1250f800580c0000d4a00e1260381c41190315040007401402800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 117802149 1250 117800899 117800911
    0x109031e090e0406090c1e0603020a0807181a071a091002070302070b03010b0703020c010813060b0423010e010b03041a04020a08010c0e0901050604080a03120219080a0b030f06 77
    0x1021000f05080244940110032001e4011500e4030a03251180c0705902c2019034180600c000c445070f00300007c0c0c154000e0003a0b0720800c01c5521018819503c6c842c003501c0f009104901c01030007d54034200441d154a080d040d9080d03182c00300e41040d85881d41d61500030f508a110705070241d40040d80c00100084204000303260b01a0b00c6980a0150300d0300801e207030680ca4554541c11500e03400300040004a06c0780361100280c038a20f4000e0342101e44600c5140e005540003901690981212006c180b91400825020b400c84c614200019200045000545c01030400e48041c10742c00740303481142c06004100405880d45810702401c221803205145091990750700200440300d0b40080ca0414460340003c0a550303c0101580083c6408002444a0800e9103002045102c20900c01c52140300c5c600004529814410103541c11358001800a241d41041c5842c16588500b15204c0445c01d541c0030441c402c0030b07500348c1c8011003503441152603210150800c080d00005a9110b001810301036817080000d00c3c80103000080081e0403007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 117803399 1250 117802149 117802169
    0x11401120609020a030e19150c1b0606050102060a140a270506090d0903152f190e0906060c010b0d050a05060c0705060c1303050f0109031e09 62
    0x800031034050240500d6407102500c240b010446041c0d960300350700284130b04c142190550700000d03400308040401501d0761802500c0b400d45604000c02580c0507900c82c8203000d0450406907903a00040c1c080d0071030f0400780b00080b91020340740c0008101558041241a40001c001c1c5014040c2102c0340d601542c14000080040e4106a1550105500781000540d01c0b09000064000c1803143d003030170b0810039512681565111243d00c0340707801c03800d2131500c221881002e40f980880b4466030345480c2d000781030140040308154180d81010342c0200c04a12081c14003281c4c454910340149880c1c6449200320104040b000f0150303001d1200301c070300020b001d40d5140101c541c400f00448a054607081c00c90561741c010420320070031a80258281c0c500d2000c5c80b00000f24001503a21550842c0c40598038013548400b10302078004c000349240d00c80c001240ca201e50301000303018001654161003e4032a074a4880ea458001103030036500060350b40750841014580e0001c07001507284658092401c00c0c40c1c0c41800102360310101d216041c455 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 117804649 1250 117803399 117803417
    0x1e0c040812072103061410021002030711030a08070201060e010b09040905011107050601050405090f071703090d060506010306050f0d080d020915030703180309030b100e0c04091103011401 82
    0x41904080b929000d0784803000380c64207500383d0380980244081d0154400a041c0e4488204080c5000e00c1c10307030260652640a44000744c000e821060107908003511050610262003140b2200c2a400c101404146285948000d250b00342800080d084880030340040c1c080000e10070040c48100911003c4038034180082c1e43c0002c0d4000d0904100e40100052400c282d440840082c4400038404001000c6050302c0f000c80e0200001e841b0400440e40e02c0d10100400003090b007040c80200b0104103001c9a000d5000d102c10300f902d04d040c55200c0010454800541c0c11252540d5600034800d00c0c0d68903100300800b0300800e403020507130f9640180c0014a9002d154000500003a00010841c65810440e010b82c1c204105c00b802c0e010000044000f007283c1d03500116140070000b80340c0090b010b6030502026007903070483d4160b124900000d04585a841c00742500a02c0003052411030003001642c1e0710850007081c400c5985100392a00c0b80e080c542f000059030348240305100020424401440101d20401e0301035008602400c0503029 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 117805755 1106 117804649 117804653
    0xf140f0c0310090b0c03040804080d0c0501201804230f0a020301030b0c0f070b0f0108070b070c1403100507030b1c0c03080306010908061e0c04081207 66
    0x104070804c0c042070041d000310000316000380c012036602d4036054403104201d151600c030b8030020000461001c0141c06000c005e1058032122181c20342401080d201402e420090340c0119a102c040c0507002080d040315542d00c9600448050b0b0302c10500558401e1440040085207a0071114461541c0410300040c01450f65071084038183e944c0692640c1c1c4a0b100c010a5203d19003280ca20200071003020000c0c0e10120300307007590151081c440c2d888440190340c1800d05007401c1030b21170703400402401014842070000030703980480203007a0785055204002c905000e000181c60007450381e10694071300380f6040502842c1d9030325400503045000e05690b50208140100350500035003101c1c400280880442e581d042c400140f82d10b00558101c030052414004c01a03d501103541040ba054850209550413a031307c042c4022101d000b21540101411015401c2a242ca12417540380e0410b40700c500284030002601d001 = true := by decide +kernel

theorem cover : BRFrame.Cov 117625899 117805755 := by
  have h0 := BRFrame.cov_init 117625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 117625899 ≤ n) (h2 : n < 117805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
