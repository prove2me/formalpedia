-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0514
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:11:49.081991+00:00
-- url     : https://prove2.me/submissions/6d4e0e21-ba0f-4111-98cd-ee2a1f729228

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 92266187 ≤ n < 92446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 92267437 1250 92266187 92266201
    0x406030503030c0901210501150e0d240f150603020405010f050f210601080a062105010609090f0b07080403090315060801020f040609080604032c040612030314 70
    0x2c4035042038040f005580c1d9401c408005946405401e031100030403024148202c041001d5552109040c0e81c03108108980e9155480c20445820142c41180ca40c0156034840391780004507400e881d140c5000c0c5c142c6a03413035189a688110401c5911002170302d00c0440d103600c0c5105682c0c1d6840d203c84054001824110306103828400003e04021514040300148100003c28460a018120a44da540c03505d00a100800f40c4000c01c1140e291041998503502140c0d6840100303480030306602a11003903490720741c1d00415a4806c014580307441d000c600b0080c0c039155a039000c00301e08200301c0e0080810b4a40a40003441114002d40741900134500300410310010040418144000070341c0c00384109003242d4115010b180940c012901410052840da44082c03859880007441015614040c4090803c91320161184d1812690301d050043e01c2d00c1045800500060010196028811181c0c06203034900205059040d0550001c1021401321142900070741c40c2c80e001003101c0c0c0c1c2010b42c140900d50b540341100300d0794482814000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 92268687 1250 92267437 92267443
    0x302060c04151206030c060c02011205011a13120c051305060f040e150f01050a05030f10020a020f0f01050a0c0f091a0904060e0106020601080a0f061509240504060305 73
    0x290305003c000120441d003604490329007018010395080030031103885640c0c0312005400c160326404100c1c04109865400862000301d032040904882e41003030308001c200c034255070a2210f58040f081c04456800220400b04102c60703091000ca1551740306069508032a07051504200c7d0540e203001c1c0ca6a05c6c00e051104004858641d10566110100140ca000c44c4000c507000b445824400c0031000d0304402d0001500f009030921b00f4441032412540d00340e030b81440b203e417520185030301c400c804280c4a100b640001c80c84285100740e2b034001d10a40341d140c0305441010707040c040e50314145200c3d080c00e140c16030745802c140052081c062044092040c030038200320050f4003aa42021307003007500034410031182104403480200079078540800c6070815a4000c10412440ba12486050711025080c024140140f081f80000b0500560004006d2109600480c41c150321600d1036851401400c0e9000c803045030301003005030020741c801e00c0b4094070b0380158402c015072160540c11a04102541a00d6010030b20070f5044c00e0041011071004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 92269937 1250 92268687 92268719
    0x501140c0c0d05070614090105061302070503040b03040f020a2301031b0c0503040b0a09030614010b030c0901020a06090807060b0a0609090b030a051f050601180e0a09020613030302060c04 82
    0x20f4280305407244480d007080b400038200507204140422070300c0100044400d06600491003008112403030b2040042102c4450206d00506d0001091540300700400e01c002241c8001441e4000e02ca4000c000400c0000d5010500c0303c4d03040d40c0301580c1d0744242580d0058014000503004480802031904106130045040e4500180083d60341950138400014190420f00c4000e00481d0080c040501d9402e55441e05100001c250898030b10017902c410b460408903140b01012250700d28100c03114081824210348454144d48010390000324418154030400e10f01d4000184180101848203024101c825210041b030b0406405680e130340100507114210614060040603040003c80055035940280005c000340c0310310201e4a4011307061400b41080c4140d81c007406810304426183c16440400060501107511030b0001510440041c0c0d545040c1800407810071b0018061823444a68003072049600415001c0c07458001c101264415100c104072801006024070906030100000d9030000003e0600614151070080304892000c15 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 92271187 1250 92269937 92269963
    0x312010e04030909050604270203010509010203090c01051c0906020301090f09080d09110d050f12040303050702060a031e050610080f131a0a0b04050a0b09040314070602070501140c0c 80
    0x20351004540d05132900d51020408d181c05195040d107000125010030403d03d803500b0100c2c031940c2000001022003c0c103000366401400f22030000c00c5802c000000640e1550408286214840603000c40010462240e0080310b00b000d000d0303440146d0729418074828105440711117039541d85a60a068080d4002102c0d00103e0381120910080001c8036829850500d01c408032110003658405011b80e0440e040c0318010402d0508442508100c5850b6030402e100d03400113000d503200c090086038041c0418005810308100601081d24946000541503048018402400324141c02d5040340b40d6803101003203c0d50414001203e10b8040741d0070111018a4060586400000700404042c0d4003662400c00c401044501220f0345d20128072708804180f0381c60095244e8008080400059205504060100e00e91402383c0c0306071200010041d10295856031991401e44602e8070030364103809140070400c507450204a0520140c020350b44610004110750f800186031609160010f480000c07000e104029144510a00007910082e4541c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 92272437 1250 92271187 92271191
    0xc0216090e070b0d020d0b01090b040302012a0f2006041502010e0d02010b0102060105090610110c0a03030302070501051015110309060d05041b08100906021306020312010e04030909 79
    0x708151509180550344012a030f0140890010075409558014001c042030607041000010b0065004480c0c4420a2040c4615400b0812050000d548228010b14100201e480c44c04202ca1800c0c1e003508400100c0c1509850141d81c15403d00204050300320a1130742e10040922140d11400d2502c0094680c0c81140b2844225031048055a540c040c001e4004d90032004810b030a0711080340607194040c0c0607010f000c011500500400001045501d00190b0b003038024140038110820b4501a00e409941705150000740340700500c258004504259100c00e1840041c40c801c0d6009030301d649003464203130300b5507802600c0a41d208000b200c090102c407580707a0070801510054985402040c1a036011507041d4030400409a810202c00541c0703003880140d640169004501c20740001c49542044111080c81000b00d000350001a00040c01c00d139071000c00f640000703c159018010061410b4a01e252501c1d01c50711a60000025130004213250104598608900780103020080004556141964008240c402c0901070314070403076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 92273687 1250 92272437 92272451
    0xf0506070c09020307110d03090b0c03060a0e01060c05010e0f03070b0a0603020d0b01140f0f190b12010806070203090303090108070e09010b1801020c090621120a030c021609 76
    0x70109448600003003410000843d581d04002d00e00821114994107454114810074004c1084540720b4071802c0300e0180c101c1c0d1402803580300c1030b50040e010391015040c99442180134001280030414114024001c002c240c036004c090031680c0c540b45080d14070000f18020b8507004401d620240040c00b00803200705582c02210b0987d19903a00400300000c020a41020703400050b015080010082c00c003242a059405d080c40001580210204010201f003843d0303451904038041490344200c03810303c400c1c181c030b0040400c0b4842c409152185000c1015030400d55002d1410f2003c03100400c41c112041c421550071150600c055464045c0c4080401d0740c901c11042e0450400102e44002000e10f841291743c03104c008401048a0b507256522000c1400c960050a22843d602d44020004c030002d60001400b01c007000c40180c919420341d6508020044d500700301100400d04240071801356004100c041c4030b466000c0011080b51a1291005a0018121000031002000f50340c0690019020380c0e40d0351020707000b19412a840030541e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 92274937 1250 92273687 92273693
    0x501050c10090c09050a0b0109140121051807030b161e170a0209030a06091a1003150c021e030d18110f010c03050a03140903120708010f050607 63
    0x454050003010341c1152516105104010785407804100300c0d15a0b5a0501281d100d581c910400c036041c0f203071b1850120345501010800c402801c22448004032050400400140c4051014207000000a5883e12403e039a42d00700101c2c8080c440110800c0c81c4140c00400c4654110b03134840718584806400810200303801c007000d66120b4071403007004207002d60140150751030740f81882c8041c00301d2450f0109031009a43d000005440706115100f9613001c40d03002401098034443e2521528020101d44c84142e54a00b640160044030310b030b007000c1c00e078040c40301180c000b44001d01e90300380314a000a4200d2074220303190034024240091680021003001c213065120003d0002e42e00c82d028140f45126105020f202e50341820000c1582c501c01c901e4071802e01c0d0040d01d19050495480d003c00c500100706400e154041142c5880a102291142c0050503182c90759050029001091100e404c101c144101d071b29075141e50002602e2585c100d1108001c42c1c1040c91821700d40410350400d5045074400055000d090700501000c1550070134 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 92276187 1250 92274937 92274943
    0x9290406030c08160504050c070b0a09020607140c060315091003020a1401020106080102040605041e0315050601110109170f0f0a030912080606041202120d03020918010e010501050c 79
    0x1075500501068031290f4500e00a9214500e4000d00010200c0b88800060079003418001c070391246030131100e01c518000c03c0d070765510392000340502200701c11366494499a00503101c10b001085400d0007684a404030340c0c0300450581c989203417a00b0b01d5000d07280078400d20032100203200304492820007c840c9030f102e59a42d515082c4440001342d2020354050f08c0b0340400520310014590b0313442195820f078020311426441d103c00c0340c03d0b4807440c86008006041044104415001d41d910040c681d0110009070034803503a603071101c100800480c40280b030311986e15014083c007517820400801428544600a201044803034071000c0c0004640010401e400ca80000d905024450540850303451603546044c0d641c95101c00c100040041c441c180045589072550166000024045ca0382140b05a0005200c240790034108955000c80503084001241c001c01a11002c098840c400c0c0646150301030241d40068985481d00100070180200c0c20307400c0701c900c0400e00144a04000d41c80014190f40c1e080c00d0440eaa1010042da849c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 92277437 1250 92276187 92276189
    0x90402040902040c031a090903040b0c1c020114070c020d032015041103060f22080307030f15140d050325020310020f03060d030306080102160b0109290406 68
    0x16000c4d141881c4241507680651250b1403902c890000f040b040c045800c00c0c00f103120802c2d81d0f40545580300748020011607060b50010072714040c005054881c5034080c0c4c6414085030441c4403850002d40d4440b001c5583c80b07148444810f5220f0024545204145055004125040b60481d005010003000141007480b610402d07040c0e6158526140481d04030f011070303101d03107065824241d40c00c0b11809080a0340d07104a03c0c0004125004404000e9100480d849400e0707169032030b811030031620000c8800b0707078681e002144601003c0c1d403050140c0d403000300301000d074030300703903000f01d03049402c00c4500c0d90640502444400c030560034218400300c0650704102100807900340346142d03001e04100d0011000d05c00b031201c040240542640c1d404503100f075040fa0203285030a00792205034010300034095920703a81440050030b245800c9400005003402400c0001d00552038005441c203a0340308645400d4450300d004844410002500fa0075401012101001c10001c050b0924003004014244680c00c1f240c104800700c403d5580e92076003e10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 92278687 1250 92277437 92277439
    0x1204230105091503060306090303061c02010216030302030309060a060b180f0301110a0e010912032616110a02090c0c030405060d2c1e010e010c090f06030b0f090402040902 75
    0x3c0102080c0781440781e00c3e0790003160410701a0040074040340104034000150f0f40640c4000f00340d034905407040a8819041caa08200680c1103124100c08892042e4902045101841c0031b03078041c6aa81c42e01c002a6482e100e4040e01e5038000c0c42c0792003400c01840061034155062480d2100241280000c60000a412044001c940755071651820b8a001c170b480b11f241000304840300054990401030302e0034600558900300144203c8403100f40481c16500080c3c42050303c15880880100180711070b08010700b52220b042e5046850549004c10103566818039600403000351003c0412200400c030007002d030340c04160f951402a1190b5001c1e40c02280d4688c0540341801035070040c110113440d81d40c0f41c3d54100140b00207440d1501a1040c83d400000c01d401d10f03125811005a40024184003c01e10300c00043c440c0c1003070707001080b200300d499503030f42c86003c0c42c0003c203000300003510b502a0380e21030500c0d0426204068080d0580c1c401c030241807804034281d100303441d511070b40001c0071400c84a60045550b90f001140c09041569030013 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 92279937 1250 92278687 92278699
    0x30904020c01050126071202042307140424020a0b04030503070806040203040c0303120f05090703030906110d030b0a0503150f1305190c1d0405120423010509 69
    0x14003a007901584041c1c129103c2c8980280c5003060042607002004516a600103240c105070801d109004000b00c5418019101030400120100042482106211303510b0041c80c0e0050740ca424044500d40c8601d12041e1500da180016140c24507040410015040000f060714206010a81c0302c1c4169000348101c444550b005201001940b500f4500109623a1041310b0040200d1004c1d80443c0c5541820f1099900c52944800d0000c141030442d142038410740e00f55a0350707000709a110813080d400942203009250140003c84010242c05045142c0070b40f03d00aa03400440c1002089400e00101020018080e04002c0950400052013001c0e00003040f505201900b0050300351050300000310802d586080564800c980203141040780d500c5064a0180b010b107080f00240681c0e01c4801e9400340000c00c201161840340c8900071142d90540d80f08407001c020844403043c041743c00020010801400800c0c4003146042c610b00562500d001d0406619500e5291650807410300d003100303090a144181d00546c1100c602444c02800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 92281187 1250 92279937 92279947
    0x50f0d0c0e091e0d0810091409060a150605030604060314060a140106020307030503060d02100518030c0105070602030423030d0f060308030610090902120a0506030f03030a0b0303090402 81
    0x204401c01c1d4207852246581c4280407841d44071200300140c0c072188503084400342c8200284036000326088407018048082528007214002601c08061141200848111a04200525012003080c4c18000000c0c4a072000c00e0805101031654440f00707030701c0020b48a4a0403c55200e480711408180206483e0308004c0c8810b80c0030000540318100081c00d14030400f9014070034000912107110030a0758201c280b00c0e1342c0c0940c0c001d00070000064040c6026680c0003001601045003a0305035000240724140312421107003c5074000800c007520041021005200c003505030014120504034000080c014441d00c200900001d0340440480d04108818050781444284542c54008810a280004c0c1d182e900c18010080c006107001c0c1100d00300c0c5881e0264004503900b00c9051425940d644003449109910900004200700c1c001030007003144d00301c0348054111600706400503a04c901e0541540402c4610181541c0c0c802e40c00440074041042c0000200c0c1d81c444282007001c01d081e5191360201e480c6014040c0110f0b481800421 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 92282437 1250 92281187 92281199
    0x13140313030f02030c100203040b1809040813170a020904110a08060703060e010b030a020a02030408151501171609030b01150305070804030516110904060603050c03011104050f0d0c 79
    0x1242d800914000c50540d0a210440b004112210b02d8913001500560400e00c000c11a481544c0042c010142d6200e09202000b00c10f080010794120044a08a82c410404a91000354400c000303510005400c005040d07480386491500c51766035409000f6002885038902a000030100908043c03000e20700e00c80a007003004042c1d118241c00781c4954048a402c03000034038000000400c03514500078a8105c44029007150700d95240d0480600c003941c03111042c00c003948030410000518031001c12882d074031400c1005040484c0d04002440d140340300c6051708a14100314901d0f4140d101300261510254120b00b080e0ba03503002c50804180c2c155044212603101074141c895140000030052000042400c000140d03580400075683c440c201698030303090603600540025418440c5200b21038516110f541024000e04550001c0000b42d40001c610036400c071000c841c015210101001041020003028881c01e204030020300c5960000301134051540507034481c00f03101e00314003510b620746038442c0881c498801c1c0d000100100d900c0d495003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 92283687 1250 92282437 92282453
    0x71d0406020c0607090503010e01090201080c0c0a08040b070213021819051203071a0910051510030209040608010204051302070804090510060e010f051c0e0d0c0302070e1314031303 79
    0x101c40d071b074000d500f0a4691000540306105403104503a050b1181da801d52110610041150092140d01d0303040d10900d071291012aa505003e000145160743d5220b0f0f031410300f8810301410b481c80015088001b40148240902c0b1200780314004000c01041d1180c41e01500000301c0f04200c3c0d14168061504003200500032206400040000d1075424054003814a104100010300220030504480c24030031904101d009200683d0300740c0003290850682100d0340a0600310100003111401070120180120b540002c81040c00e051a00070000107000c44002142081d00e864040346400c1d04070b80e6100c0a8076400607400f010001042c0940d0003500782060f04101d580740408400714048418013440d00030031000258881c4035231048a004c10340c030303a0b65920300c0d0030700032090580b18048010070144a0165200e085165040e0010040041d03440080d607910101c201c1c1c24103010f070504e0f10a801c440c446003851020040d008814120351000258800294801c228403800c10720b045010f580720000000c5180c001c0041804010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 92284937 1250 92283687 92283689
    0xc05130906021303140703020619020a0501060b040e0907050102030301050103020c030c0102040905060a0b0307172224050606040303051608030906060103050606070308040618020d05100b03071d0406020c060709 92
    0x83c00340d91480001d00700c0d686d9803100684030081d07111204200748a1a03401e070549100044030540100c541e4000f0607907078135095075550b4201d04500302012408000ea8500040120b42141090340600022800c040000391a403005000e00d505140c0c00080280350f0620803c209d49044980c10700843d221a140c00c0450040c010940701c90b40308074410280810100c07032410480380035106a4035600c4407031a80c02c1004540f8000105203203094040031032584001d540001007101c0440c42114400303c2e4800ba00084540300804204001c0e6003450f0504021858072490112000c1d29050708000341c4521010400000c0003180100041201001006102840400240307007030040300d00740c8050085545034824020140030310b60014002850307817004100070541c03d501c4100b2602c1c01c504200c2c907841007034010680ba0f00080a0840c0e0130307404142c2102e0342107010f1090640102c0b0071009007810500c0c101e5444d400f100b20303038247c5038204422000b050070421540d040301c20143d8a20141c540e00d142018000d0044115 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 92286187 1250 92284937 92284943
    0x8100b0c1518070b1318090b130201110703020a09020d11070c09050105010509180403120e0a0b0105090103030804030305060102160605030f0604291305091b09040c05130906021303 79
    0x90b08102007002c050103003d442d10040011460305d4018a0440c40a081030340d018150700b201d07079544075503601140c400403c4c07603c1126045050070581409200050060b00050b83c2003040e074100e1141880160381d004182004c4864812015880d040c481c18030000904468090003210400050030078100110305640c81c1c100c4031551400c225503a0396000545880c403480c0c0c6603640c06120101e204400c00c0c5407072400354006000b868900098607c1d0341c92041200c880f552a0056036100340213010400c640b080c0000d025100036120074195500d541c1d8003030540400504020107058a403000520181d03c2004094a58400c40031001c440d01d0740c902c000741045e801910407009161101001a045041c04d0045802c030122008039401d0045510b0804240150482803c40d401031103105445a92016405064024441d50019180c0d840809042d841c0d00c595910750180240344400801c40030850001e2100210340c1c060354817140340004040341c840103101098000346a6031001c0f6500000000c1d0914200c00d90344 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 92287437 1250 92286187 92286193
    0x1060f020f010605010801150210060b09041d060403050703140f030103150903020309060c0a020402030126010e0309010c08070f030e1c020d02060912010f140708100b0c1518 76
    0x344199800d42603e10758000c5602281c07100d00108041e0044582c0281001c44d548156030a00c00c10082d0728080c0d40c2107a000300240c910205078142c482c075040c81450b4070205100500181c00c08128184c1d03403140300c014000b034140200400d0190038940285001202800a0005030b6035036402100c0000e400e40007030000381c0d0700d02c41d81a80403a00300740703903c00c1c0c010311034244c1c00840c14014a40700300880ca0380603c4803420180521518000141c9032800a14007902881c4001c2024114055036021175400003c1084504d81c14840702002512020049400c0c4030760a203004001140c1e1030418900500c503000008250380c40100002043c903a00c00e0481c00d000304111600486082103a5078185c80c0302401c2c1000e0b51000030210314600501e48400181540c0c035010b40590348000d000180d0600312002400720b140d42c40e88549417852003001440440f50b120700d0754107181a190910704205640c81c03195003e06030887c03500180050b44404100a19a401c25407100e0003421464820440040301f144000310000505c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 92288687 1250 92287437 92287453
    0x411010806150c03040b031602010b03151603060b03310209010902220b07050105010b0f160206090a0603321f050d11011103032e05040501060f02 64
    0x140c03280d4412805000020322254401111030052a12070340109101501c0384420000050000800750143d8424900d104551003110b83c240000303801d4528204240b442504560180030800750300a8045401c405403440c010300804c01d5210a03002001903811508000380d000c01040580501c0c0e04020010390903c840070011007650844001644d000403000070761200c070040040c42a029940e0161002010050300c6c1012a09501081da542105c9078001010103030000420000344502400b416006052805803e4176000e42e8640d80c4240703021342a010600c007403030001803000b9596610f00348d0b81500401400020610707a940f502600400b140340441d915158400d10320500400c200600c03107040d10040341480940e544180d0070b404004a000c600201075420a0340114590f141c0b107178541c080c00c0c030440d0102d0000038000c00140c0100a20000d000165104104001103c1c0f081c002c00070344540c41d001d0402807001c0c0001100d081ca462b68005680103454040000761050348111f10018120313564080c0c80c945 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 92289937 1250 92288687 92288689
    0x31209080d1a010f120e120a0c05010e190305030615030c09090a0c0509090c1204060b0306092802040b0301143408060301090606090b0f0108040c0306050402060d0c02060411 76
    0x80781481014008201e08541e142400380986d00012891030000c1c1c1034034500d819081d0001e50070340281c0741c01000503d42d201d00c482007020901c00c6210311014079008050400143c488134002101c5a28014104080800850441d885007440300c02c0c6078406100c0c01e0b80f04e01d014005000c50b6002001c046101c0d2000001080003900c8910030140c002d4419564280303041c5004081c02682e00c005084d51206020400c14400181106c00d80d4070f00641c847d40012880d003880c582054030704135018200d8100743d00980b06031440203a4450169601175a0840440303c40440d500018000700203001c6483d4165013400300c41c3c210300f000c969105204034148132402510444500d00070350500c2c010940c0303444003840c01c01422540d030b0284c50f405a0015000300089030940c0300c2c2d9205e01c1554840d80c01541586c1e280c0460040900d02400414071981080c60454000c0c501515080c1c02001503120291400d0380d01c101040954039407508540144d101e02d9001c1c49920b04070b85000399949011101517800004100c00700b00d607 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 92291187 1250 92289937 92289947
    0x3050f07120b0103021011030307031d06101707050a0311090c040e06010302030c0c01180210030c05040902070201030905150f1003020303070b2203090e070503090307031209080d1a01 80
    0x400b600b0064a10b4960f00b07641c04d110307004c2002102042404020a445080c8020800c01036129166036900401d42000c111080344404074003230700114054200d64200a450b81c800e5501c20100c807041990515402d00ca2141a4184102900302c01c3e00036418a00120500080454612511714255800b4046a0701c80d0b240801602940c0039002c042d02c20000071582c10740c400d07000f840d0003c40c45010f040c580081195003601b1614180365891f02a405410900b056243c003070604060b2500509050203409003002c001000352055009602407035a01056040c20b59110341d00c001300550b400030071198030304054140e1400e8000704441900500b5030325000a94800c66481008013200da0160003581401220358408920007401400c0c104483c17401e010b0304103a0031000c0ca5086c18280242c4400000c5402c28208880820000b04060705001e4108184000c80d07030008200da03580c80d010f15161041c0072550303850b1006080300c0c0741d02030a280d8000c5220318103054a5400000c10030559818442000b00007001924 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 92292437 1250 92291187 92291219
    0x4030b041103030a050f03101205010b0f0f0604060c050304090203040b090d0504050d06050703112106101707090306060f1e08030d2705030309070e0603030f0a030b040603050f07 78
    0x340c0148a200c84144246c0701070340e001011071410b1641507446400c070350b090ba90002802e07a000c0c0e459030700300717074003410400010b444c001020384060059080003c081002d07840769102c2c1d1820445045415000d00c1001d1003a03a000c0d0610103002e65490038241001303192080b041e911031413980141600d040c0214042c4049070708840000e07212204981080c0c49071001440006c010006254032407060440c40c0055000501c030b01e01900301c2c080c0c1800051848034030179100061030603005103c15941c2c5d0b5000c6400c07002c410b942c041c40d02018a510b07902d4443c201c6001c40540c0c0000c0003c0e060007001f0030461420004070060300c68120b20742a15025403091903200e4001c5203d200301c0b5810412502c0e08801c0b00d50031030b20200c622040d070340041851003040f121840044800596060b00084140100f40310240007580042928030202c250b2400c2c08400039841c1e11442204503071400d0000369a81500303000360400002c0f41d5009004001d42c55030b0703040082d01c4140b02c41800f0054040e4100100f5241c14170411a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 92293687 1250 92292437 92292457
    0xf0103050d030e2526060a200703030603020f01020d09050f010201061805060918122104030c03180602070315090b0703090b220308040c080304030b04110303 69
    0x2207010050a001e8006044400307642c6200e0180040036450111801c0b900d02c18960b064031049000352810100b01c407961140101c0921542419038640114000042c0e02d641103d080d6a00081a544d880400080201d11003e00d040140b800324222091681540c401d0302102c4c003e84d0011120410355004a0b210042c00b0000030200f001b8100a1015080c109a10880c1c2c080c107000000300d00e5140c815024020032070113040011903440e02c0400c06603007064400310703405c44c0319411011580021b8891558072582c900c0c3c0501340c03106003c5026141c0741d0f268101040d42c603200c0100c1941900301410005c000729205a42a004174200351004d1070070914048083d000c4855650141c080c050450791040c1080041740d4001d0412a1503481400115090210407401101b82d518002082259440c00c001307441d0001f010005000c00b4100841c5915003a00300c1010243da051405131001d13640e07841c0148884207180c005015070311000c10701008102c000c00009028a02420a4068440c02c590425030781c2d100c2d030743c440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 92294937 1250 92293687 92293693
    0xf050c0a0e040803040f0c0801020f0d0608030f12060409020a031103010b031b0d29010315061a07170d0b040f05070c030c03030209060d0218041505100323010305060f010305 76
    0x203400b0400b04018011b06521891041c1c100640d10512182079800000416541c1080054954407010142c4a420014000c0794003842c184a00c82d4401c000500483d032406409056080000351144d480780e02141503654020000565191a800c1c07500385110f501c400c441c060741c03800341c80860340d140000c4c050350340c503101c028486071102c100418031080d030f0300d645130490b41c0101c44040a04109080c14080c0c049400203e2007050940c0b540c2811540701d144076002c2c610280c5404410310045440d11344265403002c0c2c000c00c8546c1c4a415141c501c4107907440560b404104100400d055280d04840e0b0050700018400315018040e0014041d070703000844200f9202a00811030311814200000e008140c901c001c58024280107007456840300c00b00358070b5449508001000c1e41d000807140c5180203402c0742c05000c400207507000c20010140892040b400b0285000f918170400c407140e001c2d51040e00c281c10a4441c80007800c4c442c0d1410050903c800002c0d6800e0008032000d000765400929500c42d03003040345048a4000c402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 92296187 1250 92294937 92294941
    0x70b040308100e071b080a0c0221030d020a0c05010c050d0e0f0c04091a07090f080102090904031b0c0f24050d150e0f0114060703020703080310030f050c0a0e040803 72
    0x84e1086451211080c5c40c55055039030920100340840090800701c0866119400c00700700c0c034410801440d408107190903401c58407440f62025040d0010503110450301000740140c0e12980d06c8401d982015916000034008e6086c0303c402000707258803602070882d0003c9002d050010102440c010381c3c071402c048280e5103040e44801204043d85c90144c004e100801d000f5442d0a010b000e03100c01e148069041250800045904a4410840c03010f0f4203a5600c01003c500008500740b032030100c00a4020b52001d840a000c0060940c1d10040c1c1c814242c0d00b505d50140c0c000c0307409040c42e58500c0704a00010040c4a20460780c108d0815064181946c28102070600103155600362802c031240d21008000c0c000c82e440350458002c0010081202d21032210500d006960102101265601d401003032480f80142e80060f40c010002800941c0020b90005103400070b89a1107095940c8039035449014181c08030299001602c00c08400241205006010640b50071a040568091207865181c2032049080001a94010405002040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 92297437 1250 92296187 92296201
    0x10c031a090402060405090c09100306080a0f140d030b03070902030c0d020d0b0d1a150604030303020705030c01110a02060105060702010507020d0302070801110408070e06010f1d0303070b040308100e 87
    0x4403107501901c001c00f442e00341070301d0320040f445085c0100c4100c460717420005861100c51900c09070106440ac0a07203800c1c8113041c01c3c5190103844070040d4070f009000303014190100042148444150320701c41c4010040b00c0c80001d11403001030260011040050290040e1036010440205600072a846010031061071403078003007030117107510013544130320303902040241d0f5a082d040059070784400d0b000510b40600401101400411307680b100046015088007401046943d4003031064a80e070041d181100c1d01410010f8072030003c0d0910505500c264140403856504c0d11f000d0003400f0581601400451445900b06e070380e140c0e00c5209000c00c1d07100751140a400309030700b40703c10b400500c0c000e052804aea51080c41600c0c050703039440e6107080c2550b45140f108072611030003140910009000b003100f440140b442c0458240c03203040002c0040d1502d121030040a0400c20040709140170441180c5640b85088406800c0360351b509860b05018400403c103403012000035442a01081807800c9070a07050042e210814070f12103064407580c6d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 92298687 1250 92297437 92297449
    0xc05040506160b070305061f1e0909090b180102030601090320090c09040f0218010c030c050d0207090f020306031c0c08030108030307030b0315010311010509090711010c031a 76
    0x2034808450103020032180b030006890ba840090203000e45417008103050404404001444842e24001b0800c0c0c1c3e00e040040ea1003550109180c00050140050604603000c520b000b16820702e089e40000d01c0c4c0707504000383c034130030440d24503200d62041034200d000c0ca01da1912620b02d90b090780b10503610240040e0308180b0920106900c500e041c8500c2d0310324030404200c01c1030900429051002102c819000c590081000d080e982082c0c011502500b2442c041180b0701990708035181444015106428108560b215560302054000c22000300319680007011103880d4040004000e40e134480c14010048401d00308101000040d0b111300039030340112401009410304030b42c110070301d400c2904103002032400c0005403106040480e5400c00110701130245e60000e0360f0740b46441034001d0140c52141c03010780c1c0a603100c1c681e000141e042c0f00c0209415280c0c004031010001d2400e0700122094007501207803690186101081c03101d6a50032010b040d46000085009100341408500140c0c2201c2d00c0d4100411f80c2220214071050902c0c000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 92299937 1250 92298687 92298697
    0x10b070b070908121b0f06070210060f03140307170c0c0a240504090905010b0909070605030a0902040204091407020c060f120c0f04030f1a040f08090d020603090115090c05040506 78
    0x210f02120003110000020f4a4420800154401131f0080418008a82d5051010a14210400300d00b4081e0500d007000c042d9911000784009440741301201c43c520340349003040c01215a4a9000750301c2e0384014001d401a41055230100d4009002445140000701441c20a0340c103400866001050580021001849030031403205454082001c00404100100300b0241c1c521a5055042c000c9000080e811103041c1800740707402001c2c00045180d0b22049040150b035502c10220b0358442110b00002c41c00c0003203440490041d0056801c038500c4c1904244003445120701103460b0703e00c11030590f42121014407481050140500c02c04228040c01d10307040024207403e14035019619000005580c2440c5401900b40ba10409600703ea0400ca40703030f0305501814003d1124001c40f460f801100980880c0007820142da800076888054940146a10340100b181001595000c0c50a1407140d0064100c9660f407400307071102c1d4024615400c00302984204184c000c00c020b8228460032907000000d495a910f8141800d04008040c3c200c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 92301187 1250 92299937 92299957
    0x60507030c060b12070801270320010c1101150e0a0207170403060912020c01050a0e0303120a050711010b0d0b090f0d03020301050f060a0c02131103010b070b07090812 73
    0x103902c2e1401644e25002c0c81ca44000c449000a0002541400c100509644030441540c000b0700302044a09248010910013520007a498204280684a0560f420060303107059200400154a0003d04801c020781215210300f008407858000c111459804e102aa032124050240d005003050560005d46c04150176030042001c14041d81c1919600c410301050040b0661141c0c0040700e4058540362002c040000c6500c100d00035110301d002030f1110f240f0000000f041405401c0840d0300b0440c000e400121030f40c5050040301c454802802c41d0420b246070142454024003029900500000e80051903480c0d880c3d418800c3d50070104c0b0041944803030300405d40b106000030a010703101d0107050090f116881b00030a010000407003e510151800750f01da48c5400c080000050700b82403094010501044a1001107070b101c4480049141c0c12620504c0c1032150861030b03001824060b146200d0000000000708030784540310007403c0c0062007407880346e01c660354075001102c1c850054407641e08190f0040c2d00341418100c130710707000d0240514 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 92302437 1250 92301187 92301191
    0x1021903030513020303031806060a080c04020304080c0d0918060f0e0912160b0c0405061c0209030a0f0c05061e03091005070815090c0901031104030c0e010e06030601060507030c06 79
    0x83c0a40000b41181e10660b0403a078034225146104a0075a000e000e030f1079000740304540d211000f80c50f12008549a90000e08510311460303001000504101844096581c03078880c0004807181d001d14820054101031041c010402114180f10b1041684074031806003100340d0b807610241460040c03410207600d0310046e016150042601a13140ca0303d01c00d02c049006000300c0f01e5081c5440d15546e5090a22017111100541034403c44401000140090348402c0c044800c00220005008101d03000109804028011445202e5050041c4110b08090007801c100c8441c030305014500106890740d5030020812540700310356050b043d141204d0074040c6043c0142d4080c50b80990544181d441d0300345031a140c1c00840c0c1e0210f91000104081c00207002c00303c1030785202001d81560954847c1c00b14204401d10520314047c10308494101512060074402803054181502c0007180c0c04014036880d9601ca40004441000c02d000340e070a2100c1080c001a924500040c02d18100d90700c1d9100d0a00d00103250714200d4110101c0030090310034907 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 92303687 1250 92302437 92302471
    0xa06090507020a0602250c0e220f031806050409050a020313021306090906020a02061b0904091112070e0c0a0801030209041a10060311130b030702070312030515010219030305 76
    0x181040c046c2c850320391248503661004c6003080607180e803ca0300030300102174285480a40003003c0203a9155008410f0b080040004242c0359481c085510201442200d0790b0070680130000039003e41c12070060419a40780407010f000c0c5540c1c41c103819080340030860342800528a880895009400c10011100d58000341c240c1c0451841c0d01c5094180a4848071681150955400201c401c0041c0d07042c03002ca43c0085003a1091240004c071442600d96500031511102d01c110b641b140001d0800004480c004d600c00d030058403080300c05100c54a102d80300d0000e842804901c440210000d00b159042c0012280c10074641d8690b0702c0c0707603403d42d028030403240c400420807203411111100c60071582400c61b80841c440c0b105c84009149481c1004d4005090791131840d400f43d4002420300c29626410b4005803000c054034003001c5626141c1c0d0b20342201700e2408040740c1c4080c100444400301c2080d280d40c59046a8407a00e0b0398449901c2c1c061846d401280e8810011704188090f204202d210b0000920030341015402c10700c0400380160034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 92304937 1250 92303687 92303737
    0x1a030709090510050c12090a120c0b040813051503091603050d0e0103090503071202070501030209060f0c010b090406060509010518160311040e010509131e06090f0b0a06090507020a0602 81
    0x10100031f50703c03003e070b82c5e010303540c1e0030100484900c86051140d154079280074440c4c0544e4404071041b1014100031b10f40311000c01da00c3c8181d100c40412100500e8024500c0100c500800004449035005a47c000b40b0b60290404411000708408401c60459610000410740c0c5040d9140031150320400b016200e0405485a440da4042001000504811400b40b00e520b42e10b0303403041030068a81000c55004a041c54018088020190b076041d00703513807085207501384103a661003142829500404c01044003030b51002d10740b0280820301c08661b220030162081a50003c030242d0300c0301e00304000d0740e12074500036915442100004505140010413101806c2d0399060200c1c00103040c1284691540040c1c0203448401020001000140f80000285401181d85000c1c1a260a8039031100c4011400040689101150000c9450100200b60340442c02c00d9410414600c440c01c031902c0c01c0c803909c80084d910030a6181c1046404207080350144140341c01401c0c56001419141000c1d070360316000e9044003107021400703c00c107511034900c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 92306187 1250 92304937 92304967
    0x9090c0c07030b1e07020106050109031103030d0203100306050604020f0405120a080307050c070b04030503121009020313030f0905030c0d02061308030417030a0f050d0b03011a030709090510050c 85
    0x719003030034054584068134118502620001080881103a06040f4100200d0740c100381464140d941081d81410515110400b02e0701d07510030300c03119080d540c0c4004100305101404858410035a40310341414845503c415040000b82e002d12485021588010001085a4074240c00d080c4010081303401650b80004550f2200c0016070411600c002c0841c5000486402c18402400008003521540c02130504290540d100c0c80d03030740c2c0250a501a81d1603e0040440c00c1c01031148103081c01060ac04d14203542d2460580346409046040e910220003103040020000c880c5270040020f2400e60720040c0c01401264594410840014050802680c01c550208400c500c0c4080002850014080b0b500013180d0f43da19100380c003c11a60b650100800b42c0c3c10034000002d01ca54072214407001c02c40c40e032500a44810380c03044800010042107903400e03855841c182d41c2d8600162811540b00050008900342c038920340da00e64107279040d41c2a440008080b5007080104e41c0c0200441e51046401000201415040000300440c00c4c81e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 92307437 1250 92306187 92306191
    0x915110604110102011404080703030c1e0302090f011d10050904020d0501030302150709090f0e19031209030206010b0a05040302120a020306070306120201030f0b060a05030411010509090c0c07030b 86
    0x100e507040b04404240c070303503024041c04010142c40c2e200c80c101d500d003a813921802405151401001c154860241c04100751040c81c250140710203c0100741541e80340164050004d62146012034001da0348034036088001d60040050700340304060500a2000d8068550800c8265001c1d41c84810500c607050120038401d4a0340c0c40034000d00840c07518005420350540c28041d2510303800405590b1141036004c10440041d501000803011201d80385004500e900d40c01280001914244140c00942d03c20603021a5180d0b045042000d411400390f140c4112026202c29188240c2ea40c0f0100540941c2c4504010400710a94100a01c3c0003000f600e07000303041c15225400201c00350002100c2103980c0e031081c0498001d51034244501e80e040030880c1820007909107000f4601611000351030b006414035583e03000310030b90b41c190754002e25002d44d0002c0003903650711f11009002e80340e5007058406440c02100d5001e5000e09500410071280d1400004101d20b40c3d81d81c44002d80403503580308040052441c016100d000000444400710304d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 92308687 1250 92307437 92307443
    0x20a02190c0b040b0c010b0d050312070e0d08090a0b0405030a1b031b090f09210306170a0606120c050d060207120e09070206072712060903020607030506010915110604 73
    0x45da120001030500d429550b0491030148200741103200c190000b00000300722148480404540c51030f6a44d501410741c0d044190304400368102c0a802d030003608000303001c40107016501044900ca0603440d110100042c0a000b00d0003200c0d0582d1241a290000c1850600c0c203108035890b04804455130780d2a5070700d252170841070f58103100070003c0c0442c1c10b01000f40940683d02c0c4280821004100100c1d99458410009500319000ea5954002a204880a5102e504180060700b0092942080000f4005610b503548017108010717564189400c0c80414000b0505070700740d038290380010f01e002d051401c0c01d003006150343c090141161001c1c1e0070040c040000d210707010700320400344954899149004000040c4180702600411110454000e2820010b46503080440061882000c500721801d0300c56040000e22a10031581002c04030400d200c03c000d003041010380110a50520030390a03160380b600d6654040d0306171041030351841c0c04100d80b410240249000601d00c0054501c0c2403130089002d40c80980802c0c200b1000741c90a0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 92309937 1250 92308687 92308709
    0xc030602070b130b010501050c03190206072c10090f14041b0c0b0709050d14071521090204020d1b020a0302101d0706030c02010c03020a02190c0b04 65
    0x8505100e80e074100168001030407901c0348183e140a585210700890b05024070b07030500c8004607415644880c200203172840301c0d04480c5a14000068010040d5544c0c80071aa250001451207c1e00d459000e906034544120131304410841008401d448100620500b061784d1800030001451000108051040401c00007405000c6c030011506041a01b40016a12016425070302d09040380905011503a000b440d81108603008240740100351510b000031200c1150355446140c1c80b0201d64840701c04c2c00b0040240241440101c02294500d598036183e980100120301c141c00041a1683d9000002c0b446880780300e000702008141c0040c03404c441d039001504a8100302044000d5681d00e59400001c8545040703841c003541054002410b0001081d03074025903841c03c01c8400d9040325143c600004a07a04100440b001141e110002e403034406e42c8856008004007601101d4500541c20001d84d0045180641300f1070350341000c01d0380582520318615a0051403d00c003104202c82c04410000c00041d6000114058009400ea407500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 92311187 1250 92309937 92309947
    0x1e010e09070f0305150d15110a0905040f060501140306180f060109081c12090203070305060f010e070806040e100f02090f031612050c101101142703070c030602 70
    0x1001c6442c02031100032211703924010140703643e4a01741c0d0030b05070a47c0911110303564140103003248090811180a522400400f00b04800902d070810380a2040e00d0081e1230421a070000d001c00c00c01074038020b124140c0401c2003120301040280d80000115800000542130080a81305030024546c01d0758102c403002401074102c0e080c04074560b4030100c0080141404070040460200010b1080005840644090b0521100341030040303000c0c6068000d0302081b60002c040e104000d907a41805501c501040380e07040e4809918000202d100d01d00030b442240540581d60301d074140c40e501d0109102c002d25150b03d0107042c41c42114440790a1504030b02035580c41c90348800015840352144001d1040244201d10b00301e110303401510320320001018a04200301180c521403156544011241442c0c1e04141287c1c000079042641f90343d085081076042840d1071406007554001308078805200d00000d9101c0b60075600aa0007135402078080f02072095004100c210000740d0740c03c0e41e140c2091503907280c1e11307542c50b6481101e640e90040f076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 92312437 1250 92311187 92311217
    0xe0403031e0b100f02030f0c0f011103040201120e06131406150a0b091c020a0306060f0e010b0304030804060c090b070f17030c0a140d051005030f0c1e010e0907 70
    0x2044051032016040a00403240c2520300603440303005a1400c3c04003242e01040300000803100b0001c01d42c000801c8000bc00020503c80000b1800340d004441c01d0340420750f00700c2c03940c00304003080c41143e070381e803916401410382500c0701e0702500c51504000c0d07000d5032400c0b40c0815100205006200c56030140d1b8205009c000c1c51400c0740d0901c0000b01f42540003500c070701c2d0b062050041c01c0d118500d0031401080d0801c4900c19102d154400180b08410903000540a140380080204007102c441c6101c01c181c4811b030400300e9150780d8410414400f803108847c000d0014000c2c40116000030180e811032110750016003045c90310035441d0f03115000560040300342601c010741182c0580051100e001c0348242050321220010b480c528140ea0000d03080d1055080c480e00704803400072101d5000300c140059825080100000f0b12090420014004c0c860703500e4083e0f0742c400e020f02c182818030341c480040c2c007110600c4050110b240240d1808180c66442030304050140c103025401030a031303400f0f0381d5420b41e01d0700c100080d403200711104107030721 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 92313687 1250 92312437 92312449
    0x1006030201140405030a0b060604030c090e0106090c021f02160812060901030c1e0510020a020a061d040f09050d020706030c02030702150d0603080d090318030c0e0403031e0b 76
    0x150585018000402044c030503610f01185c0c501a0315000740c0301820741e85590300410018400c1d580060702501d4081000301d503280b035a41085565080d1070340240601a120a0528210ba00900c4100090792141445551500c4920b61051044002c10801420030003100900c44803204500000c0324003600009000321800d4400201c1e41d04848103860f2210b456056031749088004929004c1c901d0206406841000c00d10031050039000603140282042000c01d00709140a03640b24500d5504030311800c0401c1c404038000703218514104240f15100c607040014240c203000c0c0001004070201404802d51204441030114108002031800156590300500d4034030310b8200001c1c02c0b604c9001c01c01d021500704001213005681c55213403c80302c1460441c0c200350f4030801180803e00605456000400d4404041012800744489030b002d01800c9010340c5a0b00c0e886c440700400089400c0143c00000c0419802040a0020aa8108215500c1842403d000541c11280440c4c10f4071581e14070080401980c0320f0400c960303503081c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 92314937 1250 92313687 92313707
    0x201030e03030f0f040503091905040c0e060313020a0905070c020901060e0f040b1909060f122d170a0e040209090105010305060d06020c0d0e0a150302030403050702031006030201 78
    0xc0c0107141503080c8062484680741024011916000344c51002c41e0a10074140211450040001c1010162001e181801c001008152082030702c20341c641417036054420301800c95040100070050040389940d8410b180d901c03030701d1030345082030f40c00161003007010940d2501407003150300540e21a1119030392085240304000915a0507041081042440d040f174040c00c1c1c0301c00b0102c5214600455011540d020b500d00468060040c141511001c1e03e83c0f44800285404554000c00c00e0b07405502400e9001c0e81c540c0d8802001030714203000140303203802c100e5190040700c15030040300c846100f903c0d904000d1010152a00403041d854503103160700c03000000481c00c15290b0491002840701c101503400b0350402002d5000110010014401c0505064407400020305a44e00c190b0980ca0b21940700c68110340301c0f00480c00465131002d0096054001c910501d1500f00245010442c0204907441c0b20b850b14207458681d18101c010b500b029104400f40042402a540107980c288448040c102c20144000758103451400018408100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 92316187 1250 92314937 92314961
    0x5121501030803073c051e07060f090f05010b010e010503060907030b03030f0a0e18060d06020c030d0603060e030712230a08090c041506141b071d0f0109050a1104090207020103 77
    0x200f01f0001c6102191030058040c45111070103400d455007064102a4054a8544050302c0c00038640b0b0600c404001c120a03000308180c0c0910300030042044100b0054a1100c00031400901148090000070708900e0701101c0d41e41e00041a02d404160407005a002c686590410420145640c41c0450300c00030250788144c2021010030115011408096000c0520b01d0014002c0e10f4203000307143c6e45103440e0034401036804458400803c1001c89a9030481c411502c8001c11843c08210f81c00d50400142c5544013000200359895550411a82c0e500244c8141c030588100040360728410040d5400380a44440c120f440b0f0103000700c400191942d403c00d00c2c00c15522802c207181110395911a80c60011214034914181c6854000e4800300e09080801c0207000b03c080e4024085e0840616111104120349240a400814000210f038048010706060079000d280b02184440100c0d40e038907805959000400c5282c4c41a0402500181520000201d26101640418440d40144c0100150320b4001441804559142c4110b441c0050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 92317437 1250 92316187 92316197
    0x30a020f011a0607020d0b100302090609010b0f0d0b10090314010e03090402092805090906071718010c080129070201050901110a0302060105121501030803073c 70
    0x548003403000714015400c2c6900c0d0050b03402007210700842d120785c2c81c0e80658a0300080c09940528010310110405906804101d0040b100c400c08114541070034040c04e4141c070f8400c2102810407818076011046078002001c0200c181d0f84030191102c46d41c0b03422480ca01018202e40c2c5104405003542400a1002807a01804045a16190200c4213602c00842038072207900d811170340580c0d5120818005107403211208e049803903125010712007100800c5c0140b0b60760201c1e003040d100c4a1a696409003419200c540884404021036070941820403091307880720406500450040c1c02e0711114035090700032421960020040e4007c1000da000500c00d4110a4800e600d80d010b80e21442544101268800100d038050204003c0c141315004c216000c2c643c0c040c540711070b00000000d04499100d2600d0400075134542c03081c03160724010301071807560380031162020404040811000844d020607910b1075845c3c0074140d00080020040044213107000600340401c1c1c402c428400d00d040228104151008400d0341e445066500301c0c0c05000e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 92318687 1250 92317437 92317451
    0x6020d06050126090705090c0a080f0c070b070903050d02010902030c0607170c120f07060b010306080c0d0203031c09020a050a03030210050417040e150406120605060a0f08030a020f01 80
    0x401454900340c260401c00000c25080c0c46400c90b881c17134a907042d0070960740001050100031900010384044d000780d00e42d90f030b01c01d80940c4895030400601102a80c0d0001c04400800c00304000c60080320030303560030040506d81004525981d403074041c03c040d680008100140d4485d60301c1e80940c81c0c20080b9940c40d00044071054a4401190b0304c4010740d451074010540c90010214035402482c9050205071110500040701c29950403215900c080181e10544080300c182e4a02034100c0125482031045d4419241513000408400d03c4040c00c1194030100c1e071508a0389403104026054004110921035000d1052101010822290381d1040007101d4015801180c080c1403100800c0011990004c4d00d540c181295010014003278485041680c0e800034407030501311500342c000600066110800111521800c142844440302e81071602c208000d171110b5100e003030f900320154151000482c3e03459001c240c0040000303203c001c20668070444940311042c158011640c0b03400214004051540610101c80c0d8401000003c0000c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 92319937 1250 92318687 92318717
    0x80c010203091903050a0b0901050f150409060f1109030705030c09011e0302100905030105061008070e010e0904060912020303040b131406010906150207030807030c0c03060906020d060501 82
    0x10740582c5200c01c0c450110940c4251a0010036030600300030310341010a40b03e050340c03181800d8050b003e0070b440e010040d6281400182800400c1d50220f80100e804502c01d40300c55007410f0800001d0101550300340e5401e6560b07111080c480141344141401611002079003902d42d12200100360500c210359020710300940100b044003825030307079002d0514152040400040c1300c99004102c00800d90486800080d00212964000c20920307403c8003d103c100c4004400a01066654400384103100344910108d00c00300e1000c6021800321409601d482d070b51100b040c54162003a41aa100142c10454150b400f511869521080b01c801c0c40fa8500c2c0804454026000842c5142031668079540c021b0301c010001d2800f5103504203140108031131000c00f1006030500c14100c0e4144d50711807940c0c038001d02c0380d8424a81116001c19107064000c0c0080b03150803c607a00030028609045141e00d00761201d80d072a410483c0e00c0600001301100081841c41480d05040c011500141c540c0303e9800c0c8001200c005422403418059100c8041c0c506d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 92321187 1250 92319937 92319943
    0x108010e12030c070b0c0d0e100605100f030506010203091c05150907090f091209060906141914030903070c0f0b030a0921110d030606050315062a010501080c0102 71
    0x26603101c000450301b5619107103254614081c0195002c40303107003803070344d01c81070380300c0010315036580d454194000c000050391081004041d62000c070f14a03003c00c01081e4810301d00b0b4040e070311080d88104180166485c0085078800030305008580a03401d014407024405203410300c2400c0002c4d0f40d90710180c0604900344c2c140688240d69881d0349103e000b000c0d58440d88e01084d241604e40000c008540d1184d0300c4110004104409420707642d96000382c0f0006400c0c0040001c000d8892095030170260034180d00b4a250101d840083d00e11481404584014400301400046203410071000130b611502603003000e96142c017a580307840c034080c0c6100d40c802d081100b0080f0041c003884c070914003142c0e000026000c00051140b11443c9c0381c0d0302e0b2005000319000482000403c551030315002120207040088450a44002016a02c0b040c1d049880b1401108005141840007840414195482a09904008015908240c07070039402204000c2c0310a02d46911048181d1468440442405501d01501c1800040c052031407800740000d507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 92322437 1250 92321187 92321197
    0x10181703130602072105030405090f070f0e0d02010305060a03080a020d031a09010905070c080307030605010806040509190f0c090903020c01020601270f0f0203040201080709060c0f05010b04050108010e12030c 91
    0x2480404410380c45c0108641003080314000c000c040c10f03c2440d4603215040c00a002021a21800800d42494201d11468800c08001c080118028021103001f00d1a030011001454010521504481014400300200f207070500500140041540280000300036200001d068503401140304440c40d00380c0440b08041e03074600b2006d43c1510107105001660743d507956002c4030141c244010140c004000002400411503054000342d041e108282c0300c0d040c1507140c02081c48100da60440e40c4903010781224a2074030001030200315001145000d29059041800c043d266100791841c00c0c1e000d04081179450041c081059018000060010b1090019240940c5030408001d4808012542440c80005201540082c65016800840319242d40141080703204c840c1882c1130b00952080d14140d012540c4c142c0011503141c420340451040d5030b155078841d683c249007941d807000030710f070000800c581035501d0707220150180d11a40302d00d9000300410400812802180c100d650309121000e00c3c140d6948008104200300181002c0c11a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 92323687 1250 92322437 92322479
    0x1051b04080604030f0519030b1806060403080307020f030409140a09050601140105130f03060b060c1203100312020d11010209090c07050c130b0a050402091018170313060207 76
    0x1502149140c000702c6c1c0500c541d00070301c20030781e101c007016000b007988c560312038803c0000c161040440c0560b1442c111500210803141a90300800810051000401000c00f070340d0400421300480c1d080805007000241141c000d508070f103c0282c2e0301e900300a81c51074151607694004840a50401c03c4918a4450a80754601402401c80c544803400712407109901c500101c480d69020b0300000c00c0f00c151106201c144000c0d07584020f4a6850800102c2002d07460b01008aa034411204401000d41134200f00d00c0050300d400007420480d5080444000001103180c00d03050322180c10a90f17002d40341588040c0b10203009061701410f50801a0310500958040d42c1f42e03202001c0d080101d80412036124001ca142c0b40e0324211a440070207401002d482c0c1c015011603050b8000c02841c20b4122100c0a400da22081400308a0142c3c00059902000300001c20b04054000c4900c1840c50206a02e13041c103454070f40c3c416402d0500214502c1140758800291412100b4620000a01414261002e0b04507a0701e048130810344124185510 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 92324937 1250 92323687 92323697
    0x3150301380105270306091504030c03050405060408030a0305070807020c19091e0c0201110405060d0906020a05090a050f03060f0c12040807030e0405040c090c02030f0c01051b0408060403 82
    0x2400c0140c1c0030b0030a58500c1241c0d41055104895924810400441d2204140d4001c1c1b041c0c0010070302440c0c01040c81d541962170785051042c150350f1034400301c40c060400c000c1030b0f0500100304004502510f60000900150280900460b582e006c1c3e00c40040446a00816090404c1040c0050000203503010035820800741c1d04031060402ca40c4000807540a00c0e91030f9004400c2107140c2024114000202041e610f103a140d440802c11464072402c506070309031407416002c8e44a4542c1048180700f1854028050003d81e1502c0c640010300c65010f642c2e002c2240d018030f40780743c0410004101400c980c9803000c1140082c00095a80c00054005580800e131384000207041c180d045200a40041d109400a10076140c0b408001043c2221038101802d102c00b0650042500741c000695036100e181c02c0d1704045c0282801164030403d00d4021501c0c140512008001c00b000700b6046000130400c03500c400f0b03c604003410a00e4071510001525042200b000c00301c142c0c0311518001e09080a01042020310310208219500c03030340509003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 92326187 1250 92324937 92325041
    0xa0e19150203161205070806100c06050709091109092205160303030501080f1c0203090603152d06070218180c01092306040b03150301 59
    0x3000462030488000d001244040200b1401480160041d00012910307100d01068907848a80d08058500466150001c24541c5002c00d05504052040003403240745860030001e09503441e542d039030039201c0507643d00d800102c2c6644c00b0f0091044501c600d4050015071040640b0706569080429080a0008c0c02c5010720314842c510040c502030b02c59004414a45e01c1010b903207004402000902902910f40016400203250600202e450310740014541c04501c82d42c00200041401000c236509030141040419046020601c04454603440c0c0c100598090380c110365640044650810910261461104070b58100016481c0c0100388441c810359240036525068800135540c8800b0f001044c000385032048190301c1001c00108211900708c8141f8101e0341c090040d020b480c0001c40c40c3c001100c00b41a1030103010151250500051012010040020781c104400380082e4105a82c601c03c175101d9400842c0c522000c000d4007100d24074140760038400c9002096264000002c8001184440d0201c09000c031040c20b072441317180403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 92327437 1250 92326187 92326193
    0x20a050405090901020c1501030b150102031c02030a0f050606030705031003020d030201240b091e03031306020106060207060e0904151d01050115051903020702060409060303080a0e19 80
    0x100315405044050700b44102c40c2000b141c82c0d03000350f0000c644081503020b980700003950380f0b41c401500c5040301d4010041c040140c540030f01e44401289201e1910381944004c100c03035050182680a0658458400040181c43e49081440002030717801c0d0150030503d41d1300d00420400c0584e00c0a055a402801d80e140c5179460341d444032a034030305008141e00041d50000520f01e80104041e41500038050700c0b080c1d81c20200d20010b00b4242d21030800f201d4024400042ea090220600038103107800b00300400707060000c9600d030725540d80d0082030840d88035001005002e034400d2030a0180d01d409000e00c1c001001544010100706161070030007409a950b050310310780f1035074030311000c2018401c0d1045c109814148401c41002070b108050858070b581d00841103141c3c01e0b94240750000070700c1c44218250000842540c0c03034140c80c14500c81c80c2d10303004c044442c2c188801d0642c01d01403403025840e060090b00241000000c0010340c642142005410080f00a0a4141c21030400990120340b1201040e06004a225201c11458105880c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 92328687 1250 92327437 92327447
    0x109051c12060906060e180a0902032503021503010b030a02070f02041e06122012070e040b2406130317030a0606050c15060109030b070806010207050a0e0109020a 71
    0x62035102000b030400320040f905a03100d911400460b03010391150840c403200d02041c417010100400c074990a80a0203000100036400d00d4212204140c80141540e0040d10846144905042c4c5441c03054044031103080c050085003441400034000d008442c01050031585421403102c0316100c01004c10041d40c1e008200700b020010410102125507034001c000f4480601014040d110034420780702c43c540b013103090910001d0200c00800440c0602e941041660205413404031015201c00d003c3c10b1415003180725032841042c03085050051401524401300c41a1440c00c043c2000006184040d000c44e141c10038803000451110b80f28a901030f400d0b00c0907184181c81e0000e107c00520009080d5001904928104c003440d0381c18100340d001148a1000c01c1d2003085015202c1100700c589015001c81c00364958824054020401103005030146e00840c14500340840340e481341d880c100d08000540d108404544c0d64000d01c001c0e0768062100001034042600d0510840d460407803541c40428041c0300700301110b640010790401003072040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 92329937 1250 92328687 92328707
    0x120c0604020f04021b0d030609060b03010515040807080a0b0709080d0309080405040c0207050909070b07080304060902060d15050909030a2003040324110f0901030e060717090109051c 80
    0x15500c0000c49080c0d440301501c1b0f0300c0c5031743c407040000e29002c8046900307412846030109a0b900c0c82a0181103a00707010901100c6d0301e500f904042080b000703100010309400c04000701d80140401d4000342000d4003403440c05188a0002a280d90284000c0e02c0043c0003980000541c0d8010200f41e1030042106036542c2411001e510960300007035046400d02140803042a00002e4160440c0c4041e00e480603165141c503102c80c3c407080f81e8022000c02040400010004c58060300195420600a100005480e00d460340003a04c5540402e0b0703202c036070a488100b94110309101241c03075001080e00395484501c41c505007882d25103a1251088402c140511800c800b107090381400c40b0380c009882e012045030350b03642e02e90030a401007441c492140342c0490a0109600c400340b02e140691b03544903801990041c10b00740400c0920003203401c104481c50416550308243d80340d1641c00c0103054001e4081e07842d6102d01048400b400c5640341c0c0c000300600c9103a8148110003001681c0060384e6407404d02d5021124065405640d01101c4250321 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 92331187 1250 92329937 92329957
    0x319030c0908070807181104120309090203010e01091a03120a0903320d02070510020c040603060c03110f07060b01110102030a1a01020a0c09020f0d090f0203120c0604020f0402 77
    0x6000800704042400162800a50304070201b80c90295005051000640785c0c1401e030380803555400c1c0400c22181009904510b0168800c0c141000308a490b903000c442281c009901000c0d5040a84004009440203403040380ca5803001008404030400300040032a075240e041e00c4102030f44080000307103000d143c1d120384002d00145500007220381c24040101d00203070301564000071024100b0032250076501304510015150b1240d00c401d8026100031490700c5c0420202070380003c8020f040d80100d008503a22540c4500c21400a14803e0b42c0c0003a03542882c40d4024203d50024040c0e801214040220390a2074010380251a860781e07000502064801c404001203480c0366026002c01607070360000c81807000046030b030f401844182100402141018011900499460445036000351900c0100d50091104981640007010001a494030032450300691030881c3c81114400d41080e61014440501802149001c3c00080d060704030130100b050800f407a08547d5a21600c3c041d10092060000b10360500c03e83c0c803160141c0e03208e070300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 92332437 1250 92331187 92331193
    0x3200306010e04060e06100306020714030a0216060516020603072f0c1005120604230603060109020301080d0f1b03030b0907030507020714030c12030a110319030c0908 73
    0x696501e50041e610302c182c90490319182480c420240c0b034800054824451640c210398000190300d181c45003802540308450a44104a0358244000c0c880c40030402421028010b600810150400c511a0341046800e074006800b0000c0402c213020f440100e000303a00c118550129407042da00d844014041e0f41c1034102c103900b0f00c0101101d44501041d141d900d14480540c1114000391020700c001e4008200000200d03003804008510b0502c0141b030204089207189501a202400c002010030000c41c4c54180005c0c01e03600751f40301075008001c0021604040c0001401000b42000c1035046505181b02d1603125290084200c040284103801c1245041c403802d08841c880482c035107071452500319800c0080103029048042d50040c5c6542021039040c0d842413040c18417480041e1302070100742d4104200181030ba000c0e040301a40c9845220910480b070340d521088102070101040003590340c2d00401c10058540600240c5003c00d0f500140310090007406007800c040d600341030900d40015450545103058030311060360f4201d40d51900c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 92333687 1250 92332437 92332439
    0x1e04080a0803040506010f031703091203010b071a16051e040f060e01020d021b0a091d07080705030705091f03030201060504110306030a0305070c03120801031a0405070320030601 78
    0x81c0c900000c5019500a80907290300d60388510000d13001350010311004101e1085140c640060007000b40c05150008807210030b41d40d0100e4140c52016542e002038014035020307540042d040e0704008119150f140000003200c5038040d02e1504e0000d40c403203006200120710600000003041c00e23039113865000300340c07606060040b100c0c4ca6588500525910032424024000407482c2400c41c942950700008020b0320481c10b9a004001d9103109962042c189180012101c2e002002840003142e504201e00400c240c2068007500c0c0c1c1e03407880315450840d1a00f90194003100003074000b0b450134029907d001c19101d0640344291158a0652541414038079000314a01900340d450180103004010150f0640083c01102c508032018412443c4046030041144403c1e0303452035055025111a00000740501d014121085c0241101c90341c141e43c9494114480c00c6001004d0005401580140308114142c0817000440c00060080006407400b0759640f60740d0841400086d0140301201c40100040c40c2e40212020921005810388284e9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 92334937 1250 92333687 92333693
    0x10507210903031103070213020c030408030309011a01182303011409070f0509060904030c050d0201060821030708090106050a03050a110306060303070b04060b040e0303040204060605030c1e04080a 86
    0x71000e103000403800070340b4000c0790600f042400000e5030100c0d90010803840c18075904d50000402036024880c21103040c0410f0200060811083c03000d10b206190303480000c00d44003003020040c02c0038040010250306012940070041710101c0c05106110645000004001c140c51180300e207100102350101c5c0c140c0d032540c05c1c03c8018003054030000c3c4d024021007418045400752600c804845101d47c0890041a405c026060009582031800c4070440750050b0184c01c00700d190825548406003400068266403001d80e444950030400b01004011a03000809488521204004c02c1e2402220b50302c800ba110000b00810403020421006080d03200350002d1800a0258951075503a1038217a4450008110a580760101c001d8880280c0c100413454522941000b0007551900c442951a402c1c400c20150040d56440c1c0e5a840e0034103030752038520a003254030f02c00e14002d6849242c907104000c00d54543e501702c1002c00909100f8801c0c2180d80740181e82c0310410b03a44500c19080c0e85200c1d0369049010b82d5100000a2050303076224024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 92336187 1250 92334937 92334947
    0x1e0e040605060406050d0e1c0c230312130c0e1b090f0d0302070b0408010b09090d021c12021c0b04141b1309020403171801051809042f0a0501050721 65
    0x388510030510a25448000101002070b2810810048542d42033000501c00035050700803016400029042110751001c52030326620200b40c003d401000300400500e0a000200d500b41080c11611800a0307007291402040c14046036400744000510390045640b034408208043c02800080701600001c1c0130a910303550358500c0303540607200c0c00d00d42e14043c0b4580700214250342c2c03000c80c2d03103802e29070690014600306191800c6400c0e0742414211400070030500d100c410074005070074002418110f4078440d2000043e05040c004500b01c60b032030550345120703030320300300b046003a4414007140700d40c0c8038110480c00c081e110711010201e040e901c07610104d840007000070130000c6406002540079000b0b60740121002040800001c0c0010320354032805101c80c0c038015005108851540c460b10003030008442613407507480d80e07910400203e1800c5805840460300300c41174001050200c004107020081180346040c03282100e590100c045011610203000d0607040090004158091000020090030035145411510704004007404000748 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 92337437 1250 92336187 92336207
    0x12030501090b01020c0619140703020606041812080a0207021921240207080307030507030b1c1101020c100c06110405030c0f011e0e040605060406050d0e1c 68
    0x4a285400b40207910365100144500f50140017500092070500ca4044440301030b000d0b0080780c020080748901000150110703d000d403079003510a0b001006107080000400c000c1c0c842c184006000c51040010a1010515090340d40b0b000c0c01c2e4030700b008d14040e101c59445501a106415001e90401000002d080c4591142e4403548201c61701002c400000384455414966000d280c090701901107040490080e0207004891854015100491801441d1034800c0c1e551481940003140e03c0400300f035503181000021a0180074004403421f044444e60801c21800800704000815188040c2c00443c00c0505450386900810104d000340d04000c002c0350440007601c00042c0502c901500071250719081680c100c0c10700741c090b030a84040e500010302a040780c0c0c5010303082c40101d001e4a51a0303410441250880c001000c44021607180c10310403a901c000005240380144016500c1079484180207000810081000355409019140600d801020125000d51040707080307840d014460414550300f0701001c0d941e140064203c40307956 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 92338687 1250 92337437 92337449
    0x10f050d15080606100807081e0702030a020705061c05130501020301030807110d030f0503190f2403080313060f0219030f0b03070b070303060e010603140f010317030703020712030501 80
    0x5400ca0381c030b40d0244040400b012445d14007080014000c18000d5009000256200c00803d0148401c0921142ca820602101b40c0d512801340e080000c3d020035031603040c441c03080986800d984082c43c0402d00c5c1c103140f60160381c2c0100001160ba0761400301c0d212001c40c041c205c0c03806030070600075512540c4909014001e540030080c21950b8040c094546911802c1608101c0c03255909501c6400d0900d4520300305840d503901c010844200800c144623034154503280c2c0d203d241483e411400002a80d980441c08045072000c4400850401d04200720003000060750010889901000b01d04812070000c98a02c0c2000240c03c0980c14103000e907001103200e0320f01d44400c0c5191802103519607400d11100b92451803104c04c898030303820302c290141c01c080401e07c043d460080003000018803034034000400c06c0d5120030140000401780c000d44006900c4013030210b500b001c20000750360010030b145004c2000c0c1d4074680e200444000350001c0d98800443c04000900102d000b9419a110386030040714021074141c250000800a0809006503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 92339937 1250 92338687 92338693
    0x1060803120f0c04140111070905010609090911010c02011101020301030602090a0e061807020304090e060717010608010501230a08040b01090902011b020f0303070c060813050c010f050d1508 83
    0x2a10b50b038044202d1a0160095003110340c640f500702220707044440400e90042c2d05002060008884000307040014074010000083e00040d65410800000c0c00295150300030100706003446101404a250001000000385003402c0c00d2908240314030050326040c0100110081c154401300000050103040c0d001840b0252084940b6280d00743c40700c0003001089070030303624036800c00703410325401d100803031207800b00d90300039080780112810150f581011006441407002d031001c1035080002400035003a0000a80030f129010281c20f22003943c1440c500826000c01407182c281000501c00c400d5485410a000c140c0340e004128030015510003604901030241441a00c00300c856502c928000500d1030001d00c00d41400310b5050f9500c5860910414404007070b00c0c1d441405076072000c5000f025a8065034100024984240b00740b81c6c1c0d03080e151401c28080d10400005050090007800c0290645c005680451114503c00302400c3c404030030380c4800c8048400d03024015459202074508540740d18040b0840c81c035003046030030344021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 92341187 1250 92339937 92339941
    0x907080f010b07051b12070f150206040203120d0f1b181404050a020f0304050a110d02010e01030903030b210c030c010801031e050a06020a020114010e1609080106080312 74
    0x49030424410340c00c01802c0c5070020804074089178680708000039400c4004059038840d07842201c0890400049030b0000e849a500682c04200e1034144a000e1060740a95001400c450300e082c1c5c02207601c4081450701c99400060000361030a019840385c1c0030009128282104001201004410758040180001d41e80040fa14103840903005d01088003110b0103660190a01034031542162060001600e009000702d00215001e00c481c01031070b028903005d10f200b5401403004050005050901c410011103000c5c200d0700540ca20901000580d030000707140b0f414120207107400200c081031800d0482c0140310030005070764070000b90640c101c4400045480b46807410081420742d038000030548100740c0c4d24008400700a010550100040010a035024030751241d03c140c4a444110600752a81c070300d42450441d400c01c0721a07584c0480c45070701a95091003200007405c05055444641e50611880120f4010001d02840030f501841d088082c0c41c5200d5154100104084030003400f006481d0f0300015125002162950030000050300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 92342437 1250 92341187 92341199
    0x311010809121602031005070906110f12030901020d0504141b0a0501110a0803040804031202010c0c0210031404060603060c090f090207030e13060e0a0b0306150f0907080f01 76
    0x1804031045200c42ea00c192610300f0124820f201003680e12001d0740e00d070007000d131070003126417290192601c20380325980d406182c5810000040d0180300c0320089107034a94130000101511070b40000b036803030340c40b0015903102c0d071255294000e00d80603106030005400b10030304120902003040b241006d07800c2070300010020303513001c0d9006001c144603082c00d07000501e5101800c65001c01941d4050700d180600f4201d40402e0b580d0034416900c03504081d41c0280c4007100e040c100042e08105110040300e1400030300710700d44000d1041050303500c1d000307026603e5540c010740303e0f21104418543c1540203034002c0071112208041c15070240b400b400d0000040c00c1c2880141d0301d1030700300000340122901c60704154081e100034603010050707581021804c4000350001082102440540380c82100c0c0e03a40c0341c0c4580c1d001d0710581079010900601786282003e4200c00078010000c1141403202e290119a00403c24a42c040300c004200807008881c0300005108509503d40d0641100d54141440f060719801003c00744242c410300391120380e60f42e843c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 92343687 1250 92342437 92342443
    0x20405061b01050916260d05040f050405430c0b090105090604080d02090a120c0812070602030a022b050f060915010309052e090c0e0c0d060311010809 66
    0x2d030390042000c541c030340140096424140e24401000341c518585a200c5074002941c1c3c5882c000841f18808a480070a00300706082d031507112000580f50030f54081c80b141c102051807030071410355124005a962560b054441e910710041c54585401241c16020700101701046d071020384600321b40e04007030322030022160001705d00060501072140038200060090100c2d95a42e04c40100e0b0b5001341412002c40764007000364400d1583d44940c10390141c00040342901d0301b100e10b071900c40b404a00562080e00ccc07e401224480b000a80701000307a42c04941c100d500940c4d00e42d01c502e1244001e115941105400303000c801401c4590381c09503500c01881c1c0c0c076245070070002038a4800c00240716020480340c3c0f651150324800002d20402400e007015183c140c0c181000b00f0801480e030b45040c1400f202c41500500c2c6c08101d4100481000414480030401d01d160004218a000a844015110040c1d0203150000c0021401040c6008500001c8500b0012050020003d541c0c403031400a403040e07400c1c51034900003920301380404c00b091004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 92344937 1250 92343687 92343703
    0xa020904052d1504061d0709080c19030203011104080f0708030313030c0c06021c05160f02030717010501030605010902030603060619090501080f0f030703020604060f020405061b010509 81
    0x38142d610682e5150304061154240d00403c074140e62102403056100300d45440c0108130140c0301c03900312105074281d8031100d90b04a02004241001708910207204204136a400300740e0550119080d190b0413074410222407680d0603007030543d0009400d5031801c0240e866210008025209980c0c801e0282d071201700c5411001c60f500c1025000700c04e01130308104049407818101e4104209094400e04100800280540b0f40c400301d8081e44c0c3c07010000d6080b18201138600008a0440c5034141402e0620a003032400a40c0c0c40c6103145100500200414981c184c40c000399582000b0580061034103008900029a11051040c0a40000e1000300c0d801c908010010030716100700c0c02036901c06c50b00a8000d00e02c80d0b42d0001000760580341c01004d2440308184031004528414540100f41c041e000ba5001052a8040049403e1402038020f02c0150241c005101d84400254041000c0e03401c550081004602d000c89000184024400e9612003075004000003030420003846070080d0745d0907850088008100c60364400b907003d500c41d092 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 92346187 1250 92344937 92344981
    0x60a050a06121802040e0109062003060405091c09051305060d0f2d0c08070317090102011e05040201081b07150902060a0809060c0f090108041a0a02090405 68
    0x1e40041504044450343c004824002407400c1504244503540224086403844020700209944426203d01840841d0051744200100d500f03004180c5d0742c4508030003005000c0580414880c80c0c558011a000079010000c0510030707204110300451882010700044c0403102c242c8105400340f40d81802c181c00301c00907031148030f01c03a11020f0225000d01c98141e40e40340e040d0070014811200003000c00c0c10050419a000c00040203501a2014581c0f444500e04001c00b282c1608d61002d409640700d140c3c18800511941192010305040841d420b448440c0f0741d0040c2d01400741c5644440011561108111000c41c042d0400c50055000ba220400e0f5a00c40542003010032807004464880b6003010040e1a0019081700c940801c018030112000031600d031180d0029055500c8080300c000010201014080c1107401802801e41009140e491a840c15810210189050050204440c1440304040010b808e2110300342e80410001120003904280d4501044103400a4000d021000d000703078034002c00501403003648220311b42c2d9820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 92347437 1250 92346187 92346197
    0x6030e0304210203210c070b0306060a0c05070e04030f0e0405070219020d0219061101020c070303030c170c0406020c04060f0b0304020a24030e0c0a03020f01030207050f06060a050a06 80
    0xe000d10b0031040e40c0c0c0760107104a8241c458945c11400703849620134070452603191040c0d07155a03056060f111500d0002d094102d600d00c10740400520a0b16510342c02210948941c82c2000b10284003e81455801e01d062070340a0b84a0301464400c00040582c000850060154140c80301221801d20905101c00c48030126402e60160780201c802201c8010841d00449801d03100502104903080305a021840481801e0700b283d40c251942081402580e8010045a07940c168070030007142020505002903a81c0c0d511071001900389561100843e07030702e80c400c1180c603007084892285407509040c94200c0690f194894484c0c207006020706084007181d07142030300402c01116800006110003605041c0c1d01d0440b87c0c0064412a0311003412980000d0307941c1c1c0c0500221184030004419170882d41c0d07141e005004d403184900c814620742c101d0004540c0350b9130b07400840000d0384d8040d554031a01500c0500140d00911aa61000e130041c0f20321121036021010002d07a59114076410385811914550306e01c00c2c41260a1390f800b0f001d002c55 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 92348687 1250 92347437 92347469
    0x10e06030c0c01020705210f031314031207020c100210020a110f0c01030606050405130c0201020f0c060402100309030210051b07061a0306130206090d020907050406030e0304 76
    0x86081005180c001448498061400c52a400300c01c0c00c80e40140012030301030704a8055812041006071140d5201c089a00350186031000c03c030a0704044d03100007400011000341802e9410306003c86c041c003040fa00c90b0382508690361071036000c40300344121404907045001880f03000780c1a442070414510480c0e0441464004000900450721035001039040341412508015460342c1809028004110224a84503054050324034611464001425500740f60840802d04c00d00700400c1003c1c1e103803014a41c22034440300100241b60700030b4850490292140000121b105a0041082c0c400d48901003603190040b40f08460f64503d9404915042e0180e40c00c5207409409600050001c0d1140c4200340c00c000d511425040301c45c001341d020440c801d0700c981c201200551b41030b959618040d600380c7c2d01079144024480c04070010165481d0817006003aa00401b5500203000e45804200d44c0705e992112905540b015900604420756460a410000c2c4160494800d01d0000303414440e404100200120031102903615100200c9615 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 92349937 1250 92348687 92348689
    0xa0f0305130203071503140114010503070e120c03150906041e06060e011e141309080a0e0148060606020102030117010e0309040510091a130b010e 64
    0x81000a01c03020641c0e4a4a20050040c1c0d810b00000018140408201c10501400c1c2c074010b04444295940c55003500c003141c01808507040d440010101200c00b4a8011f0341c1e5541c0d1801114092619406c0d1a002101c0c11110b210030600412401e08594080c1c00300e6080c40c1c00380b90744452066050f50760b1030060308000082004200c44101042d12603803810840442c20302e4980d5440c0c125840c5510204506921000500c0180000a02a009541c03059a140c003c1c90030601d800707540c1240d40d1a4140701703902400c1b10191404c025000400001e80080a09443d0f50056001a222519501d040e070700007075201e8604100540310401c0804020100410001c22040f143d0030401c6400040290100460b201032030300d030002d4218050719000d0402c030303800541c0b25450b21400b01c081c00812103480b44030b6410301281c00180d0070000155410801c04036070201399a1610003491100980d5504030341402d90500d00d4280442d0601115880c440d43d099031080c004899401e8050100c801071020385002850f043d80c0c0c0016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 92351187 1250 92349937 92349941
    0x1050a050f150d05041a070207060f200a05190809010806010c020910050109050307060203030a05040201110d0e150304030f0804060e011d0708030306240d0603060f0608030a0f03 78
    0x611002804040c4641100e0411402d2074000302564a6140d869000b00810080d140b05080c0d01a090142212403e08040b4006502c0d20fa25005031230400564400c01c40b511840f500c02000aa5010010040a042140c050b81d4450030008015900f611442e09019004d000d0800c0b00011281c000310a039080c0540d40e4011966000054001810003004907050360150792140d5500e030103542000141010ba614080015110030203d40c0403d00c2500840c004101d03481e004001c4030307030003130302c40c0c000040e680e45500c010781d03e00003c80600303e45880740010070480b00e60010544c240740e2904944407429140f03602d90340401440b08460007800600e81030140d002160040e805e40b80c1162044d280461a80846180e00d82101c10000120f20100b02d50024200188014040000504141005140b45240c00000700e81903100c0b64011000c83e042c2c24a410380d001d40c1c4c400680d40d000103084410f002503030752414010701a0a000c1070580810b840d00d00c001914081c000103c2d22007002e241c503050440e40300c00400f80c3c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 92352437 1250 92351187 92351209
    0x2402070306021303020402040e1005040209030a030c050a0b0702070e0c092b0602030c120606071e260306030d0305090c010c06230f01060c030507080c0f0727020301050a05 75
    0x70810f09041010006a1b581d001034000b9013904d007101c210519014060003000410307540303c5401244100a031100c1c0303440c08142c40000580604240c0e09088180c982103240807580040030741641a0302080c400c10342e5022409a044441254010443d5150380e5241043c0784545042c0a600001440440103580345610041c480b0184d5101c00c901c401d0100d40b40e01e01a81c0c400c0b1450b00b82400002403448003138002c0c100c0036401100c103a50706414030b03029688030041d80304410b90414031100801c2180c020003100c1c51141a000100e034244480b508030395410f1007400e400681d00c084c8039020741590b4485031880303841810310580a801c000c1c8031000450005550030100018190391280d2503409031407151403804441a050300f1040484440d624080d00e0071030f032072203068100004011301103a400000c281e02c20140c2d62140d8122050541d1825020324007441d004800c5081c916500480500007601c04c41c1501031403500c01080c001c070010001c02d110745030480c4003d0283d02d41c0005004018000d0b0308006400030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 92353687 1250 92352437 92352457
    0xa1d07080d0f030b0a0305160605131205031c0b0108090607120e030f12100509070509010e0609101101050718090e030403020a030c050f0105090f0f031905030301240207030602 77
    0x800b02c01340b4020617040c10550304141c2e02071f406440c0c0001d4400c03c0800110061985103800341c146211403c04a07031079040d1707200b0510070146854562003400028403c0b2032440b214490301481641042031003e0180c8000d02d01c040c0420607400004404203404201e05202d80c0740c0350b90316803c0000303900d41c86d0014244070000101c103100c02d004c0c1e0000a60010000d0610400c00102d001303291400800800003003041d030300094058202c5206001c0d04942004c1901d1004400b404e091381c2929016002c14004e01884403c0fa5101ca02c031b9084166450f0807407001a51110380000031710982d501d82c041941c0c440200300a0380e0742e410008108011a40f92a80580103800200c819a440c041d0340e030700003030342030f020300d030406d803100d00250008001d50b10306103250510302142800c01ca0304128416002490341011111716034001da110b60501c10f4655024080d003511411000008003545640d801d129540760024000c5607420015150b0740701e00043c0020328260041c955034024410207040d5503c11020703400c100020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 92354937 1250 92353687 92353691
    0x6060a0807140c030d18020d030c082a0f01020a090e040203150712060e01030b010504020c120d0905060105030c210c06030112030305060118170c04050a1d07080d0f03 73
    0xb0542da650100c001e001401003d00210f894810b50f626000465140307005140065511111ba040107032910b4420388422074050500040412460608507218800d81804c0e030701841420310086c8e2050300c4450003c05548198084038160340d0410500b03402c1b40300d003218201c040790304d9030400c1010341d80d0840d00c2c0e03074424405001d40d5420700101140c2c3c52b80c82c1d42502c10b840441e94044d900c18036514244180b0005010000c6504910b500d9500c42840e420410f01442d805282c000440080d0140d003080422801141450050fa0398000711038020b006001f08076044030705000321000010545000500c025101900034076607038803080e4002006240111200740c00c003043c01500c0c1a0b00e150f955010256009042120503050810002d11b0002c0c00c1310750042000703040c003c540070902e0b41c2000b81c071600010781f610750419031001420b0300403c42c5004403000915500505007020403c5487c0580c110102202c429403441c19602e40420f03246880d5405070003242c006a01a0805c618001d2254485901903502d0b4280 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 92356187 1250 92354937 92354957
    0x703230409180b040f030210060b0d0c020102070b04150b09060f06070f0501151a1303080c0705030a1104050c04060212070218070908100905031e09060304050c0109090506060a0807 79
    0x110500c00008642c1954420600175080d414140c0501c000061409041820000c880c02c00d074005105000302c25102d034200741e880b0207500c4603074000d6044402c025045a5041c0c041c0c6804d142051b02c1d04075242552402d44d08280c154202c074180130381710500a0b4002041c030801241c1a00c10700c0a6504208000d9454550038012170300444d000b8451076109055101c0190030141c1010034160102c24000400c0c1d00046007086007a40e5000b400100300d068076030144801e50740b0100c10102d41d01e0104d40750012581030081c881040100080100202030890041d01c003407000740c2c3d0701051800700d4050b5229400c0980c1003c40d11050180030b030402080c0035407004001491040b0307030070003c06030484103c407020302060162500340803070f040811402014070145201400038004a035035030340d141e0191040e060507501c04a0120030b140035094003a00d46000703015100381d0b10783ca8681406507484000600044c04070b100080c0c01300d1140c51314054a48160320191246140a048030380071a0282c10040050040160b03200c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 92357437 1250 92356187 92356193
    0x1a060f090616030f080717061311071e0c060e030a120c05010506041107031206170a0303050a02030709050f01020f0105090f0c0a030201210f09030302070323040918 72
    0x70203841c40e010484502d01c840e00c2075207005082d40c690a1070210074070410000b002035841c2d20802200744500703030001c460050b0719510080b42c080003210060a50540c105182d0b00a81000200a004010b001c0c1d1044004500030800888030030160180150684070303102c0c4140049030040031101d01024015048a41b4220262180100490380384d210f4800141c103055103c0c1880024000c01d90420400c5130100101a07031810380a80303622425000400703102c40d00c40c203800da055456020714014160300ca00059086050705500351a4241e03171400f100070918080c080b540c0034a551007920b2281801d038482d01116424001088603520301744101d24110301c11440702d071149400a000d501d0180e004100203145015550000c2c07810311754500c420b00d00402c0c00c00c00820250b03900405203159000203c03134412203e0140c0c004035010305660301101c81c1c42410103a2810405a03d58020b04039980603070b40d506c40301c42c49401110801c0d071241d141d21200c41c00600084c40468060340c0a261308c4c00001c1503903400101030313a0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 92358687 1250 92357437 92357449
    0x60a1b0803040b09010b0102030d0e01060801060b0901080106050306010c060908070210110f0c093103020715020a0c03020108091f020406030c260403200105010f0501031a060f09 78
    0x1842103603420004800e000401056000c4907810001a9000340011504440000d60324000c1481b00c910382e540b1542c0d00f84070003000794005000b41c403a170703c001c1c08810345603060700c801c0d1360001a00c00d001038984000041d4040c0b00e04242ea014800595600c01044200d848007030284c501d030303441511041020440d810059440752951751f10840252079414101034414522420001c0c3c41d01000780c190000d00e12801e0320760302c1480090f40203218210b050b56010303140c41c0c00c1034400403039410054000b00c2c404541e000d15800145802c1214909818825081c0741c88004a0b110861000000c0c8035008e0041d00303000542c01218540c2c0c2c031201d11030031200e0010030340785800c401816000e82c011155500140038000c0c1e035490300074840d40d6411400c001180144248440d41c1480380c407190301030004000b202080400d84180501034005440d02070700920b81e0815410305009003000c0c0b083e000d50003291980040c0c20750080c0034100341000301da500000041c1a440030710170182d01c00e40d002200054200070306440c0359568 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 92359937 1250 92358687 92358737
    0x30e060d0e0d0e030705030a17070c080c0a050d0209040605041401020f04030b01060305010b0d0b13022214030d23041e05010503130609030c06020a0c03140315060a 72
    0x703a0050510060449001e022202510070303160081c0c01000e414460390f00c00084101c1400d910002102c41e05e083c2c00400700340b80c0650310006204119825001030760800000d680501010101c42d042a844d60751410040c07520603c81d0300030f402c0308030303403000401003485a40281e600c107000321000f01d08070480000c181d003240e000e50020500d400c4080307403d0080c015844951070141c1210f080411840d410030301c200d074213030144901020360300351a10814201515440d4491125040c060425500c0d922020340020020420f10102d1402000d00c4c0c07000985004c41c2e003280e421911018025003c034003055141113966900c0303d082e060f054031540c0404803204442c8030003480201409001d0012000661640c128004031907404141045002c0c01400038015070f020f600001281c3c0214009000f200070326065403101403401c07018180700e01c0860f080c89401d41009503a80b810344660b80d2040c451050b100718810a00050349d02034292403003c0d07204049400d1000c01080802d485040140d050202000c15254502c00303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 92361187 1250 92359937 92359961
    0x60510050907020a2105041208040806010b180301060302010518011e0801030314031905190926070c05220f0b010e011d06031005130506031e0a030e060d 67
    0x680d805001c80e0003540440f071000c1c880172000e101070001c00104280140d01818141d0f00b07610281c03008204d04441101c000300484c03400c0d0340a940e911100d140083e08100c0c0b08100903880110009142c0c034041c440d07903083ea54141c54540c2005103d0408035000749211032542e051007032040e10f40d0b00011088003c060904032659a441d50740d03055150082040c1c20141100700d440a0600c14401c2c0d102e05005101c20322001c03242d0000d03090787e4443d80390869500300e02d003080718245005501c106100300310745659400010210540294910480540054030400700c1c05051045000e109100c1e903c0c0c4400c81c0c4072444043c6000c00c00c04848200c02c08202e901c3d01c0c0c0a540e449650320b801e40045c3d60040100c1130100c409013095441800109018004c140d002da01940c421080040000c0c4022031031000b0a010f407002400c0602c04120039200200186001d5900c58403902c10f41941c4452240d240d030700e8050005104001e044500382030381d02a5401122003400c1e6034016824082c1e408221a1842442000700c0b03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 92362437 1250 92361187 92361193
    0x209040914100e0a030e0d0309090504050c030615090f0a0207050f1c0503010b07230d051c020403050d081b0304060902130e03161a0907031a06090406051005090702 72
    0x180200700d1007140c079401e08202d00f9400001480c004070360050390929010310265000405e11802e80b0303003110a0303001900201c0a0b140f4190500c4140040081c0d04200701e5000c1c1c3c2110610386842d1782009003103040c1e44103241c0c4100d00f100090b808000d00480b0365002010020094104003203079807210305044140c00030b400903074003101c0c05100e0121000d0300b52050400c181002441c55040c906100000d100d101d40c0038002e040c000d6070341d80904400713042045001002400380c7e410f141c21442c000b4102e6001c00d0021a490390340f0700c0c10074081d60703582c400c40741207a038404c0050000302122001952034401c010000506012010921a02e0401441c019445a4450303d0001416103052040203200c0008082c032150080c038001600380101c60000403a484110140c180204c804254542954904d0b02c00c600e60780d08003411410300401b0740e00000e4110a0381d124510b52203640c590981c0c0405a801c048030031a510810000104004c510142d02017504800241c402011413510f0b1000300c0e046200a640000c010381c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 92363687 1250 92362437 92362453
    0x50618030109032703030c0f020307030c090e0c0319032303010e0103030813020604091e090606080607050a0504140607050601060503090d0203031509130b09030702010f05090109090209040914 84
    0x4c8406aa4104408205a18121402c503100141020300130b240042c881e02c03164070000c0641d03404200e9035000b580e00c24a4031100c04c0d01c85001c9c102070308021400030301a1041100c0250701d440c0104401075540c0da00005410080403540b002c44007200c00e00840c03201c4142d080b02800201402e1030045003c0c080d5a034000903554950303d8010400c99000b03143c502a00400110080140d403418105c80448010010110b41252886c0da13850f0850350840c0c40c5c0c0960362615106c1c000704a074a4000d0403c4900b05015580076984404c1c007500d42d80f0074111000d0008200b0081440300000c1d81840c82c01140020703259505040740b5075551860f150003a0400c80c0818404020484442c0c820801c500c1d2103402d5101135070840c1401f0390141854010131640328881c00c5090006400e00c0030407050404e0194000c403036035884c0d0070506030325516988422400c3c3e001a034020002200035004d41c04403030000e041030b55260001c40c684003002c00203420040b8201d81c001c0d200c86055001c1031807403030307041d000b070f801c11000e08415 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 92364937 1250 92363687 92363717
    0x80607090518070c06020d060b0d14060102030c1f06090f0e0105060604081207020f03100606020d05030108151503030d02032401050403060207030c1403070b071805061803010903 78
    0x140000c0034034150b410800004105000e94080c2024216a03844040940c444007100c41c43c00150400303812040d042440490940780701041c41e040341d051010307600c15a0819171070780c400482e16232213041e41780045580b015200c0404038000404112911100c0c04000501c00d0b00e90300c20b413003540c100b080a0304c03c440d2281445014210b017071140640110741110094903151074802001e80703e10104600c2c1882c10070220361107043d9119840c00500107200242034806815500e014140280300d00d000c2c0d00c0c01842081d996039020341c01842180d059a24103c000c1080b80c017000c0042c29003120003441130486854800c485050740d00c00300058400d0311411100035032030303240c0107201d42401240800e550301008440d545028643c0d8128044900b900d17004600580d5a940c0303070509440700101040018035400003101042034180011001d4040c051282440901c0d0340c1b5010b1007200c103c1c0010000400f0096022820003842c9800c07401000f4140c031416014a01401901c000390031140c61a4080e0045180e8034030f50030007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 92366187 1250 92364937 92364949
    0x901060305070806030c0a0302041a0402031006020706020d0816230901030b030109021503040c081c030b040b0f01050c010603060507111e0d031e09030509030c030106030b070c0c0806070905 83
    0x4400400e034006c1c100310110000007100300c1003030710000e809035541d51a00200074020690202e1046401780007035540741015115841030405510410340180200100070404520109855071402541e9442c00120386a641000c071000500b4080b02c5c0500000f00d03281900c1c205140710071980c411240c20a40d40303404282001405484000384054444e0345080d55000050360ba01451100c5030380d4001c80c5540f02d560320701e40300c503480190b0b801010952184000f9107141d500034944100f02100c0d107036414802c20400c1d90a1100341c81584a80d40d5008e05c0405a0591b60b500c075030050600f40c00315000204089507a500ea140c100c40c025110790300019141520f03d42c050800300030018030410000e0001068802c102115a00c0c1c241c0d4042110030036440314803030419184003400ba11290050100f0400c9601454a0040c0c95039000d03036485406802a407148110303902c0c0c1803150b042120f4120440748420f5031004811102c00304141412290500c3c40d240109480d41e003004030500ca140684c44441c8403070304010030404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 92367437 1250 92366187 92366191
    0x1f050d0b0102060108070b1b0f0303040303181104021c05040b06090711030d05060d120e09010f0503071203020a0b0c0306090a02042702040911031905010605031501020c09010603050708 81
    0x410340d0f0104004126103400020682e0440381d426000e1030300ca01c040d03002c0b4202000204607510307003441041e2a2801d14070f0040004c0d401140319880030840e0203400100404500400000903107031820034401301101d420150010403034200c2020102c90342c1545e10070700c1803c1b11000e8030141d44800c40e01d8204011420801034080e00001c0328181030520003c001c0c80595607106100c16081401d441d0700109101340c45a050901c40285c1c010341440d03609000807001007615900059052003103500b42c0c00019000c0030204510160b50014002e4004c440c180359400204034400d140840071442050030450200d2112010140104c1660f4041a40e0341001010070944840c0680912100c3e44100710400000780c1c10000d00d000b09440c40c101c410781420030b541c60002801240e00014480307041c40c00820080c00c0d060001e610a505280c1980c01d4042c101e4a51011102c09006610200c2c1082004c030b84184c02c0701c504c0840c604014811651504484404501500c00c207a02c424046a15082440400d9400404d240e03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 92368687 1250 92367437 92367439
    0x6010e04090f05060603010506090406110412080a020607051c09021513080c06030621010908130602070b0301080a03050318030a0c050f06091c120603110a1d151f050d0b 74
    0x840541481c00002cad1035144080c1c801400c031507941c0c0303180b5138102006c03050f03c004000039002a03214060608200b01c195000780760407401401100005070f0550300500036545406800e01c810122640c2c1011180024000c698003a0f0344000702c0c1d00a1144012030100a101914600d0400d0300b8081ca0049007901d009035461a5074070030030080c000c11003c0d4880100c0c02c0e17414460a001541c0c5801e22503152070042089c004054050500050711002805400011400302d0300325500f1209103659406214011340403c0c02542e0705500010303106800300344540082c41e080715403110340b0b40e140c0c0c000b1b450407451a84541d046402003016840751405009040c04009116030200018281b103140010141d500d4076035038541d5208103017140a059490702d2007004140c0507403288117000c00c49d00352a400d00300105880c01016078800e1800d01c0d404104140d140400d51040e424511800f45152a0300c6998451442c400d039103581c1211205580c241c48505d010007030750600c0d000740c8949940e0800d00c00b05000740c5040038002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 92369937 1250 92368687 92368691
    0xe070609030f0f03030e070e060f090903090d03210614060c1c0c0506090304030c0614030c0d020706020d09150903050313020f03030406030f05071407060506010e04090f0506060301 79
    0x10004141c58101500740b05900224800e40a0514a0190010304548a00700440d10681c0008a00390408400250040c4070450b0010152605001000800b42c0111800325103504240301e94101400c007a95100201072183c1032403182580840c80e8280e100c60740502c0b160100b80c56240c204466008090080406102550468074201300c08001c940e0315000c4180040c03075012030700100c0010501c078040e074580e2907138060150b07042c608040444964a40141c0019109203003555000154507020340080b25943c400010040d0131507039240080c4030a6040404c01d0403940c0e400704452800140e851000784003c02c00c0c5c4000160707103500e60610764100200051031038a10351500790000003207500402520307032040b208026160500000c0c80419001440c03003680903010302c004140461100e8041e0011110100110020410703903031030b80380860302e040041400d0b5100300d070100301001c00b0650b5900034941c015418100000340e54101808101260b002c0002521440785030007a4808002e0309004050b0880011802 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 92371187 1250 92369937 92369939
    0x601120c0806010f050405031b03061317090d12080a0c08010602030f0c01110f0316020a020907030c0315060309051009020604050d05010603060207030306030515040b0711030f0c010e070609 83
    0xe000600c01402c00c0d410300c50302c0121007150910034012200138103001f070203072481030014014001c05456401000e40c424010040044c401006243d054201c80d45c02c00c0b40010070204510000f0816800a070f2455008181c090030b1002003184189807141c102415500d020803807505403955000c442c01d98902c03c1c04c008002c8010054103174000291a41e6130b00c0ca1340c10b25580c604070842103005011b9004d2007641181c0118002d52000c0b0b00d04055440b40000081ca00501d030074040c07049850351a0540c1c0294030510b4236000c2035246100b503000552180c4942000200e40c12015102d2241c04015400000005e4840100008120f002d2210504001c1005018045441c09900040d034901490003141e00411009002d8000e0010941050f402542c1040d000c5665500c41d050080141049010a9405109180421000a881150f814407540d00000840301e151a036090858240322000020311052205109080000700d0441c020507021030100000240c0300d501c0c500305e41c10007074036a21500c140510528 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 92372437 1250 92371187 92371211
    0xd0f1209080f1f0f06080a03051c020c1207030309020301050408040f090e07060311130608060405060303030402031506150d060608160905010806010921050606060a0903140a080c0105060112 83
    0x81c1e0001c000c04003d0209a280c2c10207400c1d8020310741540652620b00c82c508504040c5a042001401648601c080e46141100d0000f1124103070311804120030a2641318004400c43c4100070805030410a11924020a201c02590000781c299201550165580d00d0b00207030402400a95440243c0100454101440314941130042641c8580c40c3d0f1041006140e1583c110810040205d0f0850f00301118102c41c0741a4903845e40c2d030041444a0858049018516200c041000340c54000141d0340310b654000c00500d000510880c0642c0180d00107000150002d242280c040e040025110180c41c240d032421000080b06860081d000b00080c1014114445010302100d00d840c15640c04844030b02510f03000e0030203c880c2e0300c4000c0100c031146110f500003a82c200c480040e0340041040079900c220020b00450481d901501c803107041100d00e10903200071001044480508100090001e9401c0b8034064035601a03801100b5140c440c26400e81c040414581d10765504c07c100406503030041c0140c008010305407004c002c42c0a0f144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 92373687 1250 92372437 92372473
    0xd030318211d0d0606030c171212040f05010f1416030603020607241803020730050c06130e0c030c070b090f1023040206090d0f1209080f 60
    0x308045001c1c3d0081c05000b020700515400c650000d40d8485940c1100300d5481440c16508032150840c011700d070084c01c00911030490648203a441d00b4400b03040300d0400e619650368074841d502c4150411955035480790350408600100384128003103804240c40e00e025900e4140240c3c04601d54080b0843c00345440c0c25400c2c80582c8500e410381d442c0790740c403448aa00040703802050b0256030743c0654080046509055041076040c5201d00d051580c28070a0b021906d20945808203800028501e00e003810040f482d80d2060b440302580032a202c00b66034050420365041e0700841011071913a43c82603500104d07070205c800041080040d00c4030455030040040031400d0070341c203180741c100c919845958009404118100d012940342c8030309000700055043c81c801100c44104489200e90040c10340c05516500540c0c607002551540e8440308030a62142e07500901c410315240c858010003a555816038400d07110803002e000c00c2c10005411309500e03850200c50780c4030058181c0c5062541440c1c02c041d40c0480380300782c00c0301c0d50184001c0307204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 92374937 1250 92373687 92373737
    0x10e06030709050d0f05060c0a031401050105030601030c05070213020c060907030503030f04140d0f020114100e1317040e0105010c0506010603050c0f07120e0d0507050d03031821 78
    0x444d00c0c0c0c1000b503040d0a01341d01d00700c02090007030064081d030002d1150007040d540040c1040034072030b00c00380411003103000050b2400009203e011301180007000003d58035031003a400b0340104989810070318280215600800c0551507c08505e41c030032540003e8000c040c0004010f01507203d80e200c0020302803103003155212902c07400042e105954400420011904000c01146540f410402c20002c4540c40001e5000042c003404800c00030601651810b1020028082c0d4030f88041d200312000710030003031081e240000c4e10310350290080c1209400c0749404110f1000541803088909040c2c8e002541c5512036040c8105403400070410707400345051015080c0c0d42c030009074002c10000e04444460a00046035505c101c0980518451900f01c2502810002207035010000c001c0210b006c014042d503210849400711500b802011400c2403400f800700d600c0180e04001c03d16140150600943c464034000c02d00e030b6203201da25003445503a040c04866140a14548050000c0d181448003000f90340c80c5449880030000180c07941c0b0040030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 92376187 1250 92374937 92374939
    0x8030a0e0d110303031f0f0605120711030a020d080601031a040b0402040803070302070f0b030906160306120308310314070b1807090507120b01020c060a020705010e0603070905 77
    0x38054140c401e00248001108401002405032545c83c42c040600c541c101c0000c19030035110300030a0740007050745100d0147c4641920342c10740f030345480e16809420b041c20315a0300401c00001c1200590040d8982181440030b03020b1550f00c1d400030680040c5250002c1d248642c0105501d04040c50185030700241d0480803000360101c14259000620011403201040103840707144c00090b000e00c000a011810541d001402c1811110001007200c4195110b00e40c2d689644419102c3c80b001c1d0f0b02460103c0e2510103030300070325410f0401d68280003403803c6e603402e590701a00c0c100c11000d0b40810324801c104849210442004d0120342c040980d101e1840b80f03d00401c405d41d03c0c540e4400f40c2046a9441e184109800c15802c0f03c00b03042d0095000030040c5059030364072001039801600340ca400d0066401c0000d455401d401154040d140399100c00c20b201e41e0206000c0c0040003050203150440c800c01120030819240d5900500500d0407581c050000e1342d052100141c003001441240301d0003604104200b148165101c04041c0980780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 92377437 1250 92376187 92376199
    0xc03070513050307060c0605060916050d06050904080a080711030f070606090914071a0405040b0105070221010e071401031d030307020a0618020f090c0c0f030702010908030a0e 77
    0x20303181041d25020115900301940610440c10042000350300021440b118500c1844103000c1542c510051200380d04042d41c480c00440d190b2504210464010400341a0034070302c2640008405640d540020f4404105540030b80314042c0001d08291040c0d480310300c2d1703584200f09003081002c210780c1620031581e0b840b91001680741000701061550800c4020b41080b0300500f008501407203a004030342895054001c00b034559240d64402c6d84000140d8803c503881d4146080100755140b82040d252505100c040e02144084c1410400d04000d41001650bc1140c8901040c40303a80221450f20052a044d5007150621070322421a03510441c401c10144d00f07120200f1842850a20300403c54040e206200f0b80d4840c0751b0900c914040c0804003c2040e074940c00500080d010340213850900002d6000e031014079184e44000c1c8041e4200c0002409100f050510990940d08100340ea42010320340038031038503030031b0420081c01c4001644d0f0b000061b805081d036034810402009030078804060740c81d208101902414507000207a0643c0200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 92378687 1250 92377437 92377447
    0x14040317091002040914010501020718021b0a0b090f1207080904060b0c0604030824040518070303032c030315060904020703080403030f0c090e0c041203021f050c030705 74
    0x52018810803a5114802d14255219600c0f902420702074810050300c0f204000b0030340c0000860b5840003a0803400c84007050300d4160001c145c4406180030703520040201d1003603000c2c0e40b00c040c806603041091107080c5005100c10340c0141131520102d4206641c2c0203004d1407950003c2c0c207140103818004116610250311507100380d03652900da0042800780c0f09030b5001c64851200030488040509021520622a510030781d1503500a0703403001c03420454145059020014049600845a141d00b81a481245c004494100f5031554000c50000b0b549041a00d07001100080d07190000c0081c44000110545c1c0306415860400740414140c0301c2c455581c0c000100071240700300a813010700006c0c2c2c81d010b0803501a82c801510540d0307101018100502540001d4404a00091419184441c1c105580c0b0a62010924554030801c2c12442d013042e801111401800140a1550400c00018010461840903100c01c1c42500a007070071650400052182420140c102c0c500c0d2400c00b0100010640c54030110399001c0402e043c140c2e01c070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 92379937 1250 92378687 92378701
    0x305060301180b010f050108101202040b04021c05010504180b070905092403070803190e030a110114120403050703051209100605010e0307030228030f02010314040317 73
    0x250010395000010b6506800740d074000e201c040f4000c14180d811410010811070390301c000449601d101103030380e03c40c0c04004540500c041e411f207070004a03440b400203201060031040480040c04903070050081026026003240c0c8000620100e019603401020115402c011103264110030302e51300090007600400300855040010180c80c0070341c654002602014061903168508091403050281000c41040154180c4145c0450310b072400141d403000303680c40390300a103051100b03003079010340385605222605040c0540c420407681a80c600708840790196009010030380d900788140001410900c11a03001401a40c1e003004100d0195a40f4000150400c1e45440d109a407144182001c5890b07000d03404290302546244011b001c907400d4002a0103030807500c0d001c002c02615540b030b03005440d109000300b0204e030140c00c103160030405445c000d001e0080c16503c100b14030008030241c2210b1406400d0540048a403050100242025940d02d4407942d054100c00c5000101141844d48001e40f12141c021460140b40034060002104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 92381187 1250 92379937 92379941
    0x10f060504231306020c0303010311030a03020a080901020c12160e01030c23090a05180f06060d0609050706020303150a0302030312100f03050f0d05040e07110a0209040b0a0606140a0305060301 84
    0xf030a07030850011925001074041040e01c7ea8028402501c40c043c034a010350b17445280c04100d041041f60315400400c600f146959942d07443d40c000114107819030103802c0383d1660702d0b1107590401180400350700c003610070300403031810840c1c3c892400c2d0031440c0810600342c01400080c01042217002500c1040000c0080b012002907003140c00c2c40da003201e06401c10030103424802d01c244180c202c0c0c3e0140c215051b00310049480722611550310880c940140700c0340d6001ca070110342c440c14903812541505018560100c0c0802f00c0d034a4603850300035981c0c01180140d000000300a940c0c90707000c80308501c2140032505954890f00e1a00042d42e81c0c05000c12510100000c0e9004c16294206001e040b400ac00084240222480c0e8a0800741d03104e4182075107262482c0200f104020441d882074040700c050b22100900b12605440705c00d0225800815a017290015215002041015980300792561f40f24078031441103a9080c4c900000840d090303032695030040b024841d01c40100720100c43c00f54181c036150314152800260b107036200b500282c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 92382437 1250 92381187 92381221
    0x30b031603080705120a230d0203040507060206012108090f0306090d08060301090209010303080a0905191e050d050c0a021005190e06040608040510050108010f06050423 74
    0xc1000d4280500104020350500900b01e40c034001c00542d5007807004031400301000c0c441c441034880080c0d03143c007200355078015034800c041c0220001c00105040591140340403049034025201607030310350b000840070000b5550400c00c86024110b0b10554003014800204030700203040b010365004025803070108d034010150b124001c5041c032083c0020100d908a0601d000d80d2616403140014040000e01040005049420140211005540c0c00b405040c4260700c0d68604070344400d0080d00000009444080080c0400d804002031081a00c001c01d0001c5503025610b8090800202d255845080440c1d0f10784ca80b0204001203a000310410f042d0074015a224024140681454180800298414000e4801401196010300942810940f096800b490007070400c1d02521003106444607580e000c00100414068544541d41049d0031602c03070303812500d0b0300350b441d801c140540c4c070240c000003a00d80d9680c900600c0c150980c0100c00080030195010000301408211101100c0704400250b06e441c804180851213014805c10440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 92383687 1250 92382437 92382463
    0x9061e0201240602010f020c0d030b01051c0b09070f080106030209030304050603010b0717040b04090b1318050106090b060403081806071b0603020307020d12060503070905160e01020d030b03 83
    0x8100c490300b10320018410800d0b070152000642c604000c441441c000d900c00c45280141e200d00a0982e4810303c8022400781012503103c030f0421500b4004001c0e03221210788501c021042c0700d2000324000714031405002d602d01c00180301c0d07010000d9000039440d000340c00110703090644500c2d180140e40d501100011070301e148078076070025420103400000013800c0306401025081ca01e115840794015003410502145040c019030048041504c006c0000304217400340d03036100a403802c0006c0c1260340102c00c01e500641c1190145845421980e8400000404100702071084401a09130002c1c10424002850003082090055000040401400260f200c0644181e84080c5c043c0c0d410061000345e45602600d40071514200c961010260380c520142c0220740240280240c034403079041940101140b5001007002c07a440ca460f03004070f5001640e21a800b003841d0718184501c00103001c0c0c004012400c0e00386a540141140f031200031507420862804040d181e1680d0114028188644a01e404121032414100090512100d00940 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 92384937 1250 92383687 92383721
    0xc050705130605090108031e0918042003060919021201060602071a03010308090607060b030d030209031509070302011d03030a0e1305070909020f070b04050705030d09061e0201 77
    0x1d4008151500000252982554611000d9036a085030664a00404180d030200b421035420241c4103103124405840c040000500c080d421122901840000c1c003025a0165800e82c0c2040c0e010b5184050180080740c010815802066189030000f070094403485090710b8900042d1200e00810155035501c0110740c1500380b0407008101c8255100406541c50701c0510403101404518043c010f03451000c5004d070b9048a8110f00010f1400016204010840c0d11038202201d1060340c0d2542c148082c1c8081101001d25041e80c0c9005a030780c0482001c140c680b529120b204a03d0140c01c3d010420f410b100400d401084a40c2800c064001300704801d0358000303202c00036031030a8262002040300060f542d03102c0150300c1044001d40750108030744400c4210a00391a0101c40500c081000f1070b80810050045a0040802d170000b40d01c801e09000d26560f60303024420054800b40c42c03580c84000144414a000c2c818041d5516a900300228490b24101c40039100c1801342134448000c5003440e03a00640c0b0b034001e405c6410781040d81406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 92386187 1250 92384937 92384959
    0x18040915051b0c120304020402120709140301020301081b1c080702010815100f05070503030c0d050105030613020103020d0b1206100f060203071202070302091602011413030c050705 79
    0x1140060a089800c07003400c01c110340d0b004281d007003800110340c040b100c050050700038800c4100e13207100c96900261007203801c55402c2041c8405240100100c0b80102d10780d55500004520b001240701c4285c003c0c855103032207a403040004001149001800c41c03007007000c40c1c0d542c0007512803420024160303042441e580b15880d85060940010004400000c011184c800d80f102207150702c4840c5924603001c02c0b000c1e0660001e409145000c0d0300c070b0265909502c00381791407800c2480d0044603540c080c190b80059400c5c82c401c540c04503280f40480c40c10300809015142c198010182498800402003e5804502010341031681c002142e505a01c12504000103174007018000303c81c4070104642c1d1a84d00c0c8002c4540c03e6404040b80d0000c01c08030b00b202081c400301c0d02150300442c10907409882d16280d0a40180011065100c2c0401c000016240d44000f54030454000395509400403140c034010303003982e241c024080e4510205204101070f41807c0103400403103e80510340340d1161482844d01d00d1500e1810340041c0e9110381c0e403801c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 92387437 1250 92386187 92386223
    0xf070303021c02030f0f040c0b0406020a020f0303070201050f0c010b06030412121b030f020c1906050901140f0403090503160602070f15050c0c04060611061b180409 72
    0x785220404055600c2610b03810524000c128001618410781314600c0d4000301c0c90030f0311000c080d140c015028100d0103030010794440c14454140d00c02c0e4440005a0407018902040d4a0488001e0000c01410f50141d03141c07506541c002040381c86042c030317654a03407140880c4d0702002080c2540644a194400f030002e03583e0b41000e0030801034108100c1c440c14009014180c0340c4d401c000d014010940d140140d1805a001003450400c160007501c807541001d035001342e0902c03040c0b207080410003100e43c8400c891445031000c580e05013001c1085d14030046c809183c40e8141003142a1440e40390500b507a020042140148180d242c514040350404060380c4001d0b0300d8416001199046400d940c01c1a08580e82d039003c684026030f55108100d02c0d01034a1291410340c0380d04c048802081e03800703440201200d2341440281d80c03003003019800190491380180c01880019a002c60001c8159004001061700b1107000c0d80011070030140409008114425102d041d21102c003c080c0704d1046443d503401801c1082e034056400c2d4034040c0401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 92388687 1250 92387437 92387441
    0x6060314090a02030304050f0607020d0c1a0a081501030e01050a0501050a21030806030708030a08010e13200402070609050c090f070203031303090b0d0e07060906081603020f070303 79
    0x425440c016400280100d0018040024059016580540518185071600e802c01018003e01c207002c80c3c00c201c0804c001700041e80c0d0140b0a05c0d26a20a44016502c5400d084695890303d20402e81c40025035810814022203075000b060441e808000b420141e0000070404004070050a01000c140c00e00398208000d004800314241c0103d03059650644000a4980e0740718400c2400c200010460104048048014008a03100381c5205520560140803688841d940b00443c03441c40d8003a00b03618001680c1200103101840f043c7e01c2c1c00c0d80003036000301d90070b021640689500d4000c0b4562045c03096400040600c01540792a107070161115160003920410142055013409900c40f8842c103140d0344120065400149110701406640303005070714960045003580c2d2400751304415421207007426028044039140015018080400070110090b42d4540030410890850586160070882d40120050003040042440881c0d401643c4581c40711040c0c09a8201d4424030740309900a00c181840161145800038441040c03541607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 92389937 1250 92388687 92388701
    0x30a061401020102120f06030a0f05010b0f1002030a0f030e16090c0203070f0b070909180201030501050916030b06090411040f09020f0712020f031303050c0406080c15090301060603 79
    0x19034141120689410012400c030320640c143c89061054202c00f14014040d469080c035800040a03040743c049081940f150060810000b9049a03507130345400e0b51031480d0409014400b80084140d4402821485049010792640a0f086a20b010001c00c514050449442600400740743c0141005940e20403001d101d1500b6040d9041c040d0400c1e49003003182c2d01c507001d44004126050282c00c1503c031400b0410f5580c0f24406500090b00120800000c81c5000c21007102078860721100d1015040714030f800050900c001b4003038600c16805244130304c4000c42007100703a828180840a5010036441e000410031024000a0f2050181d060703403540003403600382e955074090b5800f0014000e0f2417002508140c000c0e61001d01400782c3c0304040c0f404250190502c19100024840540e034200e0305510b00546d0418490300c51203610710b8126586458059203a00800c20610405200020503544183d1b414002242030505041c0d072001c89040c214000c07028884c52040301c4000c0340035903001190040c001e010360b130350b0b03040014003070644 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 92391187 1250 92389937 92389949
    0xc1e0102060f060d0f030909110c0c0d020108061c08030c0a020601080606010c030507050102090409080306040e03070c141201060b0d1a181003021302041a1201030f06060308030a06 79
    0xc00c00032601d4501403440d124403e0600a015070b01a255690b01c401200810440480c18002c1d42ca1002c580d0010750b004d480d155102a80304c0c0c0d0b031a1070021401d00d103007501c0700340b83c00d01821003a4640c01c050b0344e00000d00ca034092019100e2410803000058048650aa10701010b491210003000348009003c0341d42c01010301d0000d40e0b08603007059032200f03031481d242e07401030740d00502260551072100e0000f400303070002d0300229000710001070901c69607a000c80d00340c034500300049401c440c00204010241c41d00b4869030740c0ba120103400a5080c400280e48130b00c2820b549014070030149680e5408800c181c0e4480c00304940c5021007070000d02c10135664021541c2160002c4488600729401c1411a2108240790b841d410310030040242481039807510010854240a0050000d01481d00058804400b50326540403500425111610040e070f50ba2908030110000d01c01c1c00b11341682c1a0082103d1508002801400c034156a0888041c0ca031066940c03a004000f4101d5500c000c1038010040100044000d080c0c3c809001c84030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 92392437 1250 92391187 92391193
    0xd02040e070207061412040c0e040c150906090905090c10020607080105100507141207050304050a1d04060e16080c0a0605130e0402060f03010312030621140c1e0102 72
    0x146606042d81c8000c0c45034400405c5010602c400c00c1d00520340c0e016150814051032103251250344a965a0701d003c04111030030740c0e220152160070000200e84e0441070708003600f03500e0320260075824010000c01d129194821411565200d2001c00c140c200c0a0040d501000401491500b6000343e1940107900c03030200700c2d0804049a94000000703031030304143d203180034100056540d4a1800c2042e0352002c27606010604109400d01c2420812511440c00c40b00828131140130308010f40d00ca500e0841008851100383e08400401480001107146844e4405003450304254822404030b00d0221020802d072074458118003a0500d4523001e02c0018140300042540048028160341414810b0385a11040e030b100e216034002c06d10040da410004000032040d2814480c2c2246c4002d0800745002405040c150950b0000c0c0c200350740d1070780c28644107140903405210b00b000420300030342d0b12040f8a07003d100b41e070a600007859001d003055100c150b60001180b410300140300b9130a1700a000381084400043d81180740f41c095000c1c1ca01501c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 92393687 1250 92392437 92392439
    0x41b08040b0907030b04020909160b0409050603010e030a05071703010905010806060312031308090d11101404121a0702010615050414060901050c06090d1d21030d02040e070207 77
    0x7580490a0000d1384d030810300c05195502c556083c00281c5000410250280c0521010b100c0d541c140ca8003002d00070444507030240e84036400c103980001210800fa000520aa1604503440203c10b0b0100540b1445061800d00c40c0d1240103a04010402c41207024a42c030302110000000700700c480e0790707074080c07816120300c8411a4001d60b0303141d0a1666900303211910505204052001650301808100e9508581d8072800069080102c21000315080d0074a1200c210b0380386000702940801801d20030f0b03c0341c2107110107151101840044030700600c0c0601c55401201e410b039030300100c090140403945010003180c0e4403168045046180c01400240200024024581501580c00f43c001d810740c81441a18150ba03070f1f01508a280d2480709040005079800413600a0510205004c41400a94203100140c484c509070307400b91900d007001c0e50380103101c1040013003010b610081d2250b802030543ca540c0c0401a4140010340d1680c440d581d840c00307542c9540540c1e48800d5902d1f00002c1c1c0420300702c8810036203a006190039001c0f10166 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 92394937 1250 92393687 92393701
    0xc0a050c0d09180924090f060b040e0d0c060c0302070f050606010212040302090c03070e0306040515010f060509010807090b071b080102040302030d03020d0207021005210112020f041b08040b 83
    0x16801044d0003070702c1e0003110703986040215031601c94101a140814000600035440d55203290701404040019643d865031040a15910b0170030380100d41040c0c130311001074241d651070b41c00064050032030150060036069403050014a01e03402a030440b407220350007500c003178501405460141d03500d110445106005000f03106060350800100c009503029240d00a00300d480c55550b4804074256500020040000c0001e104200c0c00c2d2520103107c958002c50190010303013544c441d034000c204e00746003045c0e200200c01e4101d44400c0020300d03480310a440500b0300900c1c00c0c90803501c401104031556020345d00034814954000451100304204140c003500d05200300d0b62071140495540002d00e00301c1c0030340c3c8406501600007038041d00d1094881da00508421500000c01414941c03aa00407400d442007034402c80003c14000921f040a240c4612241d01d220703003850f654220258104004998000100c040081c011002003000340a00d0751980c10054000c41800d80c0080111900c460050640c01e0a46050b264401050042460 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 92396187 1250 92394937 92394941
    0x519020901090303080a060306020c070306050105011409041d0106061d030a02010c021504090204030b06030f0d02071401030e03030c1c0c350906100e09060c0a050c0d0918 75
    0x5080030584070706a02d54550b480036030b2040e000411160040340e0b940c00203c001134807480a05001c6030888028160036003149030000c12104180c10003814004100505004660040100d41c070742101074402040e602c1035500203440c40642c0e0b00d607085003942030038004203100758040e1001d00190302514142c0c165003e140d0a0503115162880060700055400c107201e13016042c500713200ca4600c0349201c00e0302d00e0706664141c0e1204a0700240c10480e0060402c10a04c17150349410000c2850170b0816001900440200c0700b40607556200302d101c3c0c0841d0100192054016a01980c010114a040315055030b0b62403405180c0c0244035440300c501a005840c2407002c000482d4050700c01e401c841c0381d40380c4034030040d004024505854283c84070b2001d014441d40c039101c0b00d41d000c28036042c80c0c0982001d80080125040210400306034030741e99082480b600c0802e40401000620000d04181c0085031444095038484d074031482111140300300c000c0c1d25a14403030f010000410661040e48441140d0511240f02d42040310700d41c882c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 92397437 1250 92396187 92396197
    0xf011b050702060301060f090b0a030204030204050f090a03080910050406060515030708010b0f041707030b0606180621040309180b03100f0605031e070e04150507030b0a0801051902 79
    0x2d00003105100600030f090140e81c80d20071f01811410610341031035840081001d16841080000002900402c00f08110300303047c0031301904205803200c65074003883d111807800e07500c6008000103020004400c02181d80b2510034410418951031011040c0300e2031900f803c0440140406100b118000c50501c00034010009261041d280210529a11145542d01c0d00d800201107401404504040c903508020004141d10481124007007825810050568280340d800d2022003008000d000c9030180800304101e80d0f224440c640c6c0c03103040a1080347d00c552506105034424520b0510120880d441540f400d0500c0241070700104410b044400c042e60089042690b90010703c241c4406001c1c80e030f0998060044a0f00391500c5420142c12513480c61780020740c59944d200001e14000e40b40c1032181c03030141142d01c014800381c824005180904541c501c90350382400e0965501d03000d074001040740303810b00e556140428681b50ac29003080410180c02406080740584a00f0b00f11b00901090302d600741351590007002c0b0a01c08a690003655 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 92398687 1250 92397437 92397439
    0x40b130308011403120408150709060219060603050a150f0902011d12010606030b0310050105030d080a0204030206040605092e11010f06081c0305010311040f0e0f011b050702 76
    0x201c8503441c011404000035802c5000a505008034054450100c1711140a40000d00a200c0140f441c04103090300c0351b2401001401c4602006003219041c49181d8001408022401c0158403c14580c200da06100c2c00138040b40c2c00090141c0124050907040c40074038008010340000e510300c200034044006111504881c3c612900a003c61165038482c0b4038003c0c0034641e411600809000c416103c5402740c00c841c01c6990a4000c607000c01e030307194103c400718101000300e10b0590703210101c00c000300d5040600107542ca881c008103603c200b003075030000600c048200c1c1d0140c070015a4041c007800d0300c890b1901c0c0090142e400495007980a18001140980010716070800c40c2c04c032601c031014400f000d4076141802c40307980d000c08041c14210340d00d6144145140480c0d1060b180200241409042e119001041c104854170080e5505000c15043c00014408102c00d800c0da1021044121000900070800d100601c1c0500702c40c111800890240c56100703560044190092040c106041058692140c80800203407018081d100010b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 92399937 1250 92398687 92398697
    0x210a02060c070b070302030405101d070f0f0e090f1b0f03032113020306010b030421080705070f1e060f060311060a1106090d0906080402010c0f020f060c0303040b1303 73
    0x30404c1c0c1d601aa0056802c20300403000e88040310341420300d40d8156101050040342401380010350385010907003405004090905441c0320f4690307502e00128030f4804561405500351604010f03005c00e0001d0010400041060011030a41b1107090310084001100961860303498050303014101c4040c01450f001c02202d68103031203003004542061070014000480304000348603c5406c060710383e4440c05039504000c0103009180b02007441d5900c0c505031506101440303054501c502c644d803089603100e021581140300d565201c80c8525240d03880314801e0070000400564094050003200405004c8044020303022840c108807030040300c0074008018100c0000003150742510000e81050008590b80d01d29140510062200420303a207010205241c4061015050007000c1c1c40c0c45c8401e0b803050030281c007116080201038000f81806d062220440c90140c00181c9881600c86004140070300748840041156201c10505540c40405440603071980951343c03c00c0e5590340161010389032000c6000000310080c001c0c1d5540c43c0020340c541e0b26 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 92401187 1250 92399937 92399941
    0x1410050121021c0509010b011b140106091a210c04051803040815060102010b010c12030608060901150806040f1203020c060a060302010e01090b0f090102210a02060c070b 74
    0xe50011807200c401c40000580800c2006200d148164003c10858501080001c49007456140c8600b1640b07030442c428144020841d01c00c012150440412039025000444581d01100880780d00e8010403042c0c0000e4482c41c03400c0b05282007038035901d95240c0c0c441c1c01500c1c80d0004140140f0890400300701514400b829522101c61a1140c1c2000d81100c1c0e08200000c1c40f01d00c91900100c61181143c2050700300c030510b6886007141c242012141d081440d00304200303000030480304500e000020084048210064a516030b250070b0809071034800ea0182d001000704209a50190070800c3d8000c1c042d20340c803028505000b04040004c07542902c0815164000c1c1c0c0e005c0701c240c0d44102c90b552003427445004a03c0b40c600741603003804007405206091002c06e114030203002001034035608510014051b451448407050400c0300090052001ba52210111034406c50351004036512914582c0c0100d00e0080040b0b005050181e1020601011842200140c80402100c5d002d4515980e610407840404d80512403000d4840890140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 92402437 1250 92401187 92401217
    0xf04090c05130b0901030503031e0c04050103053301090603020903071202030f0105041b0602010b131a0a080a030906022806060e161407050c040b0a05031014100501 72
    0x10094000d280c9503003c10168008400a02c10704e409a2056803913410001c10400791030140703003409107207001c041d495456504250300400f5680c091340c01228140340ea580c010582a40e030405801c0c26801e01b4021003400901d40b04040000c00000c15040303800701e480368201240c007a0203802540d80e44000940107010203403400c8140644074405030310a82c3c0500030081c0007c120b81081c0207403489140590a8048000710868940117800c0003544003800316407404441d00000d640d00011500f2520b040300d40810580207084c01c00340d6502d004003286038420685007001402c0d0001007820180580a0713150204015030b160026604c8150906250015104152860751000031020310b101a15000301e0000a210b44c58a0513070031a080196118211960180c0c8140b0102e94884120812080401c0b02e44d801c2c60710640d04c0f15a680000f508061186841e540741c00c0150b00d84403079640040070028201c6505004007820b61000b0300122145074001440e0200040a40d0907903041042140e030706035202c48070003840c02d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 92403687 1250 92402437 92402449
    0x3050a08090a080f0313060c03020a0605061c030e0405010f0b0f0c0304270b060406090504020903030c01090c090b03060606030f060a0512010c1211040e0702101503020f04090c05 78
    0x42005502200c480008a4251804c0000085034035541004568401040b407000320b84480c1c0c1c2c1d02c1641017004010515000940c08140c4080051b40b00780007264548030440042c0c4a910010f48850362416020aa4000d00d58401c100c0040d520040e1020025640c0790804400c50078404e02800040e194100039002800048000421018800006803402d05480e1901c014825115001240c1888036110040098080602c28259913076030840b02a8a02440d100c0080d246980f28414113204960118481075251414801c5030200d5a0308002000555418902001d803004c032070040b448005d2030109007007400d040008102d13000d405c0082c90745086070f56102266aa040c0c00802c10354005442000000d000d80b101008241c0e15004d0300c00104540b01079000081124519440c1d0410f85070914884004405000c401c4030240e0b8118a00e081c5aa41c07055004c2c0d207400580d00200d0b1406151103004120385500d211076000341c0344200d4500650840140420040d139003121000340403030801e03174400c01841c9008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 92404937 1250 92403687 92403697
    0x6090f0402011b0c0e1e19020906040312031d070b0d0905150907090e07030807030c02011404080c0a0801020909070e0109030b1614070503040302150f0a1e0903050a08 73
    0x2111100c0000f182d58050460105603c01048100140240204c5d0365840070390f03103084500031003a46440e01c0c012806030320f02c8428103010410503900149440d03158440c0422540a19007058118510310f00e9000024003c100411140e2007808400c5002c02c000038020803018101d4100e07003401c0b070900a0b4810740500410280070b040341d0038407820000461203000000302d1441049648082e0400038980071401c2d054550300381c400446504480c10500c00120fa41c0d00382c1301c485800d4940018040018030060b240203910701200c160a12000c1030001d00070f02c1c00603244060450948810300c0340303559002c01c18240d000300a80c05900c005024000340d03142e4414a0340d8100550140b401030001980c1e034444141d980d0003036a203051400c400d00c0002d1802d58008421303908030041c007001c56140c5080b5490341c43d102e00442c04000e20410040881c000f4104902c029a03450490700000903507a001d0a034000750041e614100c1d212400410807592280d0384d030041004c94100c3c1d400c02c0180a0032070417a40c2d0000907503c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 92406187 1250 92404937 92404967
    0x106081b1302040914040201020d0c0206070b0a1e0207020307060c0305030f09010216030e0a061704030f0201150b030405010b220902130c090f08071503020703020a0b09070e06090f040201 82
    0x42404009907080160140d108517009203000301c100350525000081c102041406890107120081d0824001a15032500f00c0d0700094000310304003040d0703d07030a0f0040082c0000a411310f48001005c40840c01b03920056000701500d91086080b109025581c00040d1450003a0b0071024002c1501440000c09014006030f48aa001e044500014a0548407028007807258029401c00e84c000703001070300c2c1d00701d280c209960b082c00a000d45040044511916102c0001c0a0710000c10040420505401060741070b8000d400c0440f00030040700250120a490f040e80091a80007180c1c161001e40c20407407401801d05091280b4030448030440d440b844007044031140c060140034010800c9800c82401000b070040403e251184640f9070b500c0e5956021520314166881d0345e08015900450f03082c4d0048941004240d920501199005201d800c015895034020b00b41070f4100180690003600c0342c0350280c00c0042004010814206a504001410388e03551110814402100012650030704540001000700b00550b018620b0700302c0c2510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 92407437 1250 92406187 92406191
    0xd02010c1d120a020907090f091803180b1c15060e011103120405030306011106060d12180b0307020d0203040b040e040212010f02070b0a0209030c01080618010b07050106081b13 77
    0xc0783c2c1e01250140d170b42212200006014402c09002c05100415094000c2c808004180414281104000d08000400200406004008026901c045d408444110080c1004040c2544401010030342440c001020403100103500d15080d03542a50743c00480560040d1801c0742d13280005414044015504440c81f440f40c14050310040c426030505040100200f84200d1103000610f40700c2c1400e10000d8180c88440c0802401c2e40c211804106550b00c0e03114080c415160041882c144509207000d040e24081d24103503074203941095a507404180d94142d00d0003907020b4111030b802c070744081260207030480e06d0b4001c84c040d901c690f0354100420050407101d204803e4001d40000c100d008580086100c03d82100c0c070001d020300c1308a402056890074041c12001c80342e0b0045802100b986090301e4600001c2d10303050000400c5061182820200c1c50390345410422440aa42c0524400c00550b15841d00c00c1494004075030407600340d0b0a1450200e01c8410119001441640c10280511102c0c207010400000880700c00500c20095 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 92408687 1250 92407437 92407453
    0xd0e0d02101a0901030c091407050d0903030209060705070e0105010504060801091104052806050c100903030b04020c0105040c1703041205120304120908010e07030b10080f0d02010c1d12 81
    0x1690310f2280900852060224505d250700e490360400c15103000030510500074805004000358580c0080c1100c0c07402c0303028400050070708001c1c5410340082c00b03074201c1076411541c007007016000c0100001e180801e0f0b440c0c004003002107aa85100440d070511482c083e000c0019401c4004010308465500202c0c1d0042580d0003075800e041d202d00201c0d05011182e80c1e070313000d0300b0030410000d00c90400c0d984411018000c18038000313140c002c043c002070baa00c2c004018821102030780caa5030041818407130750214121680007841550b0f03030b02c0009011780c06010242e40a59071503019900001d038502d0301c9030b110410020b298000d507052a1500600ac008558015815a040c1c014540c1407508040b46400a601c9540300701900c104040b05030200401030b402030b03013103000d2581c5000c6032005450700029240045035402468200300340d0f60907003048042110799100301e900b442501c08202500d1404288207003409441d40c000c0101c00f190060803103880b6105824041d030110f080b104c400c1e05081080e800182248079104852003a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 92409937 1250 92408687 92408689
    0x40f02130e0d03022505030a12020a0c120c0804080d120b0a2102030d052a1011040f0b09010f030605010c0209091606030b031006140603190905030d0e0d02101a 70
    0x5c03082800101d03110b410003d803609078240c01c61000300c0c4480e03081008609100d003010014000207040da0001e01141d00c1480c03c0c140f00c03881102a00112580103e40c29103a664502c4000c0e44c41d0340040d5158086080b815041c01c0b0200307548600c2c0c0c0c1c00d9400401e016000b628050509031280003603801795030703052644d15000015031800c204a52800c1c085564240d59031079440d40340203c0e00da46007001000407080c03000c2d4000000c00002e4600102050140000d044600c05000c1105441540d21070341029510042c0011100c40040c080c01c080d00d007c1e00c403408030612011088040351740c1d501409010862081c0701d8070141c01d000d50302540c45a2413604446e102e8980340c004c0d181c418102e612941c0000c1d12041040c000e410f0601441900682c020030038803e540c100b0b01700702c070001d140740561401400007100240e8922610802050070100d0340030b040001a00350304040380c0b07903444403c40c8010f090400c1e404140010000400081c0020b40743d0191442c00c0f00f8401c80304c0500b03070b0a4452440c01681420f40301e11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 92411187 1250 92409937 92409997
    0x303070f05060103140d020703110a08070f26100209060d020c070807080d0801090e19050106050103060f03080313020a170a1205040b03041b0e040f02130e0d0302 71
    0xc03050281004102e0303589949028480002e4a0854419940107501c034580301da6000142070050740c0d403246c501c0b0301c2c1c80e8006011400700d15807944106400d2041d1000051545140d0b240241a0f802d2010304484041c060003174030301d00140306540300b8101d901c00d107254640d411180d4040c280180c402080280b500b580094501c05a800040803070350b068101c0c103004c101040e400c1080d03000505082020b04400b08031000054100c850512498a03803075210031500030345070002d004071b45d4882d0000209510080c5103050150003014036008242c042481c14001080042c01070032800d01300c0394007400303092656071002255000b100a4103012a0440104400824181c540c64410603a41502c1c03402440c4603007040c2804c050020f214032100b4207020701000140040b100041c01c6a40c0960402034000b0b0400200c010800b481c0059401005039818072000d1000300b040c000c507203107000c6000321074000016203092030303040803074110780d020707105c29800040b690310301d58001d070050003000014140503504001071503881c0d50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 92412437 1250 92411187 92411213
    0x50307090b0d02040e090d02072c100518090705010905130218030f0d08100e070c05030d18120f091a04031203150608010e060103020c01020903010c030b040c02190b0402030307 77
    0x9440d0400310300700b400d023a4100b00500007001420903002c001c5403800700c40340c00c904060700ca2500030002000000c00e0f02c0442803502780240700182100700a01c05808080e00200410394035040709000ba6a030008603903110b1262003050740c400422042d10300402064800095000c000c00c1102e20201e00011041d940d010310110303600d00318040103032101c41203041d80104400001000805983d1b5001414400e80e056000aa40d0042c0c0c1030516000711040c908089146008840b072056540e414100000c221110b4120060102071107a812600c42c011f842d20261a0884103104035800900c84d00c40411084070510145102040715221552a140e125107d4a00c0100001002404681c0703c00094085240e241590310040107a4600440f00354181000301d601074001400f0a4109a004034050551135820350458207240c03c02002000200d2007107101401500307484003c00d02c07840c5413120140c03405001060810502030400032105c00380e01555191156034201130030a98051001380100e030002a220300c1642 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 92413687 1250 92412437 92412451
    0x90e0726060114030f0c07050a080309010911030a0b06060a140c012403120e0112090b010302131515020102120c0c070f230f0d060f0507050307090b0d02040e 69
    0x1400340d207006800508111600c007528010035504008005841c4801c021564000780544040c0da03482ca06810710a00c3d01c8034070790000d4840d85001050000400e015031013803010910440e1030b0710040308940101a210764804201520703403100740c00050300501d081e600600c01c0b000305040c103642c9050104124070042c2c0158010021b6030795940003011038803c80300501c040e41d00da03690710584268203603581c42d900804107202d04420f010510020f030703a440e0300540702403810340080142000130390345601f08114800d6082c401039000e0101d9000038229405903000c0d10f40c8903001c4d501034001051904011110040b803003650402155404d018109400d00a41341c1140200034940f18590cd90214440c1c444c01d2407810342c020442a030702800b00300a80c9020955000e02040f007102034040402000c0302065001948170745440c3d1000300e402e10902005000d0340b101040800000d010020399641c0603090380c0394402580c1c0000410ba4148081020007000801040041c07103040025042030b40c1ca0304c0000c00c44505840038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 92414937 1250 92413687 92413757
    0x20f0a05011e230604110a020105060907080603070b070203281119090203060f0a0602010c080603070f050904031202160308090d1b1e14060f0106090e07 67
    0x101003400d0324600000c001900401c0c042000c84029006400c40c110703030a180103103007200140015260703174642d84a017030155641d0300700c1a80c0e40b1040000900800b001c5400510858111001c01e80e030a04c141580d901c10a009001040342c10700341014210381f504104005c9034144075000411508806040e0322441e8684492000d495002c03507850075150b40c0c40300113400c42c050401030740c2400300d80a504144000b142d401e0900140d5070380303e0740003141420300c0240d0310303a0304103c540d00000340203a0f055000320820001d40e80d0740c214503100c0f0000c168031140e2900c02e220340c64118650500c03461070b011a9064109109041c000b225200c2c011700c54007643c0182d802161a501c031501c0c814249904110040c2e0700c0b4a5240190840c40110a00602000701d519840d1007114021002c1070104901d0000a90840c84040201c8240c00341e2490010902841404040d40d20700860b0089102d81d844119264141c0e01c40341c032003804d11820054590043c0900a00c40010805812a1488681c42500000c0d200401c0340ca40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 92416187 1250 92414937 92414951
    0x30206070909050c091309021207091109180702100c0807031a1e010516080301090c0903030f03090c030206130806280506060403080f04080c120a12020f0a0501 70
    0x361580d1200e90048110b02d0600c410801d2048a020455010480864840a064403441426402000ca40c0c00007500070485154400c19604001500001c45018647c02e0000781c44040c811240350103541c2c0000e420400c0c28403c80c00b07c503400000d9952010003032040740c031900380b00049201910311007241c40000c0340c440000d2110403540341c0107402c80300092412070180c0b46041c8c130110300304007110100b0702c00102607051506e410380c1c850022602402c40c0513014a0086c15241007003003040d4000e00c14408410701d00a0121042809130f500881201d405032120a44000008026405420041d5003140e02c58034040020005942e8040a4500015200c810a5803581401070513446d044014050f020f0f84c9504900c00316051a110755100c0d0096041c4c1001f00390340c2c5804001c03440c00d000e1a000200300b8440401d8020030302c06000040d000322082e4038200c500619445050103204140418034400c19000042e051000c64032580f0b00180c115603030b2049031038000e90281101d042095a440483d020394403020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 92417437 1250 92416187 92416201
    0xd11060f12060d11090705132402010603020102030307050d0b0d0305090102010b04060b04170106082e051003020415090e070812030705031803040305011b030507080105100e0d0807030206 82
    0x1e400c9501c41800c0c0c03a5424858200e031280f021103120410001d00c03130319100c00090000b5202c1e00548009032400f20311136500300e498400030b42d428040c08403030442c1b01d03941e090b00500c1540305004110489030180c001e507245441e840011038880e40134207003213034600e501d48030b503070030b0755101d82c018034404a00035501c0c107807a281c103880028251400c26010a2095081040c10301c400304070b100131034080301c04000c82ca0703090704a0300b10094058000c541c40001c190092200b14103407061840090482000f09071700c2c0e921400000510001165004e079207440c40b4a81048042c001030520303902c24020800300c0c01809450315030320784540c8180c650002c1c0b03080d03054202241c04c010301c04040009405022050b66440e08610300328000800d10701004203040850945a9070b80d0081710300600444000d160804000d10104810400d001c112481072000300c00000d2a040000e91300e14411901e89059490050004845510340181141c1500c403081421390301104000f60356001422507001401c0c1540320b50068401450207078 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 92418687 1250 92417437 92417467
    0x5190209090705030c010e040e0708070f0f0b0a050a0e030a060b1516020d020a0305100504140d09031103120d0f1409060402040915050a060e010f0509060d11060f 71
    0x1d0080303a40c9510455003032000d13560114070b00042e4003003882c1204038908545c1c0080d01800319400f14915034018a44085200305000c6015001d9520380f521446140c3d9036a0020000b03602580300314042c1800078070500581500c2100101101c1c182807424004259036040000c0c103041c09601e0445516544011601d080e00b410303481408908034544406040c1481c1c00c1d0124243d0301034000c020310903441e008941c0304560320f000081c005182c1181c1200c1002080c041440b00420742983e0540301096080b001409a00000803012040340c0e0a07907c0d086c2d054695524403481d05403142e065549400380c0e0000f01c100380080e10160084104201020844c103918903100802c4508440713904200c900c4d020104007a05000042590f003060341039500164800300c0d400d112103140240501c50944606040500c08501e1a176009801910400402c61016036030750110348001501e42c0c80f425806c0281c0800088070761a00d60411054140210600f8852040400001e1100c2d40030070400b080004012aa0301d0041c0e10903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 92419937 1250 92418687 92418691
    0x9051608010c0509030c09100e13020405010504060305101a03010c021b010302030105090c030c041203050a09050f030a080306031011131202060313062a080c0a0f1b05190209 76
    0x2801d0513490040700e600402c0d1500490682c44e4001d07080c01c000324001e000c103480c01c440207103410018411b1a00b804401017001c212068010313032103a8101307000840d1a141521421017140e07403044c0203082c0f0143d00c0359414042d0400c011384a199001c2d10b036042015071001e0203040040d41040c2e006d08042100080507050500500000c903041510601c01480702c0e880710350508da040f030340055410303032641d8880888481a1181b500b124608022010b00ca40030507070003401400c002c0001c0d0721942c100b140c589040c00719030700e01700c460198182e02580a69021039040c0f40110b0308500c018098441940300707480a030040d100c05d88203031410381c0000500182c61413130099151003e00103403006400914410340008074a404080d1100000b906200440400c0003520f41c0a0b2071070100d140010345440d91f61080f0403094100480210b40032482400000b0b02d0069050101e461074030301c40d00c0740840c1044551080b96a0100094507000c0c03002500b03404404541300300959200410420351440401c41e41e0301c1801021040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 92421187 1250 92419937 92419961
    0x109060e0c130b06030c0c07030f060203040209061522030b0405240106050708090418060c0e030309090411030307150203070f0c0506070305070509040203042909120d0905160801 78
    0x3d07003200d180a9644282c03ca0f90450240c82c1c031140c40d0302a01c0308081c1400669400140f030300f074140c0c400d91b00300038179a005184114000c8911110340e640384801c1c0303d503a119112042c440f01030100095400d00c0e843c01120460b100c802891f00d2001926580c41c41501b00d070540e02982d141c0d0006085100304550491404881e440f80461100303070354034000004c1c00c01d0140304401012902c011135011a0754032a0350200412410002001c612140300e030410030300078920325406000164003002e10344050f050000031030b001564007030140141980e99845080954640c03c0005915000c10006800460342c41e44a00c0c80c148130301d4000596038200b40300050450130042c0d03001030501c00015150340120b000846e0083d84a0301508010415540e0142c04650f1485103646459106201206020038007200e0880740d4905003ea030703070100c6900d05040c003c00140200712460605a4070807910b168030800ca05001d4104c04242170b202180444680d40d0b441d0610850b41100c1c5a18020003800704a150024040e264100003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 92422437 1250 92421187 92421191
    0xf1b02030102031305010501061d10050d051303020d0504030206030c0a020f0d11061e0a0b0604050a060e0906010e0306010312030921080109021c0911030304060c030e03060f0105120109060e0c13 85
    0x399103410ae04280021158485c2c684841d114010b64000d60499040b59103c210801103450242c3e81141540203140081d80107115008804c1100d030301940440d0706a075001000726045944110b2182c003282d11805038401103000302c1b100b4182c4100100040301c448411921352050306041c2e45000351400400a0041c1441d000680c100b116090840b14965000713092002c010403902c5503000030800ca0301c61640000d4200c0c0140364005502030380720303280c280001e40c110390000454441c1401110103000180700c0540c950030400040000a0ba550582900c03002d80d030402168216080e104c5c41c0c0380c1c03400050081c903015041d40901b11103d81c030800050144c05800d10460414108140e01030f4140342c03203000321700265070341d090301000c3c00001020f0074156900101203d90b215210a002442003061001c100d0200d03144a030300c42e20134600426024401c003690412415103a00e48000c1200d80250110f50302d1555503101c81400202d1950701175100340b503030400700802d4580280c5042c4070702400382218210410b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 92423687 1250 92422437 92422457
    0x501062303070e0f0d0203030f0a03150311060c071d0a0e060702190c05030303010303090f120302030d1e090506061e0f0603060111160302040f0b010f1b0203010203130501050106 78
    0x10780c00840100a0f40425541407115000c11004217100381c1410001962501c00842d007031401000c11002412161520754007480340c00c44048082e6021802400010569244c0704640041c42c1004005429850703490b2080b102416500ca56000649400c0c0c5645841704501c4000c00100e112980540d10143d0040340c000c0c102d03842c1c580300c004d40b04c40c0700b519003100e551602022041031110380b018100141400900780c0780e03696960f15001d02254018070511881c1440754000161030001101c5c1d000b06950560041d5290894003c0c0000040c01191450446041c1600081d020300f1910702c01e211405110304014660341c1845810000c51750002290440364080100c0c3c0004103032940b00304441c144800f81d44881c0ca80e01d400d030044e5240c1d006441540c01c0c52040044040f0b01c41100508403040301d0003603600b0080c4130b14410441e01070313904125040c0d0119611007000d80360700f4422424460b603105000d05100301d0303009a0380001c2c2a80d00039a443d030010891000103e091200a1180600600260070204061 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 92424937 1250 92423687 92423701
    0x20a0311061b030901020d050c030a0e030a050712050409020a0305010801201204080702030f24070512040204060504020a120e0d0c080307030609050c0309070f060c060e07090501062303 81
    0xc80021201540d0b140c0d00480411040034094060340d01c0c5051091060000f807820b440409001d80041340d41c10440390030200e81543c501c1c0f01208454101c1499528645059915240c0d41c0c2d03552410f64101e41004004c1100103101c401c2440a0400120140d6020619500d00403501e42035904804c03480d0b09417043c0c8000b0300c1711380010000312003a24480c1d01e425007141c1d845003045138050145100284d00340c0101e1403a0000998049100f0307415480c00c0144813007103280481350345141c0303004980c00303004035400300b1466122040c06008140c2c0588022f0000ca2826118004601030380c0010304400085480340c090525001403d00460a4040398580142182c40c446200181501c0045c41c1c041c04507200000481c0c0c0329403107500f203c0054004000c050140d030404114040050b8000c4450700756900580704041410034109103030404640040d5109060b009041c1c40300310003484641b4000c1201c0c0308030480091079082c14001c2c82d0007800382da194031400600d1800c400c1c10382c1080403241000050100108660 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 92426187 1250 92424937 92424961
    0x15060405041a06040b190e01200c1f02190203030a1215030807060507090e010b0d02040305070909150203160c150501090c0207080c031c120c020a031106 67
    0x403900111400700d2821a41c10744100c81206000780d5035000000010081a90110940205040d40656000300c41280711000c0c1150312500c0c12040f5400940503c2c01407110404100d813848807180b428003602c0034800c0c1c41c80000d004104a000741c404100041c200020f00640601041d1028003040c07100700d001032201da001075113034421003441e03070180071a0821b04d44003e0020342c44501078180d0301823140b003500c0e264207103640c1f16004079904036411783c10480000e40580c0300701014070443c0c0501c2d034040714036420b0217003c1001d900290b020101d9507509120000108404000c40c41c010056100000f5420100d810040f03502441140c440c04c2050040081c0004c0e10381507134101c0e554126034542a0703201c0c555407402e11200d45801d180c0340d10550810b000424121055400224440ea0784d408a8012903074518035a81c640d10601003081d415046001108024000290000e60341d6003a40342c52100e02071490b00da8030407100c50017800c07030060b403100040e00209600b0080410f9414141001403009280a0031800a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 92427437 1250 92426187 92426189
    0xa0806040506011a1909090b0612070807020c0303042d0305070b07110d030206071209020a180e0a05070504140f060112060803040b030907050f010f05071a040b0a05150604 75
    0x81d5650486000c400ca070381304182511046184001c802600c0002000300400c500d12900a02010510300601c0c40d00d03e25012044480d407255070015880e2179600ca08042d51011401040754040d80075009003202a96011300c010320160001c0016222200c0000b1030a4185008084030a14400311821051000c0b4030000b4500303007191185144981d84881a1511454075041165082e41008400345140c04154000c902140300780461390719540184030405a0f182682c40c0e0070b0010f0340141e46c00078240701030040042e0055030307020700c10404110504d13042005844c0c500802c4003031300d060304842000e124524140c0165042c01011100d001202c1c10a10f05071046120007500150501040001c0441040c0258104100800800c03054a0b159981c801c0d100c0c0d80c9907c01c45d07140d05c950090400104151520320303c0120411010382d00c1d140713203e45000041d62154400c0c9004d94600e01c0612045c40d20032401c107181031240e841003182910301e081010300c0e80b00341d841c0a800b00390041c0317103440100705a44417082900c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 92428687 1250 92427437 92427449
    0x5030403121e0c03050603011b0c082109030408010e03070c060c15020d020c010e01020a05090603090f100903021b030c13060b040605070c080d080105060307050d0c09050a080604050601 81
    0x2074203030350b0382c691100b0102419401c60301c02c2d082c524404051078040d84182c3c0708040642c0203200000700e02000c000c00306000700c0d40b280801c100c5607001010480200207440c201c26400b01c010b40c501c01441004000050807205415950700000b000c2c02100f20a000e45041b0140d001e00030b41c106042139490380f26908541c0505020004034400c1c2e5401c0c01300000300008107940450f4215a2944208901c001030350220760601c10b9903090101100c212201407089406150030355940d5814039000d44200000c1e42e101034507031502c0d4400c0c0020391040d1042030104122400c945040015a442d25160190812107110b203d00d0100c82c5d100300501c61a01c02150700e0603044800c03960400030a944030000c2004140c1c075000b442000e0300c081001314245da041070050644601504801038200d560f101300e9655510b841942d0000142504010001810050044c40c1c010003141000c3c1c0c10031110f045000100ca440e02420000220039400803c020300b004403c440281c4181c40180c00c451a19480d400d035039003010f1043e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 92429937 1250 92428687 92428691
    0xc0503070303021606050a0c0f090b0301050f1302040b1305040c020604030809030c0a0c06021203090703020d020d0206030712060927031b0c0e070302031501080a020d090c030507060503040312 84
    0x4d02c105007880359030140b5036100b1303420070550a24035407407401042c2e4440d03d0b4012428070428540080e025080c10f908aa0305810399a1660703080c00180030045411021558000c2c481441c59140442580050800341c0050040c550b107505035555820001034060f4480e0f40600d19008008403025404500c0c940d01c1030b014103088107035455401d0900e2440c41600c0007404140164a4074004026a0f645e0141c2160400ea00b11541c20104018054091000fa540c0d40380c1c540c010300d0200010305100040044507800108481d100500c150082012070744121031010016040d0a51001060103070700c2944042c0075003907420085044000c481501050030a000b908110321420040b0003058420481ca9420105e0352100d900e580da010328040200c1e05031070240b580e10a22510020b00110700c00e2080d640b007007120800c2e541345000e43e03d0040d1001c2002412001550380c0802002010301c2c118050140c06a10480c92000308518504005003001141d4200b10308020081080c0408aa407000113034685079050240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 92431187 1250 92429937 92429947
    0x905090423010906020403150501150c0515010b07051506030307030302180a0303020f0607030b0f06030403230901081b040b031e04060c0e10050f1b03071b060c050307030302 76
    0x1030081d8601401010404643c20b0110740f4082102d1038014108030303403180707007407004424080401d00c0c1075032800d000c0e5010390711861414014051183c40100c1001e4000d40564120080c82c2008810381d030000d03000010006000500e200401104024001c0701d140140207940c42c500f40500025100e02c00c3c624050109500840e08510380f03200c109149100c8c0e40f00810144076079540e8940a52946800d944c136450902030800011031040c080d026505200c2c00c002c0000e07040310702200800c14903402c084c2064081103440070340340d1240409402c268000b00c2020201035121620280010500c80c401040003170032006201c00294403402d02d005982c21b681c401400203880380d9683e148c20091405462a00640c0c2080307005000a000060f405078100c0c0e2241c1d510010408138180920612444110400d00011010803c00b894500c0300340142c100381e22594080c009004c0340300b0200c2d256800010f020f4a021001ca10706a4003c0140c2034080c00500d001c0c1403141445141c5c2d1a03140d02c90040d03200107018142c000035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 92432437 1250 92431187 92431223
    0x150f0c0304090c17010b030903040501030c020c0a0605030603070f1406091206040b013822030b09010b0102060108070306111b010606030f020909040f02030c10030c02070609050904 79
    0x1510040c082c41e0314104100c403061440200000d5028600140f0303100d8210000c503211008100726071003410440d0046182030302e04001100100790400001d4214041c290b07808803666140c850b00401042e003903031510303144e0a01200b010305080c1d040e402a0055040e00104102568014121450000003110450389a0f4060000b041c600c0d44140c002c014240600310401c010008864000340c143da041103103088681044a003030210030625400b4580e4201c5807101c101c120085e400005010003001d00481007440e01c051100b100280d011504100c0380b09034034a04103c0074240921070207030ba100c02403002b041e50303514100d015629000a400302400840d01c03001c40e482c1d07946403c07007140c2414441b090100c0380202d07071003410350013400b06001e40c1000906020900d16a031001380242c8508440060240c0a16100d903564150403a00d60907080740c050017002c0c4c0c000301030b60340e00c6244c2c4034011341e5850115000d00304000090805000750856001d001c1c400805000d1078880d0702c0e6942d8069030000300440204401c0c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 92433687 1250 92432437 92432443
    0x7030806210313090c030501050603061908030c0303150102340b030c070b070207050120010b0d0b0f060109030f030509040b060f070209060406050607080f0708040306050105010e150f0c 81
    0x41d504607140320014860f2024000f010300c0c0801c945281d00c0810804459240031015030b4028858160310100a00126907130303240810312043d8003800014075040c1c0a54400c501400d41d041000402c0480d040441000802ca00d05400d0040050091002d4014039881c1c01c542005208016040340d00261031440c9240102c0340522000c028000d0740031826260716059049a10315408100110781e58071904010450450000800c40d05942c4140c41d03000c00c0003541e59881d28031805103800300c8015902c0782d502e281c00d0b4607030340e890b00d1015000d20f20a10071441d01c0420062044009007945041191000c000c101060050b204021402e501d4988a40d840c01c50100041c054240c501085500c81000240b0002c20600d000050894070310030748150380d20369250b42c1004222402ca1040e0358010004100c0701000440f8030005144482604c80250704081c000d440301e00864105400c2250305698860041c0002d681014124407940701c200c420000e0554805002102e500a002030980c050902060b113240171007041c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 92434937 1250 92433687 92433739
    0x403050f0904050f060102011d0705040c0504090f0e0d020a1e02030c120609010b01050c150c071410050a0b0d02091e150909030c0a020d060605030d030c02010c020307030806 76
    0xb0300c244914240754000f400c02c4138060b07410302d0240d0f290000444140a90a5844150306261805400d40768980014800500741c00c3e04204d040110401c4007194100052103101c1c0e040f050041c001516440c02d07130040e444c00c01820349250540d41700b500c4020015584191900080701041c1c0900039104503440401e1a110030f0b0350005610100001140411480016205225000d024020703c014001d900055465104100074040b9031f8000c00070075668100c014030029085a101040e09282c43c04544a0440ca002c030203160241c0c40d0410075a10130051920302a8540000c6c51000402904506400080c030001d00e5000c000e02450085000030001c000d2492248a411100c5100c0100c0c0d00c1d05541184404090700d11051003020800046001014000259001c0000f0a00108066201ca0b0204170010080090441e6981d03250310300030600343c80a2207050300c6214180c0340444c1210b00d80001a0940b10150001c80443d48140311803004030350b120f6512034004d03400b503400c00d501b84100c00800c0004030030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 92436187 1250 92434937 92434939
    0x1505060421060b030f2b02070902210a14060108070507020f060c0a0305040504050708090601030b0a0207060c170c03060a1412010c21020415030b0a0e07051806120403050f09 76
    0xd2a1017860303980300042a00306d801010802d40410307070006010641c02c4d20b0892125040107900c07441082c0120380a65004084034003c05184014500302051030316401b840460b01300d050703161100212824001e01d011151307044013007428620024940048000c084c0d00500f00041e10030002c0700e40b1041039071507103400c540030440984d0942d600341c1c4003401d024006900030f1240d41e0059181c440010101d91050010f640240c14000282142e40d18507214004a01c0000e00a1030300150700300000400100c051051200d502c96076146c0c00489400d0310340d0880400303001030046801c010304104004981c1d54990300c40c416034a0307042c078441d0208500c46c0450b450404482040da060762920141c0600e541d000b005246046608090034441001d440c424001a40264450a84043d05111104145a000e40c121030301c030050160034000d0040d60703007411030382c11a0140c8044000ca00300081c0c1510700903c201a1191100083c0c2e042c80c83c1140042c40001c0f803480060000d4208580424041860721060702200c2c22064 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 92437437 1250 92436187 92436193
    0xf0a23010618050d0809011805091e060411090d06060b0708030f091c211103090706090503030403120c080d050610030b0904030509030a060f1505060421060b03 70
    0x1c1c48000180c101e45481e44218622030807a030340090a0320f04055410030341544000b44500700000200103469424240c415420718880b111004074882d158041118810508107a0040a00d2491501009c0390030014190728012350411503030742d2007002c0c0340003214136200781500d150000030350742c2c28140c001b0001608800100140011440c06002c004000f460107140f1400c00c0c1c1c0c1254440d0038096907107000e01c0000e004404032400a116010f0b001e400014925003200300b42c0895021007502c210115220f4480c0c604100101005010000008215a802802603414501d4209060400180d941d020b2403000500343c3c485052101c1c00c0c1c51052100da0b4010b0340c040b4116895124100754000608000c0341e00382d004050038000d000c3c580c2e1090213030541c00d50003e40000d80c640c5451b18110348640c0000c035041c4c0c06218846104001403580d119a484462032030a0000344030401c004648011145a8042032060b02c0a0205200c8885d0780e4031024420340152000c10320880d0a0b2802030302808140b464281c1c140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 92438687 1250 92437437 92437439
    0x4050a0215130f0602010e0d1d06090909011a010c02010221210402030d170412030e0717100213060305040606090207061e0501060c0b0603150405030703080a050f0a2301 74
    0x3e00200c04a02c1a030307840b90002d020625183e0400b650f120700c500660b00c00140754550755403001c040480c030080d215502602c0f5600e004101404031b200c011013514882c600e6036450b4079000310080c2603441642c0305402482c00c820204001d0300001d517036404980b440c00f40b10b9035a00700681c0c10307404c41c0100c0d400c80e401c0f40b44010800c80c0740e045408440b401102d0507030080c0074401004000038800d000284484401e100c06062544890701c4441c0b0301214181d291007031507591402c07031382d00030802c21003031004140c088619509070070020059424031880409405200d40117001c50700c0400d01d003440c00780070780e85585800100d540d41e60801c41c000d01502d510014104d4800a80c520a03c10250030241d858603e01e201d075485082c1606e4800e04440c0d09203c0e800000f0030010784440012440400e042d0084c900404880c00b42c552851640d1502e0802e45013221a07500001c0c00b83d0404d9080f04c1d80c10343c00800c80d0b034100710070301c0d02e001e200d0313140440100500e001c20380d40c0c902c03c07411000c1001c0a9880d850301c4c0e00328006035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 92439937 1250 92438687 92438699
    0x6040914030a0206010501030606050d02030702151518060901030b25090501200c0d030e06040e01060f05041a030402130e0c0102010f0908180a080a052404050a021513 73
    0x80c0d446002d42c1d90050040310004115540680621011500300b07903521454510403104000080d00064051001c50085400d06a0540802c0c07a185005000d03280003400c0d00c0748090204461a10440140891081003804014060384c0b00d50b00141142d400500d500303a16510440d80c08450000e524100c1101981d860a66035420351183d980401d5030f41c01e0300c44c031462140130204d034100004100901c008991100e516200d02c0e0521a00c0320004502c20706114610a10b04000110247c01c40d811150303010259400403c40c40754801050b02071140181411498a030504464240c401160300000112a000002180464031045075141c40001c1c0410100806003003460004d40303880064101343e0041d82010708103c0061b10b0761149160055001000c0d5180492080c072450f440325225a140d0f03401414003000140416043c0503100071144524041d04005c044450a500008ca110003c5078035860306000304000110700080300d00e600c1d501151601d40030768034220441080d12a10b00e0b00340300c504c1409400280 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 92441187 1250 92439937 92439943
    0x6020309030901031404052802040908071109010b04060518030303100e01150221040b0315010810080607030e030421050d050c0307030e150a0804050c0301020903030904020306040914 80
    0xc204243e03820301100c0c400c00e030400c0c281c0c5025200540560080c600001c11390758500380803144050071428a070143d070348d01e4001038221030b1014000d4980c2039000070305008000ba503140c1c0719800c141c100c482c2441541411035940d060301a900030602880700c00180e2055004d06c4140780d0000314001011a55640781558444900c0001c0340329134981144080d0011500400c01c407051055005c0302c0d40246042ca9590880c2002148000078040c900381c8100004218140c10130700a600c07441d1500304400c003620000c070005041c0c2000a018204000e06004140280f001c0450344a07080102480c02080c0c0103241c030022402d610807980090b40001212500007055090148469145030040f0140c0d25100314250050ba4248204040f1704000d400030040d2800003802590480d54414005e00a418401840d44c02c800b825400441d4a0003c00c030130004110402c04104201a45170340282d009500b025446e8001c25680d0050b00d000c2d600c10354011001030440c0d1696400000a180c102e81e0300010709541a40c01c0780c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 92442437 1250 92441187 92441197
    0x801020703080130080927060303040e010b0306041407030e10090b0403140c01020a050712020c0604060e03030c060c0306100318020603070e09070504050102070915030f02010c0602030903 82
    0x201180c2420b00000d80c000000310a400120340038403d407110540f1040c001c2c5202040200c0446001405010201d03180d1200010440200d070012280114206031500324000200c0c014101c600c81d0b07004001c18403114030b0001900d41100d030000d00321500c9485030400030380a05103510f08402403400f880c0c100144541c0c0f5400c260040e02d40002a1182d03914032007240f400350f034082140501154211008600001e2003146d03112b4600c0048989241000981d219031801da901140f01d24000400c0420003505011403180c5c801880c1d0341c40e000400c2010844404207003203016900c41c0300244400485c0d41c0c0e0784c0780ca090080f1104403004c4420340c2d0051409a0300761100303800546406008004101000340c4941c02480344114400b410b9044507102c000f90303170802110361b20091100c020000040b15022840d294200c903240104400c2d00e85540f501d0801c0e000924251360707613011108403800c0050245283c2190000201078070b0308000d15032600300040c00140d82c0314565070b000410081c0b00104010b240d100200143c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 92443687 1250 92442437 92442443
    0x180103020705011104090b0f15030603030c0a0302011406120601090b0607020a1203140a09090216050a0f03020105090d090506070501060b0d05010801060506180904020103110a180f060c060504050c0a08010207 91
    0x110b8003003858140f151504c00c00051a0304009e4058440000c3c41e21207003c6e650182008003100d107001802c00c166400c002d2015000c0700035039120b081c0c82d83e00c13460b4840200c1c0c0c040401c0d210f02c90b0131240b4a0080d6542e44041c82580d04c01c45e80e881c402603035511400304507200d10341c01500110710300d1f84d940e55801d00c1106040090703000454440d240d000e50303021706045921680c020354034680e2003400c0105020003507200078141100524090385404c0040c1d010700420710002c1c0501c242d411032803042d003030181c2035404c01481461181c0041040c0019250004030081c29244266002c1d0f0302d0301840d280c02d900508003600586407282c0301040d4a016912150401c40c1a40e189000030b0044954503400e1140c90f010700c2001d440070341e031500c50803c3c5504000140c035900ca401490f000c01d02c50b0350780c19012425400300300e00c00300090203001c03c4a5000a100d10400c01404130101c8040100d1030000020030310344610a00a041c240c032a000305092200400000d01055002450120820365821440f4004e601102c2c00b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 92444937 1250 92443687 92443691
    0xe0901060c051203060d060c030b03010e06060a0b0d0908040e09010f0b01080705070606030c0617090d14071104290109140d060f0509030c120a0518010302070501110409 74
    0x460381620403035603009410380c084010a102c50302c01d5200d0003140c00003010550801c2c400740188000c2115401454000c00450724001070500011041c1402c2d6441a20303c0e07141c1e50702180c240009500c1d650001011149424045600c9a030030100b800098400d100e00608050008500070440d21185541c26001d038805100800c540e01814031034030281ea03600c0c4401400b0031850f10000f0900e03401000106a018402e10001826644a6071030000c42146604503a00045c2000d214084070b00032940c001e9000041d510081c07150311140d4038003d2a0841040304468104000301d0100d04008002c545820007442c000c1040c030812a00c84206114040030514080c40c04070081180c411039409516418107840100c0d0721404201584e200340b068802030039600702c2d03010b40d49540110104449200303603409141a000035592310402030301c2c0c66180020012107100240410001140c4258000c01141c84d072140340c0e10080e440c05075020040c0c0090241c136030f000e001795007884154861146098024826905000c0f02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 92446043 1106 92444937 92444939
    0x13030e1e120102041d040c030609080c06070e010807030e10180b0c0304120f05030f1003080c0a031107030807140a080d0504020f0f01020318010e0a03030e0901 70
    0x1e01903696010900b0300c81c11018070403c6241d00781802800101d4101600c0d0501d010409100c024102552884040100120304c401d0700c03820441c8000740c03140e52914080141801c41ca4447d00c90005003100d00042c01140244a200003071100b190091100141c611503540080000c40c0080c80700c81d0700000302c807002950b50f0a00d244200d0381700540b00c2c0c50381064034040c00d05103400d015480501c480c14510328411580403096980c80711200c2242007064903100b980c00c0d50285290409071544100103903282013802e0018000d00f100d4820341c3e0704000d00380a044003586440d0980001492131200300207100100368030031902000d2b81c181d80103441001425956100c0c081e1b02c50924100015180ea08020540c81c16070081d00500d801600c680104441c9580000e49a10601c00b10200703003002c0c5c082d0701040e81d00c2019048581c07030f4044d02c5005169202d05016107040600715441d4414403140c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 92266187 92446043 := by
  have h0 := BRFrame.cov_init 92266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 92266187 ≤ n) (h2 : n < 92446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
