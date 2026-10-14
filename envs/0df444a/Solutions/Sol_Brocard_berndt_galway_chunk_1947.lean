-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1947
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:15:36.454335+00:00
-- url     : https://prove2.me/submissions/0aa8744e-0c11-45c0-90e2-42b2cdaedec3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 350000000 ≤ n < 350179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 350001250 1250 350000000 350000041
    0x4021b19080406032315090a0b01091505040b120103120c050c0f0406151106060906100809070906061115190e010b040507090603051530010608010b010305010509 71
    0x125881301d14601c0d254603018414801c2203c004100c0034032420f0b52446c00301050740c1b6410303100c080099580d80c00b040207581100d10083d012a12603502840031040315186588070030603900b80b01d031034141e44140d014890b074004180000a25041e400500400060840140d0f0104940c07412104000702520384540320800c03c0ca00c036100e0700d5010640703805603c45800510043c03c2855400c40100d000701405402d80804410108540c0070301d200068840ca03000d120305014080c043c203004c60340300d4910420717282840080c218100380e02c11010001240b41603800303030001510403179540e521401d500c1600c076441d02c0300014129041d24421010005d1558420340945000c240107200420460004001c01d0f00400d405e590341c5030018108010404500d0700910780781e084030101d6804210640c1c0c3d603d00e9101003a02d104410781c3c408100105c1d1b0b02510000070030f180050170000c180c460914450b110351800c5452a6010454a03510f80b4451603041da0544103103401882c1c25281c1c06218600328030030700700c0d00c50003410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 350002500 1250 350001250 350001257
    0x6020d02160f0b0901020a050d020a03200606060f0717071203141906050301020a08010807090204030b0601030b01300c0201110703110a150501170a260904021b19080406 74
    0x4484d40940e1081002c02c4c10300d81c200083d111619007103e8001d4a5030020b900507004a0740842c00c00320324664001009420b180ca05014003421f45400d03003000b485510101c10b03504c89110a10556000c203072070504030030204480d8000640c1d254024a00f43d84030080304003070341050610307014042c6400b20300203a02540c171200448422038208800034002004000942107990151b02c04100e2020f041c0d0015051416140000301b180d4282c0c2d6228498002c1e8030450000800c807030584404904c03294082c3e041840c09581c1410060091544900051418890000c80203240900c440c660b0030101550701c241d240100c884d1000380300c105013100e50914144200c00d00281040011401440c2c460024054650410351100a030403841c090002c1c02406864280100e914548154038419009840040c0e03002410758085283c1c070b0aa0000700c0c0c00c02011f0541c10f41900c400c0e500300180741255070303148014007000700411080c0c05203049000c500b5150a511481407031001c0038412041000c2286841a40d08644581c44c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 350003750 1250 350002500 350002507
    0xe151503070305030d020406030e060408090108060a0510020109020f03240a110c100f0204050d0b06130c020708060721050c09040207200f10050702030309030706020d02160f0b 77
    0x200424603040d0310354400340003804007140746035000300990024801c8401c01d580034040304850351030382510b421003603c0080c00020b040110000f19401000d107564000802002d5884041c0c0d5078000c07801060780f042500005275513030101c0f20708500d803140c841208564164014000f45d0028680840c4039156180441c00074601c038030000b1103586071900b241c18038006038a9a41c1c0c94500c4107140c0b540d11001c0740301c0c41c442281070899034602d580041c0b090f00d00700c58004240510700c40d296155102140c0c0d002d411542c000c60000d141540e800d00c0ca004114001002d60b000305011844c180015090003805841c0100b0400e80d0005c8154200b106426000c880890010028417501c1c2d10300035001500c1079a01040c1c0241c000b082c02420b00488143d80410340d0140380f4108204e03048001082075000e0400481c9500106400d03140c1480780c400c0001e4034400d84040e04a03071400c0c140000003854460954003030b20050740f2140031030f01d0695040c00b4100c00d00507450150800c1d80e0410004d8011800303c1d00410305d017140c010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 350005000 1250 350003750 350003791
    0xc02010c02040603020d050d020706031406010c030e0907180504020a0503310f0b0601020c010207090b03010216141005150409050c0d060b010311070203060408071a07080106030e15 79
    0x3640820000c4d0b500401c0c071808540c03c0d00d4802e803146854601440940180100014030601034000e0304900e2030040c4242c4000d0784c80704019206070040d1107058040208807802c0c480c1c1612030302170f0540580c119440d0300001c041085540c05140e001908080e0041f40144140454142c00c04140da800071443c09078095400c20007001d015455441042e1440d042c0180020311050100d000303901c21000b405544007400d141d13101c0d001a03a0b6101124402401607100c00c1c1c0401983c2c6c540e501c01c1d0b8000c50011f0016160007080c40007244190201c442c1a23494400039042c3c440507180403c09403160b440f01c6141030215180c0441c1d0406140035100016000ba81c48480310010008140401124034000a0862804500d60b040c8000142400c01c1c5035804031307190900d80c9201c06041016a440198014010031640c1c0d110b9070b42c03440c150064a012601c914001c032040c070700c1d00c1d134800100780310350802d598042e071962500b40020290b030307500b2480705803c0e08500e0440b07036038a00e166103030340d4004e0300d602355041c0e1407101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 350006250 1250 350005000 350005009
    0x51f030812130b0115090602010917220305010c031b0e0f1804150b190b0c0a0203070602030a02010f09120f210504020a0803030c0307030b01030b040c0206040b0906070c02010c02 78
    0x118010001483c240012035000c030701101e800703070b6581c15550b034226042d00c811041e400c80f4405180541101921007003002c10a500c1002019990303121308040703a124403414024044e010480d001118581d4640c501c00c0291030f40344c0700300409420360441d94044445522006400c283d01e1240701802414580001c00907520307160100c0294127030b000c6501450340703800d0920641d110100c1e40940a42d81c28800231041034a814080d01c0c0500d01c2012904401c079180108a10300759002404a2420340201110400540e07810f01802d002021590041d40e0b64011a1a000f4211401400c8540c03140345050740b500045924452950742d04002400e20701c3c96a07401d41c07800e5a600d400885140c042005003001041c00142c03680103240103500c2030300e000380703d540c496503280e032207000813100301142410600015030a688a0b4005407241c80d01070400082000d014400700f41540c7c580c000000241e4442c0c414081040000340c03816a00800c0e1501502e42e9042c180c00090050140340c9000c0d0400143c020705c00150b548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 350007500 1250 350006250 350006281
    0x90a0c020c0904060b0a08210c070510050c010e122205310905030324060d06060f0f0e040f020c0703050601051003231e0a051f030812 59
    0x40c014845600b40c40c10f480c0c054080e1001c0003d0a001d03226060b40041e030400d00142d40c12550034201402002003408020941c49a00860b00b82e24007403080c0e03000000c054403030440d6a4800480341d51410b0303407240c20500e81c0e401c0d198815260000380e4082c8010303101d0190803000356007400300e81d01c2c0c44162019452440340c0d58158160048c650010005e000034a1485400c0c682d01e0700340c42c00e00c0706021f030b100d01600e190040300c03480e41018225410800019048402c0b504000c0360740011714400650f000c0e42c0b800030501541000c40d04040d225034944080c85142e4015101000200613171800d4130300c01c0000100100b480d980d4103200e40c085c0e900e0f4100c50500d0744098040d500c00000030030464049964900b011680c80a0078800c150180041715540300002d8841d00845500b00b103901940c00d800d0f801080140c149581c010440360b007062944000e609403c20320b80800b4000c5900a0b0301081908084140f140d180d42401d441c0060401d1400c4100001400c880507a0344002070440100c0d1207581d078400143c1040c4c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 350008750 1250 350007500 350007523
    0x13020a05120f010c0216050604030c3c051503061305090f0f0307120801230409080a170604140c0304050a0f061e050c0d050606091804021905090a0c02 66
    0x142040d02560000d54000303005d5003140b07442c09031650000c0c0d03070707100b4050703d80712701d010241c28003034507042c284107103020415000c0050130b017009407000c29140710301c3c03003510101d100c0c0751106401551039027000300d40f918081201d11019180001032940c1010b80009003001c08541c0c030003051325241c20000746810402e02200500f010494195084003408032811a1a42c1c0035210031a003070381748200007011542c420034405060714041d0509a41c03c40d19854881d004207000301030154010384881c1900e0019014130b0250070310301e481d51600343c400380504803100c0c41d40400409039030086d803510014186040e03400c11f8564120040ba030441d81d403501c403402c086060580d10131004d0540d604070150b0300101312096020350701c00b28034019850a41c2010f4101306041d0b170015150a2550310040c450389400710907a502164011f0002044980340803140004612000b182c0d15400040c00c4200d410401542000c0a1490810051003c0780000c44d0034080041c855581c0030b4000442140e640e178604610500812580e5200c0e0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 350010000 1250 350008750 350008753
    0xe030606130e070e160f14030603070b1c0e03030915060a09110a1206050d02041a090106020d1403100b030415140601110c030d030f020708030c03070813020a05120f 72
    0x1511542c068403041e205031000c48440b00e40c1e20789005c003d445107402c10080281a501c3e60201c0207000300c0e91401e0b82001d080307035602d8001c6040c0007030f160a45000a015540c5110b80184421102039250011034045020301100e40d0400c00c10811205401309143e07502501e85000031569403580300105003500c405800500c0218a0180c81c003a035440d65002030300404000e40d80d02ca8502010103080f2042e2a024480d0503000f40c50b03c1d40321001485d043c0c200700030070a10400e10442c8420248005000081d0a0b8413210242e08400c40901c1c400c0e42c0050317241010000400600e02d036050480010180380800d1141c41c404810201c00700d4200550040d088500c1f1040800900c040c030350b03c40340440008415222036007c030b112400706440b05040400d80c042c01110003000340c07007170030390880050303019250341c2406109080c0c0c04c20ae52000a03e180d0041d501070f81504005980703d01e0000e44c00f4003c0704026285160800081c00e0780c000581c1c6018022050340d1301910103020840c1d0ba9019103181ca420b400c84841c0301e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 350011250 1250 350010000 350010013
    0x14031b240706091707051f1b09080c06090a1a0c010c0807090501020f070501110a02040504060903031d030906070c05040903080a0f0614060a050705030a05040e0105010e030606130e 79
    0xa11020b900000c01890240c000340302d0210720015940d050348948400284141c0101c001f00804869080f41400c1d9282c602034007080c07001c141e0160000c0d4554103859000032504490040c0300020040003c03035800003090780d12074a080502c00c00540c0c1d0504600c00d460050341c41e000e80c2664241010305503404e40030464000e2012407840300000d032074403d045480310000398504500140b950310014010001c0480d18015018042c108401114080e50000b40e1401c0c41c8190300160005032164803629210b240120800941035500d4640103080d034555a40700c1c0890000d40281c00940480441151940301084134000d81e2545103103059840c40343c0c207600040d07020780f8041e10242850b41291090380b00f00d00c4260200155062120f40c0021a551802020400f07810090035682d40c0c14010300612064926081940c02c25a0f10740e541d6103180d02110a400020310042410001e0305444807241d030140800b4284102d40d642841c010950301c40c002815070b4420100d005048080e1001e030740c454294401c18a044d6000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 350012500 1250 350011250 350011253
    0x80f0a050f0d0b101e0e0f060c010608010c0e060a080406180803150301020c150a060f17070e0115080402040902060a02010b120a0f02090702070509040c14031b2407 72
    0x4003c8001090300400404545a1505105074001c4100643c150340d484141c9001d80c100325158005144055000034601c044001241d681402404820480701c0011464608000c2601d0030741d1100ca40842c00c0c0708180d0319a03031080d600c581c01c0d01e5010042c1e10b807515143d40c80c3c1c24560064019070820403030b9a103801c0142c1007441803220085202d40741102d03c21102c1c0b0860007c2c0350803840754210300200c9411182c1418540300d640e01ca515040f0110300c034080380340c42c0c4807c0c0c1c0e540700c03228544c05403002c05850305c0c455000d4030080c03180c4c20052603409040c02c4a503240c03592a900e004841d07402d2804002c542e000160441da515485a10150740150506486004103480603000f003040c05641485161160489116203400040640302168480a103180ca96581d1f800d105031010060403400a50041c01004a03a40e00c54142d0135225500905103111294541103214030102102c0c036020380240c001c50000094004400c8a084000d20207640c51000101a03040d07440485107020280850050001130200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 350013750 1250 350012500 350012527
    0x6131716060c0b130b01090902031501120506010b1305010e031c050406110a08040303181505030601110d1e0903020a0b070c05031b040203150918010f0603080f0a050f 73
    0x104158428940585a40c4131a000324202030014240203212207601d05c0117000407040d940203038400c14070213022900001404020b170180700d40e0980040985c0031050000f08140305081100500400843c40d440d80b03010005200f40d2031a0041d401403e0601144d901c894005440401485030594490101c0301c0c02201b59680c01007081d4031500c01c940c0005c2032080c900e040e0b4440403652154413079202104501d414510703581950045140040c081c0d60011102c0700086100300e0340ca1500b02e4400b00c1d44d8150750f07407502900161502411141c4440b107984000c40040745240c20580c3c0456000884e50b00b002c2c00b0b00c0880080350400c40c181c1000703401c00da880b03000040c0c44106102410140d03204d00d80070280d094883d01403640d103000000c5203c00c2ca0b000011038550310305141d802140c100d00c640198032840c0e00114049170154809540c1d603120700240c038850f010b43c02c100703110700da460707480002052015a15586031810b5a00131014a108041c0d000101000000e0150044810320f08000d060585c6600081200c82d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 350015000 1250 350013750 350013767
    0x60903030307110d0e1e040b0d05061605041d3313020a050d090c030614100905070504030303021b0601080a0b0f040b0a0203090c04110408010b0613171606 68
    0x80c3c116101c3c0594200843c0e01404509012480262803180442d2019a54055001d0310040094010343d503900904803d840b40840056401d01542c02090241090000200d0000c000c410a00030424144406d010b0318880601c4e04081c580e00d0031940200380c5800e0f1408440c0e4054128503003d1981144100a6250a0301c002d2000d0130422a51140c20044440804c02640700d100e02c41000548104041643e07000c0a0380f2451b000e41c000c140b441c041c40c0d2281c0c0c1325802c4403510104c03031554805000810007180d9500c0042e201511210300240074904040c01c010b821401a80401814560003052000e54400e040c204d02a11924440450b800d95940f50b8009445100d00f04c001e80342000310034000791000e90305440700b9001c0c07980219681045c0e540c0000b05030083d00050710101c110701402101c0645903445004909520f4404500c1c1c17543c0ea441e00902c80d0865030b40419150082e0018015032403108402005d10044408242041c0e0200c408442c1c000d05001e10000c030303101160003200004c0b514951100c0c68 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 350016250 1250 350015000 350015027
    0x10203010f080f07060e2101290a050a050d030201090c0e0906070e1e01051c05090f01090206090907170a0c0f020613140309130902090106050c0705040b060903030307 73
    0x35075900007803038000c0a0711001e01e8000c8601003240a00034201500b0714440fa120302003000180c0700c0c0c100c7c03502d00c0464291000401c2d80c11a203162400b0182202c030025954a40480084030380c49107551500c00811036480041c4922841284e0028452051600139084440165803040d00d00e08959226801c0840004040d21840399510902d40007801070f6006000c0c2c469018402082c0c5001040c030ac0c400c101d0440801003402c0d042110501c40e07010b03000540031181428107210700c0c01140c2ea2801e81401c9180807007140c104490303a818002000c0160b1030303520403240a08401d45010600f03030340f0550140d07000d26800c400300e00c00d407141e80e04010035400c06a06c16038107c035641d903c3d48403842080c10200c1e40c441007640e11a0118480d0b211180c00903459103903900c0c4008080d416642003107070705000900b02d043c0b01c68080030815210b04c0c0500031454031400e0140134002d00c0c100a420522080e1010b41d9032200ba001d03841c0202d90307030603000301a65171f0102501c0e8103a00080460740d403440c02c40f80c01131495039440302 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 350017500 1250 350016250 350016253
    0xc01020304060b0a08120913020a110d14030f04060209130b0a0e040b1303030b04020c0c040501080a03050f090a18020d061a07080d0204050d0507080d0903080301090e0f010203010f08 80
    0x183c001a00e050501c0400329000c8000a2090540343c0115039069440400040d074004401c8080040203040c50000e005140c80c0368a40a13a6881010102070800c4120f200c0b072005c0000040400c6012014031064a4020030b05c045451a65510340c90200d0080c464440101e81c0090303401962515050240c100d140c00f0745080d80c500c0e41d550395851083e8200322055800510b0001e03204d0000e000020140c0515401070b00902d0041190484400810102d81c045030251806420004940100782458040d1600400f000c600034450000251001482070099580030006a800090001041d50396407082902410381c00c04400c90306051342001c00000c0d44070340a00c01c03007e07041020002d00c000841440601004e1101e070700d64940002652000d0043d804003160140d03c40d800e00001c21300343c4a42c000c80745054490401003048a00b8844c1817443c1401c038032021000c110701c240c000d00000d07030b8800c00d0300e0440701c1d11000401c41041c040c070f2980c144101000d008036250b102000000c1c14070251000c54084548030030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 350018750 1250 350017500 350017511
    0x4051018030e0105070f0c06050406020f1209060c010b0616020906090106080c1b060907030b1005010504090203060607150554010c090501080a1e0209060f0c0102030406 74
    0x30a9030465403810400500480c140310702c2d21099501030380007010000d200d101c0d0828142c10655510783c20010035040351000403400718060100540400c1000c00300303a4620300601c60400c0d44845400c40d440b07640102c5000b50004110042c94440c25045804002c0d070041ca0291142d00c011b0540606699111040e0300c14480d134170101310705050202100307040c2d41c1c1690358a032181d9aa1284035403542e11495007001e60b49004e88515105c07040a03c4468000e8154401601401d45142003e581001019000310040405a50108002e0780c119080700c085580c81000980c0301d6444000048103030041c4031006e030000c1d40f0466066402100c1394003ea1103001c0304030454403d12404482c4540b5401c2c81510303104440c00b101d44610a800c0e800001c1640200058241058400d600c2c08081c00d6510540310140416100c0c0341c02d000d51b681250000c0e5108034254420404c541407111600500840c405031008929400901c1202a440d2103080301d0415502400d0740da40c0b58104070f4004e0007940101c800340ca28901c1e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 350020000 1250 350018750 350018771
    0x1c1502030a050a240512070b04120318150305041119030201180e0a09060605150a08060907020d1d10110601170a030f03090f031d010206100b0705070e040510 69
    0x400113100c60300c1041880c030900a052205001300194035642c080c220b840b401c8030008065a49038001e0000d000c0340304a24694400c01d140103030840603e400501c0d0460000581840454018000c50100500c0c6103408101c0d61900c1c03c00030301005400a8458001e021a40031401500b001043d030b03022a803007a0703200880401c103131950f001c14032250300500c000c071320010000c1441d00c40a5000314244a00a000005a1956860014062200d0910600c4820b1400706101d060706400418066000c9000d45a80445280015000391110740b0350b0010070610034401c24000704000700059094800b1070161115111034001c070800b03044506500885c3c1c0c583d00c02d110000c40d00d45140d00440d0300f00300520000b0244058940c1e01680c0f40d1414071038000c20583c1e80c0f0401d00c081003916a412010354000e495010f08c171060b00e00c0d003a91410140c50a141590301850034010101050803a10f81184e9071043e03655102c140070324009040010661004c1030840031907082c0302c2840401301e00c034000040311200401444880c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 350021250 1250 350020000 350020031
    0x60b0705101509021305062a0c130c0201060b2703160e07020a0c0e04062306040905030c0102071202061005010c02010806040b030d030b15030103021c1502030a050a 72
    0x2001c0703042c00006080100002e401c0d0f900689110000b086082c0020703034442c1c000c156950095160081650b4071000b00d1110340d4002c0c1c85d174288143e5050058200d1015410115400b0f41c900c20781219030030f5a561048046501c01e41c4450301622044194550310669000340e4038104500c400e80c00c4100314452170b205024540020840621310542001a001e54a4480c01128118005000c41d083d13000700c80140c40000e002500b0100542074819446009040c00d00b4034800702d4440c1d50a0b40c45a40383c03003107a28010704000324016403042040354081003450440c036105e41907005e040c00c40c82c0f49600103e658000c1145044440c81844500e6003110615524000040c045050703500c00c3d2800300350b0000c8490090b5203d1107405a029074040c0011400b00c0d20000464606040c900c01d60001030380d41e00c3c081c4001c4c43c01440c408031100f8000e103020300355411500003c00403580102d03e0000d24580401210400400d0b1003c0154102c80703240845d22454148440c101401e011642c984401d0f03e42040d03030841512 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 350022500 1250 350021250 350021261
    0xe0306060d0303091e0f110d0f060c0212070809090c031b030a0b030d030b2d090901090503030406060e0f0c0a030515060a020109020a0e07081315060b070510 69
    0x30040c01d034100c561180d1000d500800180c0000d40b2607942034500c9440c1c068a8142d52036a45100c1c4080401c01c1c1900d0419180b00070310021401c0c815610100d1020104094150b5044101e0304000005440c44244400b40d00c5e10241d0f0032202e00080e00803138842c060001002c090081140300742d640d008107503200320941c0784a110888605003100c0320100c04001942c201c101035a40305403811000154202c0103400607180c001c80701c2c03030f40b00040c0e2910445401414000c0ca0706545a283ca03411068410380e0301036061f201410801c03258000c4446100040d9441c509401c916039a40e00701c42070b03d50b00d0a0505004018000500a0320903104901001c01c4d54650201240d5104074404604c05080c0080740070201c024010281c03100000c00004442d407452652000010304c0a408960000249025031348180002014107078010381e06030400307504000d013294101501c40c0d40181c2010034000010f03018941413259564250110504610b0f014011508400b00700081070500e0003074040782c0041440d104118103444 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 350023750 1250 350022500 350022511
    0x902180409050a06091113051f05030d120f02041d01050603070507020d0c0e010902040e0105030a080f0a030e01140915010602071a07060e0a1e0f020603061305010b09010e0306 77
    0x900c0f00300c1e500046402640000c00c41481201c3d580030036540c81c4001131700f040d80080044000355940090004007100004034802e012268408a10200c2ca8500000e44510407000a01c0500c040d210802c01d20445551107800d20100c901c004545481d101c440326101c2c07040760109843e00d441d05000200f841e14095054a20801c0c90f596807a281110981c2446280010050110f43e0003040d940b0101c1e0718000e481a10b4040c01c829007005844510300480b00c0c0e407200301a4043c6009405c00b006e00004501c0140407110028900311440e6681c8219040031030043c01000c00003e6175521741400090340c6241103a0f00303401844541c1c11241c00c0100003810f00102e000a105030400f590105030100303c11700c5036450351100c0281800840c0d08207111515404182c9044c8101c03da640c0e000440036108003c6030012402029020840c0c00658224035030380c004040c45500300c0a032180a0100c0002c0b6640d035140b800900405624a00344900e5075140910350b5140c00420340c0ca800306640d00b25055460800050321440340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 350025000 1250 350023750 350023753
    0x1e04090c05030f15180316060b031e1203280203061512010501121d010903020d0801080607050d0e010f1e090c05040f0b0d0b07140a0f27090218040905 66
    0x2926405117650300140c1240103200c46010a10a6284d943c0c0e00e03078000000b2030b0145d400070031000c07044010107080450640295000007a000d84164044200107401d003206a81c05900b5950f07600c0380c41c1c0304404041400300b0444c80c0c290a841e13006d00c5400700d401440c0145004d460b20100c2418044909005025040d0041141d641d004010010b030f602c108a04d00c3c4820003003c000070582d07040c4203a20007080e40701a400020f43c0d10303541804105541040804000c20452070522250f50400c013034240c076464050440420083d0102c0d00c4030031420ba507030244040d8401207008204c100c2da0f01c03200030003031b00e40c11481c6014a8405a250000c08069000745041c1d81c2e4012002001e2505002c1000300600100d400c044800f43e451041070f20944420105d80c90642c01102101080d20344107400612a03c140c58400c4190a424004003c140e60080c8100c81c240d11036052000560388544c0c010221002045842030500228110000300c3c54603940c01001c0c0026004410f0111421420501c815206e0001c07005049 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 350026250 1250 350025000 350025043
    0x609150503030d0c0504120804030203070e06010c1101091d06010f0e1c0f0b0f0414010606090303051c051f05060301030b010605071110051b0d08061e04090c05030f 72
    0x1010f00341e849503034400510300706241040e866182c104040106031004484005000405100750700e0f0400014005280240741401c0b94904100002c00031b4281d021300822248640043c4409030380541400005440a400021030307911072800150381000040d0750b100d0108440c071081403211071180c2e000c1541ba040240049144149042141c5040c030885c460075246078440d900745600003488040c402c2d00420211414445904090a041d5040085008010010303890040e0804c41c2e0364011f1844011241c1605025840b2080500d80074030003d07849a00c54800c070700d03150800000c2c081981e0400d40c032146035295228090748480c140301e8588420300010b04481c084000402500744a1802000c0240c404c0301c50341282c0c6141c201245898018081c1400451804030b940c04d40c030400481e0550982031040d006040544020101030702170700c006840b2900030f120b004a1482c1d801481c01016580c40300c050410080070000e030500e0701910203980145071080c05250170441c1201ca001940e5035034900c1d141c075070716074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 350027500 1250 350026250 350026267
    0x601030506180703060f02090910080627070602012310150c0506040b0103020906030102190806040b0d05160f0f060f0309080d051005030f0a060b0409080706060915050303 75
    0x540d40301105100003502c240c0c3d0000c0b001603120300886918500d00080540c543d07002800704481e0800003024201d449144aa041004445c0040d4041c3c110110410402c21000da0b01160a8a1940c60700c01c007441c1d1065200000d201c91f815072149810070ada101244102c04480080c1c1c4a1486007a248521045c00100c01030180441c0f81c2c40c0299042c0d00c03030601071081d003807039611070b0b007031000480303040d80c098600c840108254100300314200d9101c182203008624042d116881d110b409200f0070020000c1000c0d910000d40301b03845a0b408a0800c9a00405801391024146032807951a40032050700c0b80e201e4480e8000003900082021000d00766600990002041c43c10b004085400c04074801e90407040544071f0040d580843e403018024001c0d5000c0500c045039620b03100a031440a1143c0e6070010b802588100300781c0581e040d0202d86024100d61010000c5604074102000030f0103050242c42c040d000000c0040d020042000c1c561260301102d00303156043c800003c04501c6640c001581381700366074140c1c208010014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 350028750 1250 350027500 350027521
    0x71101022106061608120105060a080424110304050f03030906180307120203131e0e06060c01020a080708061e04020c0f03130e0604050c04030f0c031704060807020601030506 76
    0x9600c100043c200e0b90400c142040544540a54004150343d8a80009103500b1010b000403001e40c050700c81505d42031318086c40c450700104405001800901200e10701c14003401e203d0b0300074802c8a40700b00111004c1c171000da407002480070280e00c03c0c0e404071f0342c6110310103025824220200541e480380e130240000e414a507881e02c09001040780045a48685404204041e0001031101b40200394420314603401542c46001c11068007041e03040301d42200c03190960400c1d036204012600228141604c408600000701034a0f140d010505500405d035808000d0350020920a42031580000103a204043d5543d5200ba251580b40901003002c01d041041841c0008100d00515079040c10340080c01d90f4124141255109009014810b0840d0854400101500107050b020806404000703685078214400303c03010005828000303021695072095210044c610340440f4202002d00003000714500045412000d910107000c2c041f8082c0074240e106000d40b101050400c000b2844140c40010214180e036400341c000c2c511034480400c4003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 350030000 1250 350028750 350028817
    0xa05060412050a12080f070903170c03040302060706020702690307090b0a060e010203040b0706090b070804113609010606020d0903020d080d0e0607110102 68
    0x5862601c50f604a440024036142503180702007a607552161064100550103040904c4094400000c200700c0d00814404108180c90241051000307500041c6d4502228010078154007880c1e2019500400224864041c000d682d00182815407080301e040b5154800207002c2c000700350707814241203408038000f04c040000d184186504501084082c0301070300f5103a00007443c47d481c12008052000c40499400401240342002c2050502901c005002481420350040c0820718490440c03080c402000158002c00c50706034028170440700908007400d1081e41d01c6e8203904000d0043c180d40760040301e03000200710024110a216410860095a11280100c1d00c01a004104010803900c0f03800c01e070402c2d000343c250044000c2e1085003a40d6081e9000c48041181c0b50441e41c071421640c1e541c0c000c80642d000151282c3e02d030356000032a0815264111418814240ba5040c0402c2500030380300300201c03003071412203044010780300042e2907407260403d5900c40c000e40c0c2080001c2403e07030145540e2421006d19013000c000a8200200c0d54 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 350031250 1250 350030000 350030003
    0xf02040906020703090806101409131202280f0f0c0503010c180f08031b030d020c0a0c060f120b041413030905090103030815040f060807060306050a05060412 69
    0xc00e45603100d80340c403030403a4080c3c0780841c0421000c190130810000107000003170340b2003140342022040b5440c1c00140742075460101c05092068880720001406803401847ca880f00b40c1e04451401410200401c02a6442c030324040d40f02c0c81c1880da40c188240d80750000c43d01030701440d40603a2928060b4081d07030f1002448440780c4401c0711001c0014101068a4500344503170440c1445982d1410401a491070081115800316044008510304031038050001000c00002c50f074020440b240140c9802ea0508049400c500484d0441c1000a0000400d04401c41d4000354118849000754141140255103500985526901407200e20200d202c800394030003803d000e680300c0820803c1c054404107071802c4010484c02402d030111031400f0204d07540b0100c407003450741c0560507138040c00e416204c0314040e5040d170b10064010b03103008020890203441c10008041c203480700d812187c1304079410a001e001c555122001d541c0c403031040340680d40010340313000070000b01490940c604a0895502400e03079407810b42401010584607104a20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 350032500 1250 350031250 350031259
    0x4020a11010203150a05040b100c0c0801060b09011128050c030105010e0115050403020117130b0f09010e19020108060328020111010e1e0a080705010b04051f030f02 72
    0x254690030900a0006510401c0c0300410a400c000014007000320260721070700401e0080b80b03000d06601060f00c03490241001c40049060148405080f0710300a410400b064100000d0f035401c1042c005441d4613450050052a0b800341c031012862200700008035902c800196408445007541110703c14481075180c50300000d01e0089040e195030065950100c1c0c04d40300f00781d00c0040e040c940200104811410080c0000d0b038030482b80b400c01d00e080c0c9503400007042c0408403050501400c244030046004500301c14903a55545500c90030b1840f41d440c04413620f89410340229904081542000d5000c6020b82d404644903c00c42d072085c52600d1481d1040e0011200ca0000619580e0507124003142004150150b43c64960b458140c1040b0311001e00041c40014607000400713808202581c10480c4501800402090b46a0341d101032403802426420a140307035a20304035103144044d000da81e000070f410080c0001034100202840043c1c5046c411a101ea180c1d0003004c0850000a14012001050078000500c003008145000c600080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 350033750 1250 350032500 350032517
    0x140906120a121701180606050c060103170409090303090302010e0703050601120503040f1401020106060311160809060a03050115020c030d050a02010b0612040201021b0303090105030402060c0d0c0302121804020a 92
    0x69500c0d180c41007a040b003076103000d504204c5c031041c0241e40942d40c05020a454098184414020000d0380d519040c000180241b91403448588051340d00b0040e00c000b13006101040c0803159a50401030700400740302e481a001035080c0303000c030801043c0006003203044030307840402004242c1c600103d00003040706c1c10501b00c07010b0108200005800818800d9440a41000282009a1150744001908640d00c07903006005040c107110002c6201ca1003034085e1500245108106420325080e89001c0010b0b1081d1a1030031750008012920200d65580340e070045058990804219000001c42c8034203a075a59040d81c1c80b1035056218001e4081e45c00d02c0f441c090000504940004140d640b00d0400080b40b94100280746040c03c0c81c600100307c199030b4100061840c0060071407800c0164480c61021948038842c00445506025000000c1811525031404543c542d00107070065614038007504000403e0480c506c0c00c2036006100e04103070b0402d10b0034083c0889144490000006014801c00702c14040a0342010304141300307000124 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 350035000 1250 350033750 350033777
    0xa140103021b1524060f090130050c0f030606071407170d0806030304050d0f0f1212021c05040f050607020304060f03110f13080304140906120a12 64
    0x300561444025040e000c1109440d0080c140740340000c0000105003032040c4d110030032001e61200700448407240e1640b280555607080903130040e105001c8113000216003200b02108003601030082003149183d003418103402d0000d6100d80c401c3e02a140190100100390440030804a191850194010324585108421400c040d41d50102614100810f6900000c4450110084c408003680c003401600641c0c1c40c03e0a04101c070303043c090f0110b642d07030245020b040e00403c1443d1000c03040c01182801c6081c80d6a03c101d00b105200d82e80e04e800310b90214004a80b0002c030340611005d182c40010342c0240c0b1a000700c0d8000c0d000e80b00d900e00e9800c2c2c02400f00600705881c028403000702280441c0062200c0e5100e0400d540043da5070724a0040010701030b414810350001058607180422101c05050360484416505013105140c80d10400920401d100740c09512078445484002400280512246000d0001d040121044504c50752414207000f1401005030b02c13502e0f00e4000b15805400107001a07414000c4034000d00c1e18110b81440e1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 350036250 1250 350035000 350035003
    0x50406140d021306140a080a26090402030405030d060803070305070807032a0507060512040803060f0a0602060610030b0d0b0405100e010506131515020a060c0e0a050a140103021b 78
    0x160380028514010703d000303140c4681881b00c1020000c09240000305909401c984442c0340000f05100c0c80b82d1041c00380c4660f021210048400c2d1004105c00400c215a0b03401c2600d485a43c07030380290b04240c45e01e03051400010714103002200744c1da001c0e03415403941440d0000c4c5aa0b038070380d243e1080004a0500034101c03a0060049402101d411800c068010b92403a50001800d09501c1c00c940c5910102c1005004c00540449008059030715030003660002c1120303202c0d210100055a507000c283c290303030f03000007420400050541e80003c1940c0103100179a0781091744601188100c041e0303603002c01c5198001c1191a0780c000040e0fa5846026841405103041d5604500326140b450103407607200c5407010450b07459100f402010f1415070900302d000d0300e80e2030cc10400c01c05102d40c03890b00c1c51600d20646c0c0c880700000300035110a900030f0007190202640810204440c3c080d100010b403404801505c43c03401000b5101c004a0f070344c180664040280e4545c1c40c031003041c0b0101c5100440c0a0b5205403150718245c0145100766095010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 350037500 1250 350036250 350036261
    0x1080316170409050f060a0803090f03120f0d1103040804030f02010c080309030705250e07050d050a0c030c0315140607020a06020d121b0507210504050307050406140d0213 75
    0x2581e81c400b003910f09002140b41c00005021b041d046c8600000790003048540000801c4905089080d5400d0280003048400681080c02401130100d4141e00000c603001c00c40120320040240c100300d0760301000f0403484140307680c60302e010495009080c040100000d10204000e00310320340305113205140c403051b0301c64207a58400c429042603800d1f83c465031001c180007040210500c421100307404007070b02c80425000c147c400c0000041d07443c8920b40401e00070b0001f0581d442c0c40f490460300700110468051085040203a01c0b080203004050400300020f14081e54481301a109000d6944101ca0722540702075100d09200101000c100003080c240d0b0311600806c40f550040e26011081402070080d41c001d0305800c610b684029128001c0c450078021454603022159007101c0c1d9902d050b4918107024900513803a00980e15046140340d04580000c42c07100040c0011995556000b40108280c990983c00d44803c0740d5200c0078403040d540f96025009040304044800d8000d414200d0001c514540010a1110881d45000e0107404490 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 350038750 1250 350037500 350037509
    0xe0606120f070605250f170408060f0402100503070c120918050603010c1106040b270d110a03270f090221061311040f060c061103010803161704 63
    0x290041513440c81703502181003607004055104500311824046603596601845c011100800380c452600c40c1426610320301c02030324080c22110084481c1c6080940c5801c2d4000000c6404034455000751070030b4059a803080c01906e01404072501d07400e5801525a41304400c54800103050000c001080100180108032143d40c00040c084800d00041c641c280700d8241070079201420700540500001c000440740740000050381c0c941c400d400c10098000c42c0c0b90107801542c190603030598075071189034450444154010114041281c4140c4e500c03003140d4540300f4000c098542100003000b901240d801e00e10720307001c000700030341c000b408060070440003a00d291582e425403406040ba0300003640700d550120f007500c141103142e00e60b2202c6420101040c40e461074120000380c4414000e80d210400e09031175a050700076040748202a070f00500450b824148880e600d031075008207841c0f040241034074a5810320382c1d1501e100b1015801c6a0503102c000000d10301c2d00600b08090001a0b050b6603048601410420001c0c05802d000d002500140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 350040000 1250 350038750 350038757
    0xb01230409050702070506070311120408061509150d02030a0501020415020c041407230a030b0117130206070c030b070e03010b01080709050f0f062b0e0606120f0706 72
    0x21424001da0030308a0300010059019903000b90800c0c040356079803005a0342d400342e0501d01800200400340301541070901e10440010080004200890f208a000c581c00b886501c01c0c0082c0f034a0400c190041111300c0d0700680b51050402229800c8815074100002d4003501140040c080b41d4010440c0e551307003401c907441544084d0005803e075411404080d0b060004004203c1c0443d820300c0544aa5031b0079171120007000d0851410f2000e41e8400750181040340e407090b00d541440c01c0449880d0086084007074040c0c110701d004180010303108010b909003071640d440a42d0140340d03c2c210101c118100740e405e01c44643d001010640300d140102e080000064202094988107110b01d6440820507258007080c1429101e03220241410701c00100304200d50705900125407811a0b20442d906542d6040f158080340c1c8025107600c0c2c6580008000a410290081c14140008031160f441e84207104100480e030747c14101c0d011703c0d4412295400c16000300c0c0d1189001c41403208020444425500c0100240100500d454003a43c03022010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 350041250 1250 350040000 350040007
    0x503090a06020309060a080a0f060801151a07080901050c010204080a0b060414150f04090602090a0b030f01031205220e07020d0804080f0412060b030624040b0123 71
    0x1814a828000300400701400110304244400340021914050082d003071080010503c009050b40038a60010f1100503081e80c402c12075203486001039400303400004842c5401111450000501d07a15141050b0300f61803080000500700800341c0d881c00181da20075511103040140c1030203840c4806500784007d00007022217070300508218546142c00d2081400040c02070740720728a030480d40004440319040403a40001604548009035003c000003071b001d0041401c2c0290002d00d01107a190810a00d60700405182c0030407135280b40c249984003400d000301c0c4412200c4490f01c0c2e101c98010000144c3d0500b012075070700d100303003841030a0a03618003210302105d500c0e07005075105019000080201001c0c1d0780b00179402078100e1014014840c6000d5024241c640301800090000c40001035242589805a003920090107201100801c4102e0314201840641001c1c420103119010b01c0001c81d8620b00254590702d0702c11150f440c41820707030501e40200401000300480540c14840c004072000f152410003024140d01400c00018140c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 350042500 1250 350041250 350041267
    0x307031502090f010f0c0605060112150f0f0f06030b0a1502032a2104080d020601090c0f0f0503041505070f0215101505040f0609030204140f06060c010212040503 71
    0x948202d60803840c18000c2940b42918040d81c0240041040c0e9044030008c00c00d52140380049840c410211200310003545800c4011100700c4c142d202000460700c0c210180044030b9200c0d9000343d14940180f044241c03403e480d88080141c2806130b0404041580000c20340e554456440841e0284001300e0704580700160000240c0c500114001c0c201c40410f2482c0c168502e13007210603054995a43e0407600411100c880b007920340a8071002d0046d0443e4060985803042c2c4500c4200d800c03020b5542c150a01074001d20710b00344001d511100b441100c0610368805a9a9002c5040d01c00d100255055400500141d60b00c4451448180540030103020381030040c2c44c542c0c1e90418584440070000c1c00d100d4480ca542e4101d1900d07806010382100ca02c003194007502c80d01d10860309c0c04e03881244140c49a114940c010390516440150020b0f065802c040f5902c00c5078001d643c1448103500311859184451400c59a0b17180c001a224082a560b041020280000b0210100010326081c503c03110103481c1d40f0100c07421581035000089010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 350043750 1250 350042500 350042509
    0xa11040e07080f100621180c0e0c09040e0c0a081006081b09090a0605040f021f0c12022404050d020d0e0409030c1e030809031606020702030703150209 66
    0x2640a6150400e820311804c3c90388440510000d944540c40802c40040c202c50381c03809061110030030412065404004000103c4040d000c21840000141c130041d8581c40d000500c0c000c1e84508510500c88225158034080201d402c0000620500140c02c0c02c2d80324244d0030b0707419901c1c0c909020303010f0100c4600500d5400c408403041d4082e07940701c0d0030a038215000340742d0003540d2501d50b076072511081070116650609517960f644818030f00040d00d200075004030305290500041c0454035030524611070003599034000e28407030101c403c02c3c8800c5100301d040004280c111040701081991009100f144014815107101101014640c0e0a072203000c911701402c060900e0500007085010048109010381a00280c4061441d2110140801c41508209802142c941c50110f04240c42a24401400c030707405a40d8030500100304105401e00c8160a0088000c10101000300d40e09600000036118100180148011b42d011b05680d050082d40182c00308076014456424040005072903a00c4172071020500c081c0050302c5e61181030400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 350045000 1250 350043750 350043767
    0x20a05122a0925180504020a0e03150f070c0209060909010e0f03091912031101020904020a08040507050405090304230d080711090f04060903020a02120106030b09060106090303080a11040e07 83
    0x1c2050020460b589076a4000b4203a204c1c04076041280c00503191000e003041614041007000041741e0501503801529460880c1ca1034090040510341d25084056540090545030201101000380d4403458502c0094600d02d40810001d502105450020503910680007020b4130745001000c01a04070b800c00714445e40d5904110030080310341200740d40d0030000645005950450b68030b101c0806020400314400b0b810006200350104d500560010300115035644401030300414000055904803550b00403030100280c0c83c901401014081c081e100c0195180911f0b20402c0307a00405502d44160040d4500c112600b80c1da17440e0351841d1040c0d802210819a160740524102140c2c152032a4000c1c4100c0a42050102e600c0d0a00d0802e0341c40b5500c0500011f01001ca800c0a900c7e004016900a40c80718130040304500c80d56040d0801001c681c03041140986c0c5403600010b00740c07201d9090103848009a051441000420b1107032040c10f410007080c0c180099107040724a410b882035400760b00402040791b00360050010711940032054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 350046250 1250 350045000 350045071
    0xc05100c170709050d0602070c0e1503010e03030a0b01091203080f10060804061a030a03120f02090306270a0b07091203020703020609030c130504020a05122a09 70
    0x3080071500d450640905003010500807a80682c07282035140d003c01c01c2e59412100041d07003100b0440c170442d54805030316403110f004841710944220504c4c050846410305000b17421030b02c56001d02460442d900d480030031009000101403c1d0411405010000349d0314403858040006d103000f40d4071540c243c030b8200b01c82c032100c1001901410050b032680f18104041c035809070159070802c0d0300c03450218058020310400700420300d940100b40d625002d030381d050100301600003034030520b07503565440c0c00c0c0059084803000a049002e07140c4125050340104000682c62000150180f24008a0841041001c00d40c200366a14100705502c0c2258034544c40700903c5402038000a2410080c00040400a01c40d0504d980007500c4001c3c0d403000034011100415204001e9409001e401c81c2d8910140420801c44841400c03080580320a50b8242e010725072824003ca81801c0c00d003044410052880c00a0803409900b19461440c280080c0c7e824030544c200a06030b074003035514542414000d0020344404042c00e02c00c1a9104003014038001f5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 350047500 1250 350046250 350046287
    0x21201060504141b0307030912020f010b04020a020309060c070e0a02030907050a0303170a0b0607050a12020601061706011e051e090d060509120f04060f1805100c05100c 74
    0x401507900005031680188482e0041e0903910307a00c810000354007404c0340010007820055200272200d20240d0000d0411900c0c80300c00d009000e0813823100e00b448105d114000c010360044e00200961442410000020710290071940121840703142da0307402800440200381c880404946c0c00000b07001281c0d00030494440584403c60305227149a145581c090160030100045410240e582d50000c2c04c400015440900328843c0504030326a039190903c1d1864464407004000c440041904641c8401a880007901c1c1e0305941da10340fa1490446400014902c44000041c8058100030769441c00d1030fa400440c4c24104050003e54032003e0306c98484180070a6541e0006100c07900302407050001410582d54440c0f240d807540c0c0c00c04000609919011030190425a5412010781d18a030000b465840d1811000300400c115440e40c0c0d40c409806a8142e400c468144456994411090036840244030515251114007502c034240d0a1405002195944090400c0e000d94000c40f80c00e9603680200c0d41c50703a040107038408241c03000741 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 350048750 1250 350047500 350047541
    0xc12090106231915031401060801060c06110a0504082b03091a1e0a0c0509040b0f040f051006020a0b010306112b0605040207051513021201060504 64
    0x551079a068880402e240c4100c01c5034000c0b10725180c85034041c0360112010907150403589500c51905138103071000f25041030700183c41c1034140b0710031262805045058680a6580b41016464034504550030134811905a40141c0d5400303c100c2d48980c0840202074640031038444c140c89a00e020b04030340c01c0848450791403194020500512a800700e800d195841555001c1c180092009181d0922015410650303220207407800d00f100621000030450200b001210000c5c40e50524039070358085005040c0c606480074a00420300034802d00960b8682500980103010029000c4017040c85034400180c01e0b00c10103020104010380d510113002840c40900ea10002a100a0009105204041d541c2860000303052002a1540d641d03030540118840c000c0040b42c0801d00c2101140c164003500d41c0c00380f401264107241a118041c0f4001c2c00041900380b60003503904907030b000380c042d02c03020740a180b10b44100c0d04000e04c1c82030301810244410380107070b650707030007802102d08681c00003e038a5082000348001c43e0f107512282d12030b800440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 350050000 1250 350048750 350048759
    0x70e033406020f0a0803090c0301060306020c19050d1d130b04050601090303081512030c010b01021605010c030e010203040b0d02040302041107150c0c080c0c030d091a031801050c12090106 82
    0x1600c000d41980020801d5881d03441d44447c900b00450703071158039419420028000140b25050300502034071a15041514020304883c540103110110b0404010b01541003400d8840510340200303214080510101c61001c5490449000503035004c0d507540c0b6072030106554200807942407e15101c0c0590250007824460b804e20b0440d18090242d5400810600742041d041e280044580c5807001d03102c4102c01440b08403521403540d001510301030055503005500601c2740080610b0309041400351081100e0f8182c68403010105075032402c803260040c0a8a41c0c4c19848200300c00202c0c80b5551000340501003c0754801600c4601b9841040151030905500071060881070041c3e00104071661100c640f0b20000c0e6100280e145003004040c0e0381034a9424019003800408219400307410004030340101d2514088095071010780e1090829901d000b100e000e00c03403403001e60350341c0b0242c260030400041d500100e0305160480c000d41d801e20140c0c2990800c6808146468010a26022200c000d00380756402c045034000034016603041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 350051250 1250 350050000 350050003
    0x2010c0609030206093912063405070305030703110406020106030501110a090513090c09050403020f06190903050d0926210703291314070e033406020f 66
    0x400171b0560b4264103503079400c825074a2010b52240c0451107001c1e9085483d0882d050040102064031780600310071010303420720920704000d02041c540d00d6103484450602410f0b450803a080d8200070305040615564110703058040344100041d200401c2181c7c00400c4160540c6480b90a403610400c46000d42e00d01800042d18064201d1240300940d80c0941d0500400c3c0b2100003241e018090501c0c1c00360085511000c0807400d01c1443d001684514065001c80e061040544909540e488084849034240f40044681040c4241d0a0700b200610078003925006052038a4241a501200e08840044980200b58000b00085c2110f6182107a50201135000d400e0800310511505d00420b400720280d9021003440c1c0300020000b40c0207601001594801c600c0c0c0c0c02c0040c0c910001c1c0301001c0032076200e6601c240007000036940c40f221035001d05204100315a04d020310320b443d082010750315000d480c16200c1d8980502940c4030341811000884225100030441c1201d14005580c020000d68a0180c2080c02150480311080050010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 350052500 1250 350051250 350051323
    0x20c090105010c0318031a0f04113307020415030c1a0f0a0c0b060609030309150714010506150301151805030d080f06031c0c02010c060903020609 64
    0x300382442c03040080d503132500301c07001540303080400410440b291011040c80b840048901d0b2400d101d09800c0c90a4603a91007900f641c240468000f8142c41c6407100c00515814121810071074045885210b11206100c07407000104e0300c18a07803c1d4544902d01184080540c9854069071003c503144d901808025400c64a90b00700c002d5060149031070000e400b13801927080310300f0203080f2150301a01880c200d03210740b0030000080c50064140400d031060031041001c0344c0146010412200c041b100280194a003010040078403050f025030b4010a0550130b024400c0708082070400c015080403007122000000c0714079015003044001c0b130f041e148507a83d82c401400180811404000c0e02085600039080150668181c0381a008030040c0c81e80085405003c1c18025007681c07a0054841c034003400e05052a42c01a41d150800d0554801104070b2019007504d022030310342540b500898000a0550040c50400d800c2c00340d83c0c854006442282c1c01c1180164055403c00108440c00d0100c146614400000c418040f40b018031622110b44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 350053750 1250 350052500 350052509
    0x91119150804020312120f0709080307060905031e040305150c040302040e120c0c041802010806150706111b0c0f01050901050c07090203061c200d0b0405010516020c0901 74
    0x10741801003020765070200b14422074015455041ca0f0b4880070060048000202901c001c0740105294011614140c00740ea4500191502000214101005a190403000d41304003070382603901d0f000410052034110b203880c1140d10307007070100c0d02d541350703290b01d9072401e2464450b04400c003201c0d4848490178001060202012141182d80403140490040c6420b8405402d05500c41813203011070f40000740b28070709040702013000f0070101c1003200e0800c810030009820b280c605e84240e80c003e0008000100040c214039069083e64412030410042c0f038184a216034808007141d0204c0c41c0c050300b01c2e02c0070515031104413100030342c10380c150f41001c050060300322900085139198046580c1c042c10b001d0f01183ca0005a40301d0825681d00d00707984012906200d43e18954079000707510540c4d4040c091007050078042c00c004664112004a00e5104202d841c09048002000711140d0004d52a03079404000f01c5524030214101416141c043c40c06140005924140b06036159400d18007240c0850954101000c3d502141e59201019030445d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 350055000 1250 350053750 350053757
    0x6150105181305070207050111060105060403060c201506060c0a0b070315090605150c030f1308150708011505040509060102010216050604020a0f08100c1209111915 72
    0x140012000250200b0b516090041214504010070008a9000076a50101c0d002070300c0701a440c10704030346442d440d11070900582d604200b0070041040007645650210304406014600a00c403016500c9042c403050100022146140c0d015941c030040380d03146000c140b0b400007412100035242c10001c1165a4030323040c031144003405641040700081c0c0e01d04d01a0304062041c101040780c03100c1158039202034100500c0140240307400b6180d8a12510100c48481003142e010751000c0340103600708202480c03c0012540b280c60715606050307020300002000700d0300300481551f85613110321700d000c10703d0030b2070f0000d18944059000ca21200008050b0030210368000007142c05596003501c400c3c6980c0c3d29800140d01a220b1000714000c125158030b405418004080707405401a072080f200c0000c81943c4140406039010503005220340c43e08950724a60780c2d10004d40c8401402c001c1130501d40c1402c070109400030104c40b002141550b00c00300354031a00704c0320300d0040e0b40f40b504e00501581d0140c42c5401c00201440b203d0002c00c661091 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 350056250 1250 350055000 350055037
    0x606061c0f0612080c01060902030402090115140409021206030106051503040807080a09091a0916020115080708072313090b0c0d0b03010603030e0d030306050301020a02030c06150105 80
    0x419035900950b01600380461604140c080c41d244c000b029901004070120305500c3c100c8049400c41c86070003102c1c040d0b5001031002042c0d03400c241c500f50390025814618800c0c030820300c0c0c40322801321080014000a140c448001601d801082024506c84d84009061900c640d140c40e2062010b43d54650403040d04007080c046050316607695117002800f5102d0018042e0080c80e020030200700e030366400018031007901d10780301050000a101c001d0000c800c48003a00b110741d120f1130810000702d481c3c03035080a10902c07010600c004502c82044500503418000a40c001005541004a0600201d007040203100f005003406060005210f1030180c0c0b0240c50003e00406900c5a04e1050880400800075007020340b08942050880c0b4030f9082c0b0001c61000c1e980201e02c4028982e0600021804510301840f80b40d0849805858049041c5a40403c200c07031600d804400310141640d44d0b0b4045165242403020344170f1185140c0003550741d01c24100d50303180f800b2801414001c075801d0001090446990000688103201903120f102a03d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 350057500 1250 350056250 350056271
    0x8011d07120b06070c0905040c0e150111010213030c1a1207050a17131e0209010b1c061401080c040b0f130305010f091202010911100201060b070f050606061c 69
    0x45441071144c060094008203002168082d4183d01050049120f413a0003c001640c845884410800c108c1d005d15165005900b545055405201e80003841c03800b0700001403500c503d22070000c0290405400988900100e00c2e03003400352403c54040c0d00c82c0b082d0300d42d41c141e08080450b1000d10300c0c0b90740241010300f085004502c1007105406001e5503442818082e116030290b141001659407010340c140404d032140c540c020105c0c10000144001d1041058000d0300c13160704c2e83c1c01d010300ca080c0c13a0b0082c100d24080088e081050040c59195200c3d0401522030310034913180c1d0281c15000104103600c007400205d018041044104980b00d003a4084402040780240030b035448201d42ea503513805002d82980068125420588a59241105584041d5850f4852403000e140001481da04908803511001c00a180f60703400c0c80c86d10f0f25460f041e85080072f405210310012444548601c140c08564010030412039003c0300d860340b403004200c0107100700d03903014405a41c418141600c0b04290220071425030504501aa601e8000d0070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 350058750 1250 350057500 350057509
    0x180f060e0f250f061b0c090e1b010905031e2802041407020d0c0c030f0f03080105030604020918071a120f010f05150903010c08011d07120b 61
    0x54003404900c05540300d03403540702c2d048900c500807110916030407429084042111500450020140c400c00d0703031151110030a40c07480c400518a000300c1600c44000d13901d00010241403600074070100c1403e0502070400b0140064060b030880d101c00c60410f0612140040502c0941c50028483d809a510040031070a0f030319103101d1060404c603001356481e002d80d000b51002003600240c0140c40114500c01d403020071503220040443d0840799419030340307800140c201c1c180070713142a48501c42d55140c0d58015100490450303038030340c0c03100c240784000b05003215110b000349030b44030a150b00041c0790350040100f42c014001c00d00e0154001440d20b00c00500007003080340c25450815140d0010000031010300032585d80106a003c4042405045030000c500703508041910900160802c0700011580e41261544810504440e0900d010001002c41e90580c5201140c001d01c124804c5e59024000d042030100b03a40c540648550502c5802d0714041d03040c4030007171907598850b000c0c48129503001c48440707442d1000c490000b408800200005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 350060000 1250 350058750 350058763
    0x19051f0209040630030f12060506030114010908070518130501060b03061002070503030306040209060d1404060b030307120f11030301030506090c27100b070f0204180f060e 75
    0x1075811034038181022404880c28641400c4001c800354806554200400003c4420302480710000c002601030428031001030702500d950715404060020204110307454902240303e582007640102076808003594046801d58000a03502c000c0c02815000e04515130401000c1010152120ba0500807001e4490001c1e061101c254114804280c2c020021702c4019500e030018002e81d0010346019108011103c41240c2d40c9000280610071107030090040c50840e030395201084003e41000c0e00345071300507804201c040d80b003e000b442203900e4140e141c0d04101b003904107414880126080313a00118000c0c0d01c100481070100d0545280e8500c181c42c05e14285108107002101120003549101491685201c04400481045000b140861086c42200110380078290b2040030081e14804981c802280c20a100212560082c241038107594000d04641c2101011a41c45c146140c0e55809050305541c03181031040044110301d03203809000b1141038000068009101103480e2010031004118000b00042d5603100340b00d6000320280100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 350061250 1250 350060000 350060017
    0xd06050604142202030702070302041802090408030a14070302040603060b040b07020f04020c192a06050a1803030c03030e010506060f13030615060e1503010b0c0f030d020a0219051f02 80
    0x4d5441e414922070180d62102a0b01040348500e0a202c7c054102d00745441035030310029001030810085071150b8440c00e00c240e00c042d12207048544c4626064000591480e1120300803000c0d03540040e9501c1c0f4141e0010129031243c3c1080448213410001080b4116502081c0c0707a07180d4040300d8801100b101280068001d1255a1241c006e80c0902503640540401d4078010100c2c00340289007048040800102c0071801401c102c0418017000180603050040c0c0d8811005008041000c6c2854022800c102013010016039040e841240000c43c3d0803900400c042e41405a2040240000020700c031134204403002034864001d043c0105002100400d051490006441900000350b401c05030802550151401c401044a0180034042c0800c0c80c0d0103c2c81000d09000300aa14001394212076a400c5900300603202070f01e5405103885022511490207a007416801c140300500c16401640e00060b940c1503003071006800e1100500030010160803420071500450004250203100092100d40e80d000110502100e0f00203003c0d00d0403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 350062500 1250 350061250 350061319
    0x60109151805040f09021203040f0303050d0902031609200409090201051204030503180303040803130311070602010f0e0304050a0308031f0f090501050d030f18030204110d0605060414 80
    0x1300e0125001082d80b01a003040d000356082040c003140d07428995070b24481d45c4581750f90388105000810209208502500021024600202d007000545c1c00180c60100300030902c2900c500c03c2181044402d04902c51881251804621201c20302070300d80c44084180124440c0d9036040d40c8410903401103a100384210b8500120305004c01d5100d04090900030190b800444140c21000d041c44580d0392950300c0002600d1280b0f511101382c0e450b541d640790790401003c41003101207040c4a003d1381803014405081c03200c0740150200344d00003d000307014000110f0076118070383c800002c40e4104102c203100948031f0503070705015a90400801755690f102ca0511005405580b00070100503440e0100214601c171030102000c0032150512000d0004c1c1e62100c04000340e10040c100001c02103262015520380031801542c6c000074142181d00c030005860303980d40124060701d006400c03c580c050b0780002c208030315400512400014000c15111142003900b0000c400d105405201c4015109002c481d0082c900d0086006100c0348800c440341 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 350063750 1250 350062500 350062511
    0xf0301080109021206090303010909080f0c010e0c0111120c15041505010906060509120106081510080a0201050d05100f030b070e0402030c0a030f1103070206090606010915180504 78
    0x440d020300800010108074461610100400310b141320000d486801085600069407a6918052058000340f1100f03400312401841030011441c171400c0f0201400811810b040003094618181e00c10f0790a10b005c06500c01e051100081c400c001c240d0000407207040798180d10f80d130346e651888044000d51424060b124a0034104004808200400181c0e488055404120210502060b6250202041521268084c8600042c410f004042d00340c81c1c110f842e036080c2c51041c0700010300b5540ba021203a050010859482410038034120600040c0c108002410008085a01c05400c0528460b40000c00c2445a481050045521407001c00c2d07100003031a00200050130840c90140b40035680c0d03e02556001001c5414001260b4800d01c005004d040c140200d070b2141e4148000a0302d81281e155082d0000d00d5905640d400550b03a41c200d228200080100450007030401d0340040c401d80c074003070102600d81800102002d0410a800c101080f1185080c000103480d83c10509050200300c40c450000c1c074140c00c00fa0b000319406030401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 350065000 1250 350063750 350063759
    0xf030507060e0c0105071b080115050f1002060c03040311070303080708060d031407050309040207050109052104050103331703070f020103091707050106090e2407050f0301 75
    0x26008180180c80350406100b4084018002c6440385071000720f80d80070400c2001410005146a0641c40e9030411030b411103100300391a400c0300380c21195134407100000544c000d4000d02051a14000038165890229030b004400490000001c0d150080500300700c0c1c0354000807011804042c080d03000c0000500710703241100c100d0350362410024800310080d120b503004581e6840114506062402d03088068a4058485201070300390005134101941c00002c054400b0b010502c0440860740d40e500091081d140180004a05200c01c0e05090741841c10601c1080001c030202540441e01701c58030001d0314101c0300c007420001780c040c50415003890141184541c84803d050038104c00c125030110184800141c1d4070509411400d014403203491a0b581c0300b0450040c22140840c0c8989005611130380004c01140e10070324056140341041202030b0b1294216840c21261071f51100f0051201205e68400d0384001102e001c02006c81160b08401c070401600ca072691004034050000020300c3c0c3c18000c04c1100c035000c000d0101035541c0d6944 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 350066250 1250 350065000 350065007
    0x2103040902070c21150e06061512100603060506131e090c090801060b0903070e101e0305010506091e0402120d20030c0607121803030c081812090a030f03 67
    0x10440c045603100b0403817003038005410052160000000000d0000d003a039490b10300804c1035440e0f48180d080440b20080020b1078a055050341500e001b100c4181c48105801d040c60350240c00c1d40d0a64114601504050011100d41d000c141e10400031200d030004441c038180000f50f00094081850380054480390b0a0000c22030000da44021840100c1c0c20001c02000582d0322064100c08a00c600010310303502d948000c5040c0240c030784000300710b80c1089403100f041e40515a110745450a038050007035103a461200802d402c1050000c28002c660b8080c004961042c03041c0707032003e04001c1c3d0442a40030480c0d040480000102151103409a0362025101c2a08079030701d103082044000d04102c020344000c110021031481c1f14601c1c3c04000b094944c0001d03c440a1b0459a50322078040340d0124040501c4894a501c40540c0c006c0801480070368141c3d20b00030b0303a010885405450015140840280ca0410404a50000031000c104c0124001141c80785d018902e0780c2d1400c0d0500055010a5990800b500f0340d07030310082079000c0581 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 350067500 1250 350066250 350066309
    0x609020f070507080706020307020f04090b010e101a040b09031510090f02030402030c09151f0219030206010501050a0903050607050c06130309030b04061d0c2103040902070c 76
    0x114204442e030440e110ba0080d919002940318031b00140e031090007104018501000c01508609008d800015038009688070030b48041c2d420781c4004440d5103030100380b0000d500c0b100391100140c281d62801310880c00c8415003100b104d01c40c0b8807030012030a8003c2080f440c0365401303110304207501407010600315041c1840c041010054005208040e00d07245008540c2e00078041600a407032080780c00501400704002c404003070000c41d00740149090140044191074900d00d5560b8480c481c424400900900d441c8049154060700d0400403900000c0076155007494040002e5001443e41d041d11000c0c40d0041d02c50603100b600b5500d44d841904000e0040c017549041000c0c059101001d0180ca654142c11141103498a0004804110b000c1c00041c00091005006001140c0c1c280259030b041841020000303114440d50010b40050b40310f4800720030880c1c004440c00d543c00d29080070841500090003401d948640f20505072655680b20310b10480181c40d8000c10310030140401c3c8200240202610b8058012020480034405d080c10b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 350068750 1250 350067500 350067503
    0x904060b0a12020f0f060d05070327150c02010e0102040b03040b1f0302040506060f030405070302031c081302030a080a09091104031a152e0e030d0509040609020f07 72
    0x881c0740700001051603040d001c00c034015401402e600c0c0004803c07024040d01040c407111040d001401002003c101c0c00d600d00c90b15100b800195030000307895141062100c0030032405d020110b2005c18801148002c9008400c13007040319417004000080024804900343d01524803030f045003c0a520105001519421140c002d612507840b40d890715000d44e5a481c1002660381c4c950001139400c3c0041c180910040c1420b034440760304030078010032085c10300034030901c0e00c90954811241198960802e42c030800460408000000c4208030143c004150300f503201400130003520000703083d00c0216080320b080c1c20564405002410403544c000010780e50700c0c10104009001d0b0811446011a00ba140030b0740c20a01c03186078010340d000e490b03002c6c0340d101d0f03084000e5002243d164800b80014803100c0443d84515100d40c0c030100b5107010700000038500c1c280341200d03101e20000c45202c1d0400105209045041e101036907408108038483e09041d003402500c1e82006408038004040c0c1d60400380362540300251528503c051038014140c183d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 350070000 1250 350068750 350068759
    0x4030c05030307080d0216020409080903010b091519120c0e0c04060c030507031205011206050c040e0613020f030a1b1409060d09150902100206011d090c0904060b 71
    0x1940c90007410340e20b1240d2200076055280038844140081299001001903146000310301c3d4440e80300d0f030000303000c84486030021140c140000a601e049402c00303004680d410039044910b11803528043c05620f00341e0003a451040d11800491030003c01101d000050480030700102c80440d5020441444c20030090344403405036101210604c2e000800644011040340c05558480d6610100700281d590300b0fa07115008004100c090100d020008804001c00d482140e000f0042c40d4508410180d841c00c0c03840443e00d01500036298020308010620285000a1302c85801403025203030210702c0311030458408000c0c090f0346c4c2c0383ca600c51400424041494000c0c0c1203043c55481c000c484050161812009035407d40703a82601c10303035884003030004515a2410320f01400c1c0c003118440340816502081c0c0c0e21103c3c40c03030600c185e00d141240d981c0c1c0c03000294100f403040c02e00c55001d18001012a941008200c04d0307090101507048843c41e10140c0002d1800d20203100c02d100c00300c03005e0b140d034600742030174540700380034044c540ca826000c3e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 350071250 1250 350070000 350070023
    0x1203220b0a0b03061003030c080c0c130b042712022a010f08090d030b01090305060108030d1512020d0f02040c020601060f02150c0c19110405060f01020309040f060b040b0403 76
    0x148106080c180880e0b1f45a101d000400c1001c0d59000c546070403103444205503020301d10100c01c2c25214071030040d8003804c401030005401400c28082100301c0e50b10300309000c1d081f0202d0415000400003060610384560301306061008000c5115401c1b40b4018480640c0c0c2d5600d44120014403142e00350410070101c0650980740c5800304020804101d5038a0001c8510403055071010700119040c40c040d0340150410401890110105238507902e400d85041001c0c2e20004650b03100040d1040028040d120729000d105142c5444207802d0304d841c08201400d4800310300030780300704408407008041005846994441580c058018810450f40c440c022b5260003092003034401090440c524220744a1020484014101c4c0030000c940440d02c038202c4440c800d07080390030299600d210b000c02002142003c140340800302d80c07080403000100540a814407060340c00160040d170103401e44000100c40380e80c0110584083e040252400110550070241c400c0c01341180e82d0007680e01c003000003004078200c5901c0c0e000b0400e507406501c1e0a1038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 350072500 1250 350071250 350071261
    0xa030f05010218150d0b030c121b10081b0403021c0501050a02131715010b1b1603060218100f030501081c0818030d090302010b031203220b0a0b0306 65
    0x2404001c0ca60b4404c001404014184041001d94041c800c0801301400b140c80707604111000c01c0010441940c0c0142035130041d92241d4a059210303208119101d0240c40747c0e00f0150210102500c8407201811b640a01d2500e60141809111144161402190010b00c00c00252040c1201e21420161800050303400c1e5080c01c0c0081c50141590081720b103004501903010f0401840e1034012030032400c0c030a001c09e50b140244280e01c1080604100e01e113000e841e80303e1441d5030392640c0380310450000a40c2c0d5105122a0001c14202d814540c1003071450088a42007a4007507503650351044803000b84841c5000d01a80410541c1d131210b80c0c43c0e0b0000800300398240c01d0318104403590f29510216501c106142060f10440c28421001c609079100e03004c100d402c40b5044001844071459506194210341000d02d20407040c59540e04a8030501d5824040c200d0582401d6019040c03d800c881c021318203511000b042650207140b910024241c421403c01b5040d42e46130170508141c1d04c0d00704100c1480180400110a61080c45400d02140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 350073750 1250 350072500 350072509
    0xb0a0b0a180b0d02090c0a140d1b080f010b0313021504090b06070506072109080d060902130504180c17061e0a0f1d0a0c0807030519020a030f05010218 66
    0x9050980040a0030320a43e100c3c2c2e00d1b005207900440800080040790031000d07058400d1704001e420603041112002c120740400e5003120443c24400c118a01c00c0102c0c1006101f90443c4c210520748c1501e000c0a29180d9a545c5c0881c006035442c91407200a4000000050841c0b00620403000b82007510780302c02d001c0c00824440401c00641d80640540901180c01850105102c14081e040303074a419076124000c000c0c1c001c0304110782030442d16607410507a403002c4001887c546c3c880320340c0300380c00107090b42100460400b0310495440041076070a010300c034040c1d07903501005c2c11882c1102800340380301640000700c030082035207614a108100100208050340c2d841400042800710522014101e8681d203051881c0880b691001030075005407a0b22100801c40701c0c1e580c116548895a80002038581400000080c07400c101d4524010220491039444801c2580100c1c90030700005c2c0c00440d000d00c410210302214005080c0c1800010003060940e480100b8107406020010108641074019000d0103079401c0400d18002003010610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 350075000 1250 350073750 350073769
    0x102070b060d03231c051008011a210a0506061c051510090e03070c050105070b1506040b0706090203100b0d0b1801020705100c0810030602030907090c0207050306090d0c0b0a0b0a180b 80
    0x840e6180703144010032152f4100110001d046001c0d4800110452100780f10315801c0c000c910394242c980c5c0d00280104010b904045055140d01500280e100c0301500c0d0360340b03030a505c03004480b410300080e0071f580000c610000700c104041d034058144c448080080c0700b014103085640340e00038003045034084201040081c996006e00140c0d01c6413038110008502c03070f90f40e9244040040a928010550002e0107000201c3c000300e42201424906d0b2081c03000060442081c01014900b03000c2d0f40c4003440c0241018101060f47c1c4a928000a115504c0401039a00e0349030b02044003c4070720303801d0b200e01440d031010079206c1c01e01070300180381102c05003407580401c080300c01e85200b10748481c82202e80c080d0b0307050380080410011f48241d0081d82e11448900030744580750b8490740c000050307a27000c001080c0180d00c03851092090f40f40500c056600140d980c17000f010a40c401d48805401609100c801915009200e03000070181301c00f5400000013100004c1460880f0350b100c01c0e00d64648410110620321040c5000d59003005810300038200d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 350076250 1250 350075000 350075021
    0xc09090f030405011404090507030b2e0c0302150f01050a150813050c090103060e010b0901150804140304120606060c020102150c09120102070b060d03231c05100801 72
    0xd1441d0506220040d60b03100181254000d1140c5d08120005180d5101d105507802944145d401080701c8544404103c1d94015816078030345248140710440d00704000c030502c51500054103060500c40c001c00c80c14140d0400810200360010010f005003004002e400f50300807181a581c04a0b0840801038440d518007550001b40407100001c200c0b020301290021117590307048030009100c0c0d01155804080c400101d21001401e0380101d49683d00c490901110380001e01851003070030016145145603601d42566034507810082d10f0710005002c5420041814040e081c00f03000c111034001c400300c0381d4983d07030b0f215a05501055080241da64034940600070031860b104150050071a60141e00801030f202611030622400d000150810180300820003500c0800d4036a910103840c008500400140c4448481c1441003901c240201498420f031510680c4078000307604801030420700000064460181e00038002c14500c9445400404040201d40092204002200d070308014440d030070060440c0300140d0303a106150700340c0e92003007031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 350077500 1250 350076250 350076253
    0x1020414101b1b08010c031a0418060b060f070807110f010e10051308030418060b030a0c050d111b03091509030a140a120801030f02090a1103090c09090f 67
    0x101011074451051a0341c40500745000503840395032203102c83d084507080c0740542d0119440300800240b0901600c803020002a0a0303600b031050410b99640350f1056001d0140003040b05533136408080b69034441e0030035184110301000806070f071811581800d001c00c0e000080116020020b4a8103401c040c2440c0204012062041c3c40f01c060034a10f0204114180e03499000345c008101d010b00c0381075410350b0ac40c0c9241005004000103140da032814035080000f0024100c2e0038104c0c2c03508105080041c29401c0041b240d10019210703000464a6540d803044405104500341c8002a50070440064044600342009050310041002c50b603d03454203403a030154480c011407003900da100c05074521030f4000015104c000c1c0b5601c40014161060060107030784803106101918032044c625030140114500f040340000d6400c0861040d402d000403598519921904a2144a000240100c40c54404680001500d41040100035241054180c40c2c0c944589910340c2c900303000030044d10070350f480404900315180110301c060030f140c071000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 350078750 1250 350077500 350077547
    0x30705150a0e0406152a03050a02100906050901140c0f1303020918060109090f03120f050123040911040504030203040b13050a090c020706030b0607050102041410 71
    0x111280036400c290040760500c03281d01407105450ba56071150101402c0650381c0f43d41c882d030341848020b00c6485c1040e080c1e000780c420141031000302a1a40c00307003040e450781440d102d542c945040310101c0c207014601d11002c442171f042c0003080d020842c09410083c4601c4d1000000c005400d1016011070103100240c03400300ca80a0304020342046826400001c04010b0088824062501e55035800700e00b11040840780305200c2d40401510314071901040c04003a00400109030b007400110401e0311090303c1348401110003424030034030700141e00018006410040c41005805003c000d907603503448081c0310303d807400c0110821685280d00030412502e8288240c00b01e03d42c000304820402007000c0117000080070044e000307a0039440b0501c400140d0505001c010002043c01e25102c55581d8901018010311585e1034010707100d0f46040c108a04c0b0056030008801c0b081b1465440c001c1003d00c001c1c0c010810b94071500c003004d05254000034002c42c102401800c05039214a00b40c0710042600c81c650021640c03800310040203410740c003400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 350080000 1250 350078750 350078779
    0xd0c02011d0a12120e120d050f16081e0403020f06091f020a090b0d060303030515030d030b01051606020408060601051e0a12051503060705040f0506160203010509060411030705 77
    0x1e2200d825152603101d000110b400f40d0003001403901e1b0400c54041034070a000552440c9003038050080c25000603080c01a2045c42c200810301e21080c000d0300c1011310400070780c03000046819040e40b83c1c01c209004150104a09818181802900c4141505a038a00f038450100400c032416000950201548071404c0c4144002540d0091140a54020101d000410503241404110340f8440c40041c00c00ea0035444c07000450034550b20f40070b029608024034030b10003162000d401c18129100810003400700011441c000451050070001a281c6014119040c14180e0503a1034030010020340d17074020400e0341d00b50400c44103107503a244011102c0303200f6203090f202c640d4a138004000c0684041c0c006008860500d081c895861158809107400b00c401c211041070b13101d16900342c005030711f00b004c1c80882d42041c1149042c4e480d2904040007004c13420392621443e40241c40019864450042000d500603020f603004000384981e0800c40c00e4540c2d203120a8074140c416401c00005a040342c603000030120203d4034050003c00354040300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 350081250 1250 350080000 350080007
    0x60801063e0105150d240c091502010203040b0f070908031603081003020315040f020607060603031d210c0d08030603070b0a0c020906040b0a0e1b070b040809060d0c02011d0a12 77
    0x407180d144c034201042d995801b0150114010550b242070139a44d000001440c001a032105c1840c8020b07804c0c10340e441041440040307001c403041542d11990b031050000654441030000c95a400c3d00c0c0d40555020302010512910000c0000e940c804101c0c0641d0340e06000341c50b0202d01c0304030000d0620000354164400482d002c2c0c007600794800d080e40240118000240c020712074020a6013540b0005040741d01035610342c0d00f441059000b104110380442045074940a0300d05900c045030f8002440300c2081c1d1003078130303044100484140400c0707405042d01015000c1649214145441d9541e6002610b01d1440380c091078902048980c61f0f0416181106000d070764030303546a0030b01c0c5c0a01ca041c074400f03005160015115100c0c1d100588500c1c18040041030909400c9065140413450181d0100300c5410f000200b80d01088800f002c50603030b48250f5041a00b1556895480501000003030040c8204044001904e08140c01c2e01182601036000154401440000100c440186018103450b6010218000c195400883c0104100c43c070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 350082500 1250 350081250 350081273
    0x402090705130306023a0e0703080f2107140307121409010507030e030d023601021e1015120b010519060801063e0105150d 54
    0x116410614030741080c2c2c021a00c10003000c1d0308150791050300011b407510742c0005181070f09001510071707501042c07440301c0c8800200d800d1608060390032080c2d20744079041d80d140410710508005551040300156500280c0c4400c4c107035500301c0d81500b51506805c3e034100a42c1110b180c000e07031007450655501007119085013400c500c1d40d00b000e07010b03208200c40e0602c00c00851045210304034294142400c10030300c80c0780c024030341c60961743c000f40031030109030500d4001601e00d0300c00030a4803103002c40c1d104056111403100d84141c041c60703036401c0002e08043e445030043c41d804ac0c28011010202c182070307094580c5a400500050025410301d02c013009140d0013042610349800040d8800e645440720550494940c90755040801e48a0303d40c000c064a20b84440360041245103004808005840e01c10700300381035000e1030701e82c001d010b01505101d90b41c18004844e8185a408102102040c07052010780350207003608040c0c0e000861011404031182586619044c00712700150760b1042c01550250000b4010140d8114581e510300f003c08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 350083750 1250 350082500 350082511
    0x609020f030d0503040f0f020913060c0302190c060b150301060801050913120c02100e030c1002030304080f070c09090b33011206090902011b020307090902180403020303150a0e040209 80
    0x200e034805118010b03907500109c0c0e8020b0520001c400040313039080c2000c908031515410080c0500d0b01c104034000805a840840084006090403c030b80c1192107400c01d88040c03e40b00c01480c1d80b120555202c04a24448400554161500b5a8600c403080e0b032140f0500464807801d80c1c001031b4075001100da43e000101e900c0044506044035180100e00c107161a800f00d200d0103000c41d080c0c000b0414224915026040030007080f68031403421214500a0000144065201c0c072000d040a0701210b0005510381c100203a80c8215802c469200d07401c0d0039401d9031400d0780c1c002015240d00840f130071001540412070483d154800e00c0c480d05201d24206012407107404003c1c0380c1072480200c96041c000403600211014140b0b02c82c0340014110600c01213021456440011711b00385000842034558442180b01d9400b44c0c800207854410345c0c820510001d03000615000050340308815208400c0050080d4040204255011001e540110740c41006206107500c5074040050140180c05125003101f003010001e005071820841a40e040b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 350085000 1250 350083750 350083763
    0x1d150606070b0c090d151a060d0b010203130f05043b1e160608040b0a020d06080d021f02040317033301090e010506190e0301090609020f030d0503040f 66
    0x413000804600c1903040301d0b030142c904005612524034140d066000d0782e0300101d030a0140c401c41000701b030700142e40c0b4021010452246030759a0034126840e4000c208580010315204030020545075248021280701515004440c0158100146258940501031003420840c54201c450b00380c2070f600782c0d005402d40110443d890320a10640c1c90030100c03450303c4801204040d0001d000740c84c10400c1d0b030320f0010b0f08007110703800807040041c844200000300c0d2520002c20380000d0340391000b590312003107036000102609a91300000981d0090050104c451a00010b408403a0301c0c80420300c03041090b009a505049000b1031102410313a10343c400c040c59483c2d40d504c005592000019051642420504240c1800d4001c80740628090360450144031800b0740c6c108041000600502e00451034640c109000704529028a00c0c0141c1c0c5003c7c805000c4030128010107100c170075280094000c2041120a081c440b0141400d1071044c1d0080c070f02000b8041c45414003265130f119490258440b1851611a59a110340a44420030190f816 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 350086250 1250 350085000 350085007
    0x30a0c0618060e010c080f01060804030c06140708100b160206160312140411100207090c03060501031a090403140d1e051609271d150606070b0c 63
    0x552000541c0280e050103a040024000a1802040d086400b030000003814048418100307c00400950f08440c1514924170b403203041030f21585402c0d54104c04126008202c20b04010381c81c11390f03200c0700e90403900c1a00c0a80d076149135515422442c0c0c2d4040054091001108030400101c00f04045100181c00618405031001c1c0c64003060004c603c01851000303030224000340319200c4c40802001030340111702681c1080c04a81e58182010782d589000014849001c50190b02d1140040e44041d0080c04464001c100d07242c81031102020f065001002030909000c0c2c980480c0c5054003c514920f1012868244604050700c9180b0703948841d101034489003500303080340380504801c200c040010030f50b50051000c10424940e26802d000e41480d09a029988010302800713004561000c108411944603243c20101c82e940c1c80f49158080788031303a20b01d01c4103001603d41480d41c2d00309503001680d42c3d000138030007144400440c241c0c0c80040c1d410300c5c01410703500181d41c82d83d4094418401c60000c83c5d01141920b0f00180840d00c260725 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 350087500 1250 350086250 350086271
    0x703050c1905212110060305090a060b01020309040c020610080f0c0f0d050f0304030b0f15041112042105130b0901050405191a0a050304060c0e13050912030702030a0c06 74
    0x2200312505240880d0f000d140091145c0c451002c01d00d480544400d0409100b189803110b5800e9035425201d401410464807500038007101e900900403249a200040c00c24400c1c9000998040e40c1d0340340c2036918065840100a000800c450085603c0590503100009000c40064003001c009550326100c10841d4480801c90305c1b00002541004a190a10711240140d0303213070351460400c140c0741c020051480115540c075508000315507403500d5851000d004203c40c00030f000c40180e1420003240c0180390b0b0300d528800302c1100748414000d110300342d1442400e4a4100c00e2001428900071151400745e043c44042000301d00d9811712082e80541c2c040d051602040c507009040c5680c490004407803c0421940140590319484103010404001e104030103112840008503141c070050340d80003041c611009201a00141d030300e4108001083c80b5214101c860f40700100200d406102d10605100140000d5500d8069403083c0c07095036100505085c04e8034454906030b00a1420188950b20a80e07070310b0012141103890319517520f880300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 350088750 1250 350087500 350087527
    0x31103031209010e070512061314070603050f160906050319050a0c0906030219050304110d300801030609032109020a05040b090c07170703050c190521 66
    0x5204280c18800400c0c2e02032200c203081d050a9494000a0040c02d03c0741c81440c0c0d01d0300000369260812100c21003117080c4c2700e140c140a0f43c0c0d0307000381d4032484840c0282c03440002e03107a6058000c1c1d409008100303140c1c26962035011a0a500d406149401c202080c5101002c1202a020750043c5501c114a4011955812184441c40080703e004584842c100b554940d0001101c95010780781c40d001d00581e080441c60b100d01047c03444091160700c2d1080c0c0030801e000002800304245030808188543c800790024002141c0380c9486162900340400000740890580311019003080c4900c0c60906a40d07160301e92005903401c51700c03000041c00140c00c05a0510002d0500700514070500d415822103100c42010000740132820f841040030b18030350395014601c540c1c100083c46200d980c81c109001d03040b01c1d09070303074441c0e5503810380c5003c405280008011030018030001c00e121040c190400b0003480344805d0b0b0002d940300c050b18803404c000e00c401501c202515941c8030b0100110010b41040c0300794413441c51030368010300307020800c04e010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 350090000 1250 350088750 350088787
    0x1407060c1505150411130602210a12050601020307020d0309080f070b03011e0f14091614090117040c031a090c0904080904050423031303110303 63
    0x90501405401030100d240a2400100c0c0784241c280000e041015140c0400e407441c5071080d20441d96680c07030704054007815040380d03100304034283d05040c3c4540c5e485d406903c43c007c04152241030400c9025841020700c0c0c50003101e01c44885602d0300b80300341110f182c0060003030074010400c0b41503100401c07a40d000750b41e4601000360454420b40d40c940c0c80341e05140401d4108010448003400a074000f8800780842460001928107440680c1103d24254500d40144002d1120582c410424032102d118007082c07032050b61901d1004a8800d80e0742e00c1080e20385c4040130750710741c0b00d0510403800a80322140c2b90141d60340c0c0c00014003110205140500c1c1580300456003410080054600f22074098031100f00300100030300400c102401a040c00c0c0c0c40c0340d9901d800814281c81d1040b20162601c00d40d0280c1c0050100101d038000d82e001900054002c00031442c162500b070b07888040700c0040c6e07007031b1001c1d40080004141c1c000040324004a21b0b056040e400703914560f00c2081080c0385c211000d500d80424008062040b4090904 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 350091250 1250 350090000 350090009
    0xf130b0f01030210020307032a08030118150521010b040e010e010b0f0105070f0302011b020a0507140a050402090f030109032019110a15030e101404020108041407 71
    0x60108075407542c4108070503500825400f00554000384076440c0400d8100c070305401c03c0100e02802e26048404003018291013210148001c0012102100100c0c038003102d50104204407004050400c00c8071032104070f81403415002d11440e070f400380420901c200300080c842d620801d2204000000309480d4140c01c00a410b44010030f00400700d5a41d103031030306010700409014100b81071101751046110304044100080c0544290503000e000c120012940c101054400d41c4200c070f10a05a40b00e1550313481e05120029120301c03640c1030036540d503c503046000c0307100000690003d0310544002d210a040342c1c500401c2c48069000f045803d03602140703807801e807002ca884c20b0040d40545482a41d07410100900e00e4801d1140071032040c0f00d03041d0b9501280850715402c890109400e00160080c0c0301003544a1400006141803a8941180040c40701012940400d00d4054200280e01e0f20844241e07100f407143c0d400c0f010100c0d030741c0c07080b506802d072050408030b0050b5000305103280e0054015603030381c04505035400a59183c40d416601c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 350092500 1250 350091250 350091271
    0x5090901090c050a0302060a0807020708070608011e0e0a0f180804080d05040501050d0b0d021504090c020105040507050603070212042403020903060105040b0d150e07060212030f130b 80
    0x14081d08100401002c10702400d400c54030320510a08507008181c0d98081c1800d040305004c0302001203026240200420001802060304856140351103a070010b003031400c203105a94045c46030341d611030031fa0b4503406081000e40311600b45810081c1d446613124000342c030820351442030941d030b61050081c17a80c0300d801c89006660b0003807e255030b40310702d407a070035510f0190f02d9136001c003c00c9002c2c0014491682c1c40300445039042101302001c0784080c203920014005003d01c8100952180d5120301007189120b01c140548201c550090080000c0b0000c150203074240c400464000b840c5c1d800101d0706001070b281600103507400280724411101c10854020750490550f020b50050364031022a00b241c81ca0040880c08208076150f50342c5015801d20010101083d5120418040d040c03285499000300c080585803030042c00701054001988210301100c0ca0039480050012881d043e026019622002c20341038000100f101019100240c85844c50b41e0318034043c44980d00140c4000d00280ca26021b04021500d030901ca0350003a050440c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 350093750 1250 350092500 350092511
    0x30a0803180312092404031404050405191503020d06020310050a0b04090b0604050916120c0305010815040b07030b04181101021501150e030a05010921020307151505090901 75
    0x13400d4515041540d8401428100d80f641d41c14561480d813100075800990508081ca0443e15060000702d06006a40141d508140791404002c40c2c1c052a90b01d0001c1c0d1560004100128080c84526000c1c01c40b42d404060b400480025500d00000e81da54000d40e07010100c007a2000200b0b480d0000102e00248030ba00100b191480071070107001880003807003a6040700c001140c429107007a2400c80803d030f030001c0081c00c0c000c6150b005580c2211080c001c030420320100d00c1000c0304000d420b46c008401b81c0100020b002c4c0000ba4440c406403501e01c0c4030003907030140c00740b90010109401c0d40d60f61a0120060182c0707135072080c1c105403515403009841d04444140c01425124400300113819160400091400842000003848007169000410140c001c00100014186172450f00710102c01480d004a071070544d80041c010480c1d0b182040d000d084c80101c0748074000c0c50001c03041c4012560217940c4100e07568051104080d021100d1001c0510360030030103034002c100d0085200b200705070069030f0703074000750542004454041c030700c0e5140c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 350095000 1250 350093750 350093761
    0xa0f1805010c0206070e01030c020114071115060f0d050703080d020315030604020109050f04110c160902090303090405070c05010c05130512060619090603030e1e030a0803180312 78
    0x28040c4600000c2ea92006003401c3c5032000d0024003441c2000d1115040c1983c600c032440c0001c0c800c1d0403120103004a0340081411341440007004102c2c00005108003030340e0040d10340140200c40004c501d140a0700300108460040f1401c4400c000b0303001c1e2048411103052090140000026180102078000d041c1c89020040e141c1c5054400b03980d07401691815248250880020440140e8001140c0c03820384030180c5155070500080c9000c50000c0010494440c0507410204107400c05000c000740151040c1410b03488200c1b680e03614400780081c0d0040078603d560542060040152500b0240e001a42c8203007a0b1030b0070303a4121000e48980f401c44903141c41c6200000c10010300d000710a90a80710680040c501503560703030500031521002c240c0707030500a0042882069052410f00c5030b89184c7c0da10303502410200c0c5041000e2552454094071610740c10004501030b001c11081410000d444c081e42400290b0044c0141c40052150741e94141203500c0140f200d14a0138094603518040401040941341d444814400d43c02542000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 350096250 1250 350095000 350095003
    0x20702090f04050d05030c0f0408010903090f0308090f1c050109200102060417190504030507050f06031515040e180607021b0d08030405030307031103130b0a0f1805 72
    0x8091584034018041400b000607070010700642100c1d0645000d50f220b45441203200300903c0b0381d00102003c1c00c800b01c1d000c503074514103501924013544aa204c880b807035503651104195091803484043c004003070a00c981c851034240741802041302080181013240040c044050218500d00d128825681c9a6449080100300082e44a032080750070300b44040e120304080b0000000350b07100d000a000a25480c1442c0e030038500d038424041646c180f8000c03041c0c00740801460240041c041c1d00144425075a44c440c0150000d000c0c100107044031040b08010b4503c6140d903581e50083c0700c110030740c1d031000c640280b19141b90f80850344240c03001d031006d4100e04040554a0030005800c08000080c0c18140819800c80418442d4242d000101d0180c06114408103030064519680040c0000c4a0a0340280c0030506c0041040108400480150300c41e41c01d6481c100400d400b11050303142207000840d808141502440401004120498100760740035000c0840460910824403c01c0180d17000b41011201c13000008442c80d040060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 350097500 1250 350096250 350096269
    0xa140601030b060a0c02120f06040b01150c03030b010e0604090f11090a030321110909070f090b0706021c090312090b070e030f071502010b27220501020702 68
    0x40919041c002484460002901449034100700011701c03004d00c2c1104110349429581000801c038110503183d2080c00a4030103a202c5108440071070b00d0404100011408020505440c034480c4016034600c081c801595030244c2c002c080c24a99181402502a0303449070680c0c50000500281140e100c0220b80c1c020890720000964004401d5940000e2051000308201c0d1194094981140e4251034400118680304540994020288903848000b606040420300c0da48000d07001804d01c801d058600800c2036403404400c94541401d18902c80c000b48148004018412000001c0d11040d8000c1030010b2820142d0504800c0340804601c543d10303296200c2d4002c6c0145a048035003200c400751800c205001c004401c0c1d88012007901d00810720302c2031210248590030561400c103c1c16a0302c0b500c82e011142c995803100403c0f01c00c1051004480f00644c245000c1d00304905022001100c01d41142000d0380c6010100302400d1108140141007511400204401c00341408065101b400d61901a0f4001a5124014018400f0080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 350098750 1250 350097500 350097511
    0xf0601031235060a0e090105010f0605070b0a0518150106090f15050a140705060129160611030c030a05060604060e09040302010204150207090e0f060a0f02120a14 71
    0x11103090258203810003204841d040b11103011120314680c1e403100011403103078450f0403210f441c14020b41000050703681544500d041e104116001d0381c09036074035581295217100380d06c1e0040c080e04940c0b0200d508160391381c2002da0412105940b0009c0756090140c030300d1030510031015405011007c200104040ba80202241000c2c0030700e241e0003a00030b4180f131000300c08103041d0b40315581008000510341036054072a24100d0038028403140c050395107230b4160a10a50350002070041842d011206c0828070103940d01c003c0783c0d00e0448150241c250500b45520221000b00b01000d406980c40c5480e44e1003900141081d200840c41141e15400c0780e0340f281800f14035103044440c002c20a9014003001c1105200d1071350460b1240310303200000c0f10f020103907503102e28089002e4000c03640034052200840d19111085500850386006a465100c0e00308002215940e0980e900e50b02e0a4441e01160003840115001c81c0954101101c10f81c030407500507203003200600000b607107408102c8418584990b1040072030740345030400d6181754100c2d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 350100000 1250 350098750 350098787
    0xb071b0806010815040f0209090c01030c18060320030708070f090f0302040518120a08090a020f060703020a080f0d0b010c080423040614090907060f110f06010312 71
    0x56040c5800b044d40d07155035403400c611080200c1c00180c00c111020040d02400c83e405005c0e00450305165040f20b80d25a200c5141e00d01285c100b115152407244590075800712280741e00000a800b61a0030025802400c41a91800411561103405110246880b00071744c020421642d40f803501d440d2500004128030001e0480104000e01c610003008580c0b940c1008800f9250111070010b015200e0b0b00036041100c0044080650310b014501841140742540c0024102024180d03d0300c06403a5038052940d611004a001c2c001e51119159040503142c2c1021000340040a2003130045440051858a91301100e4000701c00c080300a810000b86025902c2c00d50140d82620202070903c01c1f01011075a807401541d0055000e03941c1380715602c0c2149100e66100000c10310340c041000d4000c01c2515240c3c6020212004c2c4901d20030300171020380000c520301e0840029441d00b1120681c1d219584130803c0c03402120f140c0304051000303074288110303504040ba0400600209000b540b00708203d80b20202a1200034204580308240d05410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 350101250 1250 350100000 350100013
    0x110a08090f0601060e04020c0115050f06160602070807080c01051806070e0f060708031009060f0b090f12010e0a0c0b0a120c0201020c03041d0606090105070213060b071b08 75
    0x144040010b02034191807190030b002c140d902940d40807030028018049900c0c003d40c2428003800140c4400041c840560b6000d4818114252262060140034447c82540300401c00c42c02e143c4502003007543d400f40030110b105007103181c0b900003952a0201300d5081410400300c01c2e5503030400c1c08540320301c2142e05e410000780e04000e4a0a03142640001d0003428400d9001030194003a4000801150b6905d23003102d290b16800240c180d113070f0605000c0101081c07214028103036480c0c07a103100455515020300c40841141c00102081d803030450000140078080d042841c2054100a503071584501c5030400b0702480403042c0d20f00b0002c1c8180185030a10f4400e43c0b04541c045000440c00b04101e060b40e661020703240d00020210940401e2140c1c80c980100d00a1066a07076014480c040801c021a01d181c905480c2c0a03c0d00550b58000c0054a03035004101c0c20b0b11404106a010030420080302005050020b5280e511841d440e000240450f5105c600000c694800d090807a51124065404544141d0143d146409050144000d103107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 350102500 1250 350101250 350101273
    0x230402010219030e04020d050603071d1909020d0b09011d0717030d05010b0a0e04061d090f07090c030f0c0804080f04080304060507050c01170127110a0809 68
    0x102c80800c2d00311070000300040b522240034940034034a0403030261000b800465031050440c403440010413050f00d9403446405691390000d0200d08440070120500d8620424104540700c1d25003129400c03907039543c4080315030b44070041032002d03940354062500c2107800341140001d946454072501e8211064081c20388041e0700d803a24022201c1c14001800b4065601c288070900c0340034640289146940942d0040c000220f040500205040a041000c2c0020b080c041c1c0396084112030784000c01081c0c07079403802411110f88a1413007810150002222082e0421198400d032030882d110803003c0d604150240c3c0243da2450b89500807131116030341c10b00c650f2540313400040c0100f00c50760761048028440c40c00580007030322034400801c0d080c02030540036040743c0040120508580d81ca0740e9070400a41103400681050710340780101c0760f01c1c42095000f2046411410400343d03010402d6800d16002200710031a100044414030840c08584e0001380080c410460100008080c00d500c8100e0003a00a105d000010500a4036811000e140c80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 350103750 1250 350102500 350102503
    0x7020f010c03140a05012103030908070c03020306010b040e13081207080106111f0504021813031101020a080423100b0a05100e061e03070305041110120f0605060d2304020102 76
    0x7c030039103090901a040040300703040440140c450000b0141c004000000c0402c100300d0031400901c2260b20907030a8070300c41ea9844a21070040e001d02d210f000b5259006c4000103028000d442400d040052040d002182031150b260043e2301d44072011103908000c02c401c00c00601185420031429580c288402d401440c08929000040881000b03041c0c003002e0309030725040880c1c02c65131458940ca0790201603801010180c9040e003124030318110186415004507c450520b01d08284060080743e02c0f0703809a0315030380c401d91500e5850031104044901040d020241c1028403148402e410310608006028440d40031079400c4011003000340d07030891503000034420325442101210464104d42a0010301030b04a801c00d403980800107204684441e41c4030b83d841405000010801c0c115055070100d03005078090502000c207050303448140105124001c0c5110045440410710388412441a004ac44803140300d400042601035a910100d0300d07540140c111303485c00584881030900b0007a00c4185042202022010540301800c1640004cad = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 350105000 1250 350103750 350103779
    0x6030a020d0b0c0c0609010221040506060f01050c1009050f1c030504023105011a0d020304140105040f03020c01020601050105070206280e0a05060403051507020f010c03140a0501 78
    0x4203014580800143c14a0604041c3c43e410111031056032007524111041714000e42c0005000500c00d1b95941c0032440080e0714180192045600000524803900c0300d00030809120450120941040420009145480700c14090140036065508001c00c2c20380040c6003180c203103440e1510200b0264000c0d00500d03544101c13a003900386410702ca41130014490f15640080380c0050340241c000880202003c51005811170b03a0b010344c02c1c0c11000701c0410040c03079072180010351501225583e506440c0f81c051100c054010300a40c0110b8006200b01e540016260107846001c2c00e44208490550b03400d014120f040007410f406100c140e140020910182030513604100028140b40680754020b40514400300d0501d0300d20081d00c6842c1c002484425010000c02030551000707182c1900c520fa014021014031a00082c1c50602c02c00355800c1c0d9500502078004442c00d1001c881d001d002c010f00e10740c11845441a6100025400e1094400000c0240d40110f415514101c001da0f10007000b804070328015140c4401000b801e41e240c44030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 350106250 1250 350105000 350105003
    0x60d0603020f06280c02030102210a0b1509032b020d090b03010b0a0c151e020301080c01051e03040b0a06060804050a030807090e0108061b0a0804170408160e06030a020d 74
    0x4013940781002142c2a07002000001d4040d880010040d440903865402c03940c01054101c01759000e59240d211200a0f6001c8000b01070304040100f6060540c03414060142001c001c010b0103e8160f4208440c5154016240d9105182e039641c00700c42c0e100d0b00d0341c0e05200b81d02ca894010b0400051851130004402410b00c014420110654404030b05051140d12598a00003040d80000703021450072407201003003009050a40030f6040849019922640c00382690080d6412201418050110015900019561036111000281d5101401038250b50700400d1180598020b500908080d0010b142043d031400845605411000600040104110014000082c00d00301540d141ca001011034455113800d40d11501283c0203c0c1180c1e0903140081996280061034a209805021000c1c104915510340d021492180004440002d05440002408601c3c01e0a03c4410b010034941c80501d0a9a00c28406041503403498100e441211805010403124403802401c1b500140200c0103000301c902c641e4002000c11602200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 350107500 1250 350106250 350106307
    0xe0103031128060f0f061e120b060415080c010807031116030504052d1009091a120a060c0207050109060809160303050301030b2a18060d0603020f06 65
    0x12110411640c0c0c0c004e000c0d528441c000a1048442c02190300c0003504032401031041101a682c20100301d071110350361044c101c90300c4580307000c09030b14181c0381c2d40c001440080c002500213454202c00d0140703494500c0c4002c028400b000103842800303141800181a8040501990105820503401761a20b0415208a80e903480d000341e1002507a04075854207540b03e0150764440381d0310489840395500f04805030b00014480041844c2d02e01c0811401608000000010460305000202202024044140c4503070007000c5c00e03410520181d5105007032000040002442d14100d000359042130111340104040d60140c0c0c000311000e40050582c081c01c010000b0018130f03c910403c0e0402025001068000205200ca4080002030023102c160715a00c1b4140604141c0c020720045032440f0404000540000304040c00e000b400012168103410801c404001700301d00e80199008102c0c89040e0700a910440d0703a0b2100500301445a40c07008640c1a282d0700400c910740240c003590900981c020030881d60703005424010048c03540000c21 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 350108750 1250 350107500 350107573
    0x60503010603150519030b0a060e0117190f060c0201060b03190603050f01060602060a02030601090b0c1509160b19030c020a05030f090f031f020f0906040e01030311 72
    0xc0300f501401940030b1307900b003110310507402c0c140400010110203072406070390585000e44400c103019080f21320521801014030082c80c01485030012aa0384106c1c0c01243c00101c4a0000d000390715460620108201203078050841e03004282000300700d009801200c40c0600003000005d01c0c00c26460741d81e01c4001c00c9607012010ac10170140526456a114101441d082421111041f8182d01c4a500034900c0740910000362103030400161146469008903407045506a6454844a240c0501e0703032141d80004004012034040e00c0c000032030200130010464031840d1098002c200c00c4e004c00315402c150801640090580f510100035065070200703c603000155507406860000750381d2007400d80032400d03e118180010300718080000e06012450218001d4103002400307c6a42034100e550108040d55003961105001245130890003601d610140b640c040c00540c41e41c0d04029213040d240c0e20002d504d5a0143d00081b0f2a03000210041c414923900020420302030604000500c80750044e40014850040c0c6488005004613504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 350110000 1250 350108750 350108771
    0x3062b020402092b060501050a060504050d0602090607030f1107030201081503010e1209010e100c17040503010e07210203031615050f0601080c180603060a120f0303060807060503010603 81
    0x2450300c1d004c650414070000c1c42841081a20125007862240c03d50300e10b81420700100b500c1c50b0501e020700072940c240d00c1c0d16240070b1900041c040990181c2e034055a520b942071240860b547c460724000d20b40c1b10b00c280e44141c005061410701501c03503080c001d00ca000543c4101030500052340c00ca64002c0d005030543c1000301e41901240c002a014007412880c3e00cd00340143c592041680c90020060300d001c800076242c1200c00e099080a00007030900300c440e0180010b01e00a401c00101d074005400c00410880b0b140e0f05481e0a4035200440d00f5980c209001d034003242e10646041019010301d440c0c008019030041303a011300749102500001c0e40ca000c0c5000c00e00e06480800c4a0307004000e8100301c1b0301c03045218500140700902d0614080b50703100c0e408075192408a098240000c15800c100011501c0f055007e9155010342d02c0c100c02440a00e400042035143c2203920903c010407400a1402010306052191040740c122172200c2c80c004080c7c46142c2c0c41081d1950002c5c07c1804120740090540b819a43c0c64640043c1c4513011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 350111250 1250 350110000 350110009
    0x110102040f0605040311031c0e04090503041205070e010f051e220b0d030f0f0504050a03061d12090603041109190e160308031008011103062b02040209 66
    0xc55002194075400c0a00008101e07402201030022a400354984010b190761403024192141e41c050120748403907004d880003030a03850044581503c1c45002410005101900781d1303c0c00c0c0b41d68490303001007040000b114044c0081240810044010344400c504405195140c03c1880c1d0700d03002c940c09503510401c6440d2803803005940300728048450796401000403900080d100c451150f04078200d40c0f6013818600b803107001c20040c1400075034002c0896150340c8502c5040032689080f128071130f08030001000c010f02080b0004080d55840c08102c023a40c00703610009000985c240c00000d08001031045140f55801035100c40e04084a10420f4902d04181950750a95070755440c41c0a010351a0000500c3c1ea01c40340f01c805118450b502c2e034440340c001007800c10382041140100c245982c3e542d000100a80208031403444248006100314000e1604407441e41e624000854481c8091420764003808441400c02070003008100c0c42c0e1400b02c119500d41600201c0006055030b40031100c2c4d034521208900030703000e10307000984800355895 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 350112500 1250 350111250 350111257
    0x20a050309040c350c0306090c1b01240501020f06220816050c01031404140319230a08070305090f070603091106091f0216140916020d110102 62
    0x1184454500413984d0303d4202c0703070201242c0358202410504000521103000b1800326070003960001c03c04c009a54403100080318590204103d260032102c00b881c1010b11040c02d00035240d102c607a4900c88010201503150424a1030380d9076200c02e04552184401804820300822291f03003200c80f040d40280450149d000860810a005000404c0e142c4000b5038014981100d14140029511a20650356196480340044040e190010300b50030b0f5400c001d5011500107000d280d00c1b2290544030300c0990b41000403906e1140191542c00f10b00001203030032083c00d4405071003062110b2091303904403c00642003840109008000c214010841d80902d60340b0400320700302000800109070f001c1290001c5030131994981000401605041c50b049071994500301d549202e6140040a0314880c40011700035901e0300380c107502120360140c00e00580304198020400d840990b1350940205001800f014000d90420303850400034441c4041005148003498500000000d1001c0c0d03022a03201d03000c8030705103840580ac1c0c0000c0c2000c1d00910 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 350113750 1250 350112500 350112527
    0xf0d06151d100603050603070e1e011d01060519211a0916050724020d020703120e1209010915020a1a01050a0603020d0902030a11040c020a050309040c 66
    0x95141000586410071480300d501c146449100ba16810703940b03501c1034080d07901c02d8030496450741041c402403025482d0444c540703510031400006c0c1e003c40c501c240040d001c1d01c03400307800c000b01500c410325201041044031482c03e401801e8514100b4500700744560b41c400000c1a0003000c108103c0e00c50354102881441c4068604546c052100400c030b443c411621084d403400000405900808205001404102c3c046526100201c1c5a031203603481c1400c681e0303c1c0c804092a0108070b4903084080b007504940c40701184080d040311440100f0043c0d6a00040c2409400e10100c16100741c945810011402446640800e01c1140039203103c00003522031000313600583e2054025000329120a01003140a03034110b034006420391610b4005e086404401c1c00040c5002c80a5a09001700354010303c62460810502c0d11aa004182c92040c101c4005111469940003e0519807401415583c151608005a0071071406200c0c800b80a52540010a0010095503c564513802529a101c1c85103541d800b410701c54038002d000301c0d400d0704c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 350115000 1250 350113750 350113769
    0x80c07112403010504060b031b0306060c010c0804060b0f0d03050c0c040212010608060d08191b0c0f090c020a0803090a0b071e05042313020406080609060f0d0615 71
    0x2104410310719007407500244101845641010400501105800c0889000398900d20a0798003c001001c402c4000340d1026100a41011041019480d280000e1203100180d050039a9006003a09103400d2103000c1c0d41b00c402695100d01c4a458801c00c555079001c009104c810781c0350610350740342d0a00c1200f031801c040d40c07800351507080b80c000a08000c012440ca18541d05035007032600c441d142030711190103000c1b2011031140c0062000a00304144442e800c0f82c0c50603291180054904941907001d103e041c40d000350610741d0101d944101c5940103201c8420040542030160420083c100441046090020364034007001001404a030b400001050304c1d0102480703c02c2e059038100b4810b041d1810051001040010701108403440726680c802007103030241c0b00340700312001c40f0074040c40802c200e04c000408903156000c000c2410b81c8a04540012030000f205400544005c2445e2b444802c294902003003444501030000742500c0c481d520807000b41070180d88034801c00e8002038000d00b001070404d0010800e417685a100d5004071450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 350116250 1250 350115000 350115049
    0x40305091c0c081207032714010801061e03090f02150d1515080a09150204030c050f060f1b030315040e010608030307140f03090c0a06080c0711 63
    0x2000c0300000100491441401100b245a607181c07011500c544c0085202c400904082018101081c40380300e80f01c400c10500c0d0902410840c0c4030018280891460b880300740f210b114003070340101035a001085240142454180510705840c0b5006505110a8941e40355050503540c1e46450309000030b0070800b00d0040d6010b40a00e03006100c0100342c1005410040c03820502909000004a0306480b17880410120707800004203d85a04183c0c800b43c940c07000060003c18115600c40141000c81c00d82980381200c6044540b00694480c1507040402d800c502caa0803544c02101c0d07000140c03005403120b40480b0450329220102030307200c41c40c651423000301c0314502003500800d2002000780640b12803030390805a103001048408101b50070031401c449085e52428401d190258005000007000f40d4021040d08104460b120032861030705145104102c03d9400641d1440041d40c040d8a50700d0f0300d0b040110114000d400e003403c02014501e00700071118403912400600421285040e924520607071915070200d440c01c10f81004101a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 350117500 1250 350116250 350116279
    0x150302130510181e0e090a062405090415021b0a08090901150c030e01050417030903061b073e0a14011403041a0106020303070215160804030509 63
    0x1c0ca140004200881c8003598000150141088114403006130b40b0380f2400c26010b1070701c04203402e400360080050b0610701a04003a4000101e0900c140700303861001c03401c15001c01c06403442914260341150001f5000b2640c40c414000810f45400b10b18014654201c4096543d410000700c2c903c603482422600d0703600d0300c1148210310800c1380f50409000080401c3d1540d050076030341c640c00704d00002038091010f00412424103212000c21310426582c415404103040c079600d45a528008000c0740c03082600d400c070f80382d080403c6407035081c5400c0c0b12032034000c0040f0034540703000081d0414031805c521070404028004884c000d8088030b018440c402c03600401c0007250394500128010001601141c0e12041620b02c9241202404143c6100000582038001c1041c0d5540c03200c1e120300c00c04508103a001810030b0f80c100a001a94901c030100040f2064043c01c0154091030701d84c10218400307890224108407c04070030103990100715090001c2c00143d00c0a21141c0380200d03c40d1218141612144100038074290821501c88040702c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 350118750 1250 350117500 350117507
    0x2a030f010b0f040c0e040504080f040902030405010c080610180e070f170121050f030318060a0c0507062a0c0309050a06140f04240315150302130510 65
    0x340e203050680d94040030308040b0040108072094000d10b240401c5042d0704402d15404c05501155109218a180a2800500c241291659003007540715500d0703641c00104000400500b801030030303c4840c003410500031a04050340040ca15242400020301000ac1c2e00e880d400d04c0c07503144004d81c8010700110340e5208035420324440051a030841c40583c000811101044140b502040f802c0e210304075103402140c00d010101c2d240081d910050100d4044d0344034413485114600a030010700042d8010a082d0b80440001e451888803d0300340f280040c107400c10b03d8601480001455008800c0342e00441d8001c000054001100b0001302c690301e110300103014418403106101459580201014440c0c0e402511020f290941d90010403c000c99240030f400300103498145d00380240c010350320203001c14401d0b90700010300b0582c64200078803120940031000d031942002810a0070100c4d415200d00c0c1c000c02d0f9150700007101181420030103560780d032a00c51520300b0143e00090280d0000d990799010805440010062280c110417110001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 350120000 1250 350118750 350118761
    0x9020603070f021e280b0708040b010e070e041d07081e0f0309060f0705060a020301090b011e0813150504060606090807050904172106040b01022a030f01 67
    0x38000d0b100d1342940c090400d0b101210a50182e030024000c002e0101c080b45074480503002c00c07822850585414840500080300111054420205540c92515a00d01410000b103041010fa1180e09031050010a02000c150f2011008030b045105960208408122803452140100050489042801350020200f201907000c11201d20784600484004200c400c81c0b140d40d920f407014000c0c03215982d44104064289410250003400e031b800c203420b40141c203151090301c400b81031550454079841b003158000f0043c80845500d204a0300d48000038a0150b0345c500054080380a09038041c6240f806006c4107200256001e024a00b4241106500c82510460030401e001200041c00302641c007198400d042c044081802c1c0d105106000032100b02e40b004260192504040c88010300020b03106580d410030320603006142000b4400282400c448000c4848045c03441c04180206c2142e0282200b0301c40d0f0b0078600d1a401036071f800111030320b0080c16003c9445010700c440890301940e00c200c1c2812a0103008001c00d5104001e01035211 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 350121250 1250 350120000 350120027
    0x604030809100b1c0c1d010306180201020c1912051609050403050a050d02042601051b09060f0c011d010606090f03031209021c0201020712020d0f060902060307 70
    0x3294800060b00919800b50b4101c0569140c000084592103011a04400188002280a0400398400302c2e10780c0c9011003078131a0b16852410441c0303540010401c125203403040316646840c078803501c03581400ca940000d45403641c090040d440348c4000c1c9002007141c00c015540348020018500c240548911903e0b00b240c0318492b075515480c2942007088002151051400340c3e03440742c0e50507a5020f1920305501c05c142c609420411001e02819405d2002007038156030080d0b6a40c01c2240c41c1c610842d501c04070f00010742074600041805030840d6140d00812000031103182600c080b00001c0310075548401d40814200424040c02210800c10340c02d0404c0344602550422095140c042c0310740080c4481c5d81c464009070b0344003082c0d1140d08103608460b8800c00110344600151905400301c1c000105e0488559000548903117a01d03a1030198141c07100112608640c0c04120b040300925005050300c5603100c1c2a000242e4095000c040034040304060701e00c030010040c8951120819590040c541500c0e800c02c0f03034004004100e808203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 350122500 1250 350121250 350121253
    0x603090309050306070504030327060818010e0c0f04091e12050403051c1709030a0f08061c03050706140a0b09060d02040b0609180601020c0a030803010e060d02030604030809 76
    0x8002c100da00740441d800d84070701703026114503141c14950798040f20000b8400380070101e075000390140d41f000c450301f06080d08000c0010b03a43c0e46400d8109415050700314030380306603140d145a01d130441801c140d1001141d42ca8880f613003250003101d00640b001c0810054060401d00500c211000445a019400381c4d09032840c00d540650704c210034828060170140c40c0c0b8403803404060100c4c0c4c070816000c0301c845185440c0a0805c0b00b02c0c1381205140141002880b80710006480e0b483c2c481e00003182c4812602d5004140484901e06072600d580181004404a45003648006100051000b070392138007007d03d0301070340483d0b480d6607111904018204c00340302000007801d0306a0300755041c641400400112440c0403c45280030390b03401801940160390030780c04c1000a0a06c0d18407542c000005220032602c41ea2030340c0020114070202c07043c1802501e40200020304000c45007405a10843d6090001e20200301940c0550781542d002469659407a00c8400001300800d00103400298544101010042012340c800d920303038043c2002c0030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 350123750 1250 350122500 350122517
    0x601060807031d0a060b060a0806130b120d1206030b0f07090b04080c010f08190c090504090803010e0f0403050f091306080a060c08010510030513080c1b0402041a030405070e0106030903 81
    0x1040207810f1003648c01072030000704624045400c0e071034441c081c1e5240d0224a580001c0a00000307012680c20900e04115480c0c980010384030001035a0000702c1c10b03030301c0311448008000f01070a6682e44400c2400107801640d100d944480001c003003500503c8128040c2c100f91031013540762550303500180e641e1015a96001c4c001409040c80d518118013544644d405040908407000360550882240001044000300a82c10001c2c0302c44005000d0304c4500c11526854001c0038025500d44c18501c00c0f2000c0b11000d0302e41840907121004020110358042d060340e04400040b0f07410790340d4890035000038a6850b810015040e200c0e02d0000e0005a09900003251401c02d841080b0511080c4a500001d550b180000d01c44c16801c4016070980c0300c003c521907031040e940001c4010f20468904200d03103426031250230020703ca904940c405042403040c001100c07550584040104d5080d868282010350340014154488021122440301002003420071005100071000b51403400c1c0b00400c00e40c1d550400074080c191100081e004140c811 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 350125000 1250 350123750 350123771
    0xd030c020102191b0c06030917090f06220b0c0c010c0302030f09010c0c08030a08090109030905010c020d1208012c0705070f08031914090601060807031d0a06 69
    0x180203940001c02049010b5400045000f000d40310901d10b40444440c0550005007400020b0f0002040c8000e051070b56000903240c0c1396468054a090058505001940c1c014403403807030255500482da00c5041025210581c442c100301090101003600da420691100c090081d012403400300030405011008100000c80301d445022000544200400303d0000e40160810000c0320042e80049008240000c010b14046050300000e869510b0200900c3d04101003c3d0800a000c081060b445070501781c000000c1c038000c1022007056a005414040c0e688100c80c18072801d2599034041d0369984000e0038481c1e0b001802031401104540d0010102c0c0400d0058040c0c4049020024a00c101907a0200d00180001000d0002d40d841c0c19200f1303900c58002c02c208a0740c0d0b0380100940c00014140703901550103125544a45c101c00c0c4803101d0100c00f522210f000310303418103101ca130401c4100e000009880e1304498541c14040314689441d0022000340000c082d0070040000f0100d000e17165200700049001c8924003c0108000c50244c0c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 350126250 1250 350125000 350125003
    0x201110f121c0b0f061c02030903040821120c19121a060301090203180d080709050405160c08130e010e0702030406090b0c0307021302090127031506080a050d030c02 72
    0xf2522854001940e40c584064a0611340003e249010125244101564000c4801c000f0303640708803a501025000030802b042500000c200b1248151f4461441500c0500c40c403000c84640c0c000d000c0c01049545158000c1481c420900e402c89007800d842c95504040640344840c0502441c1d01c6000c4141d9452034080c29280c00c1e411008200d8038201e005041918507440c01000704040e4201404001942d21101c000b0481c104082165580065950310380260501d89000f0140c50100240c1c00180503e08002c204134142c409030201c80c0801d030840c00c203292044100d091490060082440003c40c550900001040b10030041d01903e048400d8141c803100c8a0f0390b10394080b07031607016a11035200840c0040c01c00b40481407004000d404004030850803241000c000e6000035081080b07a14840f00d5043c0c1c001103956455a1041182001e0b07001c41d10100d10300440580c1814a40401d4032001e0a02e1610208507070408206800c6000285600d00896008003d00d0a040d602e070840d013071215010900d0101d050305035500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 350127500 1250 350126250 350126261
    0x3270e09101b0e0a08030318101a0603040c0b0c0a05070909030509012102070c0513060302031b010509120c010f1e0c080c060109020a030c0503130201110f121c 70
    0x1501c1000c814041c40c26010f60780c4108a41c0b82503400011041d0110b44188100041c45c440d52841d03c1405280e134607a826541410170a10000d003106040025840140a510749100e0070f080069904a82c4c9541e54104204080036a0b04000030041e0001284000c40c0d40c00200084100c0c0644155070321a0b43e02c5042c541103c0d442c420003030125900b401542c480358040e224038025603e00205114200c0c104600450899000c3c407000c07510b07640ca454040c40142007400c250f0101c805810010800241141c0001c1d0741c0300e40354940c0342c01c500c82400718000c00340d00c01c900b502c0c00c8000140020b03501c4500d2034400ea485550b02c1139a140000e201080200d4040d201c1e1107070034905425000d140110002e41e10044520281d1444150781c003200c02c00010142040411106008003161030340183c6807000e001d0010250b41c46030011100b001014402d218540015100c10f260103a42404c00603200d0f02000300306400c2400f50300d4140554001d1350614566400316a005152001050080039090702846110004548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 350128750 1250 350127500 350127521
    0x80601030b060f0a0b1603080117060a020a020703060f200f0304031407021201050106090605040e010b0d110d0c09050d080d050a020d060803071505011203270e0910 72
    0x1840e95021942d0307810300b800040c030503081c090558607820380c0701c3c4000f0001d0f90007000c102d031024074000580010305900840140c050702d00346289510004c401500b07103503a00c1d00030300708400d01d44d40054141800782c02003141000965000c02c091084854240d00b84000740504a0085d00c000c0c0c002c40ea4040e640002001c031865039103091405411519240c5040f60081c68040d442d03038800da007c10440e0003585c0c4145020703903030084180c0040390660428000411031069036110b50140b0000b4802840201411078442d419a50005515074580030402c0c0e1640c040c2c0313076100180384200000a0000c2a80c2283e411079000403200351a01d01c1102c0d9258240403a00203000006025010300344140c040c045425000b840e00941152005424009001c07002c0048403501d031302104040d8400140d0a0800c00c040e0044036403400a401d04101540c03500c01040301c0c1c00007a5400a0030003aa0f5145c4c0007852250300380c20352a900403100d04900064903000e080500c1c2e00152040080e61003414151400c0c46507601581e500300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 350130000 1250 350128750 350128763
    0x50405060601030c090e0601140f0c100519050c0904020406050414030304210f0803100824041b2402010f1b18080d170f1b030a0e010608010e0708060103 67
    0x540341607070107003007004098401070410181884a160700c1f01c2900c00b03071881cae0801101140d40c848849500034942a49104800c1c50141028100701111607180700790140c24600e00e1010501d42e90b104100c4001c3d209001400e94490310110b030101c0c5950f406070160068601c45924883c01c10003101c10140d99000e20312440e18140c0c140c04e10903038000179014140000c680b281c2c0135034044112680e1070300b1094000319050348a0300b04021040042610801080f050710603014004025241c80c2c00c03820910100c020006410402094010300c10400c4480030303000203284000c00c2e03488801c0300d26890542460302419540040d803e041c00f01c40302441078405d01d00d5007058019412071504180409843d02e5105220304641408185000901031105200010084110345e542d18031801c194000c071020840007410414054000c1020405800c04907099188510408100b054503995600b004034060000b0141500e45542040700006a8000540040c1a80242c0340300381c5004a4071881c00035514902440054401d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 350131250 1250 350130000 350130017
    0x1c0201090b0112051f0b0d030e01030c050c060c07050f06010e0f24040b060d05090706030e1605130609090b040c29090102070f0f14010509060306120c1003050405060601030c 76
    0x10301d00343e51000840d00082c5d07100801e1a01c103034000180b101840c02425400301c1c0390714002c40020360b0300d4810700c00400140c2c01d007542000d0540400694801009200002010340020701d40b00340101000360440c00c88000040342c541e580c49168844040000f07a6112074049040340104880c85602d0080c2d1041c001c55107400c0c06a68200f0b0200310242009940c1c15170072010401143c07528115a0107480e10400d4840024440903142201c020122224a10301e9041a00480040c1e44651241103900d0103c1d0000c8a810308195881c041c500010001076101c92440381c64901e00344c3c2009550007459108d1801600c41c00403041e5500c0d26440004140c0e46107070380801009a04210707442040300a051440810b20440e40c0300b507124003a4030071038181d54001d00c0001d00b260b2400c21070748500c0c200604030040207280c8142010080c4003c18041d00016003000e00c90140b1072000c600560040051a101e104000c00075481e4841116000e00104005e9806988600810000a01c103500074042e003441c0d4001541c44460 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 350132500 1250 350131250 350131273
    0x2120901020c0f1314061203040b07150b060703020105040506090f151008010c090312020c1c1a011d0901060e0601050c031201030804080606150d0e1c0201090b011205 73
    0x8004141e0143d036584280102c2e00791040c500b0b80e1040f9440c507168800400c0440c2030072420030079408120076401205030306c20001840030a2191060700c80060b030104022038102009090744000d8000c240e000c4c0c0d0007440c0480d50005041d4150481d034003d500940a0300c055854070411651111103c1c403075202140e10802807690340c000003d00f09540300c041d0540a40c5030980720b94204d402d407241c100b003840c00141107110a0007404800302d00d55241024500080c96a0990900820a0144003080d440109444c0d0f0088005204c0c00c9410003441c40e60981140406686031810200d03186c1001040d02003100c10320b000540c0c415014821681540d508100c80040b994403480112143e900944034041a4002800b0007608280d05d201000d003c0c51081d000c180d250747c244012981350000007410f07039124018607042c0d11040101d10702140d0080460440c041810381c40303007101030700d002070b910b610070301c0c1c440740b213084c181596810341c0b184c04c1462050b8000702c0700741d0380e651501810406604010f0031036000382c1100355 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 350133750 1250 350132500 350132509
    0x4090c0e0a21020a060207080601080303010806070c0501021e042315070c09050903041805060108181207060603050f061b071109070f0201150f092c0d02120901020c 72
    0x8036640c1000848544100c415030124890013007650010025134410081406186020b10015026102c0c2000850666240080c159501d0070040d04040c1803000100c400010300c039082d01260412000344c10407031049020031035182c40030fa01c58441c1c00c5880c0c81c41d101684504500b448078a003081e5005003680002084121030102e0b90703200d14000c50b9000710a00340060095800c1c0a140d104001c01d6000e981c9031840e00040c241d900d512aa038000d4101d1070030342001216030300081d907030f42c00410240008402c22121814603103095680038607101b021030041011030070044141c0048081e00c0c40340d0103031000c4e980d00c592041d90702c00701914442100c8041985101c000017120014040c580e010b1034100d040d16070808007190741c03d0300c280c89000018064544549a031030302400307440b000e000d40203075001c1c0c003500e046100d02c2c032200079010340301d102501c80e407041e010300240c0301e4402450070315090314034582417202e00c02a03902e011521018003d40200380030310440da89014286e541401040e00078000090b084020427 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 350135000 1250 350133750 350133779
    0x4060605090f040617030c0105060901050d1407091e0c0f050406180e0106020102030f01301109090304080706050a080c071a070c110f150d020c1204090c0e0a 69
    0x15003050307441c440000c5c500d00c09080760001d00901805141c0d03c01010034a41d0948034020151030080e101803004124585400c5464201aa0030280e0002c100e9548202035041188650000c580d40b0706100038071204d040d1006100340e90a80c00350302048a28003076101651a92019004417003c00d40910042200d640110600041d8400748000c00190340c0c1c40707103904105008c0030b03002200143c0d0b01000f04406807040303a1905000d403410300309080c55501c003c4000d42c0520034001440407032250900ca220100b050800c07011820800062101d4800d00d0300e24000d55403500300c0e118070801c5108810340011024002e900300ca14000180c1d031030210f999103503007865001758005201142c900441d42024070800d510390140e5406050303103640e140c0c4120001d0801c1c02c091854280318038030561203021171003140e50341c1101103810345071043d0b00c8684451002c6107150003070050b60101c0c42c1c00d000f048100203501c80b8140007001601d1401d40c0800c41d1400604080340d50904002080f034104d158900207010900c00034124 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 350136250 1250 350135000 350135029
    0x6050f030907120f030e0306010302101d040c0c0c0f0605030402010c0302030d06091e0e060604090c080d0201061502160303080c07060221180a030e011205090601060e0406060509 78
    0x8580c40300759a0366810600410100054a0480c00c1c2e22118041541c0036203034980f2106d00f24003c040c0ca50441e000104480310001c441c8050010800b030303006219030000080451610700a0081000d030100e120701a202550503e01101d01c40b80b04040800d00d850501a02e44c10785200d0b99506007155656401034661220380c600c20780652105101103900c014890082c134001d400c043d1004111030700e0b10081c0ca9056104110b11a01d42400c100a141c42801d0000b91560701090407240031905040700e05104414010300c2e000701e4664055250283c00c1c4c2e5030150011f100b02c55405101146200c80010101e8498841b00440701700144100d1040000c2440351004540046101c070703201c0d1501e2500d559610490740720304010a0001500c0110030400c10b401c0b05c0ca80d03403188901942c81d900d40101c044864850b0002c14004003031180c0100e04807120791142501d070740d5103442140108031508108440c1d03a42d903003013480b035080098441d03001da0585081c40c0c0503900c104c540e41d4850780d040178110402c220034450328924 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 350137500 1250 350136250 350136253
    0x819050a0f08130b10090b01170a0b060403020a0b0307081302311a04050105060f0f03040f0f061508030a02030d0f0e0a0b04050c010e0f09070309061a091006050f0309 73
    0x10b150f40400d21a410300d5008600321040034401d83d00e00b1442c001900c0500c28032030305100040302141c4089001d004400d600080c1c01074001186100180001c0755070249d074101941081d0394600c085070941500000390300480c00c648600340140d8404081e82181031300b03201c00079002180c509005030075440400d05900309000c0001c2c0201c034040010000000c480c13030100e0708520b024031510700582078145403081c0340c017520040c0c1d483c5190a00402013001e1a00c0f070400c054082c0800040028103211400c04030305119548040000000881070030400d0180400410500740110320800010fa5908004202c0300c01d0012500614102103072040781c10010010440c143c039421751201c0c00030301b07000018407814540c00c0c8640003442260030030341041403900c220f80c0c1940e03051182d200c010502540e05d441440500c80f0080710b404200340d6903520110701410441d003000700030745e040c6101040d80c0c80c1c0000c0c4405030000300741d42c0d107050f40d41d4004115100e10300030300c94800820070400000e101d14400800030760303202c2030340300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 350138750 1250 350137500 350137531
    0xb070b0711011503150509060112030509041e05070c02150a030e070906061403010b07080c0a0f12020d08060d0605070513030308010f051e04021303050304030819050a0f08 75
    0x11501c40c00d50f4143c50001c049003d1000061007040f8480c0c04118903650240703000c020700c0ca031441001d940e0300018050704d01304420504042c001c041c85013040b0b03080c0f040c010303105002104280c02c2800c0b421007d091008400c038140800070741c4452140d0162044076030010513482d080810802e11241591002c10503100b09078882e541d0450075503042003028000c01e803581e0001059480c01c1300050020054903080003c1c0401040104004205407045d15410f907000a0055600e0038a545079501d80400c5902c000e004009102c281030502204440a00c180c19240e026070b164011900740864604100719071494dc09a58002e6031b4000c103680b07034810b41e40012581002c40c5840440b900c0e4584201480e8005c40001d180d05005200b160404448480105810340340340502414207180c14040030451525203000360340c04500254808401c04480008641082c10742ea80c641e01d078102800d4030740c8441205c000c100b1000410010080c03040781101d00000780c03a9130320300345481c007110101c5400c3e8010345441100c50624 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 350140000 1250 350138750 350138777
    0xc060306151715043b0a0309151101050405100506060702220207230705151b120a02010e0d140316120501060305060907020105010b3906011e0b070b07 66
    0x10055003014003e1105000c400750880c3c0c1170040202d001144d01c001c2d41050b6100c100094210034001c040d02d4006408200f100c2c0850f0007156851401c0c035045985608002c180400d000010444001c00030b2904401e0099036a00e10502c040f61140050094100228110a0444140c0c00041408004d6800c10140c504089a103400c004948440280c40c590054540e21540389003040107440010242030714008150810110b43c0e034441e00610000c00c40b44010340030b555440c1c040920a042c0700307441409580c0d882c1c070500040203009280f074418078602d0b4031a0141c0a41c050f4025440d4a1190100d00b04142c5542d0302d03c242c0340e205400606120007402000c40585220030000d0283d0780c041e00d45560005034030b00c0d182c020400001e101900c1c81e01564500710040c401000c141003250084507501c2880d034880c020b42020006503020500b000c252503108103190180000c00800c511f07040ba025003c90031072801705800d882440300b40e43c1c428200c100008010704000600032a2526030b10071100e0034601e07004640c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 350141250 1250 350140000 350140031
    0xf0409050708180111180f060d020d0b03061005010516080f0d1d06150307030b09030c0f01020c060105090711100c1d0907080402030a0c06030615171504 67
    0xa035003400116540c041088940025503d00c241010f10403030007803007485d107512804000c0d0300c24005100484c91503a5014601c54541c47d440f0140900d01a1903260317607888005400000b0b401175620b01e9542400c03c01c0c140060b2070b0000d62140100c04031900700d40314078540b4005607669401510025400540300c1245070200c3e2411010b005441d03100c5140355980d0340300446041c1151454031141c44040600010b11384542800242d00c7d40c09458910006900200b182c0000c0c589001940010300d001d142004000081e60040068030f00c9000b5901100c03034601c01c03041854240d0280d00c07500680d950241d00100518034000002603001000703030501381160300d07010030350904100c09204054840c03030300c0b0101400714a1780324034000c10700c8400b002851200c0000400007515414094405420889140d001c902959400e02c250340d101f0783d00a1104100b1503580340050090100c030b12540c1954407074000110002c0c1d0040560751241c0500548690481c0d481d100710068080d030110310300e41c00941c2c1e100c90305111281c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 350142500 1250 350141250 350141261
    0x9070503220312052a0a030e030304050109050c01090806190603080705010e06010b0f1206031903020c01021005250e06070308181501030b04062009130204050112020f0409 75
    0x20750ba0f600c40140c03141000301d080c0c0300c1c05042c001d29164422800614400003400d00c2d840e00c408000401c1e601c0441c54011009800d01e480491101d000000500080040550054940c60301ca80c00b90391140700380c08010f54a0b130885105003400d42d0003403000540300040d0007a8203050b2200508c00080d64a49988802c00345030880d000840d000d030356948004d90804030030400507004025030401c007450410b10110007041d03401550000304402d0240000f0407543e5070306100d045080c108100c00580f01c6a442e0400940d565805401c030341c058040c03503054200b0b02c0f400e4080c05100703e80020b403009142c2c8092001902040c402d51940d0308200c00d03c2a244515501c0800130815103002e03035942c00700c40c240740701d00500018081c861841d80358455055030001a00b5800034504483d001030107607102c0ea9032420b00b48040d141c0c440100d070350030f0300880240c8540003420004e803a00000a443c4074840030440061401284114064240800c03140b00c011010a0071a030001c00090750784120287c1000e940d42584403e550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 350143750 1250 350142500 350142503
    0x2403050a03111c08090304120b1005010806060702010e0f090108010b010813021c0f020607060c080f010608060d020109030501060605030103141f0b03160303030e0d08060907050322 79
    0x401540c0e40d4814180d10003240b09002841401811050400200c111000d1003074a01032030901c528100003c40710901802a44e008080c00800301c0303652601740ca03045070142e804584030f030204002c9802c0401c00c0d52040142512a050180171145011816001502c0300070b41c03000310380e0340210145d071400d003a903e400b0b2681c3d000740481e01c000305070300c0004400035040b4000140101c1103141c81c0700200001d03030380c4c11a128403010212100c0308418080d42c2000c0c04003107846503010b500021f00086881c00c2280992121502c480140d40701004c50f1a0341040c004100340a105902c0010030170404680c240c94130303031080b41e0b405105052400742d40d60b803070359202d003994803a80c0020081000400100306010312440c0c9112045148070150000500300c4a4048201d400304c40c1d014842c6503144d8812a0381d450070851280c0f542d8280b550010081c4e41c07450020054100c40480f105076010300010a81d132903020f80500b5000384801420052280e8803900100c2c0d141e00004d01d040800d4289600300d11070f1a5460803c5170070036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 350145000 1250 350143750 350143753
    0x9040e1e0c0303030109021308160612090f081c06030605150102070305030f0d06050306190b0604030c030209070219030c0201020d1b0f0206040f060e090603030c030d240305 76
    0xc0c2540c00c0c80c0e10302000d125440c00003680020456a085540200441e419294400e04c010b0310b07042810504420000c640c1c010421030f04c12900c0604101151344060022220a9030700c012822a450580005442c000c132401840100c8500c1c1c014001142000502000207035100018040c81d40c1e5202e000a0b03030007070390060300c0060b40d4509100b003484c10140c8110b10030794280020304083c0e1850b540d02d0b0340c07071064005026001c100402d80042c1000c05401400003000000d00b00e4045060980500403e0440300084e0b100091519901c03172018189801a1003c8036048410006242e1660b028008130a40013480c01c4118000d40b075403a600100303c0d150803400d240c002c0c1d580e29a5181d542c400079142c0402c0344111400d0182640301343c40c00c1c0d884085401031059002c6036500224025102082c403074010b031b030011842c411107101d0100b1201d0f4003102d256076992040f528100c0544880701450785a10640d4009000398104100c240c00b9030409401aa001d282454502a80b00c005070140d198084020382080f20507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 350146250 1250 350145000 350145013
    0x309082b0b01030b090403032703051201050a0b0405040b0613061d0406030b01180f020f0d140106090e04050c04090b071709030301060f090e07030b010206010905070c021509040e 78
    0x25844600c16007640c2030003801d0030000035006400184480000400040416071a03501c54070340d003a200410038243c003d06410009a070750542c80c0290150700b001c1d45110210107807a0000942e03103000211070040b19203400506242608003018000070300740d400b880c170303030070140400100d1144140da0616400034501545d44042000c50049107a50030502c84845c0d1b80b0860030602e003480403031008684c0c030f03044071441c1500d52806600200448040e01c1803800c5401ca452000c5000840822624020007088198900c200102648030300343c441d83c207a0038000e0700d001895590f401d0003891842c011050b009405036045a90030a010800941a5100031800b21441d960582c140440550020402284d01c0d04582d6900ca00d8940420659540d0105104a00030016404480e0350710347d019a04044c050800c80320404820b25041c080600580b030310800080c01845a44d00010740301d8000d100c0d0304e006121a070f40c5c50030185202d408124014011010041085904001c007124a0307480b881800d004242540141c0f46 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 350147500 1250 350146250 350146327
    0x160602040e010e0c040e06031c08070906110d0e0127060e03030a0c0308070306050306010b04051206150103020d11070312110708030a181202280302030a030908 70
    0x307110740180d10403240142444280900e104520042d14182e814040040741c103942c8841c0000c5c41d0441504401500408099805000c150302100703072403003541d007500c80b422495078913001101c0400c64000c03034050035003100100118003840381c1a0480c420f036051401c0d41082c00c05a40042c4030346080c15008100850038007003084101e0f0885021800070350214007542c2401c5114001a00c1e850810780d004040080c000006518103000b80c0c421030282c80d01604039901517031140d50f94a402c1d445030207224420b90140e003401c251440700081051091038008860301d0000311020040d0040c1d00240301e02010540c0700d40303503250905021006881d480307001c0c2d41c80c40c40c150f00f03480405040b01c4664440d010603074030401c14070002c00e02031412030703400440d51301000441152996403c1003035000d030007004101e50590071081212550001d0041c1c031880e4940204050994034502403e40d1511048004015800610000d0105402a800204210b00410600f841c5c0512416a030303100d01100101264a003a00915580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 350148750 1250 350147500 350147519
    0xb03070605090102060402041e06032a061407030201060321030605040b060f0f0f0c0a0b0105010201090b04060905070e0109090311030310030f050307051204030212070302150a0516060204 82
    0x500c940e00348149041c500d0300000303488590082029002e603898010340c0d005650605003541c2103041c0c0050401c8603540381c0c945100f03110703503104941c0550700c00e0282e80740300f034803e40442404881d41074580c4c281d03a807040e001d9400181c0088405400350b561b100c80000110f030048040f044003801000e005080d4060a01c005002c90304180c220501481c60304240301040c0d201c2404480340111429109030300c0d012007041b0700d6018401e500041c60121408104000e54042c0040c801c0941c1d40b048200f081180c3e01e5500480c2210602c03038001c1d1110f442c100205001c600141c1c40b007000c042c040c109540b901c1e5111440c2254058087c0d00c8681e42995030b002e40070605501205c1004040d402c40040c0d861030510f4a08458402154000601300c42d02209103041000030820444042030340c4242a181c90301c001c980c40071015009031100303901848150302c801d8003000300880c1d501e058943c0104040b404548407411702c20141c00c8044031030300340705003040780d184071035941c0b407840c100e03188a50b0015a07514140480f88 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 350150000 1250 350148750 350148763
    0x50f0a0606050102240106050f0408010e0606092d0a020d060605030702072301030c1106010902030f090d080408031008030309210f0a0e0a0b0310060906020f300d0b03 73
    0xa0003025450070001d29168656917032541110501d16010b500d0b02c40004050803244540d038806207840d864210074800303009002c100e89105d0881240c9044603591401c0c05450000b81e03410104440c840025090300c9c0c801c503061815904120344500c0182082d40302440d035000c690b102c0c1c00c694007040c004420072411a6040140d60081c00f017001e9025110020000d14070300c0350844000c0c140c10b060702d4990013000a8404d80501c00a00103000445142e943e60300c21010080d4000c1c0c0300d091003007110000048001800041c81e842c7c128540d500c214580c6c0d2191140c003000e4102402c410f400b46e07110640000e4507201000594085c08181c400f6280c0c0c4401580e24260240d00150002221042888a00d0100d030000d4183d803058402070030080c210b4481c0400040c2c040c48990404000c04030040140881520a01801e030151402501c0d00d1700ac180d00c440c01a0395130340b010070880c1003660180e4104242c08043d29420321041041c02c880112980c4144001c1045420000a14091580e1020a03802c10300d07080050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 350151250 1250 350150000 350150023
    0xf0108060601030e06191e02132c04140a0308090c030a170a02100903030c0807020106210206041a030a060f0e0c0a021204090e1b0616050f0a0606050102 67
    0x804c54480040303000c907218500103111610b280c1c036407100090090100d800040c440d0111704454001d0740d180a2520b802504003075100040088003200c0400c2d0407402c400300710303a88031000040c081c4d44114443e2001c4034600080003298090740d907258085030307003508101050f00e036407207611441010300e0451001e0340380c0368101c041c00b846a80310740304513070116030741d181000184d98001b581d107565010b2408040c2d24096041c08180d0704580f801c142002807613410f60200c4031403625a40e0348030458035884800c07401c1c0c5105000340c2112061103400c0489008212a890102da03201404990034990f1b5468080c2d1114130211406084190020070040d51044511810000c0c1c031113031209040340c50500c0702038070040d81c0052051408400c0000c3c3c030b8082a000300000902c103e50003000540e52038440a40d400a0300000e4124070043c482c201d8807002120741841d0107091030901604103170800d4130a01e016415498072a000b500d240c01155a440d8241c0814030046010078012040411a0391801000a00c0d1620702c101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 350152500 1250 350151250 350151257
    0x17030907051504052b020a060509010807030c1d010c0605010e060a08010c02060c2203030906031104051c02210d0806040b01090501030e032116110303010302090403050c060f0108060601 81
    0xe2065545d29038500c1c0038900f00c4801004908143c0a502002105105001e90b00500b14180011043e41c0140103040d03030842a6114001529000429402d0303401480c41040031503050017640c0324010042c48445803000b0140b61120030748031340d522400c0031103c00303800404130107106204000e22428800c2c01c0710004c0c1040d000030040142c8002000752a5200901b60000c00c000018031506003011492040e08000c3c00b4100f10851280d480ca00074004402a214101c04030303091613000103410103080147c504440001d880400c114800345001180d911400708100c0c0c0c424820103060307500781000c41c0b00e07449101101d40142000c84036044094010140242024801c5043c8903030881281da01040380412100b080c02c0c04214903c062220714258010504046101d144c451000c000314100304140780d0080204030041c1000d00403a01e4210794150707500301c4071500380c1c0c01000100010306007004015800f0380685401400c100841c46143e0500c1c0781038814401c60144000141720002040c05007940144007420f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 350153750 1250 350152500 350152507
    0xb0d030207050913440f0304020f12011e06030c0b0703051606060302030111160f020a05060f03180a080a050904150e0405060718030201140705160305070b030103031209170309070515 80
    0x3d02034003c1c410700440340310021001c00801c8c2191104031205260581c000c0c401449800741540440c002c01801c0c1c1141088000e007400740f80c03403c0c070901c07405090382d401c04105d0350b41605052080100391320002048041003410041003c130f00d008880203c3c40107100b5240418094690700401d0300f5110310b190002d00d00c200030003a00c01c14410220f05681c2556004803110103d00850000400d821229844503411030390025030300d4241460100150310400c2c1c284005199280201022a500e44a01d10000c011400410001c04058040c030040c2c0f100301390041000c55121036101d43c203202c1e40c113240d01c2386840505d0407003031004104013070107100e900c42c0c03c0d494403801c10050181d1103041031100d4030019041c082d0740d90403807050101d50801c03540d1b0350780c0140c1180c0c0740c500c49586216041507984403d907194011142c002ca034660460007168100c2e6007682c5c840303011071000d0078803600400390310104686141d84203c10881c00083d500180d1320520108015016852600007402400300184200c98205031041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 350155000 1250 350153750 350153873
    0x15090612060608122502060a0309020310050103021005030912280f270b1207021e0631080301090e011b0e12031c0b0d030207050913 58
    0x2506a600c42c081d900740540078625103d6501000b1707003140c50080d40203a8002402003110f07406401c031003003040c4260b048860103110001c0c44012241d00b80002503002c4030b002015620781e882400035581202040050b01c82c2011990401407455000380d5000f05c40d011001c503004d140d480d0401c3c0000c2000c289080c122400840d959005040c00c4a1611401200e02c03060b1440c50002c88800205014003e48000d2a550384d082200b06094240100c85400041c0300d10855001c00f2022015514801c0c00480700902241d140d80c98403540491b0b07111010151424200080701c0b82249501c03010152500884000780d40354105103611042d100341000340f00940e070404a5540c013488260020244012040c505061003000500026845000c2a50610950b100101c1c600a61281400303280c0481402d92a0804ca10b0040100780b2680710309036030b00540580c01030841045941408115207070b014400503004102d808135035595410410902080786800107088403440d2042d071421240c8840000007a01d8140c145610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 350156250 1250 350155000 350155033
    0x31218020d0210030612061b0212040b031e310c21021003021c0504020f09090313141201050115110102040306021602010e0a05030d0315090612060608 66
    0x661400030f00403070144500c29240b074460f601c040050001020300c4480022982000e2010b0054040400d080c0c02c403031119000c030140001400d02130140388013451070800d45040d07001d86140e003000304412a00ca0100b8640e0308400c1c80b030794101c2e101346405940d150107041e40c06001c0301c100300b072090f40410f080e9581c800b03c004118a001c202040741c1103c80350b01e00300c11610b80c0b0054a8000480c009400c09011408601c80c00d8040c2c01401d054160b4044100d007070080640d414050b0f030317001c0d50060340003038034400781c9001401d02c1d070b0b03403550b0140c080001c403485c0a403d9040c2404c18070280d40300d4480903c8600027405a45031401c001d50542112100900055050a84402809418800500600801048090854200390152001581c00c000d045403201c0c40c2820812240c603200c0b070120300041d40c0c030300047d900f482c1054024081d520050004c1120300a980020780c014001174284281c0003d0746040041c20800c94020580902200343d00350190391032034544042130f1100380c0c018555a0704440558810342c0728 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 350157500 1250 350156250 350156269
    0x9010b0307120b090a020604061205060d0201201e03070c08011a1908100b03010b01020a0b070e0a0e090312090c0d03120213090203150d0c3003121802 66
    0x3c03c0036405260307866410b40305103841204035000350080030200d030000301140c1010610750304510300c14080c407803961010108201150008402070108017040003c0b1003000380500c03801c030000c1000080303604082054100c0b10b2000403001040b200c90348000742d900100503d1001d0100280307103000007803140e58600312120641c803020a01050060300d469413040c01104544103d14024400502034a040200101690001d00249110707a0f00960074841c80801c01e500c00207402d815140c000e00111030f951100781d402c803008101d0000a550208028502056189504009500501c080c1000390382c3c5184110200c03200e10b000510200e4103400800e80400c0c1a100c08501c1021140c0c18509451042441c88401e030003800365050154078007145100120345070100d580218010525502c01d140d0b5241d2403c104418440350300d40003007205003401d600300903540c084042d160f024081d1040300a4081e01d03c40080e00d0002180000344c00040320284044807100c0f0b68820703003004050341c203002020142c040c6c000c110100ca = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 350158750 1250 350157500 350157503
    0xf060403020a03050f39161a040e070903060509030a080f06040b04020c2503050c0d020d05010e07180c2f03070c05090a09031b03050d06031103010606020304050a09090c0504090b09010b030712 84
    0x402110b0001c5c04102d032305045502910141c42d0750700ea9428000e400a00c1d1208a0004039403291038a008910b00c83c034000207030b8800b85555968901d1682e140d4200058001300a000c560b0003d4031b034290107070156102d0010705804200100106400380a503003100603203280b00c003100404040b2024051000ca9008203011a1224055a90720301e1702d0201d2010076010064034402501d41d510b400d00c0c2c48101c02002c071301c3c4021910800844040d00c90000075030710454940392100c41c0420a4002c03000114400d90f052030080c107000c070703451031b1061000080003419a802050100e0f50303004481400d2089141001c440c1c0d803c03040040d020852540d00f80d0780a400c410100040b610b6001d503161959003058480c0b800c650041d05a980e041c484641d4901e0712040b050150110280310354240000814528030000a403400c942000341f141100c2d918209a0f1001040e0700c10094901c60305c1403102107541d07102c9004880080d88600d40844070b41c40c04090072804c40300448001c0b842901302404c00c0090b8007402c01c1d01503d06 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 350160000 1250 350158750 350158769
    0x1101030501032d020901090b0310020306061204021201020c0d0801060302180607240209090903030609010b1b03040e0105011b03020d030e070e16020f060403020a03050f3916 76
    0x540382c1c60300543e44095040d0001d40c0400500004148001c582d00b050b008090f050b02115008032050034140d0581c042141c1c01b6400c40c40c1402040e404c03030300c84241150000d00151080406400940440d130980c1d1000c2661811540021007891466910801070390040059180450811607020080102010030090182c4108404a460700c10b200c24965500000d85088299101d5481d030b00300d0640c040c0d00003444040c4101c2e4200001a84041c010044900c9a1001030a203d510b80c203100725010300c0d401803c040031596040a0f41c40d0700e0200e080004001800303c1e4030000b005989400300041c2a03240c0c40110004c500032140d0000700080d0009280360415400d814040f03444d0344c010200300d25011150303219405240080d402d000c0d8802c81d12100c002c04404986c02c0e6091070b00c04010f01d650b10a0191001001640603154400204c0d204001074144034080392140d51509059004140d600d00c3c20764906020240c00002c20090050f050001196801c054070141101051015641d86c00c0c03c0c1c68030540340791 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 350161250 1250 350160000 350160053
    0x1d0a030309021f120203070509040603030806010e0904021c031701080703110303122715071701030b010e1503010e0d02011b0801180b0901030b060f010c1119170a110103050103 77
    0x1064003450503a409089c028008019181d86c80c14000c1012070285c2e1400d01080e02c1d04450300345070804003034180c840c50300a0300ca48201d005455000a0040c0009401d03010021142c2c03000c500d46000c910003600034801c40000b003942500318182100c0070b20700305400600c26401006004803141540c0341036507000414000c00036021884030b901c141c0c0710480f4004c030502e0b400340782c9031102d0110024401e18000c00d03043e502c84442e084c4161003c503a00714207001c090906a5420700410410103000404c5601500d039910824660360844e010034256004062603001580002603808640c960900c82d1001c0301102c04005c00c048028907002a15030361040c06010400300c024000c030340c04496541c200310142c09010b090302c8400c3da5241041122124165951031103204400c503e180d0703030361048030b40c43c4071160020914004040c44070104480905080e01d00740101035501d00008a4034402c4081001101003040a000c0d10400d0b03142034140c8010032613565061528100c010b0001c982684000400299944c2d00601f1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 350162500 1250 350161250 350161261
    0x1b1c020904050f10050114030307050a08130905070804110405131e0813061205060604060c06060906080c1807021507030204120c14180a1d0a030309021f120203 70
    0x2c1c82880650101c607841101001c0390144d00e968001412140c8074010f5a01e1120000105a240c2c0f041d024081c0c46070340944a210085040f200080c086071212020702450b8640d160501d00a82e8021038003a030104a6590400040c0800507044002820086408000303c1c0380010148020262504024002c4510341c81c81d450003811310020b101c2c41d107400c05041e540710342d00112440401c9a41d401800006088150342c255515884c0c0a41030041000801c0c2d6410030f418400c0c110350082c8007000684000d80c07210030010b12080144100c1d4050122240a0517400d0610024080008040d07442d08480310794840030841490f0340810030002418003500a05c400ba102d001c03046000e4025904080c04d0001d201c1c440a04108004140104482c5150024103154003d1820418208540040042e24505040014030b020280d80c0c001480302420b400d001c1940d000b001d003054685180d82c030044020070b9841c2100340651801c1d1200180c02e800440c022030001c10200401090612041146500d954001c00804c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 350163750 1250 350162500 350162503
    0x302030601270e010b2134181104080303010b03040302030d062c06031e12040b0c01050108071d0601030905060702011e02040602150c090a03051b1c02090405 69
    0x402c8032800a01c100100056202e00800f203264a85208050b4016a10318003003400b1406184590721401030131003d25507600110f00c0d4254a005140b400d170000e000d0b03000d1001500400b60141c07000c0c3e1041030030b07551010049822101007454002603605e0a110401c00e0100c000112415504840e20068482c2c91b140b60580c41c0d4041c10000310f08440c208000032500e8544400103c260300500100608849243c248110390a0425100700342c15800c070a20000d2148495110f446000202e0030413074500030880102c418190b0000d070007048640c400054101020b100c2401098090215900600345443c604002d42ca6000f24090001e40341c4860b4100040e200d030b01990000400580100c00e8804620309498003c0c001d001030b076030100090805103502c1286441510a07201070320341d1034005000000c904c3c4800713160040300400010601c40c08200b80f204540324408048021031003030f0001d20580021000381075901b2038603001f540c0204548030049404a0000681c2c1001c41e40549003d903040c0c0341c0b810800d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 350165000 1250 350163750 350163809
    0xf020402040510030504060b010813020907110d08060a06090807030312181505091c030f0e011d060109091104090309081b090f060904150b0d14010b0a0302030601 71
    0x20741c0301d140490807001e0584c068105605c1540304200800002d980000195103180c4281e07076850b414114600d101006003005c0b03040c2c581003130503414080d28281e500d040080c0345c103800c4150000018105828080f06050a91621018020900b030900343c803400c142c601780e0380341d1480c8409001c120000010072582c11040c0c1c0502c8145c02c40c50070100d030015032400c25080c52071108095991082c41c18000406090020130f42142c080050b0004506101d11074004074050945000742034401e9954030303984400d40200340f190b06401c199504d0350504100040a0403400e02030140d20115140e400c1100c444001003008002011100341200d0000e8014903a09003202c00b40c805411400300c500c5101c00540c0030340089449006064021683c0703443c6680c0d40000c20440e090240c0d102e0b5040b800c141c02150000d2000544292108202840018a1401c03100020b00810f5071510503245c408680e05d0303020701d00c0028061104440015252401c6042c41c40d40803da45000c1449004c2451114050001d43c80c6900c0903031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 350166250 1250 350165000 350165009
    0x9060f070c0609030801030311010509190218130209010f0609060f0c0b191107020d110102120f0a09080c0d06021e04090f06080f0601061b080c010509011a0a030f02040204 75
    0x100100f04940c5806041c12a00780000d41c0407070311040e102c5d0741a4405009091080c1411009001480c241e40f05004d40c000704042c00300d9010190161151030f410034a02c031648a4520b41da40e40d83c0c14280741c0107000e00080103030030001c94084003034000d2100c0c50300515002c08607900742c03a0040908a40040c1110b940481c4a030052428001c0d00a000140041d0f01030300c0780d19000710008008180f80050000c00781d20902d08001c1d002980d501e55100807500c1c0d0320b240f9802c0362040c016902206801044089075901c042c21f0800425004076541400942c083c9980c000b50a84400410300b4800e03047c00240e13111800c80009000680010340f248084280c002c090b143d54108003a00341d1201d0b1035000b0300c0d01400002e40030328042890980c0c0000c03a134a00244109450386400301401c142d03400c001041f100489020341c8101c80310301070003040340040c501000501221486000019080c101048600e00750313007019040340c0910b1061024030070603a6800c10140d0480e0303800210101c12255030f00c040740180c0502d500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 350167500 1250 350166250 350166263
    0x406110c0105010503070803040f05120106030b09060712050408090d0303060902070c03061104031e050c0904080c010c1e080603010f0e1f05040b06090a0f0609200309060f070c 77
    0x84500d821501500954142c80045099450351601c0b040f1055480c0101d200e18802482c0d40042040726060034058400711741c00b031000129000b03450b40c03150b106030001522604c0719648001c00701b020141d48a84a0107210f0382140b01031050342460f8075111b07400c0c059420b07800d1040100c44111000c041c0203900074030050641840541d01c42120b410100b0040c1010f00c01071b83e00f9800c14840c02a148401c404403000c0d00e9000c0040c02c1480002100c40c5045441d80d0000c4130380e8410794420500f03650b20014031398401c0d4418881c11b942c0c0c04070b000c00b02d0300790740015110800788801a8280882c007030350106907881d82415031510940c16540d81d80080d000d0b00400d070700300301024030700141c12404010200b004610001e80c840142a08105641007004440e42268080c104040d00408100107161101c0e9170340d0408018000401d150201c59065021160540e00c401c6e10540c0d01c0c1c0c01440d202c26402c445139001c0300c00700180350452400007010354070348000820000c410707182400000c0c8140d00030105142100d41226 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 350168750 1250 350167500 350167507
    0xc102607020709050a0203070516030908060a061e05221508010203040512090f010e010e12060714030c0a0e0a0b07060f0e0a0309090b0f090c0403121106040b040611 72
    0x1000780d114101805030b508501d0030f200008505400c140212809130b079040d40c49902d44691100c1020304541441011030801051003000101d40c101042903d00500c0c1040c4001a018902076030100d001c58900e205104401c0d04080402065640200c1e0b007075850b9000118141002003d06104000c01c40320401c007035400302694000c1070505056000e0751240340705000310741400620486d000301078064600fa1325070080f00250340d2142075104c1e00343d18010850604043c60748000c4840054111000c4840e00702059000d101003207000c40d4000820400300450f100c610f461810004a80407451003001412000d0007040500507020791151020765004103800700480fa1592243e16094000e0b0820800300000329041482c114411080400d01d10f550070303450b40725a00d081d842e003241b100c0980341c21015541c0c0110302c030b040c1d4009030707c50740d2039a4802d4400161181d910342c19071414111100b40b42510804016518000e40704500000a044e0b8010f42c00c0858140c0e42d56452a110b0003800300628203462100010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 350170000 1250 350168750 350168761
    0x12051005041a1008040c1208040806071107060314060f1c12031b300609150905010e2802070f14120a030207060209040615030e0c1026 59
    0xe07000304100c42d4226042500c0081211084070100720960300a003880c03d01d040c0400001c8245074208a0300c3c2c0c0724022035410b1039034580c00181018021143c000200301a20740f48203c012043c071800c0c02400560404201c0c3e0300d0304086414a88400602250168403041300b900200c0d6610382c0810461036042880300909001407401d405008904846c03407001c20308041d0711070f541c282403801e11440300c040c41c0d0707942d080c80c0c49080d00b51b80043c04100321201d0801040d060400e031a5001d0150001802d41014040b88505080784e540940311519800880910702d03000050002540c290392054000c2400c2c89202c412000304011013080d440461000140d4510006182c0300708040c201c8851503450250038080301410388200040e444140c3d800407404a00c804203c0303505114000e0303011b0305070b0354000c040040c2842901c0000c1000c0383d2554200d00c0b10b10a0114407642036960601581410700c03a000c1c05081007805a10200343d10b12340400302807040c40f0599105070510980c0810a074030341e1a101c40d41d0030050611 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 350171250 1250 350170000 350170031
    0xb0703030e07320d030c021c0c09091416030308190213080d020a2102030705030d140c040e0705030606280311070b010303180902040e0a0605030d1205100504 69
    0x18030300c58050007048030f0403100403440c1c0b0012003040b09800d62524100b040095081111208581c80c401555070240340700c4802003040301c03810401030501d2a90000c0d6800742800c010b500c20a01d06007a910540c011155041511501034076070003101e5050800704020348a182e10799103940c0b01a801d6081c01d500c08103c120705111912030304400c0b500e81100b40d80c600121644200c0c3c4480990740050f14112440095a244680303140540d00d0318005441900d04206443d1340e4142107500011140c1082d68480254203089400d035021141c00c2045003800390300c1e003850b050901e06840d40080c0000c040c094040009502c070744038081250000c400400c0c124641d900140c9440b5041c44003071240340000792410351810321105000d0103d96805404c1880385c220baa285035800c071904040303629140481b200304200000c11034841d0000e04050000d40400515510307107003a001c01106c00701d50200c4d200307a12110814403c5904107900301d0024502c4100070540d9910b10040551941495100b00d070894503000f0a0007200e00c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 350172500 1250 350171250 350171309
    0x3040e04081206010201020901081603020c0604110102010506030307031d12100e1006050a05040207080c030310031703040b151908060f0a02070201080112060b0d0506040218010b0703030e07 83
    0x70199141c02e280d12010300482c01c0380036083e18107010454110115144240302041042d15508030315000d803600d4908149030b41011002d890071280d0080ea00c41e42011581c082c062540e004d0804d400550401e64140c80c010501400c1a00900455400004180c03075522110a04415034a21a00320303940b0319506015000206604001e00c503103402242c0002003541100d0003100308450f0010045c2d800c3e03c0c201410400251b001c5017080714030790802c10a45941c0c05090003d0341c416000719005884a600e1030078003101c0328a602c8043c1c0d0076107000300100400a02040b800355007050300a13402c40355001c0d2410209110302c0300000810b0404d48a807000040e40710300058421700c1000d089400400f141c60302001c02c42a030044400c001d010400e03075801400b803140155a00005d06004500114284002c0030204105000c460016103207a00040c1c1080150300b04072105a03030064107405409125031500c8000070060240390f1008003019150203a00e07103000070400c011000750461604848103504881e1410308440b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 350173750 1250 350172500 350172517
    0x30703060e0603070513061a03090d0f0f03181709040f020c0d051608180108092109060d0c02070f0b03040c03060506060c010e0303090f191403040e0408 67
    0x2818200003190054140c03054a02a0b08007030000c15407203081108004e0020031400e014030f55150f85401c00a03503180c0d03450f40802c0d50b03e403110105a6a04200449034141803107131041e0014404140e00c6400342c191302040030a5460300324038001500c5140d00c280700e42515100e12001c0c005101c0c8160700300c81c0d1401d99000b0a001b0304100d804201d40411800d0540903805404401601c3d07412040c102c000300c038001e0004203050342203281100c00d651001c1d074501041d50080d404403003908460641c40ca12a503006800c2c035411800102c018502c2a00b00c0c104a000915550840c1c003c01501065002c510345518040d9404c034494200203000c00c002503103000b503488049108403642560b4022000815034410811207000e241c22400c03203602c541c255120b06003e0500681200d030481340420104460344020303c5155800b81e1650051552410004900c80c079008a01486442d16001504d2520303240da03480e00d07004500780c0c1c4407150800d0003001d1402e40c0d045014545c840300300030802e001003200700503640d4010031104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 350175000 1250 350173750 350173757
    0xc040c020f0c0a0f031106070c06050414121024030b070e010512010902030612010203041a180a06050403050405150c10020903030901111f02030108010501060309051207020409080a050307 82
    0x1030b403280c04001c03058180348141d000c0003282e45000c0c0301003000703005a41c0c000303007010b440e0700d00c0c0c0241960384529240c0c8991010300069000b103014007006280b14141d00c2041d00880300c1c4000c1791408000c154460f10143c0031191440c0d80c0d40841005103018911103003040e02e1250080d44001ea40c4e040001c241ca60403580c19000078031011042400c5d42c020802d50700600503001d4a81001e82c208400d5000070740c00901610351000d200c042e01005d51000340005c504c203a10400318040c50400079407107882030400c06010000035030719056520520705d80c0081c480b00000e8102e0300103c0c040d2105d003020b581d64030890700002d810043e60748170f40d580c12491100514660030340c84200e810707504c01101e0302c500b01e014014034107034507410800c85c10101f58464451039104a03d101306a80c81040003940b5803200c05205015040001e8000c001001004000e200b074070f0041c0140d007030502016a6690722035458548510480c4100d04c000b1651505540301c0d0f500403000640c1c0100c00a83d5001d100c540506160411900c00000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 350176250 1250 350175000 350175013
    0x2100e0d08100528050d0b07080402010e1f18080a03120216030f020c19050d021f0c060e061006081b030a1a1f03110f04170f0d0c060903020c040c020f 66
    0x513814070803490051075800100c247c0058440c02000c440008001d001030381005407484c0c100000740c0c2d8042d18000c148a20701e015070841e098110000d440b041c11100c09107a04c04040c0c13130402c14100003080d0401010780c140340c240454007000e980301000780189800d0421006135010320104064002848154030010340c1c08580e003400c5207500b08003192610908031090390f0384500080042d802d00314070000c201403004081e0940b0700010203000600e200310014860001c0c845400f04418041140b00b90b8500c0c0306800040c05051a00903a403034448403041c03142c8410400c0c00340001d8004140120b1083d4500781c2c1d110304503038070f0034140240e90103000c02c6100130703042102400c0c1c1000b0520b4070030700d90f20355000e41c40f030900a95481c03103a041c3d005180c04c07030802c6010402003005d040c189214000078000f4044c80b11252640c0c104500701907242c41c0b00c0c2c220503502544030445140300700d900441c030340000302c1c0e10a0300828503100a14049003004052184103810a080483e031400321070300850300b140b2000b00d00c022140e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 350177500 1250 350176250 350176259
    0x105061302070c03110111010c202410080f01022503230408060903070b011d130f0813030212031804090203010e0708030a02100e0d08100528 62
    0x124460902d0061000d4001d0000700001204c0d00c400394112201414a94189412142100d0035100280780d00c0000402c3d09400100e400d1f21102e8110302e1410500c02000f040b840c10948458820411680351200540b800000b00c2d050508000100500304001c10b90300d00658807008179002c3d400c80a420070302c0402070328901d41d80d10b04029000d181c1c5a051365510f041349691005400d01056545500028484104401b09a04204101050044c100c442c0119591003203070414118001040c1c201902d00c9034008076100d9007901000345107400010780c50b000508045103290440307142031a114001d250302c00c00f1400b000304400078031000c1e044900035a42804c5010620210b5504c038880c01099188062081047d8440b604140d0301078030b14144040d0001400d54004922603203403490f158855151503200180491344030f641409813200400104100b408030111035501603482d040c0100c013900400140070001b03201e510300300321460700414010f040c0c440c14403141e4450510803ca058400000c1c0f0001090018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 350178750 1250 350177500 350177539
    0xe060d0c0f361d01020a080906060a122a08010c030b06040602100f090606030506090f010b010507080a0324061d0d0b0901060918110108012312010e010506 68
    0x81d001d00462100c412101c2c042014002000380005101584080c0c0c02c0b582c100103000d1000b05045026030f211000280b4051010038945400101482d0241482c50030070004005402d40041103540d205070050304100b0100c05100031f05210240c081c0612048203800644828194406507400216a40c1030000000c0fa400340040344c840c5104030401070b80580c40c40c03041030301180d20641c50240481004501ea40c0b00d40c03900000c3d58007540058505030000418800103130000c000403040c01207100000c2c0442002400040c00c0e170b00544c4005403065074001002d501d440d00c2075002e50000c01c0c0101100c5021603030340c101c5401c0c81001e8004c00011484614a41c04d00e00417101c0c1d80010f505004240a0920b19950348441d0461009045100700b9034a418001c160a00c143c0141e04440c80d085896010101c01818408100c0b5210074409052058400050140181c0a00e4000c5100294442c6001c041041d602258840461140008142d46000c28250a0100c19001240181390885a060380c0740c141c6031054 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 350179856 1106 350178750 350178809
    0x501061806061b02090f090309090103051606030b0a0603150e0421030506030a021c081902060603070602100504080d1e1d070e060d0c0f 60
    0x5000b40c6911040b80340f5070036061120b4440e8111a5000718a0251020700350350015104907000400e0b4010420840e480620b006c3c007039070030355a964104035864000c0881c418030101102c0d400028003038860300500c40d038400000d001c4100d0500e040e405800804800042170040c2107403200001c1c81801300807a0500c114001c0f101d1107944440c0c40008003000c0d03c0d8480e0300081c075107044140203039506c00003580826030f5410340303071041030610b21154603500040542c0001c00e0340c84002040d04046003041450a46098560215031098590400b050b44400140c02004016032202070000401c0006800003500207005005452078078079880007200954031503001c20420785204080552143c116071290341804010b405410b0580b40c4400f444646030a0184940308400881c0008202c503640e8084411000d55405684010364603941e82d04000c41d100b0510038812603070f4002040b0a114003141e13216 = true := by decide +kernel

theorem cover : BRFrame.Cov 350000000 350179856 := by
  have h0 := BRFrame.cov_init 350000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 350000000 ≤ n) (h2 : n < 350179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
