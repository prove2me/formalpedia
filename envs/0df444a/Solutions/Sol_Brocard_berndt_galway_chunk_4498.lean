-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4498
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:49:12.703243+00:00
-- url     : https://prove2.me/submissions/08958513-f119-4658-ae8b-3cd3d6091a07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 808812949 ≤ n < 808992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 808814199 1250 808812949 808812967
    0xc020c1003090b091f060b03010909110a0603061d0105090f040c0e070903060606020607170903090d14010c02030c150c040b07030201060807051c120e120606011d0108072003 76
    0x10a00808034402d8000c07140c9420044c17444201140c91a018111218200784018007031600f0680c480234110b442000c800e145c1e19201070019440390000d501c090002a29100184000940323104080d41d507404004480c04194107240019501c0380700201440304992441000400f440499040e880080900c0401c500c040d0030200030041441c030080c00261480c904113480000d0903803000582a200e903c959840c0961480480e0f41c1854050000e8031483d11031100780312280440d503900341c03502c1e04035108500c02080d5130030407025203003907603242142902550070500840c0d000c201c3c00305e0840d40c1da0964252000c015514003c08603450b0195800c03104195001003a900100354055200405941041c0300301c480a555540400910100e010301c01c1300100d60076146400003c001c00404241d10347c1354203018051140c4480800c0c0c00c400e060010720f200781d1060050202550f0004901d00c6040802c40f00c1c100d45030001400070b403079480050001000c000c00800c6d50a04101403030700e0040b42c42914000c0c1ca60390fa0b884 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 808815449 1250 808814199 808814203
    0x40b1005271e100c020619030b03010204140420070602070213022217071a0408010e030a030506090c0a0c0f05030c01090201080f070905010c050c10030c0809010c020c1003090b09 78
    0xd0002e0b900600128200e070000318090704c252242c607903000b0400b510304800261004094076020002034145a16441d035002c855a0078000342002d00320035400c40007403600720350420041d078444090810304020030b103018010062203071085a0a95400013009a070300c19892001c05d4002c203180d041504601e10204a01101061401d400c038007203c4041e046450654980011000b00300c2002c854440d2a44141010894200984c0a00c0c000f07104030740005003840d46e035845003429543c4010406119400c00200340303108981502c201d9801000030b481c5554185040948000640300d00750101c410701941010200412626600c03140c09990322801740c039101c00070b03040400c2c042c068a96049001c50b003401e00207502c01c1c21880718a44111700302d541381c841403403030000103542240008001361407600591460b08440c0d114107803426203010403a540001c0d40790a00100406100c006007042116074103000705120032a60009480c10002000c95010101c000d0f260030036402004c000c1402001c0351200b4003003111113080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 808816699 1250 808815449 808815499
    0xa0e060f0f1201031118060f1203070b010f1a07081c090b0702010f0e03121f0b030f0601020a03080a11271c0f0f080c1b040b100527 58
    0x70a050704201c90700900204455203005240103090803c41c0b45c0000c0790b07448c0c0107880000c0040f015140f06145441c000503203040d944646030507607415030841c004010841213140c0a400a1144031a080368008072200340351124411600e020b440040c02040c103181520f44140005201e100900d803c000045d02da2909078231020044801e0005940303850071a000ba030005000b104080300610001e5490403501c51400d42e152034000c0e100210801c5c40c0d080303101e032404410f540c3c03070007426041c0f0b5074646a1511480b019060240200344c80d0442d040a041140003a0300200d030790707400082581c0301003211032003420041c5d070320b001e8080b098001c100f010035425500c1c4005069807500c1c1c24141d41e204400407040c020303008440d1840c50001c0c540c0407030301d094501003050303188040c150358031507100103140648007254a0714020303011402c0042c01c010159110701c1c038035042c4292050000c00386c40d0901100b4102d44082c000e4095100f100318031045500b140b04240c4411000301c80903031740080c44403840d000341c0742d02d451030414 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 808817949 1250 808816699 808816703
    0x1603140d060312090b0712170702060a150b070b19241703180415030605060307171e070306180b090c0d12090f08030c060c0a0e060f0f120103 62
    0x114030f001c03014900d489040760500391004907002034501111943d440842d218051071801c10440c0742c0c28200c6100190503400b50040859500404050904400b100100d400502c00000d040c4000041007000c04005c2043c0c0c1d40380c60308122203042560302c4452182a020b41c0425000c0900d1428043da40100c030f904a0710746054a00040c807078010b41e11500492803001c40602040c07541e5200b07000c210b1034a1410341c0c0e103205980c8068004200e07d100c01281c500307100d5007a0001c45202da211340400c03066040800c000310040c2400d48441d00b1100820820640310203010ba02034601e16440e0040c6800302004014034401558811001c1081503c0e9048403044030308002003c81d880c4d03503a000810710034440011700408000b0b0003042d0b00c0385009a82d80c0c4040c1e60250f400c000c1c050185800300041c84070141d42c052402040d00c64003a40e0b0780c4282110706400c16070000c01c0550032290500a646900c0d501204249544c071382610900d54031002d0640d46100b5008040c500c0001c1200000c027491407161903189541224 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 808819199 1250 808817949 808817963
    0x130b030c0c0601090b0d080706020f030406140a15120c050d060e2509020702130903050307110601030c05060c070905070504050414130204110c151509010b1603140d0603 74
    0x41d8864010300d0035a8240030380c0e9a80002624074800219110200908023548500c40040c988216100303004040d0704100d07016030b4865524849008040485050341d640701d074840b02d00f0031245064503400341c085902802203100724602c80060000300311061603448043c04009007a8007030b080b00c518001019251a040001c42d03170240740c042001200343c004c1c2c0d035070444042103905040c141c20000904000d401000702030703a003d41a0154a08a4642e520484000d240266141c42c1e0720702d00b95501070000c1c4908200612541d00150041010681955044c42031340e204444c502d03640c4010740c40d00d0345010381d00d42100082c01e10700010300c1680c58220009001b2141d0a440602ca850440d44001d1a40c0700304980003002d090746001d080d001803502d40e0220b07103218841141c0505040c40c41410760310b445180c00030207240303598603800d0000803107a04840b128a0081180e5010217503040c8490380895005107409180e01681d034000400805003e10748820702041d0b41a5059101c41c0c0700b20219019080c9848191584 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 808820449 1250 808819199 808819201
    0x140c1f050a11040f300506010503012324060406020d0e0a1d060a092c07050604031b050405040b0a0f020c0a0201180f061701050102190602130b030c0c06 67
    0x1c02e82010340703003212016001031103c5494440707840390b04840b05845030091204516040007289010b400000d402c0c1c050720050059604260506086400707a42c202c80c41c0c01d00811410f22030440d003045440d07001280c0030004100d455043c84410032480b49100326540400c1c0803d002c42c1035680010050007801650f03841c100342c000404107100540c0041d02401c1c0e07031140350520396244007042d1400240c1000014060b10b00c1950395404007004c4529684a101d5440101c8000308190540c621110080381010f001501a162421000034230f140704a20005140da019843ca1516020041080000504003d00b081c0102e20f00351402d8101200100c84240b18030746441c5d03104519010b103100396500505104024010b001c266001900c4002d000c03109090201d40a1078041000c51f08034040d200100b181c1d80703598641c1e6251031030304440c2c33440582000f4111352041d0045006080035017000c981c584c1d000f100c0141c0d140d01d841d0740c042c800111500488400000001032107400c0c44140004d000d43c2caa040261806 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 808821699 1250 808820449 808820471
    0xe150601080f040f051c09180c0519090b0304030503181b1c0501020d0e0d03020a0212090609030624010e091b0c070f06140a140c1f050a 60
    0x244820b680e42e0070000c015a0001d03000810354142282518050821a0301c840041c400c01c210740003c0d507841c6800112060b60401100140d103034054010184a54280280040b03a04018100d0054004605149201d401d458503040d018403d0003014000c41c15031a0f580317140070705014200f0781c41034482c2c6103400c0380500c002000480102d1127050086254180008c0c070a1940e040020284100800441070252403112000088091009108052235020081220042038410906003d10031003c10705060040001008040d404104551802c40380f04159031540c50803008030721f260240c0003455802d44580e4080c882161049081c8400b05400705110500d002c5040c001125884404450740d5085050000490300107a03940801158000581580f0360620440991151030105603900c03071101e80ca55100d007405615444030442800a020885170ba1800040001c002c10350b03400f48498070910440410110a000b90500800d0401d1151048160794211042e6215000b480152015131619207820a0858 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 808822949 1250 808821699 808821707
    0x7020907030b030d030b0301140406050417040b0307050d0605040e011e06060c0b1e070507020901060807052710080105120a0206161a04240b060702130b040e150601 72
    0x201a10015000d0854013004403010380142003040030056065483d807011242d01203100583c0340c8500c2c0909004141414035080001702520885501c001c2e0b4031041105001d0501d089045a4111b502d03850b1140d5503030003d0241c0402405540c000c1ca5000381000781080c1d0403141500070b07503031040702501500b41024207115007008079422446004081220f54000d100441c08260801d5480003405606007032111002400d070078501c2084444a000c0b80d8041a440c1c25030404410450241c03810303040407030441c1080040a080340c0644061080c42d0000300c0116504211180601d02c0c0080000d1b000038580019408003401c4180c00340900c5015010072540d641039842e0004070152919000f400140c40d040004506407000c24280c01c040e95851017503501c1032500280c14443c107229078061a83c8115156006110140c400c204404801005041503a450440e98800c02102d03000740d411140c69040300410550400075140d250301c0640d0103454450085209100803c4a00302104040c0c200540c655031800191 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 808824199 1250 808822949 808822961
    0xc030a0b01021b3d0e0f0d080d150f0303120209010818030f04120614090706051c0606020c03190312090602090409081902030c1c0c0c03080702090703 66
    0xc108200c10450410302030410b140b0740c0900c1c002540100740d13003624074a452203542c4041013605922189410f40c6142d450f612500526030600100c0d24004906030704000152058002e0f6009890001e000400b6811000c050740502c40b142483c0440705c81e03a17030b50348078102c0c0306810a102c250007082608a14107030303400c8648221020007005031a041515194044103d5001491105814085c4002c000504413400c03141e01910042c5540500c5810540c02031800c10155101031802c01d425015160600050040100d512001da034168500151982410a0040340307056000d03c05c02100c034507040d00402c400f5408038000602e81d8080c2c0445042c5600700c41d1b01c40d00d022030400040c00086000820202100311070b001600064001c0c4400b504040da018006000c580f9001c0040b10045400105615030605101d55048040000c0c00039600305a856a61903455410f004100c0c00013028132400b20038041c0c0200074000000e030b0002c104c0a070540d01c924000007142e00039041a0f00c2030540000151a052180c0502 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 808825449 1250 808824199 808824223
    0x1c020d03232a0307080c060a0b060c0c04112107020f030c0a021509090f040c29030618280507170403021f06090b060306010912030c08030c030a0b0102 66
    0x74203084202c81c11128600c0c11914034810860000f00060400720741c200b0082c1c4902c80b0010f020b4110f505284500300100d802c40403649000b00c009001580000d44007280404c90b5060644020800c1c9c5882e542c020b00901c12482c4500030a00842c0e0a40c4041c0d0003c1d0351603104650540071507d00c8041070f012181c2d01e002d42801e510056000c00303540001414a000c81e5402c6007039068642e81090140000078a0319002100c0220103d90064200000e01c00340386201001055070020000100070700601d040c5c4916070318152140484030000c086556a100d403d0440340012204460b040541000d41030696200f03090348445014040304500041005c05500c00c0c0740c0a0a01c2d40c44a281c865070b50102203074081d400030010740540c05050318609519238002c40620360300482001c00241c01e8240f0384d04008450000c0405402910107000300401e80c1d801504184c19103045403040c0742d2480c600e02d41110001034181c0f0081c1480c07000300034460035a1604c006140102c00741e040602060b107120004907030b104502615 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 808826699 1250 808825449 808825477
    0x100204150e0102100606080405150705042d08030d050a060f0324060f0e090105040c030807060603050d11010b01020c220e01020a021c0314061c020d0323 67
    0x90000d500624044015039030600654080c80b0a9541020407101c0c00d5110700c1c0800e11307035410403003009018842001c00103248030f0740c7d01071410700f1013000301940144e00403402c1300e03100031032011901d82c0140c2e20a01584111008134074442d4075400300035101d800c0050481d01d51410200810500807441c001c0d00103890030070010700c000600d540c42c0c1110070074440d66049986280c40e034010342071404502845d406402d640c0200c07081a4030744801454411402404256a645001e00b408000b0b05180300c000100c03900040391030344a01c3c8906051000304100d61004250b0f10840d4035400c00740e500f040d50070860341407004c002c04c02d03007007440010b82c0c0f07410800d0002030f80080b48242600a5500601d10800c14680c0405d0004884588140641c22130b0300c00340039080582d0088001d4000c40b03003066040000701c20b02e840c2c00c0c0041d08600801c2140800b010b4a220300c00c9643c4803500c03407004029100c40b0001500140400034030303203d5050181409001440e03a0740719081c0c68001030304410240040760b440c03001500c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 808827949 1250 808826699 808826729
    0x1c1104020304141b031e070311010207081f0506030a030c12030b060309030c0f034306050405060106030c17070c0c080c010f030614010e06090d14100204 67
    0x10400258002442241d883d4450141c09400e54400c00210040c4440c4c0100510740400e440105494401c0300400e80c42804954122180d442c2d0001c81c0e44011a9030003405d02d0404040240180d04129550300842244e100c0e0410160f610403110300030840110702e80608020544464040c1501e900d5944c1014012030500401d0f840080d03640d074011601402c003890b0004591708006c002030300c40d9005490401d482c1d840860210140c0c03070144460110041b80300000c601d03141031000440f40641070810510044920240c0e40c1c5c042c0302c003041011401840c1269540c01ca500d65240483c000c00060710b09480318412000080380c072031b0080c031403d42ca030121034455001500d40080081810040284400c0402203843c0640000403140d10301031000e040160302800d101d00c02400014110503c00192004040c20060100581030a04101000043c400c3c42c040d00c01c480300c9070115000d4400c0f0380f40350f40c0241070b610140381032010b500000300444080c04140e4400f24407083d9074000340c4c041c9006000c8152041c0d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 808829199 1250 808827949 808827983
    0x1b0a0b04031109180d0c060513051905070b0705010f051b041404020f0c070314070b030f0a0902060a090504050604021213050a08031305060a05072f1006051c 69
    0x43c41e5036500c0480c0070300016072030105049003810000944019030118a400e070030802080490f0042d10b40c090556495502526140d4072116551044803400090000604100c3c10501000b405490043c25540c04078556035595481c0160081080d035036444101898000880c516100a0032000955040303012003504203400e10350000303a010031b880d11003544070f6400c101d0071005883c810f014144503204107028100d400d10390300740b504c4200e24040404201d60400351003401902415010b498010840c43d010811035079800342e450004040040000e5480341f00032800c0100d0b5644a080c01090314015a418041d80d1240b4041c00103a000e400c15441e5a2114000080c2144980d034000f00482c03800b400854510420584071045540d0041d203400d0003680c02c0c29004820b02c0000c100c03142e00400306540c10401c034900410000c0840300c82c1c0d6401c0241d98801e81e00d2210281c0d40c0c11881890080003015152101011a0203400038900b0340b017030a01591516000a05021180c4031950800d5041161503034603213405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 808830449 1250 808829199 808829209
    0x1c061401081c0801090e0102070b01090605130219030b03011d010501061d13021e03010f03060b190e06030a0c08030a020d090b032d040b070206090a0309030f02010c051b0a0b040311 79
    0x40500090b5923609106078030201c0c1e046c9a40310300070b250459000070034505100030710040c0842001c000c0281c038010840b0f007074901508500c220300008a450001102584d810001c1d026045116a600c0c001d51159980c5507680410350050b03040301c45648522861028800c00019122160298140d02c140300b02d11980812119400801c02d80340703828040f18850070b461050840540003a0024200010a86000d00400c90588103030000404112000e0f646115100042c408550107802040d41d00c00060f004a00141c0f0204016192030343c1c80740715001c02617114030055a5903080703440e2040051050009005181e4010101c4a0686d190124001d1859440b412513003008501d6200c13101031440c41000403c280c000100425004510078551541141002c0c0300007450100003410309901c9400020220002079001a19081200c0e80805185000c0314140010303900c41000c0c6030040d04502404600d1071500e401d412100c10002c008490561202e51100d0040311a070040d400014000c03074a500542d000d51070301c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 808831699 1250 808830449 808830461
    0x60f051e1305190f020a050603060f1002070810020304020901060c0305120712020a080603012a03110708040e1b040b0a08100515070606080a0c051c061401081c080109 73
    0x507804035400f10301940d40c014100340e0b07054000c1c1c818180e1120450114a0300d000741c1001440d041380d0050460074072100007606511a0300380d2900c00c0703100c5100c0001107402800803400828800c001e4828202040410001039032007224203d125280c4080089140340c0a40c58642007940c0541d1104d0078080030400440f10a00060400003c0c84070b00114140c14038844c0c0000c011000d0207503a44d004c0c07810324405240c296101000c55070398000417003001c20080066100302540e0480c41c0d140118031000c0910000700c1600c13070300e000504001400600442c07d03169001d40c0c98040c0e141c0c0c003004e881500034040784000ea0300440c0501180110200002c0c8440ea225620f0560803804400e0802c85440e5505e00003800c01a00a0340c05013a80c0c00826a01c00b4001c1c1c2c0d120f030500401c0030b107024101c01c41c85075641102c1c43e100c1b402101e1041c41c0c14241c2d14248609181c11000090f4010b108000d0407110600559100390309103d80719162107840d2040c20400c0090f203010320400c55544030940b0990074a404072015000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 808832949 1250 808831699 808831703
    0xa0b0703090c060906020118050c040207030309020d0503032401050d0b120609071a040f120f0503030f010e07030902091503010e011b090e010819060e0307060f051e13 73
    0x788503580321002c1114600300a008200b907807680011203140800181c00d46050698401240b226020a1400f08401264552405c003088a0059441c00c00d8034040e07006000d200c0000c1c2d00003a400001d2410800008021800f40081d0320180200300e01d48013074200d504840303071070302800250180703d083d06030007482d002045a1240284107001061428030300510740101115920465030200c0010441a40e003000a8200344601c114140d20341411300c0404010a1420b200303000da0030700c23003a00c0702040c042c1c01071003001da095100007505d69a082140c4500c032035000c20b0140c24090381000300403410080c000e01c118410164042d002d09402d5488030540024106407070742d0310b5015500c0c0e03240f148421000b84200003445000c02e88603295017080c0c00c0014a81a00c0d508164411461000103210504001944203000d40d881004131901c2c81844c80e008028145000c100c40d01440040303451402c10905410000d03e1109030107007081703242d4039000c032031a0107040c2c4040c1064002c98000071480e01302629528881c014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 808834199 1250 808832949 808832951
    0x3030703050405090424050a05130c0308180a060c020a06030207050604120201020d0608010504050d02070e0a090f140c0f060f070b04020a0e011e0803031b0c100c210504050a0b0703 79
    0x58a00419040480c2194000d24174203a50341c0810502303156034450300d504408240ca48000f00803496841d134080303a01b0b602001d803504c0b50102c0c42c1d041a2082030a00e0107800009008407400a0360b4650181070400d00c7d20341284940300d0080c02250b014824400daa00a6803c0801010706803034688403032f440500036055100c21550204110881040346000b43c00040c10b1100000450746064100103052601c1d281000b41150000b1008000d03600351410110707000703c4212000644c1046614218030200c8050200800305642d445401c8103403030000c50f01c0686140240e590303007240c9070103030100040c1d4460920403061000c014029030001c501000704440e4014405020043e030640c40302c0c074055206c40c01340c1c4402d8641074a0882038521509008000004000c040020360550a00f1010303595401d80500256664031004200c040e02c104080001071045003842d0307020446101c0551000300a640e1403908202000f500001508480210b441128404c507085800b0f0502504140d5400000c05400f4081c50101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 808835449 1250 808834199 808834223
    0x81801150308071106030c07060605040510030326011d070c080d0c090504050a02042111060307021006170d02070e0a02090d120203070b0f06010c0314040b0f04080606030307030504050904 82
    0x10345c86030f00082d40541420303614903485101c0c9180c6502603d446410450180e8244402d10907083c150101c04401e5981c5030404030410380b00000c1e09040d041c2c03039800340c1000002c00c5e000064540c240c81000c1008203840c10803241160303140401540d200510540007010154100060105d10b01d25134003281600080e850120201c0713071760b9000075090302e40a60b8400341e80c50b800141005802152003d000c064044030942800512040d1103651103140d4032100c903030243d0320000022f000c0d54401c0c89800035840603810200040f9403100200000007030031503020121071183d010310003004350000800004441002c800c1f40303040d03550300c081500a5004000c0407900041002c4c21003000620440c85014155400d0340299100c2505040c6103042041c05004080492185000d00c101c0e80d0307015004171000354050a0a140101e6161028041441981d1114407425808034142c000180e41100900841d410ba03c2154030b29200c6108040e201e1081800040100707500308400c00150616806d203aa0080c0603509036100703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 808836699 1250 808835449 808835483
    0x30616090902040b031501081e04060b1801210c0902070819021b0411090f011b080d0501140109061103120f04060c03020921120a08180115030807 64
    0xa982040d0803213401410b0200800030041d070b031101d011440c01d100741303041619402d264807800b24400980300c80d2004460620b00240901c2015000003401d2500500b10180c15519040082c02c0d110080c01285282e45104880c8000300c4070740071020501a2b048814611000d1429281d00002e600440046445a1050000781402c3d034400c500e1181d1034402d90081e054410201c5050521720b02000b041c103108901e450711500380c1d4944001a01da6202050754a810b049a0b8200141c5c3c603501c2c0d0729005040f002400504100704000103000d4842016a04d00c14800ca9803541191003483d00001b00441c006500312508001030340c0301d0102c8040c06000301041d0313442c1c920650b00003000940e040b03540e0141444584140700800c1020320030050940c400d8a801c40c140710001c40040c0200e100101c408a0a41206000e02d40c0c4580500051f0082d01c402030702290303a0207500784050a03480044940c44811a05250503004260060040c25010403501a8540c0c0050840c0d8950140e900540c0c010350302080040c0041031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 808837949 1250 808836699 808836701
    0x1e0f27060206070f051e03040c05090a0902091302150f04090203010906031e081b032a061308070b150406090b0f0118050919020f0307030c0507020306160909 69
    0x34140c950702410403442c1c006805440c0e80d820492030000c20074100080c030011404c0c483ca1035036080f45280d820750750351903504041201c02d025801540c3d010030001c0c14002d040c415a40200307401031080e140d03c44190f4690000351496400c822010b90040a04000345008010010043c458070740300d41005420a5220032a4000300e82003600440039050303480d6410b10a001e15042c1d807480380c40411480b40f800040541d00c00005028440680541c5184208030303103480c50050040e00c00307200c211141c0790101540b4111250000d00c441140b070303a4a0158002090000304801600381d078250b00a0100c42c6052420350b10492a084c0c01460040840441d003803040b11680d40e402420300a004505022489003807560400800301c0c100e00c002411700207406510303095460886a80d40456504554404071561101001d10f54083d400701c182c203445100142c40e800020484002e58000d8005075403c00c04000218000d81e05407080c0d40019506a20a00c00140f10784030b05580d40300803030b0291910b00c40482d036841c0c604c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 808839199 1250 808837949 808838027
    0x1030201140c190c1211040506030109051207060b060a23070f050d08160c020d0311070617060d020319051903030608060c04050a03060b030307020d0b04031e0f 70
    0x10040701034818501340302106061401030818803148181c07030000c55840081a003440e120160085440380f0004005035029409204a00d8012041da020b092029803c50310b42d80c08110300721a03842ca080c0002c1c00908003c400d80712070f0304071500c0300d100406034040c440404016858003807041c80000c00c480c00000b4014658540300c14480e0009001c803000400029200800c010100300036901c2070a0308100041c1c0c00500d5185854065400700c0c0b170780d4120b007002c1381e6030301da02c5070100d150b03110b1101c00060156210003001c29030148040c61518588030001004262a101000039505610800d80c0e8402081d420044a210603c1981103501d801c0ca504081d610a80140c64150b0109503284010003003a5418082d807036100310203116840c07500f8140302c001054000d450101a001ca036584251040d41c0d03c04000300c44255800401c0b1192165503842c2031541e840d0210b07801c400280c150315907500f40c2c001c42c0030078100002c074a032901710980020307010032074141040307061301e1500c1c181c0218540c060700c1001c40c5032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 808840449 1250 808839199 808839223
    0x204020c01141f060809070f17010608010207020a030219180c030e01060609120311071202121f18171b0f03030c09121501090606031401030201140c 65
    0xc900500e0582242c560000020510414280803500042c0000e951078402c10aa4029007415072841e110058518500f00311034114034015004040007040c0544203920302c60f5480c00700002480001c1d252110740d802d07800341100094005c031011405000510f401840a1030003500c0384404040103a1300c1c501c0a0148500e8645140707003c0d42d496800e00125414092200e000b4800b000a2000c1841d03c44002c07d4201e00c0d01c030b0701c1000420000003c0c01c05115a0900001d04591070403141d980e6100d031005464605c02c1c400803403054070401c80a0401c8c11002c100c6603001c000055586404520208440f005072802641280900082460385400512481c03080c075852443c1689007900c4240500c03030713404a011024401783e681d5100302c103250003680c030000c1183d5008108880c144c0c0c41e01c48810108034440300d03001407000ca5000e914914655140d640c020300e4126403002c0b109006482e520b40d42071702200c0520b02c6410181a0715801400954000c5d0103015106820300d0541e490802403002c1c01e81040001101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 808841699 1250 808840449 808840451
    0x601060f030f150518060d0206070f0c03030207050a06030e0c2b0c140d121803140a0b0a06060c0602130f03081315020a02090c0f0a0801051302040807060c020d0204020c01 75
    0xa1005043c60005c254082c0d42422040c0094103000d4000743c0c2c0060070180091003440300040107001c008020700148015a0711007840821703240c403868041c0d10349109000780b83c0a04c040c24000159103100c1d024401000b816a4050801000234006115282c62200e44250041900001d0000101d01c0441c0000031079024054240340507007000480014121240c081d144101400c240030b002080b40e00040e40c10b0a205418100281030700c04201c1c1c0d103482001d0740043c0cd20980160100c041c0c84010645035812842544501c03000d90324603c0c8441102d501c1d003d003d001590249610001a00c0e50b802414035110b94407041c0003090769103261143c07007ca507030402c85002c130703001c90442c62a801802c000c10140100d4100e00902440d4417000941d035003000140648079955000210700e11002003c204c0e81194800c1c000182d85600c103540142203260284210f5000768000b03e00107070400864400c1d03809403005500681100d500d0301108545603c0010b00583c1d00145200b450001607036280f000701891058400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 808842949 1250 808841699 808841741
    0x311030d061a09010503010e0901060306050705070203161206021c02030403090e06010806220605030d020a02030f060601080417130f0303031401081207050102162604080601060f030f 80
    0x200500400a0b5007480a4400203002d0408181e0b00f040c16281513440100a2000035503449010901428040c0d001804040c43e00082c048440d80c03000080905a000b170b03045411681007020780b404212468170541c00140c4100b2302d0300000410070307002480141e840c0d2651000303912500c00c26a089038015a8228041001503800300450b0540d42142c6a0045007401d10030418541000880c40e0340313042001070306408225a1500106d8086980403030050540901228005a080c40d0040d540344952002680703c2d02c906800840c2c03004000402a101da841a501c1c21200d0300d47e9030340c036403111240c0400b2503840706081c400510007129102c68080101201c0c0e408000f02071035410042d085511841180d400c4400200041c440100c0001c2e40c1c00e420466010034580d40e80c1e1605046009010b440140d128004801c808242400140a07500c0000300000002a4070313541c0d80e144000243c425449034250a4109100421106018004002c42c0f03e415082c04a510002200710314101c1f610000c035031f6903a83d2050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 808844199 1250 808842949 808842959
    0xd0908120f24030601030f02121509010e010e0a030509010c12030221060d20060f13081501060c2316080d0c02063a05100608130311030d06 61
    0x2141c0c40244041036025200c42442c180402d0f1900d00500000d42160960100c0300215150b51030384105c00343d0307108c0c1685d840716050442c85e08940016075600b9481d42c2095150a04000b06104030a0300035030120091030540c560b650241d800d504041201c40c140f1802d1164007010a0500c140511000b64a54005995074848040101d142c040a5070030400c010040041080c0703a121618804219030f089440c503c80f0400c6650031100a6140c100055003103031012a040062140c002c0140c03418460102c001c204d03950303c840c0700540d10090022084990404140100115801007014140f0703c1e000b00d42c11070261020641c03202600e05800b0000d02140d00451051000f110b0380408140030304002409407000c0710b00d02800910310603400d00c02074415140003420807104c081501104180c0c400402c2c9446100c0100311540d8548a42c000d2480102820180041c1804010000b1003080e50803039200d49400c0c2d110074403103000c500e00710340003202804071124010559600800150141044402c0007050baa418a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 808845449 1250 808844199 808844221
    0x111030c07210f0809010b1e1509150c010908161406100e060a030203120c0c0108192003130c0b190807120c17060d02060d0908120f 58
    0x90000c0303286006056902d842c00381d8031940d81c4030108010b160000d400c1d1100380f506401001806400e59020700c0b0b1500101c03501c1d1407840c0100d400300b0100c034482c490001c0c214001045105815103031741d0100d00e00e00f00b00c102d00316402c042d0061201e010000138044580d035407103407001d5002c4464254140c10600f982c1003040800120707801228a42c0c40038002c42d01702040d90b0b0005504902860000000380000160b1503100c03652000c0055070014121491080303500c164502035031196082c00d01c0d41c001c00050b40b08079400340d544503006054001caa0009942010350303900041a40560110a1600c052040c030503014118000e54015880b020004041d2191441e010304104040c0c1d21150000d0414400f81c034011010980d03c400c8840a0304111b035640e034410b40100c8a040c0b48400490b103003413910503c0071286500c443e102c446241e0590001d481502c8240c10000968980e102c02035201c01c040281c12104407064018030f4069108a102c1404c003a022819071030303880c2048170f40e1f002d400502c8040013003c10381 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 808846699 1250 808845449 808845473
    0x606150c0105190510060806100314011e060c0309030b092a0a1e030f1b030501021e0c06010b0d0e07090509010b011b02011809450b06030111030c07 65
    0x81d00005d81011480d107a00135040c00307802040c0c103102e40401d1400b0010360b0301942000c6624140c03c1c0d078500d04c56031900003d03441d0946e01070401240184030940400c4140c0200e080601441d010744441f07035420b00c1d503503400c4480440145070fa40d49026549101d0381650014070325181c080200d1003401c5d0945141d100b40000d06c019988400261024500c0304c000c2c40c41317024807503000e9942000503031042c400359042610408590704108024036070040c0000041c8031041d40508038150f02110350154040841502860354060b10035030300c19940205004000380711900009000b00c1096000104401c80c82d00740c80c0e070a0803d294019103525031104100040b0386020301c0341010310642420400e0302840c02d8100c0b00740024041c88024184184200b101400b400c20108003070080421a0341030005404103003140306205c0c0c0c2041601401c00318515410711501140070485c003e00103001480f640412140c4074984001c40141140ea095540c5080c10000410381c40020340c0720740c0e100080d140d603410780c5281c40120084 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 808847949 1250 808846699 808846711
    0x61104080f0d1d090f061c0807060c08070815030f0a030e15030907180b0406060f02060106030c02030d1a06030403050301032609040c02010b2101050c0c0606150c01051905 75
    0x100c20360700136070719041d00c1a048285000100f00c9580e418011482d0801510000e0f0b1194045074688000c0041c6c1e40010f090392886400b0a02100b00545402c1d00d9081c0260b80040104a01e0800185010140c03d00d40101003c01012640c2c4c201e1488442400c0c104c0b07407102a00003513040680320800c0c2c01e10900c502c1041011410013883c6181c4209030a844484500071107010101d181c0080300c010402c0d03080a002124002c1c405c000791035a5410191441942c1d400031409030184400001e2818000d11400e28100c406802452410f442625400d009000e82c0200c414480e40715544c111141e00d400c4069481035129468144e60b07541141464080d54850a42200c80d8000c440e4890a418000c4010740742000001e407004906581c3c207140070f902614440d03114540081a0001000c03549102c0100a00c40f101c02d00b00811564170f481c185516940b10ba92152446903000d40d0100b42942820200008a180c1d651000d500703105442c40610300307607281600c05450b643d19106423020071b02d283cad119480d040381c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 808849199 1250 808847949 808847987
    0xc061d03070807170c0a12030f110615060c011418030906090105030a0e011b11160b13090e06161d1c080c1c021603061104080f0d 57
    0x901d05007440e5501d0341e0344e0061036000150119244021001044121062000102200030040d10360800c25400c0101d08030540c001280c0c041410300c4540912500790a000c00d0700060602340d80c4105e1a51a1300c042d0074082500184100491a00500c0a01c45c02c0644810380da02c004841c10701c18100360941e0222500c2960342c0d0401c1000000c11365458040324043c0780c0c203080c09034032966018400002000d400c0d010345429401c01c0c101000090b00800200000540c94a80305002401c440701c40b566010106e448190109000c1818401000400043c240b40c1807081c2e03001070440d45505005050b40d02400245203035078000750502c40d503040f2070f003e606081d4100d881c0c605400750080359800c0755840c110801901804070040d2600e054000381040c00852508080e00507501c4c1110f00d00f0550702c104040030008150b001c3da1007444210701c00308100700f40f01e07003101500394a5030842e21160010000e9125841d0341c48420440090321042c18011038007962010300240c00061601c880240c8510300b140b14802c501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 808850449 1250 808849199 808849213
    0x6090c030d17190608031305011b020a0504181a01031109040b060904030302041703030402040e011b050c0304150c0219060203070303020702030c21010605031b060a09030c061d03 78
    0x300159075440c550040f243c0040c180c2003001c0e08451001404c0d0f5400003504e5000010781c03d010003405031541c1007100e41c00c1c0d0b41d6540d50031401c001d40000c0028a44c2c02544182c17030281c1004140790a0f00f103000382c0c0f844a90f103402007400c00c0d55100c40e4400c0d0600000325103403400700104280314980008803d032007815104104245800d81d54107524603030090007984900300301001f041c207140c82641900c018010000b1001d0340031090603c40e130354a40044400320311490400d0340440101c1070602a04080400c8280b4114150404d8a0140c85a401c80031950065100030f2200203540300002018a000d03402e15100e01283c0e980600501081000d20f4904050180d200301d0104403150380001110741d0980c0510300140c035000d0610029060540400507264024540d0030400301c24040980740758001c0300c884000708001a038841c241500c40c0d02950b80c201d6690000f00701c050b4142881e00c0208800007507031a00901503a100c1c2c1d600c2d0700210180d0062000078403410340c0d00e020500ba80c1e070300b2949081c00320003d29130 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 808851699 1250 808850449 808850477
    0x216060c0507030f21050a020408060916051003110a09030b060103050f06011b08030a0606020f07030b190e0a1103010605041512140604200d2d020306090c030d 70
    0x5400226500d900403c20b14074600c2d43c032a045400d480e4003103c84017205020500302102140d0207500300e40940c4d610b034001da0b00400c881c00d500240281c1035110040c2003402d0180b4150400c840c200700324052000349515048210070242480340200020906900c440e0011829402c2001041c400100f085040c9840d201c20311220145980b00340741c0c803400900c0d0640300d20100074010107501c00c5d0b030f80008003540004400d1000210081d00030400f520305070350803610034001e101aa40d0b0b544065100c054000c803451000300e0005c200e003440e1107450014900d000305450540201840c50550350b0101074651241c00c92540000c0e26086c040c10000700300413641881100049102a250304156214422101415030004000c00850340c220700c4080001c40c082c1d0b407076031405040c40c407500c529056420152000000584956251400442000715000200040ba0003449045004000d6a48000c03a119075280000980180c0e8204482032290003030a0280c5441500d94090619042002d5002c6060012034000400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 808852949 1250 808851699 808851707
    0xe06060d0803060a152a23120409060e0601020a0c060e0609100f0e032103220506060a0b03010e0720031303050d050a0804080a20150703020901020c060d0b040216060c050703 76
    0x850300120f20074400080040d14209864082c5490500e01d170608c01250000342110542d00c800c0c00c5a1040c0240400c41c4d0f6103400490316109007c03001400e20401440a02489114101e00030303c500f0094401ea02c0c24604070002540010100c4140c40041d0141100d407078681d03401000301c01115025002000e020075244442c898228915600001050001c40000c00918102e1000703122848101c0040702c000b1002d04100e0b44031401141c40d180a001d0210380007911a013000116412110f85c000c0001058462039021034590440b003240290100c0d1040201a040c001030008141199817900c584032081c0c5945465428034002ca0303070b1078091000501c25031011581060b1a240e01c154400b84260b80c5441810040e5041a080811100142c106a00d10072456000094011118080480340030aa5403054011010b038402c00f0140b07030040c0c002e0380c040b40380c0e41041005003c00d0781529030081640c06452000c14201c0c2c201c0511074002001034804282030040c0c40c80340e13191294640c50024613115041d18003078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 808854199 1250 808852949 808852973
    0x3060b0a0b04151b0b0106080a0b0306070806010f1719110702240d181401050405100c030f02190807091a0309030705060a0e010e06060d0803060a152a 66
    0xd0004013924030102c01402c91000304015406140054070b5610b0310740c020000d410450390701524600c0e000749090f82d4500080d40c903120704001d54a07a203c82d500d0800449454010300580340c284101058800c0c1a000341d41c08082c421612071703250f10031040c1244540b0007910700445101c4c4405a041140d1400f680703541000a800c002c20345c02c107150002c491142d17010369101d003440160000d8601980f016048108050f001c0300540288021a0030001c0d090f00e0500b00c1d002520010002c2e404a020300310140640d4010901e14945400c002070840507105140f000c4c1d0348801440e03580c4009406040000607004111250080800e10b8448150380c00d0185a050741900c01c50b07000c520178400700001e000c1000c20000c84c4c07141c55100d000d540315800c00c81e208601406802e0003000300395080094545101400052042c400c442c010182d16590110b40c949445541c400303007246420105004d004540307104000031410503c1e10035031344c8030341201c202804100c04c00951010000000c000a1200001c035903526916 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 808855449 1250 808854199 808854239
    0x10090b060409150509060f0a0b0102071e081209011707120f0609180215090306061e0901080303091203280605120c0307090e071406120103060b0a0b04 66
    0x12003008500f09011010f0441e400c40c81000d040ca01001000340005c182913026215440c04030b00315456008145081c0e491100001c1c0c010303804a03000b00201d6010f01c428052600c0e0580080c10866215002941400003c100518074504000f4011805581c030514148801d03819950820090411074401040750301600b50724200662180e85080c0819038642c000ca0051a80020800522200702d8640741884460f080591242400e40c14500400c1d19042c121200408000d0240c50140d860310200210001c3d5003000c1d07045944215000002e603140c0203c87c90281c0303614002076469181039141240380c122000740b803e07500e06d0144144510010640b0a00b4030400081c52810700c440c038140f00032030080c14645d104540c81030080116551001005c918101180c2781030301130360443e5440d0604141070395600c0112850030b40c07005004008852a0940310030705054018485850092030036500c8088101c20b81045d60300d941d88000d000664603020500034014400c0320101800e0914100603880100200448 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 808856699 1250 808855449 808855451
    0x4300b06010203120f07030c0e010c0201390618020d080318010c0e030f0d0e12030d020706050708060a2d120303050906010b0708030a0216020904050f10090b0604 71
    0x416490782c000c2c41541c40d40202c0c400400410b03d000f003851a215001a251003021925065288c070a441c450300d080282e04806031070b04054030040e03500449a10b024482e48042101c1855940b5035003103500d0304900c0210804001855a407841410103100310744c88800c8110b40d11000b008210300584501c00b416100d603800480042e26680c0f00c0711000251502070744006603951030b2191940149820110ac0748256005800b03c07000100411034042e41c40020082080100d00d0300310300c103c0d480c41c0984010707848202c40819a401c1004000c0d41c1d105a8102c2c18046410320b0300d40301000201603015418650200c012074845c4002c80c81c18503100c10741c0b401d50001c02d100104446085404d00230b0b61560400912441c20100170b001d5003820001e000305020f80d80c80d80c46004032000051090fa83d50181c5101c0d0f40c111a03001c0c0356448283c00180294003211000c802c40001c241905c0c00f583c3c603100200d100b0750061000e84042d080000d021414400c0001c54511079078030301030782c14020444041925600c0007081d40c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 808857949 1250 808856699 808856701
    0x30402010e041802090426030118150b0406051b1b040c090f0906030605011208390a0b0612030d0509030408160806070e06030708100504060b04300b 65
    0x51040c1d181c42c030340c0c0f6000c0d4005144030140000c000c85022401c00e80c0e4866542c007a43d160300411880520300c428031a03200c40d59011102c0c000c001c00981d002c0f8414000606020b8855590340500396a40e4000758400008144045a0070200d96403c0d801024207200c1c22000c3c10b50040f006854003910741d000c901903806243d84038000d001031402610400040e00c2c44003a050341c0207035104100400b40030180003c42d03800d820080000340000f4200340c00380003507902121141c2003240c030001202c04038603442d580241400110450681d444100050342c40301c800c2003c040d0000d031485003010101c0c85405014030740107508100502d010b07c071010007507400c201074100d408036140c1c5400d80f00340d1030760040360070050b414029829001c00c00c1401001100481d1280026580e095803900019654032402c90601034001c1020000111502d01c100c2d601c40e40100e04000c184031031622070340070404541e4249c2000301400e20010307041c0303d020781444401260400504861415401d000220740486146401c01004140c1c600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 808859199 1250 808857949 808857971
    0x1f0f11030910051008010f020714340b04031a0702120426010e0a1a27010e10140c0429090d120f090608071d0301020c0d14030402010e04 60
    0x3500e520010f013408170080c040400310201c600000c0d0310401302215840d400c80141c40b1141004550a08091200003c1c8030032441154a58006204010843e801c0c4401c09034001c610010810043d0019501030390030100307201030810380840c4101c00a042c44c020365100c1c0c0203641c1d5201454044074155004041c8000800500000c0d41801018800080400e1350800c050560b110100241c0e011303c00b4003a80d8401d900d10000103044031822410340d26034200500580349a0305c50006400c50114407032222000046042c00890050300703040000c025444050f4031510003420480a05c1001034001c6060f07a01c40b03281515010000b00e511404030300c0480105400e02546203c90790076002d0311701400d0080d1840e5020a1189422286004801d1422001c40c5066841051081c42080740300241c4a607521100420345441e03006613130024580700502c90300303095a140400d42d83c80a00103004442c03d40e10083c010480302800241c20310200503a131b100000028420400583e911130404080e00d04240c0c4e000803694800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 808860449 1250 808859199 808859221
    0x80c03012303060411210d26040b070f030506030318010c150b01032a0e030f030415030612030c0b0c0903031204110a0f03080c1f0f1103091005 63
    0x40d0159038940603110810045c05200860124055003c59001c2800d10142c481c018419000701c007030f50500ea00803404c0ca0400f600545000c5500070f00341c040161600340400c8100c96038881214100d418517030a0091282c89500500c10400802060409108070314001022a6032401040d460b810b10101c801c0102d8000c0c1d0007528065000c039080450b0880301c20342c900c07040015107403141040380002d10702080c00e13107100d42c0c010480002d118003100765400b000c1c0088081307034420640300940350300d070003961041c1c0e00030042000103000800c0c04030141c0741800c0c03d1040c00340c104c4030254410f40d090b04800a08000180c1d0000c410840c15038459400c00c01d540300d01d0b10350f1805000301c1000c560507100000e003400c100010400300074441d6128181340d0b070b4200d061100b4001c42e207400380b041600c1000700d21030034000070301800083d00380e008060007281c2040d8081060a100b401300b02045046440d5206081180350074640142600d40d04015045803035410803582296603a000c001c034141200744e0b101d000c0f480f25901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 808861699 1250 808860449 808860509
    0x601091a061e0a0e190e040f21091505040e18031e070209010605160204050603010e011517060c1c06030204020a0306061107080307030c0f0f03120c080c0301 69
    0x2e2044054940c100c0c1e290281070801c40000d518414a0407442c502c0e5814818030b01c02c1c0aa610b8205551201d89035035480726102c007102c0004032206c000d100c0c03204050a00503500a90100c449641710903095203082e541a45044040300c1004c20000104030034044642c00c165599000a003008011203000040c1c10520300314050180c40400c0142844404500400e010000c0c11b515402250500310a0760b0782e00042e541c5214290103111008180c0c46900f0142c40c080d0300c101d46c0140701030b00100d07031001c402e242d003800c5401c0200d8900c0c0045c0f562009201d0183c484610703036200c0301584000d2504d41004035a400c0790f4003e60b4082a402d175442415600e20f070131355400c01d40046d540903100790b40760300100fa006009000c070f9010f007a0008103429a2003041c40c1e40020410100c8103803070085c41ca80300c9076440458048803880e00a540c41028041c1d6400083c1504050560581c0a41c1d502810f00008010080a1301d045440e5142040b03c40c005110407207030f8141c200c3c1d0440300d04030350603100b48160354483d00b02140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 808862949 1250 808861699 808861747
    0x1e090f0b04031103040e1503010e21090a080d1413030204090f12020c0f0d0206030f132013050f01060807200c0406050109030c0515040b0a110601091a06 67
    0x40170500044c0700401e4001c0751302400c0302860071841203003840305042c201e41200340541096030096010392001401d20300103288c40001048150b2402c6160070204082c401c090f80071141c260300c00e5500452855000000034440400c403080c3d40d00c4c0000302199000d400105000203403041c0c0e036440c101c80030080040c030a1080c1135400494080da40e43c00f4000a521140740a8007203004d00c83e81e4240100c0b0b458451040c0907480d5000302030a00f143c0740c4410812031840014040c030041400002c1345400707c0d03d0700801180510204850310b400000000c00c0c403420170035078030000c103005052500340700490400081403410345440e840c0c41035850750b0b0b183d0700301c07020320340540948140703c03c02c594600300307210101d0300300d034540ca068170709121032a920b4004480c0017500344000341c900b07602890240801d25194810301d0b11643c4a882d600e090039204d036013081c0c0d43d03809680880003144c0710780d00664800c00148002801440d032400304002800c14224038541c0210540c8040e03200303420000b001200200d0798107110283c21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 808864199 1250 808862949 808862953
    0x105040e0f070c0f03090503010608070f090c020f0a050f01060b1c0c051c0504020a050904050303010b0306190603020a030b0402160f150c020a032d050a11060a1e090f0b040311 77
    0xe20170300700070b08841d415000d110301950920342c0104501d5000540882243c2d503048910107103a1821542100518019101000314060030028144040e000c1010045032402100603103040a000001d01d400c403008d80d031112000385403c0c40700c2500702000c5c03c1c0010038110000d0000c6800c50003804215141c0c4100c07837081101c80360004882d2803c01095000314459403090710b000e00a44e80751001c010340305d5001c4074010301e26402000140210040344000e0b5400040140c49001801c080d00d0b40308601ca400358001100090b4003080c1c031881d140d89030280380d040c4407054a04610300f02200201e0846030b034400d800030345503032401c000020810640c070b02207404403004001c04103c503141d01d0340025151401420241e00080c28001c0700081c08407041c48440d14042c60702841070310031881c56400c3e42c442d0482c4041005000892020101134981800218803c604803100018140021604c0c4804840180d55100140d0302d000e0114001030a41a00c1c03000c0a0340004010040b541d880c41c0840e180c001b0541d24903828 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 808865449 1250 808864199 808864223
    0x30507060905010f0627090b062103180306150303090415050d050601051503010e010515130e16090e0406090f0c0806060a0602061603020a030f150906050105040e0f070c 74
    0x10744010904401c0c464030080041c0c406c1032182c04000700f03584107220050682e40441020a0407072401020810081e03401c18000c00c011081c0f0b04c00c91f411600207010402c6550a044901c0307120b440c05001e615400306003000070101070001e01c8042596030044400e820b006540c0c0f030700300780e5140750f01c20b1800d0018032008041180103142482d00a40700c1400380b00d9a070058151406a0030b08403003400c03d981c103941c0800d4440c0030680c68201000030042d2520146102d4200403c4076445c040340000070070000d0002000e4641f400c0c203104241c5004103000a00300c20400c4420744092019010030b00d0999005a04024045400451030600c2400782401400082c9500d0046000140500b0301003203481c0f2441c0200c0703401158a41d80c01c4c0aa88800c1d0882e00301c00072200d07508180e074a840c0261701030310345200b4524000450040017072004086500d06000199180e580000801c12407845004040107040c082c6010343c1880d1400310440324205000d401805603240c1a03000854261180d003040b03980c9500b018a090310 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 808866699 1250 808865449 808865459
    0x813120f020c03120a0215150904030516030e0f0307080303060f03070e191506200c0a1d01060e10030c020a080d05062e11070b2106040603030507060905010f06 70
    0x1940c1c4c0030035000d6002d40550003036500c02048624180d8812040c1d148c4410b15000c080707042223600c0c00002c0c030882c03c1c0030040c0304140c800070710148c0108055109031110601240a042008480b1013210f4655120b03a008800501c1001d1022050301e801c03a405403103104030f41000c00000390400c1c045400c1380780a00c11000410400110070802c00c41380c02c200540810403020314070342c82081c114140c02118086000d8091407040c5d984052520313049080700303005840a101204000502c1d60501d80c2c0640f00800e000b20f507407070002c100c0c0c440745401000c29042680104131008040b81a481d44200940145651050010401d134000d120196030782e5071040030690746c0c1c07103043c004130020300055540c14021400140c0b024107120300d0b501018025102003044081103030658408860400ca06c0c1d45a41035802040000030743d03c2c1c201d001400c03804030f122120440249484030400308000009200300c0c407450500700c0810220f030b080710465080541248000c905220241442805410244100b02400d031905c100010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 808867949 1250 808866699 808866733
    0x506030c1b033001060504050a050f0406030203012f120408160b01060306081b150f04080d0c03020f060f040803040602130621051b13091b0813120f020c03 68
    0xc485900001110340036605c0e201d048441c0e0007240140c3da0850b03d4080c003800249401c40c524800303644020400305101d80c40360f020a0035104161068021030403415a88000046c2c4111000c02c824862a451818614807014104014078007420107010800001003e03034040c50382c00f0b04032816540100351402c00b542d440034000c005000f20f104442c0c290082009242c030700441c1c946a0f500d40c0b40001e00602c080300103030200c0c104950105454411070842080300042000003400704c00c203400300310340713030821051142e04000c2e00701038152890003a20340081080103100c0d2020a059600980c01a12098980da10b40c03600714000e201d00c0540120380c00c5044000203070103600c031051010b041d10801c1c5c0348003000401030f00c11060301d0302540c01170151058035180100d6003410300044c2075071a104021003902203945600c1d0070102c41176a42c01394002c560044820706400e4200c0c0703880c4c1c0c000650449010307a070f100648420700001e4125200700104403080d4642c0910314820403190818140080588801e0024182090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 808869199 1250 808867949 808868017
    0x501060c1104020a090b090a05031b1c0305030c161a1b090102071e0e0a090c0f21061b0815010305040f12030f0912090506030c1b03 58
    0xc841011006003800c035410315000381c0e03130314500549980b84d0083c20a0b1007505207030410020300d07400c801d91200010b4559800c01c140321b1030401c1c40d90701542c08004407041c0482600003401200d6851074601840c00060340c01350440e940215100c0c20180c8500813446850140140160050800220f1010142c070349200300c5076850207842c4a1002041c0d121190300361a0b414002d02c0c401a0240e042040100326082c115030400030300700c20642589440c681ca5401c009012202907603000ca0940da110103401c20072002c0310182c07000e41258445a80054580710140a6120105001c0f114900c1403040400c10040c440e0030901c5110300c54042c0e62101d150307803c0001c0c000e2404444d020001410f181584c007003035001c0e2091034021500a02c01d240b440703005072502c06100b60341c0b6010030101940d41100f2030329080c4911a08110611a08400e004514440e200030020303c0d50760042c1e8401c80003001801060309590003181d0f110500964484c0150b00030240303041c118080d0304103c01c3c00441070102c22005041c1e601d01c1c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 808870449 1250 808869199 808869203
    0x60801020a18080d2007060203070606050303090a140409050706260f0f040c08060a0b0f151806071401060806011502060411040914031801031a09090a05010501060c 72
    0x41903030001c0507490412a078940788140d07099038111080308101e0a1180c0b0006070740c100c5003c1e81540101c25000c03106d160442550088005800c04078190013003140740d015a8004060480066060070681c6c1d0003c1c120314203900c00c0f0920074208411100035a166500a21855a001415165015501e8030302914020000440703c881006481c40d00c0c4155600700c040600800d0707120140150f9984180020600d554060301c280c4d200d900407140001c02a5003000032601c075102607070001c40c14a0242c0144420b10803440c101c60311030000c6450a00803040707000140e40f40c1410007114a024400250080780203403140703c41c0a400000c81d0609201d5940301500402d080703c0c00c02003140e907141e0f61085032083c4105200b0051005070001c0e000f140110b04884004034403481d0050000a030031986580305921312030001240381064002050a400124500e9440ea01c03c00c02070038240b00d5603458100101c00b040b5a03c081a110f0b524410200fa0100340400c642d00c1440e5101008010035610380c1e4001d0001e0030fa03001d003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 808871699 1250 808870449 808870457
    0x603060e0c0a181514070803040813031e1a07080411060903010f0e2a040911060307030914070506120406020f0c01060e01141e19031401060605071703070909060801020a 74
    0x42a9406800d5070101c2e026150001001803c8d62643d964200199101c482c00314012400f070580800400c00110443c6036043e1008101410201b1b186005080f11000440058118039a002040813094100c28025800b56100c40360305c1159480b140000c03094080c00e040715805620340580c03500790700f613582d00103001c080c1540c0403506c1c00d981c44980103120300c2280c0c51a1443c104200220340d071904103504065602c610404242c42902901c1c1d0106400c1d400481e000d0002907140c80748441882201e000c400300720310780b510141941030309060110f0b110b841076803807030700680d44224005020300c0031940c141e45081e010f8011403540d40c05060f8100e40038011318007804e04c1400a4000025802070885031032210140054101d51668201480c0394030003241c6070710016040300c0b01c02641d103200e510381080350780a18410710008503280c1e00001c1c42c60845489800940c107119040003000301041340c2a640c0e000c05800070904655030341d01c00c00125034001444d448a000e880c00e0400119200f0010340261001c031504d651 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 808872949 1250 808871699 808871717
    0xb190c08270a0602090a1a1908010602070e100509070207061202030708040f1406090f060f04170d020f0f07030f0804020f1c02060403110a0603060e0c0a1815 69
    0x4032000700200084660112640002038500000304250060702d00480000c168030380c40703540d5504030605115914107100c1c6000000410380c0340000001e0035890000d015203044842d171345c180345c1c01079078940c118003404d990070340e444000406c1e1103400c801071006090f01a21440181c03c0600010f541c4a02c58000c40c0003044a5502c1051200301600c00c3d40e215103107a540b600c00e00d4842c1d464108076102680c40589880380c0c00d28203e5008a00cc106507400b451295004001e0300d0081803400303040241c00b905100320a0700744002e20001c01d9040508002d05681820305a40c0c4001040c9160000d2090b4040a0318045011804082d002c480501a20000e8025111204d50f8007000c1d408652120048500a510600140c140e10503400c1951301c640c1c22a4544050b20303010107207500000c01c01d804c142c3c012506204040c0c0760200f1400c01054010080c503031401d080c0011420f069801c01c082d80001d2107010400008603001008510130a4940d000b008030320f2400c0d89050700c40801c80c0c14192001d84580200310700513 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 808874199 1250 808872949 808872991
    0x9090804032d02130213030c09060b0c0606211002121510030203060112060b030604060806040305030615070209041a090a0b040f061e0e0c01030e0a0b190c08 69
    0x682c5810103407201ca407503140c0602003036081222140c0d01000e5000303095400c0c080b1980c0c8450380d0780d0007000fa6014083d40303281c0e585442c20060907111280c2140148100500074540b070a030703001031070356001030341121204907003031100f90790b020700e00340c3d1017a4001d540c4113420114994032542c1d40103000450407080455034964030704900154003822089010b8120780c0c082041c081c618401e501454000300145043c12400c1c0d03101d0110420b03190150403240050714004240318039885c00d807140310024025030000e8841807415840c0034000d4080107240d540105030210b0801d41c141031150880b030030307164001e00c50246030800d410556199450841131031850741c180804100c8a00002554000f82a880400e081a554a55070750400403007135081c080301c480340c841c0b1110560085644081c0c0f80804500c1d800078501c00b00d22f040078030b000d1000810364185403505000440c81d6201158084101e6003003507001980d0741320040d010301003070301c2c0d058101280c1e8503190140640340c0d40840918020300c041d54101448000781 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 808875449 1250 808874199 808874243
    0xc030e0a050f0111070f08031b010c090b09210a0b010e0907031707060e030a020c0a0e06040207230a0c0b030705030f04050a0b01090b181512070909080403 68
    0x503009480c0e100c441104080b507698400c0804c2d104084100b41901c1000b9643c0c07942d400e4456060300404059007020501e8110280010041980140e81100910058404142c0640b440b4660b001c0d020140c0385c0040c80da800c9031a501c0c0c02286e03030507128548044000f00c41032082d0700e07684800802c41e0001d11440000680d030303120b501d4603070090981501400c0e000b403940d40d91a0540d651030054440208040c131142d00800d819220750400e030034040c40907542e01c0e640300200a0070807441c00b00c024400e00321941c00344000b034185104a50321020984005a9555031402c01c401c11940d9508500342150046c07421031074100c800f00b040e482451290240201d41ca4540c5080810740c0011603c40c0c001440c28000035491250141103590028010820303219000c085880b0303801c248070240c101c41d1400d500e40042d59180d0510001d0a03150302000c014450710b07800d064900004107900d2140d8a481502284503040300000240700c480014041d401d02008001c1041c68440501d800c01c1c0700941c0c4103284c060450401541c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 808876699 1250 808875449 808875469
    0x17040e090d0e06091003110d05042a03030c0213090521031e100b0403120801080a02010905060a030b040603060e0d08150d1a0a1a0307050102070b1b0a030c030e 70
    0xc010445401d02d003030f0304c1c1405a11440540007200b09a19101d07400c181100300001800c030201100c801162914041c28035104e5080704041540c003111034011032102d001c1311016207a003641e0349454801240c2083c0d000082c1c14a031422041d1400600e003101804c1040000150074145a51010180f000602c159001665500007198850103220b450860548403a1642003040d03400b5a10300f85010403680c0322030745c4002c160400d410841d00300740540c010b1010745400845090040c480000108a005200e82c002400600980300b49030040303201007901c4d16080c1c040e40200d10200809002000301c01d680342000000740c14251a548070a000e00240303180907a115214081c4905203191245040184020500210280080085d60305010301c0f150425101400281c190040005140109a030084c40c50006074071000745100c02e2103039001850410980c1d8002c5641821140d0455515403117400007202141064140b05004800d4061407d01c0380030940c000a5010751280265a0300000b151088280108441 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 808877949 1250 808876699 808876727
    0x1b0201140603010915020a09150513050a05060d0506060f120f1059091b010c210c0b090d05190207030c0f080f15070c17040e090d 57
    0x122034072804d403200c1950000e2040721164500714a40c1c0756140750344c0c40129009c1291000180c4002030034180180024240c0024000803260200e1162502d0005406072041c1860b41444d10f480303600040032a511002070301d1068191a46153340d502e0f50850900140f0001c4801c0200c5026000204100f01c4510224109a13602c1c0004051034640019161114440400141d407005511003200070202d01f54068204c0e070001225052480300c95040141e1880c144000c00b10b6226601001486000003a200f0402c50b01d1602820100240c8540c0c2c01c00b400d240300808a22200d61700c2c40e901d10100c00c0e902c039011903001d0307026014044164641410007030711981102907034800034130103010206582c140b001401c2c034000b110307004030303011507a070782d80d60039a10760041d030000d440038049090070001c140c024401180303a00b01c07010150441303041005001000710009008402049070056a90040100b503c1070b8142100802c1101911143e845641c80036404007100d0f03c0c0c41c0c81c0100107176401d0882c0640c481e01c0c40700c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 808879199 1250 808877949 808877963
    0xd03020a320d020409020414090a111b030c0106030b071209020a0501030c0c050706080a0b0613120503040801150f08010b2103070f050c030d18181b02011406030109 72
    0xd20704001074622038224070070008200d41e08000020701540580300410003031045401d100f4508040a0801a5101c1c005007807120b91800d11078402c1f002c400300301c12a101003c86c08107006206040040303140c07960148080d000225881d044012040c081c04a500b00d104d00500d665120148044c0035010040c0c1d2900300d07000707412280303841040c0f29a60080c1c00c40350a0005134507040c48003d246884440c680035056002c02d02240c08103080c00095951030041082c203840644809141c00e40740a92048012064400c0743c601605607072082c010441c05008070323001814a41e00901c4030758601030102c02a00803500ca129010b410504000a0041c4103003c0e59030700c0c00300144144000044078107034580100c43d5480001d00f50004005200014140c201c0d07010801d0b000341e004260700c0b002030090510f007103a4602810240040c2ea80f0100605100071940d100f594003401c0581217010340000c0e441c01910310040752445c0302400d07912544800d0750540c090f52608860080e0f602c06503d425051500300d58082c0c3c005440c3c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 808880449 1250 808879199 808879277
    0x30d021504081608160b0604020c06040204050703090503071a010608041e02040605040905101112070f051201030813290705120f031008010513060b0a080d03020a 71
    0x4204910003910b00d555034140f1100d102d640310344e01d9114a52000001026504600070780f0f50a0141200c01c41790720040560741113217009481b082c0940d0b105401840280304a869900081113603100e5042010301c150721208490301c84001c3c0c500a10800004560420b1004141e800052200c1c40740e06c1150180382c101503910000140f2104040700b51146410030f036005501e030100094151214403c26442500038000b6001c60484440712000b0350b0103110035146040424000c11540040c82c2c003086400101d5402e10145655402ca400d90342c03805000d44000b84001210000400d101182d0003c00c03025480c2c0300204d50f45c9403900700d0030207405103942d0b900d00d0314404680741d0190261a10001c008040c0110101c1340c0600400a407081c091b0321010f00405c41e0074002c02480441031041d4038034406481c0300c070300078011407810060308400d0300340c444d20241507113071903002c60140780d1103004003030025000540603594080d0300c2880c00b402035800100c507500050a00c108540340c0500e80d851200c242c40381501e403131a803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 808881699 1250 808880449 808880453
    0x1e07180e07020a021003060509010911090d030309060f140601020a050d0e0a1802130f06020a17120f1518070c0804081c2a02090702030408060411030d021504 69
    0x403040041c8448103503c503043c03540c030259880746452264028a95804201e050421084c0f011050741a445803600900301040705081840000550300c0002d8241c413191824901030401710060801854040c000900e07015605512070303480c0d00003041000c040740700c808841d20383d06c0049030384016003403014100790040b032103814115100d403401b80c0200b0f100802611203581c503140b0f4102d41054580d40f1808181d4005100c9026109020f405c60040c101c00c250150803d00d000c4019403a603a08902c01401a480d07446035a0000103014241d40515040c1001c02c810340c0f92041003500c401100f0b0361003045440040366001070300d2600030b80e4400c054482c02c0c40313403005445214064641004001045501a405210201d10303880c0c200080702c82a40703003072600306920b40950400f07010a084040d0fa075007281c4c2491203124172415034080c0c0c9001154140e80001690b03032074690890641c051074101b600b041c02000c0c1032000380000c06600e481c0d0b01200710203843c0200354400701039a4400b6030a5280714031401c05400680 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 808882949 1250 808881699 808881719
    0x160e010c06020f1327020f130f080708071503020304080c0a0b0f06040b0112050a0b030f0606100906270f060315050306070813020315040f060f0203090316050c091e0718 74
    0x303001f078a03458483c1c14074050808941c180c1c441a00120381e50040391004100c0c502c41082408010401c103009891070030f04200b1914244500104c4c041c040c1500000403c04002101c8200d6900c4903600303040e0b88085807146408084100b0039101003030f0764100b40300412142d1409100d802e182d030b00161a1400404042540d0a025050051230481d1a540d10005000613880500c2140d207a0115140500181c1c5043c80400a112009103500800c200c0b60303900a00400c0c1d0452180c2500e88030603104185100d44043d280c1c11710150a40107842010490040040c0f10380d010b4011b0500030320001105205a51182c05041e1b40748000c0721808002001c4c90042000707490301c041907504542c009400c2c1c0314500c03440c00d5028805041038408032010503a24642c0d5061002c2c41c4140d0303008140301d40095286d03003454103c503942c0e400f6003d58802154a500c4042080160403c165403030040050724515540c540201040104c4075440003d800c0c092800f0009403001d8461001070401c1e6030900a0803030001e04100540d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 808884199 1250 808882949 808882957
    0x601080115050a180e090d02060f0615070204200c1b0a030206030c0c0303040311060708040c0618080601090221040314090111120c011103160e010c06020f132702 71
    0x150307484840711012810f9600c5c40070700c41c480c0031101d000780940120441c0003480c200380140700b00038040d00142032021960f103e0701d1100600c0c051aa920f80c40e20880e00015000302111110b803904450b00c14841c121000765071000d000c0d01c001e05400d541104110b81c0c2c401d1601c55424000960100704e00d081800140341c41d0000d140c00801c2410944e003001c03a8452010b1441c0d206031025000310359030100030140700b4401c001c9031703900c00c0252810a00301d007030654503901d81041c94050a401e10920480515082d120506110004d107042000c0311445d59441040c1c000030350000d20301074950140d034000a03e201c3c0c0007a10341401070340d00d82d65600c3c0006052580160075000100d040341000401d0303810b207080c1c01040225814048445e06031680c2e030411504140c1c03c440407603c0034650381c442802042903203c00708003150004d43c4117090401c011400032004846094000000500ea1840401d00f1419080000c0c080c04c02c521405000114403074840c4150780009034554003d0291314030201c01c003190f0080c1c0350050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 808885449 1250 808884199 808884227
    0x10b030c2b09060f18030f0201020c19140d0906030b04060e25020c13020309190605040303060e01081b150c0c3c010c020411030601080115050a 63
    0x404145030082862000309007003800704205807034442c080c0e802841402d21440544648068003049000d04c0102004200605000041d0034000c3c01c40700324203484c0c002e4045031000103200064038035051b4403118508400c401c00400b5120225503104410341400001103040b032001c034907104c0340070203403030034070210701414218a016400c10745400c400100703104484e40560281000390800d2a061400c80100207086503251500e00c00c640c0030b441d04014948508920006000b0700e40405640da9445d010043d127003401143c4902510382035410303130b0341c14840c480d400103014500c07c0e5024029643d0718081440040000c5c002e64001e9000f991391100074001d07200303004003181c0d00548070003030074074103900c0040740b942200c000086c150f00941d05a0b1060300d40301750f082c1180d0071000c0d000c544217804a80d43c0203511415031908035210501d12400ca240744e0181990b4024203500030030501000309003038441e41c85030f042940c1c0d0300e0200c0d9405002103a480c84c0d00400042c00130b0145d03070b110b0400300c01d08021144c041100c0b03a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 808886699 1250 808885449 808885477
    0x10c0f0212160b09010506040c0e010923060a02031804060b0a03050414010606050c120307170702030d0f020904051b0a0f090b0a050403031701050904020d05030c010c09050117010b030c 81
    0x9001c0000300c1c03c6101500c1a2095000000e2502d030000a00c01503070200c111420400032004a60902a0b0304102d40000380c1c0d801c01188140078140c0c2034201e4040000c0b842c0c2c50f510000200300c18039a198000002c0440300098174000740c10b283c052040c0300641c1d40324011003100e0b03403040c44810a00d51080e07011541c000e01864040c003039003a04505031401c40b603180d00702400060000034013040c4601d0400c201e500c81da941550092130740ca0030303400c024410490308078403051212112010820051003081072758804074021104114125500d092040203501102a050080c0e003040005400089102c40e0310540110140020f0710304a94100202d07807a200340c004031401d00c07500c4807020034198013100103014060050340303d880da22800c50402610107400c403190001f181445800602036512004142608554107032443c00521400d89440c50840c05241c90340c0c0d0a540c43c09544100750b55120002c10b048840a803a00c4112500d80c19440d10840400d0081e140316544c100302198951a2310303c004c000000038801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 808887949 1250 808886699 808886737
    0x906090409120206010609060206100515121302152109240103031b0819031413020a140604030f020105190509030601120506040204051b0c01050108010c0f0212 70
    0x5510760040069211090040c0d10404c01800229089008000a400140020441c9140c0f54540c0031240546024040c01204001c04410940503a401a606a82c01d20304100d60076283c00c17020b00041c8407131541c003030340328440e0300c0400c04000ba82d050031907020b9108039849988940340c00344070054003e0301401c800705503ca2401907001240000758900c018115607903918085514604005008103000848040406150b0003c2130015800f00100c4640c080301c13000c0c41d0440041108203500a000e0a00200b040583c03060800c10618030b0080e601c85024402c880c9082e826440740d036940d40c04640604640d4210008010600200d81d40c00450310b9402c2c070500d000380c03030006158051441007203101c0006010500100310f8258514040c00940c1c0940700c142d4940d1600320b82911040d5403008064000f90081d41e0b2580403844504080f000002c21101a1009aa86035854011503008003030174030904203203500c3c1c10b00003800d1620602440c2c688070281c2e0b00920075113502c400030300340d1079205110f490701d01c0800b41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 808889199 1250 808887949 808887953
    0x10e0411150d0b0906010912120905041a031618201204030311030c030c0a091505090f060903030417010f181b0e011203020f1b0a0905010b0906090409 66
    0x14804201d07042e90101c0c04510100a00c01d603031001a1900e4184201040c080c84800114104444a5600515000801d842e850401d59844070103400ca103400506040c2c00038007440f4810b410b450708110643c00c54400c0b03044091034106c803002c10f00a50505550280101b240302d00030790404442900c02d491410421903800011084075404401905101040c0d50200310074142c05101c2d9883c01102003488a01d50300e80303c0025200f5110050210342c2d481000315091400b1413041c000c05014086550000041c0c2c082c0746000790290304171800c9144100c6000c030f00c440c1c25040c80ba040c0c540f81c110240055040a0030704910302d94510001000c0b4010b0740d682e00c410307017521046006401ca1003030388202d41e405058880c1401c0c01d00700d400d01380c080e5829a40040c100139015842075201d04441440014050960080c0350481c1440307403600580c5618400d05d1a034102880c42d040074010b16013412038851f03080c1d40c0d4607811101618001d00c81c0e101024400c3c010b800140c1001d40c0144003028008000041d1341c40302d0303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 808890449 1250 808889199 808889239
    0xc010501090e07080102090f1e090a0e01060611190f0b0f0103020f0111100c050403020325060923060403021903020f0109050d1e080307050304030e0405010e0411 71
    0x340e2200e01c80c0e9445503503164004078240803243c09418607070000d40c6003a008101250351101c00519031400b48150040c10248a10444504203a800b001013032000d107801c0280980019150380701590013654079040d07000601900910606044082c410058a41000c0c180c01c1d54020b121003002c181c601e6500c0d250b41e0000150601d000c1481881d0703501140a50b94103600521101d004607c0506042c010030300d90300703c98250000707a080420028144040707088108664111402d028943c0002d415109201d0045e00c40c85441d03c59225102c48610300055465031a0b20464562600303205255450904442103011a90442d00c80302e0800c5014040d80c1c502641c0f940850019550120030340d0000e20707144030a20442c030b8041c0200c010030209283c1a0f8686081c03400003100c400030988000e00280c0100614200045d01c8190003550351b80042c00a03403680382c83d04001d42140d01c07c503002c5000030507894020f5102e16151060301d0580d4003e101c800142c3e45d50b40d6a001c280041d5211b01c69020310a207612040340640 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 808891699 1250 808890449 808890451
    0x24041704060507060b0d0b0f0601091214010e061630020d050604020c07050f1504120330020901110313030b090106050906130204051011060f01060e1002030c0105 71
    0x5607a803143d690780c0b0103040c020100d8414042051107804a07601c0c000c08038041804054002c0c520048603040c1d62a000010384e0460346643c040c030600302c8100991410300010035a100141c41c1d046000b8004001d000030025151003040356403ca1211102000801e03003440303102441ca44010f144034410002d007035085a40c81c0c0c2d0211780178100f80e0340d8000402140b07510f032034001c0c5a0064002e0314290b051004070701c81d091700c486035401f44501a400c1d00e404404250742e80f0304010b14541a01d008240d07100d84880181204d003100702015030101c1c1d2a80e000c1c00403120542441d94151445403101c14802843c600010040d612030800d03141085007540c0c0075219504244000c0044607042d03115407448038a1860800c1c852000107240d10092f03494400104903d40720707504500c0c0e00076001c850405e41001803810750002400f807904804d4010300c90b2080160500d805c114130442002442b02100c51030b54420f020311201b44405d0080c080080d036031082c02400740c200041700e42168040c0340180d904040d150310b42ca50851710 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 808892949 1250 808891699 808891709
    0x5161b03050d020c03032d0c0715020a020a05011b0b0c1c0e10150b070308010302090c0c0a020f06390a080403020d06020c0a0317060324041704 63
    0x140220030410860308010020610074580050000010b0f03150020381c49001d00c004448160000400c88209141e460402c2c056031142d140a03540c4a00c040700d015651400da9014040c0820045850681c400b0b000282c5d1a40213035004180c4c04031241460011110b2842030703402c2001e41c1e40f52008082c0011680c40d07203144190b541c45049601c032789a500c075000c039056581d2800b070481860f0a60011b801c003400b02e815890443d1813080810070000611080601e186698416010010045240070401d40d010700e40c641200e0080b9194481038030380f4800071180d40f04900382c0c803009601840d54440141401452240c6400008085a0628104510080c10382c2840c10104104c1840c140c4d0740815004d10f120811440c2008070f00500c5018010f60700c01c0e9480c8207901000c0d2140343c0f40b904c1030081010b40e404882d4121150000d55641b001c0c0d51034040e040c40d0010310054070820701c0741c00103085401d0005850240000210107440120610418141c501e807014006030384001505028400c5e8640703200007003004107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 808894199 1250 808892949 808892993
    0x403020f1201050421090b0d2d0209041a06070b09190f050d0810140a051003090c05040e030a0c080412140709020a050304080a090806010902090906030303040807030516 74
    0x180182107003003000c2c20340142c035814410407030804d00c0b20301c0e620010341c0e00540d9184400201440e040001c81e0110f02c003400607107010a83c0580c274281c60705503500642414481954103000212050180030140c83e90480c0c0250003034800e0110300c1c046003042c038103240c01214200c01d641c1d800c0340e25404030070741c0015401300343c50b801c0800d03182808104040151140c0107003070307143c4141c281c145014801c890005a1081e01c01062043c02c40705081e40d00d000405008040c02420144d40c064580c0c1c01070080c0007079003070a96001e24044000552420300e400740410301c0c0c0004018500d8a02030f010151a0130510407415642c460061001044070603402c1c6101440500901041141d9811856902d02e081c500303400c9640003a00603c00b840d4004e42040c152500641d2008c48103449115122080360307064241e0b0f10003040c40c4600303400003030040c40f00d07401048028000e80c1c1ca80e02664410050680c1c0e8030003524014400d1408028403030100303100c1c0c03004e041555050b885805c0d00b0581512180d08890310045444100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 808895449 1250 808894199 808894223
    0x120504030e0909070f080d020d20010c0906021b01210b0301020c06010e09070f030305071b0b04060e0111151003150b0405010501020c0d02060c100f0b0909120403020f12010504 77
    0x40da100750150401086e0502c000c255881080000075210522038a010040c04040341840500c030060078485413000e042007008200c00044054000d250129500c902d0000d4041c01c0c00c003130300e10702061260040c405410303110444040182c14050460000014001613003940c0d40803010718940e804c0c001061410000340040542c1e50601410a00340c682c040e05c5071000e540030400401080104003900b90480f0b0b01800d0403a107441c0a41004001201101c84400b03121449401c080751b01c0342000e0180c002d542160350741070820280040150b41c0c079200000070030f080d030b44210140d100c2022142581d40e030102c25050400c0c1002d59aa0721064100c2e40007040c856190340f6441d1031b07001e174182481240d0040800344000c11501c104080402c1c030458142c034002e406401c1c001000720395150100700c1e542c1d140c00290710420080c1e01040301b801c0184030601c0c80c58850040c8001094011200065800600590600705c03072a0500d16820052000545191560000802010340103100002e22420344554050b4400e1420 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 808896699 1250 808895449 808895459
    0x3090f0111121f06030b0f1207080c060a090512071a0d140103110112020c0d020307060507030605060d09030315030b0901060e131112061018050106120504030e090907 73
    0x1698401002100c0500020b040e40803074080000e840c204070b0b4440c0c1800a202d4a28601080c603c2000601d1544c000c9008c00342c510007081c0010307440c4103c5044174203840e0081c00b0202084000d100e5682e12000040d141c4000b40300034503110100e004200c880030308490019990710601222800c40400c0400503150108401d000c040550040c11008400c4000114640d070660351844103401c00c10395818100f01003585072041c03107900745d0704a400c0c02034440d040b41c02c2d01006003c004c1d6641d12044080760a41c0c18000482c214034083d00a900c02e4a10080401d414512043c11200c0181414001903041648403c003d0100008545284001e035001c0c94801d0400c0c030303140d0011400e5030170070740c0440f002d400500c04000f6000300c071514001c5401d906c103a40b65005811040040e2801400c40f908055500506080c001c1980c1030307400030743c2120b0001c161010100e20202e07105003107610034810640402c1c1485410002e0010070b9000d5a44984a030070003401400348c07130011410302c190803596000264405041442 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 808897949 1250 808896699 808896727
    0x501080303160e010f05210a090501110301030b19090b0c030603370f0c0b03041412070f06020d0c0e040b0307050609120f0303040510180b0c03090f0111 67
    0xd05180b60304181c1000805100028484115400d21008010000c9094290b42d64101d0010b000310752841e5500c4050700349815008005c1400382e00440b400d40c60700000041900d40710094904076030b001b40280700030303581e5100f024a101d403003502407501440d07075401c0c1070300010182c140c0c013402041100e00e8230392203141210a141c901141010414010802881c0c00c200340b80c12041d080d02d8141b882448004502424500180d000000c040010160250711030007081c9000154060b5100750302031100705840d0200311050710389811041506031003240c0204003000126071241d060800c5103103e01c0b4018079151210b04003074200c44038011400300041800404180318502802940c5d1038003411000350800c94039240002d00203114036200c16018424900c0c000c0724a210034400411821484815280c0e60b1600d45400b1351511420a50384803180d2500e5650f640e40c00d54982c01c603071034551040b014501c0d601c4030803010001d80c2008100403050303c6051000790401d2000e0145950b00161300520544400241031102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 808899199 1250 808897949 808897981
    0x60c06010f05011710140f1c17040f060516050610030302010f06140f0d120e090106050412020120070f0e06030f0d0806030111071401051503070905190501080303 71
    0x200005061100384031581017203041c3c001c11035526180940d044403060000c03510084101c40129444522032254240c01307008142000d089a210b0348149000780d50400390450075009602403010080540401440124054002850780610702ea00500880399940d0782c4501c3c100c0c0403251440d40c4400036101f00b00300340d0240a51140803511560038483e250800b90050441d1407481a0035200d00039101002c1c400d80c50b80d48503025655009440011200c2c1e44400103000003042c0413000307000d0052000000703880781c8100c080d1001ea84000f610801040142c2c2c004580300d6203441401400740421429885caa04070410115000705030b001d41340708a5500c0c01ca404803a403500101698025080001d907840204070114160b0b040a419040041c480d49800340868014107003003440210b02800020050140314021501e058540c0f5402e0007800140d0300c0c6a1007504000c41e1440c4107806601002c001c0c00094407980200744d00130340401e09214602458100f00b01540c40a0b4800e0000303401c0001400321019203c070f0301c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 808900449 1250 808899199 808899227
    0x90b0114041a031513061103040c120b06010315081c020120072d11040b010e0a090f180c030b100f0b09012f01060e04080711060c06010f0501 62
    0xb0000c000007800200303480314031599210889a5004c000950f090312400d004c90342490300203e04010001400c06441011303031007501d0680d002004041e00144041000c145400301c0f0ba48a0301c914a5620b80c10010340103441580e009425500c01d41d5004680003008014000d500d07009401d010071007145c00b00f0040d08440803072001101911114914040303001c0e08404603545070b503001203014250000e407004108124000c284000401140029041c01e00001c0500700f40f0041e0101c8007000b004007841c0054801002c00200d2541015166400300883c8445a02c00100424242c00205d40c01c102d5441c00c2c002000301401c1210360b0100307a0014404d03c194014101d41c000403888a45803000d040c0240340d0041241c0784107071210004001a0403030641d00c9103800c00e0007000e189110540d00c03c0342c9003100c035080b12071007a05e2856620340100042c080700620f51460049402081c0b20340780c8221038691500c1c41d01110022030b0041401c1008011200040104500030030300d6604a001007030408000502c0c0b40c88400344 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 808901699 1250 808900449 808900481
    0x109050a0b03070503061201050c040e0a180213060506130807050a060507020d0c1d01080d050717180d050a12170a0902220501080d0f21090b011404 65
    0x1030000e04080c01c2125048401e904140c2e88aa844c4000600000a012a82c2805509110074402b01c5000c00e00600700b03441c980d40070100c5035641c2180748400c0f074105840c02180b641c460f030040405030610041d20003800c40e442d00086a56512080812000c0d071019a19454403080780304100010203003400440050082111f9404015180c02e000030094010201c000c0d01c070b1804080b040041101d4082440010f248015030002016207a82ca800f1042000348034242542c0a1141280741c990b2240c011507600b0f90740194440d610890340540182190811043c00c6001c9039003001600304d0303545112a00041912442c020144044c03640f825405001c2081c000030244104d040f08240640c150080e4a940031021040004180c009400040c034520790301e1300c0007044142c034108450b9504007103801041c161005d620031a108407500d178200311000210f02c001c08000400066a085118428800c201050003042c0030101b414400c030b0300d0340601d04100f07034802c114aa64814406d140d50070f00740109000c600b0f00c650 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 808902949 1250 808901699 808901719
    0xe0604180203100513150f0515030304090207060e060c0705010c0e0a09020a0c0209090c031606080403051305032b0903080301120f0b04030906110f0c0103023006010905 74
    0x70100c0e81d100e1141c16050146a02d980000380081080c000d000034440d04044200c03140c1205150410040c41310307001422030613003400c00044180c40c80107420341c44801c4c00380c021072500345020107080c000c0d00030781001c98145860350910b540e00081040098000c3c40058641551035240b46030503421038400300e407542c061000758428551590340780c40804c030443c0e44440300035a441e40340740c0301191a8545954000e501001031810300005480025031461044400e81c00c613070380545082c10381f180c0700d117003480f5000002c0c40ca100010300107031040c00030b4802c11241480000c0c805403600002414a803c0014036241120031400260240603c0082210910014241221040c0c10b54a4003c2c413448140a68804d00b00d07064204420000d040d1210044203402c47c2015100e0308003031400601400341d611840700001c5940301c3c030b8000c1d451b0100d05100c08040b0400100000b03800d420054000c2d4200200360148a80134030000c4400348824141c2c03052040383c1d455003030320380d107001000546018110b4201c14018000c1c18 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 808904199 1250 808902949 808902953
    0x504051e04050c1917070c05010207050a0305040807050a21020109030804270b0102071e090204120b010b12070e01090801050403020601081603020307030f06020f0a0309110906091504150e060418 85
    0x101e000e8200d1b84529000c400c440d0b0a003445c90192090f8a0018000e202d020b0001c01030540c00307400b80095a040c1c0c41500c605694030010008800c54501070010251000910120760804044c1401c0c0c0031423060400c0340c0c0013542c0ea00c1e0511150040e90201406020038410040440031141d50343c07128050095042068061141c0001e5840390103001c3c0c8064a807040c15203800c0d008031000500014640302106541e82c50b103039204079103c0354121a084607002001c1d0003f045000c2d03240182d8000103000402402340d655040c804a619a200baa142d42c10300c6102500071411903000e0007900c2c8558060b400030801549400d0038a880e20340c0030500d40a245220301d106000581d00820940c1c2100d4200708402d200c06400c6c18008000c3c030811303241181d00742c03001840400c0240c00d6003110280381d0213000c0114000c0c40304002d12104070700880310310750f004030504c0001c1d20005941000420f401ca010f000010311170341002c0325400c1d00303c19400c524810b001240400000b0324145c01540c06c0c4402c640f0400941948503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 808905449 1250 808904199 808904237
    0x305060a030812101e08010e21090103110304061515090605030a0b030a0b011802030112140a12030e120c0715030905060403210605010504051e04050c19 67
    0x150541d07100303c040c4200812003c940012552001d48824440c810034111502ca403040f1400451041d89559400c00400f4100301e81b000c1119811240c50f00d03024041c00c0010001d144550380300405041c1450340d691425000c110500003e18800c602c55200020b20002c1c6000740c05140c042070340314030311060f5640c04205000c9d600403c0201200d009060060b200d482e540542c0001d0826013080d03c4d0144035910540060040d034079180d0b0304841360041001d80c4c42c0c045a20340c0090384002d010742c0c150f028801c0d0f910300000380c20001c4a140079a0038815101b03204480d40c0c0303491900500b40c5c12000080d44540040c8610a424080c00440d0311440c25041d00d44402c091400e519600f440c4610340e980101c8042211001c0d000303801403240e01d940f18040c0c074004e10b407030300e400f82c00342141036100310341001e2505056041c0391642c440c54003a110141c540320308051a1034200201c0380002150303050340142507000d016240d1114080e16010780070750403c45803103030002c40d65070100da68440c00200420680101c081510421 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 808906699 1250 808905449 808905457
    0x120903011b1b03030902030d02210304120f050702130204050a0b0c0a020d14070603060906080312010e070309020909030a1b030c0b0a02210601391406090a030305060a0308 75
    0x2901c001070700541007508041e03005002e0f070540031f0b406000e00510540c80503808a40c1c2685102c1c3c58039850705402d0f003601c0d111220f00046070010900c0e0070752030301003444500910f100400d4292903d003040c50408140d02240184803608000ba03c1340380c01042c10320680c545030300098064101001e4107070400c60503001c0b0a80d10001c160002e030084c001c100300b60046c0141a02c2a40450890800701c0b040e8503035480c00113000300032070300c60800214508032020610300c501100b210100103a440000c620343e400c10804a10b5100040d01c11341c01d041c0c0c0e400d03140b40140c4444152a1007003d10b000616141e849015001e0712000200544401d281c0c10f030500440003035000410204c0003500a185600d1590380c1c510380b000240715182c0c05504052501d08094281007000455030b201c3c50081e682d1010402003100f042c401000130400540b80c41030a000c2c1d00c00c41d0b440d07012102902d107004101d8096030f00c100845590800c4416254171800390840c40d0600103158040c007031070ba0440030581e03007644a185141c541e0140c1d801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 808907949 1250 808906699 808906727
    0x902090c16140714060405010206342f030703030b1516110901140f040f05010b0406080903030c030601030911120f060f0f130305040305120903011b 65
    0x1408030301840c0041018005180340d95101c48150303101010b400d0300560300d012034070550400b00203901d4004d6560500d070342980d04a48060300205144e0300d03008042c1382c3c8070001140420085280c101c1030034400e20340c950690310885140d205e803020050a9590502012812181402c170150074060008942000104507030104d50145000500394580b580001c800900b0303503d0703240001c1d02c00b00c1c00c62680036121030080c6080e8800e0a4558880340940140a51540d00b445084003108051542d0380040c20000115213040380020300c0003038240b6a8011881c100c2e8805e802c00340e20903070702007000e00280c2d0f0000245074001002100035030035890b007103031840b005200082c01d150405841d01d4461080152500031700428610090102d005400790000320350b40c403a26191034060500c0341c080420016240c14401f540180d030191a400c100c0d035180d05d4810007400c042031048040200c2008000301045041c081200381c000035051040d40c94011604042c00e50b0305030440306651075031040c1c2c0c002c200345d00318024100c120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 808909199 1250 808907949 808907971
    0x21b01050c0a11070509012606060105041e090204030308092b0e0105070c06030c0e0d0b0105060702031c0804020a060e0306071112030c090907140403080310150c030206060301090209 80
    0x51100143c1d03810701a0710f5000355001001c001c00840c1240d03018400b04460083e40c030b40c20741e0720040c0b51100b44d039030b00c020b076291408240308200c1401454805417003440c02d0110388000b200000ea85051480803a8010b81c001c1c2d0004034110140301c2c0e094410301c4000c5000c1c2450101c081d405c4800004401c21550196046090060100d034070031042c0d0040c0190b60b013440d00a601120f01d10b66540015029100301000000042d040c10b180c00300501e004184100695088403140c81c26038200018449150321420041c0e901d446440d0300c00c00351035101d52101c41022915690000d0904141c07040c01442c5150707401c0030090001440ca8012561000243c042d070150780361903d0710000da25994081c0c100466000c80803888140001040715400211004118219082c0c540302c009a0390400121042c002c1c0c000c05100e81d1074104000c0002c541120003131a08031414403c00000d00341e4405510501005045811010035220340c04941856014003845074010340540080c404250164009403513110014030f00241c503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 808910449 1250 808909199 808909217
    0x2070315050a0609020c0c010818031806090a031101230901030c12090f0b01090203060a03060f1503140105150d17120c070b1605160203010b1003021b01050c0a 70
    0x1010140e00f002c0d0080040c1c4204558624404940507112101c5070340040c04240c3c2c0c5800700714918494400c0c1c15804ca80840918249094900005000c80f100040e00707a0000090101001139981d81614200440c0b0410498120096410000d004c40e0000c01c3c0300540c02842910003421401c1c0e140444200342001d1900181d90b640c0510142d4200300000004030010746408070050801015000c6c0ca01850b004410b4468680c0c3d0313411282c41607120840300c1c10303000200355108100195054001c0000c61a00080100d1b544200c07140c0614100207070740c415101c0c2c07000c01148239803852082c172440d60070040c0314a030040c1040203c40400c00e43c94003100005c1808641c100d02411901e00801941e4406194400d00401401d14448039003060300007210070b0712000d0109011440e03c0120309626140c48400d42c0701e06040107413410002c2980980321100340e07090754070b4000c142a1076503490076201c4414516280180c0311280c000d034011581c24101c4c104e6200740e15180520003003082d22801d49005400134a410304003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 808911699 1250 808910449 808910461
    0x11090601120501060518040b0307030b04080c0d0e19060206070c05071d0106120b010c02040209060702030f0607111914071707060f02011401090e0109050f06040308070207031505 78
    0x1400110710300000016241500125001e81e00c04c00a0081d0403041d900340f10345408084c10041251f006030840355050707222910420001305000051a070250040918608000b2649038050810400c20018400a501c5210783c800c3c0e45084101ca14501400701e401e02c0206003031101c047c0da00c20b07000d4450024005400c08441c2004020400750340500054001e8001c48143d0030f0100a01820a01a900c0442d10315030101c840f1102500c61103054a00503510400100161b800b030100a60124850740e402c44d00800c403010150310204005041500d500000708001d1421040c000c3c8844108055010242c008034002000c800c015425020319903041140040102000a162850515241c0c0300e58401c2110180c40c80c00c0c000041201350407900c003a00c9195103841007101c200d00f212040b0101c0e0706074500d090300500442a0b154440a030459441c0c00000365031020742c0b0703000d16250341c043c100f060130341c0120204000c142d84400300320707000807a6000400c2c425007150f9440103207103481d482c940d041e29501c000080b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 808912949 1250 808911699 808911707
    0x6092f011116030b060f030a0c0b0a1b03020a060e07050d02040f060f080319090e19061a1305040e0d0c03020a0b0403020312060a060504030212071d0a0e010911090601 73
    0x310000750b4100400410341e480c81c003102007a00840c0c409204603c04207400d481820b021481181e82c42e4031500310507081d82000d0300c1c0d04068002413030103020400c1a000d0520441c0d4500240c03c0c50502035002090039001503c0d01c081551100700c034104280e00110810401d9445001140503140da04440106462043c3c1035044010110b43c1c0c010f030600305400c040024001c00100061544910204103d08144201705055410000714172822000009500004030000b101c11040c03041286144004200d65580b061000d4004040c03505c2c40000038070008100680700082c03010f038001800140e0b070a1140b070320322144168680c02c981e5088801d012100300000304040c424450f00207140e40c4040801c04a042c2424025500c0e04a40204d83c414110f460108810b880c288908108940c2d03140d0703440b480d1500f10b500f8801180c06407045200207104110011468100500300e901e036103030070783e00e8030851460942182d4042c1c80d181007840c411645000800f4020403040c58174110600c0064500840a49680b0b004031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 808914199 1250 808912949 808912963
    0x6140712082e121509081210050d02240d02040914130b15181503061005040e030c030f0903060a0902011b0201020c151b06090a23030706092f0111 64
    0x100f49170041102c1040218405007915440710f0440807915555482c4401226100d4061251f00065803a4035400502d0a5070180b00350800880b1495441a0300b94001c01554000300206040703240c000ca001e02691150f4030032042c0703050002c100c070041c0f0300300703200314070080c0d0350342200034107034584490000f4003648000d2031110b0f010382c0180030b5649400c2003581e8142c07000c0003602c0014901c042e01c1d001c048503140010741036001c0c038000c06810712802d180c2802c1100911b80400c480e11107000a10580d8207039070041c006042c1400d10038001c10350350b81c400301c1010700700040100304826082c90045c020016036400301c1a508564070041e2004a100100d000503841c00d800d0600c425804803160b2100c4080712202c101400b2050506501099005000510107464920445144505030302407510100403814410760000610300016040401641e5080d825040d680400300c00e558880d11404c42c1001c01c14121210100382443c0b0f065840110880c140740d40b03041c1a6100780714100140d802c4450101c0e4001d010360 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 808915449 1250 808914199 808914233
    0x330309020a0308040e0a05010e100b0a110604054806090303070f05101a06071406040b0f010501030e100c0504050a0e04020405010509070906140712082e12 68
    0x1d5144c07580c0b85484030080c00200c500006aa080ca8000520b50000e0704103180188066001440c4903824a51b1006090b04442045010020000b142e0032014006001181c002c0b40501c01824031029114606414081741d008841c101d400200d0307005400658001c0e0080c05510074800707c820016807103000a981c0d00850300b0300e80c0d03d40000500038003005140000c001c4958820001d807006a0b520b826410200c68040f020b0303110008010f40741d50080d05e012001000355902c1a28980151030100303001c68a0028115401c840381d44200042c07001d003c8203650402c2c0106404d203004c0c00021003200109441b216050f12520005071240601540c6c640210190380140c03001401c012121a40c13410030510070351081d1410382c002c52412001207034034204106014030802d240c1d141c141d40c292402004480ea2140101110900403060100f4000140d11381504054032500b0742c0c0e00784840c00c1c43e000710f21a1b2000c060034400350401e400c05858904003200400000c03510f003900d480c00303207031200d00740f40c0301900128540f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 808916699 1250 808915449 808915463
    0x1203041a01150314060604271d0f070b0a0c030210151406030705030103020904210c030810081c02031c02120106031a06030414010510330309020a03 65
    0x46a41c0030b1011454034007220396941804803400808100c0076805056600c2504204200300034015096440500d06030b080600d00c0310340b105034034021050200c0d1007200d1510001c61065010b089542c808004c0012401c8042000d4411540740441d64400c1d0301c548070300390301400410340102060500900400c07081482a80040c802c44100241c43c81e0800c01c40e0040d002e4450324400c4440f001d06161017600d10403190b41d19060701e185d0964081045500004008581c0000b48903030104040d0a401d10706065450076403120f040d0300d204c0d880c000d00203500007003151542c208454801c21080900081031901c64603500405080d800c04540102e0461007050038a0032020f001074070203c044a04e55004040d1115412141002640c8896084003507691510808180e220b0580e600712441c60700900850300544103d028801c00c4520100180c01d51704120b4407050480f001c08001c03c881c000c0d1002c3c40251500340310301d4000c8095400801e507464008940c41c2420140d81c0ca003444219252070844074061900566 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 808917949 1250 808916699 808916701
    0xc0905120c190f090605060706270606030209090a0b071b0813060306060f020d050a0c140a03030605041401140a0f090501050f0406060c0b0a1d060405010c020a02031203041a 76
    0x811002410918416400701200e80c500014480009200b00400e51b000213003850728001060b00c41002504514a2540e00388171000106403080a582d000440024030640c0081001c41c6140100b00c080d02c0003c01b00d45140d008889002c000490524401d07502547c54200040944014100c0c02000682c07107000400d402c10020381000042d0815950303504440c02682d003400015115002110202603001089000d40d014403d5010345c94000c00c09410054903520f0000320780d111907100c5000b81000781d444180b06411291582e001e159250041c00060b000c2503500b808182e102c01680c40b191201413184888441c2e505c401103030306a4542603d0700017444151303035a009058507010000020a000c0c400c0510031201440810710b241001e003ea201101c2c80c68031030108481c815203841b000c14000910000419580b0501401c41c003d84504142211a500004060303c0c5060b26182e42110043d4514505543c40080040700503540000e5a041d07903211840c0706038070b0b903c0c1e91900c160400f084440100540c1040b02c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 808919199 1250 808917949 808917979
    0x50a180f0806040501060501170f0a02191e020d0c020d1112100b030a0201050f0d09120203070c0909080f1e12040510270203120f09010809010c0905120c 67
    0x182c0b5030045020714002c0254a94a4006513410b542a8031980128040c1800141020444414240e48508500005450141c6075014004050094518903000c501d0f64845005400203c440d818445502030004040001d00802c000e8002d074401e040003882968000d07141400c110040204040c00403010b441c1058051216100303980340d483d013014031404036182c408040d466180000d03c0341c00040d010703141c40d85400e44525841c80d59a02030010401c5c030f03e4407805420001003060100b03200c2c840e8254003464a44101d80381a4400045551202e0243c50500600601103000941169500860390451a42d200b80d480703c041640186107c04513014500030510350752041548840503c10340c403a10070ba60fa140b0107481681d00302c0710310380640312141d2281942d80c500403d8004841401c0d13030009040360724602c00c0f20441d1405030f000c02c1740701c04014808a8842c0c0d403541c02804954114100400034803144040210080c4040403501c11607106541c00c3ca2000903240090003d103803a00f03805005a01c0c100c000d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 808920449 1250 808919199 808919203
    0x3060515041e051c2a090f020301031502090d08130e1e040b0601050904060906050f06040e0a090204090816050f010b092e1401021c050a180f08 63
    0x901c00c60a4041030000d481c581d038000a40301d0029100018061000c02c41a28101050b5240b080c1c070440d8401c448005e081c01040320740038603043c0003422464210a450610704150142d41e80300d02040f11990040c40148000380c80b00f500301e494000a01d00c010b0f03d1700442000511049001c00740904440030003d0180d202e82e02d40c1450308242d410140c802c59082c1c4455001c010041306080f24002c0740046800440c00290f40c20a007141c020405151060600000701e000801f1911a94001c804407551202c2c00c0001c2e041014150000c80c0c0c08a42c00d509141c40c002c84000e101a00501007900240c3d60b915000442d660380d80f04014a58000d5021034855041d500c0364419030b69419002d503014400c102c8000c81441c1305014107014600302a00000250702d0720307070078900701d00e80c01205050001d250549500403017910451b804020484c0c0e0050b83c904444240019041061180c03a030400d0614219180c3c45d00c60b08a002c0742c904c8240340c6803031540244150060411503945801c00c121809001000080900340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 808921699 1250 808920449 808920457
    0x1205030405011b1e02011e09080c0307050918120a0503040614010f06080a02070227011e0b1813090b090d020c1e04060308120907081c03060515 63
    0x10a80325049601e1043c3e50160707000005001c018000006407055880440210b0000c00c1801d05c181000f50801c2c8240039212840451040160b000420504041002400c2000300c8503c00905402070540700d410b20707000c0381091030300505048aa4040510381d076103150040010701044111121441d4584520010080403603000383c0d0141c07102400d1810070380900800d00001030407100c00c0d440d0361602c1403400005440303040c0003c0402c40d91079800d000600251300c2c0c0c04400710440e509180340241610358503a2a40c20f110068000c885610172800319031000c00446070246c003e45000c00d00c1c0c1521014201c8280d200c1480d05620150004d01c00506000246902d8000b542e07901d00c074140d250039540d1290703000c642c0c0c0c6840c1554a001640048046032607428141204191004c5070026090841009804582a2800c1d0b62040f15011800501c4442200314a4003c58010002d6406813080c54034194030b480d07407080004001c0c4c000c40c540000c05090b80b802503200c03200401001c0c1c0040e010f010784220180d19500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 808922949 1250 808921699 808921709
    0x3050a020d03060f1206020708040e0412050f03012121020f0a08040b03060d0605010602030a110118020603060a030501050a020c12030702060f13061a130b01051b030412050304 77
    0x1080260034804a4040d00442050b42e44d890f01d1240788929140441c05900805242645c14136420072898003c42c00800041001d01036924114480b03080500e8481c18076a542c842040c1000410300c20310384c04259502c1243d04451104051191600c551811711600c2c04560380001c0c00c0500c145501070721004409065613a151140d000d9800030348002444d0368a80c0b062a5000f4a00b010410040c0513a200c4d100c007458022030050309080d80c6480741d0303aa0804a407000e030070200259001068403e4650391000325010911040c44c02442116a01d00640f200c510105000910034800400083d115403100c645102c02036410034001e1006040010002c802984981000100c900651095000c0341c04c000c1c04a80c01150705030b00600480d62450000101c480d405032103503a01c41070001034100460114040c5544101080d404811102101010400014a442c00f000029802e00000c25490380c0c228081c3d44412005038800c505001110036200d080d882590009050200700b03500c01001d01c0400000780c41910 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 808924199 1250 808922949 808922953
    0xa0609030e01050903070932010509180a0222140f06061315020c1807090e070906030902060c0a0c0305011505090a0905100524040207080f220303050a02 67
    0xc0ca0440110703003511804d80150341650020400308000a159404a248821401042d242d0110580c0e44010078042d42901c42d000031055070014407480c94840112608544400ca40b1810540b00303080c0c0341c0d1108072040e0060b00c02d030081c4c030a00c4025000314034507480c00d128011040001180e000440c440881081d9410b078806050940010307440d00303104080340d101d204880d0518030030500d000005454822809400011401004806000c0d511819034030708200c40c41d888414201d15000702c004101051613030101c00c000c2503039014040002c1d003204004007039884a00d00842c40340010b001142052184c1d042040c410f1041591358002c1c004804803d4003a81d11400c0240300402c0e96441401000b1014003500d58851141030114904c500a5485011050b100d082900c05540003020031808940d0700315842d0312440318180107000c10a0202e610071120182c202c0342103003031400a45846680703005440d0816480400060094018101c201d40740e1000105154210540c1c0c0c0c42c2e15000b0000c0d007003495405c0141c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 808925449 1250 808924199 808924217
    0xf09030b191a09130812010b03010608060409030e010f0c0804080a051605010f1b0b070906030e06010815040f0605091501151e090503070f05030f19080703110a060903 73
    0x840b192202c203011800240b0107080c0c0e403241c10341032202e02641c14040301da0800c00c0040810424151140a000300a255a52a16503142685c060414240102030305d201d43c1c904900e140010341c110000400d11003088c070f0403013140280150142c56000140c81c01514610011400048003180041d15198851142080d6503004a00c43c856030824000d03401000e001c5110040c0c044200d03481207442040441d4180707183d20f0880700765201c1c0007407108203840320000038812000c2408200d402d40106000540d50800a000302d41c5408a441d48500320039071a40401111039000c07405025418199020b025005001004907082c6540625070b83d201031600c0c3c58035100c41c0340c00000d480e03900542e055448221511405800607003148904003009800d4029024003102c4000441c0703a8804014860140c00e0302c8004a412500706410185803c04640c001c010316800272041040b50190460141c0c6240c1e4409071035501c1d00d00c41d240c1554605000f041605c5640715000405090000c91b400202625029884012032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 808926699 1250 808925449 808925471
    0x18022a010b0604031106091309030c0b06240a030b10030213051c0b061201060305031315020319020a0206120a0605030c28030803010b04171605010f09030b19 69
    0xb050080384805800c6442d581031144903414440000c008031403006104900d4202401240002c03191490070980c000b8006040341001c00208603002504210300300c1301e124110003450450341030b2554002d011804554080307801740500340207401201040380014610094003910140c010300940281040e1a1929040700300002d040c00e0140050204820a41c0e00c41c0d1502c0040e254440300b0300740500016005030070304a25410095080c46070401551081c0e01456a800d46400c62081100558214803c00003805d084221010b030000100d03414002d22410079024800c85407016400d04040d254042c3d0840c10001e190f1171000d42d8200160700c01c500f50481001000c1d11982815610680058220341014941031825500b40c0c902d85d00c0c81c0c841406203803400b2241e4a0f565444a90741080e4080c00c207500021034144540c00410b0040d03400750441000810b11044c04216540c007411041c80b6403030603c18070b0000680010300c15012000a1074003c07105a0a90500b46201070b107500d41ca0300341080a902c0c1c207840c941 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 808927949 1250 808926699 808926709
    0x80f07090225110613061103090d03121103010e010501031a0102190503070210031d01050705030601110118031805010203120a0c0c0605040302060103200a18022a010b 73
    0x1802100345120303140104020544008061211034003511290004a100b510a59900700100724000c3c01084508004e480c046c4080d220215020744a022600b040c4440200754a40440c000d61250b05860542c07501e1b000ca00c0340e40000d11640701412200c840010012411480c6148668121142a0307010000140d04001154101350107400950051700640340d03184d031008a80004030360680c0141c003a24a0031a90350300080c2614240e82000011036180c0b0a200c1d90398a6003100c40a81800d090001d2100e8038000b0001045440028062410720405840c4a038608000b5403284070300c176410455800300b1603060b080c007820409840c01940e0038805494000b10b207552002c0140c2c0e500c001180da101c182500c0f030310100400343c0304002d030240c20400040e0404020403a2401541e01440c02900940010350440c105024950700c4104180010441c0104400b482c4e181c1c010460112080600074481445240b141600641709200240c000031583d22007442080349900c20b50419001d56400030400700b0384d0001401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 808929199 1250 808927949 808927957
    0x30f020a0608100e1905090a0212120706050709170a0b0919120311030a090b1005030a320102040906080601120b0403020a02090a020c010c08060a260304080f070902 72
    0xb01e00f460b00c2410411501d03158044650b0002c40b80100e01002000c0c0d42d161008451048483e903a155000b440700b2025414640000d145602d07500000d480c0c0110a508248010301c2510b0008103200d64407400640802c1c446d800c5900030304180c10000c1c40c8064950442c0e41c1d101c0701c00e1000c0c1d074030544a002043c10540002228580c6210143c118400d280003512030b081408161601001855198a0006010f41049009600c20a01c03a0380000d200300080c204400d10b0b85000300f1903099007074039190074081c03598001406aa66a8011102420310b115100940d402a155880b401c1c442c020300c030f00d07244000406402600a852034a1020440c00390381c2d10361a40d950b07500b803141a0100c401a01403d0101d0007207030030154068024011140f001c0e0250b0302103240d41c18200c4413170b100d150780850a911080000e0041c500e150f01c440c80e0402d43c1c1d0804100185000c2060301c0340c0000040081d4100303400c045d0700c062614810109509807601c0ea0317540d280098440d20301d00b0341c40c2028018610003140307180301c5200366 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 808930449 1250 808929199 808929211
    0xc030b0a05131517070f05010905210d05121501080f04031e09031b030201090b1e030f0610050c0714031c1806030e03091513030f020a0608 61
    0x2081141c580000c0c04030400c001055010120784a4031611401000c0e000042c00400e03160b02e00312140301c2c000c40c4850804c500c503004140c01d400088010402603a01400e202c059400895182c504403081d01140f48074920a449402c00d14094183c03032150181d0084050210004010310261b142e65401c5050b05d1512a080102800320300d820740865490590000d1142e4810722034102900500ea010390486045004880428001080340405104004040241400c0030240c80c0b6501c13f11401c550000e0b00e0029030703009000070210081030034080c0c4c011850070302580c000040b124646e070f800c11300031182c2400802c54609000300c3c10900104001c502c42d4007103504101d0408082d01c60780f4103001080402074a03500703079164188030712502c03811071901804c50710000c0812503c1d448014003100b1044a50f4803042e078040414140782607512010f5103808000c807550000d08858000300181c0c95800404240201c038000b1980b040708600100801c208040002c21140c0200c03125544595900c0003103507030310421510 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 808931699 1250 808930449 808930459
    0x33050a05030118080903031215040c02010b01020a14190b010e010b0705030f093d0e0d0b070c0b01030b01211e031407050c091b120601090f09020a030c030b 68
    0x486000c5080c076130191804210040640e86030101180c00d40c2500c0c50141c4080c540000c0903407400019180a1041c00001000b0b40000d1281d1589500081d40b205000300001d4000080391800c9110210b091000c15980a88020300814690060824a211400c240222640714150714008202c12a8403815500c440350301078011450040d04488200c2c6070780110074010341200300309003000340e200c1b4003203190700f071142e080c541240c50156600702650101540039011003d00295101c24200c0c1d899000d520000340b6040050b002103074641000c00c640a26243c440a403100c5031100021080048502d042412500b031030035452061160031094210710f0004010090820700c94030000b402d488901c892259010b8000c0c200041459040400680a6031001d0300032517054000700703084061468185403441d00005c41400c50f1103c4c8408801d501030608c2044100c0da046488000001c62a030b1240e0589c0015085441c0b140c42503e81d1007250401940004031030401103410000b044841c50311a219140c2c420100400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 808932949 1250 808931699 808931741
    0x1f060c02040c030b1e060d0203010312021c0f11030405040203090d02073002180a0f06150f051e2701030509030901030b01110607020606030610081033050a050301 71
    0x3901042c904085d403030260300b010b028084003003580303550700c0503600840c00341c628092580c880c8203009007003030406600880c07910002c0750401c60580d404050b400180340c00e410000c101c030746510b00c1b02d03241d80141c1d440303560310500020400001c0900400c4510003421a9000c0315912034a5401e000f410303000c041070364403417080c40c000307070300120806507441480a600250004c180b1600320800900040350031107405c03c107141c4034a4100d40e4019180b10706001458568030000b003054540c000240000035510548042000120328a50380c5414024840000400c19050766900c8080612410601944940c00c40480b450042c0080c0c03154080c1c090948114001c401031803900000c00015001403401858450412444480140c2c9008041154034040c00741a001800380e4a4500201458944000e20f5207007500c203000b4041040da50001760000f100201c85e00c02041c10724003030011001d020350240151928035103081501c80210302000b040c00c00e486094074030003100d0751270707005043c242c4a80d02584a26034034600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 808934199 1250 808932949 808932979
    0x3030c03060418050a060617060f0609041a0709030308070f170a090b0f090d020f0d03180827010908030f0915030103050106051f171f060c02040c030b 66
    0x30f031003251103208460841141520944580d0316150b46614212100e0782d64607001d1041090b555099482d0300295001807086142c4050340b19034080c1c01900103805910b04a010904002d600342c445060500e0302c108441c042d00c0c040c44003d02d1030300c0b0b51205402289400c4085a82e02c0d100391603100322510030741c403550200026000ca58030704e03c00003445c440d00a40c2d14443c0c40000384589841c180100d9040c48030f00800e00301891014100740c440f80c2141d003590701c0454440b000b07500114091490791094100002c0000301100c0c041202150100c0007042c400000071000c1018254003406100c0e0903822802c0c4003000b08200054031900358034001c40305d107a8410310440c3c4688400340300400d02c41c200600410840654021040c0c0b280c2c00a82040302c1d01e035120603060090b41494141c2d030300503501000c400300e8950104400030300840c0c0d69020b6070460040c058001500b44010322503c08501800070700c0c03444d5080c2d5400c40281200c1902c04100d100d14103007460315698038402e01908125030f40061501d580b00d8602c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 808935449 1250 808934199 808934201
    0x30a0804030203040b07050a060b03072303120a0c110f180c0c031207031103160806030f03190207050a0602070611010906060b031e1603020f0c07060507020a060203030c030604 77
    0x203004400310302c003c01c000300d041e0320010042c0054502c10780040000d400149026002e40d90340c02200c074001e901c1030904004000024800c0c210001c00c60a0166102103290042070502100c095500b48001d00021860000380c2e21000d0300d82c205000741030200310110058200300b000c42d404d4402035071041c24410712900d2610400d00d000d802225460310580b03080004d052007411500132008011b25110640100000f440e09030103500071180740e00402610b9481c00c82040b0007420349001d9407a04002080c40044e440340c404100c0180d040711041c044a403903459440728046898242844a4014018000000341b2400d10a030200180c4005801525082d070410f041120752003001d0b00c0c0390040350340716010180895158400d40c0c0c003800d00940031664a140080300d0803000c0e491084806c0d004407060040040d88501400b240c00d0080d428030b80966191041174490040d80500000034003580600c540002d211a0040f00a00d0132500c295800180d45a4808082c1c1e143c1c042102e0802e2803090400001d0280d11b02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 808936699 1250 808935449 808935451
    0x9090a03081f0e0a090317040302122a011b0201110406030c091e06031b020606060d020705011401031a0907031203094b0f05010204030f0303020319060305030a08 71
    0x955800b01d941a075905032070000400d00303030b854800040e50762004609042d400345501d90b983e25120001007082c01c055a000307503540b003c5800b024844401203000c0c0134100884000b00310403500402c802c1509044242c000d0b0007049440400940840c002c00080843c40c018007c0d5401c0f030111701041420946410019805400d210311000e00b0012403040c007052100e41d01c0c180740312500c842c0801c1907075503040030405400c8400b143c10009020117860310103a402a07002505a51054003585c8141e00ca13648502800082d010f00d0724020529400d0108401100001c0001075040300c1c0910358054a401d0b1010010035100c50a440104d0b65400040e01440450080e4500070104420362400090701d409580310301c40300c0505000b00c3c1d000e02403110044c401d04148101e80b8a400c450900380b0a540c0c84419001c5200036910b440700811907051544a102401029415200110b0304101075401320300081c98024021340c02114403407a41c0001440070003000c1e810313100c4e0070b00b030f41e40c1319009503d03001d017044041d03c440c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 808937949 1250 808936699 808936741
    0x60b12070201090213062907140304080a050a0204050a02090a03030302030c09040606020a02360a0207060905072c06010503040c081f11130605300609090a0308 70
    0x24940301c03e030b001a01c5004007619807942281000442604040714103009110741c1403031030350a000d04201d108800044000b00c81c4100e5010301d841c108000285e92a82c11400f944d07010080358018220f10781d00780880450345c000424800c9500b0003540d0340302c0040f10100d00034941541c0c0c00c61302d100c1007400000e0107903000310f8102003030740205800c0881c2140041d042d00c6e81600400e005820418007042103040103094502842c2d0386814860000e4a11400d2074000300c2c0c1d51840d08405a180408500030320700c0ba0741117802641d00420140405061801c0c0b040d6104818894666100401146400b80c50340c8054410782e00d0450f68900c4c0043d4840c0c4004483c1c9800c054015034004040b48800900c02a0810040c880c50b050220524402d41c04082c2e140c080b136006000d8254000d004020562000380e42c82100790940340c0da8100a40c6800c005008110840020070440c0d02d2102020404c084e000a0b00000d644034000132a400748080ea940b903005074aa601400c40103010503003c2c004245101040400652004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 808939199 1250 808937949 808937951
    0xf070b131502011e1a031203070c03090305010e0715020304050102070b030c21160c121b2f01031506030e0f120310050a06020c04110f0304030908010b0301060b12070201 74
    0x124411101d40090360b0320000000100d684102c9026500080d840c1e040010130220041d00d024851f80400e0226031200400c2041045440e81c034040c01c00d07000d1282d0340003454001000b0800a12800182039403450a4001d0203140304c1d24400c3c070401c02d44000222000d454040e4007400e0150300e0001108001e404c003501480e1051028821000380c810000414804050484050300c1c040c00c09103002130355031071800184410080512034900200d00d092401c805000300c58580424081e4050f41d80d0f9000e0030034010010065403542c0750030f0b52460028003504036902180c0c0040c0c0352408a900c01542107801095844010940e004403c01086000e6800118068201010381c2d0041c054911690304000342c0c4003070341d0641c12000c8240700c1c0110300d00b10311002425059540035209800c168019544441c6848103070700c2540c948a64038007222420007911030320400c2801082e00c03410280740280c8040d19a000700c000541c60075031151660316050181000b2100c03141c100030300d07015030070301485114140100319000399 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 808940449 1250 808939199 808939211
    0x506010f320f041b090b0c06040b0603010e030a0c02010f050307120b04020c0307080409140105220b0d030f0206091b01030902030a02091f1202100e0a08030c0f070b13150201 76
    0x540f914040d00d50716101e071607500701d0302520024005d01003c0c126000172000407000e00c10a01940300000d201d50b041600082c0700081e558a03000024050a15a00207023014040464000049900540685001c5200f40c0380d034040721001480441c0c65000850714880043c12110030010000c3d441e500906040070040e02c0980380a07012101d513032461b4440c4100f1900c21100203401c1201145078800d0728808600302010f070450b0f5240200048098520615110000200203040040f60029902610078100041d01c04512000d981c2006044403101d10205070240c041c007800500404008680b04070146803560700340ca21022034000450041903000012a0144216941000543e50b048152441080d510301001da0740c12080b45602c088414560190a01c064000d0a040041e40c2d4064549010390a038540901d541c1e4043c000216030311070b190301c1f000c06c0d401300046038980c0e64000314200800c028804210b4102c00d95503200103900b846070072400080040098818410001c20003c01129100140300101e80303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 808941699 1250 808940449 808940479
    0x2010c060e1c0221090a0308030c19030c0215070f050f0d110c280b0c1215030c01091508180304090c08220204020906160506010f32 58
    0x81d030007060440c40e015134003221138a190b002d43c49030003000c0c01560802c1d1508140c03100c03000c03540d10441400028032212010000820700c600840a45d40c02111144062041c5d044805028004024a0b2000c0c0014003407404001d2006489001440c010007950341c0e00522035a19130012102034001da5003107604c0742010003e4080f0b010079802203400c05400629141c0d0f441010303005007858007458074103104452a03c034140002886030710003e00482600020300160660316403001068510031780d4404010101c6110034002c0c50714a0101c0c209800d2802d070220380d001d00301c031070043d0350f41c540d0391148003130b42417140b80e1188071940715090341034010b00016002099008000c032000c0c02d6170019041411180e9542403040c1800350302c075034007030b4008000c108164900e5070302484840d80440400c02c042c0c021600000d055109031907080440300c1e0481091030f14400b25402d460b05544440b400e11500c070005141c0c2070701064491150400c00d6841c0399004c0490011150345685d88903041c0711074910385d4080406400400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 808942949 1250 808941699 808941733
    0x907050f0f0a08060f0115120f0b03030309011e060e01090b0402090a150305010605040b0703141611120d170406181b0911120919150b01080402010c060e 67
    0x4064192100135011078078000b0141d11448005034003104400c1d41800100d4030745a0403e84032080320f80e4600002c240b520740c4240c01405441c240c0c99071905880000200700700703040190700c0901c0140d084540e520205500c100c2304429070311540500c1e004031518600410400ea003070362001503210805070026060000400000381d0703c07455644140f180703002100035420400e62601c2468050000350829506060900c0f980003154051118010140304030400030403107584104040d184a4001704c400c03e4034000b242c3c60310079252810460032500520084148412000c0c001c00c070109689016a20324401143d11030344c6080c034940140c070030307a042995105c00c40007543c4810802d200150213000300c91042c001207030304045901000e0388140701992500c0d020452400c614800c40f1018020118a21700c1c0f62107001c010780c1040c0c49058070101c01c01d02c642c0709104010891801c00200d5050348802c101e0441c0090041d10026011900240064030051a8900007000ca6201542000c61442120010511248001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 808944199 1250 808942949 808942969
    0x5060408070b0c1201030f02042a02070b040b0306090a0f1b080901051005040c030e010603060606110307080415020a06090503130b04050310020a021219030c080907050f0f 75
    0x2031500d40300090a01c05000384802c240d500700381059005480c0c681c800c00d4a950040041c0070050a45460440d80019540c2e035400140c002240c0c94138290707038502a080c004244600406450002d40183d09000a01c1880300c020750303040b83c855148051840c0da031941000b140440003040d41d0304c400e40d00d184104030000701e0300c54040c0d0349540500460924484031800703040316000520109039a8100b4003006000c0f6980456001241c2c4244c60102e000075030a2419009014940390b00c200b190310340301c1c2c00010710905401c010210b408a4880c80e0039000441d00745900c03803044400240010300100f1042100721000d814403032502003c2d10503200c00d480c0d5030340c0e1681a02d1031600150b525900220308038003004916480000207044100d06986060b00c0c3ca004261108040e46038440d1180d40070a040344480d001b40b2000e2401c40c8035038685940e640c01c030302100592207031080720760000900d000071450040f80030303101c1107010b40901070043c09000c0c500000c1003048145800203640221160780b1042c9c090311003003512 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 808945449 1250 808944199 808944203
    0x70e0a23010518090c210703140405100b0310050907051f050a0509060403061d0c04093801170c04020a2c0a180b0f011d0114040803091306180b0d050604 67
    0x86c0d0641c1c10581c2c001025507040c3c441065030303004900d0030302000483c0050007061000114001051b221001c1001906000c0d801e001c440b10710f402c1c001040010070022070385205030780b01291415090041c00c01c8841d014824040c0b04000310300d04001c7c0301e889038050005000565401030442d880c0075100e55804007610a0040100c0d000500c039195101c02d0081446540950030007514104070711001500c40404580080c80d00b20b01c86030700d043d00c010740c200440d030706200b030400780065035240343d40e46510207180207800340c1c80003403070340290100145940344c10b000f02c0b9041c41740c555070501000c41d90300c01d881000074a10701003000d0860710390a014032a199245c1c031100a00c108000b174030905504019600540321090525031068030f9920185d2400d81c1c00800094003041c00310340b04c61403c0c85490050352150f51072070744081e00c03040200d000070b5032a60001c01060881d1007a41c810300d04c0d03c20541004141c0d24180a03400000d4802610b20700791043c036074450310001d80c1c0103211b0b13003e075001500c4141c100310703081e102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 808946699 1250 808945449 808945507
    0x170d05061f090501031d0105131a040c0e0a06080d030c02060f010b030c070c18020d0b1002071703070804060c02180906010b03070e0a23010518090c 65
    0x4200c854501400c8018580c44007185000329500c0c8048000c0107022280982c0c0d050503581c1d501d81102e906903080750b07909102031100800a608000a00208070140b04900716003400c59000300038052200c48a2060003194032040c603e5041d400c0c1980b07070314007074002880f080340b6035540e42d000500800100500d11071100541c8001822114542009041120040038410100c4449004103e8060600101c960055509000c10b4440c0c100f0315244040b8541d585c0120b030220703050010410801ca15900900c00c0001032801040918038050074415080080341c0d0340005600007074801c000c0c0130644003891101585410a41c3c1c0303807040994903850950000d4100720001041d4510520450401400140510401e02c06001c8146071408031540d5680f0140103010024501001190080e8011030041006010051118841c1612003111040010348110041510540090007004a502401c11240c1c03420035500c080045034450010f01c5901c51000d40000019001081158860b40b0b882c2a018205260701c04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 808947949 1250 808946699 808946701
    0xb0a02070b010e010f290c0708012a170a020a181502010c091518120f05060c0f03010521030a2c0609040c03270506070309030219170d05 60
    0x1c103040202031b40c20414448007103850300c0011030031030010071800c10083c400503503440300e1035071000c3c0c201010b580c0024455820b000e03610303249842010821100b4440c00b15014100501c2d04012100340e2604c05048000c01c40c1d10001c507042c06d610f81c0040824400901740119041d00044034070703040c000301e940035491810141d400c503603001781c0c2801002106140b41c41e10106060501201c04640040300b4041300500c1030540f0142480380c4054034000051448070500c0f01c6084090801040b20021200200c48034024400040c400d850100e05855a84101c61109400c43c5c0c2000700713015900a54540b41074800085005064441d0420402008894080c0d0b95076035102042d2184100120328030014075000c010b103031300308001a07180c043c1501d01750350046501040341f52101405600510300c02da07884550710001109814210b116200740500c0d070344900129503041d952100c0840c2120b402d00300c02401038011a51100d1188850b070100610280144020500030b40b08158091860344000351249400c0c4d1600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 808949199 1250 808947949 808947959
    0x40b09090105030f030a0f0201060f090e0f031e0915130608090303040201120c0e0a120308010e090a12020f0604290c03070309111225050307030b0a02070b010e01 71
    0x40c05401000240c00420034005080d9080340c0300e00540400c0c40400402e11400840e6600c00d41244005240307120000040e5a15113420f20050511041d00ca0218403500c00c107030142c1240042207030305180b00e07034031130b500c00a0b20b04000c001030307603c00c0c1d036603640c000c260700380c5c0f1640300c05280020645000000e5982c0d22844c60200702400360900100b0400c01c0750000c0c02048050b0340c10000e89103800c209610000380000b652031068a40000d0468080d400c440e4400e00420103182c160180c0c5a02c0307000e41c0f50750025a9075180025926102250704c1e840c25000801c01000007501d170400c0800c0b04043e40190f40040c1e000051051170124115001d0b40c180c0c2c8104c42c420388400c0481c0300c035400301241c1c0007104024035007034031160f04910000e0460390425a484031a00103002c2d0001c0e1500810400402c5190b0106c85000c0b11540c495545c50b2209042c0e089020003412030502c040800f089610240151101d00e16503110f201c401040201000245a02000b040780081e2155660301d0180c094071040807403a505003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 808950449 1250 808949199 808949209
    0x7090614130504030c111207030c1d1003021207090f06060801050d26090402071104050c0c060c07030e0303070f030f0201020408070e040c0321230304020103091106040b09 75
    0x440d482040c024030b882c0602003c00e030b12600031a01c0d036401280440d151150b5501180c03060213004003071031003406814808810000035006031021100302100041c0d03030f20070440b20a110545d05840c188003030310710f9142c10001400c05004003082402c1a40554650a54030402201a0350400d0070501da000d40c0ca100900402e0b4003c041c050260100741c402c001d0400069442c103569518400c400c01200700d205002c07242070340e480760840d114040040d00c10741d240d0060389481c4510482e001c0c82148141d00b800e0000d50140c08600c1614104c5891000a01568444010a0b2030b0b43c2d20600042d0b041121403584c12802d44c408000030201648110041000c00c80203040040020700129802c07011640100400c02010000280c1c0006460000300d1845068540e440e2805005d00b05031720040210050740000001000c510200d0380c0000441c1d00c941c002d010540d403010491010405d0110340d941070600c042400b43d4441d078040e0b20050700c245804000a105800020342540066200081117400000d80d41040e0800b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 808951699 1250 808950449 808950469
    0x6180605040c03092a120c08070501020a02090708070c0212060f0a110d021b0601030302060106080901090c0e070314151512011809061b11070e06011107090614 70
    0x180c07608105a03004d0769610400001441c00e0030070314a060710107501041a415200200501c0050451050746100c0d181007038603c400303840b403100c1c940640c540c00503c550010034407100d03c45d4020150342c201ea540c144243c0700c4510140c00101006400c000800040c0c03500c14200203034101d00001844031b458918200482d01e44000e11541c103031070500140c00741c4410110123940315008909070160700c41408a440b80715800c90a504500707030748607075030002041c5074010886134103031404d599441f4002d179030720100e1909903003140100500d143c650440410074034040e1060150084910720300444c20504030440c0e52189e83c0142d6610751080102004001c2e5841c121000300e80c80800c4424203420550b404041e0102800c05206002c0e08069056161050000d25030281c000d05900c0782d02000707040085030f00079049103549034001020401e602030880803598000340202c02c80f02040b075426540d507108001110303480c0040300b00b180e061084c2c401c0072442c490360b4043d5101501020000052110140c020012640c02c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 808952949 1250 808951699 808951721
    0x180718090b1506040b0f0f030103061407180603090819050309160f050904080c010204080706171312024204030903020409020d0b0f0a0c11030301050d060618060504 72
    0x4445146109107498080c182e5080b6017556402c207403280300580000c40584903c00c42c2c5524a54000f0000c000c00c8502ea20070240c0761000890035407295141003050b18511003141110605141e402d070108209446130b0840b00c4151f100704180d6040410080101912054a4110701c0c00b0904c04020407203400d0302042801402c841720420b551200381f40080c1d2240f02e000c94010140200c2b15900000d0601411400300c0303050900c610001c40d62503942c0d05480392940054014040080c28010941034072640e0147c00c140100c034510000100f850241e42d90200b0618015822010f41c015040440c1c11030003014000a8020782c4081c503003640303e440d04a013081c1d2280401c240f413503208494061002080d40180c03250b046d00d90548000413240c5085c00050700c1400c01800051450003090104008141c020b018240240d00d850006d1000203020350094038080b0300800090410340c414030041060340307000200380f41c00c140640d000160840d00c902180816101e000e00142c90661500d60401140c00e09110700e940e452 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 808954199 1250 808952949 808952971
    0x11030c0f09010911040305030f0901200d03050423070f090509070611032b0f05161404090c0804031701050d022e03090506010518180718090b 62
    0x981980d000031114041802082c6605035141c58a4a104400c00f003100c001d1600308003101e4132010407145079079096000080300c0d80010344a5051400224090252130108040759000d403042c104444021402020b0081040e203041a851070000041c1280040c00810070018001403e01c941c00c000e000c0102808503030088150707e142404002441b40049204001e40e10507140543e015080c003403825242d8001c0c4500790760700405d640b5203080742d80600c6000000340741c606142804171801d07400c840001c5804c22103d49403001c6a0a01d005040c6102c0d0300030b80c1d42d002141e294603042c1a1100910422582c04540100220302e105042c8001c0c190032480400d104500041c0714178082d8107000c049102c5020340c5000901440c01040010b00f904030f80380c46451002c2c01d070417034007144948504004004d003140d10401d44050040034000315241c18143c480c1303004000078078a000c1c03054440c1c0ca00c01400e141c0200d0410236501900a022640c036a1a07110a143c0250740c2c0d1000c40c40c7c1c000d9050203590a4005400e2060706 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 808955449 1250 808954199 808954219
    0x201050c090a030b130b0c0306030c0a08070501050d0608010608031b060709180f110d140903070201050715050a0b010306090b091612060810050c0301030c0b030c0d0911030c 76
    0xa5550380b041201030b030741d02148104c903585400d00b0515041d05d6143c1c006100307003524420001403100c2140658882c0d0402c408449501018400b8081d5001c000e00408030070342c103e6502407110707500800041c100100103140000741c050340c0b51001421940340390890541a08006a10b4210317150058944400c2c0854002825241c18441e10240240480b0708c40d440b161401d141c2000c031000000ea000ca1109540318009020014001465003000d80c406c1504040e4686003a5044003400c519103101449840d80301d008520b011625001541c0c160410101245e48848203040071441010501a4038040c0441715404601048108005820f882e00c070b8002d224030900c0c2076110341c3e0301c2c0e4911400c6078014284040c20000542000001c503404208000003d02c1d850621030000f50031140002c10006d0110340d40002c0001c0d46407121b074100a80720070710028181c0559400f040c041c58003054000d60700148024540c500e000d5000581d60182c1e04510300503200b1401703403d80103c0a040030302200c0740d0b84208039503007445 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 808956699 1250 808955449 808955467
    0x60e0a0b0a030c05091f0207120b1306020c03070f06060b0f09040c030e1e0d0f0c120c0c27060b070b06031626060114060c0a021507030201050c 63
    0x99401055864410507443e100c001c264940030340121042460041c0612400c0d00440b8054058401a502c5d000014440c1714400039044050801e5211542d07072211425446850ba1a040030142806a0060717562507420412110510400c00c001c10140d40704400300040f81806042c11411120035a006040074a000c00c600c080701c8840300c04840141e542120f0000b8210113880003200104a03881c0d807800c00d03201d0742a1003000030011035080c945d545401e01c1111a0501e5940084445031015100c00c00410400e0302200d0000f00441c02d60860f03002589080c0c0075a6015845000d0001d801c2e078420030b640f05015203e5440d6804903090401030f0b420345501030140c20718080d608101e0340724881003d441c2c404280c0101d82684d03810b015202075001010b07041d90b0700030f843c2c090300401196088908200c0708492512031403202d1012a00301d048a09840301c3d1039040e4040f8017806115441152808103034003c88440b0001652520320907404204540750094481c2014503000c0d00311200a0702103004040c0c14046801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 808957949 1250 808956699 808956719
    0xc030d05030a0f0e16050f041506050d15060c0311070302030318060f0c010516020607120e0c0405070201061a070b04020f031e0a0c0e09070b030709090e07060e0a 71
    0x78214865000001d0000c2c00c40180700014458800003040c140034101491405c2c800984400342542d50480c0d0b04203617500000f041004a03444000b000c404030708800410020705025601802e48081080800f00f030420f4100001d1042c5021500040086028455100149540000280c8909000c0c5005004071419600065035034092141d0021074043c642000d915583c84000554103482d1107400d5850310781e820040181d02a00046440b01c3d150302100760045e80c205d20014040f40590481c3e1034940c42c008512540c1c1d0080c042c0d44268142a01c0380c045010309135183da1058a1248069038000214941445408020300d51103182c0340010150602c00340d00410310003c0d045401660454400800e46000800300c0c0c20004120303014215036540c545402000000032903294000c80c42942103109940c0c50700f5404200b08801d50303400e1600d0340140414004000900003c40d0003410320708011848a989031030400940b507454040c0030b4036800800c800c10076150414000514800204e43c03101c41141042d081070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 808959199 1250 808957949 808957951
    0xc170906150307081005070318030e0d020604030f050a0b01090204080705060a0903080f040e06180a05090106080723040c0c06020f21091b0307140a0906170c030d0503 73
    0x450000c0300ca03107424401d80e01003140700300a0910905881106240780c61400060000310342c031401082c1462075451504007282501ca0301c059040d102c9a034812502c0301480301162040b41c0490f0080740c20030002c00426019410211440e110b000208100c000c5494580c17074160060b40180384841c0140820301010341c0104100040d254140c40b100d0b150100441c04a41c940f0240d44044c02d102e0000921034200460000200242c40011000d10402c0d200c0350144207400c41550b1544818001c4500456101d80791a000541c0108980002182d036a46440d102d604100542d07010400300f04050482c00081d64445013446c081203006c49003002a00513002001d4400c2c18a685c00030b101e5540050001d80355807220040d43d211103031114808165044025000480700341c180c1308140340b8415100188000b1188440c083c203680d00284c041c1504901c2d2020481c1034440c001e031219409110800d01203980c580d280b0680c801030502040508100151200c0c0c24207106451842c14003a41140c28528520b0340c0100440e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 808960449 1250 808959199 808959211
    0x30c0d050904021b0703290114120609150109090308010501050307050f1b0f070f1e051002070e07051e0f07061b020c0406050a031202030d02040303030c170906 70
    0x556600c0441e001500903c540c00e0001d4030540c42c5854460881400582441581c5c07291540c60905141c0300c2c01107c2010301714108079070b000c04103c014450b26600958181403c1005000040e00b011407241303481c01c01c60125006845940518844461007080042d003600420901604008080040c1c81c003e00030141401000e060060002c081440e03a44200200c40e0004003500080751500300c03001d40c100420184055121036445900e07000203200c2e401040e04800c40c0c0321140b805070303440c2c6070481c034003003100754046071058840c200a00040c0e242c03501c01e210346002e17000c0e81c0504402030820f5281200c08001501d64420001c0500110318140500b91100041502c002500c940f50500400c0c3d0003a03d10980b540100308508010081c3c2c1d4451207010303480200078007a000d40300e01d000c001040c0000c9850500c0f51551007100100100042070600c2003c01d44058144141c9162001000100013030368095841107002a41d5800c900c0001503001c030410340010708101d948000c60500c041020382da0030004e8a6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 808961699 1250 808960449 808960457
    0x90f23010b0318070b130815012106050c03040c0e07210b191502030c0a110301020702060c070302090604020313060e0309040f061418070c020a05210d02030c0d 70
    0x400c80785109501e440c443c2400c480c0445143c1c50b154101030101d0781010701a803064070300300a80442c0e001004501034200c44800c03004101c2a0307207807039411100250000c400450041c1c0b40d100250114400d030003075502c00c6015920036a40c82c145442c0a401c4010304d80d0103610b0282c0c408052220003580400320140308c0c82c41c1c003031020b00286090620300c000e20303460b020a54007445100384440404000341c01c2d02d0031201010204001301e20324040c1a0307101e100320705c92000350340c103c00d810500141201c046070101000c0a000141401183c1d8040b8105034400843c44403558000c0408000314600804034550005007610300f035003903050a0039107a000301e6070031000170500740e00c5500001c2c0200003001640c424140050042c000c1551800066008101d1400b441d408800703081d00d00c0f800d60908040044081c04203070b500300340d155901c580031241c40b00d0f2100d049a00041078080001e05940c0d100001c4200c0680c440b10b09174440b000d00200d4601207031100341c079040d50424040400d4040010034000c5d43e501c0c070703801c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 808962949 1250 808961699 808961701
    0x5060f160606092d11040501140c0f1c030b0f040e150c0a11070501170c0d06090209090718060c0609060501091b080f060f0415090f23010b03 62
    0x1611402401c1e25421050006240ca48140c4264504a02c4c550140481c1e03202291544280a03d81c4c050b9400107001000c0184100000c000741d512a406003920b0b140d4181400d0b051814220a190070540e55070742012583c2c0c4442e04101080c180055062200d142508003041424101408659112803c3d424a40f04a0769444115410942400400807070303a040040307034000c0d15107040b00d10800d400c40304000002442d00d000589611000040000991364143c44821a0744e08601d0450303030b0020300800b006000c60080c0051054051103000f040c2c0a40f220f0740c2d001d40c9880580d000d010503120001d20010411903086040080f101008480300103580e114a03191008d0318850600c01c02800d40c0c5000107020520701400000c1c1d446060344502c403400ca08480107140803103030305d00448034440203039220b4000c40c00c070034081800d9241486100310382c100c000d400840c02c0d103500c15008600000d1030f402500f0564644041c1502c0d940346115100c140901c0501c0180380c036482c2050302c0302c184814002c81200100000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 808964199 1250 808962949 808962953
    0x614091e010e10050c100e0a060b0d1202070e090c0d08090402040f090c08070513050904240b130e0304030807020109150207141c03232205060f16 64
    0x2c08640d049900688403500d202150f041c02081680202c00c1a40a0f004180d100603041c41e290041c1c0050000e1000240280826a100c0000800a90442943c00140c003014400040d50503503662024071281d4014000e12440c040301280082001040000560441070b075030b01040d40e5185141741241e030040710a507180d44524003c00c00911841d0400c2c144e1780f09004000400b000260081da0960b00741d0317501c0004903181d4601c151190f0142c4940300004140c90001800241000244642e20078020b103003d8100034035517540d45d02c0c1d43c1d03010503410403440e0300c49100f00d0560134042d803580410400313800200040b04046c1d650700e803280540e000091802c200000c1907003c0d0781c81821940080d107801103011520305115a000f942da039456200312040c240c0b00c108100060319201104040d040025002c0798180806941e0485164400042d0141e003048498500319a00d0b203884c01a03c0c0c0c08140340ca030801640504080d2003c040310591040e88260400c01c07981d0b403031381c0c1d4a1054131404460900700d86100d041e24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 808965449 1250 808964199 808964207
    0x3031e04050a0318050301060b040519051e0f040908070302010e19150e330c0f1c0203070905090f090c090a06030b040c3314071403040614091e01 64
    0x91740203581c55820f01c540480d00c0c5c41c1100040046407000c4480c181214400f400c4a40d00040c9440344a60040c01448a0451485007810070800424010802e10405400c4000071742110020031090722000004601042019024070032480d0f480140001800f66a04449916014809071607006001d0406c40b2000d41d80c214076a00b007400750314140c40964010360304080e0a004c05000c0040c4c4010100c0c01e0100d4102c0310300d802c0801074002d0f0841c01c00c0620303000700554048065449080c51940481c00085030101540c00e034400395000d14001c0d136175800f01c140b40c038007004403110000d80001401039124080c01031142000840303c8045006541e030a02aa480d002e84000912855201522880098040000b08001c9a4040003078840c80c500d280140f0a41d1034051030030f07203014419441381114590030524010b0007503507142d80c105840d005a6181541d1a036500184400c1100d500185078400314080c00341759000400281c000108010702400c1184035000540c03441c520a10080800c807081d140080d4503441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 808966699 1250 808965449 808965497
    0xd021c0e0d02120f10090309050103180614071112180a091a150702101b0204090606090b060703020c090c0c03031003140d02070e0a0207021203031e04050a03 69
    0x6080100b2920f5400703d0315240c461200c0400c0690090704003001d000c220300e101d103014094250303030b0700040641400c00660042189104104005119280c50000104075002d501102d2040209103001800d04400240130700c2c03c583c8070f5182d41d4012601c07140c4665016000da810341031b01c2264040320500c041d00400d40c2081c8540207412658286000c0740066aa8002c00890044040d01c0000050b1441401a0300600070354000942c040110100315464503c01c41c00341030050b40650001101700030f2036000a04890f04200c04450483d06c0350410400c0c2119842418001d940c1680c903d80f61041981d4000d4403000040d0019104070005004201010000001e0f1440d150210040b2a640e003054a09508080c0c03c0b44002c94200107131082082c1012800b02e09514403150070340051030410700300301b000d143d440d1005028201c42e40d402e02a01015035105200914488108006503a81c2d040c00c03840150a8a43d0001d69480c06a2200a00c800070307000162281c0d4071070301403400780309150005115180c9000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 808967949 1250 808966699 808966703
    0x9080f0307020607020705010e3003120108060601030204030b01090207051903032a05270612010306050f190c0306051e130c051611060315030d021c0e0d 67
    0x18000c400c000e405600001c440b40103061580881c1c030b0061f03840d00110b07201c3c0c0c8000a5150070203480c810300c04804110031a00e5100c004018800109440c140c52501e10b183c1120481e4070307854844400410a094043c418144c01c1813084c6015803030a4103603103031a2035250301803281c1208240c1c00550082800401d1004506d00710304028501020340e65410010042c14a49100d4000300c14034481000300d00c40040540d8134503c4080d181d41d030501c540300756180c002c200600c0440c0c40c600101036440421b60b440c800140900414102452403035410343c1010740480300020328810301047c4820511103c080035079101140e0084941021504514a10f405c4006c6c027420b0380959002988403d0304040c0b40c1102c400310070400741c02d1702c1840200902e0415202555401c54083e0013107002000080f40c070608500442c140c3ca03010f00c0e4000035a025240110b409903100302c501e03c850b8445501e03500340901d014064100c00c40914401001c0110700031000805d0503001e60407600c203012030715441410030f403546000303002c1050f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 808969199 1250 808967949 808967977
    0xa020423180703200904050f070905010c03050f0a050310060509010e270f06010e2d010908030d060f060518040f09080f0702011814060a1b11040f021c0908 68
    0x3d00301084c070060740d411039510705101d1810000020300c8903092038841c84c482c0380c4652704c3e000303443c0c5010015246990b801200340e0030000c0c00c01060361160f03144d4005003013004066884540e240392507464441e05a8450300a41d040040403c10400541e900140444061800b105d18440d80c4010240d5203034500c1390680200380c0c21300c00f00c04120030701880d24061403040300d081e03c2c1c0a40c040481030070014407035841704003c0c5a041700900d080604e514047d00d203c60801d0181022404592652120381c07641d001002c0800009488040510401003401090402072203582025410a00c1d100010060540d01002c01e40c06242d40d01000481c52049420a60590350001142a80ca8015001c00229503005002c2640811a4400300d01002002a1000c00843d170415419509086030038080019640c032038201c0d44104100f030603c455601000440a0342c8243c417640508044000d224140401d65504813122429103205010032034420000300244618184c00d00c0c0d0001321460507241041c42c60080b80e036110207030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 808970449 1250 808969199 808969241
    0x52413150206061e0a0e0703021309060311040504110108040204060b0a020c0a0b070305030a0e0c1008181f1503170c01050c2a010e060a020423180703 66
    0xc54000c6040c42c060340c026a4611407000c41c03180d00c8061a049800e0080d00a40004000c1148040040c18640c00200314a005032601d0f40703141f2140c180c602941c001d030501c180d48a42c100100500190841d09091096405014920780794840c008004291110b003414000c00704001000c550741c07175000c0400b4041e060001e40d2110140e14000b50745508640100b401209500307008612283d10b03009486440e545076460030702e182c3d9804408005012800f200c1c81441c0300d604070022590392101403485009003103a907000341c946000c0080801c40001080f4042c4a07030030940707407056031203043d40e001c15051950f400080307040280e105507082c42e501e0a0780058070647d642c40481d0101100e0000130701040d00300c00b000b40000e40341d241c541c00c40d078411601c142d0889036181444901400c424500070190322050800082d0724000c40e820103080c1801228120b540c1540028144200803041a07100f050900c1010f05008004140b008940441b000c600078a166a21103000a4542480783c3c11041c01503200c03034030f03244d6a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 808971699 1250 808970449 808970489
    0x105160203121c0e0a120f180b0d140402030628020309060612011104090914011109130e03030106200d0c02040509010513170705010203100807052413 66
    0x803c00700c050b20f0099903801c044840c035110000090a0582d20341013800991b0070918441c00b1740d44180b0318242c0c1410702041701c000c803c0102c50b04180200901c5d080c1c1c0a551744000040c003240448001d4980c190000050300284005130f14001902540420006400d103112a080440340082c01c030503099585041b07000008008040502040c00303806020107642d2182e0341000601c0b1a800c0e203000c540059011002031008104041070794000c00c1e0050b0046004840e580d00c2c0301d0300ca5094510b01058400c1850000841c03000c28203165036040111030b400c0703000300180f030040300e5101c6d128030040c801c500811003260300551107100e13203103607070100d00a0503012501041c4d44220058401a0342c484180c0c07150345800c000039010b00042c082c481c07260b1443e208602c603089255480c010760001c42c5400c80600001482000000340003407000318040c144010300900e026140550b0076280000d03e401245c082d101c0c9500350500d10394090101003c0c8200203203a6074131240b0349028420f0300708159103c40040d20300090f200301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 808972949 1250 808971699 808971727
    0x3070b01080703020f01110c040203060406080105070c0b180703020d030509120f0616050712030b0301090605090d11032706070b1f21051221090606010516020312 71
    0xc491007030715a11035104010b170040d04c50780c40300303203929101380c20101003903d00c2c1c58158000d6921150040000503416100d050460845008544810100d05229080e00c24000c0e40d15070300340c0c040126074102c180c103c0c070340041a486200900c0000c2c00342c009000c103181018000c4c4190303040148003400c00d00f1540400c00d002d0380d03100384c0c501340c800341070082502080070b813000b031822201c400704180c8034246820019a0b42c501c03020140421242011f94030503a0a07210354080c0a00c4079614014140440c2070f051000e078150030003203160340328003d104a40103034100c451000b006603801024148460b1029440440c001c18100300c00d500000c2d48480c000400d4010803c200c424503016040c400081403680a0b00240d5854041c0180148003a58940403a00111140034498141c0858880c1d4281c03000da100c0140c0e0840e090b04000c1085250319488075403000b0080c0811146607018600b800101620300704480040d0041c4a10340810919000140c0200107540302005070802001d020f11200b0360700d25a80f450340c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 808974199 1250 808972949 808972963
    0xf0f210c04150c120806150406120b030303100521070b12130312020a030e1603050d02070b0d0504020d050f3307030b0d06020a05030406110c0a0201050a0203070b0108 73
    0x2070762490020b0101d1031000c3c8544040e4000942c412003580718110b11000c280e81486004103d1a40032040c4440480c5900d10b400180c0020300264407510b005000942d070755020b40300c01c0c1c09068060b5000740304020400d001c0301050003c07500107a405412a200b41820294940100d0032000e42a00c69103d002a4040b03203d001090800d40956503800c140d110614050b40c50b1400e800080c0000300010800c00f00503025900401003209241800155209075143c91410710b202460009406017144d001082404001e1141d10b505034030a00c0034003411410003144210b14042e8407072540182d6a5980005c0c11912600ea180f0b401755000012a05070040c2c4001c2269100407880c5045d00160400004440810042010344030101d100c15090b6808d61320f45c0f070200c00809c1c481540690003240d03010142c0c04580c40d03200800b00c00109a0340c0c07503601e141c6418814241c62102d400300004a008100700c1410f08004100303a114207a092130a141d5920a00b1000c03885c5015a050141503400100c000003100c40000441c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 808975449 1250 808974199 808974209
    0x4090503040806010e10050609100e030f0a0b04061d0304090b2209050c01020307050309100c02090a020c07140d0209281a030c0112050606070c0801050711030f0f210c04 74
    0x241d01b500d80710700c01d1082d1406a0030b04541c02c50f442260200810b4011072040c118034201504032016a00c40c0b140712841c1c680b20710b009131042070442080c841800002e001d24043c407008001911254138001c20190355038812403003251030f0680d407201d080c41d080d41c8030304c0070b220400248017100c2440004006218003e1050110480385489281c8450740c0b594000310a031039985410102031030030702c1796040070700c40200480c43e181d40c00c10110049200c01030752241d1500c2c3c0541410840181c984001d100c0180c40c01a03c0d810200750b5103c462414815560380010034249a5030503110048036441e51900000c00c000b420784803405d100303041c00748016600e02030790000c050750080c0c060079089481c0e28420701d510344000070340705030000e00039003045201c1c030f0410b4001940045001d00400e207080126140e14210a406410450769651214280080c0c05d900c01d00410704d041d44440610700d840b002e0142d100c2107125246048a4000b40416a408100c4689084400e050440042240c0d6803030220400700c0617500c64010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 808976699 1250 808975449 808975471
    0x71208060f152a060403020d080f100b070501112b0c0504030b15030303040c15080f07180f0b070b010603020306180402041508070819050c04090503040806010e 70
    0x21520180c42c1c408803640008001648075450108240c00d189804800c42c000780421503408503161040c0c80040019522441c001c2c0c3c007a107402c040306400140600b402401d203460a800501c2804020041c160104040741c04c1c2c4031100c1d03607400d800c0c6003582c0980381a1206945940d40070030300c3e200c40d50300d1601d9611507000b420f480da421007541076503000845184101e8140024002d2200b480060482900d1f82d40059000045150b0104841c001034a10b92080b0b8084840ca011640204440800c40c085003074100d040d8100010304c0e14002c9403101c61540b000700054200b001907103030305140700c6014505c41c0151000307180440e03181d070b12100b05468591110104481000c401000050310030300c40e1003500d0245100608a4500901d800f070846c400b0320024100ba81c1c0300c3ea48440d00c0d032a00300c00d402c032030b4014281c08002d444500c2c6400c902c03a00344044c1400b0011780131280b81242000400c08501e105003500100d0300000d0411007400d00d41d18500031504001020312401c00007081040400f18418813400007100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 808977949 1250 808976699 808976719
    0x19060905030f03030c032d010308040f0e040203100c1103070c150c050d0806040f05190f0b0f0904050a02130609050a060303020606280603050103061a01170c07120806 73
    0x1031119070fa4070049800c2004102c00307102244103841d0240c480000c1c1c5805809000303018014864203900380d4000e03030048681c4040002c0c200080c540030400342c0b00510303007506146280d00d015004251541c446048151b00c2640e02e4210344406400780004480402c01041120388800d5140390900d000c0003030740204407003070200100e141c4650388108a10380119600c08094803241c862948146c8032168090300069201da128603961502c2402842540d1040b4014501009180c01162200d0201d850414500d207685003407442d034804503180c4056240a0110070307513840000d6511401c0090034910f202c58000c6d4403049005040c070218445d03810081c152207980b142044280c4032075408030f085807418400200036801c003a000170910310301a58400300044581d40c00342031141420307030900704242da1900316030042540d40740103009022641c421403003041d07010003071012614803000001e46401c1e000c0c00d01c403108217084000240e081d9002d90648003c00e5000701d245d1228410008040c091010480d0102d02071000d081c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 808979199 1250 808977949 808977973
    0x617010614011209051c0210060506031b0d0f1b08010806040f060218060c0a06180b0f0903210f090106030803160504030b0a060f090e06010e04021906090503 69
    0x41c0c1c081010405855541c1c1c00641e50350f00201078103554005581c02e0056401c24904280040580d0801c0d028a0340501065060542800111000382c0c100354044c4400f0b2040140e500424800030454052640089441d5070300c4000c0c00000d004030009440710582810800070125109107903012451803951150b9199a0300c800400d980c81c001190f0291000400802000100c1c141c6d0780100700ca1160501300b0424100c2c41001b0810981c080021513040ba0b101c1d000c8103062041c2c03485121007000303c1441e4400040c00f2502e0b60940100c0242c4864284065034010540000701041144d8041440c0d000d882c12004500103c01c44401c1e00700d0750540c2c18407150000900e480c1041c130a00d41500d92141c1001d01b180c41d85e60284048128507074558083c0b0008200220120380641c2c461807245d072040707002281450030041184020500d903401106083d080a0070000c11070300c00306840e0f05440c1c3c14080e148550703885000103200301e0201a84410031b1011a6000315201d50300141c160251401038080b100d18410303034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 808980449 1250 808979199 808979219
    0x9100804120c0b06062109070906090b0303070602090307090f050610030506010c0b07020f030f03060a0617010302040902130903110f030c0a1202120a030506030705010309030c060510080106170106 86
    0x4481c010010f08000001403540d1500c0d4010388461690a441454103000e8583d0340d203a007000c2030344d5000241c1c2c055101004100014002c4078064202030f42c0030b000c900362400100750740c1c1c000c40d04010000da13004205144140c42c1042800020b020701c80d010f204564614107080f000300b5040e11090b008010300304056050f00d00034018070780945410b035500e108095264580c00c08005c00588031200714041e06807558402031081001d004417100070a401c035600d0402d035080096900c0554060170510070284003070200300907044149030440341c0541d40450321060b50310004809800c0d842180b1b5400c0d140c15460414980e2000c402c2001e08071071800c030743c1300d1128485c1d140d90b24000c210300c1642e6a40050f4010b000608848000e0001007600d00403038101100c8104d241c05180c000e50451030009989a082080514080000c0001480d0a0808000e5001c041d01d000b000e02403107040c040d1943d501c0300003041d000882402d13001c0050550100030045142c8401c0340c00032801003e02c00c864690300341100407410040c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 808981699 1250 808980449 808980467
    0x71b080d110921010e0a20030a0506010b09151b071a1b0c040623061218100c03200a0c1202011b0f0201140c0315060910080412 56
    0x10b142c5403140461070740c018403d8500c50201111552a024030021540b4100302c1818820f101705140103140142c428170911045c1401c490a100394419418600422008240d603415100045400365a40d0840004112490012805900002c0c0d00050711550aa201406040f80301855070a40f040203940d181d98080e00710003411000d95072541001043c2d82e0000000c0a50024074041c800d803402176045100103821074181c0c0d401020b4400b01116036007100001c4001064030031a04072040b90410007103025003116110700900300040440201141c2145460805c0b10614524091009200070302801c00d00401034102c44104a4082c10210701c00031011010301d0568124604039961140e403080c450300c40f1044556041000d80c19556140000c002540c8000d4502a103042507407540300408031005002821614107080300b0880026203002d00148108020490f500722491520003c160308481000031001c0c46408202c0d0313400701c088403842143d42c0d00107162512540c041c1c2110044011009015145516 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 808982949 1250 808981699 808981717
    0x40305090f0103061706012409051c050703140d0203070203030d1d01050f0601080603010902090103030e150d0515120a0f060f0203130524010905071b080d11 69
    0x2000340149100c0e810202124946641c0515021410035501c940c01818951800e1109400e0b400140052000405d00500c07000855001764140c44ca503040448d00401034052801028421004003100307109000d000c1511036401600002600c102960b640340c203031082445400002400d000e04a410903246001205079641c194019025602d01460400c00318010300f880010204008038514240c4004c0000f4890148150046070008003070741821400585072550041406110b44e0502143cac2c40180c84402c001340c1100d0b414108031459000140005550400100502006a0011a05486966060f0440c42c000d10581c100450001100014420310600c9c4924011950348283c5125000030001c40380a04000d0141c48005140200d4012460580c1c2c02a500b803c00600d100704100300b801802d0081c14500c07082c20105030b0f80c410b610f10402c0b040c3c400501c14050f845650300001480740340510300140b20744040f41e415038128042c610703040c51640c200403000c000c0e40785004e0b803513075060314500122a0291 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 808984199 1250 808982949 808982957
    0x160b1201030602161e03032909040501110a1808033a020a0201021201081b0621180d030b0604030f11060d020912010204030f03050703090513050f07080403 68
    0xc0c0c215110040650b100b03c0c00300c280c62a040f050080492201071845c105a411444c4100e461686410018181c0310850301c100802e207004900e0702c050130300402d840300304070009550f5000f29039901e080145c0144020440484122400508c0006031a400350044200e090724402000d60591101c0d181a603d004000e0011205140c0344e03018000c800c2000b010044103269004414030128928464000b642c000c070b552100540c5d0003143c4404c0201c034140d002c1c0d0141c80c20700000e2521540f064107a102c04034286c11050301898001079800928103c1d400c4085503c4440f5502e071900e4241202c003006000c10b447c920149900840b0307421007089200f0f000f45501207000400ba94241410b5454195040c88040d47c01c580c0031b05001441e170100e44944020302801040c41b240144c5414000041c80544804040f411a0a0b441000103200092034103a81c02d5003207400d4a451038548201e0b00d0181c1d60480c850f000507501c0480d1416a03480d0b0f0a59404c024810403000f00b8001d1152925142982c1c02031003900d00074081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 808985449 1250 808984199 808984201
    0x807080a1112072c070f1b02180117121303030806011e112107080f040b0c241b03190e030a030501080601140906061b160b12 55
    0x518002a02c4420414200c041d02c59490f5240c2288400311810750f00140c416014010000c9080e007100c10a503403000150402c00540300d01000014400200702c00d04c00715007110742050700195110b081209892100d4000b00410707a58541d403c0801c84403803520b6610b400d101c0d042031005a8451541174031a1940c010603c40e40050445e44c040c2e07084030004024078104071450781200c41e6401c00e400340340804442510b072040c03041544a140da0400c2070f450105590104155058a200c0c1140d40848620503080000c240e210020307503103500583e204562090562240100b1854100700b07000c0f0b494007042038810300150541c905610500c0781d07036074100c03002201c05900d9044c511691000d00000c41e841850a04002030390700e0401c0c0b80e00b00f251441400c04000b6030020403414401074051040f0390150142c47d0050400398502000c203540c4074042d0640038000c2c8400404981e190300c2e03101c2942d401345481146105a0040a0b0415a0383c001d006429000c40411540000c0d90f120124101c50080d800306901c50f481e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 808986699 1250 808985449 808985483
    0xf2613091d06070c0201030908120712020a1403180a063c050403030f0e0a0510050910021303080d1e0e0a0201260702070e0106081003060e070e100807080a 68
    0x102c1c02c01200c4c01e905043d215291480000d90760b00c02002c2006042580380d141c0d090080000302150011200034486034810010280034540058018041c0d01c405002d00782c0da0795904642c541c800311490600c141e17134441c120b4408104016904003000c5ea60041001e03a030f15101130204031007250701940000c50303800d05e03124400440850b9904059807041c02030801090200b00122418100c4008010340d078503070382104000c201009004c0c4682021300e1803008041c0400d0410100a90326850050b140c0c6608681c0002d21500d241d440100c1d01004640040c1c1854941e038502c51103401401203841002840308810032030380c02c050080d214102c1150881801000084015030054a04c496100e0504006405102280003449000401c0c18800c54965016000301440c0c034142c40d0f204001a0400028400104100084411013889540450341c00082c0440c440c3c0c81080e00600700065500103980384a04c280401654606205000c42211030b8601102e10090351400c12a4a44225080003004803901c603a4000d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 808987949 1250 808986699 808986707
    0x209040c2d09020a03110f09150c19050f010c0e03010b0d030e0f0303070611072d06110c060718050d020d0821040b01050a050108040f2613091d0607 65
    0x20b40c01098200001c1d0708512071b6000c1e90740d0b001900c0e040c0012600003800891402c5c04048400461a071030002070901686100c5203844800c051031002c100481d005510040c8001004400030303001818000700b001072614940109880414009a4040e60a2201094407070405411642441d50181e4520400150799020002082520f03400e0a40c50300c1b052180c0740c0459480d114a84060600100c0d85595200600d4400c5c2e114405003c01c213101e812510410400034003100c0342207074042e80424001000d4a0b590110809809170300a504c0141c8614400c000c2c0a80d08000c0c0b002c80c0101c40201c0c41e0040da034520400c96400b950a20094202c0c03004901c0c0340c000b51003c0d014221101240303240c0005c0042c003002207411220304507015284100600010410f80c00c124200c100901028070707001034145059103580c106c0c4803460500811001128241c8084401c2c140307075895003d03030300d912a1a61154a0a00602880d41c2c2c1d001d8600c0380b038680700081c6008080018001d2400050601805940c1d0710030304191 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 808989199 1250 808987949 808987957
    0x807030509030d02190806030f0309060f0d0e0a15060f1502071809060c030e1b010905281217030402152208060712180209040c2d0902 59
    0x6960b22040c404416a80000d0002d0803440744880704110505900070001084140081c1009010343c204a602c144007032000702c12120380010550b01141c1e51360141d20391411610a111141041c2407a001d41064200340218203645418010198801e42c04d403030b500031204541051041100200d907100040044103908c41d88c17071110f44014010360f40150b581d40b1034084c200d0064201600722031741c0d0304241c41c2004528400c0f01443c04061904028070310b1041415030755110b1141d40a4104400320240e001540e04c03d01204003d4040540700c2c1d6100c07031940e422000084001c0303020010502c040c11020805076a9840756107205600710440020304580c0b0030a40c081548007400603a040031840d140310340c039840d00d17000800c110f0000c0c81f52808a40c0301a08d03544c015008581001d856a00200705100119034800d0750b515290001c081d0000f03809513507540001600607002c01c02034000050000b00410300100e00740c48411680c11004c5034421a00300480400e803200000400915401c4618090002c40c606a020f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 808990449 1250 808989199 808989211
    0x131b0308120606040f05090c0c121e1e07050a200112050c070b15041803021009081c18052b02060a05130f05011a150306010c1704080607081608070305 66
    0x114500709d41c11500e5030400b65804c0030301c81c6550700011040c04c00b14040240d4404030b1b460f503100d641090083d004000344210031020f003e00300d00011440f4010300c0b009208100016a1054014100c000e50704a800c102508030008280030a559003103210011425000da80d202d001301300601481c10402d580e0f150080a40540301584048030b0f4645101d403901c9910880310000416804031710807140072300d802440e15518505240582d410585c03244000f561100540e18003035040e41c2d82c0e0b101c1240c01c40810700180410030380c80e030701641c03140300742d00a0080c00b0070b213142029820102c0852190504c000ca101c201d40c070000c0c010069100300c000510032411580700c0b036005041da41460819604545030000c101c20b8111081c2c0d4240d543d2000500e0145940071b200580c40001c0ea00410781004120781c0d581d1502008141505000c141c6144404102c0d810814441d00c0d0715080d005601c41d0b0300d640d60607a45400c22280007011030915408100c50304400006000c0f90521350351f61190964591500710b005c4c240241407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 808991699 1250 808990449 808990471
    0x7030c0515070606031b092a030207080f030a0b0909100c1e03060801050912041701140405101d0c01030c1b030503061306030803131b0308120606040f0509 68
    0x1418005030f202d0103400b005502510311803000442a10b103006100c4556409400d110345041010510038000c21514880801c50403005119401580300983c040d00c5117540040c4040c90015a000d900051400518010b03500e10300e040140e0f40502051100c82c05c0203580707a217500e62001301b000c0c0d45403105800c4040380a050707242c00040310341c88181d001c04c181d140d0800440480e488400c2440303565070900c10a5070280d40280107100d40190324800903054800d43c06551200c2950181040c4d45480940000c1e0f09003212032014034062406040a42e201e8034030040c2160022304014070011010f440300c1030789400140581c082c0071114080e00042d0700401038000013006001402942d8010301100580c140c035602c0c00f903202c0c15643d01c1d0803010400b81c060444141c0c83c03c00c3c940341c0d09101169602c0300b9a60301c090b80404213104210903040414900c6060400300070340c2003400354048100000390000e40300b28481020600460b440d8901000f11501503800b4089000880c2c0c5800c110a00d001c1c40240e0f080319242c82 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 808992805 1106 808991699 808991707
    0x50703060b09090c09120a0b0a0204050a0b030709090e0109140708061602071203030902012d050a030f0f050601080f0c0a0e01120603050c04060807030c0515 69
    0x40700e10f02803c0303000002403c004c4081c1c22100381001c010b004041000140b211580da42c1c003003c004030744207040000840c80c051254001c3e5000c1d940020810802113081c00107404140c0c100070085000c00004540c00580c600c0c0b5440745101030358034040042151010ba050014141c41502c401a0503a80101010001d0440c080ba01c0350300f01c0504d030324000b07914411243c100c0c034181140d0000203003038a010900408058140e0310008000d40b003a201c40c0200d01120060401080c1c10300c00e6203042102007104584018421002840a0503481c18002002059003056408885010f4090180e065542d0248146c56030000c5000d40d00ca06412a808082c1c9040010b0f0ad000c2e0040c08105420f00c00c442d03c440c11140e00a4076038100c10001070008002a035600e05140c2d03034801c003000700203004504e8030601280812012501c030090303030b41100c801800c41340b80206024801c81101c2001e14900c4d0280 = true := by decide +kernel

theorem cover : BRFrame.Cov 808812949 808992805 := by
  have h0 := BRFrame.cov_init 808812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 808812949 ≤ n) (h2 : n < 808992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
