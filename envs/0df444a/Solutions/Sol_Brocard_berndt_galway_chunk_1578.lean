-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1578
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:49:12.355662+00:00
-- url     : https://prove2.me/submissions/34c2ac1f-7af4-4a2e-8e0a-0d584486196a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 283633093 ≤ n < 283812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 283634343 1250 283633093 283633111
    0x5040201020706050322080703112409030d050c0a02070e040206030a0b011206090b0906041a150910170a09080a031e060828110f03010905010606110d0206 68
    0x1801801aa03001e81c001d160302804000054810843c3d10306d907010038103a9248212190500824503000b01900720700700f80c038490302d18002004140310001c0825101d00030088140344000440303012444010080c4200c441c004100d40d8240305505001c1c5040d40150700104480005014540d004161641007203505406650000c04150950b1211400607005100e0b03031100c00d040c0940000007000007800c41c02203400800b101c1400242407100c0300c040c422040710040c480c0d403007945403a04c51201208840c02144804400707803030080c2c0450418420182d41e21400e10101d6000c40f500c40f4415487d503014501084d21088074440e14244d40b01d01c07000c14107403042140000c0510341c2c18060100c801d40300c0d50203048038094940e5200e42c04d80012001c03200f00d0314103401000030b54001076003951403240700d049034071542810110301c40c1e407528041c0c807020048031460450301d00c2809066014800e548c0c09401030ba010325005802000340a80e03411014002c1c50000001c4036880c0036445071a0a0a40040760141c0300d03103000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 283635593 1250 283634343 283634353
    0x4140309060315180103060203070f03060506041e0e10031502070309140102031e0307030606140706020f040e2502030406020a0b1807060906020106052d030c0607030816030504020102 80
    0x9100c8883c1500503860420f03800584403541500c8814410074140e0095008120060f500d00b04840020000d2030b04541d06010305080c04010803142d102c150840d0121508054180a81ca9007200c4040c4065110f0f800381d05480e10100500c00d0001c3c0d44101001141d219484642c1c0c1110100c15550581c050840054042403070780400300010507038403000800c102c1381481500d1a207035011140c3c150700b8020310031035600902c020080068883d003511800014010f0785c10600700c150b01c4841091070034403074124018203032a000f00d40101800c0100341a035003d0940c45181c54482d1600044e40f020314140410381000c4c1c402600f9000c100d890002c000c40d42940c0d450340c040c08103105a51030380400c00c003018040c80019182c0d00c0e0600c204c01c07420b01080c0c000d41100d50b55501013501e04a402030070340d00c1d61341069201d07a81c00078258603042c415540501030394810240c40340101c4400700000341400313030011206e07812840c0001c19004050b48214021707c1007101c04440000b11910103403c500b11001200c0081c056888 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 283636843 1250 283635593 283635601
    0xc0c180f060126090606010c0c06030c0318050f010b0604120206030411031e0d030510050d020d060513020a080705150f0405030a0c03020102100e0705011409040212041403090603 78
    0x1200111a408807040c10401c254125140340468100424140c0300c14440300c58092009541c800d001e11034000c0e0091034410400c5c0110b03110003081d43d4a40c807a6405050f540e0781000d0340140a40c00c4000c08039807400402c08441c0c85820201d803610003170107250025510307040008402e4580002502c1c103445508684000c00354155080c06041d030310280c016910b90003280d0600107d41d60030800380144525907680301204c0f4485c4800c5d18a403014190400c4241810401007046408455810000321202107a01820810a03400881c88081801038041e105500740810000480f03141d041841007188240e50346e500c050350344d100098440211703008050303020a045542c0381001c008003005d4001804090139403403030103a0f1840081d14004a902e4215445403558100300190341c0c0601100441ca00280c1c800c0c405001c16000c0c0300e441c2d58150217014180110a6508c0540641210684941d04d101400841d652411021034a64501302100c04a03880c100352000404116004410340702e94070742c0034201d641103841d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 283638093 1250 283636843 283636861
    0xe070501030c02010b09010b07140c0609220e010e07120c0b09060c06100314010b0a15120f060302030d0215060105070f02030a060c020f15061e10050c0c18 68
    0x90b0211140c2150f488a810710750b10368490203018001c05000300c0e2150380e0310151601c400c1280d64404500386036000341400c014152035071300444005444c200c1d60341d03d8035610b072143c5113858843c42040d548600c0ca04040c40b14400d030154441400c010201044401d00c9545680341c40340261600d0000b002140008020003000031104040c0c824003000510f91030900c454043d015244c140121241110601003c8041003844009005110000e030160002c0c1702e180440c1c000718120f1585845880420300f0483c0900000724415100280700110301c0c40103202c105195690a00a04000d00050388640128815080c6c03160001800b149102180c00d8000742a44d00e0780019289a082120181c492514403148070340103035000d215861109124a1001850300642403000740313005040e80f03100101764040b0f8511003a0300440e003289584458111034002000e4180b00e4451806202c001d0440e8115003080317170350000d041d001070107800c40f1040c00007110340c45060f036000c01c0750581d0021101c2e503c009503d00490300a42d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 283639343 1250 283638093 283638101
    0xf030702150d02041706010f122003011e1e0501150309020402040b0a050717090607020f0a0302091602010e01050114120c1513152f15070e03010e07050103 68
    0xa40c2c00d000c0141032668a0601c048040c02d5240d00c4d188940064006110080003054400058444942c00e444150780a81e9a00450515441d60480d5031443e202034070050340c1d09400410a003030f5a0460039170815208c4409002a2007090740045411000105100d868400d07482928100c1f03161840c0045000c000041c00e0740207003135440c0140c3e006030f001c00000c62508113034802040b2882c007603902c440e0f0700d8255003404000a00459010180c0030030030090740d0142c0e910b160540b0700840c0c045810210119aa000054a20f420713a88000c0d0031a03001020802c0329042c0903200703100354240340c000703100800f40c00001074205c030024007820502100080380340c5414100001084401c1e045039044403030081c2c14100081c0c0e95240031044242d90f0b14000740716001c0032142c8000713000400045050201d8004c0981d03010b42066014507051100410180c11181003042000003044000700785400d407400f228030b5404070304044a04880c400c02180080e16840c5550905100345550b100c0c03d51301502c1c1031420b200044000e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 283640593 1250 283639343 283639357
    0x80403030c08040f030309150905010210020d0608010e060f090607081303030e06012304050405100908041203020c0901120f1401110c0d02060c120402040b010c05010c020604050f03070215 82
    0x42c801440301003162000340c200310340070314001d4854841403450040340c4441d1001c1c9508800c01c0040c800030821103a60002405003214085540260702c40344041c0c001d200502d501da00402c05582800300440d00d0000c00301b960f03405a9034440c00302d03200c0e503101d0308217a580c2c400c00e03030700c0e040000e40320b80003e010901145660038205100e440d0201e44c00204c0310446240404c01e0b0003482003502c80c821030705604a81c5000140407070100340c8040c802d0b443d050703e800d0b4803440542003d182d072a4031502043c04000c108012180038050502030b4400d0400942402503595060400301806542c0410002c240c2c0318141604501050f0301c03c140701625441561038040f029000c9403442425900c508045019050781c03070192803070106400041080b203020700002441d10901408105a01d0410040080c07503003014104198000e4050b0f50103c2e040f1030843c012a031480100b01c0140840d443c14481c88911540131400c6030269020300120f80d00c030100d07405810384030700c51408020b5000c0d418003100380c0d55100c0c3c1c0025000b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 283641843 1250 283640593 283640603
    0x8060f0f04120c200307050d0503031611030a0e040506060306030c0f0f0a0303111203090a0624090e06061c0b041b2402010203070e01030b0d14030405010e0d080403030c 74
    0x101c030095540c100c40c103400d10f0042c5820040d0754134504d01c181410407500b0000c10040fa12101d420502d40c0741c80d41c40c0c0c40701a002c011924644010f5060803405558a072540b0b2906c0000c40355243c3c41344074014541186131604903c121b090901003405468824113413401968001e0245c030245030584108001c102d043d0a1594000b01400143c2c1b003159100003403040198001e44541c204903d01c40c801e503040181100d04c0211380b01091003400001240001c0b0104016804400025401e011891500b403040140100c0d9032010b860020219102003190090303251038145030200c580c1c036118041046100d81d04c041c16032800200f00381000c40402d06907101f85400c540205d00700840062101141102000c6a0b0020559411240c441062525000681102d10741582c40210300b035080030070009013021060a6654101900c40c0d8030741c016507440e1b61351407031030560102240e119104d2a1890316202d40080c401c0f00d010804440c585189414103845191209500c00c80701803a1905550302542d42003a44c20702901c07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 283643093 1250 283641843 283641857
    0x30c0b030709150f02150403140f0705010c110d080702120f0d050a23040b181006230102010204120f081b0a0b01050f030703031b0602040f08060f0f0412 67
    0x1070340700f110204040c82412540c0e11075010020090700a8074050011000d101181440410000882d6100641c104c91035554034601c0d03600e0302e60b100c2d0010103008259002d407095190900c400030b0190011200e003d07281d00541500c0c80c6091000381550500d00849069001da040940b15185a980e200020000c100d000400d0b0740c103050081c1e80c110100c2d0705c100c501076000c960700c0c00503440081c18407090190100c58020102c0241c9001d540f140d46000000e415045e24501c01480b0305075641c1e0501c54580d072400400710400039666580c40c1103000c940000010701e460f00d000907855203a54818001c0314242d40d09032007010701d1440d16a985024030348901c44281e804160a00c000c10620302c02d0001e5001d154030810051880b0300741390800031030111040e070250b84550140c003c0600c941c1c81c081204001c80390103040140e02e452000500c031b829903803c214001c00c105e10015001c901700c0c291001c04030030750328101b045440d0f80c0d5560040c0440c3c110b080c0c840440da41103d100090019a10100e10b05480703915181c40c030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 283644343 1250 283643093 283643099
    0xb01090209270f0c03092503060519050121170c06040b0402091008060402040b03071806030b1503030d020d0f0203010b1b030f090f030c090117070f030c0b030709 71
    0x1d41030b000c0d07001e0940d0000540d8400d000240c0301c07402d010342d00218034043e81459803c00d040c1c540c1d5108118000d125400008203e00c044a4000505903002950840410310061600844180160881c03500304508030303140500115a004200382403491107042000f0b005a9400261200100e00c0800c800610344800104014408114188403072809184a040e2a209034100341c0b0410040e40070082c0b584000060031002007184110004440b0f1300181c041e03030001030312112540132900342046c40c0c0049628080c20840d0409a030320551105007164050300b2000c0290716802115000703003100310640ca034140c1c000d1220f18a0043e150740105003410140000103001d07000c01080c041641c1090340841c044440102e03040080d1440001c0320384a120081018500c0d00f8420070807044d05003d42100d41d40160600b0206038160344040180000c0c115000305169855a50707844d0850015064924040447c0150803001070b40c01c5030100c0400590354000d0303a004010741041240c407070941000300802d04201c0512400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 283645593 1250 283644343 283644379
    0xb030a060306020c0a0507090c0f180506041205010f0504081207090503060408040e0609010f12170d0c020d0215040b07031805010c022b03021c020a081803070b01090209 74
    0x2131480e6118034003c5e0008200d5800e15604240785984040f000d1030605880e20300380d580c01441c51070110b4182c01c0840d07000c00880b110084032140390300800d40060b000200860307015800d92140d207400744500b0080c42402c0c402400103082e40c1041d900204090340a01c03582d100d28101c41c02c4281e00119929010a0a95858000034030301882501c00790350205001905102459411740711661004042d62403c140d5407400342600452031451080c079809280402090007000021600c003107800f5078180c0110345038044585010014404542c0043c007611501003c403500e2400403c414590220501110586da9a6070b11103900c0c2e20002011042010394420f40a0060102030444e004c1040c05180001346d480302081c0040d280400b01402800f00440102c0d081e4040d0202280c008451811450056120603103050010031040303103000201d190a00204051000c190f124102034452050307200204c3ca28110100450780341c1c80b6040001e083c8503240d6005125031412038000f0701e9803031005092081039103101418 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 283646843 1250 283645593 283645597
    0xb0d0b19090f120305092104032004060f1503091e0507090501050105040b0d020c0c090406050402040f0216030e0f102f060406050408090916080a020408070b030a06030602 75
    0x1c2280c0d4880120902d600707200386022080070b90714080c10208414200203610a0b42c45120b08100b1480d000c4180000483d031440105540007591b102d0442c00c02c00c40244005229540c501040314080c03481c24800088414207484030a00301ca90034803030134002c0711061000314003402e100801500e289411500f908500c00c405003401051500030300c098900681054191400e0f50010f078403050410074148018041c2d80c5030501116994044087e0059841042e450b405040100014107039074007856840801c42480740070b8018500c5184220750410560600060a800724000c002d8620859451b5480180010340038040401d4074001c014000c0c54860300000c0050340c054000805e1700c001032200c0740300752070201d14540350704007502002100d880d800485000d020f5541c10020000b0300903580792400f00e410f00c0300c90000c6409003c000380c4a408280303080b0038000490101301c102000010394000025032994100c0c42a00c0964080d030b000750620b2458010918600d03007018042c18402070383e42400100041603840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 283648093 1250 283646843 283646861
    0xb1807120605150918010807060309050712080c25091509020c0a0314070b04030f21050108060a0902030c0d050f010608010b090703020c060604020a050702040f0506130b0d0b19 77
    0x491982d89009a009100051101100000d17a0098810040c016083c0204050007991400d2030005285200303030400a282054a80c0103110030144181503505000940c402480012503d00484540e0300f50160b8850788110f9041c48440c03034441071141401868440e1304400702801c144445030a0542c0c8806e00b45040341d02900c40b440d070581c0002210020550048a4008041c2810088504040c0c1945400621203c010002402c10514405103800e0b603008003102c220403044640381c010519024071080c1f0003002e003030007006000d1140000081e040c0040d0300400f80e205074040c014008440300d003c24406e0564000908441b5401241c00d21019400309100d00c100511940c0d00102c6d14000741024040b44078409040301040600404c0420308100d00090100d801c00c0041e0360042e0358100c0a101242c0780c1c055070707200a40c81405c1c0f02c0707101c5120b80140c10003070007104121000d40a0200328030b000800c455120b9a00da0300070500c5007010740481c0382c0d07205403940708001c0ba44a400c1141c0216080e802c03034891007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 283649343 1250 283648093 283648129
    0x30e030c10051501031a01081f06091a16060203070306032109051507030f11011401050a050d0f02040b04060f03120807050313110102011d0c040b1807120605 69
    0x10b8100078040004039000c0015040c00e083c2000445020445c0b4201d090f43c862803241484142d03c0481c81d8044401076186c4844244d0614011240d11070703800514440d40d5108030440140d02d503440c6018450204120790b011403000318109000c2c42c00b0ba40c0d800207500b006006000745550384034004045040900301d0407007813414014140508020602c00341c00300b44141c01542c0038070b9a402800d08070000b144207c03214079401d1704008001200388101190706c2403209403142c016508011004400b503040300c07034140c1a900211400214240c82d8000d10499a020070405010f402000000c0405170030541d200c0e00c00d500024001060060b101d0103c84000d220f60741c011605c2c03818a24680440e950307c100c92581001c65480c007039145080c814130810382c818040f04041e003103071152030f40040e29030f000b5409074495001805074602c0b100c680500e00e40c4c83d162a816094015400d01d45000c0003482d0400c90752a076802c42c514603020381c0c0c0b09d41d442118404440d440c540440340d0303600c00108640d81e8051001403000260 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 283650593 1250 283649343 283649351
    0x15170d141c0212070207050904200d06020306010908030c0a0803130f030f031107020f1018170c0d03170903040b030109061d01060801150e1216061806030e030c10 71
    0x3c2c184083c60080c1c024100c4045400100301401943d4548046640107900001860040d10040213621448104810802e50160301c84091100300301054000e148145070980364012070aa542581e04d8607440394514103984c0d600403074486030000d16004099600078108074100ca072204403a0342c2e8500c419001881c1940031601141402517040ea06000f2420700301e0700c108074681045a15400721b0841c140d64080144905101038404d1071151042e801c60b40906105044c0d034005170b41d2080c3e400e030b00141c0700a0400903405207108000036800c0031242d0080165041e500d1402d542031401c1046003031000600940340c00d02081000003140c05605014501800300740b080000e00d80c2c03070018062842c06081180760012042400100a00b6401c0440c40341110210034804081d000303c510122880345614540541c0040c070305110020720800090102c02001c0840701021030542c9940c81640e000450902d5145090b44058003030005500c241c0000c009051484112b9007401c100c4a11281405a0010303558a60742e070b2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 283651843 1250 283650593 283650607
    0xc050a1703010e1005060d0c020c04060915050909030304060c09030605090d08070f08040b0a0209090a0605040506010c0b0615120a0506010f0f2003040b03090115170d141c02 76
    0x488180c0d604200b040600d13085030761820010601500481c24090b4038203984510902119000340607a4009034002002080f903152140b02c1d110003000100410600c0002240c4041010b0820008660040984800460a5130796556468000d84103d82c060303400c100c0d40b5500040020a14003e541c003504d0b181e000380c0311901c003042009003516402071901007000308502a6440303447e000880d540d0070035044200c0512507500c0c000d081000e0310412103007a80048010f400c2003603020701ca921043c01d40d58211000e00880e10f400e001126403050300e201c05031988448034041803052600204152420140300101402d2002c074482d03132159880200c49134150552110b0400c041580d0200e203a45540716103040490140020743c900428030b0445100c400d240f8040304480307150b0000d0030030550307000717141c00010305035280341440106000c1d001d1147c061000a006400215510141c02000f0741c01b0740c03040c801002051400300080395600e500c446006400072003006100d54220201c0c8117848281c1301d0010159940e60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 283653093 1250 283651843 283651859
    0x7050f07030b070507210306080a05030405031005100e0601020a0b04030e010e0103021c11040b0406090e0a0b062502150406110607020a02100207080a1505250c050a170301 75
    0xb200404001c1080010030800e40000d9105c65660803c150741178042050760000070080d0020162504400424030840d04e41d1401c00100000400903244160142c40130001d087e803507802a281d0941c0d01035502030100740b05200c05c807c21602d080d0f00c00d10500c100c5104070300c141c442800d17889041d0703025000207800310f070340408a580101d51008404020b207001c40c54203620001040c05410030040d270140464840c84142d00000941040d107000e4103030003405550b1240c1d1070a014007440e59a00c030310403120300050f0020310202d00030b00c01c1d1102c20602070141c510b0104800c4052140f40f07003d10b508052400400c0000780542c80701d00300010240300c1c880c400d968450901c40082d02d10382c2040282405648024108424260b000c510071a03d95030503158406615044d000507420008607801081c3e1612452130031074203004140800b00c903540c190341070400468a400102ca15510394083c2c098070000400740800282074804e0202e40c141340c0c000d0301030320401c0d03106940c0c0c04200030300710030407846d804008001844110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 283654343 1250 283653093 283653113
    0x203122802090906011d210f03030907060318080319051819020f061309020307020c0406060f02060601080916030b0a0e060717070306080307150c0201150b07030507050f0703 76
    0x500b400c05095410880000c100c661208030b560600640c0488117034001005005200e4103007c0851042e502d403588402e24155481c3c0040340c3c138501c0343c0300b00740b40060441e000380b00703564034426406a01008952143c44040341c139030018040540303410110a06461080851141d640640180c1e08030b02c0d014041d0b01c45892420029038403209041c3c4046540200580d903c0465004668007074031415200c0c40241075907003480c040e40d48050354aa00010412800c1d660200e003140040008907000c02c00c036a01c03844200e8034040e0250b152130241c2d02c600f011400d20340c001c80b00c540d0b001420030100d0381c81d02c4220300c400b141d44440381c0c42101c14030003ca0501102d202c0501880d0211550303440108001c0c91300540c0144400d0b07140d40307020207005100d004079044a00c29000740e03001e051401304603640c0303040c41d1902c2040008c1d0b2440d450003c51511404080c0706206000701c0405030840083c424115042403881d41480d13120001c12000d00a0400080001a1040c801c440010016030081c140503450760034110394107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 283655593 1250 283654343 283654351
    0x9010f29070f030e061c09020d0b070e0a0b1903240e1008010c02030a0804020303040504052703090604090b040906110c0c01092d0305160303021c02031228020909 71
    0x948414802c00c0c02406c480c28095034602c6800700040785d03400081c0003141c102d480d50706003e00031120900c100203406030881a495062041076954440e4075a40d40342855041c00741e03104040d50804403d215000c0240720790004c0b40005000c92400903203218060401c00e40e8806070b400981e080305c3c403800b040200340c41c504010008202d1000240040700c03500c080203481c0e1041105540501080d04081400d6440c04c20a80d0050f1002520070401400c14270004881d02100040391001005a900380d19199040071042d6030615401a242c00e042c10704003100d940c09885100640c940055481c2940004141c45004450807240003a4103955207500000c1c0d0ba50805040d05151030500c209160b0401c201c10f0342d02c445400d4043d4020074004901d0034140090004d0115500c05482445a19114443c0301200600e03001241e100e0b40031036030603034800607081d11810307900780c0d0100c0960030600c4418080041b07800525400b81c061400c03000e40c007951a513100e880418240400800765800b140d15107081c01d081c65404c3d08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 283656843 1250 283655593 283655599
    0xb100509012d05010e061c05070c050d0c02030c120a0614060a06050403080f0309010905071502070e0f0c0a0203040f09062d03110a09020d09030e09010f29070f030e 72
    0x20b20342040e001820b0341c054035036070034000e042c001010200c1880d00311206000144410041c4114202200010306452040074140c0705400342e8013240c0ca489020f1105000a590701401910014840300c0030080d0459224552800300d0260f1101c1e03200003060342c0b10b0f98105c440b1000e4688040e050100900500c078070340360080c0e0144642000144041078924090311401590409801da4a90b2070b02e00d500c1c003600800c1c030001c040340b0034090003041c0319400e48a07a1940c1d825607400ca0301d00540d04c580c0304035460301c25515404104000000708540c00600d03002419211840c1c011240b600da60741d0401044065a90300000c600c1d80c0c0d8080c103200c09201c1c2c082000140b0f049901c14400044009020a61a0800d101c0142002d0190700000359070b45410100100a05d4a40021502e50141e0321444000c0d0080300d03000c07800503901c2824019145401940c182c16212800c2619400038281011210b0840394203411070b8803104001d031018040c59040c0010100d0610482403124040300790302d8050302e000c5c4440040c0388 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 283658093 1250 283656843 283656929
    0xe1c11061f060c0c151713061503031b02010302090a08210424180e04020301050105060403050a1b03081902010e01050601050d09081b030714030906070b10050901 71
    0xc10020340416041c1c82c4d034000c0c0c20011004285060710f0303c0e600c20f0707100003083c41b00c5001c00000a81a960008403140210010b0120454505a04500202c94080103003c81d0501e4180360040e08142c003800c074000d1040c18010300e8035101c407000801150440c2d010034042d500120454090a00310b070f9201c401c00800f0381c030490403d400c001805850002440311009911580f442012002e40b0820503844030003030041800d1070854032280c0d40541d0060840e0203900070740c201400051242000c004841c2265005000b40c848000d131580c3d8080c0e1980348502e0151440d0b0340b941c010011824090017030000c408201010100c408400c840070b400d451500c145601d09034941400c120099820204036507450703c1c2d54100158845003071400c0080b5010b51b403079038580c031b038040c5072107803030f5108000020080c0500500c4480c241c0070550102959912410240540101c4240060300000b44144001ca4201060030b04002c8150b49070350126042e050240d01440520146c800c20611242c4c008401e42542d18103484640 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 283659343 1250 283658093 283658117
    0x106050a05010e130f0e0f030403051525080402180105011b0804081204030314040f030b0910090606060f08041208090a20130e1c11061f06 61
    0x5420406612510b0b040c0403102824111a82c0e610001440d00200103404002020480c04034800500c0c90204082403441210009500b0520000c00d5504495000005000010354010170b4a203c480186c48070104143d45078402048000902001e403480480303076a032076400e28150041181d0002d680c0c00c221050010900103110903640110b030140d04039000080350180b02594a840c2d11180300700d50050040380201808410006a048024800c4138000d55400200320384541803801e1510030752042c81c6034a10142c0381000050401d5403499807001c00602900e005088854683e4207441b40500200c40c40d0390f0702c441c14010a50820b03240b40170f400700c51602c0496450207507508440100e021380110300b80503014000440550302045040c2e04e1340d0b07200c180c0e070801c03103030001c02030340c4003d03004814521524000d0340c41017001c4014412503029560b020000d05040a041e0162400040114191420010010206c9440d50410480540241c1854284608050502403cad1445201e144c21010810104140c94 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 283660593 1250 283659343 283659349
    0x90b0901020c010f020a06050103080904050c0f03190e030a03150801090f112403070e0418030c0201140f07020f0f010f03271a0603010e10110408070e010602010c02010605 75
    0x1d0120042c080c01c0203040302e06505002e074609640140003d04580c02c09001204004102c40075241000c07055805118076140c9070000b41e0389001d2140003c0704c4600c24070001d06c04040a0105000446142c00c00003803440c10805024215071110500402098442e401c02498800100c00381000300f254000070010030700c00780d82c1c0c1501c0c2c28424070058402520351641c4001c40e507609800ca408208c03800107028680d5100c481c1d4a61030b80040b40c4d040046030780004810003034201805242c4003e40c000701c1d41e00c4262600c0d5801e444020b000d0303400741d040000303810000c680c034400c2d54000d00c416907115401549419940c410030a10000e40d050490242042100150090f60010481019580c01d8100132601c1e40e11214096900781540484100707000c10002c006091155142a018440074410348041540c0d84a100f4982a52141085894158080e00d0100300380000f40d840140c1111300d0f40003462906030740c0e1202e40d1900407039810410740303d03070300342d0042000903024851840d84064900003030140074940000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 283661843 1250 283660593 283660603
    0x6060f0312090f1305011203080604090b0609041104050a060f1202012a020904030e0414070206010b0a09121208010f050a0506071a0901150905090303011e09090b0601090b090102 78
    0xe05000303a0046202e281c055070b0f4400621402c4c15500c004010543e9140032036880404508410303804078070403102003402070070a8081c40d00b1040e00458000303030320f460700c00c10701c0400000208140c40381e98501070303901c68950700c03406058003581215a021a6040c01e00c904441e410101d41e0160511102c0204d6003130050340c00142c1884c3c0d103162401011035001c1c1c01c4881e5504240c01100080d8030107810700c01c0008040d080075103400d80030000d03101088494204200c001c004030040d1822000341e805140100241a4042c1c0241754146062410009803503071202c071b45c0c0c8908030610088510f42074003a42c4401c440c6e44111359a0041103150310008140345400702003090480c0341d004283c01400001140400d001ca0310392001c000c03110f04a400c3c005c41c50070100050013071100450203204905c0c818400105400d01d40601c40c020703503404001c0c500c1d50346091954180c0d85051904014003210105000030180341622071050320a002d840a602c0510f010000100301408603048400a9030041c82480000d9070700181d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 283663093 1250 283661843 283661857
    0x70b091507030507061107060507030506010c1103070b0301080706080c0a0f0507020607080c1005010b0a4109100f050702010c0c080703050102180406031a041502030906060f0312 78
    0x1800ca0390341c40040c20125910f04c50080e024114600340014101d04098000041281c1c50140000b08499110028118255042500c909002130141e088038800300309500c0581c0c030f5042c2c000301142c0b07015a072143d0707684254001368041c1d00c0b107402000081000c60703002511940d00c4030021126501e015106480600f0b418018401203080000100e00f100c119210102102e41e842d030031203100c50322801d0160040b80c0e80e0000c041b00ca03600908140c000900c040384102500d51100040d284c0c04d1440002010181d8080051088030007514028070b50504041c00707890000010011140e142a0313103401c0c03402441401d01c0e8071030302c2d07804002c405100141003542c440d050310517841e03091a0002e080380e402c0c200350464060503000140540101d001c0042041030560003006204807002120240710220b40c104022030f109484090806280ca03285448000c0e001401c3d04e600c10300c150403948142503400055000c9801c112182e810307640c072080031b0046a00e0510800c1c40802c104800a02e00c00b46140651031041c05107070307 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 283664343 1250 283663093 283663129
    0x20a0b0c070507052e0926150c03010608100f0605160c0b0c0111040510120e030703080403081308090f0604090203070507020120150604090f05070602070b09 69
    0x1c241e030340410900b404900004c02c001010050041001158124580d410001080b0700b00c502c035100d00d9005001d54280c2d0222001843c4100315880380b10003c5d884850504086400b0f4090858950411455044194000d0745c0c0011040d0301c03036060050180408801030703c00d041084c1b2440d000c000802424900206481d000e150143c0c0790100d21503038508980c503401000301590040180414aa0451005080f02403038490090040c040e0a840081051045010790703504490305c4a000d04002d4086c0e0001488411141c50000f20480021140c50850b005800c0881c00202c13014140000c0c9580140002d40118100b8854400d42e030b01ca60302c203030581c8124407040e406902e21b520803405d6540e030b807001d80380204000c1c1070641d40c1340f034a048c004009074403a075422404508440c4220003004074008002e18a500448010489142d88080c180c1d6800c9001b00350702d52140d1142c0007071002940800d82c1d8140c05200781c0040000310b003082c10103414407190303812040d1800814440480e4655642007102450080c00e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 283665593 1250 283664343 283664347
    0x203162601090f05160f05060f0c070e160e030105060117070909050910150803030105040504020f3d08040f060608030a050306040f0504082a01061205010b01020a0b0c 73
    0x5002014054248002d0107450041d900c3c03200002d012022403200c0c103902d0b030310140c05a000c0e1150141501402c0600030550084403d00c00901c0c1000ea8100410545520904030703030159641d0507109140c0361003210321940150221000b2400603410144000300d4040450080c0003500d0803100003024500f200b9030019030f04d030b1218041004180110307003070070140c02211402e00c01403500c40706142d61180600114400549418101401200824004002c2e9995140514038507440d00003004040c040182085ea48450483c071400d11a5075442044800c100000d052481d0140700002079035600da0000211011f01c582e00d02610700019032141d6141c0c2d109900682c0300041004034280310f0000c0c00660031003040e0f4880012039046080d0084065885400121024020b65400e000400213650b0709a400410050090040d8a20743c6200c00000882a5481c8103c24800c4404001e41d400e45038513501c01c1e804000d0482240d424080d080c0121150139034280018151002d90f40d80e241d081000c02061500c0030180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 283666843 1250 283665593 283665659
    0x1803030c02150105011220070c23240f0424050906040302040905030f070f0c06020a0b0109200a17010503011a090a02070204230708070e011103090a0303080103020316 73
    0x8800b6142c00d014404c2e001f058441c000c40c5440505612070740503a0103608141800454001030380d0003806007001000d010042011075110811001c00c1c06009140003c6c50180031081c075042c0410043d00c010842450501c0110403610105c10340c03c90035a01c800200401003086e120640c48940440b02141c3c0d05850004a11406041c4030382903000d100c0400141c14000034520741031001001290403803034000e412035180c0c15581e500030385c3e8070688144014800441c0c24010061248603502c0380c9080e004c00600c12610700c50b850303000207007544086565030200710f05601040c40c01002c61625400b406065008100e03074150804000c80034040c01003c280f1900d0140c1c000b640d86110b40e01559686c503809030040c0059a40903110084410703982109a07000b07003040d400140040e00c00c00440d4040e850759100d0006503a030400046500800c1a00c6580d6288810071004410341c0390000e00e280194084e50f28004554110304c101400c142410003440b140704066801070200d40d00c40d445000003420361411144003410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 283668093 1250 283666843 283666871
    0x906040c2904141302070b0109050403180303021b0d0b16050d0906020315030c0f151b01020307031404080d050a0617010f050717011502011803030c021501050112 71
    0x541c04420519400410300080120840300707035101c1860b08644031090148891081803c038060b03800003600e00c1c1e410000401042c0026400035400500a1030040c0c00300c50340d1040410040110361049005921110f241d4582d035050003100003007030004580c0743c07c2e20405038076420742200e0040e1825821072100c251104034580640210fa489410000c0140001c07011414103000035001219403c8460700541d20400240c036003c158110000d000506400703002034090b0038004294515070400c0c289410810001c1a401ea24034028911041d82400143c1c0e00e10303008000a09546c50500110b049505403028040001c51700025544450038400c8005440e982d952803850250504c1c0d40034060109200a800401740d00c1074001d0000d400d45503600f8030094540e400b003212007e024114442e4035480100045c0a5818618540100000076100104401070b0b80401110b0140d99020114042a91021031443e00303a0140688075841c50010002c0010b50b1500300082c0001c070b505400c070290541d8610620090f40c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 283669343 1250 283668093 283668149
    0x1d060316090605030c0a180b0f1c210915051b01052401050a18031a01150503010506030711010609021804050f09031606090206070303140906040c 64
    0x20385951003108a5903690459600038041c6018a41c000d01a00981800d6810114039080c1182c1d6294002e0003550914100c240062040420550b4020415a04001c982c0d49100b4901002c01e0180010a00f004251814011050991050b800390403a007028208419400c401c0348130455100c081c07800e286a494180440b030303521504226044401690f6400c00b13851034150300c4903204150010b03102c09411646101c0701c615801150603540000c00800c0b044000d503200e014400c0310f9811080c44030410039102d9a410131010f00481485002c00c44490040215404200b003100203d989406d1042c511350419000ca1480d2200400300814007080078000480078109620500050183c000115101c04409a10241422080c88074a109074100030104541c8040000008d0182840300025468000b1402500d880940c160109407075a60b030714095000561500c00041655610954001444220301a0390074000e10000d001c0389025032001041000080340c2c0c03015241a0f5140c044020803894620001103206 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 283670593 1250 283669343 283669363
    0x1090e0c010c05030d050103060e0d020f06360c13020705061305240703290f12120a0818151f1503060e150904020105070203030c0609060108071d0603 66
    0x2486e1000000600510342e0114545000c084146c50700c190342490101e923280c10f51612014990803c2002c80c0e8184030000c80c80c12031503400c03156220040480d00440d024105921503c180e00d0304440102400b500d040030400c0c40024105004604000080c2c03642a50396100070081445c414001c01d00205101041010348600707880c0c590400107840d0131f010b010509100c15265000441e040c040d840e54a810014034440c1d594050411003500391601e8010490108800d60440e0f82002c15400910701914007401104a0490401c0109560b60000d040013081d00400401c00000604c1e104280c400d10b00001c102104059400e9001201a03200e28104d6082110134001203041200c812000041e1406c6c0084424a0740e0b105031406c022480d07450034824000300e02140c1a0220207030b100d03442c8400d881d04540072a0058018901181008407c0d4042441c60380540c8031007403940c0c800420410401c0c420071100c2d01609045001e00801841e01094030a05003642940c03000118030301d00024a982c800300120803079 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 283671843 1250 283670593 283670617
    0x41202130c0314010803120610110a0506010513020c03031b04050301060303120507080105030d0309030203040504021c0501050f131d0624010509060703030e0a02060f0a0801090e0c010c0503 83
    0x152090450068010b044000c080b400c40f103010400040c10720404402e032505040c20014030351080d500c0c07004204000c80180240c109001011a010440d1b050422204800a2090005110315410300b802c000803410040760049015004128001c913072880402561741240803510450340c4030b40c5c6218800c446025982000c2e426610380382000083c19400825080003e0344030204100320f4071303111021141080240906500356008004817103d485c869800403140c0303402407044d00d08094a440004041e40c1c0301880446900e8805442d01441301c0c03807803243d1401071600b254121481c04200f00862904241c0254000481d981c400c1c80017020007600341540b101d11040c0b02074944c0b510380008400f80982d802200c0d81d40510b01c003071042c41554020811102c10075030040286003884000ea030104c01625031040d51000b00c0c0104404000140c564801a140107081b8034045900c4001c0300c03000408000c0160f01c250407403400c0c00e0300071449081c08666901201000e01c1d00300514011410301600d14440c44c000098 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 283673093 1250 283671843 283671851
    0x60a08010f0614090f070503091612050f010605010921080309060921072901080c0319020a03020904140307050318011e030507030f02040306021e03010b04120213 71
    0x15080009a100d141038070805045407407103080c0c0c0c100b80001040d0444800b08484511703004242032134082d0001d10b034803030080300485400f246c00c07604110f414001a4040c85045076002c00800c200542403101d10000c0350b403400200695850600000c0034041a03200d8410070494a4218150191507440048000c41c0c10121155480c1418120b8039503840701220301d050300b03020301c4e480c0401100a00045412180c007074896642407580c107444402c1035035101092407001d568841d5104c9144403200c54050b00a0403000040c1500b00301c0c420070f1500f030080d02038188080800c0b020803600140d4800b07070034500341c035010b0b2480305559480c0e1406d411a01003208000d00c86100c041100401c0200000c0189450522110021901c141c5140156040a0002101c20071100c62840310411203100e42d201a41c007074550329000c0340c40c0901280c8041241c2c01703500181c40440d000600ca891004820141101907a46206c520303256601d80314011a0502035030081c004d45000d0414400159524001e013404a44140d2000304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 283674343 1250 283673093 283673111
    0x40b0f070e03060f06120604080702100c02120a06061e03080901020c2e0c030c0b100521120712080402011211030402090906070f20010501060f080901090206070209060a0801 76
    0xc0c1913003401c5030418414014402d151482c40b602007050360145030b10402c50380c205250350b4200003040e08000748a00800c420420030070090b03a20082451003d0628002070400310007a03086c21419550160400d486020003100081c04044400251004a07604404203540320b00003003004034100201d03000c0c15903008210341029007a2550340d003980e500b4024810036207001c1e02507903801541c0e280d800076009404168070004400110300307140c6005a00015503613030405c1c503907142d074005002d80c001408070382410b859840ca030443e810b5080261040140c94101142c3c2001b1559903801d09540000e280582000501c0d40881e085902580038890350b11110b4070240300e099142c01c0a50b04680045505902c074200c540042041008082612401219565034241400c0c3c550031040d9848a40455402240d401e811288025000280f2410f0301801e05955516048044542c004041e6280035141c0003950f45440012401651407808031003840780d051341c400950350ba8000000b40748404030340c005402035007015011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 283675593 1250 283674343 283674361
    0xb1c021801080708010c02010c050306010c0c0b0a020a0c090501050d02060f0c01060909031206050f0d031b030816050a08070809010b0a080c180c040302010302070213020a030c08060306040b0f070e0306 88
    0x362003a5040c400c001c0050300c1c000c2c51b00b2400d0368035110310180890410000f20350254403c0ca41c00d61582d010b1146625404d1713581c8080c02070390303100c0381d890801608140710880410680c42601d0000380040036051202d941843c00090009070700b08002482481c002810516030310143d4241d402d611200402002800da44e400700c50050241d14808130005010044201c0c41c1c2e071007034410041541c3d00908800c40041d00d040900c40b022007503880507818001041c0d4600760503820040d5410950303100c0d65500009040044086070f40c1a454418482440b00070b009961880350b1200c20343c1d501c41111310b461030858544012150041c03101c00c2c0c0207a041100303c5808505820002442d140c004004e03954503018041034052403644020135501d6540d440c108000c20030140d0300c00d40140400c94001070101c000303503080c00c4040d8200c0c5d0191890202180d103450060200c030303030080320b45030344000141e020b480311b03141039992404840001012030380941140320208840b98856003062034100405407c17264030b070030540d0342 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 283676843 1250 283675593 283675603
    0x607090302010323061003060308130f0b1806070c1d01030b10050d0f0c120b1506090f0909071206020c101506030203070c1a04050c040b1c02180108 65
    0xc280d01003400d0251240d082c1d003840b46808100300e050312000b007260b2107a8041004015204030030208054842c10080b021401c0000101402e005072841c2d00caa0914000c07603128022640da00c403c0d1107503c1400b03500c84485e0306030425038040d24100c40982c3d485481e482c050f0075515007904120f2040000003880d00b810007010f4032807416603000c1c00c040940c039602c8001c054a0b030940c0c0d004090f044001d0910040010b00c1c0480b034000d049100e806594181e60311040304040f8810a948180c880101400c240541d1100a40c2201c0e044002521001e14045401d0046889409140b590720b016494110020311a607209022441c0030f000015900d440402050511601a422880c4c034080340d801102e14005900f601d5100d210103540030180a40100351074190141d00079003005103181e09201a6680381c00000300d00d51030103440854bd0790124501d9042c40c1c01d2841c03410f071a0039200c030b00403482c2c02280103699548030400b02c4c00e144512000c40301c0c40a02d101003034140c807075840c2034040003101d4000801e03014004a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 283678093 1250 283676843 283676849
    0x2060405060a0501120b04210504060815150c0a15020409060b0408060c0d0207050a0c0806181b0411030103030806092406070212120307090f14060912060709 69
    0x10460780e07141c076820040c80c2180c00a100b2484484480d03940c08001035044100d066100c4d01901c03466000411800d047c98850100070300f0100000ea001806110150704140b41603004007880750210104200f120204510029044084483c1013011406c44030b00c000401c81c0b000b15680c0400d01410010101d082c11000e9000340c000e4410756410480e01203440c07000c2c881500c00300c484010040c80f180d00d60703020302041507000344809030955400300306003004118200150f407151440f803c039010700a031401c44039604040c80a0001c1070003c510104040380c2d0540002c40d501d8400d14081050481d041003c002001045100ca415030034120100000042c590442d001a1060106507003070080c50b03503020101990542ea0807000e04202c10000b15550302410807601400300c0920140100f00c00c10020807480d80b0740316101c0c11400c415003001003004919603104900302c000b000982103101502c0d00341420341403417005814803540580808180745100b5990402e5442596075008182d034a207050140b8018003000040c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 283679343 1250 283678093 283678103
    0x706061e0605030415050403110a050304091b0207062106030b04110108100e0403050d02030405010b030709092a05090414060f07021509030d0f0f0b04060e18070312020604 75
    0x1031000a00301d4012802c881c800e5a110022011a00294150a000b0003000d4010b03001c20194002080b200e80c0300300000705d0b81c6800b0780000d5403290300c0c04825500380e50540620301103140c100c0e001c240082c1e4000580e04107495450614800600c85c2c5801c084441c400c0200a4240a0a0840000600c15131000c02401940201590056044010015954039106850ba03207100104600c081100200c500781072a0007a103c2d14281c4e18140c0152500c80c01d9070000d42d81652565900c00c4070150503d0b04122003070062940c131030f06001c4d000d80d0351a118015030a0120355841c0c50705d410380d018500008814004050300e0010240d03a082c0c100743c10721504450800d80d40b41000d101e080c02107007448410f24411031143e0354980c014501c04e6a0402c50b44032005001d40000b02d05c0c88180203100042280d40940d01820820340740000d2140c5076514808180c80c20012014040c9140603028420100d012442c580c1c80100c0c0300c02e05d8410460403461928080f011750001e00b50500301d648000d101640400c41d90f000fa4050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 283680593 1250 283679343 283679399
    0x9051f0212130306150e041202012c010b030d0903110604050415080105070302030f010b090d0507060e030c06040605030c0313150603060506040c020d0327080702010909050606031506070606 83
    0x750805170302d042c0226801c213402e480025000907020281e84490194a02c004036034445000010086408902c040c0f000007940400d00d1120141c09228105104500b03c0007022204440d02014000c1030071404058003045182c1000d01030f645500040754001e0902901c108820354000320341401440203802880030310750920313001c541014807034000d490255007007000b03001460b440c0603e2513045070701c110780c000c0d0440b00f5004200003242c0c051012038000c01d51621410880c580d42c404242c2080358441c5c802d0301c00d41c000d010a02180354440700703880d8021070b03440c18181c2e283c0351103010a09010902100402c000c0890030508080c005d1a0011000c0380e06c600000d1000d600d0342070030001039034100684000184c2c000004100114826002045450310b55007011100c19010076140c101e4000d443c1c01960000780010b01e040455074410001c03001400084c101304030303034202480083c445120241c00444a0039401c10289626581c1030200c0700385680c4014100006942d1727191004c190305034120440850810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 283681843 1250 283680593 283680611
    0x301060801060f02190201020a0c090509010609111803120f13140d02010e06040503060937030509061c1b0c080405090a060f0e04021009051f0212130306 67
    0x1980c0f0800e034030101da402804807900c41e2940c0ea14035481000050741107114545003540400c4104001001030b014820b00418986003408846003564003e40c00780c0341103441c0200c1c02d00c0c02015134081d10511800440e40c0b061000c209070000b803503e201e01114051034003000500c10381782c5401d1002007034038914030b50039444220794035029800d011586400258002c0d03012001e1400542c4119403040e40042c0003030200e8103103922900840d18000044401c08030035440500802441a50010400018016210034a24211481c0030b407841c582c243e13000c0282840385c00b1841e440d2694443c030958550283da0b03940001e41d045801e050002800c44210108000268241c0010740d8600c00d00700b03981000d400c03c3c1142c0c07138a854102030000344200101540754850752243d000c01c200e140c28901d000101880201011710f42094010842000304400d0a8414400d0401080155448014a03240190ec5001a841280100c0d450590800403200c070b082e004a64001010540c10705001d02e0001981e0060f84208180d601c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 283683093 1250 283681843 283681847
    0x80d0c09140907030b0301021303030309051b0a0611010b09070f090602061b07060b09010305030d050a050f04060b0111013b120d20030109140c0316020c03070b030106080106 76
    0x451040190008458000244010700a80017404038002c0039000610301862541480300e078100541085001035102d40b079034428098204021794608041c0303d03030a101e0392401c400181c0407910034803c0c5428003007941001c03500880c2c29804102c0c03201000c4c10b03101da180782c030350300080c4014040d00014010640780140464014400503141c0c2c0f195200003000c1c558a605c40c0b450aa241d00900c400300d4480e80c80f100c5161071a00e4000c0014002c51160000b1034481d500300c062001650001444a011079240100f0000484100c030001a007007a002080018040014001210386481c1030703c0c0102c0075130030003098814521003010110f1190070b512138a00b16030f2074a11550742003409007020311f00a9500060014054140940040044400c8584001010404038003c0f41884402e0380741080301d0701c800300042014207540e0140b10030716803114160840b1882c0400710354200780005000070507a10300c0440c10a441e130340200040d0080840c001c007282d894584e5105001c0342903009004240004060b4000060107034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 283684343 1250 283683093 283683119
    0x210111b010c0219020a080a1a010b07020a030b0411090103080301080c0f280f0b040f0518010303030218090c07030e030a08070b0a0b190602160506190507080d0c09 72
    0xd002e56014144001060140762480d003d031500582c2d00040c0c803000011811001c0115403c030038400d002d0381d080c813402c0003503a8401c214141c0c032000301c4c41d00811106005036a0664034606403944410b901603103807114103000c035409020808142d00011039000100a00100d40041c5040352041c0c0c0407103020940756024040440c03c4004a0750b00166000002e0078a100d08503c40701e1403003061604500310a5803038100c0396a200180e030110101070f01c0058140310320300d00f0301c0e5000080c0100341e91000e121050100d108000ca00e0510014003010350102d5190141c04480900c410703da00c0003089000c0c641002c008004680c0d1000c00e0490114010445002c1d150401080b080c4140c1d402044c60381c01c20f1611380310000d04590091072500e046544030f860b074040d0b035900d115031000500c0040e8505580e0f814120003900c1d00e080070031210303c0140d406004010696450084404c181d100e007150303034031400c1c1d004002da84601800380010301482d401b007100c00d00c0c4e850640c4404c03d83d9041da0f031481501a80e0701004481c0e8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 283685593 1250 283684343 283684361
    0x6060617072a0b09070914150102010b031618020a0f11010e0d1d040c08010e0709051c23071202060f0a260c16050c0613090501090b06040509070210111b01 68
    0x280c7c240020824000f540b400f01c3c0b54101030001040460301080041d0400c03641c0030b141407030345603403800c02d05c481845032030702e0180c2807400c0f501140703415203200010b020110804020f404011100100741980700081d0040304025201c10100c81c08201c3d0441e02500b410080703801082a2068140c088042e482c06000d501000c030381c035854003152a400c1c078688040703200005096209010103004002855119001c050313114854108a44196a0083c03610401002c8040c110647d601110302e40300d50b41200c046440da0807180200b840341c0f40c51009101150241c080c6051650300098045503c41120380c2220250200d40002c1c6101c130543c511507142148004400c1d0343c00001c03031a041c000850202e14017290345040d603010324103c44007150801c0010301c1c1d5a0006c41d0440c90602c24003403c0081144070300400340940f00450041c00906a21004184280124854203228110382804562628000d000d900904030301400d007801142942805682c15034051000350990b2011072802ca050280c8c18841c40b004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 283686843 1250 283685593 283685621
    0x51606030c0e0a0614160b040b01030302191728050903070b0403050a15090b01260a080702010f140f070b01060201090209060405060a0e090105010306060617072a0b090709 75
    0x41a179504042c10050780000c030092038401008442d5001050b003090015203d24442c01d99400150f04511b8000e041070416041d12040e02049500f1800180007600030307102041200e940b4030b841d5030002d508a2401400d04103422204a400750b400112123502400600c0c8019090f012102000da50b40403000d200e100e18071014000340c103c1c00b80d03800058041007000d0b0001e445250049262405515811001a801c2e440280006855035a03071082010107080800d10141f090041c0500c4d0358942c5603450140700301c1c6c07030090401025103101550702c0d0103060603907032107403544001e43d840d11484601545660700041060300c81c015510000240d0030710501030b840c02d02d40d015250103210f8840e003051201a00c005402c0d15400055002c01003584445a0505e5105003620380021076154175505064040b01c0c516004201040803101c40b503060200d82240240d005491441c182c586101400580050a41c4605500246014114502007070100b14200107010718040030559540c10390b654600c1085400458981d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 283688093 1250 283686843 283686857
    0x313080708241b072f030c15030c13030b1e06030a060b0616030302040302120c100f0c0c030503030403020d03151202031509030309100225051606030c0e0a06 69
    0x800d500540b1841090304a0715034425050207416601d00450145240c80240d130030300185c81c000303030000d00c502d14900d820f034050b005001d0750300e0714401055902d81c2c100034418020074000042160884110110b4117103880920703100c12410b03207915014a0240b0107a481d095040e11903d04030003608101c0410320f0141300024010803203a0129540c000c09005080985035004005003c0c0800f0000402c1290400901c00d84d001070b82c840c00e40c81000f003010f40d420301070441136004142485140d1140314000d003510881c0d0a101100c1c50440b00e0894416400c2c50004107078804000000042003c0000134500a61082d020b80c0c0d455070300207500300e080f00c980d801c0007400070b040070004200302c0d80c2c80d0f021030140c5030019041d0740c0c15502450380484c1c0503a0a80d1600d042e540f0010030022102e1080c803011075001c0c050b810540c035182c103054980f07803208104c00f03191507004000309c90081003180801c5402e80c940c14031808500c0c00350780d038a8094000c0400c04504008140b41084a488511b40300019600742c40ea10380b2540 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 283689343 1250 283688093 283688101
    0xd0f0f080702070e0709050415030305030601080417040902030a0c02063607080a0c081204091a04090804050102010c050301030f14030708040b04060f17010e060102031308070824 78
    0xc410180103031442080d801112030200c1c000342000107082c414101601c54000d501d142c0b0090004035032284172080c424008241c0d00b4800a40d0002c12281c101c0402d103440001629541001002613200840c09480414005070020309100103802231841442c81c03070030821502d6030f0643d00340d03207401c4112918001040040c00d070641d000d02141d045890003d0400403103d07002541c480700c1c4c1c40c004181d01300040342d5121103251400c00c1040f0012a01510003031019005e5a10074099511841c0902d00510801c191541d15001c9200c2d48000720014007400117105200300400c5040c2408140d006004241c01542852202c2e1281400f817022a0b040700c0e442001684818050f0700c424500031001e89240368540400c01c00f440110300500040e001402c40c03000050b60f42e6203480e501411494600001d00148100300a13807540704140112003904440c0d00e044901d50310366401780103d00314410840003401d9100c16800104000c480019420140c42681084130010f803551588400019200000780c02541c040b10005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 283690593 1250 283689343 283689347
    0x5011d0904060f0b0d0f02040e030a0903060f0e0313051c02090a09110307180c2a081c050a14060915030a0c030803090607110a020f12010501170d0f0f 66
    0xf0849600e49110016550b510000011212480ea8005071944c43c0700410f84030a5181c02e224008085c42c0717110045142502c941c6003d01261014840a031000303644c0d542c030b003d1400158105034030414003d0103680e560a109031700e0b030903409151b01a01d03014181d100c1a241078080030000350102103070000c1c07144089a0f200740500b409441d060b901101c490454150800851b00c0400c038440203881a40803100e56584018a00c03c00c503407800c101041000000d0102c0000300410121900108a01c008405e285503024107000b00740b03104800b10820300c1d400d120b00301c008000b805d910450007602450001c0c80081c00301841070704041020b8400c41d610141070f402103503645e811050032010710750016068032030420150305c8030703652034903564000d5480000000802c0390100080c00348503031009460511601c0c040c9040e03689a1765040350f0070300900419110090b08004e43d20b950901c01e2080c0000000c0c890b56844001803030b8043d104240000e601d1040c01c2c51259500c0c083c0e00c5400d0302c04040c0d903c0050740141c1d02c4c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 283691843 1250 283690593 283690601
    0x30605060c0a0b0c0c0a1203051501271509050109080d090b031b033408070516020406080106082a010c0807061d0c030102070803010504020a020304090e060105011d090406 75
    0x2440992013042296807104031060040c220500e005240c1d401d801c1192810280907964010710140905070702414400291307802042c20900c5401d030288840814051841d28220684243c21001603030816081c0c1c0c010182d802440003003612820703a22080c03010398130030300240c1e10311400c906c41011460202c4280401148e07840510360210012446011111014031144c01daa030060740c0e90109a142407804c0b12103071024905600b85da20308140c1c1c048101c550840000c080c0e00c1e001d00240b0030400c0004100590b116030408455003d90010010000b5940d00c60206000705114881c2d40950701504e602801da080201c88061014190030102c10303410710000340111000b40c24044100c0d10940f0500100000c0368181c4103684461196000d980e98402c90142c64901e0240400300441c0b02c3d0b801040740200050b2001d00362411504180d40c0962910550801079045020300d80010303055501d003011300000300000080b1281298030a0702d0741c410a103104051121842e54400240d9004922000858002045640 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 283693093 1250 283691843 283691851
    0x206090d060207030302031b0304050d05030a090206031003050706020d020d051e1615090c1412240114090411060c010e1b040e0d121515030605060c0a0b 67
    0x2210300440681ea51141280c01566054000a50200070040c400045546031030620004440c0076041d403038290340d8503654940d03e40702c520400c000031000c603805928130303049904426070080000740c40b450149001129680148002d440701d1052610001d521070020418221411990b03014100d0320740d0200080e43c150340b111184141c0c9070300d0714284200e400c1040d0b002d81884042c020510400107241c5c14200608914401a881c1042c503224014000a90340c42ca00743c00c40e03100f41107041d40c03201c000f80040c2400300000542041400340900f00b00ca6810031030f04c1d0401c00c8100500c2c45407181d0305c820403d924589003029854000760440d0100300811400f0601201f02000104900e26000b0384d580003030f0035101c0380c400c0a901ca034404100c819400b00700d003401e860785040503074041240080c40401075507600003c00d125014014100c2d40303281c000e50300da08403078085d0403500d00c0e54000030340da6800240141000d100c00700c0000c0c40c01e40045554940b1204881d03078a85200000c011075601a00e800c10903400280c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 283694343 1250 283693093 283693099
    0xb010e070c030c0317010b0714010203010f03060509010212042307180209030a05010f02070201020613050c0d06090b0f01050f09010e19022205091f0608092a0411090d020609 76
    0x108910308a85c400d607842038003030015603104640300e594501d0880c48000c0b44401d2110603034010f20060046100480c4040308490f0044804244c80c2c50304040d1500a20400d0f08555040742414100300c103010448008804a07a0303240078880340144000c19194a07101940900c4407013881004140207520340c9074003d071000c2031005003516448405503807010f00312000300000441c000c0d0003080300429585c06001c101d900c001507a40344e10072444541d84060700c03040b140d18824440e100e4150071000f80503041d442044025440f880301c45040c14030446c3d19404007424403c480c0304000c9008103030303868101401444e04841017481d079020b094490b001c000c100c1952545001e24196801d001069010220b140502c40d6004800c00907050f15003800280030140400801620305128640203881e001001c24000341c003100d040b854a60156203400340c0c142d0801400f01010300c1214032602c07070300c03208544200ca440e003d010119010040d4100700801e41200f4092200401e0b40301009084050160505900401e4881402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 283695593 1250 283694343 283694357
    0x203030a0f0315090c0f02010e0307030f051b010615020c0a0e090a0611030702010c090312050306011106040303050702010b1e060a140d050618042312160b010e070c030c03 75
    0x2c080c3c80340003031107242e002807035850f16100c1003040b0701d41002411070038940500c0244850ba208a020541d00d00c80c000005040140124880300d02c039214809581e441030445444040f9034928000e0300d0b0203005e01c0c0c0240402281000001840c603400000c04a450b10404ac2508038018900342c40c20710b80b0300008040002c180134001481000600754407455061802c1e82d554182c99042c013010090841340702001500501490001c10710220300d01c8080c080740141146002c079920f40c0d030703400106c50342841c0c1142c241c520710940c4144010180c141d04210303c51442a8002c000b43c50800301000134803141d00116400d90010110b4a80050403c40000c01040c001414100040c4c4641c03203001d15560721003444441555607803018424603141003944001d50424030068002141445e07201c0c0e44440544620090b9807104503508565109401c0c081100c000011503080c0d6140e950f00c540f00d9041034900c0c0c42c100e440420307201c00441c15200b4140030380c0c000c44450ba101284000281d40944441c800d101c0290240700c51 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 283696843 1250 283695593 283695611
    0xa0e161d07021903020109061a0a0306050a1b030f0c0918050a09120206010f0e0103150c090308040f09050903030121030203130611011508030a0e0a0504091a0a05040203030a0f03 78
    0x50003030f500c102e651180e03000260828590405004035001d40d9500b1803c20b0030745810001d540e541280c48002c3c0d0382c00200028140d128000c03410020b000d0704021900e0300040e047d02d81d080c1605640300701c3c009061000c042c49040030000f0100c030300b040341e070081520428110701c0b41c9050300c03481d500c0b03554841300181002441d08216184c1ca19030300020400c1e0380c016840300005006a1135104507550003007800c144800769075411a0b503031070404c6d400f40864000b050ba460516440d80f5100b1403000004640040c80c56950702c0d10340d0040018191140a0050704504003004910f000c50b0006c1141d0403541440ca045440001c0605041c4440c414004240c00b184000e02105a030810f10001e00c0004181a844882d0701c05a011000c40c2903a030f0040e00c02208104401c402c200c0fa40e404000c54142c010b10345005d02c2c600c10444001004900b00340c001d2604145807028840400a40d0700e004880585400019080b80c0d540d440180103650007210025090380040c00b40c2c100ca14012101801e02030f02c14200401c807030503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 283698093 1250 283696843 283696873
    0x2007060c0318300f05010603140109080d090f1401020426060714040e01060f0f031415040617060402031c0c081804020c060613060509010b0a0e090a0e161d0702 70
    0x43e40c9410369146c0d40d01c440030010880012203501540c180030000340582d851503102c000700d9000e80d0810800e10341c0c903090785804101d00d4841c0031116540c0a2240b03440050701208560007500b140c0070703c07400c1e4541400c0452000c1e80c0b102c40a2950b02d0050018091517890700f100311a640c0305441d200040800c14000403801000e40c2c400349010b03294681d10008040804040105900d0703405a072403052518007000c0c0d99810a14907082603001c1071058161100500f010040307002004158000c0384884140c034006401954007181d264000c1c4e00072011180603540d9026088140c013510740002c80450840000c01d0002400c1070007811700b084a00081d4000300300d0040100d42641c0c080b807940b101e10f07040704041088900d04003603c03c050004101d800c0066a0401c400710b1034005040c0039aa0503894007180303c0043c00d206041a44600d8000780c0f02c010941000c000d540c002c1e00701c8440842d62801800d403014000110200a4407c907200b220f82c1c2900c0c50752030134060880c1c3c100686841c003180161461f083c0c4d100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 283699343 1250 283698093 283698113
    0x4090c1103071209090b06070b04080d090501090510020a0503220b01060206180c0a060305100305070b040314060c0901030e21091203030103122007060c031830 70
    0x20b40614008114620343c0c0200818166241d0401c00200340381903056040c9803a4001034940e0150302c0000402a5110381c24400054003a58160030b0019007031440788010000306402c602040f500c03900444e21365231150440d02080e40214202e02e00014000d200181a00309280c0354550031381011140c0c5d03640075420f82c80d6030380e181e14240c02080c0035a1190061212801c21660f014100205400180881e4400e002c0012490155445200f08054551000c640c003281c603034261400441d44403007102c03540c503030b11b1425115a0308203101c00d41e1804840c100c840c180460200f909845002c03984101e525129105005600800a994245103184100c010802c400d0343c030802d120400310394182000791a180d4410401c020030108450b8000e880e0400d000400006d081c0701800c2401c1c8549041000c3c140d90794201d01e03030040b09080310041046c13050860008245405c2150a83c05a000381c0d24010004a0348544400c80c0e02c0780e01c40c200390a00341904031038204a800340c404c00c08288504541400350510b4480c06186 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 283700593 1250 283699343 283699357
    0xf110d03050c0d110c010c1a040f030807020f0a080d230a1109030d080c0c121201092f0f0d02040e060a030b060d0c0503010e0601090501081204090c1103 67
    0x8140005280036011008029403c6030740d08600d80555203045802e503980c0c0310b88600d070309641030240400010040040503d00d0445040410150701442e160a0400001c900868041900032031821004114990302c0070601c2050700c0400001040d00e803d469039104825400103007800c3d505607403007105010200b05d07105d440519001005425a081c108400c0032401c44a1032a202c034840e483c100851721080d207020a98501e83c00036400d00b06440d544844a29941d4030a4200900d414081e03148030762007001480c4068180250009038041040c0e80740c501102c203c8030b041c00e010314051690104161910030700b0030546145d074100780c00d15040ca03000c1112500550850000a846180c0204041c800c10b4608140e01d40d00c64411100034450030300d5038481c4e120201014040f103004850b001f811806200c0c801900c04004c02c0068003c00c6480900c00049071a90001c0c00f070b007c4264240000010348c20340014503548a0800007040510f02850002c11000800454010318203214007013030010b4040205002802c3e403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 283701843 1250 283700593 283700597
    0x10c0f0e04060303120905070519090f050c16030207050d0c03120905011409150301060804020312090102030d0e1504050706020c030d0c030c060b12010e0705060a08040f110d03 77
    0x401a644400640400340300d0082a009030328101041000c2903111948441d11980d10310001582c101130305010f402c1c502e054211541000311030b820350b44004450300c208022260066001c0107400a60040781060301d9081d1103a0340500018080d813040c03001964580c860152190040710361751a6500041085000c5814080c0c0c3c448510000400c00d110604591500800700c03403800306141400c2200291002d840814150032501c400315920409884190b409001010030049168983d03030741e140300030701c0300e00111400c90003070203992030300c0c81c1030907030907040e1180410705802450401d4844082034008040c0810a01002d01c01c9810462145401c4c0344418003d601600c0501110b500303204010b840d1000e075441441c000d50040c408008850362114203803000941c549840c03021011582010700207044440c40b800e40c40701076020711203070302d00c0c0c154009241c9440b15400c2d41d0001e0b9543c81007140c280075864000300800c207140c00090009260b40a0780c034540b0b2084141d14440c00000004c100d00a041c0300007200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 283703093 1250 283701843 283701857
    0x15070203040e0c0d06033e220e01051302040e010605090a0b0f04050403050729070503040812010f0602010b010c2006070f0f02040b030c03120307050c0f011505090f07140c010c 77
    0x41441005800740901ca111005405141f00400c0125107140b41188a46810101310002c0055455040d0001c2c0840c54030f0348000c1c0164184400c05400c900000304c0101d205902e031000d58a0581c070306003e0f03401200d0340100b21410550381d444c20032000d80305400c00310f603102140e05000101a40d81e8031a0501942c000c0d80da99403125642c1c9000c0622003200b2070306280401038480c6c400003005044440c1a404811403900c161280c50340c4c170b040440d900541c042103d0210740c1e100089521040700345a0000c0350400da0082c040240c00c440103640c502d40c0c44c00080c18200c540d05095000c5880c0c003081010000c40503000500d80141601c03488910403009108450400205003220258906802003000b1800d0032000b40481c2c0200c00d000a64449240305025601030003c40000d0b012030060060702d507400f40240981d00005000d500c0b0320300806001c84401814034225002007000c3c01d08000702407240c05500980036003a00d4640041c2c440010a4400150440c0100300601c071001c42802010101d50f89034548107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 283704343 1250 283703093 283703153
    0x110708040911030103080702040c050702030d02100f020c0a0f020a08030703050304110f0d060c0e181905010302100507060f0e06070909020f07020103050c090d0515070203040e0c0d0603 81
    0x5015140354145920500350b050006001080c190b10031070343e0107941114001103800c05414240d51a0141a0020394580201180e4805039500030031a060314041c80d84003000701c481002692400c038054240c112405a0020340a100061076810005c01820700082000040f1130351950420310751362010380120b001403c040705000030819002280fa8000e00304440c0000642008804552454849000680040d80343c20210805034002e003020307541c2d201c1c0a042290714032000d0042c11907142c4295100450300b0102d074080e440301071080c41458142c95000b41000034110b4a04002c8484d40c22061041d0350540d59840380312020400c52203240c284090100c080d11540c90301140180a190550b0b00651891780100b01321041c06d202034007142d1190798242000152a1104404400340e8052031180c59001540304070000300744800000c10040041f442040c0c007000e980e0b0300500303d0b00d07400781c2d10440203c40340c400301094a08408001810030085400310004485035a0f4944001a0044440c43c5c1410140342c9049 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 283705593 1250 283704343 283704359
    0x100b0c0307061506080c030a150b18040501061e3005090105010f12210207031b0609090f020717040807050a08030702040203070c06020d0506010f0810170111070804 72
    0x1c0c50300c80200c0e20b41201150304e04030016003030a00080440143e010000009085c0000b07541c01009100d60032004010410f4a0328282b074003e5008441e040740d018415001b84920b460719006490584001d40d8410404608600118074803019820941d0180401a080125041c001883c41c040c104a08010b600000d2281c0c1416000c60324003070b01040c116414840140600041b04040704201cbd030591120010210b8141404042c00032184400070008480e072281e9500590f00041c0042540c3c052011820107e0080101c003044113554400e0b58080342c840a41002500c81c654050012100c03070031405031904455035240740c038550555481d075540040209050145c0002080444040c2a00352001104181000702c0b0590f03a0181a90080c4520740010018840300e224111100311103500643c00c0d9281c5c01c601c02842c01400048496600254116100980c407034801c41106024200b0600500302d2981001c0209055423000d10b1140099902d4000d1340d003880003260002c0c0344160050503c90380b01d908003200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 283706843 1250 283705593 283705601
    0x901090e1e1f0303050d0204030812040b071704030825031a060c0717011d0c0103050c090d1211070e060307050301110409180804090b010806040c0c0803100b0c030706 73
    0x5014802059090590302c6490b1940c1e05005a941508205031100d400594080c068412500004d100000205881d081300103c100050b005a11031115460140c3e60950116202111004005182c3d001c0c580440d011070f0091100d550806003200c1d1900b5036040c50020424403140c0c111209000070340e07505219000f5600740004c0112000100c0d1070070b140048481515071740300e24502480c0028814400d20428411096002425500c00b40d006090380e40c03141034443d5285c503141e0400c140480d06010020740f4100020085a030710040082100031945101c0d00c6101c401c3c0c001100c4401440300410b0000b040440402c011002001400c040c100d2a00e0f10310103040c1000001c0d84100c1c02607044c00038809003500001d040d101920305e58130000400c208a9419943c0f0700c4544200074003510030004012480c150207410a104d25031080e01c40e03059580754201804101d40c500c20761800002c080d6085c51001a104030300850b04000c0342a120425591912a00c5407a0380c001d4100281d582c0c130003d9010104609030007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 283708093 1250 283706843 283706851
    0x30e030f0616180819061505060d0203040f05100213080a030c1202011806020304030e0906062505030c01051f0609050d150603240902150901090e1e 65
    0x141455051000c40340c0e5048161000d4101445412003514220345500a0f03040010203400c0d00316410f40c0c9030701c00022600c94911105032000350401c0140401c0c01d003050419800c81c5c3c40034000614000048520344025003002d4001c46190411191038008079404004c1d104010800c3d4100503a151240c40c02d00c5a00700075507000341d901c3d401a0030844003207900030416058039500700500044000c014402203004114510440c0041c2121001d440b0030321006034051441948aa12207a0007002040e0411181d01030840314160b000c42e0070880c3d40103c1104a100c1f0709118000d01d07082501e0040c41e40d034981560055024640e070381c1e64540401c001302d60000310a0050503440303806680217034105040200134482900034035018112119020040058070f41c0e20b48494844903904100c515102e1400064480305114491a40300355802040090101c5100f000b6407d6401849003001c01140700100020b03800420074541840050304000910500062040f441a050040103106642941800310013111002e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 283709343 1250 283708093 283708123
    0x5100504050103021807170a1a03031305060a03020702060304061a0907050a030b010507020d060b120313031e020d050c03060708070c0f02031002280f091a1303030e03 73
    0x1000540c4480506480c42d002c5201126100c6d9100e09064440007020352240c280000c007032040109110040c0c0c0089c40300842d05403240140b01e07945d030800d980c0b80503034141071580d26000241007100d031600c1d4004101e0b01e183c0d82409410500942c00181568004640980701070340ca03244821286c6138049400f01d080c1c4400c0b01e4900450514000045c00d600034080300a0a065070f519010182e6030184064071245075000b4841101600a4034008000d405183e0780140900d155000c1c00c40c507041d000c000e4681c0004c0410000511500e0b6840b10b103503400c1207042006440001e0100100542c840c541e90880c0d95008a00806010540760180751034400c00501c0b0004001c90901489141d42d803000e0201341d49a0007124112070f201003800002d061010700710300e44410328400607031800c00c100c1c20030002400d100c18208820802d845020f082c0c81e202c59401640c00020038001050020b10200ca042c201c2101c00c400d4980d040015013008814480125081a00414220032406a0342c3c0340810202480704041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 283710593 1250 283709343 283709351
    0x1c0c021009030f14010914030a3b0d0204150e0c09060d2d09050c090f010b03040c0e07032909220b1f090e0307110301021c05100504 58
    0x19140c2962040c1c060f40000c210090303031a6400302502094100c01182030304103600035800003c0b4403410340d6030380c801401440401c54030740e210500855800e00c40c160404080024070405070702c01e00e400440250380c8100a61103843e425007007002d600c0382d100b01e05040451114601e440d0713080000380c0440b02001000103030481c00421108a0b1610340d04241c0b0002005982c02051040c2c1c44000f034107441003540c0c4206202c9407120020110311240e500100403d030700910544000b46072071418811500f40c00c0f15000c5444c007580300100031303254280009643c0540900000388140e6241c1805400d401801c0d200c0100190700d6098504410154200070404103d08404402840300b0140208142c0440104203401f02000012420500ca091001101d070803070340840c13007406500d40320605503e070880503107940100028151001c903032503045115a400c3c00c00260001c40c244041a0758010703000500d040c0c0c46802d95002d002c020075481489420084080b801100460380c0c0c600f6400301c81e01400d441c1c0c0010710607428 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 283711843 1250 283710593 283710599
    0x14010e040512070804060e0d0b090706110a0209130201140432030705010305070e12030409050c0301140f221b0504050105030606070816080304020a050a0b0a0f021c0c021009 76
    0x4603200305c03002c5400d10b0800412514082c00002d0019400e604045c00b21480007081140303441d00454204c3c150740290322801c101a44146245d981c1c1d03111120000d41084520b008100c40c0382140911070320f09841450290345001050340c6100a9800c00c0e44104d070301a007440244080c6070041032056481d16198130086072a203c3c0030380007070340c1c403540c5c1c0c03140b141810b65501c0455421442500d011031070410181c41e042c40460fa801000e9aa03038401e1107a00c02c2d8615000124400e0584a012a81242d0800c100106445000740800c000320840240380381d480013200c80d100403004003021f5000c011942d16500000da036081d81500b04600541d4100120030041e04200c140030b280e800c07000f580c2d0001e00680310b00791245058504044107104101c804130300c0011418146c801c10041c80020f6215038070969500e8a501d50380c13001e00044000074010036140d60302c10311803105a944142d4000c0382e4541745204a82c0840f1420b09a034151108a252180025128080e2801541040c0c00c541d20005410b103480e04010389 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 283713093 1250 283711843 283711853
    0xd0207020607050d030b090727051816050c070608090c100e0f0108241201020c0a060f0605060703110a060c020c01090b250302030c010f0209120c1c0614010e04051207 73
    0xc000581c200c2240c460003007205140327005000c08000d400701401c00075001c85600200e40811608854044020150b407890145d19403141d016540b800a403080205052820000140d0703030407100404000c024465401340c40401d40d04c1c0c4800c8403002420341c0b07407a1313030b0700074100c0078030a039603034001c0c00107041c0410001441007000002c4070089651407451a1303880e40c00b4002c0c00095000c01c482203514090341c004107110b200103402160300c0c080d0724825403042100d04680540502529a00e00c5681e601030402e200c11000302c6e02500c0c80d800c600380d075102a0340b415216551802d0803509403104100040e4030501c065611541c002110602400350304481c40e04206603004a01200c401c00111070400e100700301040d8040500800c2905d4002001d58001d200501014846500035004201c44038451a03148600c0003843c10046510031a894000d0101c1c07140c010000c00d5480301a500d0281210020b0307441c184101c016261a80c1c581c081c1110380c0d0f0b00c1e511340c00d050078420f24014130403106142520003000084d002075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 283714343 1250 283713093 283713107
    0x1e130911030a02030627030708130819031407021906030c03020c0a170c060a09110f0906010e0a030b0c120702060c0301061d102c060f0d0207020607050d030b0907 71
    0x41d281d46e4600305c100c0c1c408121414150302c083c600c60700e03500c00810008200141e0f0005004544040e000d400e50841d650111684e41d095a20305548101c5640054180464410030a200100801d8000249040010b601041d250410b080b10b40d070341c07000042da007404060780c103000d03a80d20040c0a00e0306506044940510b90b40303d03038203a0301c002d015855410000f480f84142c03a0a841c1d00e405100151511480c0c45600c0901618510400b00c5a02480d0b030320b58801c038509240c640700c40440141120907a0350b24440151802d01c545100c50b90712101180300000021510511103120b1400c0600c1c3c5901d80080040780c4440410160240d02503401c900204007150b8107000c00c0d0783c111001d41ca010100c1400007505400e441040300d4416800c2031240b0301c1c042519400c4440000410b011540c402d40301440002c0d28140482916411603220b1401c0100c0a04140700f9005061021103803003006103064180c1d80002c900c1d034864a001c54142c1c012284810400c1d070984690300b0b95440c10f90702d001c02840d02d840024000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 283715593 1250 283714343 283714351
    0x1008011a12060d020f060a030e06010b07240609060b1312120c081308060402090c0a05090103150e07080a0608070515070c050303031314011a1e130911030a020306 71
    0x26400c1c0f02c0034070056603540d05907044a400060680c554030700d40d03618000c02800d00c5954030f0a01e4441d050000441d184642c2c00c40e01c0311a00300280382e600c2902c000400ca18010519448a000c90b11840e0108000700300d0301c0b82a004010a42c0380d26a1543c03951000c0407104001ea00c10010464006982804901c3c0310701c3d4114408258a000c14070030109162844250041112030882c140c0d1900005c5201100012001c0c001ca0003100c585100d80d541410030030007440781d0900403000070414000d81500b940a03070070116419103081100107142d515205182582e01003215404d00245500d014020321036801e1191801500c4000e005c0c0031030a042c03602046280c4a981d8003070007030201c001010303010f0002c3d06643c00d000d0318000301501e5686c2042000808001e50094003031319800e206011140c804181441403080001443e00c11807000030a038070030440001410f40d4140000e0040840c1d0444694550010625041c2d102c9400100018141442e00454255601c400d02070343c002d205400c090303600040c00c5030f40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 283716843 1250 283715593 283715599
    0xb0612010b03070504031a0601030f0515061b030f04051e0a051302160b09010c080f010509040311030a05180d0b01180b0303070b0702150c0f0310051008011a1206 71
    0x35030386851100300c13414496640301521f5000b00e1840e070600c0700314141c0c2a13401407500366000e0100101581c40042141c00035108a091508072092100103820150083c01864a104080019200e40440d165046900c20340c03800072203003c0090280902d03e0b048400c0d01241504203100c180030100e01c4d022900800c905d00a041c071840400120500d07041c0a40c044400c50507034801300544000c1d580c60800c0920000b940e55240707039400d21a91441562140d641d4502c2455550780c0781107503928100c24001d003d0409007043e03042045550001003103980030001004004000e0b81c49907500e540609401c1c082d040002d2440744201207820011000c00c1c13108080d681910513450441d10025240c0740d0990080010000458141c080070440e03400748908d0b4402c5c11300c04d450b26020b441845140310600031001d00c0031640caa2091200b0302060481c003a0303103030107181e0040500c1003d40b03c05803580006044659085200000680030000512030400380c400490103181c164400b05d030801d901d034401204158001455140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 283718093 1250 283716843 283716847
    0x12070e0109270b01030c270507030212010f08010c0e0105030601030c2703060e03070512090a03020a0905190b0a050108090a06090c08011811120a06020d0e010b0612010b 74
    0xc5000322841c40580101c04840d41407189081601d00360400d04001d2100703490b007660301c200014440409902c0f10038030280f0310007c000b0796070403444007900070b2002810110070907500b404400c2d000040c041045002c1c00c520f403841d60041e4a40002e15003510740002c5e040081021031046c1800690f004030549402580034240855600f0390504111030b46560800d00c2604c075000c40f201003241440d07600c40c0c902581d01034042484000140780000ea528412542c0c000c04035400350010000010051026120003040101420044c030350300e400152050b20a0741005050551740c0e0103125030413080310704100106010032418005107004000040d00000b0b284240340c127000e00d40001500b41c030b50611605910940c0114100b0070b2040c0c07410020007140c9a4051a40d03290710b84461302800914402510a005038482060f0b0039100010080c01196001c4070700710303100b52180308000d10000b003c50001c1e1610511804000a0002c50000803a096030030f0352040038082d0000304490300c0342c94152034129041d1020742042c40c2d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 283719343 1250 283718093 283718111
    0x3090c0e060d0618170f0403021201020d05010b030a0b0409020112020a03060906060530060d0206070209070206091204180b060412080910050c1c1b0506040212070e0109 74
    0x24400c0805074802001d0034504040c41c2040813044030744519050066240c07071042034011170704039018030a4020328031003400d060000300300619283c0b1464040181c1040054203100e8450504000d0360400e030044ca80c400c0303010040201e405820b100c3c0140d41c003022201844100c0e0182c0020780490300e500d0090861035000141003020782c0c002d41005004048034403042252641d41e140043c002d8102a201800420030307003034204035000845002c81c0f502540054034814079281c900c20030000245402e403c030380011003840030a0160b52100303c40c51183c3d04a80107419640350826045042c6a4810340503018604103210034480c00051804110700d0b03254448000441034003c1c0000b401c58000c0d035100285c44006184a0403c0140640c058140c1480c20f807865040250354800a80381805401208011580030300c4820207401022598405410000d0900d00c4c41528614403103048002d042505a809034403545c140001c6080c4000060300c0344401c0c10213001d03014101200d0756100501846059a49500d6840103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 283720593 1250 283719343 283719349
    0x120102090f09223021060308070c03020f04140408031b0f19050322170d092d0609170c0c0103050108010c09090f0e0706110c0103090c0e06 61
    0x840c030340743d02e1024440c440d02000d01c1c090000d5000c18918101c2c05240c645a5000f036410100701d00350071000f42c0c0f02e40c040c011207502460341c100140086081501d4580c00d00001142c03140000b015458010140c00020b142540140030070380c51402c0c0c07028002c030700d82410a414501c900b0005a04076900c00c8400d40c0d43e80700c030081104c041c0c1c441185100112030001c1c400c00d039100c03660010441d045005449a08000381d0303c0c4151100c0c001190f4207050210028070011840f04c0803000c00220358401d8007030000d047c079000d9a0b810710781c00c00d488400c40180e848601c1424010608000304042c819420b0300120508021a0120000b442540c010422a11580c40504010209106031807900761305800603110710039500c3d100e40e100c0c41c840189010a00d84030000c5a80d00d018052000314000540b20316410910700300c2c1010003480c4a01c0074009241e651545c58241850030302c2940002c003103030382d45c50442d041504422400c1c00d01076082d00c3c0c103142ca403100010002d02402e0102003200d0307120030350041076603e40c804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 283721843 1250 283720593 283720621
    0x30603070e1503010c080a14010605030f0a0f0c021b04060b04120314030c04030209070c23030403020303130519050f0105070807050d030510170c090c040902030411120102090f09 78
    0x80b66815420101900c1c010759110616a21980204a0034440fa080c030f80c2144580f00030a011b5400000d03020000100700c02c410030010354005030b1000d400541100c001c9190011184803031205001a0404a11003040e06104d20001203604403c0380d0410403180780c07041008041c4941c1c800c0041c1401440d02d5030003854081c000d0740c5200c104001c41d6913036030320780b651082c0000d07405404100d10640c00003000c10303507041c0700d21040100154024645214182031903600d03443c08a502644a21030701c803c01c004001a03c0c00d20180c02090346081c4000a040e06001c100000c400380c50000c003910708000e200c02c018a40e11080c012030788690a0801d10341d50740303903070904204c1c85c49809400350441c40b944e406100744c1d07507042c0d1012303104011169115144507215415182428440082d0b0043d0758030580200c546071625800c49034025840b101c80620303050713a40e040030090341c00464090710660132480d00282e440c2480116401864100c1008501d408004000156a0880f4900084c0220240000110081500c0d45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 283723093 1250 283721843 283721881
    0x10031b08120d0c051206190302181605031302040f140412020705060c060a050c070c030311060604060303020607120f0204082401030210050d060b0a03150803030603070e 74
    0x140d8103072000d06001440c250340510626603010b0719004911000d180304030150b580d6262800d004024079100c1c1420003071407650b240b032240c41690070000008010307615220415407650303e01095036400e14040600c85a0040209542424004104104010301c880c0007141c150203039040380c0000f006050908490002c10000b912451400030b40300170f010910420702031188a00080354200c41c00c690b221414408140181d24000c00c0690140c00451001402500000d42c04a50f54101c0c60a0902580302e0991841072a4400e074003080d5200c0203880190818060590b00c1401a034003440841e01d036940c001e5803454010082402c21030324200308400d144c1e054202000200449006648690311900050784540c1400c0210301c041c540d088000101d65441d00f410b90480c0e400902c0e955203444101015101648061010b6503690741d034504c080703054080c100c0500041100c5a500240d081103030070b1220038089890b009030700da40e80b041c0200702e00e5503000078081003540ca549851107581e80380c01480c01c2c4e080704440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 283724343 1250 283723093 283723109
    0x905060612210d1a03070504060b0d0b06071205040806160804060c03060308040f0527041709060315010e0d11040903090807060c0201170907030206070212060907050102070e10031b 79
    0x1003166204c08100700166041d02101500c0a0540c1e8900f0001103031450b114000030b03000180500c0e4000b52059020300c00a10f00a13020525182d0b80342e40d40c01d29840d080c90400007165003c9001d1003070741d204000d50f0382e0101d05443c8624901c0002d02c00075101000040000b050305489010444256120390881402507500c010710645640c0c481c0c1200002c082103000d854001c0380c5001c070100d18003c1d507014141c88110300b200c0849454441d602c2d2070041e014000c0c0c004500034000c000b80c48080d1500301c01144511a080095000543c0e81c4000501c0c28115904942c0b01c2c0c803040300d0760b02c0401c094103514403981070100c90015494a983c5000d44101840d644140640e0044040010340550010b40c030003a0b140c800d83c1c034400b070036819201c4101c84410070348000c0c4640c4c0c0900750a00040c24404000d0107010700040039680350400c1c1038001446d01208135051a0350f130700110020089941c04200b4180a00b042484160603881e11040b001c201055500c0042c1043c002113020585d04505000c40202a000e24 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 283725593 1250 283724343 283724351
    0x3030c09040b09040b01081002190e011418040c02030721090b0408011b0903050d0507080408010203071706060702030606090a0e0316031e082701020c010905060612210d 74
    0xc1d003420000d0880c00d00c91f01c00d0780d0051864248404001e072007100e9141071055095202042803402c100c402c6080580058140070011259490550013a009400c000d1681b040501810f20003100b8402954200179401040d5070060012000181410804c0089140700e030422502c15991800115190200c3ea40168a0544002400f02e64210190000c401040c1c0d00c241d01031100320140411034000324944400707000c40c4c10401c0200d158134842e070300800880380507101c010304054a0f10402800c81c0d100b580e000c0d020030760419010a0014803c0324840d408001224a00d0400d007164001c82c4e1901401000c0038070482805000440c3c50005509c07180a014000088139241c1c1815100c00441d241195030680110380540e140602500c03411000080815803543c0d04600e5803202c0b0404061540482310b1202c1180007008100d100100c24405010b00045040c0046039481160070528102200a0000c60150301c1d0b985440d00c15601c00102100d56000302c0c00320056540d19403650080500808100e05001810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 283726843 1250 283725593 283725601
    0x7060525030203160b0417090109061805150306010206070503010f030602070f1e0b0907060504141807020a0b061e13020c060f07020d031509020c0a0b010603140709060203030c09040b09 81
    0x70751741c4074a208503c21803c80044d141d0101c29054140140100c0d0f0f40002c84003030051040920501c800b84100100c0c3c000c00c21140d848000060032802c0d4040c290b0103151001c01004680d41c5e040081c940c10922504100d8910350411900b01c00c40c1c2c02c10b020280400c0d4000a012040150689854070f6058100882803000381d046c55242d0035400c00c01788247d81e23018100002c22130499010412404544030303500c82c1031070123145c82200510b1a14900d00c45901c40d403ca441c200e0100c2a08018500c140801d82c00341160700d00600c1d00d078041c003001034482e40c05062420b00c40500b2a5000d8081007c400c8115a444070150729805900064401d01400003140e000707032000e02400e01c3e0080e050720b003c0d81c0c0b1038003030304e07803600038031340100c003201c6503110f2a8480c0045c80c42d080220001d6035009100f03014004090384c01440307036529064021802030b07220b07200007591000340c4030000ba8120407298118001d4034100042c40d02c7e20340000d54901028044020103000014100036941d00d0303510414840e600600b014001c3e01d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 283728093 1250 283726843 283726853
    0x5181c090f0b03090706020102121303020c03060f01050307080319030513060204030302010c0e04020a140a02151303020f0f0706050d020409091202070f0305031b120412050706052503020316 83
    0x80e21504e0b900e202c2c90001280990040c003d5550310036034807000d40140d650300c1c42000140d50000b54142c05502a00c20208842d032010b11107948034850b080400b5025524010600d89401842d03408a1619001480030710990080140e41c540c6100481c5004200c50b16010480d1000206401c40280818800980041010f806401803003401d403e03611000c0010001c04103101c240e02c24007540782e0020b09640c460380024010700d03014054040040c41240d62074200f901840d40c10380803c0e168a4951404a0240320801d641007140b94044c04071800074204c0c04036000c0480d651001c1d680501c0c1d05000001c030310009403104c1a81690020320780d401c01486440403904045160440c1c0d10010300c01401a5940804c10701a0102001c00712940000250b1a007a13418520043c204071307224071903449004002e00707103100700009000f44c40500324018400d50341580ca440c1c51881c10810b9400001808003d210035100c0c10b40310000e1801c1c0858000660b041e5400c945001c82c158401c51141109000e074905080e01445 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 283729343 1250 283728093 283728097
    0x60803130e0606090f0108071e0908060a0c050313020310020301120605090705011205041509080c01060e15100c17040320030a030f03270605181c090f0b 67
    0xd01c0441e0210140d02c942042c844075224540030305400040c0c02030700300700551143c481c484e40b2950f1441c0c1902d40006003401b0401d0b2040c0743e0320f00400103103104006c0c4919a81400655003021181790100118a407100000c2c0caa804010400b100e03100c2805448429904e00340004921404142c10844d41ea60310350030603c058001c1c24400f0b4070103a180500003507254400040782426204141c4580214030000300802002c0c2000520445d0707140e44002c501c5800041034040c5050003445440c40544a80ba6030701e0603400c40713050794406405a00684180083c007101840da00317103c04d000740c0301c001e41c0600c24441030701c840310b01c950010301401581007103d4521910001810940c1d02c00c842d44403444101d1640100146081c2c0003031680364001031101000a4080c064031003044a0604000c201c070000d80e00c01c413135804403141c101481640c1d02c488c00020025544681a444040e040720340118881d5400191303518000300c0300000c034500f60032003c8243c0c41e00444c0104000c11044404c08009901c07030305034030001c2d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 283730593 1250 283729343 283729349
    0x1e0303040906170a02090a02070f05010606050a1103090d02090702031308060105011b0c0501082d040201030507031404061a06180a050a06050306040c0306030609060b030705010f050711010306080313 87
    0x210055000c103048070f03c1c0030600210444d0020300404003a122603880400075401380d0011158542c0d43e00031900012000c0c01100018030700e58403100c2d140c0c1d5040f0000362440d032842009222541081110382000e948040c1da0044054050300e900b003130350b5150038040c0d16510682041c0130942500c3c58000524017000079480f4103030307a42a03032104000031541c0b1140b8080200f8101c028034201500c001888154495488258007100084030180404c100c1801c0114020721103800f001400c18280801055580502606800c074045181c1080900c042c008003001c0080054030003450582c44041c40c0810705e1724030600000f00140200815600c2c201650302c0c0521401700440740f40940107103080000c003442c00c5a00b81c4100c440380c0c1c44440ca550340c0c070801c000007005544a60790906645600101c08a4103500c130300402c02d807041500240182c1090708040c60400b241c0d10940c1000304a2141d50007041d4440f05450303405500000490702c0641d2400107030054001900000d001cad100204103d452096401003000072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 283731843 1250 283730593 283730609
    0x18030a0609030e0402070b0109020f071a01030606050d0b0a0b0619020303010911030c0a0513030b04030c052b08090a1a071428182c060f1e0303040906 66
    0x46070400c3d014407050740100780020b0002e558103001045080040e030000c19510190040043c90b2912980d01c80d0a000c00e4041010101c1c2c86030001841001224803415001d021304441c8400401502e0355031084144005010410031398480b074242445465010966041d6010f090512100f002c040c1d078029900d402c01d1080b4542c0900300303040081101e2541d011240641d03000d03a01c80d40303003e04100060704c29520a264100d04a580100f0000c04121030f80c0d030b2603009520940e02d912100002342032051500401c1c2d01d05021280c0031b03040d541d01c0c002c0d000c00070040201590620f0006903680000341410300c03a61080180100c00c603020803c0414215880c250300c905484d8071251000c20f883e122416a82c041d02407500b0300252071000c0308450029a0007540b54104103403818441c000a0f460041c50701350940d501c520446220700076a10a00345071b100c0c0c40300a009001c4030580c03151402d500014490346000300218000e09070801e0303140500e91152a0302d4030039600602200c2d56240e0799000364000b418503105102d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 283733093 1250 283731843 283731857
    0xf0c0c031b0b04020108190f05150f010813020f03030304030e0a0603050606090909100c02100c0311070b2d070324170106031704090501270218030a060903 68
    0x68400d60421032002640d0b000100c900840d038460b4015180480040c122003174004411030280140862030054502c203403518040170400e41842c1400c901d503d08209240b034454942e1076100c4800f0303684a0801a400030301c00940780d800300160b0000c0b40d060048c8006a41d010701002042100703040e00603c5900000e0b5003500c0d009101561070000314120381e401c0e504994080e0741044034159074a0425500c1e07401c81020400c2e110b003098030545076401c0b0307880700c06014096000440350a4a07180b0364820320080d802c29013030520040100c0607103001c0c00d10a0b0030000f0a00d82d51031000c00c80000c410040881e20b1030000004010080c003400450341c00071412902d03c400139082585011015003803101f042000c1680c0c03880414418189540842682400080c820040d940e807003001000c600d445048807407503066002d0b242c2d911414a4050415a10142c000d0040c0700d284a81c4003803000d0005c0390601c0c1c042500313280141c0355480681c914501d82d80080310103900d480382c400380105004555010000d084d1280d10703200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 283734343 1250 283733093 283733117
    0xb090f09010803190e0301051e160c0609080f07241103040b07020c030d030501090606030504120806030313030506090609060907031419030504140f060415030f0c0c03 73
    0x124140c0824041c00040c3c0c0c10603c450962500d1074201803540c1d00c1d00b4106417460300c41030b901081c07c40344c04403850340f0102d4006003035080c0180600c61030340d0003c08001c41c0f0601c401203a400a000c00383c107007500805450781e6950940c240070605050314034a0344000d4009945c0c03032040c200200c001c20340c0b9a032a0b10b03c0b40e0b0341e031080c9540f44691050b0003c0c110180c801d5411546c071926101d02d80784000300b0860a42c0903613000f4a0b110ba07028422010b1107411a1800980d550410214804807801d0390000c401b0b042c603120902001c5a00c1c020340c82c840e040203250101c900e0b83c500000ca82580500e24280704941740800c404020440c001c24803a10441d03899003200c14a42d29100d03c60b0303482900352503221189c0c00c00c501c1400442c801a20000241c0344c1d1000300c44442a0301c0050969082002d2003d0b0300182c00400c1c14064042080000310a50a00704c400c0e804014551000425500c124440c04031143d540e8004004641d0107600b290310451000c44080005480c40000a4558507201504600003a200c035448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 283735593 1250 283734343 283734349
    0x61e05030106050906040902030f0304150305011e0b070c1a040e0a09080d0c020304031a100b040e010e07030b030d020c03070603020f0a0e1206040f1a04050d0302090604050301060b090f 81
    0x1001180c00c0140344404c1a2685400d200040c940140c1c00c1ea01409003c080c400954010030090004140904cbd030a0b525482100d00107040319010380058a041020140401ca514010040f205c151940c011035540e44490a151007620700c04281d21910310015510003000c4100c10306409041250004082403250b51384450b12002168201d0030001d0041d5000e00c0f03090700320801d9a1283d00c1841d12030044900d02600d075207800c0540c0c45243d2141411101d6003040103107241e02103d50704024242044d456003403a040c0100d401c040305050181c0c0d044000d0090014656920a421508240c17401800b6a05c81641c80040252980700781400c0d2b501a1088c10800564907100c2c2c801c03500e5000301140c8203030400a00d40411107040090300c820302d1b8441c80074200c210303c2c02000d00886016a101e06220f0407104072502c2d10420820701c03244004514070312141040302042c00450786500f017618520300140c0c2c5080301d82c0022003d004a810840e0950f10340070001c18546203940050601070401ca8801b02046002c0c410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 283736843 1250 283735593 283735601
    0x3031103090a09180b0a0b19080303060105030a18152007062301080601210305031612060b0c0105090109021e01030209100806040c0306061b080c01061e050301 70
    0x80300d4002c01200c004000780141da40c00318091070b0410401900c0a03900303483c1c1c4070b501502500d4552455a461004000c3ca10b0002803c242403104440740f1801c19140c80c403859140c2c04010010b50601c500000002c0030300d2040ea010310160120b0010020806003581415060800e00041e298003446c9080b02d1004058028400f41407070074506400a490254030756503090207000307042541c07200d030781c1d402d50581c007203032a10a403542c040c0205070018403003507242401d119850401e0303512a100c60f5101c4000300011a920000b225803002c00c0700c550361070342500642c0480328807181c503030004402441e0003400300b10580250000c0105001180090185844d444031407800c980b030802000354000487e00400f0899007011801c40c07000c0805040040c1004401c5010501543e682e840c49400604e501042008518040c811080311a00c80e1500704082801d00c0741c05803119400182c041218210204010f08109091085441c030340040380080c4206036503940004c00c0000c40001e10030890ba141280810b850a05100d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 283738093 1250 283736843 283736857
    0x30b01081501050705011121010f031104090c170d1707080f07020109170702090a111b0c03070905010e090102130b090325060311040e0c0c0a06051003031103 69
    0x2038682101c002100155260b5008050444095488985e0f42c002a81c40b240904204240c0400145060a0800c011442804140c210302d40300c081c8030710180007080100c45801da0610f0255000510004c2c2428401250301880c0e10841c0104202c0308803054500300425841001002c585494072840581800345d421524201ea00c4000121007a000410781400240c9064104183e800000f800409507119412002640c403000040c03118000340340130450802202c1c00ea032001a44000700010314180200412038881c405115603074020415000c1d021580620030b80d444000300070204c40313003681d84404c080c010700401d10601c80100000c000241d4824070600840342e0f002d5418400500c2e03075090410650031500b000c40442c0c0c240c4622040e200040808541c1100c1200d0303070740500309215181c80c00c018159004000d0100802d60f050004208071340307031141c41319040300100c02c00544401c0368001213481c143e109540a8629800e01d401e1100000001800301c0943e0301035501e00700c16040c001001560b902c41e40c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 283739343 1250 283738093 283738111
    0x30102030f0a150b0f070c06051e21040506010911070809220c080901050a0204060504031203180f1a0622062303011407050a0e150a020c01030b0108 65
    0x20000826a401903881004407244801d1200c3c0a5030721404030190742d401c4411224040c1c1c40002d07007001404071030141c1800410b503a140c0640340640c050715282107410f8990420108590224801144602d108051184400344206000c0523180508045544150a200d08003e59140804c00e0126003903460807514034a4001c100c02d450f112010040c00600100c80e2504900091030004901c4e640d0b0b500d01031101c421003180d40781c1c41c080c00c020f2101d07800c44101402103a212481007204010081c3c01505540480b50070101800c5061040d15096001e040004241c51402001d01c40803020008100341039206507024042c00400148040b803c4a022002900c1c1035500c0051500700412812100030002d02c2d8016401e4082406690382080661000991a244101c10f18003038020409041c00d20030f45c8900b904414942185080c010805800d83c07244007802c2080010394003007104241c8031900000010b041c0741030107617650170705a4402526840000b000e240001e05101403900c0961040130100d010780c40c49 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 283740593 1250 283739343 283739371
    0x906091101170c09130f0504020901050f1305060316031212090f02064f140105070f0c090606120b01020d0516060e060403020f0304080a08220603061403010203 70
    0x1108400310b0030b0300400c0f06260300540c1c1d019145c035420914003800e1440030910350003080908152041000040058000c02d00502107480303695010396a900030f000720010700810001c0c09858000c00709013044942c3c816608501e59070f43c070000270040d200600310502c2c08a0380d5110110700c007180583c029201300702006403180100a503c43c3c09407a01b0402003a241e52a01c12001104a000c1c280180103c2e6480f5111104e189941c20390940c0c44200441c2150400d400c2e064800c3d0a080503506640755126a00c95410400c020881004001011403d00c05440c1c108841e1a40300340c1d42c211507005061030303018078000110316034030326540c02e0a04e000e80a40e505050b0007415803400140411038258005809101180480d001c403100415194801e62240c005410040d008620b0070303040c06458600c2440d5260b1540d0f10800c0304000d5200082501d08545510100d256901e590311b03881106440700140318103d10710810000001e446030103a00583c01c890b0446e03040c0d086580814201400c078007084960358404411 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 283741843 1250 283740593 283740601
    0x12010b040f06030203070201240602071d04140709150f080f0c09060f12010204090e070303020a0b060112050a090201020c0d030903080306060705030a0c1a090307170d090609110117 79
    0x1036005503900c000e003071000144082c9e903224502000f5009160242a10b14407043c05c0c40401e50510071640030300560320040c00904110383c10f01c41103090007403001d000c010b00c030346201c01c1c60501030018500400e036142043c091904a030880d10310800040c800d80d60000c41600000540010104409018001550242038040c008100307110001500904107a07100e12032414100c440c0d070340c04205c8003a24000ea400180c03a5810a0031a0341142c110b0306519505034031408007003000907070002d205001760383d2004580daa95140d070001a5800070413030341c1d1010510700300420071031100c1e100d80c0801c0486000340c1c01c8400c0a070b14601805411140840040c0000d8000704091000c140c081d0010f540000c4080c0c00c00e490080c15840d441d0954000725074030b03800a1082c80601040c0309024004c030072a09a000902406030920894041d9a44906000200925102e03440c0089000111095455661451000380400c4c81d0b113103003c600a00364900c040301c268400079440a407652040040c1e048031900c424002c0d2454071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 283743093 1250 283741843 283741847
    0x8030d050c1b030403050c0f090a0f0b04060311010905060a0f0809030904050108060403080606180d060b0a08030c10050f1b210a050702010e030306040e0c0901080312010b040f06 78
    0xc0c004220004000040200c01c110414242c0e4504800c44034101441c3c485045140403401c0c882c4030149144a07480f90030480040c3d0340d6034080c50340c1040f02c201000500d01202030041740030341380d003100541c2c0c000c1ca030440001c2800490140c42c03900d40310990360381003010f80b03132000c0001030b010700e603902d400107900c0010080c0568040d40546400c046800110303820920201d0010b400c2d52026000304800b6006017061208042e003005d1000d0701b0940455079581448036940401080351207925401d0302c00c031528801c0a092002a034040002c040c0302070115582d01e41c84d0401180d8940c01021209441e1080013400708100c071307191081070b0060303200d41c0281d002607d500411403400d40090100c0d410054040003080c6c1a20105001a40300b030024900c0000545807140d20001103a0006001d0815a4142452900e1045000c01140d038000c00c1180e0001d007500090310040d1600e002d680c00c054220300c90400218a0360790020103010b00c4c20012580d030007030303a8a511842405010302c1c42410444aa00c0000b80503140c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 283744343 1250 283743093 283743101
    0x9060108220804090905032a06040b0a0b0a0e071407020a030311100204062c0102060109110408060a0e0120041a09060a09051005070f0206030601030b100806180108030d 74
    0x6008001d41e030700b80b94070350250320101c0e4031305c000c00c0ba80366000080140903a5585620008421a0410010003c0c401c41d140b41d52a00401003006000341c01c0ea100041c225001035100c4c03081c1113009010f4104a50b04d51045040d510002c3d202003011031109503011035144028401c550603141d0142c8548516403440d50705407041843d500794100a13018080702080c40070107a1001e400142860b940b0f103000007010050700c075603030400340040c2c540c100c0302e283c2e4036141030b40c00041c400d045031a50403000030b0000580c40e143c01c560065070031040700c900414051080302d8409400a2200d003045074001c118640c2d00020311403c0318607034041c00e1740c0008288420421521000008141e00364a034540310b2600c541240090020781c4400040e074040740e0940000e003d00c3c14109104c0300b03401410304001e8544290b545402080f0140d0a000a100710800000201c45074860f40110030010005403510002080010000d40070180c1110341d0f40c020100c20f0000e000c0f442c0e400300e11038121507008020303515060680003600090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 283745593 1250 283744343 283744411
    0x3100507021c0c030f030e030a0c0c08100506040612020d140a02090106120e0c0f22090c03140c0f0907021203160210020405060924160209060108 64
    0x150148042041c0010b03001c0803500300c1e4402030b07900e03400c0001d914074014090002c0070100c40c080610308240c0582c2008004203e601e041c4450130700341d9807031055282c00782f0503c01a030003030350950040250150f03c10740203400040c0503200444040c03041c0380c2c6450300c5021440100b1b4000e0350288060802c14003040d10136000c440e8200030034080e00c03040070b030540102e45214020f0b80080000741c030019030580500c2c0c04d4410f446000403010050900001000001810390341e00500c018400c030340c01c02000c0c20480804900b000c80c0003124109011564080c2020081c03080d040c0306c1900d0b2201c11450070320007850049200d40d07602100a1000003064000c40502010800c0204484254810400152004d121a20240d481048008162944800a06402800c054610743c010148600511051195507100f006507000355209403041124141d6405810140d80c1070b90320410280e00001403581e0b148038010ba194903145d8029030b0906181d8840c3c00044a01c16802ca40050a003c0f140b01c0001c01c88180c00042419 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 283746843 1250 283745593 283745597
    0xe0607050a0c0b240a03020f100c0615060210060602030d020711090c0a031518050702031c2a140a030e1006090e03032a0d0c02010b031b03100507 64
    0x88107042c1d40e16401e804005031007580384c5000a0424100144002c610600710100940c4c1401e0200d02d903502188000b01c20408251140f08180c00d8602c666101703040551003260007007414002e03040c0d2109a80d003a41a030b4022003005015041e90030380b411183d400b41100311031403039000710310304070040081d1070094100c51411035090300301040d8065142d43c0c0a1945003c1c41000040d260340700c0311000c000d421514254416046080c50000411003405001d030702d5105110410400b040d640e6032020100d055100d0600e9000080d2035140160022400035440328403602d00c506c03d90540c0541103e41552200c145070b0340c1c0400902820355010070b902d000c0b006000070304820b0401285200760003094a040500600d402c07a0555940c82c8100401ca0245c0503800c011080440914610b01701420940721030302010100042c40c0380c4280c05846500d50743c40407507241e42c02200003088220903e04009004c0e213040c2100710700c80c0c0f1032080424200452800c51a6004200900070708102c00c41d025920702501c001400c07002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 283748093 1250 283746843 283746857
    0x6011a090112090b01050901050307080601030f020102071a070302060f0105090a0b030712081e0a020318031204090e0d0201050c0703080c0d0501120b0c070201080106030902030c041d0106090e0607050a 88
    0x34454030b680203c00712640b140402c4007881d030418080c00342d41d540507480140300b944201001c1000010200f9058196a00140c1c04403843c025800182c1c0340c018240e02540200e404011803000520b0020080d14207544641c0c00d903021526162340440380b000003030003100d0b031041d81d09001c145042e000764000c095400d00642599461580c0380b25062401009072030a0341d08203000a481c2c0010b083c020254030303102d444148150308000c68540002c2d56406419214178815881085000031650f042091707640038505000002ea4641e201c0488401030508844140c1e0315106100781c805e40341740180074452040c035406110600f0324006440841d401c00d0007411740e4641100070040080c41c0600c80c09001d0213480d201c024040ba030702c2c66182c01515504020310201a00c1824048000180c2c1e2000326a4111529403a011800501d2070000a003000c0c0380280180d8086e1a000300d8111542250609001c503141000081081c1d554034541e000660f041003503900c13803941103000001e9140d07016001070301089200d450020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 283749343 1250 283748093 283748117
    0x1b030b130203011d16090608070303080a060323010b010e01050f0f09090403090e090d1205060111100f0b0105040b0703031e0207030302042318090f071205070806011a0901 75
    0x1482056407000401c41e4002d07440c140d801c42417900c0ca0340c000300002c40041101500c0c0046640c3c50356064000141007142440201d602c1c4500ea0700701e5000f80d80c00ca00300560710308124a9114010042016400b21542048141002980100100c0510800c103846207480c280455901184981c485440800e103481c0601c814070076612860302c003e100e10300c640c44000106080217250b070b161041c024a8182c85610448441d10996444100b801c00c14030742207008101d5450702401a103406c44941422480c034071400e40780100344000e98101420b0b155a510040042e07540e4500116014030980c010807004800401c80400000e00c40d0384800d1240d20030200d8070500d0140d0086020990b4000d10060740004c0d0080703001d1000128800c280603442681000080140d1004000715507401c45945a212031240c5100010340c441034180302194002003031034281d809480c0c032600000f5a400d040c100586080c4500400454030780340002d1500e040c0c07191200c0d43c16009c08280902c0c0180d81c88081241e04200e0008008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 283750593 1250 283749343 283749371
    0x106030b09070501020f06221104020a0314070237020603070804031209020f090a020f04080303040b180312040302030d0614040e011b0302090402041d041b030b13020301 74
    0x140d40203410010192242c2d91a02000928120401007103490340e80242c0244281010f46440226240c0494000311390380e80d40070300301488031001032017071250032500004422107156030643c0100007101b66007690f002c1c0d90301d4425003240d0782e84200429400c07601008060091401e008108080c000d00b2507405902c0700e030a680d011a5030390b0006e0720480d0120395540140000c041e04080c10b9040341310118001c020401b00c54000602ca1015030103814081c4800340c000c15018032407501110303002e00310300b08026516503540002560300d9004036015991941144041100880c1500c845001c51710100021410403000181c05072491002400843c1544030403c81000003000a018200080004038000c5c11805601414401902e64050482080d039161204c825014440c041c010341c1256010702d00181c4403e0b1400c0428001d200303607000f002c0304061000c030aa00012000c00c0c6188511302c1010b8561020380d0b00403030325600107030501004281e038841c0c1c80000c4228400009614065000070000300c3c10406001c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 283751843 1250 283750593 283750613
    0x1d120102210403090e04020907050c100c02030a080105090411060f040504050703020702100c0206030a110906070b04020a0b070b0f060105121519140d0206070b07050306040501210b09010603 83
    0x1164401d04004801c0000b41038004d81114003e02d5000040102c61401d5030000b00240001030458080c8007004c270b5000c0082004101030102d088882078204600a54801301030f50700e41150780380a001a2028001142c242001d84c0c12601441d40306210844001c02c1408000c40342e08010304c080e071501030a100c000b13000e40d038902806000c1c44094400682d0340010340148031984600100c181e0038032500211280c016120706040700d42c08004007500080020350081041074910a054065504c0b5001058072402d029441001d030703014501c21a0f004100580e20b9690002c1c6016140b0050005044031001803c8020419207040c1d01c8001450a035280c40d040e0b841104134a041903842c1403140048080781003190400240c3c044c05a1144020001400e00d8150780c2c41882e80c42c038035920300034000c62000604545845040d1a40c141e030050304180340307180802004003181c02c110342c1c0b503100da402c010001403c41d058251a072048c0601d030035102c2c451422a150b1140985010300f10b00c007a590380e41030000100e00013031a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 283753093 1250 283751843 283751887
    0x10031e15090f020c1c0e090a05180703080d020f04030209090c0325210203060702010b130903050304030c02060c0a0f060b010318110103151707061d120102 68
    0x1a10504460030580c201c030840b0316401402e042184100118980007600196203943c9207642a8003142801c000c041c11124990000400c03500004100184104404143c11151051041404951f0000c250305426070355417403e4400a000e84004100304130072041c854004180981e41131404615007039581c2e000c5502280d0444034003165030000e400805d02891b040c4040084412000300d8070a030b100300d401c5545010f008520441d140d0003039590300088069902002c0742c51244c0c004082d14494500036402038040d1642401c1d6a11030031400fa40044114068491000d84603015910305003942d4480e6015038400b12003400c107a80c8100180074000341c90400300000c0b09035501c6a2010700b0a401286040c009645a900209040c9070404000750743c4903aa003880590300741d40050804040030f01c2403005074024400039070188040440d041d030109030180c0320b10f0120230b40e8910350200e5007403e50b20303042240c0b140312002c1ca6a03809203046042c42c2851400b0303100307801c2444a950006280140b80441110103c3c5145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 283754343 1250 283753093 283753121
    0x2060f2a010f05010608010b091210110310080307030f081807060309020f040209090c0a030f06090606020c010822111206010e0108071401050a1709030910050910031e 73
    0x1a80d0b901d6082a540a014010301450030702c5181c42d4100111160309002c3c0d116428040c5200c402c12046440c0708000b81203654070500c00420a010030088080c0440d8811100144c1c050b1030320400040c075a000204840d00303580c040e99501002c8004500884103018098040e60000d8100e10040e00e481a0510000c401010b56440005440c2c0562050000d00369044144510451040c030a000c025160102065030003202d1307190311a96013003085d005a004010f0840c1060125140171004100d1391aa940141d0030f4600503000c45075003408500c011501e07014120f50301c44080621045030b0360080029901d11040d90310a10411000410340004202c07042c01c4116040100d0740514010046001340f00f42d49405085d001c0c000d010800d007072403081001b04500840c2103042000010300c0604c0544101e90030302014021101000150070103019140d82d80e00010200f903c202c4496052862090082080390a4404007800f01030000c031500a09800400e01000710704845c028200054540041e544607125a80c150344e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 283755593 1250 283754343 283754351
    0x100c14060c03090c090603100207052104090b041803140412051e1908030705070b130209060a030215030408042d05010302070b0f0604020c070303030b030c0d02060f2a01 74
    0x841103c0d1310b0007941201c020b000314091800d00035039440103c2c0d00340c0302c0000d038a80036076240010718007a4503128016000150340d8100d1401800d6614a580080044982101041c000b030100c02d400c2004840300c0c81e40c0e000350f05248281d80c9002901074100e035224285921040c900b003e94071301161440e040c500a08980940001d40080500100e207088448040780c001c00500c02c00499030490506003007006005444010f002c80003481992150044940480d801700508600b801c084160301d00c0460745030001ca129100407000113003503040542d100001c59800070041c680e168038100d20000a42d202400980380b5445c02c100c0401d011210700d141d580d03050100d412a102000450100704110441034000c9410103004004040105110054194126680200c82c401c035440344c50028000b44110380e0001954091440300100f070541560021046110681c1074a2a1124010030000001241e1400944c4040240411b942c01140030000c1c0c030001d2040c5050070080d025440900743d103403080c110003600c0d40c2c1d10b03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 283756843 1250 283755593 283755601
    0x30f070c0608010501080a020d02040f09050a0c031503020d02040b060304120f080f0627011503140105032a0a030c05010f03140114030a120302040e0c09100c14060c03 73
    0x81000150300410301440e20003200d50400340024032204019094542c03968000c034030743c59400c03a99411140101848210b51000c5a9150800740152904640e82004030340780101e850340306030080c0075884445d080316a40007089411075003045001c04a08600b41d03002641d440d1144100c2e00e03180020750040d40104888440075900c5c8000030804500c81c000203081204020510152050300009103800100071103500500318180e003404022908582c00001b450315110300005290f00d201008004120001c0c4c1d03003880100166401410140f6085c40703000c3d01503004104104044580f100307940c1e22500c01c4110107030781035035800c0042c16282c0d282d00140c4024007182c1040209681081400a05a9850906000f030040100554070030060500c52102080c4c82000c400785035503818006400226400302d0450700750040103000500075001030190400c07008544012a05207601038094039441e11004050b0200b488507640100d650070f0b200e90044500c84420113074041585c8050041c180300301c48204a00703880c0d1030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 283758093 1250 283756843 283756853
    0x32306090a0908070201080702031303081c021923040603051e13020609031203090c0a080304080601140a090207030206100f0302130c2a05010b040203061305040204020c030f07 77
    0x20300604600c405920b440400400140040103403030041d030702402e1140c41c1c0c0c0e4036a01c003a070440c45143c003401d03041c0b152060007204202d0414007801241d5440311540144642d0402c2c10760032480b4905046803054402895000c28074814160711214030000c20b41410140001c0320001c09942240e046400803079140d0f000c10070a02006014001b480040e00603000c028140f502c1c5092001e140d503000072b400f0f0030300050400c4440d00e08103d0030400c1280b118002d1b0340c074a07107011455161b11400d40303468491400c0400004040e2000415501a03907030103800740000da445c100184400440c44080c66401c580b160500140240152001e064080c2c020340141020f0b2034442145060954140c0112146040d0b0715014009a1202039030921503c6001400091940c071241058a11030100114036400241303881502e8040b80c0391550040c0c5d00c034403400091107001e04c02d00802c000c0e400226079080d001001440c88145103401038210940081c0090300041c03400642c50358140c01c561120090000703c4c1c000007000c0c1e01b008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 283759343 1250 283758093 283758109
    0x3040b0a020c040902100f2106080f031201060c050a0f0b070809010c050901030f0b1f030f060b07200a0620070e0f15130f0f09030915032306 62
    0xa03000c82e01007001c41d1341307580020129100c42d8002c1040100050709800454042d0700b0b01e015841c016400b080014181c03400c004050080d5004203c82c40c003504100202045001040e25403040300d5405c0c8802e541e003050822112081c5031079061b00c580c41140800c03c04201d0100842c13661174056623040c840391502132030142101a000c0c0100c1c3c440c1e81351a07a20b80b015039200003541d04585007482d02080400d4940da2200280084060403139000011090140d120724207007184141400c025201408120009040d540844006204406081d0410004400001c411080744d0090800d444e502181411140011800c1d5090507003003c004101b11014502e1040c004035044440901c1e8000180081c2d410940700d0106171402038084801c401440003c1040b610601059044007500070741040d0600303414801c3d09004e000c1e0301041000305072500c02c180b801400c0d58090b290005806441da1200e040c5844051001070515960100400d50f0f40c0d105049200d03040b148201c0c144844094078101814814100a52a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 283760593 1250 283759343 283759363
    0x3050306030d090605030703020a0306081603021e0306010611100606200105040218062d0414061503100509010f060f080f150109030b07020703050601080f070b09010203090303040b0a02 81
    0x7100024000300491648217040b03a03031000c101d203400742c2c403a21001c4040c1d0281001c0d800c40a424010b070303082c43d450110b15070141c80c12240200d0300da50310580c039104c01030b04103080e0000080c0c00d07800c200010301160b40610408004141c1400c00c44115200344c00d5940c003119220741019000505e00c10341c050b4010708e02000c4c0060b5600d488c0080015003003035130000395801e4401c14852034902001001902c4e0395201040f0324040d4440c071403441c05c01d00400389000310100ca0550303d5840340346404001ca6419004d603a6252007100090403805426022144448160f003000304643e400c4204801c0c040398607169500c84a00a0440c0380c1001c40c0c00b4205000a1b004450081d803800820105c90304015080ba2281020358009002c0d88100441c402d400c1c0049842921581015240704808428004a00e90000d440e000f102e002d01b007540c006988801d40551600020100c0d0501540500828000c45c0300c018001c200c080320500480307240140b06400b003801d48d0015401807851080c0418801080c540510032a0b4003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 283761843 1250 283760593 283760597
    0x40606030309270f0e030c0d1d012c0a060513060809060106050d0902090f0f1506090112140f150616080304020109031b030c0b07020319030905090403050306030d 71
    0x8a000d24150300041c01c0c030a4286241d0b070f1a141d0200c00b2071402203500818942d04044256540c1c0e0305241541030b950205c0c601303801d000510003a50f040342d08100c1207980b21807110595800c10410b80d203900301010301001901103241900c1d0548043e415075070741d203a81310040c01c00f070300d40f29200c0110004802c0c50f04171a50001c02444098802c01c4459040480c4160645c1d030a800c0440d01d84c400d03418a50010000510002e4000340308d00d061008403410000c8582c800c114000144c040b17640c4244440c1e90108400300c419411450600140859601503c0182040c5002220014603401d4100d8215205901a0b6440382d210382c1303d005104204140f40340303001c1c103410240d80281c03400108400c1301d00c87c01074044014000000100101e4110780c0b0410703481c8021030b04500c56415142104e0f144c0d0072440350a1108466584403800f0000700140c50700252942c040d00280503201c5280d0100c5480c6159840c803108500b00501d1540101d0ba41e958061141c0c05580241d4640341ca03071801d80c00b0306250060041e41ca1003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 283763093 1250 283761843 283761869
    0x21b07060906020615010905090a090803010b040311031b01110f01050f0601110c0a050607080904090804080c040603020a0308090a1203020106060806031501030311030c0a050c040507090803250b040606030309 91
    0xd851b98101c40e215040303550980f0015099500e1038240382c01400901c0004145540020002815144040140059034012200785142d8003002040650703960540600d0046031070a041c809215601402e03a500313408089201f520403c014028950f801c40d501100c0c1601448001c10a003d02568400d07203206c1221800001803a140c2200800140c280b200b52060a00c5601c0004001d02003100c0c800c00d07540c180e10050b109202d1b4030894030b440d8000307803c00d00038694140705003001003a052401c1d00482013140e030040c0240139030604603200c40c07015074071286456820804020700000c0e880b120001441c2c45500035400042c046040c114010212600540b10074840c0d400a0a4482c507242030962030341c11260725090031400c02d4540b20340141103000c0c015440c6c40500841c1c0c1d400e000c4c08004600b2880e0080c080701d04001c20f03983d18000303403440b0303525000f1800e4907441446031118841d500700c000d00c7c8131500c007c3d04500c02807865540d881c02030001c031030466990791101d40030020141c00540001c0a4110764003026 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 283764343 1250 283763093 283763131
    0xb03061503101a0f040909080403060c0c1401290409080403080432130b0316090f050702030a03090201020307060f0902030c03010e1b12010e030c0607180603021b070609060206 77
    0xc0403170b010f00c0c020440034682d9200030000304070b0400210390045510490500400344102000f403c0906085000c1d100e100071030840105400040c823400c00b45600c101c207211402c0310902c01da14440240450141d41280d40e401d402c2003c02c00c144040d10045d0b10610030f0558881c2040b1150703c0c1003446142c40c00403103106071001131554030b0003018503c00740c4e0240d07486000c02c04d64a124030b01800c1500029501745c0614031545d03242d124890015019034030420002d1114003000d04040f812601c04840410040e04207014180d030341803082c0c003c041c2850051040b6410555182c03207810444840500c10300125540b0445042181024415072010030800c5000b0444a00254042d84d01d4a11500c90b010703007807610000c00e400c6551040c25207464441d03287c0081001902d55445d06980e07510010350520b50307201c2e6400098040b0300c40c003104a841d801441000200a251031420f4010350002c001b000300c0403a400b0500d10b41c0d19020801c1a00800c0c2c0760340c401220b140340c200b02070704180024001c1c00700912a11012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 283765593 1250 283764343 283764367
    0x30030507050a080a0603080c160f12080a1e030218010804020109090b0a0801050403022503080f18031002041d04080a08040312020408011b050a08010b03061503101a 72
    0x10b260403468a0814854581e10f040d45503000305256040205610b5001c40c4164001c500014800400c05507025400d80203511003c003003041890601c5403106100018180d90009010381c0003a214a03030701424080940841d000010180c175690102e0100060f50202c0d048c07400c8a00e581034690400b1082c00c00e5041c074201500024038441140c054070440d1078644aa194041c0c4a110b4440c0007003542100030811400d1901d4025207031040d00000904108008000004040305c2154000442e5808410903113440d004142442c01c0d40c0140000c1c0ea01c0b803290703040008040d00d061102e2031901c070718a030f401a81c4a050407007034690500d0f000484a45415850b081000244012044aa40003d54103044440b0756903071404403900318180c202c0000741e5002080c005082001504240b00840d09040200e0394801150b0701103641d4064980840300041c40340d00104518a003e034001c542201d0060654500c01c445030b000750445500c240e4a210b88a03070088010070003241c03d0b010752540980c004000314503111542038a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 283766843 1250 283765593 283765597
    0x92403050703021314030307020a030f050d05190c030e06070606030b0a1107080f040b0c0307020f092a090307030c0e01080102161b030c0602030307180f1406073003050705 75
    0x880030045200000d548166a040050b83c408e0f66000b4100d15180d0745900d044080942d14203021101807113901c0000c0c18a40c000c40c180c0d03221019030004603c43c50505001224100b000250643c00d0005160004020341c0361070005145c800d000f080d01281943c41c600d40001071440040c195100781e8681000c500c1c1c003240c040102c440d2540c00141b41c2c1d8442004000d608100d02c9940d00101c10030384001607005100034084040c14103103000721407072640005608140302803140111040410340c1e188032000b20005c11020404000f40049803407007410640c041c008a03113082d10540058550300800d0714100090f05007402160301504c0490000d604201190144481d070a42021000b0840805507403100c02007100c80440701c0c0215042562041d4050350740c48041e4072a40240d40038000a034100c2180204890111880d404940b554000070300d640385040c3c1d000c00d4410710b00c000c142c3d001504104040c041a04d8015a00b054041522001c0940e401c4402134181e00f1090654070b8141420281049006600401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 283768093 1250 283766843 283766849
    0xb030c04020315060403051b03030a0915020106030203010c0c06050606040e0705030910060b071e0203100906022a1507020d03110918191e0c0924030507030213 70
    0xe009600c03901d0364516503085403060600340d41c0214020400000b800030010740d1032181a0410020b034140d44641d014140c4034880c010414000c180141810051108601c10445100c005403000085040c0c6a070700090a60f071000f0015800603002e8500c107001c1c0704003807140b590000f00c222422131030a8a000d051040181e4014141e1090103000300015450712001d020320301c0c0340c02079088100180c58807551841000c0c0c008200a40700e0400d5090340b40e00030b41c190601400781c190020002c1207400002da45202c064240390304220344903a020f201500f060701c08000c8a03c5e460a0005c0c401180c40c20035042e49207400c1c0740c0510307012480c1c0e10038148003616402040b8444a030001d440d01040d0200c080c0840c0c0050705c00d000300c031600b000b2030071201a0115000c1c0d2001e40100016200790340c146900c01d90100580e494081e8140c0c0064002c50315001e00d203400d078890b09080c441420202005669040140c543e050005013102c031030501c0d04021418168180b0685a12440e9030030210b0801140003d0002425101c3c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 283769343 1250 283768093 283768099
    0x3050604030f0903052d0102031504020d060306141503150a0506060f0c0708060721090321230106020616021c050d1103070c080d0906050711100b030c 66
    0x200004410f104040b81e03000745030450106c40f403030740c0340d440301039004010034034154501c40035074a0201c4550418000c8a0243c031540c4814490400840f04100003540f11005000c800307507842e080000056050300401d21101448050501c25150180b002d001400d03c1107100351280d04000d002c58891042000d0158100000300c0c1c4c002000e5a4100c0803c4580c4210302070b0741424038001c9018041d0700c000040c0a010313190392005071451600c0305541030742d614044030342d4400f40d01000352107182c0b009129070000d0307000c41c003d18041a401e40b8819603007550785481c0012100c0103444a074454940f18005001500684c0c210698180940c903101c0002e44400000e42400041c0c05202070381e08005100b0041c0305814030314441d054401c0080303001c000c1e14551044207014541401c1c2250080006050020f4912070501c985460070544825600c03054294082c02e4200c402d55912105140480d00e40c0c8140d03442808103441d0344d4060001c0d60740b501d2034a07404000c5000310905101e1100110748000c10b02d200c020900b6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 283770593 1250 283769343 283769357
    0x140c16060c0201020403060524030d0c0303020d021303030c050601141e010e061306320a11190b090a051f021b0a0311070b1c0b15030a0b030102040305060403 69
    0x7030040303001e4807075580098041030400050213140c00304c92241c01011013813030f00072410070205a030505880d448000c40090101d03000201d20700100f406a00145986807104000502d401c82d00e090502c981c50b03150f00140c00180c080035000d010002e080003568050b000b450940c6550a440c0310004aa117a845050011400505003060304664041c0110310603807000100080d403903c40c00c0d21a241c1940880c41080d0000d454050600c00504030440c1c80d100005010950246c212810314041259a00010700c250400800010544050800b031008070f00002112810214180d400c2c141300015060250a1900a801c8517680c44d00250300014508409030010454500e08404802c0340c038002e018002c1d03014004101809080c040038800319115020600c00e4848110000c08548041d80c1e5043c54003591401060802071516a89003161400303044c10f0706e8000c0420711402c1da402041e06104e500c41a410040001300502c100000c941c0030b04244200203500850409265032100d1342d07119000780015041c0405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 283771843 1250 283770593 283770611
    0xa050a0210020a150f060506030c070f03050c011a0a170601261209010f1b0803060a3305070201050409090204090503030c12011a1e090409030201140c1606 68
    0x1e01c09030034a1030308080344000030f00c0003402c041c4c050143c444002140e14944403000c40e59142a4094902984c01209034509050940d51000e420400c904c1d01130301401400d110f8811940c0d02401001101141600d24540c505894010300c03c070091180c02030b030b18110300749840b00c40d406000181c050455407440030300c61000030600c43c1480380510308080a0b85e280a070060200d10603c0d00402084180003e03621800c00c080c150030121080ca0740d031000121004031051441000c27030186800303140c0092000305503c580c69a6050021104540200c249040c4480210542d04000f850340000042000608010f4036000311540020304500c01d9000d0810034070b0b9500d4000f070942d2a07034dd0145404a610400301c03a50703820121300c8000c0c40e4000b5286144410481c00000c00c1d40009110118031010400c41800e041c0710788440620005404403281009000c400d2044251680d138a018160700c02d806a000000d4580444000380091403000341400501c0380304114030901114424004100701e034002c0400215501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 283773093 1250 283771843 283771847
    0xd050606041203030504120c2001021903020a03020f0d0f0c050705042c03090d02060d0e060c0a08010e10050111030d0603030504140103270501061a04060207080a050a0210 75
    0x45400c807110341d100a89410b002c06406502a90155000e00c140584002c5c00d520129081510780e00014280060914103144103800c0c0c07c40000c5000c4140107480020408040070382900780342410542c0140d02040034401410f0301481040c5124480c00060182407811a1000d09018010300c0020308000f0340b0665081488801c1c04804050305000b4070038401c0b218240c03c130200580d0b011194803500400300700480700e00c1c10b00004a407031301007000d03000d648042d000b81c0030811590094250a261940c461640c001100740501096124511500f400e43d1540d4404034002d00440d016003101c5030755680001800f000500c0017840c1d20031100240b80290390f201603020b03001e0441c00b49149407400241004c0000c0201a08440948183d0703640605d00e01a10600000450540b40c1208d802c1003480640100c1c56040850300103000801802000041134880d030f82c07090413110302c5180c0154611220046024801c3c03a0341030140318000c2c01d0a130020301442090703031100c540b601074034140284141d05000050170128 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 283774343 1250 283773093 283773097
    0x14180f060c0f070b090f04110c010906020a030b1c17071a0105040f02030f04292409090309060307140a0906020c0109060801031101031103090a02150406050d050606 72
    0x4840a401151a0010312044a0740c40c0442800c6030b4080c02040f4010810803901c43c15224900d070020182c1d00400310410901000300400e100d0300074600c104000030400c241d024012015052710580c0b00507613401422800501311480d07048804e1103045001c00100c0300488042d40c076a4026045540d50715001c012022230b11591007942c1005145c40c41c19100941e00031662844107040310f4017500e043c40005803c0b00540220302c4200e600303004150740c2038081804510341425864641d0700010844103021000d510f440c3c6200e001312400c2da171641c010101052162403020b840d82c0884001c2d05d00d01280d04080c1d040544070b014401066026910100c00505058451183c0c91502c14001c5101c6583e1245141c004140d2142406075070058460000915100d500c100b113000200c83e83ca983da1003803642103580b520121411b5407030740c80c1010b0b121079510707141e80030610045002c0c1818000820580c45c480c07040c041e25440391141e114802c4418002000030035000011503003000035074040058a540c03200c00082c254 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 283775593 1250 283774343 283774369
    0x40b090105130305010501180504080315030f01060e0a0e06040302150a091a100e0601050a110a052424040e0a0b0a0c031503030c021212030c07121418 66
    0x102c141c030b0600200703000040d8006030584042603126030418103041010781c15640c040e6001012958204000303004000b106c22a007038120780080681d00c4004100302c0807825919542c000c40844120b80d010f0052075191403180148400c1000003420840c43d0a07240a5103421304405082031040c0c03800002440042d050b0707c6801e0030b42c2c1c805c2d05082e00000501d0070f000240d508448480005d424540085038000c400c010851051505070348107031400a221008503070070300c610b56020b00347d446400d80b6540060014000400c10152680d00c5a4901c040300c0c02d860003402000e400d20710001380440441c5160358054000104140d01034501046440c440e0340041d1800480c00005070022101405112110240ba0440f50031501580c0d028040180c0c03035520184080c2242c40300070089500321071032100508107c40260725411070081510188000300c0415500c03540200d03030780a83c00100061800070824400300c1c10030002041d04d024a9040c4884503614079910030405050040004031111401d0384c0e0b5040105580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 283776843 1250 283775593 283775617
    0x2070204090b0906090a0b0105010e0109090c111c0507061e0c020619060f0614041212111605120703060f050105010e01020607080a020307050c03071103010c0c020303040b090105 78
    0x400072420b0915105200f6140035142d401024007060050800140e03109006800441204140e486c01c401921504c0400c032440e4140301c24071030005503100180c880c502c1102000e48132200b12408e0b07019410309143c0490380101c0f1100302032507500c083c076a201d021340e41c0c2c482e44002c0010b00200e140400c09100c040031401079a40e0ba062089042400d54040351460180101c400ae1703060103540520340c80280d40c082d008016017400344510810941e17104e0b03920111307041c00d2901c01501d041c1e21042c02040c0120500010b8a07034040001f5040362040e4081513208070040000050308039081d01341d03525407040c14144a5148609441e1646500904060150400541c1d21440400410001403d002c01402003441854046000d03140c5068041d40007003440c3c0e1190056658030781c55541c1d1000000001c3d0806442001044000d01046c40c218400b0001805004d0281c0481014032410408060030b445103018201c007004201c65030180140c5000043d60141d80705c010704607445d1801c19004071440c4c0240c465400d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 283778093 1250 283776843 283776851
    0x71209021302160b10080312100e0903030603060a060819020307080d0903020307080609030d1a0a08011b030e1203040812100807060302090d02010e01140a02070801180f0b0a02070204 80
    0x40c0c40c240b90404110b000d881610400f913580d650400013960710416206604281e04208094040ea00d20310068a90040160304842e840395143c3c082c098003000f0441e81c4081541c80001448064a010014113a000d076040d8400e000f80781c10082034980329000d40d0b581d0034800b0750410300c00c0110f41c1c1c14030065018000f650200d801c50789580f00014030320b003042d1005038020b000d680700110f100c100c045005032040448000031494174139081c9070140245402584880c1d0b05042c20004c40e12030b41c0d8800454004c2c00800c0c000305061081d0740e040c009034a4409100018189421203501c03000d80041901154103e00020941c0c0703a55541c1013001040c441d030487d14650b40000c0c8100581001483c18100c140c0300100210f45d42940c446c1019001c0b0320913011296403010402140310b00541c841c0100007034004d410300d006c049003409050384050b81e07082640520050b80040c54107101030385007445080141d800700d00030709031401e5503500d44440041c00c00e034003d032261540000244152240d60100d41c1e811b580070300104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 283779343 1250 283778093 283778107
    0x90a020a1806171b09040302030f1305060409021b010506032e05011509151d130906021902070b0307180f030b01050a0509091b030a02060c071409071209021302 70
    0x81e407100344c40051061140b541c503100281c0350400544080c42540c0c503400a40c9444550340f0400d02c913401401104c03041e5220000041070760b48a44000d0001030000d02005a11580d204101544020380c40016039001c0c0c0c5401c0c01c108050760001500c03010722034000c0342c1101c8031261010362803800409080302001d1034240380002a0400c15201030030b000d035003241e031210a081d449441740c00c5100d19403c280000942034001d09690301403109256228031000502c2da800c801d0b01040e641e4150b07400d400083e5501a070101e241d450070201841400f03180c004510142c083e460420a40945501000e01901c041090780010410003200ea2842403018104414040807010b03504c2c41e247e8004202402580e0140103030450010796410303c01c074168003681c2244040c1912100e4550506400d10501401d140e143c0b145041280168460200408400344111f010707010f040e00f484202005510380b10710185c001e520103810000802e61101c00281144442800801c0700442c50000070b0005190241003585903100117102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 283780593 1250 283779343 283779389
    0x14040804050a06020607090303030b0d020301051302030138030a080417070e070e120c041401090c020c0d06050c0405091e01091509110d150608090a020a1806 69
    0x5031088030310450b00c101c091038960074100d840d00416240304011481c01c040a0000034001d40051900c140003800600c88640d00b50002801d544041d1346115203060021b01d810254142030045080310209913620104100350060150403800080e4050140c80d80c0405180c0c11a85d030501c442050035802c403450035108e03a1903095805901c1d102d814282c04d14800c0c030900061220703440065500c96142501c682d102a403511302448031100d031a400c5014280282400148156a94480c1c1007805458006600700b0b90f04045404040301c607202608002c0d98402d8505414a90710044081c10081d40102d001c211a101c0b600c0c50540c600842c1c01059010400fa010840300d50442c03085182114200d01c2c0c80d81c99642d82c0d0281c1011146080b941010030604075400384105542600035110000b00540e10f02c0c42c0c41c0070309101b0390803104094107030902c1511f1000c0800071b0640c4460800e80101c80304000d0034040d10b15500086400d81c1e40e1082911402030700d041030318940d025620540c020b040c030101c101d0213410b0310810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 283781843 1250 283780593 283780597
    0x5030a06080f060a0c030b10030c030b1c060e0601140d030207030215090301050f2707030602131a0c1c050c0a23160b09060f040617010e060d031101140408 68
    0x344e220355192080c010b070030b00c1c4a4000e4075910600035000c2c000681d00a20704070094151406003806050b11070301081e4041c0ca407001007140034008400e50018417140c500d00042038407010224807020b40d111000521406100541c0e400640030100c8001d40d00b4100e03890160300340703803440d0320107544010340112200518400400a004130701c012002006660b5440400380e0303420790140e644034a50042c41900030310542d0b0040e0107880322401f0108550310a03a0b6640d4200903680245080000041504000c0046184403104d02444070b40e0b0039060303810a000c100d0303100da80705030740b800c00010181c07038180b90b06500d8090412144440c5510003030307031000541c90414080300000240810f5428400410000700b414020030078000c200007001c55096000d00e8444540240e0700501036496100004101520f81005800c000303000404aa40b140d01403808912526208440160b0280912054603020002a691251344020003982e1508000c0010324142e20b04d54014034860340f54040c4140d8035030500c4240704034440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 283783093 1250 283781843 283781851
    0x1c0e0c013005180613060507030b060705010e01050106051e03070e04090506070207061b20060a02160f05060306150f07060e10020403020a06080c0f0a0806010f09060c0305030a06080f06 81
    0x40d2850101d001001c0e941c1e004d04441304900f0301500025070300042d11603000300d500410300d40f0300490340d00f0720100050441d80c00b00c50211441d079549d11f448150107600b0701441e40180003a04146086c24020000300c1c59203405030300c502c0b081c00f000000050206000303c40409003120060b1082003c4061898039654420050314454094403428a00064103441050061503845075200d40c440700203840d03030b50300080d08490036a0320350301d00c13489e00e4026150312180b01910404103941c3c000c1c80280c0000204c2c202080c82074210000e136014007202400340c0d480302d404503900018160b8501c0351800700308001c0e06040c0200854060881400107800090200e00d03000304505d012400d0645c0c07044450124000300701c3c0f040303100080d040f8142e0503081000358000c90406501c001084156442c00392503e000c0a00f0340d00c25840031001c144100140880c42d43d016101d410030300524107002e01c15905192003d0f042c5405007600804000000000039400e0b405a0086070091204c0011680340c017003135101e01600c2d254126 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 283784343 1250 283783093 283783111
    0x180807021509060f1b01020c150c04030b180a080a020c0f04230c21041506060516140601032406050f040b1804081c0e0c013005 56
    0x601c68103000540d0004403040b2400c02000f81e03207070003a824888a880d81003441000d101e01440f00001201c0c010070f00003820b00d5100301c40501968500400e8142281c10050640502d8110070301040c4006190b0482080c0c203c01d00e92200b042091000385401e142000c4200b00600005000c102090302036000500c10322190340884800f40740d1400407061108485800c1c400b41d010321131002c00002072280e50b07101c86030040e040e4509580351125036441c2c01c1840c41c1001c080000c4588510401041c004004040c81b40b00c010801c2c2031103803900c0d041c0001c10a0144141d080441c520850100c410002d40060106e013103840c403802d8440640c2e5178100940c1001003d074400410410840c40c4e03241032039041c0710340015580010540814000b184061000034013046041039040041006120511410084818804d6114001d000c1d5505461043c6075003003038503203403c0e070803207414140300e0500000c01055032801107c080c607120110f0480851048800140500310b400e000d849c0c03000300c18003c942e940005218a101d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 283785593 1250 283784343 283784359
    0x8010c02060c0a0318060e06010303081e15030304050a08060f01082e110304061b050711060702041e0608011508030a0c0206040b0c01090c050405090303040f0618080702 74
    0x25510590300c8200803244141c46000400c8494040d03800790b072000c0b0b032288403818030000080c0540c1e0350100b00c82c01200b00a41d15400030004008041d4041e04e029805015001c85008030070900b0407805441c1c102034a00804140540a11802600c0400030f41d0b005080c01048003200c165100e19140d02c40406480350001140590b0000c074072400c0c0040c90802c1401e0100e545024400851001401d282071414150b005580350f0000c4041c5001120107580101e01030500011901408104c110111100403841720610106004003c04201e0101501445080c1554841d995100c10b200003001000c0c02240f51003051480f8501600f08400c5a0144d411354003800d0003004192000d0100050442c1584103c104640c410084194003d200d51401600c0314030180003103080030b0712848207884030b4003c00c0050b10544c1d52102a20240f000d00e89041c07004041c195270800c16030820001480c0c607031100170405403003035000c1d1341041e040003615403206182c4420074142300117500365232810000380d51181d03038141e11981a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 283786843 1250 283785593 283785611
    0x1104051009061d01021e0303070801050a050607110d0803010e1006231602030106092f0301061b0f1a07030501060207050d03090503070608100b0405031f09050f0303010801 75
    0x81c0341e420180d81141d203400d180c0c580c0c00110b00c40381d1582240182e0450186200e045141d50300340000c00d8007024400050b45c2caa10349000e0003800800164441480b03142901c20402003a10f82000301c0d000b00d6000347c01c40703404030f81130404619403030740c0b0b404010042c070300c0003000050700781103c00d00034013804d0b90f2600481e100f80d44140455078441801c48110711034480c0c0900d604410079200003003038034814400f0071003044100750300040e017181c82c0750303000b0700c1d140b61241c904266003c40713007001c0203c071110b1000c92030a4800f60100c01c80140014007034081804001c45910092584e4118003040007903010001c58501119403a0031240c14400c00311032015032030100c01080d8694081c4c042c0314181c400c254020300d035980c581410440d000114207010b4051080c1d075040450f0584082c09044042c01c86900d5620060400c5483e0318036212a1b036201142e1034400740001e000d582d5000c5212401c40b8410b9001c00099000e0f10310390700007011800300040c40b500c07581d41e100c0c06011000c00510704030b9031414000c00203904 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 283788093 1250 283786843 283786847
    0x140606090c0306010801151e0305060f011803020609060d0c09060305070c030c080a180f05010207050306040b060f120d020a05010c111510051306050319021c1511040510 74
    0x42070743d14901144990005110311102c155042511269924206025031040031102d2405c000c0001a000040d0f199000c00202c2d00704284031291a440038600659000c000c4050180b60f4085400003c1c0704050004800130503070740d580241d503a854000c0400b0031000c41c1c440400750045010b445043c011a041c40c002400340d0b80280003180d17205825484403401241103989404d4a0f61000202c0b0701400550b8014200700310b0741c1d00f4160040d05100c41041c54060500d030000e85899401e50120744240e1000b001c02000404140000c0e401100035078906031100700300310000306c41c0540b138000301c0c0e060b108019074038901d146c1c00903140c2d4025001d00020041000f003164119051a0000751280440c1c0c0541044100d80084424a43d170010501007020640350b22100085d40101101074040b400c5510348200b40544d01c2c00303001103240858842c00f000d148181710342c0455580d044034010f8510081c000c0304d4400c1408080398204501c01400001001200c2c603010f8010346580150140a0044050458000003d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 283789343 1250 283788093 283788097
    0x17070501150803030f0c0d021308071502100e032b1508070b0d09050105070f020708030928030503390a0b10120c14040618020f07140606090c 62
    0x1d000d0b5070281d03141d41e684226a0020050141c440c1050080421010390100007920151480d11140003d01010710f00d009842442c00c0d449401c41c3c2c100c10904641da8089035000254000c00b4560b009011580c022104026400d5001d15850300011030110941840060700140850000e00360003030040040e0b041070302490401441c540a00d440d158040e102c140301d540340200107000c1c044900342c0042040341450f0740316400e59038107680721404110019040041d154040c03220f10040d0281c04002c0d81000d100c0000690800d4005207402113150f42d11509101c2d864100180d800950741040441b0303a6003620344901c24599035141c4225400170700284041c8201403040180c1d54580c90190010201010b0320703150070a03140c4001d4010a5044034404002036040c0c080c0e0405110180584003901d0342034a0f260a024803100c01004c2d062003145401c5003404406504130359414038100e02040140c40300ca00f80c0316103030380e4403031304001070250140c00c0b4084821020004003c1c3c403d040c103840425031071700d41200c101102c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 283790593 1250 283789343 283789349
    0xa0602121302061813060f05010f0c051f09060606051306021b040e0a050a0303090605130b0408030c0f0c0c0301140c1c0906020c0114060d0206071e1707050115 70
    0x4401c01a4020308025102045403040780102400a5003443d10740110072906c8030741c0034007202001810108040c0d80c115000da507207409581803140703210031640d842503190b4080104841010300c414180c410040c0d110b52180d9911030340000e08122940d118540a48a500306510840d5503110043c40424010310104100b400540c3d00840f0110f205503248c200710280c50f006401e2822131282900042c08250104a0184c80900a8031300040c03018181c10010f0075039000904c001c0300052019410000140e100c2c0e111507005400c07c24146d1a51100c01c8620005e01c90000030442c07889011620415840012070003a081c1c90b0120b008110074400c400600d6080310003190303648421031080c4640021a002c482d0024000c4501e0389000801d2802603440000301e81050380341418580d516400c0754081005046040d410100844200c600341c5c10710350020f00d0038490442c0081040602c07a000c0e0f031003039002d01900306140340d11006060301540504080c0e0070a80050301d056038550708125aa03441909082080825 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 283791843 1250 283790593 283790599
    0xc021e090a061a07020f0a0603151202030a0605060102070f0e19051909030201021e03060f091501272702070312020702190b072306011e05030a0602121302 68
    0x45800f00b0607105203150080c44059810260302080065599907020754000904411b8800041c0034803502c2c20f80c00141480e41001d00e102ca60050043d025a900141030964070b5880074001c90503980e00381c0100e0600040c0c2c0d1200410111508000c03501d42c1013651014420541641c882d03e4042103c80803009584050b91403070103410940c80d81c0c1c40c000a664004015242c0240000351400d01c42c603494055000c86400d4407411080003000b03000084c5020010484c2d01c600844440a00d806c24406203054020303541e0803d0705100081c1120011603605c5819404281c1103003480541e055a641001c2c1840c00300e004c4808017804080101a007540742c00d100742e4000e40d80558401c0180d400f4050b841000313500c50341003070ba4400214592860302e10b841d024524090000c1c450440d4035005a8a00b1200410650303509907240b404c0405805040d000014076a811220714504006000307400040600600106802164040c080c9241000510256800502c00c40c0e080e0b2084104640e500315081034621442078000b54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 283793093 1250 283791843 283791869
    0x60f111206090411130207051b01030c02061006110109050304120b090601030f03030e15040804090e0c13090201090810020304030914030619110c0c011404120209070c021e090a06 78
    0xe00c41c1040d174107030f00c1901c0c104d80d0014900b9038a5103030b03245480b65813880d00094038070340a8107030100c0d6858014446140690300090905040c80510450b4640142c0100402c11411490302d40e90351009401804140d0340000549698070b0b1645402d4240c000c0d442d105039180310101c404500b050754000342e082c3c1200c0e0089204400300741540c0d4100d0107010340c030043d066070b441135a900c010019200c0070894020762040c04450360b950700e8070b40b0401c01e4545905412225030464490060980c89110840c800501e03408000516170880d8801038401d002c864018008510034005c0039640e04070b840cae00450099029132640d160f00b50303507030000c2142e0841d00850700d6015040342c00801c0c208815074507120310b100d00c6101d01003002409903001d0074082e0014842c691059001d8a6661542d58000050703141110003241c1641c41d290400124400c1d40c0e40d5040020b002d000741d51700085c001e6109260b50910550300401c9900311100c0300d4898020700003c03450303440c80f503500310011507200c0311648100011a042c07170b20300742 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 283794343 1250 283793093 283793123
    0x10311180c160b1503010c110303060d0f0c1806050406060e01081b0d05040b150a0311011211032413050402061603050406020609030a0516060f1112060904 68
    0x1211074000a08196011402d000c0341e40015102d02100740c4a50302e400841c0b4182c4518804050a407400440024180a849035200d2110304000c400c8a40c0710400740c40588141806240034a10b1801902010301542c07007043c8003180c0f8589100f848205070015070010700061751a981003200720f492920403100410152a1040043c0d4000c020302c0e035104071450544110603880700c428444950100050000030b0341e1b00d004020420400d4140d031900a840c80f0b012807140d441075804645403036041d000207000c891207078042c240703e40e2040d6621001d040310f001d030030300154041590800890700140d401a0110328103841e003182c40012512140301b04100241040300c01c5118809043c020a806041030380c100504000710020320410016880703206100b60f407680e9943e07242980c000d041c22400760075a4403641041120020880e4403400740c500c100210100447e8180003407400e40000d0450000c1581c4082c01c04d8400c04401c13030703528042c04141c800450014070315615013040061814084800400d0184e241c0810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 283795593 1250 283794343 283794361
    0x105030c01140c03031003291305070305070b071406060105070f06020c1c03051f09090201120219020d02030307020a150f1406010e06040305120307020a0f1b0506121503011107050601031118 83
    0x128640cac003950680701c089880b52191400e00100c1d4000300000d1500190074020040f0180c4401c494050250281946041c880c00003800d500c9080780187c0f49503940b2004605019440d41210004034207041101d403484001c0740120011403645150701d02007031601002410809565400490a803021955030780028200940307400108510711042e03040280225040b00d00405910003000d00211302441110003c0001800a00d052945210002190018018000340715000105d0760201640711119001042070360a01c03c004029a01c1908a41810425918220b90007020080d01800080c6d035120350031501c500500c10688280e00c0010025403009007130b03104440d08040596008601841510646103250f15482f41048180c07000f07030b8840300c012050010a0300d080d142d6400130300742590480c1c00e10b1080704002c0c440c1100107000f84000d0082d00c06a03400d07998203500428105601500e12901ca081a0070041e96402013404200c58001992542440c0781c90007010f211500246020403030100e80d90000c139 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 283796843 1250 283795593 283795621
    0xf0e0a05101701110f070506060d0f0221032b111903320105010c0f02090408040b0c0606040608070f090b0f120609010b090105030c01140c0303100329 66
    0x38a02d665542c0d89141ca42c0308950200911813030305079404541e01e07507041e07041090a00c20090141440340c0e84025030b06000500c49400000342d01e0f01220f00c00c003003003082c141c4280300c9886481c0c02c102c1c0c6d00000440c0c1040c0003c515251810910b60f03007504440034405542c01c412200383c4521104540702c00d11070f200245a00d0f0602a808400078600800c840d0380d441034074641d210703a4000d03000c00b0031031018440138100c0b100c500d224010030302481c000c007540115440d030745464690b81030081e0085a0785000903080c882c21500319801400c4429409603249011081071784c60300d00c1910b100303200b103040c61400a000c40001031140c007507406414903044d0203031034442c0d044000d010b52201250452004040212203039100025065103403410400341030549402d4400b9421a0040d000203841005c0880042c451303130b1400507400340742d01c0080c01c1c10f4541c003504802d405041c0c010b04411061501c4000100000b0941845501080f240700c0d00c0c3d400c090b4003441d084034120700c4a401c41c1149180c4000001801d000607a69 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 283798093 1250 283796843 283796879
    0xe09070e1e06040f0e070c08033402010212060906150d110a0503010501020105100b0a05220603090b1303020d0e0f030d090f120206090108061206010f0e0a0510 70
    0x10816229080000208590760410352080d50038135003021080068101c0c42200c03503405020362070041d03030303450165031904500c1c0005081c1104a00619100295000568401030030009110484800e40c200c9800002c2c040d6101034000100c61810744c002c250b003400e003121841d01421380140142008411080001402c0d008411504180c64913801041e40b411182001081141c19541d545640c13581008006820768101030010010140c0d00f8000308442042c80c02651b074014200d103000c03035403609d410b112750400c0b881c038803980c1c20320055601000070b0060701540302d00fa1180c4501001c2142e0780d212210820b40310300c1c1d07440c0500540c0014244800e2284a201020003405004040e0402074445901281c5422a003c00c0c280c08584d9009041c4044502e0305106401050301d01c1503c0d400346010b60204905000d9179896034113000d03000c80401d02d20b44d14030f000c4203407070000002142d0307503503075a800c811110410620500740304040c1c00c004601c201e030080c000c0900c03074040f40c0c1111080e24604a000321082400c0c02c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 283799343 1250 283798093 283798129
    0x80705092d0403021509061501051303020405010801090501061a04060f090806040b011a0c030d110702031c0e010e01300c02060117032b090204050a09030e09070e 71
    0x85924910000d0010301ca0042e0300030350041a031214505c1d41e20402a00c05043d040d5030b580070b01d0402440102c02c000c4c01866810a280c607a450703885041c60440307848600c0e08007d5000c0d00300000800d86002c1540b0841c0e940d4044c500903c68556105031600c1c0c06000c0002c0d40f04012002c01060010030301a040c103400710101840c0040b0000ea6444101c0d040c880151411956070702074800411400024040720740b91107681b503c103185400c00b100760307140e03132071042d00b0110755a00e0f03c0f092086002c1d100081510b22143d000740983e843e41082141c0306011203490105a00450340700d401800f040d502c01c01c2190302500043e1901c040d80303002042081420100b415016103500c1e000010070180b91094010481d5103952030300200782030350600301d600814034a088210b040a030b00a000400e6490b5000040001c00410001400d01c00090303486003038042c0c4040304d806500182000248414809241d010000032406680c40031a941381400805c04240030689010f000903056440142e039618001c03447ca041083c0705 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 283800593 1250 283799343 283799401
    0x5011701030b040c050402031906060206090d110f0f0f070608060a0302040f0905010c0c02150f1e041211011101090b0601050a0207120803070909020c07090e030706141008070509 78
    0x1200054103030380c801c84039041580c021451270010400b04d03000f0000504400e00103440710b881c0404440d41e5562210f1a0034041104038481c000c070310201400006040c3c299001a24440c55003022400d0391202101100b14151280b5040019120b02c151300c05801180e00425010b4201c0c0383d42c0821018040d0403071103c1c00c250703a40e001c090000e13200340300b9a814848180c4400d80c1684041c01044011400d0000013a03ea84040015260401c03504040703501c5000e50905004000c1a841c400c4046409a83c0094041c02e40b50b03810035080c0582200d180c68420303002d0b03880e58581181144024240c07064284000c000b00c1c154030126005601940280c1100d8810344101c2d80003e03076030346140c00c074104910f4003918440400002d000303045621080000c00781460721015803074000404211966250107100c0c440d100307a62016600c0c8a003030140121003045400c5a0207202444200420818080054500314550b90b80031100080d170503800700300700b002c03038200903c0c058481d81d41c625662002004100e80c04002010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 283801843 1250 283800593 283800599
    0x41203030f021b07050102010e01140402090405030408121b192009040b0702150403080f1e091e07030f0b06040905030d0b10080f13050c0604031b05011701030b040c 72
    0x40d40c459040c8088540010514503140c1000642100c80c009c007560b1150341800c000c2100b1080788400d581d0071560541d48250b482d178460800c2401d5015a801c8011940540080c807440b00003480c1c050042e60340f007400c00d03818080c00303000010307950079100906005c0d000340c03025a1004075960001104014054a00c6110045440000599090012902224440090002e1008bc01da0401140c003007608e558003807500e0390505450141621400600250010b005c0400150800e641c14240300300c14006690700b0421404c0c010089504d070350002500c46240d00108030650424840000c80710100d0381c000b42c00704030480264640c0a41004000c1c0f200ea00b140e1260720300400290300b00001d00d00071305c002c140000d03801d0742d150400c60201d260749001c100b005040343c240042400c4070003001c0d401c0300114246503800d0380145040c50030485103c0b00d161b031280011500105201600c090a00504030440c281b1540c5500c410040d40c00d19009486401190741c441d0041c8000f44996000d942c01500803440e00e88a266 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 283803093 1250 283801843 283801867
    0xc050c01020d0e1006050310110f192705040e01020405120a140309061602120f0703140303090c011d0402032508040302030d0902120708060106090605041203030f02 72
    0x1202c1e03034940641c103a56104800f01c0c20800c0c00b441501503644242404201d04d440000ba5440c0240110b00c0c01081d035440344086c5014408080b120000400c03c0c1c40c035100c103c0ca6010740c0e80038002203452030214409105000c5406407100000000c43c43c1c008189032202d04101c1844020300100360038400030f41d070070400802e00e0b0b960102c080800b000b1030070007090303c01c1251070144c0030610307802002d4030241d0080c000c018070703580c0340c02c261150f000800a41c030500c1611030000034800044003121a0044c00340d110302580b5650041075a10a40e80502d0320521240c031540b071810307601c1c4000c80c4c1c40748594000d00b0030041303158824900010340e0500c8007114500e40c0e81c2980040d040742d0094a412a0b0b80604411040d240711500840704c084070703040e0a0104861400e070b20060b4a0348540b00083c0d403402c2e40c0742071001c1190f5400210340c1104200350200c1d4915916850b00313540d82c81c028051880460703610007001400901ca60100c80980340f081702103107865552680c055026164443c0c421300c0349502400314040341c030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 283804343 1250 283803093 283803097
    0x603151701020c10060609090203040303021308030c0d051e0c10140709120b190204080a0f03030b09040312020a050903011a09060d031d0a18140708040f03030c050c0102 74
    0x510030800050341c8051180e22030740740540c4064011542810b124041025a130807031620412070350014000b50f41c940d07980c94124020f103d01502c00e500c9650107080071070703052000405085c01950702c0c004c45107030380800720060b00c8034000c4460041c80e1041c0e61403074440044580000c2c0000742d40003070889001d05108107906007560303040b000784640380191300100400c541e800400c81c4001d20228848200c580314a0b2901c41c2001170040c2070000c80070319816099004a0030f5412503001701024070968042501c5840d2060103002e03401c2d07081d0b0010b800c0c0350000318a4a080b5602074059985500d82d880e00b1000d4071000700180d0400000d80c400e002091101e02f420303032000c0c0500071010690303440ca244292445420084061b02c060201e901a100008a0500080d00012110408103030399091020103046000000e44a5801c0e40004c0d41c00e552127000101581030603048614503100c6112400c015607940b000840b2a2102224060300980d143e41001011a01039407000500c1c091034644146459540b828150981e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 283805593 1250 283804343 283804379
    0x103060f171e160509011514090d060204090b030d05190c060606020f060a1107080f04050d1a06060f070f0f0206130609140a0b13091506111501060315 66
    0x760488a50f0010043c0e0b0b1004403400341004682c8204154100181c14101050840044082c40b148540440786104640305a0740315410080c040842e10541e03141c0b102c007a401910409803603506003841c00b44903140c0400d03260444552603a81505100d950307240b81c240310700134081d00030511004200540c0460013602880300a000d4a0b0000c2c05003992441409151400080252261a240c4404030252510107421201c046410440558503045204440c8040d403040d644410380c01101c100c00c0e0340421581c12050f1542d50b0240c421142d81e41e998405000c605d2064503140388480741d08100e0480002d80d5403080d0320640303000320600030b10b00f1b106a0103e04264002c02c4c0c030301c94566480404202096005c40d40c540030348801c010703040d00c0182000105c1c1c800d81c5a805810117681c2c1c0825401034003441c0f244000c008000d2524248811610303030403c4071f00134406001d908002001201950480d003000604500c41c1c3c4e00c0e004a01c50507a00e080421401040c01c10710010004507500d00010b9074840c039400007a52 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 283806843 1250 283805593 283805653
    0xe030706060e0a06052101060f1e080601050d020103050406021b010203150a0308030a1d0102070305070201300e0109210813030801061d061801020106050103060f17 72
    0x16007402c00b80241c0082c40000d1461004500b4418244407580303c0011810030003032a002410407070910041a6809445141c001e0b031010724042c580005d80034840c400e4200010180c0c2010208aa182c52495880d14800d025440e00005200803e20055100b40c1c0040d6200340039841c01818800009050905468082c1a280c681c0e034005c4180441140c0310780340006110000c0b03540c0d0150528560f600822400024000e824280d07603010183c3c0319000f42c522003041015801c00865407103070a0720b800307403103a0401c41041e800200c0c41658011a4103c0515640e8000c00c07000050403001031044600014000901e90007005d035484036446400240c42a0b806109a4803c101017448000c008000910900c0e0007440141301e04228944207010036084901c660540d0304a10b08403ca00c442d461a0282521241c011207070010710005804017052202c03180183c400e2426802800340310b82e6170740110180c4005005042443c1207410040010b140b94144910100d0810400e0b00c2d4099031404048401444601c58401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 283808093 1250 283806843 283806851
    0x6090f060e1201330f0306051312020f07090c210b0a03080c060709060503070522030f140d0210020d0b220b010309120305330102010f0605060f0d0e030706 68
    0x4c040e00380c0d2000100e0440658401000c69450a8040c0343c03030b4461448003a1000e03aa650205000f84402010303141c0799500b080003c28441c2052100035911007034155512914044c1321808607000c641400365944030803540d940c000c14194a2a16905221024420144560355500300c41680380c6603406500e00541c050712005032540c1400e044207080071001070088003000040351052000390741180c02c0d41e801c5002460060b0b12442039a828119002107603011101d90383c00448000104120585081c500d94401c8150440c86504400c490740d035582d130080e003c40541c01410911080312a154054607840d480c94001041e0707441440e01040d01070860f20011449030484030380194501c42c075409135110141088c80d0800c40028180c442e420240000310380b90003059154030110741c11405c10740582100903040000d03214000c0004c211003007202040c00e1200e000d542400180d090380040da02c1018110341016195900d03007043c554250401e80d10034100c407000303269500c41038044010100090040d080c802c0074002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 283809343 1250 283808093 283808141
    0x30f051303120501120b1008010f090203010c020a2105091003090311060402060904020c010b040c08100b0403080711030a05010e0607030b2202030a0b06030406090c06090f060e1201 79
    0x240380b00030305061040850b003484010060144400b034480c086640007100c41495444412a41c44d04142c207030301c000d0441d07080c5140140741c540d90398031049909200701c0c001c002001c8454002d0340c42c0c00c1021009400c501c03035043d4001c0c01c03400480d1a50460700091600c2d1745800ea03500002442850307460705000009580d078034907004164101102000b852b404900410b400c0c1781c25070001d40310b03104a108050095401060a01003488250003d0880d03d60061060010505580c401090040f08840c85502403406e030701d002a05050030412036003980c1d00402a0b40c5407000a850b00885e0850340100260144601c1c6080004524203128802e000b040c2070300544843d0402d514020107a03801108510f1261400044031000214402c501008021801c0005071310b1760b4903800444000c120007280f039a003000c4000100400c02070300754000401b8900c42c1d1036454200b5141c1c501140d800303c035401065084096248140102e90080215424114004048010904000b65920300f9904c8003641003641c17001c191200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 283810593 1250 283809343 283809347
    0x2070f15090605030c071104020c030d1e1a1e030f0706021b0d0b090c0409080d0507050306060a1b0c140102060603030c0a032003030702060a231501030f051303 70
    0x481e000306050720340799007036040520417503c45214041006040011520310030032142c6468054824132045202500d131a01142051100542101c8400300d5002c080c01440720745001a6120f56400c101440d02c5070400c03c3e00300300a01508a150100da920910000803480c24141d07410000c0714000e07441100501001407803c60003030710740303c260728040c510150b1061520700692694425805031940200101c1d11940b1680d0f4602d0612140d04030081c2c109083c00c5842040c0010000201000486030702e041146956086080364103002c1920203551201d02006954420380c481c95900702031900040310300108a42c2941c4402d8418000c2e4403000c1d00e8031280024112940c0c0500c0f680f58426000e501540ca481400c03401d140e102c045a030f20040600988080d11910303082510869091040d10600701c0fa9a030900e0b50011b0340d034400c129060007005042c02407046032107000e0488060880440040c80c031140e15400100d81070206590380303641c101955a03000040765002801141c0c0101c4000e000101d03000050300300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 283811843 1250 283810593 283810607
    0x10290403080d1b080f0711060109140108070e04080a0203090405040b090c0d0302030a031e0c080f01060c210c02101e030e060a150b0d06050109080a2102070f15 70
    0x38103c0c00e5003140d101c440682e8019240551020501c1d1144000340d1300e00c01309071040401101140340724400c1c500080344141e42d643c0881c0b4034140c05201111181e07a1101e031240d8643c5039025030422080c10101041c00601d500300644100c9150f4010750307040484100c0404c086440407942039918490701c105001d040700051046140380076098469520301c41a64a001e9074038801c00749081c0070035035254600c030000c41c0c0c40402042d1a001c01841407103007500c101c6c001804d10b40255100c659010500d00006010750046500240035640101c4152000c120310f80d0148191b4244640201841500301c0b5000040e6100404030708080e0807600c840d002910407005010b607145e890b6014a00b032604c3c01c007220170084000524a030b0300100d20800410070048606041c00381851a034001820340001080e081305c003c059400200a60b4001c0e610714611650b113403496680c800c0313010002303084040d1038407102201911090f010005481c1c035004699031540d54070950b51400d0020382c441002441c01406100728a0341c00b883c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 283812949 1106 283811843 283811861
    0x11160b0601090e01180b06130b0306010302040b030a0c020d020a050a061a06030c09150412060c03060b0a0507020301050604091e152901030510290403080d 68
    0x40c0501030100c0004042086c241028901380d821301e1015913010090020042c12a17928010f228084c6034401b034503c604064080102240b120180740080d802071014040005d91604a04070003420514003516000464100282101c04078000081500f01150030071300000e9441b00c1070090188032f6401c0c4403260f070416400b00402501181c40000b401310048151a080301d1030040c6000c080380b038403d41c000e04c82003990584100d00030540b0360b40304101c42d00a41c01e000131000d85440e10014140c020080340000184002844400c40c1400e004940e08003906542c14002c1102c0c2d17595140100402d2007030340f201041c04610003414850207040301c40f07040c90807480811502040d0b0303c036010030440c0030301d41340c040810f00d10291010b54401d2180500c60888526900c0c1014140003d811111880851701010b0800014103a2408103449000780000c0d44184455036541e06461000c00c04c2d148285 = true := by decide +kernel

theorem cover : BRFrame.Cov 283633093 283812949 := by
  have h0 := BRFrame.cov_init 283633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 283633093 ≤ n) (h2 : n < 283812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
