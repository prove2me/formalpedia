-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:56:18.655509+00:00
-- url     : https://prove2.me/submissions/3af4e7c6-c5f3-46cc-976d-f453b0fed147

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 185971223 ≤ n < 186151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 185972473 1250 185971223 185971241
    0x22404030308010f06050a0c030f140f0c071403030406030c0203070807081804020c030d0203181212090109030e01122a090f120b1b0301090e1507020601090e10 70
    0x103a142001441403800b1300000102501302c2d03080190074900b40110003081070704c11001c000d04100c0e0f960211000300340141000d0742c40c601461283c0751a102c4008010030743c3e4000807152101482010000a4070070078506806140900103005140780604106040d070142ca030041c0e2550451108100c0d603004101c0e0344015000313480c4105a0f80c6d580d004081c0d03040d800e032002202c189101c0c0d84104207070f00c01400d00008480e015042140c3c05038a9544480580f8181404d01032104600e006400080f032a0703441c0803000f4080c07906030071301001190b2600003030b082c205d03600e001009000c12400c01c243c3c08150f004807948038034601600008503840480100d40c484807e03610718450701d0310360030550760205190848c580f400604642142e030600c0318900b0000e044c14803104a00945400148800304841320a14400b00c8080020968015600e5a4a5145100624038407002c58020b0080085151081380c23074002c2c0381d010750107545c01031129900300760001004001e444c1190416101d02181c1003400c08041c0500044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 185973723 1250 185972473 185972477
    0x6060a060c080a0c05100501060f0f09060e1201090807030807050f0f090303130e0108070608090705090c190f09081504080c0f0106140108010812030121021903020f060403050a0224040303 82
    0x7c0d515018002e01007035a14607088090041180714009074503441a1038000301c40306441c203214495140404141804620a485201da5090174640420f02407030400904540d4031a40e9000b40940d00c00d0b00454a1780112444000074980403c145e0303041c08806000340201d207400409881c9401412412240e003a8010351003072000c0902540100031a000520104009002c1c90402d02c05525140700380c2d0352124075234000c1c03600c60303603c910100d614041c203607055500103010011019591920f000c8080d180346d104010040010b1181d0380085140d00c03012450441c104041078114030a51655a120399a94000c3c6030a054540700300071074003c44100c2402500001c080720802c0550146011000408540c0143c00114551748912603008110b551001243c0c11114001000014a40244040d0448801010000e54411000c280c480c409251402c20781d02284d108031500c18444440b103051103400e006070710010745650001071101026041c010f14680180940ca0768101d1109803010300700280307410582003540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 185974973 1250 185973723 185973731
    0x302010201060501031406090c0408030c0309040501121e081309020403060b0d0b04030f12020307080a1a010e040506040b092805010e0106030e0f030c030c06060a060c080a0c0510 78
    0x155602072141e40c0140c00207207000e0016551107410200721213806402c1500039800000000c83c6283d000058801401280c41035a40d1145107011495076034104008030b034490392510b000040ca200f080c492152020b64444403941050942d5644894004003003c41503807891800c01c41d02c80654540300c0b1500260040c4100181c455055040c80411102c84001e0f060145080d40c0c20900071036540906280e1080e858902404101f401d030708100c41c800c0a83c180501050f0022041c01030050300104240c0c07150080d42d070100f0035207808080d81c12119480700c45440c08201040500405804d00e80c02c400d40c08107001d080401c07100e0b40c031008502c25800403106680b500405098882c0c2d01c45580c890403c198000003014051035040103682c2c0d002200601c11002416912111411039100910102d001c00f0042010b481e100d00300386d620701d41c50f58043c40300d040782c41c010341c03000491a242c180141003e4a81e96680c1d9410000b499071469600c0e0f20181007503083c070200303602001c00544100030400000e107480720045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 185976223 1250 185974973 185974979
    0x2090607050a0b0c072a05030f07091a0303070f0516030b07110a030801051002011506020d080a0519050a0b040e0304080d03052e0b040306020405120a050c1011070305030a0801080303040510090611070c 88
    0x4411681d0cd1000c03c8003a005080d0701c40180c4d42c0c0001070b12202a000b964900840b802403500300d2030080c4c0306000080041031650004140116442c82d184211069104c2840d4030030800021526030507182c1004011070560401030043d4107245922110060345400002000140310140c114000740640c410b100590181d54500c48241c1d01540e89600f180314503c06102a003044520b2107810448601e03901c0182e640c410006210303048540160512000c0503008000301841d60f02c416031a0b0f801406503260610400203001e80300b0713200e441054490000036580e95108141c500305020416041d9484c1f4540b00c0300014085041086c0340002e00086102d1800148d9440c80d200c18040c0380f80b00c00c08018029040900080013281e004201c2014a03802160903041c0f6810150054079104402185400b0702e02c0b5000010040040000042c40501b000b51118803c1e0b07030303036000005d94902c021140140f03240c210b40305400102c1d416402001c1883c0c400c5a020520b550b214224603150340001000f5950064099020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 185977473 1250 185976223 185976239
    0x30a02150a0e060c0303010909020103090f0506010312050c0601180e030a0e040b0d0201021f060b04060c0203010b0a0815040302100908120a06050a140402090607050a0b0c072a05030f07 81
    0x3203a40030a880f2542010751140159440f03000c140b2070542000e4903008003d046a1190303000e1650141d00c0710300c0104c0454a03003001c07603851200340821907038040d00500c010701d103900a100b51181845094000c29070342e800c3c42c6164041c00700302d00000f40c00c943c0390352110881c0441407014221440f8159610000804158108010395560000c114000d40f9185c00d0100540d0f40800c0030500c05141e91000044a10384003404001480c050380b100d6494400490b011802a50011310400d555000302d00a001d120a450100b04041c860740c4140c0d8140c0d40512070070042491b48035190b0350f0250107401035034000b074079040e280c809840905104840003030300010b0341100c25180412403500600c62000400c541410080490f003101100d01a01910f891440444040c1360358617011101044000742605460f40c203203103000c0b40c0d82d01d0038000880e4000000c800184503450114161034003550401d40c1c1801c0251134100c1d810880d83c030f8030300680004844000100c0e56880c100104081c2d00e00f490300810b402c031310b000c0e20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 185978723 1250 185977473 185977487
    0x10020a0b101404020913111806030f1306020c120702130c050a1d040f23060934080702120301080a02040b0a0905040f020a051207060806030a02150a 65
    0x16290100c1c1e4040d030140000540c0e2081511415025100142d854007040000386800c0c0b0400740703810085003010046982d03004403134054041002c2000b1201c2001403c0010403140740408c591704600064000c000400c01c1c96007107100c0101c9401010300524000c4086091750070300080e90f00c8004c031114001501d41c118140700c1c00181c81107001220400c5860041d05000341507200701c002f40300401180c02c1c6802003503400001404540440180104030644a0311400340142c030242c100d6140750340f07072940e00d8018403203400016403003054020a22010707a83c1d0b0800e005e40800d035261591800b4903030803101c0e1201c1c0c18a090305c91807070034143d221000310b460700110080c901200640c516140310418001000540400100070955a9040f100881d1240807400401c081e00c145a003d50641c60501e810702c014460304158926a0074000c0d9244000c1f183c0b00d1050001040740c4944030306480d0f01940341005024860007000c5d40040004040d599104a1500098001d4030310b10b403401022400054429880d54020030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 185979973 1250 185978723 185978731
    0x70f0b0903070b06060a020717100b0102150103030315030b090a050c01030605010e060d1404060b011d0d0f140d0302130509010b03040b0c09131e020c07061d10020a0b 73
    0x350b2400303040f650b07403c0c1d1528014141601a84011840c0c10303440c1d000380640d80181c2682c1c2504109005007100007039462054100542c152407400c54070750304039440800c81c078042580b1808010481c0e481d550b03048000300541d02600380078000d060750100028006280c036602804142000f4200b8420a040207805d00c4084500d45041c035280200c1080540d800c001d4003004110112002501c50090f0754082020385415410310340c44a404004100801c1015400805c10000c00c1c0e9408245800301040c1d0b660640410151540c01645038007004001950040c2700561240300e1400e00e144022201c51007403034881142c43c0764000c02c1c0c003c41d00a80201c40c10f20220b00510342180c6e480701551410b51018100c0c80013620103010400e09800103141d24081c5011604c002e10054420f9421001004800d00200a4003415408407201300348a134684103c80d001b582c3d840b0300810060591a85054403e445808503941c6001220258000a00041c1d950500d0140d6800080e009070000840714030700005030307640c014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 185981223 1250 185979973 185979991
    0x308030f0601090f0f0b030c0714030406080c03060a170c0319050c06030c0313110907030f050603010603020a12020a09020f0304021c0b0f040f02040507050d0e1207060c090308070f0b 80
    0x40c40401c050717611030340100211120410132a640381c0300c1140d078500ca4428480040c0480b1420450484031101c000001d1084801980d1550001c1d281c1040b04126031005540560340011000002d002240840d030031400178040c038100302d42030b141088001c24189100074900000c1c200e601410300d4244a0288005000c116049540510794030b40032980c0201c40c00013a0400d5560311031008840204036072503440590003c6d00078580303030721860700000c010081d01004000c030700c28a003040040343c41d9040500034242a80c2c0e00404207002d103414040d1080802d1a2440140d074000701c400000140b42e000d6200a00220008056940d0b9a00d018014030881d025821521140348140504a80114812a0711650050002e840807004c03a242d5040c00c400030600104080c4d402480c2c64148290a40c10400070f140e840c2c00c0300313824880c804010884070f46500d10f50204124441c82041a01c001071102d90000001c1c60450070402d0486440e520b0760351194110032801c507210259000840144041254565407105244d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 185982473 1250 185981223 185981249
    0x201060b030f13081204060b011b06020a050d29030601061b06020c03190216050306040602090402040308070605070e120a03030b0f060a0c0b01050a031e03090308030f060109 76
    0x240044a00c0700920418420000300301003a07040440d5006584100c0d0400d91040e29010010f07050400f02c24191012900d00d403521049003ca5402910383c1390005500090911ba80401525400040c3d842011007504001080056013180381481c4580d844800340540d42111a030030146440c0041c0c0224004148203078000300040008070342c0a1249844640c0341100c0314100d440914050000c3d01500008450901001c0340f000e007240600c080f00b0318451001d0f42101c240d00044c0d81a41001200c600456070990011000900400ca00303400800c880c02c2c024000600d05645c1f40c4411410303400c0202d045035802d46035818403001c1540a100380183d50003c40e500e442443c0d0309089950358405082000341810380f203480900550b91103e44e10402c43c400074013000d43d50030701c001000b03114441060084030b03503029010010a086c1080d07494031054941c08034500d40e00e40c0d01443c0e51070b5100e40303401040b000c04c101e007031000c400642540c01035402451441072a44031414200009440c61401c4c2d000b1204c00714030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 185983723 1250 185982473 185982479
    0xd020c090f0c0a03090213020a0806030c01030203091009050c0904030504032607020405040516140a1a03070810120c15023705010e0a0210170403051c050a0f0c020106 73
    0x71242260396009050800148807a01c502c081212104c0b4141100c492074400b027542e130941078120030380f030b0320a074022800d454901c03503c28015000c9000a89903000c0903485040d000c42d03e10003540c00101258007580854030184013620000e0140201110114005100030608104000d0410700030710341003154120341114805100c84e010940d020746000648a5501c510204d0140001448030712040710300c002c42204155198900b087ea6264030700d600c940201e0803404001070f03208100c60300076118040d400805185403a0800110b0b80706802030111030f41e580d0040e0000542c1820010b8a100c1c2c01d200714003004c1c001d4648841c1d01018060490f00c4029504101c0207444c8080c0165507048002036141c0c681c04000c90301900340328032440a88001000c542c6000706001c41701c80001174102d01d09208840851416441180c111f0b011440030b07803484201c0010710042800240280b0103071001044107861940081090320007002030342e5068407003000c4e00340c0d00c180220048401e8005e288003440180028842c10389 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 185984973 1250 185983723 185983741
    0x5010305060a0507110a030905010905010507150b0a0e090a0b0c0316140417060411060c060a0209040b030604060605010207060203070503090d030306080601030b060405060a2103110d020c090f 84
    0x200040558181d00c0c0d80c3c038001030b412802000c1d4011052811000c0b2010103c95260240c05d6070140d014650116100c54400101d940c82074080328035603984414100045020300803907101030423100c000543e00006060340130a500b00c8c01c81500b482005210001c1c00c0072851400e055810460181907001c0b04082001000042c02c07649080000e03110042c948100f4009000030f20083c503004982200000c42d88074608800c0c45200000c43d0307405140103010500d40e450340c40f000c014981c461001c01c40d809411540000f4054142a03000c2c0445241c003600200b5140041c01c0004e00f0080c044038100c030481da40344400d000d95641081014003030031150008502e4010503880d516a81d014000b040381c030500c0c91250810070180300741c01c400010b103481c0341210b0103540c4038541003010b008121000742c0500c0c80c02000484c80e00c0c02c04030040480709030b500300c000c2403038034800e00d25641e8613810400c1c0c0074011401807071481c4420420104a14000a0b405024000d018401304030002070094801d900703480804042c050901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 185986223 1250 185984973 185984983
    0x903020f0f03010b12101508190f0b01080102070506010503060c070b040c090908180604060f05071703100501080a0605100c0c09140414010905100f090501020a1106090105010305 78
    0x1030040312440c621a04040019000d80b556000e0130b03412a00001110b081080c002440328030586621106114121201450a034009400c0c450a03181e5803202d0031004007951140c080881840c0a030303c0154003044c03a501e41d42c011400a138861003080e940041c00006012060011902409045000e05158242312695070700f80d002d405000f400010ba640080350401205910040060074440400d2005582e1800c0c5225150000c0c200300e5800d078000c810b50300007481d0541c215001d0b0741c215155145942d03017602044949420004c001c4401c0150480c250301704494080207544210645040c00c1849410003000409445000e015840b5241c20003a0511003030395001841c100c00390107031070119440c516904100c244041c803680041e1140e071038800000311807580b01c410288103500440c090070300465490812070884801d504043c9c034540005a00c1c01641443e0f070017513802a2042000469002c2c46501c6007400ca901444089012540d80c80040824074070070300003268400c5841f0020026503140d42c580316210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 185987473 1250 185986223 185986249
    0x230102071a0903190c0f12020109090b0d0204060308030610090b03010509091903020114060303070507060e04060f0b0a080115020a0602130905090c011821050f0307080415090302 78
    0x610310100b400c0019403030820118540002000a08001074074600707001460310440d00844c4181c4082140200b003051486503100300b140e9060303551200840c600324a0100400702400140d50125142850b6809170391207006007000385d030180d200300341c3e0703030900a00300301440d0341da2125042031045140b010800c020020040c0d0341115000e0304c010b25144d50f244021402c14411140c04800d52181c0e03000c240905074154004680304030350300410000d80e140c0408055403806408030040c526882a40705000c4180f141d001001081e43c083d00214025859a03840001031800703400c04c1c0381c6050082280c8400503031000c11a070051400d0711403801c40040702e400080d11043d5540000c2e140e1034002820721041c0d00c03851080390060a078190b0030400303410a0320010303884529141d44280003c4148c41d802000501c1f10310300d4400c44201024007144880741426a00b006074400c6010749882c0210744071079102c91814001805400e2040750f01d180d031541001c0c444406606500e0000040000e4000d060005890782c00b000591703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 185988723 1250 185987473 185987519
    0x40f050a0b180705060f0a0c0b090f0106050409120f0203090303070605090d05120703050c0415030c030f05091902150313050d0311160222020a020606031209010503190623010207 78
    0xa103424500054800e00300c01440205003554131010844988004100014003003488400de0102039900c20070081600e0348448090080c400da04c4022203100e0040801d0713082283d150050741d0038801e884000908540003070f402034401685807403c109401c5014001120744001508106052400302c0e070030a10300c0c180c001c0c510414155a00c3c04641c1b00380400050f43c00900707105c05c030700590a403017030001400350038000d580e48046800c01c4468004e083d064041c5a00c140041d10082c05403114a0600301d002d030b00302900903a0000c1400e4034104044d1a1080190311501ea8010010040c0f8001d2400d00c1c500b140c1c03102172a041608c1c1c5541c10054107510400c80780740e100e42e4041e0001110440c00010340400f40501d59140032051007200781e445100b240c0240447c40c00e070390203880165880c0800d05841d604c3c1100301c4000d00d1810441c0b000741e5130164000d96040a411a001ca0043c083c5643d002e08544c000d0f00006803003402c21480b400103404003074500380c0192080c4060540c06103400354a40c020700c0a0000c0c504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 185989973 1250 185988723 185988727
    0x30503071404050301090602070515010317090607020301060e100801200c0c030f0c010323040209070c060e060604060602150105100c2003070501021b0405040f050a0b180705060f 78
    0xa00220300703034240d401814008000304503480c0c40b85410002540040c408a81c00c5c014140285003894100091504881d000341a91030000001401440683c0c00045580d502000902070032000d80c03001d20488000d070100110401e107070301700440c001c0c10780d1405610403032260b03040052039a02d440c44401112000312000e4201034031228103505160030f1100d00280b450701441141d03801c881203c4000384181081000782c9003003040c40f040c41011004003d41c46106541e01c903451000c079005017084810319501900d24a40302902d042c0345d40d03030001501c03180d1600d203515a11201c1484558a8079108820003001580010140d038803a4144004120740c0501c601440b031080d00b04000c0c0500e01940203584010780c0a018078103854030240440e030130f1440c0c03a10002d000e8030030040082182d50001035005071601b540c0180c8a03071102c0d10403c08c0080c1400800407903c101040c03c84800040e0108031020200740300d511854014a0700542d40c130503208820b000500c140d80100401c002e0741e1906001c03509101510b440103a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 185991223 1250 185989973 185989997
    0x60105060309032712280308010b03040303110403030503060411040e040b04150c0306091d1902060415020d080a0c0c03080912071b0501050405010e2106150f090403050307 75
    0x2880b5010000a680050ba441c21405881c07502248100482020080c1b5001d1207072842070700040d012900c040207000c54101c600500c1215a010003031980140702c1d00c1d010071551491803181348142c1003948100c010800210610085180c04d01803400c02c0c0740d61100040c203252070920050700428000c0c2019010807074820201c1d0a20181c0e48418200152950f0240b181d8002c0d410014001c0c0800c0c414010035a240c1510500c0300c00110508480300d44e5000c00402c26031050400c100d000e40440c03a0103da20140401000840c43c40c0c88141c0002007581d034010b00645500d181c00034020400c0202096012480c1280c80d407601c54001c0b0840e165540c1518220002d6070703070300d80d50516055400340b151030400d0020070840d081041e05503189858030001440f649500d552400151124021805010b020480a103116881400c1c10b2610000520f210a400c00c1000c0130303e40f100303042050035170b5444d4600d418101388410070704200c45001050703441600c0d080c110b403802ea14010014000501303c2d0040194145000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 185992473 1250 185991223 185991277
    0x30b060306060a2007270e06190207061b120b1c0501020702091302100203040e070c05010b0918070f0b1812030d0c1209050709050910050c090306010506030903 70
    0x100c4e48261044045034842911499034001c1201001c404440241c2c801040d022103005601400d0b4058030080300608944c2c4901088418031444241c50707141644e82400080040351041c01048110501c1800c140e0a020616800034100303002040e008003024102400b000e402e89900d8200a00155909030394400551203240840c06032003041006503019119000341b00d945400441400030342da2003180c0d00c488410308020103036100c0c001c6100d14240d0b02c040c14001480d06010340400b054a91140000240028842e00011a460700c01e40d00031000400c80542500d0400041086001401d00c0303030045040c55282401034400b0b4819122240c03c01618003a1440f000d4640110316440091030343d05070b031348401c40501c0c03010003011403550031400100d0820703e07410710402a200b0307010404d402c070001d003c05505242c01d40001d80000303085001503104e608401e210214861103214041c89041070155550303003c0004040c03800c101030700040d00c51a401c0043c002d801e00000300f07d42c0c68040580c04c0c450a001002c00d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 185993723 1250 185992473 185992517
    0x70c0501030b183408040209060a08030c010b1c0209061c05060702100501060c0822050307140906060a08150a050916111c050c0c03070602030703030b060306060a 71
    0x50041c54035168040c030054440c10701d44585604400c4e0210001444290b0512080c002d9a105400c0800c04440114015040a03003080c1e5104001a03e1b142008e582d070320740a8074560100b803004540340d669201110340f0389810080d4030b08100752640c1000e44072600350000b601040e13001d08468443e40c80d12404803100702c018803495007001d030071000351000d51801032800b0f5140c240c1c40320414800d130f10f4503002240c801d0140c8007220050350003c0c05181032a4504080883c90301229001c80b0341c20101d11070000e841da60400c001006015020282850011041c00b405403120001c0c1040340b107294140003139941950721644140d032007a2010785a044800c8284082040160310f60801e54010100c00c04000e296110a00041803900f05a0b940204211400c44815114104000e1192442c1891005d0184061054020780248145c403001d42d9540580701002074682003496000c840941c2020542c0700615400d48983d0301d01700d8095034481d140d4981003001a80a2249080320b0b0140b11072030195510900c1e6a602c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 185994973 1250 185993723 185993749
    0x51b01032c012d0b06030114010e010215090a0605010f06140a050708030103060207110d080a0c03090803040303110d0309260d05040606080d02010219030b06130303091505070c0501030b 81
    0xc048990310b0588943c600c0c240d0808550208a503080c590552454140346040324101d0310040e00200003c070441004551420481c00c070141184644602014004102914540205001ea00900640c0603e190900941c0c005a21043c002051203004004240d00020031115000800114550f1031003040019501401071280143c48180e0110000c000c0028503401021254011038003420000c80040421182000c8000010081c1c0f03001e10181c0c038480e00440588403003a00c81c0c20140c900700c0c1c03640760903459600540e0040d00005c04a5040304007400b070a01400c071140c241c81c034090000b12100c0e211040d008030700140001500c0c03030b030901500100c5010416111750041001061007a41814200308003e030210b40910300c20350080c03030708a00d0082d00510071148901d141d000a50181028081c040d80180f0b46a103205030090700410221005500ca61001d001030352294580c7d03001c4030f0400c400041e00341040c480050922008200c0c80e004900c40c401c445044031800d10b0040384078259940860001d0707507501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 185996223 1250 185994973 185995001
    0xd1101020c12071b06050a09120201231b031210030525081c0905060703090302102d0e060909241003060305060f0f0711030f030103051b01032c01 64
    0x31011907001d40c00001020b0302142c039500e030400230b40c4800740499a20811000240468401030703034a135100d180c1540c4900e111380c011b07928030f08129500081181015040510030320580000074126083c80c151320201c1c3d0845079000e03048083c10b04595499540300803059802141b00080640820201461034483c006028142e043d034003d070031790b814402c0001c0d00e904000c0000c92806403012407182040400c0c0e600542c1c05540c0c83c0181855074007888007000d4034001520400039490132003000b603d004400080103014070401641070000306017004001c008900b482074860748041240000c242e8556614036040100d040d8184100d040050314014000d440024681d04242d00310152024190143e0085003124021340035643e103943c0d103802c105512042141c00da4540b044400124180b54071030504090008030003c11680b80500c10407c0620640003607004507459480014600120000318500300b03032003a003c0c00c3c14010b02c0401601d000c0384074040107510440445403692101101003d4110440c061404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 185997473 1250 185996223 185996273
    0xd0f27020319080a1211040501110313030c0311040b01050f03090703021201020409060b3a02070627121d06040e0609010f05031c050d0e0d1101020c1207 67
    0x1e03d801c5109070490304008011400400a02610321074502a610591280003c06417402d400e15005503030301c14110150000d1844180000c000f03400c006007a40c40518001c0000c40d200c1e514620300002609600d4140034043c9040c5140500c05903006415502180b10003140d064580e61410741076403400e86268000703940701c0168800c02d64000d0040d4014000d8a40c3d1207402e010381e9440d04110121842a40040303d150a05c2e100d119040440c424540008950b070303600aa8240880c00442c0011b070b030003030071050301c441c4c8d0ba03900000550000044010083ca4021103c48213500041e210708080380c8d40c09039480103008480442c01102010003100701294440103000c03030344540e114056403590500480d94030b802102104004a00b03422003c0b510403c5a200400420500003088403185950f680e1544010510109102000d040202c9000d19000c0006010041c1144907030741d28018040c00070030711040035591040008000b070400201d0848000c4500032a240e0780d40035640f03014240ea58103005011039160607 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 185998723 1250 185997473 185997523
    0x9060702030d080a06050418141501030602120601180e0a18060501080c010504080a1e140f0c060403080301030b061c05010c0f080106200304090e030d0f270203 70
    0x1001c0f00d81d002e40a452010040c15885c0d0b4140805c881c007102c0b4200c0f44040c2c0d00d11440001e4030a1300500b81d001d50081c00e5132018111401c4030390340350f4801e030002c54403c1c1e0040307447c4100890358900291b000c01c0900e031407002001e40744803c1510002c2801940301e40101c43c800280300d441c40e600040c0c0d40c401e0034142281c1040c21820000e00508c028001c418842c01880801e82180d03110300c060b5800e40750740c1c0c0003405040e040d0b507845007040450400e03101c0380e45c9840c0394020040388924141d00d92048085001d0445048111129414404403901d114070402e400d00092000c1080e130b10035641500e40c0f0020481560321128009035480c8110b800d00143c1c1c2101082c440104403044d0441c10001c82c01d0780b45c0b00d40120a007503068680b000240130b01e000042080a1103900d05084500f04080100d800060741c0c541502c0c1c042990580e94215070200042e403000816440d0550f25201e201e505907403001c010802520801481049900c00240000c5240c1d00c1c0400c210940d82c05022007001d91000000743c1d891071007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 185999973 1250 185998723 185998727
    0x16030e061602030f030408030d020c07030b09061005040606050706020d06030b011d01050102030a121a090108031803010605010206070c11030a060b011205160c03050708040b1c0e1209060702030d 85
    0x7a03880802ca0090042800340c00d03980380004203035810b5440b01000b5609080ba410380c2c04c80250010000a06144600382e4004046110450254010a0740102030281c0e40b80192501a2056144c0d2100c0d014900d0110100000d6900a00b907514142e405840942c4d111210262040078011581024001000030000002c3d0590000145400280034881c410216039a0300300580c0c49008006521010444045c1100c460b1000d560124444003040048610700040c90004070b06604026040b02805610014604800600039080d00340e00c0a030483c024400c0c1420000001d49510b005040807042c804480c1581c0c0c01c00a50407908410b0103000380440d4091209400c00001130702450300b03184c2c0415540340048010141a01aa61041621003480d4000c0c0d40d201c03508450041220005508001050244000044012008100608001c404262500071900f0341218600038540c8494040c0e1807c102d02201807400318460000d40601400151070f05a020082592840751140084d8580141c1b2151003800d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 186001223 1250 185999973 186000007
    0xf0d0b2e08070810090b0c070807061104080115081b060f0a0305040b1f0b1809040b0f100312030c05120a060e090d080411010c05060c0909071416030e06 67
    0x5910907088030440b200c500c0601c412034651440103814401c07040006803407c4055002420824440d041180c900103007922020200d403140d1460458141c0c00082c200f0810400b4081c50440d6600414130044840ca07001030356a40e00c0032031307038243d41004641352000c4082c2d039540261078080d203102004981d035a200b17040003401840b0840e81220440b80c0030006c981c41c03040c8038007007840380710f480144040c41038100072208600b9045010a204110f1141c008072415443c4d80c000703a4000e5108003400840703424036008005400900070300358401e503c1030300000c10200c0d41ca002e4142030180c85090008441030101c07030880d164442c8040d41c8802060a005005100c1d95a90045c0b085810000c40200d0648410240541f05c0018841c0500020042030105000c100c0c170103e002044201414034090700c03403096881ca0709240d02140c2c1542501000b0030b58207a1400c00008003507100d6000d180c180c0c040d540c03000340c01450380101610798101ca40e05071800c400309400f60044400301b900081c400d540300c40403444a50685 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 186002473 1250 186001223 186001229
    0x30d05270102120c0c0a15023108030307020a030e0604030204020415030f020f04030809040617030c0606010206010e010b03040311060a021c020a05090d110414060f0d0b2e0807 77
    0x401011000902844e05040540700c0b0580d40a0140032203203101e841d48102501c070701c0c18003000c5590802c2000081e42c2c0080140700030036000b80b00e444110301c40380300902103540580d004800e150403c10800690982c04a9000c03082941030416800346c0b201900450074500850300020b4106100040200d4041c240c003002d109040400d6a0134469a540070041030164001c10740400c1000c4010700081c000910710401030112140c0140000540554502180d400120483e042c208640c00015503000084010300841d80d0000b0280000c00055241c80120851480f05216150314220048046410140706100c031618801d0b9407000ca40c1e241c2040d4883c00001e51001c26564581c560105021035460850300a50302c070b696040d10703440d084c103c0c203009010b142c00005008841e802a0000380180694035442200c6500c007030006154024030b885400d01c00f01031141040a4800c0c0d104e40c95260001c2d032004203060344120300701404180307081214007020f4940c1002c1da0440b041464030300c0106551400254840407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 186003723 1250 186002473 186002497
    0x120c03020418120e130209060c07030c06020d030603170f0d0603140f01060b030f180105010e100e09210705070e0a0621030c020d061805010c030e030d05270102 70
    0x650001d10f90140c03001080000c00c15080344c1410103401910780a580580307840307800039240030f1503c400b148800b030429075160000c580e84000380c84288840c640c100210341c0d0100c91802c04002d80350850310351401a14078411144c0080c0d60004070101244240d4065885400601c070041c41074944074604500400e07413008454405200c1c501c2a1801d0400c14001d010440d51440c0286280d6107130640b0845d09140d00901140400929000e003101c2c411003403107024020b1149501d500e656080c40000108061002d5021042104405061003c128008241510150004109810302e4111620014154007407503502030628002d01000050100301500c0c8030380f1484500c07030204074081c2c441d00c010801d41305002016000c400b11444c083d000a0040c4140d580c16400145840c0e14070300c42e9555802950580c005000704424030f0b21200d0f0401c90240520740c10404e150509000c601c003a5000d03a07035280070351100c010fa4951142c01081742c180700c000102e503c9100070211142c00c5035464000070b010758825144046 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 186004973 1250 186003723 186003743
    0x6021605060105100309030c060506121e01050a020c03030a2c060906090312010303050903030f04230919020d0906020c0312010f061b0c05120c0118030804120c03020418 74
    0x10303602e10074400d1120540c0e07da1a8003149160030f032118001800002c1403603400009800e20416018402c004021100c0d80c5050445070112121440c01e00350341002d440300c139209005103c0c81c01c900350302000f0f590b4082d034034000000c0e4150052580301d5402e03006000f080ca41d001c004050b0b401c40d080c00304401c2d00c01d48821040760610f0711a298241e0b036910a06070700c0c0016410b5130005000003845240181404c400042c00ca90610260047c034000304e50042e4030800001c519280034a640e00c0410502f4440742c401140c034603a01d450001071100e009114521038070900c40d4006040c1d188400e003030703102e01e0078143c10050441d121003541e401c06961398026001a55130598000000850000d09294001501d2596075408582d0304041d0555501d00d04040003242c40c8850960049242c1e01d409840f0b010324038a090007064460b40510002d0800c49c0c0c0040189801c840d052014004201c00004441c200c1d44056036030095030b00c850074a0b03418403000d50402544581040025400c070344e00c1441d044401780c003814100d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 186006223 1250 186004973 186004999
    0x2030c0c0f03030a080a02091908060a05160302070311030c150f0c090f030109020315100905092e0c05030a060e0603060a021e03040b0a05090d0903080706021605060105 74
    0x1085a407110002660b0550003040700501540c443d420864204d000f11502505110308000066851101c0003210070702058800701c10041c4c131400704501038000002c640100b00a08140d8814050048044810300c1850b0b000290b000030184921626111a1001e03410703a925000032a020944501c001461344c0c006064903404502104000c0d880b05008103214010140f4150302c0c0e50a006c9030b00701540c1d0041c0c3c55540c50b00c000d009078905000100408840142d9410f05240000b1030665a2030541c1000882510b444208250000005034009504141058080146000d01091441005480086801942441181424190420041c41c09445010010301201d515032107000c5070720308215401941a803000010961015665005000701051045180000100021500002d6005075800c548044041d010800300e48094440c541d00445004040c0400203282e917401480c1404502002c1c1003418000390b1a07080040b076904440c60481c424aa034462949203041040c0c07140e4007480360038000c2188010790 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 186007473 1250 186006223 186006229
    0x304050105092a01300c11010e0606131d0d091703030f090102040b0f07020a24050d14010803091e06071728090f0e0414071502030c0c 59
    0x4080f48042e020000841c0c101802c0044428800c1c00c1c1480c81000d0340314010445500900c0e081c0b901c52948a20302240910300410700030031381e030b81c50011007590341d1600500c000050808104c854201c82c2c101c41c0c8039503010766640780c1300003441c802c6080d90f03070140c2c1c020f59404074800c0800d040740b0203d221f40740c944079113641e004280e01e0b480d01d001c00d2041d0342c0c00070400918080c402c1d00c58160040940c00c0010300300340d00e500c41c1821542c4400801140b03028045441000c51520383c03480030140001c000c4501b050b410a080c0f034503011100000940a0080201e1001c1840d1110b0b80500103042c4c5207005000c455a44056a13622640100031142c0607a18840a488446150119038000828050000781c0b0b854000c0c1c036000081a0a0941800d211004008076407001d103003101c114007203024003440200d518009003030241c500d0b07480f58041c4400f2010360b1003c0188105500310b00c1e41c0260030091440c400301d4081401402d0034281d400c41d5030820080c15403103481c0c640c000040e183e2072038410304460f2091404010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 186008723 1250 186007473 186007513
    0x904060e04140106031208090c0301020c070e06040e0a0332030105041a0f061c0203040606051f0203030c03130c090203090d02012c070e0901020904060e070801050f030a020402030405010509 83
    0x6d441a00c440b00d9810a01b4403d0b00d8996104107450240d82c4034060000c0068203990005c1901c0c4841d078400d100c1801403000082101d90050750840701017242110483c0c01c9500c400c8940c1000d014440b0401d03a4280500d2006212840d5014504600c03201102d10702010b10700f50030a00899000703501d01040c5803164840d14041c00d40f0340d6070051034409064140010489103901544030041301903088503940f03e500000c2d0000c2c600983c480e11002c50006e04102c140025207401e1070b4920349000701458658846500401100e03042440c10824950b03a50f29611f01c1034252203210030003450301c3c20844000030062116406140940c89000640d1090391082008078241d0702d080c07c49601c070b10800301e046001a80820030981c102000303a13003560042540d50f803103900841800c0342d904005940020f401c115a18103407040c100580769210881c0518103011000505201c4140500d41c014160104c0744503e0380d404010401c043e0398001c106642e24581703850210b01038942918480c84610440700066a40008004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 186009973 1250 186008723 186008729
    0xf010303120203061e0d0605090109062a03020310080a0f050c01030b030601092a120b06180907110307030504030506330f040903030506090708101403030904060e04140106 75
    0x1c0900001c2d0b40b00c0c05c080c401d0b900d4070000150b00504010124000910754003c040c420b240c003200000c1e035902c40382480300945040501310200302003880401104152038000c006c442c07008515005840e5030740e500783c2149000440d080009a1710075040000100050f0f058904c81071840741c0c050703840000a01005400395030441180c5507050b0404001031200040c03e82c0100da4515850081c07c1d05c0d0a5a170001e82c0031000a000301c02d0001e241c10820200d0a0140c0c003a1071501041a10f43e01c2c076088900b4604200c40a0703a101d803e11440501c2c01246032179219203000d04184802070146da81d1481c080c90042e006510a00c0201c0b801e000f0a40018a400c00c43c8200740c200300c05590081c1d43e01e044043c0c030500c00d088580d1070940d101c020940e041400703485a20410420314031a440008507420403100300a4248402030121b001c0181d610b04000c06183d2808200040350045da0740c12540e0362841000030b0850003589400d0360071071726010340001d4042144007418080c90082008031003170350801e910135081c0d61180c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 186011223 1250 186009973 186009979
    0x4051b060913111e0a0f0207060c02060a020c06030106050d0605120312101503050108010b0906030d05130e040b0402010f0f020d210f0b040e0c130b01050c060f01030312020306 77
    0x250315100ba11280c0d04076461401149108504d0291604003110031550b240800d100591408100b44c0da07a00e030448101c10030684603000400110345030440040010352080c1c002401508042503c0c508e9034020489030410a000a00b295125a100e81c4010169042805200085030a10000042030700308252040d40c140030910103145000c0c081801803108660290000c06030685a00000440145044400c002010b455401140f10b5241c0b10ba590b01751001c42024600ca0013425040c40115074002800307140441c82810881e0720342000032006a90750001d5403240103c0c49024041000300840684d015204d240700341c8a1058082c00c0b16003c0f00c502c4100c0c100309015038040c550500300c4900485c045d030f150342d4003c1ea9500c1d06000d0180444d080e101899504000305403a0101c01503240303054050203038800c272041c0040c80c101c142280000d0581074240c550301032160ba03900181c64280d20030001c0b60034104241d41240c1c060704003541250030010f424403064002441c03011000181c03140c24021a40103036001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 186012473 1250 186011223 186011239
    0x12010504091b030b04030905030c0a030201140c12040303020114070c0b060a0801090c090e0f1b0303041a12010902041d0a020d0e061909080301060507020f040504051b0609 75
    0x14000100a904015a0b8800e894081072110b07660104a0b140554800d80b81034a45050034580a895400c07141c100c07900c01d800c145809201600d884220600300e940911301030f202d403000d0920034191840340c80c00e44051130003003421140c16508407900510880e1b101c0d074020000100c1c8104c42548803001920903100140030000440040795041074601d8002e04006c00440085030b59988190842d5036500c811610050380010802100b020f031311980c141030640c42c014050706042101650740703c00013910b6106503038890721842e11851300c041081e10054041016400003101808400b07043e281c010213540240906c1d030000110702802c40d80291011940c80800380001540c0c0c0700c024603002c02005024081d800c0c2e09120a0880d0041802081703400c5040350003403e500e040035480005143e200c284000305580c10704510600040d86c0d5011a41103600728a891601c641140c40000c04c40e041c1c420601794454141001c0c88140400410400c001e00c940c1c010142c2480072982c18800b445c00340c007460650090074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 186013723 1250 186012473 186012479
    0x80606060301090c030b04050f0405010c02030405030a0b040f080310140a0b09040c0228051e0601030b1b0406080708090c010206060d0c0b040f0501020f0109200627010e061201 77
    0x10f0b0b41c124010f008007600b0082820306030800410100c2c0d5040343c15014009030b605c148002d2080a1142c040700402a101031032416081401080e40d9a4408000030113030509a00020117100581174140c210a0b07000d12100c4d62424111000100301c81705020f507002c8240307210210602c510f44885000c0840c0c0305607004905107440d902c00c210080901828010035030040858581d0980c01c0311208200310039160706503501101003400e03c5490500d030103c0030038980f080c40480c0700d113103030001840c1c60449a10107810007985c2d858850014414040c04c3c3d242d8001c14010a01050030f0741c12103080380c41103516580d6111140d841070f90309a50f50844a203550b025030420030100c0da8508119600d02e0005002d181e0f004085a9959005582c6030312690010f00d440002010600656031b0610018985002d40d00003409103000c17a481d0344050a031070351000c443c800f00f241520b24044e00c446d42074600700c030b8114502c40c5a816001c401400032042c0c5c4403405001400c44e040071406490300030103803400d41e64a854140d2042e07003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 186014973 1250 186013723 186013739
    0x601120b071e021b0904020607020904210e121903181a09010e0604030c1404091406060f042003070c050304080d0e0609030303070f05161b080606060301 67
    0xd009041101000703001002040b000c15116107520352a0703400e81c018136403040c01c0303c200d0784990110700c421403084103040e0030300c000350755100207842c411a01254002a240c8481c81e0140c414076088070024860300020940d48a000d4100010032003002d0262014420b200c404075405032228529403150b4000b01c0384140200210b80304001c000181080c0e10b101d060300395181c40b04007851880c003a440000718400001c000d292940c8c007042026030b0b24020b4821a080905594815038018103a0290184260718442e0300646a55150041c2010b40d41100c50b05c00f450740704241080d00c0345400c0f21058010149c000040500741801d2142c03d800800c0445440020040203a4620841d0b0001e0086020004404c0041d0086101407000308001c10024004080c40018868003805461127000350a1142d1400e00c003400140e20048112039210316246011403080e0803910b0182c81901841c2e102c208001400f038003910420000c08000301451340c0c1c6c900d0b0003401d507a0300d50442c0d6803190111503081e003010040c0010884a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 186016223 1250 186014973 186014993
    0xa02091323040309050a031b06020a0201090611160b07050111090109060e030319050c1006140405060d0501151a1e130918060e0c090106201b12060112 66
    0x600c2480c1c84265035540c0c00001c0c01b040d120b90800e640508040301c61006c03914140c1911401441d190014003680200368001070059202403050a0a00c0550a11074403810070030300c1412194801e40034014882d54980603103286a422500c0c0844640d0710f880700400c550301c2c0780c40170350359401310580d00c15088070b04004080798a14400b145c003d0f010700c001d0040200c02071411003070301000345890f9502501d0f00c01448029113003101c48a90000040e140030014001e0b0b00400c00e202040342c0d015203010540d47c0310403010454404c08820050415440c1024084081d00080c00c240b0031101011a02c0400303403090034106040c0d104017024280b902d500000c0300c04800b0f410300050110b60366146c4007501200d5540f07181c00240c81a907901440c90380074110700324040002e548510052561204002e2001c0903920001c2402c1d4032042c0034132020302c2401c6c0d4051131506480610050f085030100d09450852610003a410300710441008032074401d00c1010380100c21702900045446c1240c0305010741c1078000f105070f00d03941701813 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 186017473 1250 186016223 186016231
    0x60d05010b0607050303160807080403110313150201060504140f0402010c080c0606090703092003030d060906090b06030c0f1621030509030901120b03010e060a02091323 74
    0x15540740c1c0c4031000030381e03100000b42a41da80290003860b6286001d02c0881c803450790035000f402c02d05c901d1000380a1301c00d6010300306a5000794542844148144c0c2262050724600484840351402da12001002c2407414001803d400688100c0c9c00030300000c0d03250310400098565100410001da203540340001c2ca440d0b264500190802c0c018101128450300c00d8980181a0784100300008060380a0303810312640382000c0500e182e000e40c03146801c1042105556851070200340b042e05828554448000c180c040c0d030740c18411034800b4400700b84c040110319507072120100039100c10f200f8400c4052070138090a42500b0054120b81c4940710000e82c0618280d0041000040f40c0c100c0700c28001003c0e042030b5004006140404200480c0065121101030410b10700801006d450b0000d1072011150010f103c040200c1c1d070040300140000a03141808201855488042401400d00e400d00c20510702c580024402d5034100f550081c0a88c0d042a6840b0040200000049059810194070b008a0022600402d0310101c5003055a81d08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 186018723 1250 186017473 186017483
    0x711060c3f0f1201090501030203150c160510060f0e0604021e0d06030c06030b090907120224190e150f03060a0e160314061507050304120305070203010b010e09060d 72
    0x2003c1030b4050454022100760445540182d941005100b5440c0806c5210032001100c0c041c1c0801d4909203140c0b050340d0250f0081603064504c0e00440d40c0030403109108404040707000318420005695624081c074030352210352040080c0c064801e8007003171060a0134000c48130001c40321244000c03204810001a0b066500c460500500381d680c2d40c4000c8009650a560140244020fa40108080d8290010020081c80c00344c4880c10640c8903002c10400380328080c1c0145103641d01144d540c000580d20248210000502c03040b00c3c40d0001000903042d9200707055449202100d00d9559a24455400490074026903e030600c20b44070785500e0a01074508003920020041d984040d0183c680200e00d9035450540418540964a522200d100406100c2e55290f05108003948803102450200c6642007030343c0403494226a1003004031040b031000032168148030013081158010141a00020481e10050600130b295411101d8220b101e5400d043c036501043d0f10550200480e140000c00203000350f01c48200300140040c540300b040321 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 186019973 1250 186018723 186018727
    0x21070210110909070f030f09110316031e02031501030b0702121e0a0c0b01150e0603041a2703070c0803030702100b0118031104230c0711060c3f0f 64
    0x14100245000c8d8102d203a1140c000e00b0075050881c400c05041000004070b203000c0440f0801c00304003240d011601460620045551601d509844c1c0c00406d05040400200d080e0f0302a848000000304640044124411a600da0986030026641410f050251088400d039804115a000c071400034100404000d11406c0c0071400e00310704410243d83c54110880c0241c3c054038a0132200500140525084404228501002c4600302e1a5180c55a00c1061071441d000d00d04002070303c10000920f01c1b078010b80c086590340414004442c52059012080e61341c0340c1c0101002c841c0e0050089000a4440000087d80c0c000c1c2141d801401008a8031030600d4010604c0b942c0b164100249082070745071031882c00d9034010141d0700404400e1001001c07842031105962104901582d000c0d01300c0a01c03455406041c1060303402140c0b200134540c0d9444c3c00c3c1030000c0e52600d0041c150f648130b040020800c0d8020000109076682802a00c801403400810140328040021074100700340355901030307e00c40c00000b50001c00030200610301160a034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 186021223 1250 186019973 186019991
    0x40c0905130b1e070302040303020a08030c090307080d1242060302130b04150e180f0901050105120a02041d03070302070807050f060f21070210110909070f03 69
    0xe584074140c0f1050300c001c1101d0100c100c81020920040d52000003410300354542491942e000f0350318442c520b0060601c45011003c620000141c400310350400314010120b41081c0e440303100c00ca1f1100d015100600c041607811903034030700c0c0104034040c0948882d141092035018030b0411198520080d030394071040034081410200000e2040507021a440588011b032380050311041685424003003620590040d501395401030004002007001407240d09400f51551a0503800301103c0c40c0416a00485a04c1008044510104221080b1803104d203852107200d983e8002c0c445a6a21018018a5a0181c58503003858010340c0741d0388007500b410342040300d5420982e045a0000707040008050f04640000308120010f8001000400c0400010402c1c1806006d0881e40e2040c4a00082e000948500c00c44d0401d003ea040c01107802110240740b0800040c84218292a410013840d140b0340c0252240f5540c500c8006040c0f5200c101050b418120782610010700010700703110860f0310765400589100c1e569413561000c041c1c03121205 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 186022473 1250 186021223 186021233
    0x3150e10150303020606060403240212040803061c020105040b0a05040f0e01031b0e0103020f0105160615080a080702010c23011b02060601021f09210215040c090513 72
    0x161401d481e0319491900312815460020b080c5580580304500c25035082c0000d2011800c00b007081c1000d80d440322807850070748113641c80360000303070153320055011070314a5000c01090240030701c01103100ea0700480303000c0401c840740ca0500c3d000b0008000080c0c0000c106120600001ca108801007003412020708245090540e115034840c00114680c019044d0015403500400400c018243c0a9501c51000c1c3e23030080b4450304022606021860508c0003034880d9440c1001441180d010304200c40403551100d020242040c1c181c142100a0040344070300d12421384c84010000303010207002c00d4440105070b100303203264940400380d0011100713407890301000d41e614a000194650444d10154240114000702400032407091180058a010361540760075620564001200300500c40ea804640508241e4520320803506160b038540c005801132805036001400f80e0307079405440003101410607800c00301c2e4120303600f152061019840410a0054180e1300105481202c030018008042503801c560b500c01f064002510900c040b42c1ca0f5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 186023723 1250 186022473 186022481
    0x20906040f03060b010806010503070f0804030c081b0c040c120b0604050622061b06090302010f110904111e0703140d02030f010b0c030724060605040603051003150e10 73
    0x401c0340d40710303a030b001110b104d5608044625072003071090030942d0a52500e2040504106211090358041203040e4000a0170103000707400b494452500013075510389540f401c00745401c44c0018070b1102080c921451f400154146070902402000c010566035208100d4001441ca03800782031410b0503564002c1d07007484017044039103825014009501005800c02e9031818070103861607042c0c0040e0040010005c0d07449800200459012070001c002d50f105500149164981c10b00300d0061442e1081c0040c51400c000050b02c01d990b100f0081c010700c090490702084002c40301c91140b20940308090031403400c08801c0141d14207003422000500084c90003030500083d80300d01e1031281d130b00651001d44907503051030f030220a11007003400c5c5541b010b001d440544c01c024505901c8807980d42d5a40902d4800030911007183d0201300c0101d0155440001c170f51900d0200f4080207480e102c026005400c2800303004002071411001036050642e414400040f00c0e04558038122203c1070035200c0004d041006820b0001740f0500510140062403881 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 186024973 1250 186023723 186023729
    0xf131205030a14090108130c03061d06100608040f0305040b03241e041d07081c050f07020d02060912030310090e03090d0203120301030804050111150109020906040f 72
    0x40a19520b03003141c00c0c040e200c003541a800b20440c81041c08110320698121010703035041090305c3c1032590468290b02e0049070b000c02c00e402c02071446040007420303071908007100820070001c642c21058602d290354060005580903154400c0c0c40014901001050100d40c03258000b4000c01d0003031904038581501c601c94601c00d44d0068941800c102e000302c0ca1142c140800c902d0313602d4000c2c400c607001058000e10881c08440604c8000f0f40511696031038441c203051280c045410101061340340c05031882c490b41c1e10000d40d200c0003080401c0e16001814410460b5072845142101c54083e80c0500e1207040c040d813038090006000d01c0e0041207030402400c010f00d0040d542c0d000c070205a5501110020750f5246040d00101d403034028154001c0360024288040d1500b242008816504c83c1c400c16201c0c00710107402400000c0c40e03d072403040c038241c00e01070001c0080144048080101f003035840a886104071102c2d12052507503643c510b00165486004a14018400005030ba001040403020041030302c0c1c10903840350b00340031000350168 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 186026223 1250 186024973 186024983
    0xf070b030105040b09070c08030a020d09050105161b03031d03221a031501141305030c180a1a12010b0907030b0306070c0f0606030f030207050301020c030f1312 70
    0x300042000340307401c0c007401e0b03810001503c174a0101d00b4040701c09000b140b00510000c2081c2004030005500398a43e034141c2d00150145001444100103074188180204070564403441403203c0c0d102501c0c100b40c0981c0e40e80f0008141d800c150140c071140c6072000c8000300f0a148010805000382e0045c009a20405c1010300001211411110352030901941903c4641034154000c0c1c403050fa4454410710300500384415681e000000203540d4a1034640c060040300e00440c442094900b480740803907605040d0042c240c10b02c00352601078085484400030310041101c90440401108400c0841d00001010381209810420546020014840034038000b0f000050300d8260030780c1401d806079918140d403101031410102e201e401c13460a0404024408a800100e61501c000401c03860078844c000c52124100491a9480034085030055020000503440b45012a28030380c1140041d80140301d40140444c02d0725061080740e004039400c000035881c0c206038400d480712a801c10b5403440200070b035158001a5030910000030021182c450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 186027473 1250 186026223 186026227
    0x30c0611101a10140a030902030111030117010506010c11040f09020a09090b0604020c03091203130b07020f01020606090a0902180901020307120b0d082506021b1903110f070b 76
    0x3407414004205199150301040280000314061603022000c21910b4082c5c3c9407030042031030f003800d00109001d001061b441180c408000400040c0510316001e42d503100e00d0801c40288165100c1400448410302441030160280d014815000d4040c6003a0340510140700e041040130440740c11750f400040d6030444642c000410381d61a001c15004011420403074079403124044604606080d058203846540e40203c03251103000c0d0f10034140342040d8030707420020380c2d0703044e910042c014100f69200c400002c4240c03c1180c00b240a0f0701182d01070701183d230012441030f10600d40075001c0305e42c035030742c000c0707002c001d0700910000343d0300705d00b030038108515150070401e445e8410160040096941e05155400400424818a8410035a458000740041c10307642c0c61812410a504032841d0758440004503250456005c0c40c061030800f56076002c02c0c1030100500750f0054a40051000703807007420030380507402c5c031510b421441c40440281242010f0701d04c0028010418480d20b082c20320202c0d5419103070701a285190031082c1d04210051a00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 186028723 1250 186027473 186027521
    0x1f1e08013b1501030f0509030d02210a0209040608060f1902120423120307050a030b030f0706080c0c0a080a050c0f0a050c04060e07080919150e0601030c061110 70
    0x140543e0070482141041040240f500140c0e20f40c0328003450480402700d40d000100c3e4003424010507140090b60f080986111114280852200000d600ca202c480c1e000341e0030150002600000460418800c1e100c41c20300c0701055468500081020b488142c00080301c0307909021111300c0703848402e0154803031889600700300f102c00182002c0c1e100b154010f141d5115141d01c010f012804103000303402500c2d0048803c0c1482601d58441c1c2078141c01a200c445042605803280320300b81d1581e5400000c0540443c1c246464150094843c0329416080d4800c1c0c02c00c0c3d42c02130f40051040c400207103156005202e40016841d00700e06202c0c9a11001e403d08c800c0160114260f4000300100040c403000b845481c100500440301040418070305088000b0804000f001601030103121000034408400070b22a501c00001040700b50b610340480c0c0d01d041030500036494010000c09292035a4415107080002e40b09050380e80094905030618505102218100500300306105c680c099007070106041007050103070040b8410079140704050408 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 186029973 1250 186028723 186028727
    0x213060801170a050a03050c0a020d0503070b0603031305090a0f060e040606081b0f180702010e071409040206160c0b03041e030e0f1f1e08013b1501 65
    0x181042042e401c1d41002110100089002802580441e41420000d844641014406040c5580000040d40001d600714460003080000300090154031311400b51400c032a1038060900d5505d01400c0e605010b40d9006034401e000d2868101d0826038420400007020841809800c1507000344c401c1980219031150a00043c0300c1006490f0007201c029140502c001c02404d00429884071150400031007a80c01818500001b0b0055180c15840004104c0443c51580c56403e0401000f0300038003052002003154000d070000821064a44003501c0021070005201030301d079845640130445a6840001c500001a4220a08000080c1d5005058000340310003d030580d16403810b801c01c0c2c666019510344441c114481108058000f135023101c5602443c5405840c417509526413040462000d441c25000e8004603401c48900d900c0d450390001c8100400d0009240f49121406030000c25200a81c7c00e025030f41c40d8141d44181441d0388400e0450020085a00001803a40e00030b0748410010422800d9884510032404128000c2040d6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 186031223 1250 186029973 186029999
    0x150f0206090327040906110a090f050307172803080f040203060a0e030c1605010e1e0d031403040b250c0b04020301090209010f05030714010e130213060801 68
    0x40500005146000d070080441d401d00c11070301020350922001d100040200380c41d91790041c2e60040e8081c4082000588a6017600c4050b00044030075400500041404111100e4034203010040b1880500140390050a10060321021a6040100341c4240b05034480c1c45440001c02518010000004810b9a10784541c1d0500a0140d8001440410015022001d000c0180c80000d060780c3d00c8021404000380001140040c1c900314810350039070861510505800c4000c3c5030201c0042022200c0907250aa0347e07181d00818444103210410b4500d03080e2034154103231a101c0c02e00619595603a442813410230491900d01c114201e56400c1a5016030314101c5c402c1c100301a103090000010400c0d00000711007804480c400070010000e940140b00144201030060201e82151400d421400030554014000d1078250385513080c03000604108c0c82010310030b00c01c51800040349400170b07800811151040c0c0d200101a10080d0034405115040e419214a066082100c2c194105000302510040d00056540340300551400031040900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 186032473 1250 186031223 186031231
    0xc070f020a06030e10050105100c03030b221b0503010306050c090909030307090602070f091802040219080a0903270f080a021206060f1908060a0203070f0905030303070309060204150f0206 82
    0x205d442c0c540184038550398005850740414085c6054000c60071a450124044c0100842d0030380c10051210712590120501e03071072182d0030022a2070030844440480c546000d0050403901010205200308014401f00760190425a8000b200303a44880c40c140180020825035107049810b880c0a03000401800380540d070104c400740007880b01d1304c0109880c3d400e04c0712203813a0043ca88282c11b20a0b41d52011403d080c0700100490711a135130010000c54550701100080c801c0b100702c190203600003514040000785c800a061080307016107034050f034030410a11200d440d0301b501311a01d0404030311000c0703440b0400260f040c0001d4441019040c10320141c090f41d4440e2040c04100f03000380751945280d410450030415251104900280c00c0041281c40201c07503040041038441400103038020741101d0151b5020400030811640007140130754011ba491440d0039080d20806c0340c14000718095980c2c590020804180c95521a030491107d00c1e0090341c00520709940c850101708035460021241e40415121381482c814150140301da2688 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 186033723 1250 186032473 186032503
    0x31302100f0816080106030b0a03050a030201020703270608090a02090a1a010302120c0f0403080a090e0105040e060402060a112b080108070603020d0905101506030c05030c070f020a06030e 82
    0x1d8000c0f200009422800c05015000805035070b00308010443d52084c2c40c0300000d40d0060165401a000c60800034082c6d800b410050b07010640c0020000c0204020415803c4d00c100f01440c800c0c500340c14075900703d44030400941151050300c524000b080159450f00b1a040c02501c0c03490300000d0416080c620303004101a07000145051500c180f0060705027140c81002e060b4861030350340d456642d5116240c090b0b07225015a0b003015100290114190281c150002031203000d4900d84401d13049940c0e0b81c0c00400040e00c003002c00c0402c1c9034000c60007003001818114090880c01107281408d105590b0542407492a21003601441504813007071524041000c0d851099481413540380d89845c0c0350660402c0445075640d0b00c01d1248008140e07000900400106d803a81c01504c1099001090301d8806040444060141900c1040175603200c400c0780c00050401d0281c8500c4070501565200c0d2030035551258050303030441e08101c0781641c6094590440b20010b0b42e48507c40000b034010343e200050829034900d01c242c075080c22101c007054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 186034973 1250 186033723 186033751
    0x7060f031e0c08150310050c0f0c030901120207080d0b060d0e1b09010608041e150e0f06070c030c0c090203012709080f0a090b160201031104030201090506031302100f08 74
    0x50744010503419458400000302183c151100c501a00e5903200380440749e41c949401064103049000c000c0f00400700180b09903134120400f15001c054900f20711508000400300b0b0400c008803955103200e500150804c1034028030040c05e02d20268104015241c07204960032454014503518000341c1e2180b40600414041a59010f5981d0b04054001c0c06205010344060a44c8201e04442c0c05200d01d103042c0e40c1051039101403c3e030140218410390707401038914000c2c5150b590040c2000c2d00643c600c0001c1b101c0c80f401b020b036101d595240c1651000d403143c480303000054a02080c2000c0202d20800756000031130003840c00420480c1003241d842401c4543c410303040032031072101d17080000348030114070783e5020b82e582c0310011074802d0343d5800c3c0e012050f034244e02c040e440304085031000b20f19015180088038a40305032a000787c070305001000040500c0705141c8182d01000340410401c400c01e008605050700950341c418103c5642a0100307003141c0018040d81360810081c0000b4218105000c2e4066001c904207400c1070356403030288 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 186036223 1250 186034973 186035011
    0x1e0e04060e0f0106080a0b0a06082205030307180801090b04020a1211061b0d0e04061e06140c071e08010e0a06020d090b010305030d050f01030507060f031e0c08 70
    0xb5406441c10301c01e013820030440c5008100100c0c50343c1c0c010054000b00074200d21005030b0b98440680b04d82c80403076140041d540c00400806003100c0c2e030195950050b80c81406186180e0b05ca103000c0c1d0301500b0003040405000160704000c10101024401c0308444c60144c1c03112070b59882c2a10400525000e036810440800c5070341408180002e4040340d84080012044440c0394869941000c1088101905903c281407032240b5441b010381130760444e400c8100c035042076a00348070040c1c590070030795000b824902a52031808080c0c041001a43d00c01c0c0900040e411041c401240391001c1d03501d1461030b015007500075140c50030a030084480c41e9166444500c1c01400c9890091280c0c80310701b0325950b00da003240175014000c5500003e030300030210510b9004d20511540541d0303104003540c403070500395565044600e10f4080b09240501007010700020a241c0c5040300e5020005100c12070912408444511640c03108809058482501c84007030349a202d4204000341420b000007420341c0079102d0043c90302c00040c00d40180341c025040d8403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 186037473 1250 186036223 186036241
    0x5030d020604060207020d0206120f0606040614130b0c060901060614090d08040f0b0903010c170414030f0301031101080a02041a030c0d0e07030521191e0e04060e 71
    0x9a0160f00034000580700c1c000c0d40082900604117035030003544544000b03004030b14400d003084014021940b0204142060b0340f502d081c0315981c4202d00a940118500c0840c245646206d41c3c024100c05220b2880000d190f5038402d01d40c031282c0c008903080a0f0701c0c0c008a040105ca56003d214180c000c0005141c00740c0980c1c100c5c64070b402c030f910511040034000c484001c0000148000c070000c44000f00411079100c92415039501404626130013103132506100b5400d1058102e40c192041004080815403010018010389490b0354855091354158078a0401e800240600b110000845001e10300850140315032040001111000501e00301c2c006000c140d84900c184001c2c031000846c4144070180007115058251f6035158035003100418002c0340c85100d442d0341001420301e4580808124002200d2040045600e90203600480c203c40c0d00c024540c02000c4803052000702602c1700d090275003401d04401c40c2004034190146001b8590400300c000746807404102240c3c062000c50500d445040018104c0181d0074416080c201c480f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 186038723 1250 186037473 186037483
    0x314030f0703020d090803100306180308070c050a1a01090507020114010b0d0912030b15040501020d0e01031e051b0c0a0305090102032104030e060306030c01030e0718060f05030d02 79
    0x201d102015404a1603001c081d407a03030300940c03c2c25080314000c0d483c1d142900c180d200b050a6800200c801a040080742c10180340d0944442c09501d034540c0700c115282e43c0d01d0350112446405e03a08241c43c80d124040080300851041c2042c883d40303800411001c03550750b0405011b2004e80c0e00142c070700700c2160305d003140c1e8120800c131600601c2c0c1901d0803440c6840e038582146403890081c01c2c040d90043e0290b5110071003000300c185c0681c401400704400742d030708075030344691595004e101e402584199805070f0408001031507454032036804040400e505050001d0122003200110303410343d528850300800d02d03036100c087c401c4030500c40f142d05800441d10500140f418683e240d08035251040c00c68020207014004c20361194580c0240240c88400020b02c0314400048568010512129420744051b404035800454080d89424048100c0707105800180c014400c100203200114018810002c0c4000c007402403600110314081104040b03503502502140224405080c40e05921041c406540410b1007035001c020200b00e41500460 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 186039973 1250 186038723 186038731
    0x51c1101050306040617030301150f0504060c020a030f0b07030e070b09210d2d0e0d0c170102040510050c0601060f0e06040305030d0b0901080309040f0905190314030f 73
    0x1038859241c3c1c5840011402401c501d030848211410800071800203001c1c00009181222006499402100000f90003035850540700c001500020314100024000c00d4000c03042d5000913440500040900c0e6660303210703c1213050301d42400b180d40d01d0b030307081c00d0001c5d0591501400c1e0401c100c020141010b00d00d0400340709290310031120742d0750140381e1420441d00b884c0d082c041c040e900005401c081c0c488180c551240240051168000043d507001d036140c068492009515588144081a49648441c070307000b0010400f520826040c21211200e201c4004208002d60704816511004000b00160f2290305220400a0342c45e805000907040000c14082494245000510181140c100e414015004d100c0540219a0070052002d800d4100d000010000108680000207100c02180e038401001040a24001c0001221080c0b04510a581c41171002c8551894150f20031a0201041e40c00000d0040403640c5060034800e100803110102180040c28409145e08860482e01442c04800c00b145145042144e400b60000068 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 186041223 1250 186039973 186039977
    0xb09070504030f0c0e010e09070e0708061c0501020a120b0405040b06010f09080d0f03050f07020715090306060f1815060c260301050312130302010e1302070309051c1101 74
    0x201c841818030076904c0001014010035443c400c4d0540e10f840400300a06016285455284a041030000e401808049083d00400c029520a112501c9100030031211091100d45140002c81c1c8104100000d40c00b4070040c01183c01d59218140e000b0502c0c0596802c540540c0d080314021400d000c100800030321100002e6501910900b880f0b9101c0030b101604950f42030b17035a00905a544188203004100076049503035680c8109103640c007400300737599500c02185500030540b46a4050f0b48041c405100704a07d880c200c03e0140f15600c1e00c0a402640ca450721400da0f034855010240ca8001d0207070a1001d8041c48840324580601d104040c84141c440c1e2031101c0c96641d041c419041004030440b401c0040183c041800c104207681520121420b4100004040041d40300f881224464401c1e80e0500700c41891038419034268110380c0e1100600d55155800640e020004190240d510003100d4058103085250352000e004900d009681e42c0110713900741814441068003d1141c420f0826810801e100040e060480e81e280643c0c0038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 186042473 1250 186041223 186041243
    0xa060207080412150509191203141905010b0703092601050405010b120f12030903070c06230306060a0f05090307060201050615030f0c250305030402040b0907050403 72
    0x190419a441c0d0040b50822400e503020030403400c0902a060100f1040c4407140c220401c2135441c0c3c0b41035159900031130f5440702500c4540c0c01100c000b00324020220f001c0400346040228074090344803032041d800c400407140100c00207400032008942045a215507405401e168a41c03610b081442d40700500260540c0c1b2030408000c4039a600060599440108990400d10190080c012030a0902e0054080c0c40c0d03041000313010b90691564a080d88100183c0c003c0d004441201070101107054543c10b404661009200c0f900902c003c204070400522217155202c020291070341e072091080d44c81080c50302405045124240509810320a2218030350724030f82101d1031142c00d030601054011101e00300b60ba241c012042d01c2d0342e240c010800700165840d01900b0140c86002c04888040c1016140e80720420300d40400c1d100741c00196085030020303429070915001050402ccc1080030140c80540c0c20f00095041315440b8030101d00040c0040180303c11403c003030080d030409030421100c01003070f45440710000b06113006602c0042c000460b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 186043723 1250 186042473 186042487
    0x30f0711030d020c01061d090d0201051603020c1c020a05060a02040b04051309080301080309040f0c020703030c050a0b010303050a03051614070303020415050c100b220f0509070602010b090105030a0602 88
    0x701b54001001420780c003940c600105802c442ca42e921042c11150f0a005005607018800280d03c18824648500040c2c00382011600c0c40d10030450003500481c115000c00c0c0310f103c624084600144070749182d0381d040c0c1e50051183c40c1e540d03c1c10a0510304080c10100c042c070700600083c8412902001a58191881906c0c0b4211400076100454050702d00d054001c3c00c42c05000002103a40000480204080d10058800b88144100c601d00d5178212400502e0780b90040e00444014000a4422a4117020140c090000c4814250f25038940901d10b910a0b4822004900006886003e50350107009040d44800500403070540481d4144016016070324440f410812210300040403420580240d058a0140c446003610031100403210501400691180462107801c0c0f08815002710540300c140110060031002900303858482c000e0f0a210015110741c0c500c0c80d50041c0c0c80b03a81e80e80640c21144a00c5105a204d4801400740c2413400a010f800c40701141080c43c000c110102c0144141c1c0c5002800b00540b42e404440140d940903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 186044973 1250 186043723 186043747
    0x160f030515061c0c0e04062102240a03020a110309030a03030203090a080d051b0f07060c1202070302010501170a03081f050d0b04031202180d1b0b030f0711030d02 71
    0xd2810b41a9861494880907048180e80240c9100700c5c2030f01514100705441e1550101d14001c005c241700400c5088092110500604020350310034180b220380c500402c0300c10002c200c0940f103504601035090001e50b0110b690981a9880203268803c0a04c2078007940c03a045000020030748075006001c0c06014503030004085210030f1401c00c0003001c0316800a4200c4c0c1c5a4001c14031440152030142e640301110740c0c2c2ca43c080086141e9030320444204940c190394051078100e8a0359160050960301d08103c0c00c0c03040003d180303420843c01e0300007003e80600c60341c000940c40d03052800c2e0326a50300708442101c00c140d0014015a00007a00300d1001a0008a003886144c0b007035442045a400f00c004c1908066081403007006290100145540224020f5201340c07200c8903030984584401080740103843c09000f0008c024403c000f0701c0d06001c03030201c0c4401d0041c00c4004400d00780500010204000c6d07841402d10b94800003c2000305a828000710703410440c07600e0b01110581300039000031b5403801600110b8074500e50000349076803148 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 186046223 1250 186044973 186045007
    0x50a0c0c080a080301080c01020609030d1a060d050601032009010315030c060810210f030309061e15121202010603061a040f0b03071814160f03051506 66
    0x8901011070308442d03400c0c5469880303a0000c0c03256080500c51812040300542c000f00344039105440801c000c50800c29040082e001410340300f944500304030300414800a0588640c2e000f0402118400800300ea5818540001003c03981d103680d03c00c51100545490340203511603101240d81d681ca00746004504880e8140000700081da241e4070007080c03c0ba0604002507040e41150100d803003640c24009011800c0d43d1644c5860a209003100c52141450b110b025060018421142000610b0b002c1e141c000340d900000d40e12681200c0c10701c4018054044a0381424220022a01654a01c480500fa4514007540740059000741c0300075130034008184007011181c458000340b00358006e80046801034418000d4003502016204070040b00c2c0f04090145043c4401c000c211704190003000c18100340070303009002d014070b03040d480001040c8900c040d03000d95443e030008010503510700741054003681700f4040c1000d0703241807400c0c0034002c030900000150034142040e04100b4618001c03031034501a60f00988045503a13030581c842c642405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 186047473 1250 186046223 186046229
    0x10207050f0411040b0703020a030f0f080c16050a14101401030b07051309090c0603020319150503030301090c0801170601062105070804142e0603080d0203041a0403050a0c0c 76
    0x10413400311b0110b080c142d0000e0b405142038001c1d11091302c00b100c001c008444158a084105012901c46400710700419542802000e2642d02490348c011010120340d0741a080c03030b42c3d0300d034103550b8280504012031f41c025081c0103915083d000840e04001100d40c02062080c030070300520015016041c1600002d621600a008881e0860076802c0e940f02042c0c1c86000b2807004140d042816a00d015000b031010614600034801c42e8001c0c143c0803a00c415080c14844058058105011a149075844440f0001200e460400c091406410300b9a004504104024002856081e050f44001c0c4c4011041c10041c0d041c1c0c0c40812100d05440451074001e00f840140190003c49081074100700003a01d24242c104107107903500c0850a4040c9200d00010483e441c070a00d031303480d90388801044e0800c81524140168282c004201001c1842004940010554603034030b131200c034610341051101d0f4600c04d80010030842001140391000350803040040d1185901d08280d1002816402600d8241741440000120340d418860000d13032203002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 186048723 1250 186047473 186047489
    0x1808030c072306060405041e0201020304180e06060301150306020904021903090b090309102001020a0c0c090204031a0604110c0c010305160e0d0c08100911010207050f041104 76
    0x10390701d0840040c0380d054407403900500340b034050301c0d000c21501d1605000b1b190085800c04a6000344099140b501100b580520305c0407410b502c010440064050280500381740129041e040c000740503d11504018208103009001c4c92199240c60714142014840c502880180e035040303500142c50f2620034000c01c0080c8a000c0745614105410b0b0790743c00c0c5540c5c3c55040040b07880c1c4156840d0846071070324140c15a484c028181499442602c46980c4000f552007109500c0e28000044841010088880c3e03c4608991190304c0036400582c60403992010300000c1d000c801c008007000f030400c518140c59078680000c0a41050302c07469011114034081032050b42e480d0888265440b4098106a903007000d40700191f40c601c00200402e010030305107800543c505017070608280c1425020b403106240005107208111207203200d0402150b4202c40c40d140412031304020440e20380d8003100d040c0000703000b0a690800c21000751031aa0064119807014009000685031b460320f840c2010000c0c0d40c0402c4011000c48201c017940034603008038207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 186049973 1250 186048723 186048743
    0x1501050306010b19030f18050d11070611032a0610031e051501090218040209090109020c15070903060f0c0c060e071a030a06050901080a0209070c080723011808030c07 73
    0x10f60011001c81041f00c05200d00e00320382190000070340541c0c205c9100444404981c00c500404c020260041801d580c0310802e1030107507407911901c1d08146400c440c02c404044a80340744809045c80e42c2d0020004503410008600841280c3c524660f20400e040000e0380d03442c2c02c00c06040444108005041100c580d202d90380c001e00c102150384600310007000f9004005c420070030750f6242150741070038201842150501e0001406200b000e0b820020032502962204104000b13a2043c2d035541350141100c080e83c240108074aa81c1d030703a400e902c1c600340002030301e00c0c4481300c203000d500e00301800741701a401015241109900c14404203859141e2551942400c150f036200301d00700070314040945000c03411080154480c0c7d00c403020400006032510140221031809024034041a481a0070940c0949003003050b45074070480500d03014072500f20907a0388215642140c0811207081e86a81602c070701c050003407a07201183c44004030080054a03502d52296420203c40440680b407400000003044044200d50211103140d500400201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 186051223 1250 186049973 186049991
    0x20f1309030320070807060b0f0d0b0403120b030c01080703060b0a1110060b0d021305040e010b0f0f01020a02041509020307051306090b0306060c0109050f1501050306010b19030f 78
    0xd8007510311290b800242040c103c5000d034400c3d00c0002915085600710968508080f40c1c2da46c2c0340002c1c0044680c80c0da000d241401307952400d40d82d800414140500c01c00400311303641014940540000c1500303145008035030800c54500d1142e1400038a0700c12100091130050f90ba52140303141036000b0001a0802d0440400c0014041c052517040b0360304840706402d507412910202c4500c0c1c000c20465545005402101c0b0040107807084501c3c064001d0610500000c0702c40c05142d907100000380456500c0c10703d403060b0341d456504001c01850500c8440d1030308281507034005050365038080002d456811080e4002c1c492951307103102120b80c0c805c031a901405010381250441d076a0401c10009003840d00a0b04048411b12001c94010404910600064044515141c0c4080c1161611007c10034250000842036a0941d0f035428440080b82d006c12134003043c48803039009001844c1305c00c0e2440103540d00503008180260f205800404c10b8448503030441e400220b5070051860b07071101c034840440c0605102c121000c121070810b02c4003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 186052473 1250 186051223 186051227
    0x3020304020f060d0c1106070503130309081507110d020c010c0f0611030910020a1209060e01050a020903010e0304180e0a050f03030f012c06061b010603141603020f130903 75
    0x3c01c08098992141065440e24245040d51402e003143d48d400012014008100d2001c51100c0603e4004d1003030804444258903140c41c1407400d04d40c41c41e0400b03008040340621031040e40100e400d0750403014160140c4a4010f0804003e5603070464000d42c5410040c001c0c070060140a48000707510070b510340c0003409000c0c504000f54010a180c20644140700c841c0907030250510300541c24400c44818401680b0380400f804920300d007890041c0440302040d101c08e900e503152881c0400c400c2c86098402c62482500503107800403082418211144100d869405038403c00051001d000f00107290184a455000007080801441c48290b04000081c04000e08a100e0000681220200800a14410309509004020356030740c60950798000100107240d0803020091500c0b1828290400302480d0340043c3c00740800c0d18100092a4103500c1e00041d2980201e503956605c0203008200746030f03440c0f440701c3c005000181036200d1040302d02d80c03000026110082c03099060030648810742d202c45100ca100c3c03410302c84041125599074240 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 186053723 1250 186052473 186052481
    0xc02041b030b090f16031d2b02030301090221040b09061e0601030c05041e03020901080a2001030b15030a0b011107090b0d020d03090e060108060d0303020304020f060d 73
    0x4900400d06007002040b40d41032440d10544034810383c40c0c042c0d15949402c0c030040d90300c1142c000d0075001c05403180038201d0440d50313100305141040c10003c01043c110b5001400000fa0203030704543c411100b810b090020081542c00010b0380d042d6400480d0040c1c2d5811441820040c3c0e10460b04065540b1000b4800c120511a0003c01c1c0d511a041c0b000664065588195072103030110100141c071b906040c03404020a007294031991290071092490306080349810f448503c0c05900d17051405100e03141c001c110a00740304500b083d001c450b005107031807401410f0800e2107546100003101f55881681e150b4002e000410040da10079000b44c801c0c5e0300c0107000160703042c00750521401c0e0b591040f281c20010908051180290b94490210408908528800707040e5880c1040c962501510300e05402e40c0d030004451030b088000d81d0310f085030507500038841c0c0c88000c2140e1a241060342c5286d00148240e052018003410804581c441c20003a8001d55854030340180e0304d99407880040c0c902400301260030b4022101245400700040c6a0780 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 186054973 1250 186053723 186053771
    0xb0d050a020d060f090b0a1d090c030729161401021c090b07020d020c130908030c030709080607020309010e06070c030c08100209030c120708030d06090c02010b0a05010f0c0204 77
    0x17001e0120300031000078015030415a100d040c20100b50345521142120000d4030207a0400d50001c00d40d8034900d40031300082d25000890700721440c29502409281058a00503010715403154414101070b00b400003103406000110b4220101a20071880c01d80c031040d0020082d81260500c001c01c0e00c001d100003d0070380b495070040c46030040c00c860083d98140402e200c1400080c0c40e5060f10705550051103036071203010501c821203d01c06804110642c680c1014030000c5e0780300340507600c504019200e5a45030715003400018140d400651020b4429006242800f00d1aa800702c100d078801e44081c00c040c0030110300358000c60b0051080c2c1e000504140d508510200c1000300d0b0b450381c01700f15000c4408907000220200304c040200d20031a10b006030704da801300d00c0600d401e00780b01503500c002000318410340f42e100e940c0341c03903650866010b1002c942282d41c1e590810720500d03055109d501084c42c06403008028094045c3d000c00c8401d46a8000d0505001a00310181041449a006589119070161040c0603021000c0080b0440d056200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 186056223 1250 186054973 186054989
    0xa0b040f152405060711190504022118030f073009060e09130809150702010813030c1103012304021c050a08071b060c020a0b03010b0d050a020d060f 65
    0x210010b40f0380340076400e40303040350340107916510485c00300c1003008043e04080c140010300060104c1d001445903282d01c05003503042c11341d40c10308001500360102c41014000040ca03940e030200400798480c000c904008181d034041e4005480305580c0700b1f014104a140090000e0a07080007502000c040c4c0303190011207035001c20385210340e1203e585494403550203407000360716a00095048080c040000c0c1e890800d8601070101da0740183e2000386011001c0d408554003040043d921410711500003541021540d2211015030310030402081c900c0c914031180d40080a44072400d070050098500e85100b84c03810707a820b5001c1c02e5044007011202c803402560008032040801e044806034030548a00110020384c0c0c0002c0321204004e903100d80905202d0b22182e03a4055039404c503000594020003928101d420390081d450014005d000961a00f19181c0007600c100090b01d04240c0042403406024030041199482003020784003116108031020505540340344650000303000e03000b03151212030704140300000ca44140501c03c5055039400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 186057473 1250 186056223 186056291
    0x3020904020712021f110a21020714072c06011e0f090f0302010504051311040b030a051303020d0e06070f0605010f0603020903100902130c02011d0a0b040f15 69
    0x568144040b21a040301c4400000310030007094803002c0c440c042d48215034039140000312100c0e003040071448c101e130480e040803142d11401221a034090041002540700411000143c0c03111134046c0c0358898074004079110300000c4007034140040b806aa00500c1607160806c0300d01e42c2c0c1d544012a440006000200d14180300b0042a180f0b01c004c541c207071340c900513001a2901a11010300e060300e00b806202c0c840303e00220346c0788100d0f644c8012048600300000240001c0c0342c4204899100d003000302c4000200c1e0005031103481c0c040042c41000000980124040701030380414202190300744c12050100d01184034011000389081c07030300d904d0300041150640c80b03641a5090f035004c0602858460030290200d01c40c0c122000d60640c000c92004400c4503441c2c004081702e600c06404416201d0407611080161031b030b80e01d282d00c0540d44a1961034511416442d402c11050300280007020b141e21240c9402160303600c0540060b10f801002203c1c10148482d02c2902514208030003820810360700714100600d080c1c092442944010516 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 186058723 1250 186057473 186057523
    0x30a09050a03020a0b030408040803190f030c1707091e03030806031212060a0b0a0207140103020f0f1b0f0703030e01080c03060108060f0303040305061e070f0302090402071202 77
    0x40302180c03082d6640941880c1e0b01350706148020f40e0301d0300000c200306c0e5501410031000c2240c2c0d40600240001071041e00071000965180d45028001400c0301007904100342c0341844140c180e41e840b41d2203040603065110301018036101c40348203d9900701c0c0da800c680d01d0280c0100c01021499480c20648007203038001d079903c4140351140c0041540b00e041c0c0c00c116640c0804148698800d81c01e03640d03d019000000200291241580c90500e0907140c3c020f0490714001d60082c04c0c0412071b00200c2c81580a1200c1e0910f0110f00d03003501c21611104900540c1c008202d811400310b405c029402c0d0389803a400c410308110048419842b92070310740b1580e88015000031000140b0200d40c41c1143d5020311286c0380200c14912a86056603510303401165005c400400d106d1b4004440044005582c40500007480590b014030054180c529240407400742842c030a85100142502d9001000482580200e0110f031036072491030056a1000000c0003d4042d0180110140642d400b00030222480e81d0000360b81b000c004020600500031401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 186059973 1250 186058723 186058729
    0xe011503120804020105031603062601060605040807090213050405190c030c0f030b010c021906091505031b04090203070c0308060109081c02030c0601060810120210120e0a05030a0905 80
    0x14054400901007036051010960700038581e51340d6072840c1b842d881c00056034bd641e80805012090302d42c80320440001c00446501c030255003170140101800f070506081c0d182902e810b01c050341d0f868942c07141004442e4045507941016014090420062500802c148414140f0480c40c800300c078407000d42802840e1800383c0407003506001707001e02a640030312900c4001c519040310000f50007411406007050f04010510308d80e400107a60340c43c461039025403c1100584401c1c20004050300d04c140b1a04408031103003040d800750291650040031070340d1000502e10390041901c911025082240203d1300308818450011040052a0f580401c400c65213900a40e030317045168031a030006407a0002980251440c0750401d649400754868081c5100540407038900c1100e151904c07175210641801001c0e0006800107a45c04107001c01004004031003006800c0b00800d610030400243d0000e10300d2051404004184074007045c00b650109400c0d0300141c5016540810b41c0c1110780c45150940e1039503c40845d01c00440c200c04800b1903581 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 186061223 1250 186059973 186059987
    0x111011070617062b0302030301050117010e0115110a050c2b06020a0c06050a0e0c01080c0a031104030206070c06110102040506030612032101090c030509100f0e01150312 74
    0x10303861000000380e03c5000510442141489407021210044a52a0008000c021140355610700940c00b41d130b101d50414000402d00b80c00104d0503221241c000d03005100348810100e82e1811501c458000110342503001c081501c0403e6450701d084110f006010724801423003c041180c00303ca1900711500d50300c82035412000d124054980d00040300c0c41450450704c80016400d507000380814161410181d128803076503510802034810445050103840d4881000301240141000016a2140b0908181c043c601c2c2800500aa9000b600c01103410151541c103a8280c05d409801124040d6401402c095540c0b1401d08056800382010710584002800090400c04200010f1007600e0580b00010281d5207140c881a00304184c4100d40c59040c541804204401100760036140c580031034991120281c0605585040004412502855040342c18141032604004151101084400361342c0d034120302c001126a160030b605401011125507810b480e605c0c1c40240f150000000c0380e40d80840b0300c10b003521400c00c41203c0c8112010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 186062473 1250 186061223 186061247
    0x7030e010b0108070c030c1b080c0301060503150f0601140a0503181626070e010306050606040509010b0706060312020a05010e0c06120a090501020a050901110610121110110706 77
    0x45c00204841c40080d1080d0107206845000342c000a92506001c0510030b42007800340e004800b6680501007001d410f040030b00a03400103000450241004c000700001070840b148004054074058400c0d8400508144e00600307415400031040d0035150740322031003450090a207038000d4400418805034040305c038902c4800010801c215454480003444003500d4600e1940310036090100307107840c6e0b40c802c080c2c0d1031061000304550001405810340030005545503003004011110054242c0780030760300c1000244055110503583c2070450b034400b00200d031740302203a0030a0070080800741c0004105056a40040b0061a8001001085940500020007600840080040d9030f112041151078002c07206100107014000b40010150780888610350100b400300c415940c060899004020718000304070b012a180d00350796031160088105500030fa005202d03e0030b01508029811240384a50103820314901c0c100030800c0801d4415100b40b04010b0800c0c01d1060003690702810343e003544060321855100310040011194410742d81a068 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 186063723 1250 186062473 186062477
    0x306040b0d150b010905130c08130807020d0203010b03060a06080d0c0b0106110a0b0a061a13180e070806010302120d080703020d0b09180d09080c06031e07030e010b010807 75
    0x1015491107a07030b001901118031024140301c202540000c0640315224249480680200002108148400003600d80d6001402103d6803240d100381704000600c410b0100c58040b501240c41200c10b10407840000d001d08081002d00b0f41500a80080c029200300c1d6030802401d440c07001082e43d0b50030440250844000b03200400c0500701c0740194004115150007440510390031304245061300c0b514403041c1c85140503c001600c1102c41d0580e505002c03c150b52040302c2e489001051080304914040e1130000310354100400f030080302c8034609807802010420440c3e5000312480d101e8401541c115039960141e103915058244405c0c2d001d13610024860440c0708011604409c004a951901070154a070444210025006454800003003030356040250010395400d40c88600c540e90f8404441101d032100314505041c07030500c000c40f10500c09d008038184401500030940ca1030121050703e076540c40e5030350703a0590f4074480404010321044c008110188010395605400200e030448000000b48040d490340401180c443e64111035540c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 186064973 1250 186063723 186063743
    0xa0b040221070e06032404030e060d0f050603010e03130b130b040b07050f0607020304030f020402090a230102150a0c0e0402190323040b071101110306040b0d 69
    0x62800318505180001c8200840c503a54503000d01c0149000380e5a040581000307580c4040040500d001c110145510a002074106018403100c0c2c144404400064001024019286071703603c5c10b5100c1c181640c0e004c04400380e050144a0b00c0d080500000e0a05540719070103542000b41c0700c200e4107800001c44600102d45962007030994071b80b100541c07140e004040258142d412403a00003e03e00080c6020b4005848406440c0b0303562074540c03821500d0115880c02044154028500f006038058000c4141e90480c2c2c0c00412034071900c440b03840000c00910602d07c0d100d502122059010a410000030300f54540d04520240707500c80352291500681c0e0300d008010103c40508030010009040c0e00035600840418280d60401c4061040365500040c2aa000040d41044681c1c0300b1001c4188250b01d40200107c9410184a0500d0441580f004030b0300702c8802080903040c201d0700404640600c0c480d10200d994030820720003c020380601c3c0042c0902c00d41c030659181e0301c203a04041c49501d8a10308464131440e031940c000321420b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 186066223 1250 186064973 186064981
    0x11b17010909170a1403010306050105030f1606030b030a02030105070e12030403020a060302070f0f05030309010c1b020609061204060515060306090a0b2701030507060f0f0806060f160203070501020a0b 88
    0x2499000b00c004e01d040004200d0050600c90401000c0c5011b5031160320003048541c1070406142c6041e2480400d00b16680c012a103c0320300c98150200c5400703982841c500030841000c0c0320b000ca8030700414580d00035010b42c40c0c40100b10303103564060307059034031250122034a1790f03a0b498113289259030340a01e000103035200101c4002040b032580079038010b06005218500c640300d2017a0342c0d2a1011041042c0c8000da034903810000822855803020710038940c40e030029050402d009501d60020803010078000d0802401403a0001d00c100050380d40c0016203004103030309102001940f0b014603040c800b415003a10140d07240600c48600b41c40c6840d195055a100303800207450a004c41e03403903000c1704014016080c001e030380209400d890041c0591482d901101d0504800c03840c101c1d554514504a80740145541c040010020306400008184c1c0d0300507000200700003249041946502c894000800610036103c81c1c03a40c0075030000d9504401d00140e81c00038440c1c2e0086042d91106c83d900c40040e83c481c14003080060014030418000303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 186067473 1250 186066223 186066263
    0x403030e0607020a0801020d050105011116050607020d0b0a06030309050405010e0f06061c02190c02100c170304060b0103051f090e01020705150103121b0b09011b17010909 75
    0x10b00a614002084003020340d42c1c61810302d00326401a6a8051856200c40c014003443d600404a4040e80b00c11900600611960084000030039980740595441440b0000b012415903031941c0d2501c0015030044414001410450400b000800c0706200c214045500b902000401d4070b040d100309030480343c5042d414040755541c244000c0c81d2281c028030841d401a4240070619103081c0d02c110804440e0001440103070380310b075607050b10304e01106c10380303022020030034152500310060322414199a06030300b40e414801043c030414034012084100000c000115500d0100c100300511040c3c0d00038012294082c0c0341085181c8542120324900d04840202c074940200410040042c003507a9071001005104a00005050103241e5541c5400d11110307031078448007803d0f404011b006001840c0f89000051005003442034010f250b00080a4600c00d0030400079003803840043c000361003aa401c0d004051185000701513281c1c3c0d266200c034054000340179901c1030120a8003100000c41e41d821984908074415410004120403403800440d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 186068723 1250 186067473 186067477
    0x1d0102011509020310151d040b0105040b03070203040905130b161e05090d03110d0e090609070e0a0602030a0f0305040804050904080d06230d1101031505090f0a110403030e06 76
    0x170624240c41000740060b030a101102500700410141e561080c10909503000c080b0504420200144150f10341940080c60380c0e00002103804580c65a0102134407980e0f1440164254003441d0f00016042e400c000030080e5206440b010412254402c3d55540d10b41e490b0b2000d01015030250035a6200420158080554030000d03ca06500c4c203601d03d8605907152201ca00046010070244030002c501003650322041c0d07030707400805100905454810303140000400004100281c400382002d4429800f40e442c042c0132500c240e201d184090400305014104e07000142d905c500c020b549a124400302c100040305400c42d0028030384240039213401a500704003aa8242401d040c01c110b0317041c40181c0100e03088a010844a803014015004120040410000e1041c07506900c8030000c580b841740c040c4003442154450484400030710604500c02000c0d8080c40c1c000758a1120300c020b01c041d0303011074100d282d03c4078540007000750024040301c40500c100348055060002c0100c81500a2041c029400000e0200c0c1c80003c0c100ca0500308040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 186069973 1250 186068723 186068731
    0x170709171b010e280503010e030304051b0f0301140907060e012f0604030c030201061d2701090503031b040b030c090a0f03110906190306050603100c1d01020115090203 73
    0x4941c2d460b075030307942204500c07000b034040c01c0b81407801d204941003001c0c0c46c083c07240201c00d0a40c44091441c42c6050303542c013521162107520091045146240d04207481c0c803461654030303010300050020804854000031103800c80314103c401c0419481010b8000c40c0749403040c03001c01180c1d58103849226500b040d80c18003854265051180d0b200c4554000c002c030b40024800c10400d07002c0c82c001d444040c003854050400901751546500055489030103202d5045c151243c0988071a4000c0003103449202a04440c48020345000c207000e08500c1c25801c0008030780034010040010740c003412510b1000494842c0312030101009000d40d200e4180c1800b000d00000d0b000d00d01c0c2d40010642c0d540010010001035403284903150445c00740e9003003514014080032060880303042142c28550422000c8402c640b001500c0a0645036984850200910846e220004104e00b61002c2058564400314a102840091210314009182c02070b1800045801e06a01d10321150550061049043c02122040c421100c6810040414044c0d44058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 186071223 1250 186069973 186069979
    0x51002120d090615030317060d030f02150a060e0109090305070f050705031203091504050c040c0509150c060106210504020f0406060e01030e01110403030c03170709171b010e 76
    0x2100d000c0016140d118138551400d0b003004a010f03490642c02c0c01491650200306011006103604203129441d540da010303d015280c0e02d464a00312401c0035500480c185082928842c190100600610441c44860b0304060240c03103004c0c5080701c0300d03a13903400303000291010844040c0204800300900c001027401c6080c0c1844417030051003215a426074810120340b40c14008000714000840c0481440a40d04c020b00401140f90082421b80d0194105a150180c540322800c0c04a41b15035560300324008494000e005071200200000d0906c0c80880c0014400d1026600c002c40300c00b018043c00d0000700302140280758007400c038140c6d114a28460b034450264039000781405001641c1c05081d40c05403822994842c090341010340315603550340b035620b40300d08005026150302807803070452a4104030200d114171412605450403240c0610b8551148005800c0030f031780f03085054840c01141103030300080048541d0403e880008444d5592171180c2d16168022545449855807030b1a01740c158000b00d01e28509610039554607150544c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 186072473 1250 186071223 186071231
    0x20a0c030609021809010b010e030a020901090e120d061d0f01030f020105040504090606030b011409040b07050405031e0d0903110f0f0d03031a040915050a060e010915051002120d 78
    0x20300484c5020a100300d40148041e9181c0110454a5a120400c03080e400b03401d600403d00320256034000781003040c0501038010f2040e62124545007002c000c1011452100c01194850740ea0780c0c3c401d56600141c4254080c5c12459006206000c20326540b84001511070031410b20708224a90940e5504107142401ca00280d04201050001140f02e58551040b00a160701c148000900280340d8039104103002c80c141e1121840d000540d10400d00c5460714800303180e1260b480403900b030599941d00700503207a601864212980512628402001410b409000c40305001c106500b1110701040d6800203c031003000750b002c006c00036030242d031854400781405003035070042c498001c00c01c0030701010710008602d03d249100800e03800213803900310800e50b0740f0702840700100014003620140084642521261200c17a00f041e0107003802540e803c001b94a01d14550b0001001d030508410300078180d690744002201078040c00300302c0d404040e8030b0308000406107400d00c0110208000da401910001680303a042d5580d5802c507000c800c00b41030715 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 186073723 1250 186072473 186072499
    0x4060b01171806060619180b1b0c0a0506040506030402011419090510020d11030f070803060301051f0b2a0609160e010e040f0c0609060e01020a0c03060902 68
    0x580040310744a40030403140c45509940954a961503e04042c0c0440d0180c1c2003004a0b40801442e05605410706155060041c43d2070001407408641043d0b940c8141e403001804110f06951510060400150358407020844141845031010421001428070415900c83c404100030403650401038040d65000d03005040a031128007107247d1100d11075003c080e00301038030f01c00b641d0800390b02074100705501c003e450f058411040c0140700d41c501035030300c640781a9100240710f620b00801348040c80400459013488000d20100d034481e101403800603502d170410345c0c0c00c900c69400c240000d004030340d40200c082000350b44401c50042a034a480b030480c00661000120142c1c81035119412491000d00400621500c02804003c044c20300e011007100341025111096490711281945041142e4010800d00506407001d45c41e8660448d2603900d00354495031580c4000414094100c040013030b01a4106010b90111082038850300c11422042c1c00480c1c07a038000703000040425002200078000300300c1c150b202203410741c4007800b500c1d05040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 186074973 1250 186073723 186073757
    0x3020c0109060f06060c02060915190207090605060306210705040204120c050d0819120c020f0709020c30070602070213020324040216031e02030405010804060b01 71
    0x1040716802e80341c007a110112040701014a01c1140010b02d2070b0314001d150ba0404e0f900003122840b8150a4500c101054407400c240602a03030b044030a00703000c034501d4200903191503001940310810b51285540061900d5400140381c00c0950459119440051001d0540704101107403401018030600300c0703c8144690300012803661510710050019010783d000740d9183e469680380820700641d15400060055100307000c0880080c00c1d82081d2400000307074080302440307014100d03001c80c2e802c551025000d075814208a1038024050b0041014228400c64406503048140c036400b5400c01e0744103915001942c2c1d0700c2165601080c010420b4414448600ca1100c8014095003406441d03d40d08a40703806d96055900055103421460302e81071100340c90401440960851400501e9042c0b01c4da8000d49030810b24500206040305650f031a81143c88041c0d5030010a401c0d0001030a000b170100b078031026510200300c00754008515031400002078604940c01659101050781e41d5a41c0d82c00500140803400d03061004003040c041c401d034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 186076223 1250 186074973 186074981
    0xa030315050d08030a0c0c151a0402070f0c06140a080907030507240903020105040608040f020418060b060301051c0c0801063209280207050109030206010f0602030d05040303020c01 79
    0x2070243c41d40d182c49003005151001103c2415009005200711110500e002464140d0300e1540155000310002e21210100b45403114030b2405912158041e100007125020400b11302c100c5490a802040740740304903a00d0b620300381c1d45904d2030a105041980c05110150b8118440e000c2e5030340c81100c40064030b002c0c0c1e941c1d036902854461107030041da032100d445c2c0b14007080c4507001b5111030f41140c03201c1c9425a00b65244ae0000380c010711030b9002c0d003420050420005401c1c04450041070714aa80d0141007040942426401c105034000b0901c0203c1c1c4041c00c0c03940c06041842e008065a050300c5000780040588112040c1811800900030f000310341e0030f4900e40f1b00142155080c801e0000400c0c03200d20000c4100c94001102c90070780102d0030780c4000c5421840c009180e07901c030b1480565200c1c20746c00091103034202c000c410610310b0000440500c40c0b1800043c84404006064101e0100d480c482e80846400381d03203580800009000c02e0040e034006900900c00382d014104190091354104e4001c3c14010324203001c599400d400d40b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 186077473 1250 186076223 186076249
    0x140420060c01110703020d081306020c0a0212210f03180f0a0308060109080115260703061410060c0303090809100c1b0f260304060c1704080a03031505 66
    0x40c10100b84d00042c19010711120b80c1d5108075241080706460803001c0c4000f401002c42001c0d0119070b0120396009800b000700000a080f03a00244a0240e1440000c0401c2d9550f05428000c4084035840080c1006085e84105903000c0400c000d0301c49095681f000400f1a45069009003042079104d00700c43d020070001f05010b00d01400d8000c1d82ca01c606c40c0b50610000d8503a48040d0f00148843c0e151a4114100c06c5000d2442d000340c1c0e519801c801e2008642c106400040403100494022170b00552a00008022182d880010054082001591159903114051000d05854444c040210350150078120000f4030030751000e181184510406030a0801e240d010403c1c0f2a00280d40b038003c00d000b0548102484a100681c440030006034029450840c200b00f00c03001180400d01c07a0040c0b5180c03900c0c0180c400110346840030802070481b81160345484c1e130303408020041d4005c60415202480200c03441610b14883c0c00c02c590a9580c4807005110707140c21954110000c00c4a100c26400c50705c3c4140c4045520790b2040390503260 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 186078723 1250 186077473 186077501
    0x304050c060f07061a03030d0b060c01020a0306150f140304080403060504080703120e1f0e0f061602010209010c08090301140115020105150a1701020c010519140420060c01 75
    0x44088601c0c01e40c04a8509081c05501c00c0030300717580500240d40001c101c0d0020f8861000c085118514880414002e028032203000449500206a40c1d215035030590101d42241c805010f044000a0811015a040d160000081000801c82d07810740034541d401070010768000348501d00c046d10f415a40d4880c2c0302240d500380c500f05c5031008002442814142d002c43d07401c81c40d820f440c00400582c1c0c03900840d04d5444112a990322044d020070701c00000302c108141d1101000c4108030048d1028014868001a01c0303c400310b607a424004020800c0c032801902c14800d4400704401078440d20108521512030b081c241d0000c0c0030880d03056488000c0c1c011041e0032245054000c040b22002c00f464016018000303400d4030300041072000000030303007240c1c02c032103903900000c80c4c040700d0004e0a6010040c540c2030410380a885111002c40c210360900003440604480c2142d844031400c81c190f0f0400074003402d000c120064600686015025904000c4590700300245407484000e034810003052240f801e545800f8660944244c1d100f8020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 186079973 1250 186078723 186078727
    0xf0807180e0403030c17150f03010603050705010f18050603090a1505071103070c0e0606121e07020f061f09150306110708163f030c050f0304050c060f 66
    0x105034160180c0da6070105d041c00c04035070350b1104c2c11603034644d214018600c00118185c001800d034140c4507101c914101d084094020b000c0103450341421903459103144a8207000036601c95070125040d210314225210b00002d0400404020b2516007040000e80000e0002d4109018550044000480d0807060421510710400007041c1e928060b0b078040c18008643c1c0341e92030a074000b08080c4c00007840c2040c818003641c9812502c0d8030152601d40200c1e0b840d00500701c214100c2c10381c8400b0305c8a1814030741540d408840c0704001c1c1c0581c654413200102d0321500740c10540780d52a8421404240c42030000712340010401d00d112052071550307a85500c002d09230745450900d200d915005040500a11a050003600c050221500e051031400342280d4039811a407242c400071100d0307026244110010049489490840c4081103880055004012000b0310008080807000104e40c1c0c1c401000102001c1c0130f40a000680d1416480d1203040c40b0846284422542c40107000311414002c0b042c00300c486689000240c0750300380e41c0070031003a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 186081223 1250 186079973 186079981
    0x305040c0803070b07020c04113117010f061d060301020c030d0b0f1008070305100b070605060901140325050d0813050603040f06020d0e030a0309020103050f04030f0807180e 76
    0x10f0f0508012203e0203016505003c0114127029240084910100e1254131200f074a0b5480709060003150100d03041c00103942d51040c000602d484d00888030340d10b10140c030380080101050004410007140c51611440c0b441000b440400242020802d02c000e90010028001510b010240c0900608540c05009001402c1c4c1d500c5003452880d01740b4140b00005108242d86000e40310038804009084074600500220400d80c9440020b0041d80c15075120100400e02c0841c03154840c10700d4548200500001c40310745010708100400042d00c200c0740104800014009070107040102025100a00d01200b00350400c08680d081140024941c0c03541c071b00c0f00804900540c12503441c1c030088400900d102c0d070a03034070080c416132003030003800301080f510020101c0072588050010380c1da00b290081034001d0b00703018450348c001c1e01011038003480c02c9405411520800d4404d076070801c800d644018070000740800c00e94000e000540075980300c081d8180200c821581100741c03400c01011941304150750f8065004240c01c44051192454284 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 186082473 1250 186081223 186081227
    0xf0405070e0a0f0f0e071403040f0611030624031302040b0306090601050a08070f05061b06240d080706050414060915010b07021f210501080f0303090309010305040c0803070b07 77
    0x81303030150141140003100d5040c0030800400790802d2101001000e0383c0000498100580e80104407150b0350f029109020030001d01c448004943c00803140c441c0640d500f8914600c8401c119500a840561440c00450840d21404803100b4817034130056049820964880194501da5000c1100d540f1035a800001400c103581002d05109500d51554482102c81d4030041051021120704a81002900d4050700d240f0b854010301d4110f0016802c83d2118051036010301c9090008440120865000807005404005003044007a002d02c5801400e00c000a0300300c0034140f081000041d2039401540d045070007485035041410703000004d03500341360054a00c0b10f1160f1140c0741000325042074035901c40c01010003500345c0d03080c0a5903030080303510140540701c010342c0d2020319000b0b5040a806040d80800c401005180985040036206200d802468203000782c0d00f09129030289400c0081d0300008036481200c0307400285041110309001034002d401d010340201c845148042010891040410240043e280071b40c801070801c2c1002040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 186083723 1250 186082473 186082499
    0x11010309060e0f2b080601051b01051503120706020c0304030c120308060406060c020d05030f130f080109030504092c01020307090f050a180209151201050f0f0405070e0a0f 75
    0x15903038042c0c681ca81c22105202d5514000300400c04d60501012503500e000c0102d9461190f2429a4007a904480040780005015423003280714030603200600607021500c1c010180c0d1001054480301101c0300402c1a03100044181c3c015104000c4c90804881c1419126601c404c20080c694002c0050017400042071014503922050064100b181a0b404010050078032500078884804000040d001e108022100c1040107001c004031403900307040c03031500c0d40c07141c80c16081c1c210b15000c0d92140481e80c600d1040081401c20b010710645e00000d5140d1100d034501450030b491103001d0401c20390f00031410444440e00c4c0b2030400c80c2c15444004d190015000690b20302d00418040c0030382e030054010a00c00154007a06100c2600c4071040d000a503813a003c0b24400260031200c2520180c440c085846402000c046080a55420054040c03c6d550030b4a4104403090ba8a810600a44030340c040780b02540400c9092801015041039808103801c42d0b0b040c6800c3c83c0b051070399004125108020740c071801e0b410764190820480c29110f07603a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 186084973 1250 186083723 186083743
    0x432040b01050f09041101020a02031204051e03070618030b0109140a0509031b0c120105040320030403080c0115030804050111010218010305061201060609230306010311010309060e0f 80
    0x3d002c001c041982004103200b0000100004c24910022292840703982c020040b46424507402070896103040c030b03107690b0231080360064410b48e40614621041080c401300c90224440303203e203000e4000c1015a2510404950a01800b401c405071184403810120100b8082c015641c040c212601001c941d4541c001e62800c01890010000d400c0c0603e403005102d00010003004688504401d480c0640094034042844d03070410150300d02c030a80c08902e2030384401c1800c02c1900414411802610745a80340030300f80782048104036205407100410340040005200041a04001d805040100ca0000074405500c2c46248400b4801c0d40090700c8000b8003060400c400d42c2e00c10011510b01b01158000c0d800c101c05007503040e40824a24959506050303c072030010700507072544c414144401c4100002840440d0b566180501804501c1c05940c2c1290030301c0c3c0e1100d160114100343d580360b0100141c01050240c3c078549500f8603900040c82010704040e1100f51060200e0800c2c0961340c0302c084034001610503605c029040c1d91074924048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 186086223 1250 186084973 186084979
    0x70c0f0c06091505070b04200a03060e0601080d020c01120b0306190e07030b010e060111060a0501080715051902030c031308072405090d060e0a150204080304050432040b0105 76
    0x80b840068803503008250016408220288030320041104081070082240c80c22790849003010002051111541003581c901400714241c44450f40c032031103010f86406540c0728550159104420059195109083d420b01c403034000b24000034060380180001e41401e000380c40002c0b10851025280c0d40702c0e00c1c981320344900da10308a40107100881c559982d14140c0c03403051003803030ba00203050800180e1990203402c000030410028070982e00c451030064240070007000c0c20f02070303e1158407a188022a069460001214038004551102810100c100c440b5180b4041a900d900c011800b0500004003295801c02c0030f81007103c1d800d100c0c1e84c80d0f03605180c0c501b07140400d16489807903445094208034402260f005500e14810b48549441075480100b2000710ba505006420003d249924014807081c0c218008201042c03c24400c2c242105082c480c201782d03a09038081d5002d486110b41040200f001545440e51100c010650394003005080c0010b00741e5415100301981c29001000005c81e07013040f0030030404280d8140034000c11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 186087473 1250 186086223 186086227
    0x6060a06030902131103010305160612020309010605190810020a1b081c06030201110c0603180a080a030e1002040e0402130219030c0210060509070c0f0c06091505 71
    0x504140058440c5506155503040c0d65025511014528130501602070010301146040c0156080c040d0b00c2448162071b28055005403260000310502d88038100d800310340d6400260000000100e009600c09000000c0b10340d42c0d034070000707040d0f1903048480b10010502d6500d07540440c0380c800c44900700440196008201071041103582d003440c0d041130300b14000a500c280100a1801c16143c4000b10b407240d035440310300c04d8100204550b540e071516080340081e603200781e0300d2111942401c03038030b1b81d82c40003001500b55110b0340a00c001388640c80f40e403403000c04821440301100c2242074103031140700080c1c2c8207000401c0040d841d502200035400c000c0114a00e5009059400c5191516040c0c982046007000f40000384201d6118003400c14102094058035015030309074102c0c03810301c6101c40d030180044c0a00d001c02c4016014031400640314075214881c510448030080e200c1038140d560340c1c5e001c480d402c020304002c5941d55040c1c00088003199603c039a84002d8911501d983c0c14040c00c25000c05102c5204107120b40c00c1280c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 186088723 1250 186087473 186087481
    0x5040506070c1b1e050d02012703060509030c01050606030c0301140a2102030706030e0604170f1b06160f030f0b03010207080414040b01020d080c090a06020c0a0806 72
    0x211154000344516021041aa081c64040d0460f6900d840060414a0000010038030b5640303100b242c1d40580250030b4a50141d90755000b40001086461400790200c1c140320244800d000c50134408240f820482407030707028420384980c5c40c6e42c222881690b5440e400d0744003042000c08040c003481400c3e008071040b00c6007801c41c640506c81c0e844134401402808069403602410306116100d11080c200a8004482103444455110b0010440c070030041e1801e9100707200303180d80060304038002e01c11810f9850b50300010708216541c6441d000d01030b002040340345c0404e000820203031500320694030280080d02c0310301200064103500296464500b500183c0030341c00c030746040100200242c0d0050411111404141804110703028080c807558010700401c0d000a03050f500011f244070130050890001c005842121680c00026900c1c40c0921080756001c0c0d221501580c41501c86180c6c039801141076652001c00700c40c14918040b105008560400c84590050002d81e1142d81805c482e1300d4428400005812400d0042201e860 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 186089973 1250 186088723 186088733
    0x2615031006030f0b151e1809100b1e04020f0f0f03011502030f070308040c0807090b0a21020d0c0306140106120b150706021e03060111060f0a0f020c10020316030504 72
    0x50f210020301e080a800c1c1402044a40f5040140c07445140e80c947d401c0c0c0c0074034015013a152201d0f24225078100f5a85818084101490001c445100d0060403000c4c155200191006200003588000700c0902086810b02038001036528280052041848011202e44ca0394501070015009550301002c060030f542040c08407002c4c4034802815508602e07054a402c80040d25075040075220003d00f60013004141c02102e0b00400d01490981001c52401020343c0d00c81a1180d54504e0f242c0031031408022000c58944001691001d071a021901461240c000c02d80070300082d60742e035941400c8803488010740c084641101d00400040b600000350017000a101e00061044030a15030009a4601e01110f80c03468110300031411500740050b603811b131610005038140b500c080f00c2c00c43c2900320464104503a01380c001440d003280c0b001220400b140503409940b440e142c00e942074940c02e0010014050001075120308035800c0c031000120741020001c410790004108401603aa04202c3d107940c04034005546202c062500303017014800024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 186091223 1250 186089973 186089989
    0x6070503010315050a0b03010507030209191d0702031b0d0e0402070209041401021c0b0a080304030804060804111008061c1523010b04062615031006030f0b15 69
    0x240740c15070001185d80d100040d01c8020b04ca1001e0090301580780100b003100880c0c0540c020100039004580d08200c0004081c4e8102003a50907004a5514004c0101d2020a01507598102ea4000700f050050706d041030151048008440741101001d800341d80012080c401c2150424440f4442d84802d036130543c43c007403141d0003042c400348001d40300410a08200c00054a40c040a505640b022806c075034049c0706620b0502000300207041000345052150200c0c45000a034004c9c0041183c040300ea111814a051a203042c07420b841d4120014000e0720720b0032092000803074603900c8100107401c1a011751131b000740d9801d008003404880c1404644120070710f00721640399004a5404011980300042d018808a980c022003071000b00e003c1b80256102c14415596000403641907508070181007520480da03581c401c036208216448890b8449503501403880700c0301101189401c91100b8602410141c0036085840900c4403540b1503085902c146e109846010078000c08008004034a110250032010115240b804500303101c001403000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 186092473 1250 186091223 186091253
    0x50702100804030917030403020906030d0801060c0317010b030a0506061c0f02040b0c0d0201050f010509060d05070f0902040314071a0c1603030c03020c030d05030a020703032705060705030103 84
    0x101c0041c10015003054483c100702005842203092554001680072109950b0307070082d020880c801c426100000d4854140003407800c1c42c9006990380d080040e460300c0020386074900406810340801c12a030b4461600d5a860032035490091040b118100e03641c0c50302d0100101160030250009114140030000301c400860803002d1914200d00b407540c0091413034143c0e01d4410080c403d503030248001c0d43c1c000c110000b0008c001f05030006021041d4000380001d680315030202ca4550000d024903a44a6051004521241021007001c1441480b07002140c540b01e4981c0c005a1401025034490811540c00140034410841000100270311070045400400e08141840004031076200811106401000c001c00c0110a0b00d0080101541d0541003042c203480c0d840d26402c4c001d020301c00015040d40036100b01c03030781c2e00d0345820000340b13550841c140340e0f4420b41503880c2c1400020207036102050903020940c82c0c0c00d0b0740e2405000c18040da22841c1880b0501d100d00012450403d0400d21300614840c140401131004102003214a0fa0205030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 186093723 1250 186092473 186092477
    0x2030d09080618010204080d0305160c0b0c0304030c020a1e0f180b031002031009050f2401020a1e050111030108070b07060603051506030f010218090405190804090c05070210 76
    0x408515180c40f0340c0240a5980240ca079485000c0081d40000e4040e404980100e043c080f909410350340c0350405481c10741807007400812901105000540d100480805103030031a00c2890304061511041d000940e01440c9500240c2e040034002c0303441d504003022440390380020410f10014032082403034814008802c1c000c00c0c0880240343e0711071191004658050040341c105000101d003c64403402c051024800300072450207903000c100d1902d800324045800c514450b80c49203030305c5011587c05208003a019520041d0340700f0780b181548a0403240f100020071038059a0702c45003413158a40300c4606a81405405d427500750b850302c4c0040030301b0801030011640103c0c404c401d80d812403005544e642d159140c464000d200f40d83c00030300306020341c0c00c51542030b40d000722070700d405448110100c0e80001d16180b0214200d129101c200c02d4001100c05a4014605080203001ea0141c096000e1b25100f8085c4107a40410030003003c000c40320410006828010300402e8410b1803464451490326070701304107a503400714034008a5045c003002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 186094973 1250 186093723 186093751
    0x13020604050409050f0601030303020904050c0c0d200703030816050903150421020102090316060e0d08070812100801110306010c050708010e0307060f0c050403141203100302030d090806 81
    0x105000c0104000c3c0907420f030790340032a19190b0b13590030014003d40003302c46601c03030750800c8086202008070f0300507a17810314008070180c040e40701d040005540c996021040681d607400710040d0354074074000c20f0000744000e60081e11400300c13515120240e180d8451582d0300342814000305000008090f1000911444036042a02c0013024540740c5040c6107088268114000e2200740703002502d40d460603819006080b0002c0700350129890901d0200042201020381d000c0d01001600052201904d03241005500c81014020001d891500d025070312420b2ba140d004c00c480130545a40034043c010000138000b88100100300340c80013007001c822000903182083c44040c244504001c01d20440000b8403400b40400402407107d03a0080002400c0b2010207916500841001d4910710302d041c6114000c9100c0c0d0061000348401a03031030300c0c50603003180e44071034401105441d1040a4464408000070100c1a400118040c03801c501d142c0315410301d5441010320308410001c883c410010360b500100000a070002d00310360013080c50030b40e000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 186096223 1250 186094973 186094991
    0xb07080a090816090c3f02070c121502030103030e010206060103200d0f060f0e01090e06060103020a021e07060f0e03030306010c0507120602030a05010504090b0f150a090207120503160513240305130206040504 91
    0x2201c0d05074082f82c0185903100100010405411060079a000d010a03000e56000750f0f503040054048401e0704c0c190481c400301200c8540450700c0c0141c010f01d0301c0d0028090004041940c83e0200342140d10079045044803540f030310b10a012848002454900601c1d4550040c0304509003040340c103440b40c501803c020705064001c0b80f1403404c60f0090081c6901020728a80070000c11010030f03626541c40b02c6038440c00300440d0007100000c0e242d40c0704d502c0c0821103c4000e0019881d5445480045801c0c1c8003008050b501401482c50100e0403030461052041c119008bd080980c0702e0404030491411520180e00540c0700c0c1c3d2400c401e81002406980e45268090f05d801407018480e507480c500c107000b00d0314208c005980700c44c1024003c5005803495010380f23052800b40e103010075403100500c130940b01440b080d5205058030098803420034226204d000207080d005d8150754035400c040d82c0d6055840300c0050411030340c43c088140c8450303a0b4000e035140c0b14103588200500b140080403200341e00460018412030050078011b6403110119 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 186097473 1250 186096223 186096233
    0x3050604020f03070801050f0609150c010e0f0609070609180e2107060506090606030c030406020d020403050d030c23130b07080a090816090c3f02070c12 67
    0x52002c0070200c0c0a031030754030700c0c100500030042d120034010907125454401c11708981d4146002514500071000d04a0000010300e01413801e010741010700108915904e4603858100083d0a10543c1c4140322008001c200c0ca040c000e07046802c0082d03d8001c036042048044040120303107048200b800c12222120b00010312450078080044c02e20300c8940100000240c2c001d078914001e03403030400800510340604c81c10880c64a0b40c1c810400c40c004169001b50748030f1418030200e68101410f038020344d04144035040062501001c44482810ba0300300354030603181d640249001c11442c580501a01502303c59620700000700c0180d1202c40200e1034030400800311440710110345000328104141c100c070b001c0c2c582d00003820703120035191030700f52090303840841c0040018464100000c2c294a000501c1100c44c4980c910805c47e05040502c000000c7c510f850f0a4420050550000c10540003407841c164503c0b07840084160784a003141c1012800e400000004002d240d20410080002c5155100c207071307003a0b81d5064080400c4010728204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 186098723 1250 186097473 186097477
    0xf0f0405070302060307090302040e0c09010513020405040615030c0305190c030b0d0624080a02010e030a38010f0509070207031506050906030313031e05100c030b100c030305060402 79
    0xb00a40001000040c45289900010128100e0f4400c1b1350600010a0340d08035591102040300d90f254011080340014829850301c3c0d0b540c450900c450711001410103680304001015950154003041445801d000c0d04038039150705014903e212922800c06002d5801d00501100300d000d08540050b1546688204100e6003501c20703003042c10b003104001c141e40b50f410164101302000340000d07803240300002540070f000305031084030314481c0d030840300594050411000190010760705080c1c100c000507498020301d220880010901c1c8800300c1c4590404194000c2400300d0f484040d40820302c4004102a080c03031800400c04101e60320420303c02d9500541c0c0103440ca44448005034909110b50300000c108401040709150042c0342a408101100e0003141c1d1078a03a9205c200501d9243c1c89184400800d449400d101440030800d00350b540b64115006600c2c24140d8516a260203061109400000e00307825150742010392002e038180100709041d030b81142d2184520700c822001420055039014014203061319000054044da4407541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 186099973 1250 186098723 186098729
    0xa0311130515040c090b1c0209030114060405130b061306050307181112040f0212010212011d010b0304060e07050d05010c200d1d06161a0f0f040507 65
    0x3030501040c01d12079090500c959221601c03078080c500e0140b5071180c0900c180c100070201c9268011081c60071222050103041c07100900341460034640c00300300c80d49450f2424030646403080d011072800e2490742440d01c1000241c40c005400032640e0411202071030f0100da100c3c20104d810032070071122100300b8100a03030407401404513540325990500564800040c852034901380111003603100d68040000903184ea0891929000e032100f60091032140800207400101e07403401050842d8001040c070209544c4500310700f030a9070301024807112100c4990004010281000b40c9400c40e88100c10780c80b06440d8180003801003c0e000081001c0d2205899200180980d041801a50301a08001e4007001220040d4200135020740140d050320800039440030380b04480c3d015040c06120744114410302416026240362022a012007000d040400c805628100d03000d625510940101040784520903030040a0002d810030104480c0c9885800d055200c600017000100c0d0101d031100765001403640180074103521942003d0b40340903c150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 186101223 1250 186099973 186100009
    0xf020306040503030a0507090f030609050106090c050c070504060302150d11070c0612090201120f0605090a060509010b03060102100e10090503040807170604081b030d090308090a020a0311 82
    0x50501c41403040200003144594100003003402551514003003200c5802d41842468200b00010409100080c1241c000360790b1940150004110142c407056140c2c21100280070007c041280040c0200d030718602032003000000c001c11101000107a1541d004260741e210019940500c0900000381d1194840c0a903101e03045246a01c190b217600c8441d03903e080340610708240903c1005c140020a0240a09030b14025105407c2d810303512040140500512440644a904002e94400d81ca400c4007003856161005003d114000c82d0001094181c90030080c0851000e040e00720340c6c801201001040402d9030001001d6040302d6605030002051054480300b00d04200841d051400110b0070140000c3c00e101c3c0c0040604142c0306600107461009a445426010b01c00c000204c408503034000381700042c041680f43e805001030801034030140d0010f003400301d0b0f80c0d0f0855220080400000f592410644107240d0b0014205502070a948000c20908080d80c0000c0c4051496102c0240003501803074010003552591100c08141c0b410701 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 186102473 1250 186101223 186101233
    0x10020307020307020a091803050a02190f03030b10090b0304110402030403090306111e2503020601080d11150a110403141903091e1a07020f031209010c0f0203 69
    0x594009490f940300d5a0103a20503019800007041880c25132290456500341d18030524245d82d203e5609491350307080078403201c0c258007840300e40d101a210382d449080c1050744560220340c0c0e8541c80346005403c4454145119011f9014041660f0a2075040090390b4140c43e2408801e90310380e40c807072034100c01e818980358510f5009800401480105a00b22030b0305010b4a2241005208141c40403141047c24000c4002400344116101800c20040c034001c8000d000c0140b00c00e465407400305d07070310303030310b80c05010824a084005030f0002004100700c2c03005011182c2284171078585290003015001e1819501c14000310070020001c8050701080100301316900c102841100325850302d45441e81c1c1d013450b9161000903003030800b80d0b0040c540c000c40e40c548041010709106d54140c03200c0100c2405c00c507128514008282400d000d80400e50340100d00a00c8031100c1d0ba2061402c503040c0d0350350700380c1d600c140020780e04840f881034001c6d4410381c12800101b4440064071507205081c6006c400c00809030a005040300710090005c1d405020b5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 186103723 1250 186102473 186102481
    0x50f090a03060f0e0d020c0f040b0d170a02011b050a0f090306150609050328140303250311030105130b04050903030f09060402100f0c0b2a07020f06070203100203 71
    0x1c0ea0401410044a42c0c213131120445040816030b107d0b80e003d56215408030304422408124641a03104801502e8098201d00400c106036598a0212a0003075441e00c0b1039502084041c2055424040c0300301c1c0c1364091510780c034a1004d194010303186008055101e000d00c491030003a1080c00740314020070740085401c03010601c01c04000300710000b021a05c0d801801c002824400010803641000102031623403440c2c580844030000107400e0280c8800d160104211082c0d8040020301a90340d1041001e0740c000c012040c507450300e80c0d002c13101f03007113001d00c0710004c91060504040c2100d50b01c0c9007030020b0741d0464030b003550340c035106150511707058009140200c40c181e0300502d040140a141c620001c05148104820b40c1c0000090300c07964151503440c2c0c811603000754005200c071440400d0510504100b4419541070802c0a1429006d540305a13541000300c40302502c0c0c0f4040b0010300001d041c25031f0009244003526508526010f282c0e0080b4240402200c24540a46400503490045403000c0090001321078807402d0454903428 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 186104973 1250 186103723 186103751
    0x106030504060e2a0a0b03060919110d0b031609020d18080c190b0c300712060602070b0f090307320303070204150812030117030307050f090a0306 64
    0x322006082d203800e44c08940000070303081090640c03068420050205003180d0700c190401952810081c51541000b400381120f100c668a140629540e1004243c0c0f116184e46401281508488040000074440c0d03000756117103d19405090404026a107141c0e05c090ba40d41411a03110014107804c02c0c80c205a02c036564010014070003481c000d080700e0600e18066030005e5840c100015462030803010050030600c50178020036240c1c1004c1d0005c0040460300400d080d502ea410460305004181045071000c0b00300300d40010060308950003064030700f4414110030304000326824040020342d10700042c01198040800000e104020640711026a0502640141101c0031552034190200342c0c0c18248558180082984010700c4031940303011b03100242040060011410b00e100d036008c1001070170f401300388900342c507921210120300c8100510403a5401c1c0006a101d41d0b070b9500d0641c1042d1000c1c0030928800c416001417061046490b4002c0403529140d060000142c1c030f6040b50340008590079400d92004281e07625045c50204030b45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 186106223 1250 186104973 186105013
    0x60a15020a0b09060c040b0306190b070b0a0e0a1712090708010f02160b100b3004030903081e0a0f030b030607090611100c05090a120b0106030504060e 66
    0x91207000b0908443d01c0d2418429a103002c00d440045401000317100c144044805180030b543d0000340141010509412400d100b1907000e0142c00490003490001210300074800c500071541d070018040d100810803150414012502e942c40c1c04002080e0340020161040109240000c0da40080101c200c07800290608028142d9244224400c03440e643d42440120082c0800d00e1007071f41c48900c01070701c7d0102030560703503500d048000b1402014a1406040c8090104070710a805001e4450f614841d404e01c55610340300307a40904054240c18040c0080040d030303010880042e90001d03407041100c0c0e00203111038840900e0086100d414400c0e600d600d820754404034122550a41c850281011032085442c100070424056080c5902c900044030f20b000450340f80700080103001c0c420806c14042c000550143c690315441d07488000c05882d00f49004000060003c250b80c055031800700d00c0340000b464096031911101d011696400d0807400c0500c600f00a0503038400008040c050a9001030031102588426109000f0395221b400ba044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 186107473 1250 186106223 186106243
    0x90305210f0c0301030218130f08130b09030a02150d05070306060e040c020715020c04110901200a06020a0c0b09060103120212031302010e0306010608010312080f040b060a1502 77
    0x112a81c0e0003207600c01d40c040003100d040c2d03034018207048074075002200320103074160380a4005c020050708880d180d0701241a08201100715445440c03600e58907800c070072a448460f515600051080001080411407942e0002010700a0a034103440006442d0380c0501000864040c8941c0501d0301d40c100000c2200c420307410703030241c6d0941d00c003611455044840c18003403004071000000c50a0140c2e11010060200c00c880121344584003140c0e1040703905035040c0b0303400704050f581c4c1004910300c50320001c140c07400550b811a03c801083c120044022034414068002c49941d039082d0b5001520003580010700740d00440c0300e44410f0030810b03040002d801d0503080c4140e0700307651800248000c1d140b40e030001400817a224808612480e40c00c00002501d81103884007440441003501c00d18049044c0700c06605911955107083c0010f5008101607180c240300d640c90750802d00ca860401c100c2c0031003002071070010040c0b042008a43e994005030040300010175a41e40f000400c80c5c1c0c18030f07500050b842e034400d906944881c039030000e10750400e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 186108723 1250 186107473 186107491
    0x3010602011107030e0d050c0d063201030609081e07110f0a03020f03011b050a030b0d0b012903011202030f010b0d020108090705090c0405030c010e0f0409030521 71
    0x4480741082120310b074010440c005000610303a0b4441c110514110f0704440b8004d01a20585018003801700c00540095441c40782110703001d44885950b54221005e918080c101101c0030380100048000c860340e1b108000d014080285119503400142d4140802c2806490110305103121002a20b081401e4001058101c00400ca07040c0509000c50407175030412560855440301c01500e0070303112a003150300308520380000310301142d0035640e11103100c0425501400064920742150701c840383e03920740d412402000c0d22204c82905004038000951000069a20502641160312015000450080c1000c6c1c881d900c5070b07001c01c8070081000200c008200107403080150100d50b4401c404641444000107607040c00c1e1130b4808605540a040d00c400b01c0b004d540141619940b212078401a00e0300103440b0000560a15004c0d10101e80e000000304e418449410100110300c2c6060b82402c080c400e88442200080101d64840122030140303441c6c10140d42014091070030341c1c800d9042020000980c005007010300320800021244024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 186109973 1250 186108723 186108731
    0xc150103050606040603020303191103070f0212070b03060f041409012408030409020919030302070f170a02040f1e051e1e0402270106030b031f0c020a170301060201 72
    0x1103e403030548616002c13203501401440c242080e0015a0000003440013a40c020301c045544080c41c0c4520510051410343d20070f803115000022280188150403403081450101548103a0341803218440d600305407940480c048440644c00c10065010602404401460300e1200e00800140003040e00190042c104c800080c800c0c2072005042c290040801d41040e1041c6800c6400c100428403620482d41c00074280d1800240c800e01c80025501910041c8072020b030b200b5401600301e100705011504030b005680c070081807410b100c92000880907444a480320682800284203542e2030307002100340400c0d90800c092508401440001c60001062154041c00c0210f60101c188004260003110b5000d048146a0241509094107842c0c00881442280900c3c0061f105990201c000c0000b02d0050b0082c10b104c0003440ba00240d9100726500d4500c006d07041d40c800740c90092080d0415800201c00a40580d0300c19a48070100001040c0c0c07211420003a4100300030520003030300000c0c82c140080ba404001e040114121a00c0b0340c0208 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 186111223 1250 186109973 186109981
    0x801051005122a04032f0a031505150f090415060801020706240e0406090c03120314150d06020408030a11071202090c09040605040e0106090506100c080f0c1501030506 73
    0x1240c3e520841c04002d00a60305002640c035102d02e13003821164261044110b55840f41101e400144800400c1d600c2241c09442403140745498020a020322a040540b80e25111001c46602000a840300601c07800f4074010004d40c00014184840c2c0101000c1c00c000004040101941301c4407060701039400014252140340c1811604282c1031969225002201020740800e450b0ba0701b40709411461880240058408070303200d134224808038040c84640ca00451151100942149142102805031107000307444c1c0e804080701c2010000001080c20840400500c22507083e440ca0100b841d0043c02030241d03402504e100e110104002c40d8058000c00746040e00340d021001c54088994543c0c0d00b00c020710607460002d402c000d10102080f1006080303806419880c0d4010404a40346171150081000c481156003402ca103a034403160200054000c81c440c00c0e420a005454100c00090358001c09440500340d244020002c000000f5001c280366110f40a4400c0301902c00103881090183c00e000001001c020301095a1501514002c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 186112473 1250 186111223 186111301
    0x3020c100e1c170315060301060807030506030c01050a03110c0703080702120118061d0a080405040c020c0306070503040c210309050f01120b04060306050c0a0207060f080105100512 79
    0x2603482c0d984202d04491044000b60a9841c0307400c05410030b40400301c03401d2041c00503512003015502900c06992034400c1440d001c038000301a144094403040c020740045081c8552664806c0071282155a036080c0401c62204503141c0d040c60344107805100c1d05034010f0000100401c462000100031540c000ca0300b4083c0030786ca0449050813103019640000142444038034000c0003641a4204030600c4504298001c890300c01da03640c403401c01031250b2040307a4090780060300340813a01d894441ca03000041c0354401891244161000303c0e6960801a0814092000200c0020304024030405020040d1000d0741180e0040141104841c169008601c0110085041404007042608000c116002c6103a07050303403401072240c25a5061801403404036180c5400507112a00800800e41074000e643c003c1400d406915030318101180000d00700303003060300820100454142a0308000c0e5000002d1819224104e48111410112003c15507280c440c8100200508500004003d40642d0801c010700351500e4800140d0301d0380c0010000c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 186113723 1250 186112473 186112519
    0x2040c02160302240a02011d070506090f0609030f03030910110702040509011d0a0210030b2107150807030b01140409021c021209120301051c03020c100e 67
    0x5901c14000000c10009450040903c1100010b41c0d14160148415242c040065500c8840d584015030f44642c9490024400c049104400040c2c510180c481d0740e0510000490f00c1c880c5040e07071031141e400c04840102594640c402c960414400504841001504089190b02c03600102e542140301d005404085084010300c0c0103c06c00d0351035800302245072052541c00c0000600000d464101c02d99600d003c0364079411150041280b90411002c02804c2c1980c0ca84100460440f03281000c41c10181807002813240e503100c030414450b84030100b04079603508604c411041342c42d02c0a56407004c00284440c540030460799801210150050701d4179a02809501c441c03800545910b400200c03003001300c000c100000c00110040b540508900403a00c0c1206001070410301c440c030146e0b040745a004140c1c00811041c0f1160040c1000400090201e07005603605562400c0001840000ca00500d101461044074148040503c01c0c05200076103040200113540304040b6050041c0010281c443c200d01458226151002028007610 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 186114973 1250 186113723 186113743
    0x9280b06030a032f071e0b0a020706050d02091011060f01081b030a05121911030d020d0b040f060f05030105090304150207030812370515060301030f02040c02 69
    0x102c001482000e04102d00700780d001e8141c41d4107100b18100c41c008a40300103100001c006e040000302c0c082c0d00e46079184030300f102d14919030040d20200020003020b141d03103801251034012281242055511061100500c401a118880340c9550201035101450022504403002c0c4601015010880340c880d40d44500207400c2c10000c0c090480c84d80d02c900180d0020214207400408400c5014060f00c000c80110b87e100740c40c2240080107498441001300c1e000b0340c0600ca001d006c074040d40c5d0600d030007259480c035803001d641c40340704114140343c1660700015814841d00540c0c2042d4519040600f04024800045202000405160060301c241580030080000c0c82c2c9414005c0c18054001070000d5881c1a141051407401c0010064010080d40079280d00040881c120344060410341c3c12102010302541340040c0d4209050310300803102c03810704885a0304c17411820100c001d40034160005000024480e15000000c510080f02c0101d0703030761300c903100000101c00c200c066900b580701c0034400d640500c140d40c807090b000c0e40c80b828080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 186116223 1250 186114973 186114977
    0x7150914030a080c030d0f0906050f070903060c140c011d0102120a02030714070605010501020c0a030305120907092d05010b0f2506050601090b0a020d0809280b06030a03 74
    0x5020004190030100904c00d5504403011289001c2d883c400801c00d80340c125182918280c0da540a80042c48001e009895003c07000b10034610071032030f103050080e0010455001c00b0745840c1c2e82ea8980e0413554001e412900227030700301340d21890700d038550b018005001c2c10030401c20640c2454640080320f9001c0050081d075112100a6082018558908505000942008000e242004110948451a461100014085079005940205282d0b04040001e0301d01034020b5881401010100b030200003180d480800d840e4035198003d10018540c495402561900c001600f018644030300c1e095400e1800c4103820314802c01100c01c2c801c1d10a480000700c1942084403401d104400b05108104100803d40500b00020a01035805071040300d00070300c0c111020054618401400c480f8a90340c3e0f014850f5960300009810001c041220b0302500c1c10b40d1890b002502c514003000a1000e11298401044107411f041c400d030201c1110100e01c1c02c0e02c105414140d40d000e4680c0e41d405517150408000880e40a08000c03480102c0c0360303019 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 186117473 1250 186116223 186116233
    0xf150201110903030d1509090f110306010e04030c0c0806070c03080c03040c0303080408120f04060b03010504021309030507080a02010b01080108010605301b040b01021504030507050703050715091403 87
    0x207400350170082c0a02c5084c00170200c45c403074004920000b103032003400781c554001c1e411141e01240301d29002c0002c81d42100d060744603601c000010003094680071405036000e503140ca000394488615280000c0c1e01882508010b0441c0140020001182d500c08600c207102c038000d50319032207240c0b10010b080205120942e8050300c1141d0100d001d00c04a0302854072aa0030602c2600040c1c6000f007414280200d444060320080101e031100801d10003840551f00401001d1305e0210300800c941c2c2040c2d40052a0701e070702e5800100519407a54001d009260144090700d100c00c0d0001c0086944800c0e041000f8020038048100078003156084c400810020030510400303095690240000c00070002007201607805440011100542c0b0400092114035a041400703403400855000c1d0001d08000b101c07408020640310942c444d28115401008003441c000c030b83c4d245503600503416042007a80c07603600f800c10707600302070701a0030207059445100400549213040d00c0c11a140071941b1356640348060784508101c82c04502c1c40d031502c1e0340b50384a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 186118723 1250 186117473 186117487
    0xb01110604170f04140901050306150f010207031a1f03050d03020f090409050c01030507230a0c0c080f0d0503010305150606040f060815060405100c03020102040f15020111090303 78
    0x448a582c060815600c03401d030f82803014032912400142d04c1a000a40000e119000445081c00c166107454003602e4101c1c080c03c440c1c070b0320064118205660780032040c800d00320703880c881c00c65074020320040c805140c00c01220303a00380c0f80c101005c0c242400142d80030461901d0148002c5914860b0003481019a03911201400c9401c402200442c0030b904003042c5400c40380b9081244400039602e038844c544000c3e1103a005000c1c200701e03890005d0308841d0024111424030107501184043c000f031a00381e07801c1c61282d090344c03ea22409402001c44000380040801041c11030000d8010070b00c400300045841c9418007030b80480d000304001c03801c100c900e40020702c030040840c0e2060001504071010211781a0344400050714060030a82d880c1c44508420905500602c0410910b200f0702c04540c803500f440c070180400540d021458903150801103400c16035003156071000c00c40c4042c0c0080c1011b200f0b40440c3d0042414410051486448144448640843c0c11414015600c0c08400501d505642d106640e158440100910f007042c3c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 186119973 1250 186118723 186118733
    0x41803050901140d05040606060206130201031e0207081201320102150118110406090513020903010912080601090303020706050702120f030403030f020703020604090902190311040b01110604 83
    0x44107510301d050190400c0b140c8944106000501000c00c1d80c01030108007400d00b410401c1c2107946a13005282150442002c1002c01080105036414850b820706e00004c2e0403d094040c180714100a200e10800302d40001440c2c03050089460203021122004515900b903644c0c0c0b80c5c102c0300c10560b0241b00034503c50443c884400c0f5400442840d008540b4180191030305c11101040c80400079009820a8032048918036560060422906c104000314541040d89450642400e001425401081c400c591040c03400b8100c82c00310003800e0301620f1030750102400034005419a440c2c450304e44015950b5500014143c03c00040b030941c413580001c4212234250b0050301c00c3c6420000c04a8070ba6200e904183d0300807500c0d540078115110104401018600030030041c540366421846d00601880d182c2941c0811940032480c20310240e074422085800311006090001040c040398404654542c40078810450281c084a4000092004805030800d042e1b004a604100001300d4200540d40c420000802c0c24596212000160001c0e03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 186121223 1250 186119973 186119977
    0x50415030b150315030604080a0311040315050c0c01062301080402210a14010e0f0d020d0e0a1d01052103030115091502160b03010602030d151d1504180305 68
    0x41c440a035100740c1300642008640742c0101901c0443d00d64000050140c07941c0e074144a400032186e5002e0420f440d207072440e201e8580b1440004031443d082c0e0780d508007140307400507490104d40508019100034002103940d410b0042c45103007101a0340e54041004981000c00f98032944d540d520807035000b44502d48091000280415810313032a4001c42d03442c0304060460010582c603000000e1306502003000802c0201001065034140390020140004546c000301d42144401c1d00410302000b05d00080c50100c084502c240c0002e031018050303074000d0210846a12010710301e50300700112603044c1e40d0150740319804003050119034401d0940310690030000b900141300602c005494030440c040100a1440c01948054954022141d00411020003001507840407005591104841160350300a00c0c00000c2e203405c40d072400c9006500c910400035000015079076551000d031415440f906074400382002401c08143d580d900d04511002280c165034031030a040c100c0c5421041032515018030341c0340d56010185504815a195029900c0d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 186122473 1250 186121223 186121231
    0x40506070615091505042d0e070e01030b07080108071406160b07090815060a1514030a06080f0d05040e040507050d080a20071e050a0303050415030b1503 67
    0x1080d40b01c0010100382e14001c614640d418424400011442d04007008112010101d50310f02a4000380344820802007520042d03100c0d00c207440d1011031180340307860300b003410540c058001c202d0301c1c0c40400020050058030400c0602c200340c113403522110359882e014034640c0c9103d98803480c01c9850510004185030f003070020150207561202042c641010800340d40d114031030b581c1160041c00140c2036031420404004100314102d00c10b00d600022070710600300040130408401d4140036014800070a031420285840c03040c14804003004d048000e1075141d0404414240241c6224414500103200d404500c40a410b804aa00d9410200b1a2039a03440c2602d09003568030380c0000100151402c0c0508540028191180c10200c0625442100f0095448540010280c621070300303201ca0381c401081403210710081c260300040c0030054489104800305100d100400f0005001013581055400c0856900d0000400d80c01202400642d806054803c40300c60284038120701702d640c0c0e440134580c402d60b00604802503405443c019030304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 186123723 1250 186122473 186122501
    0x40815060618273403050408120a0c090807230a09050403030501031703040209041e14030c01061e18020c1906180f020402031302130507020607050405060706 69
    0x40c02a4074210800c2c00e0010142083c4111160080260110b0703080c02000c048411010a600c102c43c1408a111091084960700310030b15aa602c0880d09000b16032059403002400b8071a00b204510b02400600c010303200c1b0303055800100d40d20000104081c0b801107400c40c1500c2c04080286603d07000f800103002e100401c0e00c8529000402c681780400d201c402800381c40c2c4502d0003a01e010446526510749401003844000c0407000c081e4082c002c6c000140d41e80742c20581c00c940c100c5107440314901c0c0230f10000a2a403180f2401483c001c0502c500f044c00307480c044060a00394080c007008022095945400400320304201e0b15092031440170100610001c0d084600ba440030205038100103091032a60300f201c0d4607208030716131008030485507112982c08101250003180c081401c5802d1910f51414280d460074480104418028821034022000420401584203800c244035001002034985d46035442003240142001e0b40c140c0c0c01402a0000a0010341c0640100c03001c40d0000741503e882c2c00c1c29901c844009102d509a0941d0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 186124973 1250 186123723 186123739
    0x20a0b0717010f050307050d020906090703020d061710020403050d080901020f03010b09100207080d05073306050307030209060d0c0504051501091208030402062508040815060618 78
    0x1071140349000359020740f0502c0001c440d1107081c9010140740c961780c2c1d40424410340740e42e030600e001038581c100c006402480c03e81d0400c000e615890800d8003c0d000e00080d00c80698540040051180501541c240c4800b4004094503402004000c0da841a031003140005030042d407000c01d84990a5201c0c45001e60b105040100040c10503d0800094100f50300c01c1e40441c00e00400400c4d80616407504c4400320b803094200740020551985007858807520f40c0c081c00c540000b0710102251803000d02c0000078291722410304410300a45d00220743d040204961031002802031585241007804100c5040000b0070344280e940052080c900c55480408000329031102000488030401d4018001482e6121070241c6405a00202e018030080c80b6420b00040080465038007160803d030071044588081648201100e030002e4069484595800b0812a039401410382180a80c00d02081c0303106d00804d01c03a41401a1060390300d08803c3d1440380300c40b1045500c01c3c010907a481580480c0402108141803c1040e14540b03403400545105 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 186126223 1250 186124973 186124997
    0xd05180a200a03030c03080703050403081306090605010902070c0b0a090509090316030f020f1504030f021f022701081602010e0715034203020d061406040c020a0b07 72
    0xd03003a100746074421400700784401c02d0f9404064200d514503500510138274040010b8946520018101c460140c00080c2c08003030325501030b0501c40b0301d0b00305a5080340c201900788010b5035540b050748000d41c0203200a03903841140c2035000c2008070243d0b04907505640d0a035a1030408a04050400c00d8150004d40000380a202c10480804851070b031200d801c183d5402034030f884d00303040144d11000c1e040c2070110411010b550840da00001d5154219155903070040e170949440071030510f21107400c0c0d25282d1240c1ca01041092154038900104a0b160028081f00c144902018401d600f80302008030900c33060300404c0d000c10302c4800000d6040c41e040101d45003003421440045400764115000070305060042d0014103015249040c10b1181c1034150003452091181c0b0340e07410395042480406116187c100070fa00050260544404164040c50700450320090350700200021018003e900c0c02000400141840f11b040408600010340a45071900c5122900c0c00342c0d80252183e000070750b0701c0c010056001442042400102c1e1443c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 186127473 1250 186126223 186126229
    0x4050402120604240b090612090c040509031e070203160e04020a0905040b06040b0a0f090f061401020d140d020c03070c0618051203070b0414150c0406050d09080d020d05180a20 77
    0x349d014a52042c0600300c02041c84040c0300a41d0001017091541e6441080108030954040d00c01c2400c035a09003950544900c1d0b5807002900709243e4200c2c0340c0d0041641c000208015000c49039650086200725080a05a036541c641201507031000c4034007400420b2a01c00040e4141081d800c40c2c01000e47c020034021116850301804804180d0302c3c2c000c4202c07250b0382ea0440001c4201f078802d41c00600751190600c4c00c409400342c0000d545810103c02042084001e00b00412301000301410b030386460101c02d81c107540780d4000c19600703643d0f600886015241d820342c91200181d02809121407101030780000100015035805c141c148520000000e003800c07081d100401110000c2400034170b601c0c0c01759214200e81113402d03030040490752a096a04841c0307051420325805005e19440300d5000c41e0211500d41c00c1441c0c0300d0245240c1600205009040176110350f4000900c2da15014855004000c1030040800400140c1c494200006180c038480c4080499070b4400e0943d04045814110b0760500c0040400026196030140004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 186128723 1250 186127473 186127507
    0xd02031606020c01080901020c12071e1202010c03060506040b0a0c061a1801080307060b030f07150306080102130303030b0a031704030614040f1704050402120604240b0906 75
    0x1c2903005070048251810b0960340550b1560b000440d03c03000b17604000300300d80310035156220303491481d282200c00a0b00000700025482c21408100c2818240001c460143c1401d2148080c1c0445070f0006518240318110440d000f4481d040030703650003900310350403d030030040790f482c0c103900070f07070b0780030240402900e01c40001003c9000d0003400e94001025000c1071540c04d400d2020000c03070382600c29080602000144503110340003040e6044c00340c21540100c2c18000c40d002081c24490b02d044842d0301c500940c00c0215942507151020f0702d42d0005540e08002c4e403596034881500700e000c6c001e0780c1780b0707000200e080400c0401e21076006460b40b29001800030150035038981d0799405c540321403081c0e46140b69000c14104113010f002d100e680303014104600d541646141a60b00c4019501e40c41d0801040540c5110301b6559050948080e00d0140002400440da10843c40301c801c212402c003112300600c0b807414210a01500301e102c0b140c404101003881141540181040070710301c0c854001212140d004603091006070317070703000380d10712 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 186129973 1250 186128723 186128729
    0x705010e030d140412030506120609010b130b090609090c0d031814180c0c030a09080c010f020a030e0d021305040501060f1202011b0506012c0c090d020316 68
    0x103641d9501896088000e0b24212000c0c4401483e009042002040010224000c012040e190018055403403800043c220494809415040d01c82c00b000c004a490703055102e0a001003048501c0368a90003540443c2d810f503540a400399400c13103a418003040d60b82c10328900c1d054100907004181c0c0c00e13082e18080410341008100c0810380002d4a8141005074a0031030310700c00c802502081e41c1e85480c0001c0031000c9488150341d00f079031124040c4280006914455600280d847c202101000d407035481c0103007040141441114060495180941c2c03420340d4441d80103c0e404044480f50f90081d088140042c1c5040d52030160540807071740c200100c1030345e020060f510030780315500c2a01e5000b0700041350304150814608480f41d0b6003040c2a104250309080c00b1030440501c1d43c0701d10540c24a000c00303600d00147c0541e22904016440102907124032070012417001420054110020308840c5c51282200c5000701d040488001581d40702e06503a010405c0301d5940c2032900c95203022038000f90403134440351440d80010713030210030310780c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 186131223 1250 186129973 186130001
    0x20402040306142d0601050c0a02040501060e0f032b030b0310091104090804090f020403020604090e060c07020616111009050a050a0806060603190e0a03080609040b0f0606070501 78
    0x604109444607190881301c401554661941200000c0360200703414002c014261606201c3c0100741d01104510800907034109a502400c00d00c40342d651440d001d0442c04980e84400d210707082c2c0b401c000d4580c3c100011b280c1c000000b9070040c10140491503000004a912401c908030403da210b10001000383ca081103421078219446800003003040306820310a10350504100401d2149040c030410002207664141520191000c021740051100c0412449034005d120b0b5501c02502301d10003050010702d04255520190395200c04030706441c03d40d652401403d460b032194250080d4040d40a00540c141062a1000c0050a0b44100b41c4280705126400c0000c41c40b0156041101c0007510300c0a00b0310181c00c00c503031500000d00054a540b90b810742030900c16922003100406181c000c000110006502140301c02110b8603011303c40c9400c10004c5040c4007216158844501e0540203d0101000b01e80107040141240d40f195400c01c03490f42e050344031401c5c1080c80520107045180d2010f024005800402d5080c401c2a419101e01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 186132473 1250 186131223 186131261
    0x8010203280504020a0308180a09091707080f07020a1701050403020d05121f0f03080307021504080304030809010f140117072714010603020a030f06050109030609020402040306 77
    0x441c0c589401400600e2400c80441c20070040c4001a10b03502004030540b58000746054441030300861805024500307184096204001150004a03079940f81d07c084001801810541d13120510315004400c9407003483c00c0100007040400c00b8124405500c409400041d2004001c4903039540e99000c1410200c002d0310316145141d40d04e4052004064040000c210780e0001814000d09103c00c00c4000d202d00040103142281d0b6900c1c0c3d07190750300e0904c128080303500544069400b8410b910b44a0400c141c0503001101c2d43e0ac00361080001810040040006040c030455000203524655031321594205e0b031070080603000148540d03c07000c0d21005807120740152030012604511001056141a0310003524903801181c20380190012001030100e07198010b00ea02244c683c4060312030030317400702c4000c81004202540080b01c4030440d080c008141c9941c182c00402030301010347d0b4180f0403000b10105820403500140328150100300d1017041000000c550340c120125590000b00014240b60390b988500080d00e91044c0b40105d90105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 186133723 1250 186132473 186132511
    0xc0901140f09040c0e1207061d04060b070b0f09030301152105010b07151a09040512070812070e030d140c03030103030c0b070c050619023a02030f0a0b060408010203 72
    0x10180c10043d400d8071b60b40003003005c00e2030510003801c6001400e810381c449580d0100da002294850781c000100070041202c089640b0400c60524090f0880b0036101c01e60340c80c0281010451b65030000003074905980740b031080300302003a0140e441076803540842002210400100313410040c400e5014400c80340200064102290b984800389010b81c010301c05c0302c00c500440d524101c00103254000180440003010130039505210541c03160704140d80f60400e82d130044544100e0004125007080703940d41c06029030107a910b410090315191843c0903134031082e90b0412140c02d948100c1e11703098200d201c0c8401480841c00718240502d085001c120b51801c50b4001d030400e902040311103080038200b0035400d0050b1780c81131082c82c003242c52140355a20719482e414050900c0f44107004200c0702d4140705c5c0403070741203840b9040c1c0060ba400a668200b41c1d02c0c64001d1040c101240303911440ba2004060808500840740310300e002040030b12107961241a034600a1000307058054204409000203d40420b007440114041c0000002840c0002c00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 186134973 1250 186133723 186133729
    0x507020d020c0406030c03060e031615060501111f0e0a061a090c030a050627090606010c11060a020111070f0606090e031903020d1104030b0c0901140f09040c0e 70
    0x30b00300000c5020300d2a0032020408940c070b81c07200205a076031008012402e010000300c15451030040044044c190003040c0340920401011140724a00d80366100d90503c2219a210010760342d01c1d04448801d14260811403411182034030140003a2108041118001103110a25402d0b601e45500c02c0000c841140e6220103007a039000100e110441d412204545001c0b00f480c1c1108524481c1c0000741050401d2030b1070b00b010401c01d40d9401248411030b88034000b1141c030b2101c01c0c5020111142c00742c404804c0d6019050104005511501c1c0503a09290429000b41140f0b03030007000d00240380e0020790404e01315540e880b40f03c2d2681c0409001040a180501d04164010f407503800e12908503074181d407041110a107848000c41801e0740100540d0381d01000152441d440c05460300017a0b01a2040c000000c107082d2500460b02620360540c0c02800c03d8a0003200030136516511884105518072070070028902141c0e268800348280310003c4002c02d00d01d001a020642840f480c0c6000c5400d5a1284020b0700118815030b0891801c0e003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 186136223 1250 186134973 186134983
    0x60405060619030305090f0d060c080108010c090e040f020402030108030c0d020109020114071106030c1e09180c12070f1b0b0c09030309090109050612011b050705100507020d02 77
    0x98003214845850111881e42c840d82e07600510005003440f201117404003240d03032507481c1c05030110009031174600790b21042d2403d0b600a049601030640807034202000419038010511590056040a450b40c0603445d0400f01c2c05140d90a0042c000c81d2508034450101c3d005880d20f002039402000f061005603200c0c4142240c15041c410103503840c0d000c41e0316000130100541c0e4040c44010040392000f1b0b02d10380d5201c55040044244104640742600104000107100e00800c060005040950222032100c0400002c600340048501c41d43d45000d5008202c14032811801301c00c001629002440800e400346030007501c0d404c6544000d01220441701280542100000c10350700540c1006d1400380740c03440d4078000c558036501e003a90a4000b521003851500301161a441507201001180c040b144021300700315403582c0d03614403000a4841215214040d4041c25922000c0c1001400b642144001441c1450183c030341e01d02044a403900888026580d900c6000e01803440f00b0018031569008020943c0038003010424090064586 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 186137473 1250 186136223 186136231
    0x30408030c03310b030a0e1606090e130206030612010c090f060c0323130308030a1803080c0711120d110c012001020c1912030c1b02010216060206040506 67
    0x42e03c1e0766000c503041c0300141d20041042d2032040010548a48a0100540c024040d001005095110305820410131090202c45d403422500295142c0b5110307a1903140741c50508400f5107442a481054104200051030700c0400b440d4030803c0034011400f420b052221060035203200c42e8845000c111302c00d40500a105a1500031400741c289810210540a2103540062100040b8551003564903274910b8080b86c0402c8103011241d070303240084003075a603540d100e041040f055802920500c60b054a45060980e40c04928102482c841c0d405880c0c041813a950420601d10b1039103c104210f61142003200301e00600d83d1980c03450388440c184d1b84000c0660001145000e0072008400c02d0003500ca503c00440080146e13030000e5007024040030000b111002000c4103010303a019006500b920510740c0030b505031110141c00d206086520950113260701031045000c084042e0101d907580c841c0b00d00080c607003000c001081c524910028840300d01c184101c81004440a9100c84809010380020740180c10070400d20080c404100282d9400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 186138723 1250 186137473 186137527
    0x1240e0a020304022805060c061906080607030c090308190206091b0112020f1603030b0a061d0a0e01080109020306060f010c02090a020c03040f03030809011e0b03030408030c03 77
    0x341d810b007900019281c3d107000c1030750080c2a10034041c0501a010070802c04004140c00b5011f503031241c05c0850000e8443c00700712414500128039807454500d503200c03400f82000302c8000304080d0409480d000c10880181004100c940280204110300000090b8080001c1c04680030a110b205007641c2c00c600000c0c14100090041c56032503109003080c0424403541d1800c407003000002d00344034a582c0c035401da64501a0140c0d208480031040041080302131008600c041110381486950100054440c1c0d03c02c028401c69a8002c400000f0b184071460612030002c51910990340d03000906801c0d11640c0c0b440b0746614410240c100c01c072165103440e410703400c41c1410009a43c012000b241c1c6154003400020008001715050400a44140c2d42c1e41c01103106a0360381d50440d0b180c0101d880a4aa03260348418503103070343d0b54040c401100000c0c406c100207000c074081072040001c0180c0840c1c11100300032149003500060302031948000d6040c04200000181c0c0c0030104001d01113543d1100143d5207510008800d1070049011120310b1034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 186139973 1250 186138723 186138727
    0x31209330c08040501050a0c060507090305060f0f070e0103150f1a04031101081305010905030703080106210f0b060d0e070605030c09210f0714030304050f0d0501240e0a02 75
    0x10b50000141d0b0705039030082c60b005071030b8040c4041c2212040000d0101520750b5242206100c0001c0c0d0114404040e2800340088800b07039190b030600400c140808882c000e00d45000e00020445603403058803000c00801c0141f50210f01d0415643e43c810301c201c001d90180c4c10410011404000700c00b107000ca16801c0c0e5060801c00c0c0d0030280346480d0281d05405076400b040c100f0200c43c00090308209421951803907160048000c1009410901d0b2481c0e60b0b910058080c0c0104540c03c00000c1e01900ca40810504550382c4410307051004444645070014003400740a6001d026140e0b640181d09440300c0e0050012071694980c0415048400301c040303800e0007455040541040410800c102c040c0013400f04480300d0f8881902c600100540c0780c4c00b0703040342e1030400c940c80041e4003600e10854101c40740014403905413610540d070741d10600706210030503036244101e10071990060000c5500d00664500f0710030380010203018600200d2540b42070100004409a020f05101e034031102110117008d00000945915485900813070114 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 186141223 1250 186139973 186139997
    0x24040605030a0206031008060406050402010e0907020d0e150c030304020f04090812130c060e0108070f0903030804080c0a031205060301051b090a2102030c0f0a03120933 74
    0x2d455050562020307009143c0000420011548520b000e0003c001030f4055030045e040510b440005050b043da0264002200400414001c0c586003900304e024041c10340007060108902441980c030140389c5c580c031039481061800141403041189005040010150380699941d28203841088609106102c0c000d004a1a00d48000d0000e4000307011142880a1940400e4149c2d9540351014a0780e051a140100b6a031403540000846035001500c501014000b601c1380c100d9541d40300c400700c6e00c2c0c0408445801c0001c500c4482000071138018030f48150414000c1100c1072402d4012041c89107407400051b01100000c2d5158010038501400d403043c46c2e0020011002881a03007420070140a645140e0050210b13101400100440c0710740d0303041026001010560214060070414602c00440e004010034240c0c0240111000c144a614100b020b0500401b0001d04400c81d0b0b5003140c440403008035800d007a003c1401114400440c1080848c44d8440340103803a4220060380340e240500c0d0715098960a20b15406000d600f071010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 186142473 1250 186141223 186141229
    0x10807081009080a0804050307051b040e0d0f03020f0403060606090305060f072a05010c030f060e09030d0e0a1b0311030c0a2c0901050103050c0904110d0312020324040605 75
    0x4600004130b51415803426103860500a08600c03c00030000c10a1250400300d5020410b00da40348110380404a90420960342c5901109403160b50880d5408001040341d8210340806000340d020f4180c45101058031801c041c1c80741c0c1c50305d04403102d40d04000049031002108104100c001c0081d980d100616092900c0a420192001f8200c1c2281050344420303d003000040340010b1602d0528231180c0b58010000b40403a4684000190050a00f50300701016075003001004102003007a2081345019120071001140780420002c0c9040003800814101281ca018080c00b03c1d01150850b241a00400301ca02d075024100391540c0380002c0c0b042038111101d4000d800000d840300c403039500d0030780030700c101c0f5901e004803001e0740f003e43d891802d54400050014200f928150506c01a1001580a541601d1190084039214000c5008010040c10300311001480d1880035042c45e01c0c0d600b004100900090301c6801c04001e45400009200141c2c2c00c01c407450907058a03020307000c1c0b15000e6100710703080810f50b0607036040000c54101404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 186143723 1250 186142473 186142477
    0x4080d090f06140d0218030c030c0f0603060f0a03050c04200328230c090a120f02060d090c0605030717061203040f03060b01080f060103090f050601080708100908 71
    0x152824812400c00103290303c203185003241e80310380b80030300110b58031219540b495224001c1c40d41168060700c107210190711182000105074412502c020142e090488150b000c02800790300040c0308070741001c02c03d801d00d00c0c00e40714400b81d400607500c6a4090000108810240403c4486540007030a00c07007042c40200003100c1e0014202ea030030003501401c0c10942038011300d03c1c4443d4101104070021451500540c0302c01c0041c0054890b071024030200140702c2d140c403221642c80041c040c0c4004c0315402860303081e0030404c850007054004460b034450080c1410b2483c150700003a1003034100703800c0500b0280c0c0f1a40d06504101e8258054009403040b414464150308082000424408298040c0750000400d040440c41d00e5450103048000340b01c800c400c5a6441d80c958840340400640d5202c02c494081c10141050242e60180080c580f207464440c60341071503540c8c1d4000440160030f810a06590b0b042200d00c441c00403940c1400303018044c105010007808120701d84080030f4a801c0d2101034140100e49415181ca00051401c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 186144973 1250 186143723 186143729
    0x906260114030f06010605040806101a0a090b0708121e0705090117040812010f030f0803070e0d060c14070c0909030504090c021e010b0a06081f03060204080d090f 71
    0x5212685881c0981c0440c1c506050658682c6452284800004401e90701030020400d0340c0c1c800b01960005c2d100c51a040c5444c2c002c9000706048050b0885000c01c4039014040a4461140e151914460301d0b652a40c0d001015400072005407581e590002d04200a6222504030b40d03040405089640150340802d100b6120f102406042c5900300100080c0080761a8404e0740c03c01000070703079001c5480c800d0401d81f40800c5903074041c006101018030340324000520703888020185412260004000c54150151f83e90b2503482d41e00040c101c3d020b02070485101400d50704c0e230640e1607540754481c42c03001482003155140640551404590b61420303c1c0c0821503c00054681c4d0070440403140b0240c00818808a94641642d4a000381d40108032840e18102040c0c000d198001084010030880c01320702c01e41000741602c8c1c1400d0795601005079420060400082000d58400c04842c4c0d84510400388a0703a200e40b4440384491480340951050301e8190f0007080c14400044144041e144400480c14840041840c000c1504d54a40040c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 186146223 1250 186144973 186144989
    0x1106161107090515040506010801080319050c010905010603060b1009140303041d0f0f060306040b09071a07061d10020d0b06030405011a040c1209020a030203030a09062601 75
    0x561000440800101c4050110340340180543c1c5040d1035030300504400a42c40c14442d50918000c038100394001d101450507160504051440c0a80707820b00b010401306c0c100c2c1c22030200b1108109081c2610350a104030760070780e807080c00045109440c2d400d02200b034980e00d4450500c204a074602414441c2c1d006070300b0301c0866001300c44280c2c4036034452000034218052036000502e01031204000d40e44540399402414410400040c281041f62200303a0720b451501000c68810790903a02a01c00310b0082004604001d0b40b0000c40f01c221341e07080303031103900704842d040e000320a84080b82c0300032400300b0820046004004c0a409920b0300f5042e054444606555a500b40309201c080d25a40001d003031513503080b640c00645100601070709040c0c1e6410300703240c40d03802171102da00484007210043d00c0700b01c0c182c509809004143e2895503910552450380e040354200804564808031703402800b0300400401030702e0600141602112544400e61280d1404001a107003481c1e0b040c00e4001c4504031048684c8405003290f54506684003c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 186147473 1250 186146223 186146237
    0x5070201020c072711030f0703090f080c0f0706030606020c04090f0803040c030c1404050a0c0f140705010509010203071b020907080403170406020d0e010e0703171e040501110616 78
    0x50301c0b03005000703a00050a1013105080400d07082c003040b40030000314000e0540800b01da505694582048040300c15259000301044000c0c058103010520f0300c0041c204075080d03017040d1007540c040001e06901e07007100da41c021000b180d02c400c410088103405020032032210909480500c500020b95907090010001036078021f00c0301001101141c10301c1400b080030b23405140d10490701040c0c2c2d51110848003281c02d2101e00c062007641000b0000304094414069248100910f403102c1c8055008514142d42c00782d9241882403c595041c0101004a542400b0304c5004641131000142e23a4205001d004040c00105c140040c00c0d808100d01c2c490040e15049081c5d68040c0b400c0c9007510264031540b80c00c940040c81039240d8164109024140024811103600818240010b000300300700040413641c1042c2a03410001d10990140c000440800c040348000c2100d0340800c21740e800c8245448000981d0302c803441205502600b0001300030600748007d5801c005205030443d0700c00700601031880c15100d14901c1b160300b800d0a204000030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 186148723 1250 186147473 186147509
    0x41a190b01091a220816060318060e0a0203060a0b19060c03051e12010806011232030328020304110f150705061b0c3c0a0605070201020c07 61
    0xd40d00f005402c0e03104000344c030340e00f0681d2410650740c0c42010143d641215074016500140d424007a00c2201c40c00c1c800e02c1340e88042d0a00300d881e458001d11640f012907400d03019107030500c40140e03030a0024034810110b03500d00007420700594062200c6000100d0700d0322070b885143c0f2014070016070044a6503145561518080d5500e940680d039030854002071178000c68401c0c001241c05100c0007281219141aa103441080b5441aa42d5500d0314074494540000542181e1610340d00351003601217812030442034007082200801b0741680f000820320350ba00c111420400320b01e1118220a152030301085009084c1c1602e8000e509504050315141c0d18012984861481610b4944c040f01c1c294a5011072441441d91040300103840d00011306205446090032101e090110f0503500090912442420655001079076100040c40c200703101c0440c00080d10790342c4450b401000800181e81c5462400050640c125031501009820b00740a0783c41c01c5c0e825104060700741429a40144a0b030010440006034210842d09039890043c4d201503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 186149973 1250 186148723 186148747
    0x121204080a170a02030a0c02010b0f010324080d0806060f0306010c02150408010c0e0a0f06050d090501060b071101020606010e100908060924090a020108041a190b01091a 74
    0x6074000c00b0420910710001040400e2100d54041c512404440078107000d40104c10504a01320391400300015404117000d040b44c811544250702405510500031080250383c8a182611580c0805950240a1641c021412070020030752000030719801c61000d5840509181c5480e0000001e800018161410818640500300c03c2d503884086141816418002003540d0300c2d103881c00c45000c1d00401e00d23504042400c5104090361402c11402000448a44c1404400c105003450f02c00c441550200c5134007d040c0703442d10000d9001ca002031003000c0050844d000000d546e4121450324520450f0000100da041d50400300812480e80d0304107140142e0b04500720f07000441000e16003001d031200e0050b40c209607410303c180d108228503804d0028090b5400580e0b854441f5140c840210080c4c0d0812044914218941100300d13044015400396602541042c442d40d0181c01c4120902c0700079480210481e40c0300745178440707400000401c214910580020060070320b4150034150030030b0318001070041d03148081d4180c0b00c030004d01c440c6205 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 186151079 1106 186149973 186149987
    0x405030604110a0b160b06010302160231060e0108070305072c090105060a12050c0d030903020a1d0703050105031902010909020a030509121204080a 65
    0x1990350b50321042c5003a011156030b03401109148020907010341c3d40000c0c0c1040510b200c503541d0b8504041c200301a1802001d0f0081c0c0c1030600c1000310a213491034196100002d5901502c85038003459007403045e90505445104601c10b0550a03407460200c00100d5001503007165500c000140403030b600c5082c3c00307031200c02d00d02c8000e01507808884e0070080e616404e819040c3d41c0f041c0c8030b0301651005010419050030402194104010f95491042150794a000300042d4003424951002c03001082096507055074440310030310014405c400d4452000c003003521808010001d140d002d000e0b10040c07552121414000e00100064030740c503411840018149600c68401c1c2d030304940700280100000564442410b642c03a058102c281e04000c1800804141c04a660008141c040da007540e000681c0e2070702ca0005401c00e14041403030501e80780f0400c808002098a00d0006406c541c0080303c207581c491000d0401c0c0e51034 = true := by decide +kernel

theorem cover : BRFrame.Cov 185971223 186151079 := by
  have h0 := BRFrame.cov_init 185971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 185971223 ≤ n) (h2 : n < 186151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
