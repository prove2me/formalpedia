-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0132
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:01:53.402401+00:00
-- url     : https://prove2.me/submissions/561d8879-f70d-4cee-a646-2f7fcc8ce4b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 23561157 ≤ n < 23741013 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 23562407 1250 23561157 23561171
    0x2040513060f06050904140111030106031d0c210a0206040608040b011a040e040807020405010f080f0604020d020d03120501080606010906031a13020f030405010911010f020c090c0d0c080a 82
    0x140c0314220070f42d03100400005d0315403a02e44507901058043d00c02c207019903607122003820f80240440050750080401e03a40104d1444980c1c20449180c0ba01c0c8030a10300183d1100100d11340700ea4504a107514911007580c0400720801030300c0d00b41072078000012400784d04114009404510f0319800310000384298020032244082e640d9442400010626014511507641003d00c001d02640d81ea0103109500240a030049609100003500010111802a80140d032100044e410030004c0d003906000388001441c401001e402c452400da0041400716040c008002e1103400c3c1802503c04042c000c4185c10210110074604028940c0c44210187c1d440134151517a9020074030540000a0301803003400ba42c1d806600441e12401a082e8030018001405003003580c40c0c2c4440d400b40514980007102201451045015100208881140d41065900d440c0d01600b205d041040c4000d00d540305035000600024001002e941c00502c0350f5070b0311102d04903400748200380205181000d4602c0c10842d0f201d401540180c0388036600700910 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 23563657 1250 23562407 23562431
    0xa060501080d020c010c03030b1009050306013c0e0f01080105010b0304050d030c05091302030103060605180106050a03020d0f05090c19050904050c0406031a0a02031003020402030907030204051306 86
    0x40d00340c90326010044c1d00140d00014254801e011009045200c0e0a011400401c00700007c1c0800800c071800078005884500c0030866882c04110036401849420100113034800a2411103800010004003501200035940b640d90288401186140007801070200001c401e0600065501d4010400c2c0f007042299801c15001007007036184001203c2c020b541c84001000441a0404140c0151074040002070074414103018168040c1c0f61070b0500101d601e0750355001a0b80758190724003c03040f00c009030801c80c0550301441103200c550b4040318199055074290306106032030341184901100a803080d40c45074621141000d08141e40d8844a40009004980ea0001d4540c034140043c14449201c1c030188904418214095081000b0305260310115040390080003070f01c80303055000c40071a094600d03d40c012a034901641500c42c50b0341200f441c1c0190454030803c801e601e1401c1c603a2040802080ea4000a88100d03030000100e00500d5042001500a5a01400c00d00c1280780400303e82c51103051480c4203032482c0b418410005c0c00c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 23564907 1250 23563657 23563663
    0x70902091f0c0c060f080f04050f0f0703060e0309060708031306090b040b07080609150105071a0f070903150c0e030d02100b010302031006052d07060b010e03060103200d050a06050108 80
    0x822040c0c0c0c41c1c0b0311541d5000030001c187c4101610680b018041c030000000b01c80d60900030b0b03054524a0400a100301c0b8a18039211088420301d29000245030401d0103c1140c50f0390b488102e0701c1c1c0540006220340c803602c0c0c0031030816490121000082075640340c880d402041040b4070302603a00c03c501072002c401142d680c1d22001c0c2d800290840d0b10b5a44911060300003141c00e410849207082d8104c042c0f4005003880701c26982d6400342c5459154030700c0b00d003900c082003000d011074400301c071540310603189030500c00b5503e50360b225230348804404081c05009803180e000701c0c5018417070980e911140c00c004080341d01c003074501c1001a4480c142c10313200c002c100e81020a01c0c9165406402101e0148115036506103915140500c100d5003502b00c00700c3c8452020a10340c4600c0e894000070200b1801078901c1c1c5859554414a28100303048501c8032080c50b060195011040f01d65075408500e40d41142e8120201c800c010003a09580c1c0821002d016000d80d02c112820070580c00e10000080c41203c0d03d209000420030713030740ca490056070303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 23566157 1250 23564907 23564927
    0x17091b01030902010c141f091106070b04080d0207060c0c050c0a0305031606021b0601080601060c11010806010905030102070320011503140115240809070902091f0c0c06 74
    0x10201e0813100e81d0317500081c000341034443c01c01007200a1b00d406040b80540702c5801041c1044807200c003a2141055018803a403884801c0408070b00b00c6a0300d00e00012583c4240031960014005061640e0108168040d07252540484502a50010781044203600001d4003030521143c12200b075815200e515910242402c0268004043e01c1c0c00c0f100a50414010161502c0c1002c564141126038603002e0103031000f4170201608100ea4140c00c0c20250800398100401149089416030061080003068149200883c0d000000844c501d882840c1c40510782e0381e03220060742c0244a6621480e0150b100054020030302d07512814061040d9079240ca1542802c0300720075680d0a0b0360241c804001408090202000080c41042c00380001e00c00c103800105400942c0150350f19403000c150f02144544c00303800144400281d07042d007a103076040c3c0f007410400310608010500a40c1c070341d03484c0a041c2140f42d00191000310742d80c0c2c2030404510000d8014404100c90184000282542c84095003181d6200c1c400700d000c1042d50040e00210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 23567407 1250 23566157 23566159
    0x206060303041211180711120910090302061c050a09030203090603040615090203090606030a380c0a1205040f020d060e010603050d02071706040201030c17091b01030902 74
    0x18241420f050009108000d45542155100c0904040c0030641e140c00c1904405107001071400b80191a0000300617050320301c001200d207159088207440b101c610040c88181c1e040f140042e500c00d0000c2e5004881668503c0143e000654480800714881d4050740801101480c4c0441720b0314144842d03140d020b02d140c1926210a0001c0258200b42310326841c500b05400511b9005006e07150105c1d1200c8001c02c7c1030840d102c9030304280102ca4000040010840c010840180c001e0416002050041c8054442c0700c1040b00440d450600c0322500750b040c2c07204904940d8540c000c054861400d010070709100036021802c1e4402c013560000301d0a8086c1204850600d40305a07845941c0003001d09400036442e07800c2141c83c40944e8401c482c565500c0035448801e60f424421200998400c100600f1070415245019107007401c540d10083d984480902480c1d40806c010400e5508140e0a080c00b10f4040e603129825603480d00d10220380c13148041c056042003518100000d0070005200003100c0d6422100d2038034011070944406c09406 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 23568657 1250 23567407 23567413
    0x3011a090a0c140a05030105010e06090a0506030702030f160b01060c0b060405040f06020d0606110703020d02190e10031502030105010c1b0b07060209030c040e06040305070317010602010c02060702060603 89
    0x9114844182c11054100c80245410a104030040840034003681000207000000b55004c0014800c558004402c410111000c80e0603908041d1500e00040e4080403e0140c0c50040c1008404070362458004c106880385400c030504c0b0f094454908542d50818a202c4220954408454200001c1d1490103844c0700151207030460440c405c655642c20074030025140150040b102d21038503e00d8500412040c1c03000c7c0110304902500814120314000d001400c1080c845041e89207030708011010801a41c50850890b034a65040e01d1000c6040c09011410313203182040e030310020034840c04900300110480b681500406892103107a50541c180e440d0250202240424001e4501080c54810740c40f01240900010440c00140241072000f42c3d03886480c5009660400001102c4c0c058000ca512041480c00380044101c0340001d480400c038010030300c1e4915aa6038000750014043c428002056402d052245440c1c65402c182e124450081d56514500203000f000402d01c030300018001c4a01040801e84089986030080c0030003002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 23569907 1250 23568657 23568661
    0x93c0b0d050a0c120803070f0512010b0309060901110a0c020406030803010308120a06030b01060e030109050714180601020a021c120804020f150406030e070503060403031d0601030308040f050a02150903011a09 91
    0x64a4008d8a41c0b150814040180009030039151200b8096000c0d0416910050b03c80c1041040f4a00e809005012102142d05002d41600440f10b48010740d001d080c5903140c521032060050012500a05140d000549211000000401400380d40d02c02040b40c2c01444160988540c1c84101d620b04035410350000412010640004100aa104500d413101c1c400000f03000003204078041d611203242101e42e5020b01045243c01c69603100d903140c001c000302d82050705100f684a6a01d80b0200003503c40c01c0000000348030343c1ea40069100c80d40b49807900e04a0b19a84691b20180141c0300070030141c0000300403101280300391956804440ca42c10701c1da100c0a40030140003009400c0600f048030a40251050041c0e50215100d2100b001800d030f0750070400750740942d020340c81c0020002c500a0325541c5080c0c1035045080f061380440300420010381d008262591141e001101c8207008101850041e00703100c0c5011000e9481060300ba2a0480f40c03142d40014490018114000c001032628241c0f20303040101c0140e0019401108940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 23571157 1250 23569907 23569921
    0x15040f030f02060c011a010905060c1002070305160605040204050603031602010e01030e011505010801060206090a0312020c0313090507020d0206040210020a0c06020106093c0b0d050a0c120803 84
    0x1c10850705840200203609000300400704508541402d41e2150b040f0f0450080b802e10340d40c2110440d005840192515440c0c4102c80628a55a036041d00e001d0b0011030b40020302c902414420410364800741c80100c501c4103818064207044001c3c04040d076050384224074101c00700780c19240000481e180f00d48030f80204900c4501d0740e0010350b8030b996010f1041d0305244e119400000400070030f1080d004441c50000702034200c0c6083c4000106221016007280c01554484428800c1481c000660300c403000e64149048180760801c1c164a0303010703016442d8901154440461b1007003a507050b07141040305407844032404200781c1d034800d0401c9955400c20000c02016821400101c1c015003008502c4210491040c01200d107880d12030790320100c00c0011640000c0040c0d40d650820b11040000d4007406801510b0910f005404070190008810601c0b03440b20b90030380000c04200080070750320b10764001100c4080001c00100b01c1c501070b818540d031686458030086815204d0780740080b0b440c1c1781c10412503c030a80c000340c1c3d1904603a6404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 23572407 1250 23571157 23571173
    0x816060c0f02011806050309010b12190201052107030e01060513050c040b0313030314010b0a030e0f0304080d0306080706050301051302040e1815040201120b0112020708030615040f03 80
    0x2501c00c1e4104410b4501040f00c001020310010700500301d6503580b65513458841009821504076100881c4188403418010903e4400045d40d04502082400b03d10161402d920050303130f42c0d20408190714040564401d50b003600e130f80054a10b41c4140c506440511003500c6005405080711028020039034003c038800d9092204450350391209034041d6880d0446860261150950b1141e03400481d14403076610152041d400416625001e0043e0062411201000f25414070540304868024900658200f66990034a110a0041009856810003294064035942c54680140b035441e1401c521024000c2400d03c080080e081c4800a0000200c3c0da440d034403030303080d40d00b00402c0080c442c09400141110035024040411604030500c41c89000d12110300000d001440c010036001e060103886c1e40d81c081d5100402c802c220143c8d0300201055400711603954009131506a180c0113a03006481c001c0d81110145c8007080820403c410708000b18003c0b581161019102002c45000c01c4040c411030286801c3d16404010820000b80e6030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 23573657 1250 23572407 23572433
    0x2070201030b12070302011407170a05090a060908010c111b18071e0c11090a06030b010306020307110d0207090213030209090a060b0103022701020a020603040b010816060c 75
    0x1458007041120300c49000810082441082c80d40d240c04c002c4c0208110f607003101400b10000d8a0682072410403000c3d80300e4a00011014412081e106000a03101186d94828000c9405c0290020700c400c0c01652502001880b410f00742c01001c04943ca0801032802940c010b403280d82d541d100c6038005011401418030480d442c0c002c1c005c0d409070014511503441d50030002d0300e0003041c03186010f6035684003000d0302e83c1c0e0003440100c0840000e500703009814108902050b0000704418400c3c0c000d41d50030400b9111801620010240da600160078089150008400c00500e90025805200c41d55100d146c2102080360782901c0d00e40b5401b081016070701c114802c0003000c0c40d907000303001400c080341d40411b040c5175243c0202d0305034541207441c51002d40101c00401c04100b298400c204564100707290840c102480001d40805003030304003003e0000742010f0054800365a1080001c03101c281c3c0e019194540300c5c201854605c105400a00489100b401a08550508440281e400404640c120360f1940d001c08640c0e120410200c201c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 23574907 1250 23573657 23573659
    0x30102121803072001180e1810020403050a02030f01062117070f050d02120403020d020d050102070308150312070b07020c0616020108063f01050703090201120507080a020702 76
    0x81404003c010410389a02c0345085211150700a03440c10341c0d0800106802c00346460f5900d90300d540c9400b44840103070036060740d610207003403d131895407100042d03c600d01c1c2142c50f1305401c0d10381e8000180070080090108070007252600c00d034216039440307000a43c40380c00d07030b501c1d801130348025807007a407404216201c00400e0343c0407680501c112480c00c1c098400700c02d80e19070184500741d90200300d000c2a4030030058200400d01040c0b1040c800340801920540030203a440c070861002901c9203002070b07401d4043d9a1021101140554010003c6545507114540680759401c100c1e10b0100890b0300e00508403940c2001f180c81d05081825440492920030982c0e140c591590026080300308500c500d00320088039458087c001d002800c0e2401c14130750115154400101030700001009140940e101a0b03410300461414040c00b444c0c841c3d100c0c0200003480100707903203030701514214408403455820072003409020303034265000b600e8141c001e0382c500f24101c0c04101c948094030b5090356003000058000d070014903500c14a03130181180500c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 23576157 1250 23574907 23574913
    0x6030703021315080a0e07120204290a0602030901080c21090102040918020604090e030d0204030b0708010e060315131703062b06020702010e030102030907060206060301021218 77
    0x100280d4482c05a21140c0002010401c1da0494a24442d00207880c650700070900c90b030912103965054051900c3d007219200301c40d90402c02084400440d0707659001843c04203580c0f02c040d4140043c80b9003407520381051816903401551409004500980b01008841400d001038469900075110b180001d440c0742c0c0540c0101c00d00d003100c204203180d040d5221a40500030750840c000961101e091444402c01c50389600c4e1000140400c80407408010b80311a415034007243c20001000078a022000c9032207040d489030b00c899105141c80050b001c001c102d078540c03601d8000c80040c0e40341c80315a80c1f154061400d4240a40b88968168030004020050010300926239501000c030040400c080c1160ba0780d0461541005840c02c841e411001c0100519410800c00251020181448031542154255840c00c100203042c0c001070245600016040b0035640511144264160050b000310b6581c174114455585a20180c000c9100500910b40810100d1031705000783d540e540d0a080310a403150303e801c415080741041c01c40326040300340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 23577407 1250 23576157 23576167
    0x30313050603040602070602070b0f0a2f0f0c0f0c0103060605030f07050d0905010906050c09010c0305180a03030e0a050a0812031b03040311060105180a05040201021c02070906090203010308090603070302 89
    0x11f01240042c00c0c01510614055569040170310000740701c450300a040082a51034184012007074001c203541b0002045015400705101683c041c1443d00030303c2400501022100c000070200d501040000d240030318502607070150b076607181181c4011400d076070140c8035540000710144003141100304c1c20b00d04a50001001e0801b5407030110a210001d0607641100c0c0180d880f6552201c0440500c07a5a010703580d4020a4103002614140c503010020301254080f89001c1c0400501181c01c008144c00c010982c880c2c107070000c00e04140c1681d245001406890314031606d030b010300d07035105c1e0018260405130081003e80b4169400782030500260000000e1a810042c10407101c0d40640304948001c91424004600850080e541d080003051441c036000d107001c00603404140649a4626003003120740f100c0a42c44c1c5c00c44030031603010401e9242ca000403880d011400c0391034207500c250800c04010342900010110101c5102010a0144a583d84004000c901007440060003500081003001c0d458030b040b000441d0301070b03000c2c20018101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 23578657 1250 23577407 23577413
    0x306040b0a0302040510030b0a0506010c0b04050a05030712020c12100903030207080706090c0e102606010609050406060203070203060a0b0105040e070906031404030c0b06010201022101050a0503031305060304060207 94
    0x2171039045d15070240034200c801c0c050040c8000019400d81c03084045030244071508001000814107150603070040c18000b50300c00840d040040c2804944901e941000c1280e8030b80c02e682c28101c0c0c003a2082940d007000362080300034214040c100b01c0805100545220003401040b11484510809040b01042c210308260b1700300301c1a0300150002020b041c3c21801340100280f021654600044081b1840c2c2000110300340c8201000201001e204901007078802d10f00d105500103501c0050011400350742c10b5800711a00400002241e125401700c401c1c000c0740c004407000d00c04a540d07030f80140e0b124424a200a5003680009002486e03003181e503040741d502e8a00616003d0b141983c0c47c103d8100d02e071402d450610000d03124035000c0110950500810094141c41200307a995400e00f40c1d03000e44a01c0d0800f900408072601d0703000041c0a68000c0d810317150421000d801c02e0001c1c03c03240c1d01e03440c1945c00034040c0030f1080c51010343c041060b0500100b603850310346400d0340310750301c2501700000c00c1425000204221a0140c0800140c000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 23579907 1250 23578657 23578661
    0x2040306020705060709290c01050f060301050c09030a0809030c060f09090f22030509060a02010b2403010b0c01020405040207050303150f030309120f010504050307060c140306040b0a030204 83
    0x21409180010b0321401036141c1181014000f6003034504000c4041c00900410504030404e85894800300039810100801d181124224050b5907003a0800c0c0d440c0c0020842c001e80310000b4544a06c804400821066070f079401d00362244d000744001c0e00e03007542c4800c03510000a01c48100078045100010216000305409800048a0354420750541490302004600c5054908003807204a4100d00254020902c40c0390800310f04c990b40c0c1c400c039048403040303402c40649010705020790110f9020f03030710242940d543c2e071100a0019001e8400c850701c031809440610301d1190791803102c402154001500500f168550b0346050300f54170007908011080300d440d55080200141c3ea940d83d00c02000c1c0b16100d100070f152241b80c6040203100030b007a0602c000303000700c6c0a41d8000401c5d0340d0200482d01d1460382180d1400b841003240260b54a0080240300c150070b15880d040c280400d0040c0080589501841500c0500c00000b500408603100b0081c1c600c480040d49041c40030644a1038030f600300300c4241d040542405180c41d03803600005c003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 23581157 1250 23579907 23579909
    0x120b090c09040b0f1c061107110906010c0803010b0c21030f0c040906180e010c05040506070c0302040507050720010c030509031006180e03040807030206090d0f060212010e06010c0b07030f0204 84
    0x2010317482001c2c0c8010040e90f030180b051190f0750b080c2070720304189160b1110300c040c030711004c07900c0e03c0385015000240003a0f0041c10100e514070b40280c0c85c4c607165a1541d444c8260740e40544028031003480b5551090b6550003003204501e0000ca45400d0850444d03d90040c030076121440507060401c0300400b4000420729506501ca00310040250b04283c8054101e50882e00341159503803a0382190356414101a01c212a0f04a030498080b42d405860701ca83d42d0707440d424406220a51508000d500c9800c0101b0b1042c100c0c0e00c80e01034050302e4000c003484480c00800e98140a01555600200b80c003081c88810032101203805030303001c1e00c18107002030705460403c06600440c2c401c4503502d82004c0a500c090380f41510901425115a403490111000114540743c1040c50b03417569001c0600c0700900c6003000050b042880c0c2c4a55540e0011340354044040504d17804e417803500300069040080c02d5060200b0342000002c03501117210849000c3e19040e11044095641038943c002050380041602d018540c07a01000c501d41d0300c941c80200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 23582407 1250 23581157 23581189
    0x5100204030308090d08041103010905011e05070503090606010813020d0f03090605040b0909040c0810020d0f1103070f180608010e07020111031501120507120b090c09040b0f 76
    0x1a9103504500c1c0181c09030201401c2610607a1100f9541c050142e08102c490340c02a030803200312640d180c1c2120019002d8070382018000d00950034411038054601040007868031820b6041c00500c05951000c904803118001181c900b05140d00500100d0541d50107500d026800040c011600d22190499801080308056101c008648000362005600d00b41a8007007001ca010781010b01d0200c0c602443d04900240d140228500180305000303000200301004030300d40841c2c2c000c100000036079849070384000341c810003500011030350b81e0310302c0c204080000043c1d000e00c80c1c562034601001042d41181c450000840e60209004285028401c05000c0c490b09428440c040c4030091025030b960648540c1802e045000c03028001d0142c10541e030410602040d880090019217502000710f280091102d4809801240c0200854210342c0c140d920700010703c11403642c07090b2818001116075a090004a84044c00d00140b1a0101c6030810134020030300c1008024542a002401200300083c145094442800d000aa920101040712 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 23583657 1250 23582407 23582411
    0x905060a09020304080901080105100f0315080115180908030106200f031c0501030b07120618020919050109050402071a090d09080d0905040e010f0c020304180501120f0f0510 76
    0x1b039525179210030141d02410090313a0030742005000d1100a004442903440000515445080c210b000540305a00b0f5002824544000d1000305180805000441058091020350011039441d4884501d140e0003800401c81d4802e288603e561711b4a14104d5840030f415101c00715221a400002d201558104144881ca1038102c1c0a0355445c0c0440403050b02e200d100b0300d2100c42d0241440010130111b019480b42d29880442402d111100000000300900180141d4010081481e428410031031070704030543c081c0c04010070030b40d4500c02c640400700c0c900c41c1f0002c981c031413680082d41e915818441820f01350060302180c0c0c0b00e481c0d41c81100012410000000804031100201035214014905116900c40a003400403e9907001500c4405201d08004014205c41d010f04c0c2e0181d9181c50101c0100f078825440700e800e0300f400b400c0030030140100000c001d40301e510901c42c3c3e0112112050f101c00c2030310303020312032181214220b10300d00074961030642c4c070030305c403202c1d500c070145e401030502e03540100071482c24030503449141a01400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 23584907 1250 23583657 23583667
    0xd0816030213030c060207120c030201030c020f030a021605031b1210020c030a14070b0a050c0417060718060c02040b01021c031e0b010c06050405210309010b04020c070905060a0902030408 82
    0x2440c15585a01235600c40003400450000701d0411120324051365028680072a02d5002c0100c16032034010020540c5400c0c1c840014640b142c02d6000c00c6c0c1d50200d4001005c01e550550355a0100742e41d4190060340c013040501d04195240c4240341a2202000c0009a40142e55503142150111801c0382c0021054002d40d410020700240301540c00740388903656088205240d400c1408035100c20396901402405119150794840106400c194260150380040035202070072803040340003034480e03520750b48240c030356801285440c0030121110b210381c80f02c07a050f501a0fa0321052003030055000c20024000901c0400d0543c010103a20722481c50103050b090108024a03103011030304061480070303403000003440a901032800745010300c1c0c0c04850781c2c0610000080303500700360041035a8545090503420f00c1041d102e500c001c0002c848003140100d060304095480b07400f54800800818108409000c282d204034001e40180da049440d0502c054000d0358806604100d01914594460391591a000100c1c0d01c10b444c1910400d0000c1070b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 23586157 1250 23584907 23584919
    0xc080105100504060c0f0305070f11100201020c120702060415020307050f0a08121504051f09090b07050a02250302040b030c061c180f12020d0816030213030c 69
    0x140e010340891441c1852400d468404010302444103054010709041c806e1502500b414030940c00e90b400d95410944000d8280118503000400c40720040c4083d0242c034100c40250320850042c8282c40b103410383e0340081c0c214000c407108403203183ea01500f0b0413030340000d042c0004960f00b403000244413048481a00116612001d6041c02032811a0303446808401d60303c020b000d0000140740c84140c03401c208003400000c411751120441b451040f58481c211035009840c00301040340c01071000300b142048441413001410203584841d0513600b60f070200700f006403080c0007410116603e280b103400100461070781d62040c1c54140f05083c040700240c842404c1c3d00428900c240ca001c0c03080d03140520851000c190224000c0ca01440301c44040b8a0383c0c060000f4607060138032104c40e800c6002c03030103030048001078a845d9100d0140703241c00c2c60219030b40102004103851006080c9840c1c1c0110740002212046240d10744c03a4480541e0395540c0c070032103030800034102100f05a000e001710555072008641032000342d889078108900c0310303041034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 23587407 1250 23586157 23586169
    0x2030a05100b1c0f1404111e0a0302010e010c0605041a01060e2b0501050c130806070c020d02150d090302060702070302061804060e0c1801031b031d010c080105 70
    0x380104000107800c1006000e140008a000c52444001c3c0710049640c00c5035a102000a2809400384580240b0300400c000c10402e4000d040710501c1c600300d84036034103288030403c04030481000300c3c02150000500b100510156014080000181c00d05240141d14040c8036035941098610a440450f10150007a4003030707884d180900d041e035014109600e00030310281c11500000b0390304001c130703140760301311000030b1111903201c0d1840c18043c0704254001009000ca03040210300c060700d41c1c1c406100000c2d041c040341e001150030b81010036494000d00303043d0303a0081625819000c00c90b07814024030089911400c802d4914030a240c03a000600a40c030700464000070040510708019041c044010f00010454105210620050f17031741000b925509112500d40325560403082d004180200350a410018041c3c00900070002d00140c804006c12988075041400b00d01940110f0044d019202c02c0320108452980b44110406030611070303800012441280c500c40c110741d42c80210707080d085400d40041c02d000144d0a00060003e4140a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 23588657 1250 23587407 23587409
    0xa150302031614090f270d050304020307060507050d0e060d051503010c21020708090a03081e091302090a03080a030209010810080303010303050a0e1003020301050102010b0901081e1002030a0510 85
    0x9a030701c0300c44c40c40c01091400b207500008000c1c2540090550305000f070a0507035000424810114012160100348260000d4419042158100c1c4a07105117100418280d21490aa407803031607014000b000c0c81440729405072030f40e142284285400070814000d280744c840c0c25000f868003c0c212244104005c40e2820103150079600c440c20b0034800d0040c000307280c0144120348400d2001d115800b482c0181c03504164035141da403500c03807401d140c0e602486141c40401880300100083c01c520000c2c018100040701d0000800d58036010f480c0301d9079846694901c0a000130200c030340041030f12003002031094044648a0b65641080c2d003040e070802000a43c04103010b03510b560070240440e0026100c266149040c0d191031306055491005000050401902040d1040414000d140c5043c0b0800002c2000040f00502000100290824403882c0e0066080a2501443d0b040102c18030f41030b81c120801820a0038078803070501c1407041c0c100d014048584500381c038002c242000392020303500501c0301d2103012580342460740141900d0059 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 23589907 1250 23588657 23588659
    0x20301090e0601150c030905180105100201050115140d060b09040c050c0307030e03070810020d06050904150b030709090501050108010c05120103020409140105040317070f02060a150302031614 84
    0x8080140f1480184091315240c400c41031411824180c15450100e880904540c0010b8004040c402409610300c480b0f890b9605999042e5040d112007200501e0407030a0b50001c1c46000785504410300b9400649204070030105141c1045900689098003140c01030781100c5030390b880036001c0800030030b000e0510f16107401452420100b5240c203905001040c050540c8900c50307048001e091102c0c10781c00301d075151030074481400107002c010f095584111200c40241c0c044c0d03104071501d4280c50319220001c40d852400c80c2c001c90140da081204603080e240304000000080a18a00103503240c1305140000642d410306014000006110b10004a184d500d007980460a5501c01603413502408014010b545212024125541c1120340413039001c18102c0d464207019109000c007078070404040d400d10b0100710506801507955040c0310000841702c40c031039907071800840d164040601e9210050300484049103d444a58010104c404020080f05403056030325800285010148881e031002240c5104c0100f000c400c0755240c4252041c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 23591157 1250 23589907 23589913
    0xf211603020a05040506030a062102040516021c030e0d021501050406030201140307050403080c0f07050109050102030a030203101e0603050a02030c03011701110d2c0c0907050705060406020301090e 86
    0x380082e0203009801640501401403101000050603001c180d0042001040304400c48400a48000b1200f00030680c509001d80c001d60508000c00c0c1d00c0c049001ca0226500420b5010b040c4800c034451548800000c0e42d000c501c10036849101032904800244840000d2201c4c3e60014680358044042c0074a01c990161700c440d2286117001c40810250360050340200b55400d90440c1e8036902c0d51400025541030182c1c1d00301034129071000c184502c00c4000001c1a115008904048a0003540c0e2480112107203901401903500681040c132440100600903009190050310701545401c5090700c4598101c1c0b00c0c50303000742c0c582400004040c2001080e81620560b5007000140e401076186150160007071949200c184540d03a131039581c0305441c0c0c601c80d03c00e50061041241c040305007503803500c802e400380f030203000e1441c08010a5001000c43d00e41d18103010b0b980080b4420910301400ca800200e404006418100a040c001800810004480040d03014401c552007103201d0400142c80c0d5042044240c100d401c0d40307200c030a0a074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 23592407 1250 23591157 23591167
    0x603060c020d02060a11220b070f140a0302100902030703120305160801050102070303081905010b0c0f0a020307030f02010c080406020d0801050301090c090c030e0a0f031403070c080f21160302 84
    0x10071a0b5085913088111240c3d00304840704604410086014254404514014027094a07010081c070070b40035460090107904030b0340e04400380c00c03078481c2c442140450050260340308505c800380c510001d0b00b1041c00d4600040685a80700c2c0e69031603200340e02c18480b20030000260b032002008000005908030448804151804044a6060100107590380855000260a1202a000140c20110110100c10142660800500055958003400d03c04e40d000721007101414002c040e05d441a65900050800c07006130001c0c010401c0520f151a8150400b0968101743d04126005505130089030170040203000611070342d8018000ca01142000902006041e04500d20990409120383e01040705018079505843c02c642e0001034090301c3c41420380060041182031a124011140c00c0341c00d02c0402d809015405000b5155010421500203007560948412681d90010400110101c03001c219400b0180103050032415041e03142141490081452080c1b0032026403000c06008100300c05d080d11005039005050150038103505103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 23593657 1250 23592407 23592431
    0x30f010e070c0605040c050d030918140c03040c0b070c08070b070203030703210e0a110103020403080307050a0201020f04080609120301060e09060609060c03180a050603040803040302010603060c020d02060a 90
    0x807008052001e403c1035252008181841040280304000740002401034080c3c5503030303103030103481032041c1d118540140a8143c04061300d24840e000f49805408040380071400c559800c05003004940028209613080c0d42510b40200300e85008200808445004001c8041a50f02d8a41d40501d03249407038008804580040c8250401a24000709541c815640b5051500e121030304952141170b08071840714820442420000c00078600d00c0c000c5a040c2825009a4070038601c80160740041d07060f07210b107200082c58081c0030030004010a1080c03014012207480c600c000340ca0b0103054210402c003a000350300300d128140c001f8401c0c4000c00c88104541d003a00e0440e404c080342558980350016005410b1105001d004150400c00a091940c3d200200c903950140204020386645500c161345a5030b40102c0c800b09107403a00114a01da0f82c5c038103040f5010840341c00418091556503996a0441660000342040b810b5648500021001070458000d45d41800c801d580240124202000000d1030088d0144c60500520b150000640c48 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 23594907 1250 23593657 23593667
    0x60602031908060f090112050609010203070f08150414011712030106030b060f0a0e0102060108010e0606010c020105070b0108011a09040209130314030708100e0906040308130803010b030f010e07 85
    0x2103880c03141404071030b9999400c00f04180c203008902d00c6078040003410022501c0a920b142031112140104d040b90000da4441c19080c0c200c0c842924240f01003a0903681a5108500c074039000ba5010203d04281c802c0d91408802003000e0710750842c062801c0c1461200188444000d440507a4040c40a00004040001602c402e8030900e01c0180035038010552100105213054079140c0846426087c0703600c245a60700400cac0c000804908900c1c0e29039005014039800002e00c544140034882034001040d002c3d1107152905001512a410700c08030803418000207101e8600842e42e04180e03e4001c104007000030135040802c10007401c0b40740f6408292031180701541c0c01c0c44007523154154141e52045904d4400c0803008003030f0030293f54608550000485040c80041000011580481c5240c024400c0d603404a200035102c80003201c03d400102c80c04083c81e8810310005010a21410003103400061562100540c20340686a0b2845035209800801d99410004240185c0c0f40d1016415330050881c10810307041400d10f1440240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 23596157 1250 23594907 23594947
    0x1008060f0402030606090d060605040c0f2c03030a080610031509020906070203071e121509080408010606030501050f091e0403050d06081608010501050d060207050109050106030803040606060203 85
    0xc040c1c1e5022000940c642c49040031035041001c001c000d8441c1082c10f180840c0901514020503018034144840680700d540220801c80c90000a5100d0355034082d01c141064007012500d1040145403184184100d107030703407018001001608000e60304ca0f0f142c1c1c40e002d414850a440041403c0080620340852250001d42080c0c0b204182c1e2802803002d82d8503036071000018124010200040c3d410b000b0740b580020f9010b048800004420700701144014081c1e0380e0f107007001645684450180c03c048944400c0c01d03014209602c03140d40300c0d1151201c981804c0c3c4846d200760846441e43c01c0f02020980e00c3c4014441850001050907110004840c40c401c2403070000c044001b99044021002040300c0c407803000c1005c1501a806803074120040c40d1003000020b80c0c9486481e40c80c20503403188211114285404030301d880b41030151030b050b10700c05001418190501d035075130303030081d840f0080c20f80e40c41d5a1454620000360081c0100c0009600503100c4503204c0c101410504119043c9502000c2550300411000780b02101403a2901 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 23597407 1250 23596157 23596159
    0x60a05090d021203040606030204060e191a1908010507030b010e03010209100c080906070c14090f18010906020c030901090b1204060207061d030c011d0319170705091008060f 76
    0x25491703441d5468820041d02054000940c002d08100000c039424000112052095039000c01244040124a951204980c00550701c004a4803e03d20440d02d182444007080c0b00e0340c1c020300704210040d27984642c0c40c0c0c04c44c0e60a40f1410002902c416a000360b944e4407900f1404801c004a00031032a000c20b810000c0d0900d04218440070a211102c0700507008d000b0b13484143c0742800300c00380880380d8443c41c5207008104185e16011b0311140c0307010044500d040b0704203c112203101c6e14080144901a880b00604030014602000076043c445d1b40300c080c42c4002602500213442c10400600c015511040a07000140c6142c5154201311850703c800e006444160091036a210342140d00f01c03034010381d1406c042c00c05c100134050703030032103101d91a880702d0600d24103160000051190b011402c00030004505040d034180780280005001c0000c2c0c2d40706114003c403d102c482d81440c00c0304003604011f112000744008006500c0340848000d00420030100d44448181030640176003094aa0170b1400052501d4410001900c01070114005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 23598657 1250 23597407 23597443
    0x714060307030b0a0801020a050406080705120615070606030c03020306060108070e0d0f08030906010e0c090901052b030206010302031e0307060b03010f02040e0a0c08060108070809070308030405060a05090d02 91
    0x1800f64943e0013802c000f03040944020b5503140c640550144c0103900c03d12420002406000002c4c070b00502c181d0603a402c05032040e58080c0951540d07820000e00040c01448000c003240d0410800d4006152071040b44004c0d845620054034080c034600402d810841d00404171414014150304205d1900d500901740b04d030540d02207500b15048011401c041d03642e140065030007010340c080001404180c1d030f000a2042e04132040e6000c1c0804550391000354804900950b464a0303000301e40800188007600d0500d213456104000d030486442048040c5410602000e003004054002d40c00100040c425801c00307118041c00600342001d01c040802840310f8465981c03013100e10151502d40d5440c0f080d042540c0a40200741407800661055440c1c0c6d071940300d008154401520246001031505407003100713490140034002d2040ea03050b1900e0702242d6411401381c400480080041001c2e0040f03503408400512403274003450256005100401c11490910f40282c2181c80107090303d4429445104d98400c3d0301d40c001a40c6201c0aa50041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 23599907 1250 23598657 23598671
    0x80f0610030f0f0f0b0a050603030c0706030915020703050c100209010801060e1206010602070503010b040e0303010506030415021801021902100c05010605060412120e09010506070302150702010e071406030703 91
    0x41400c0c207610b00c443c0101104000392880c0240202c1280150195402ea5810020b5840d60b01c03c00d0b98034400d0580003121600880d100f00803184c000d502001055000c4d6406c544551a100c012804a074821403040340864400325280c1c00d010003c20141d1b83c20131022104616054207100003038182401481103d0800101129013085034817600078550f0a441034000300c60855071901030207500e0740054003407107020390b10b0500c68910710302d400c0c05078406d0800c052024501d03603401e002c240145c66000800c20b031241620410005180d80c0f0310710041c16039465001807492a041030100080c2000814011a03400c00300707540001c400740e0384d03008e00c0c0306910320b4505010b0707566601894454003400040c0d100741e42c040000310b0002510518050f4400026104000180c1d1081d00c0907002d41d0301d01c651084d120313000600c0d440140444d0600c00010a200c40c003e00484106284060030040505000c40340400140d45a00314481c080c141003000a0103840440c0040c8a140a1400420004d01004040f90101500c07218 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 23601157 1250 23599907 23599913
    0x40b0903010f0c020706020f03040e010605091c080706060e042a050306130201020f030301063005070e03060703060803070210030e0f15060a03050307020f040b0a0f080f0610030f 78
    0x400348401940c0d004083c001440c42c200069100e41071440745070098000c07801c0c190800754001c8111025501845c2206050ba42000000c5859402100e102c5403c0314004121406180060b0b035a05111440b0b880384542d254498a8010b0a039841a0702a012018408003400000303901080c00400300503443d0300e104a000b01100d0302e44e100c0b1103154811501030058a046c46000400d13500100b88060003a02107680e5003000500240e917922003442a4070014000e0828150040308075200c40400c0c8411620510010b8465413250040780c0b81030b1500404220b418844241d142000d0203c0d652003591401c5c10440d8914107241e0586030b10483d10001d100f0034604501c0a4154017a601202c0742810300b90071920040386180609030754488031014010040501c900148a91501001120550f41d00501640c1040241d60911010382181503800d540a6112a560324042c5c4810a581d002846440910310740780b86004c0909042110364140040ca507000b440420040000e00388200044a920407003034500210581 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 23602407 1250 23601157 23601161
    0x209040b1f0801061a04051809011d01020703030b06040b07020909070807121e0804030b09070509090106051905010507021003020f030406020307020f0f0d050c070b0f0c0d08060303040b090301 84
    0xc8030300108001e61403000c5003400341540182c056500044030702c1e000e51040794403d201c4c0d0042d0310440da88003898081e5200007240c0061929003046400e4008110320002403c1454020545190a221a135011502c48145035044c0900119107000390b039451301c3c040c10116040c3c00c80c07080d4900030b0300890226002c100c01040401408004051860a5402158843e10000a00342d2400015980c000d90400d190340d0b00d00f00f1010104006038020481c0d0b285c14516941c040303603140002d100103050b0081900c0001d40e40c841180841c420303080c9000003d05203040c2400c008050483c20001c43c400408003500303019590308101180c80040d01101c08024030a041c150440c0a8407602c0500c2004520200c144002c00c02ca5401950007a004c6409903007030070080880096540708075980400459220405441c0028080c10003000142c081501f952540e64075a0712089096002c10100030201000085100d0741d100c0034483c0e00602c003d075291549442c20900700299a0340103e00070000084000542e074072031541c0035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 23603657 1250 23602407 23602441
    0x80703090b1b0708030a060f0905060a0603110c01150501140f0a0c080d02070c1508071e0306030b100f0602030c0d1d21060601030207020d06150503060906150109030209040b 76
    0x1113890580e40e40743c40012039015000b14032503d80340c40c035005d6003c500c4080c0c0d03000b03072489214040c5c03500b01c40d2803400c5812030242c48004002c914643c0300700710740c904188080c01400c140010f00c8079441096842e00000408024003c904600102014801451410034810072540d0100583c03a1001000c03c482c1400da0341c51146031446008180300081c44400c000c4d030500e845040f540d40126454800c1c001a0301034601e20b070f0840303490000a4442c0701010f407090400e454182502d50500c0c0003d84e10b600c0c1d0380c648100c144199484a220001c11074200a84020481103030064441403018504220081000030355030b071107079103032001844210a014078828141040c10700341d00c0001041c000c240c0044450004281a0520741e03401103000701c400161081d402402102d0407958017501900d03607060a912244024415202c036441503a8200100081e1541c08009480c000d181d40b402510160404e2000701012002040328681440445503040026036100400c5990054025000701c83d00d0740d60041c5a80c212800c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 23604907 1250 23603657 23603663
    0x1060f06020105040c050105040303050a140405041a130606170403021207030c0201020601090614040b040e0d0203030a150b1903060305120903120403020d02100c0c090507080703090b1b07 82
    0x22040003034035550542140b80581c0c05180f000e0000c68550004454522840c04050003060040015603801752088010ba45178452090301e03a8280303600c070300004090354070001d000139452003000007060480c81c1000302511014110078080000610b080340141289814600c607440440701400081c05050007480100700b81403000868036601c003100d14001c1e003070440c040010b070b0041c81400700201d499042c600ca1a07041da203200003444444103064041202900c0c252340c04a410540b10185d009100104226141c4200c4054015546030b00e0000c0b2040e04407a008100721001c06000681008041590411a111030003400c3c0c2105030100c5001d015809403903d03078001030091181c444541031411006020f03060206086003a159011002b00200109000c0c0e804081c0d40120f545450b50018030300466030003a06040340c20600b110748a50340b19503d107400c055100100c11f41d2290304120307840d58000b0301560301c1401814100f1490313080d0745a024103804000e10344c2e65003180010031401360041ea0b2056031080c40d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 23606157 1250 23604907 23604929
    0xd0504080403032037060e2103060906030a0213020a020c0406080d0f020a06060305060f0c0a020c15040302090109060801050105030f0c01141207020607020607020c010207030807050106 81
    0x1424034080d00309600900c8240e00140d454612143c4a0080c00e040042d00c2107914018a050305482c071000c41301c5101c1020131000ca80500c8410400b503110b0760381c030258583c065400082c8000c1494540360410021120403200100035050542c15255200c080d280c01c80400d9071340030129907480001c40e151803200807003c0e60054040700030f10040d01990300280a43d9880f5420fa4850000f140203200c2514a903000d4640076400129190201c1445000d06005100b41e910440740d000c800c40d11aa03040f0b8000e6041601c00da0050401c1004a03c404c0c0040d43e080340a1b58a00c41c90400c120a000751a402c6503030805118491a00f100a400d02c0d040050700d0286400078150202c0d5651400e020000741110701c250182c0e03500b08800000c040c40c021410396409404180604004680c04004484c3c0c00c1d2142519150300d0005c1c40103400840082510714491501a0000c09240c140480c020345850342c020540e01c2198007410b4984043c0c2d0340410f451044a41c0480c210f501c5404a2414601410064004046480b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 23607407 1250 23606157 23606161
    0xb0c09061b010c0909090f0f0c050604060207060f080705090f01030e120403060506062d1e090a090b0d03080a11030721020703080c07020307030204150603060b070c03170d05 76
    0x81d0065000404015003601c0790510641d440e4204001d8466850740900194007000d071203004100403881c2042d5040c03140342e40c14940d82c1c0311400601980c01640182005901c40c0c44c0a000c2a50443c04010031b001d6030b402c04440d42d1801c490000d2107440b610042901031003100c1d8140c0c020380d01030740190300365900041c01d590b940b40d00045e251100350003c8c0702c255000c9080402184079030502d0012a80365000340311406912001c50180c0084046100358080380d5814100094030a03202001030b42080c4051801d8129910b6091800301301c55000035410a11b000c500d403980c0c0c14541c1da6404603007607030a40d160500d6002580d48030005402448864866051030b0030001c108080c10b40d001e0781a5006c6404681901042c040b8603802d10204e0007040300003008621940003140e050443c01010f810311500c000c00b03d9034866201ea002c54103403240d0f2034031444022084c00007072006075014003070390f000781070703040c003254206006c0341c4812a110383c0910029022038181c40041426408040032104e58401c8240144054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 23608657 1250 23607407 23607457
    0xf060a11030a0c050c12030a110a080307080a1b02030a0c0614040b060102150f040209090c0301060801020c0c180a05040c030614040213020705150907080f060105011106040b0c0906 79
    0x24802c1d070f04440c02d01481082070001d00e0b180c1c2c604041c0386001d000441c00c154a0240a646010104200340550300c2030451240c00200c52a000718494426603944a825042001007107013940c14040f90709007800d2074128040c50341d40d400000c1e500209203a143c0079010b900780c0d0034944001c00c0407206100da81d202c100100001e02c403141440ca4010078003079003201d4030010100c403140c2d0300038401d40b1410001c591920200700989000312000b90000c5da03107800d0f100080300600000b42103030482e511080175650007007180c000c0b00c0001d026203065210192180e003030300042c205c0c00f11540000140210209a0f664010805120300c40031801301440d48107030204840700c0401007907414800120340491250f4070315151000400a107009403545945d01900030a10b40c00c000c110390b620400020440c000034802c0d084001003100d0100041515404540041c0840794100030004101140d94101080164030030428080080c020b02c2c001c0340d11180110b802d98581d0400400114507100c1c2152070211107200038a80900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 23609907 1250 23608657 23608667
    0x1311130b041403060118090201030e0f010b01180621090c0e0105040506060f090d03020c1815040c0f03020a020712060b0906030c0d03030e011503030206040506070e0f060a11030a 78
    0x2d03240c0031510000001042d80406507505002d006444115400c170108501156842c0c0222880303c2c8141030210b10142040c1030a490201d00d020100c0d05a9119030040c1d1055800041c9000c041004071341803491030341000000340c4403000d100380d4052365050708103900c588080941d0007514020381c080180e804a941d24481300c240d4017420b01405100c0c520f4980071558038070300b09046825401841e003910b420304044004100502401000a9055000d01c2000725402d0359a5001c000b00200841e43c91061030411039940c110384e14010310014001c038602008412101d030021b00f004907a0140c0d103000350b40c1e814035010481c1030010303e502c54003900306203102a02c100603050300100e219007016a10140d05035688020540d4030b03010325030303c0b64010001718600c901291007504103000012540c800030400c858481c0000a1019082d4019401604202d041c0b100300003082c003405410206524100c0b040c0c0700020b0005624a100400da18480c850015400d020140030380c942c50b2581c04998141e0740c440d0300340301000d85 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 23611157 1250 23609907 23609909
    0x705040806090304060f0804060603020a120309050409020102030412050a060c05031503010908030109201201031509020f06030414010c031a01080f010909050a0b04050a020f01030b1311130b04 84
    0x80c012240000c8801800005030b801311751503907075034010a042240007521212400f8100b035a070551661404400b50711131325415801003010109110f02c5d001d0506008100c0049900000d2055041042203005030381c0c000700782d03810f03100c5194010803074584c94070300740749000d00d81480140805c1c180342d0700b03509080d04940070f9403151551680d00382030b20380400c041500321580f840e40100028824401400080c10380d900018440003200818045030541928014080c2c100400103e403a2aa40700144200301c030180a071540c4651a135024448907945600107400c10307082f0381c0343d94083c2c02d0103c0064140201e1500741d00580c00f02d603008200101c80c10100030041c00c10101400300b0701050b101068055480f440d04188202000408240e842c1d084c50f08910203800c0a075410740d898801c0020310804204804040d500640c400d00040c4660f018600c1030121400c0c1402200d4181490303d089903010341c40301180d4081d8840e640500042404051944c203901d03004520f01c00b0740f901502d41000ca00310768500001c2c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 23612407 1250 23611157 23611169
    0x150203030403030c0c0c0b090a0306060308250503030c030a02090402070309050f0d030207090506030a05160f0b0a020307110109080d0e0306090705010504330305040c061103090105031509070504 85
    0x100103e0080c070405e07a189424900c0060401034041020001e481091001c2d1592890042548100350ba503920344400313450060300300b0350b014580006c101c07114280c4000b17103015240d40c00008144a01840d2982500c2c0c1c00001d0200540c994008001800c1c1080c641c1101c400601c002c1c0215217030b40c41c0342802028412940551802185403280f44610742c60714030300308025107a16a005000c12400c0040742d1018000107000c035600352160040d0100090b60a00a000c513220240013640400c62800f009480301c0d41280e805030b03810000410410441d170390702200303d403051a0041c00050300c1140700d4004032542d510990200f02d06000303644038400400d0344014561140c42d0202c04407880360302d03003110007910350a2622900b400319400f004101322904200488480e40d01c00b4040d1420b95000c8024031030a6a2000d03454040025500c01c204020403d00b05140b0000c0e10307640c0340402d034602e1a400742070382e64415544920706001000c400603001d1301131420b07442190200038000e07100e5130424a03805051030300b00340140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 23613657 1250 23612407 23612411
    0x9060c0606130506030309010c050a0f0803100b0f09010810080102030a0204051509031c03110a0305041b060905040207050c0303042c150103020705190309090b041e020306030715020303040303 84
    0x900c1c2d1006180c0501406000018007035032515444400640c2c003903402d140111010300800d01890b010445201e62801d40a0107409403640d24a0b00da200d00031610559001294107807020b101c981032403d040e0003a070340c160000782401030190302c4494160b030107104070764400c1919600000410030082d0153300030344200e5131f0646a203c04407007049000d2019001d440d15064055000e0454118005003c0ca8002540b144a050000b4040c0c4001d0b100c03207040d80081c08110111b82c0711801d1104024066035030b406a403c07907400040082c0e0800800400b582c3e403d1140d18802c170f401080c59010300c28144008200d500d40141202d90b80e03030707884084c8850f8041c0759441c54042002002030302d450800c1c0e070000c4e510920000c1c1c20000c00043c040c00640080d004100c0c1501e151280042c840d1080c0c00520218640324003e48413585424030b490307c180240c841c0309800c5030145042041c450380b079201481c061201d1074400301016840e665000003281c81e01203158409600c0c0250180c0b640c109076000300055001d11300907902 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 23614907 1250 23613657 23613679
    0xd0c050103181a040317071d0303181203040b0c0607090b030106050901051308010e0f060106110a060b030c0303030f060a0603060b030403030c09181b09150305040201030209060c0606 80
    0x448140310115103014100801044105506900e83c3c1c0712558800d1090070404d01c14000c0e056026a200000c5a0003404100d00154070001412180b00304c0754804003c5004514200c2da0301c2c481040c0749010f038401c6005030304061840c5a01c810502c2614054141e2003013450b260310b01c05a0140d51030a041d40c054010422144010581c43c1600c01228141c540c1c0d1b440d51450076692030011079645c0d00038040201c000030190710120340c0f40001e02130903a030f18841c2c60080207921017042c0c4042c148032060b4048400c1c0628180042e174440000314035050119000080040d81e06c3c0f1040c0864104101c40024580c14000081080300d4200301041f4a40500000c0e6100342c0055101c440c00d03000c03241d180c00b030404c024200340002000a480303078000d100c42442516009810580d1070400281e01040c0700d0b64400c40c1500c0e002e018001000f1072400c40195819850328803031403403804009076417214201440c201099140c01c00102964001c0d0102d5070032a4016050750382d01d103402d02080351070701c03c00d403165882180f45c6d0107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 23616157 1250 23614907 23614931
    0x307091e0b010c0203031c110408060a0f150e0a09050303010f0f081501030602030405070302030102030c09030c0d080412030201021215030607030507140a0905040912021608071505090d0c050103 85
    0x98200c0c1c0e05503015004514200c3d41e1071f56003080d100e840c1842c01040d40c40d14004480e400920b07014100412410000344490308000c6241d109852508581100007868100000b901e4807031804804100e9000c0004000c094aa5007800405007220706400b901a200c000000501c00c003500410303408540c1000c06030070055131178540d03a030b803100348580359061102020070050001c580254000c6401a02c0f401c102c500144da00c1d8046801d980040300c10502648001c0791000d44e40c10300f4490f01c04124000c951500c205100341e43d818919010340d010f903002c032680d5a051041014002d5046a1501d43d4100e041001440d040e15019a800ba0400e2050701038000c1001003008280a40101c0d8003502c80d41d215550800901084051b44d42c01c0700007480b04010000303400291546840c800c2c0c00c115401200a211070104213240a0f14004860141034500c0103044e4040200c8200420801c1c15203182d00d81c0d00da14031552003411034490084d5104c5580c02525039210804009061101c201161000e8a0500c035000c40c00c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 23617407 1250 23616157 23616167
    0xe1c111003060b0a0f020102130f0f080604050a0308070207080712030f020c010c0204020a02011806060f06050315060304020d0503120702071418060418050102030406050604020a1205060307091e0b01 87
    0xb01c0f40c28000b00c0d0600900e4044c81c0900e00520940c1c00c0c41c800141440064000005c81c3d0480703502c09410707800130000a01c5600c4031001a0310142c1980001407505040c680d480750b03500c40c00070002400f08440032011540b058424428540140b40300d10840f40e00c2510b54004540603030103c4001c902203440c0fa000c0000090001c0303101c400c1401e05071503203540e5038081d0f002c2c44081d51240c001d9a085560f00c000c0701070789074040102008050f000700f100054090424055440e602125048541440000d00801c104040b920b520390305c0300d010035215141c50751641d1002c0307004400540401015030201040c02d101c0e1001c411031180c451006642102d0481c4d0b07491131607900801394200c4003070f04070340c074000304035401030700c82c690940c01c070101810000328284200c08512003942d5034081184c181e5000014403042c480b65004041d000201220210f141c6184c8441c00742001c413902145c2e00b04c0c2901c403170000d00c0c030796402d1040300c0080445a40902859000202d03118000c084240750500c918a03051a901c100c0d4401c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 23618657 1250 23617407 23617409
    0x2d0c0305060904020d06020d0e01150609030c06030f0b040603030c0b0105040e0307032105041203050601050901120f06031b030611070b0f1b1602040b0d02100e1c11100306 75
    0x6402c2041d140c80d540c0a002440085160a4a54036001c108081518445102d2482c000b1024030000a441d070140f80c00c0c0c0e00040690740f041d41040f8032a4018004505091180012240541400904078000e07052400142465030b5949900c245400f0000051603001a050075820f4401c0141015a070380716001c01040390560300c602d407a554000e100c050002802100c800341d1500c020303a65460390504a8071090141c500c100d50840d5580021517141e910385801d0b0003640e0f040482424541d007001c82d4000001c0c9034020243c01200c1c40c42d00c031760445418040641c4084091600020f0300b050401188109a91584084c84111411460b00b10350f0716070991a482500c0c14035610200701c204984551071101a402c0c4080c02e000c030754500047c22100c080041400402030080c0b25814030300c41501e07500401c0220740310075090500411031134207090700590310b503a5240111881800d00c0f20660200340003040e10040b061800720b18040000da805030031301a0416201d10742110807602e0b4808001d8074282207042c0c0e201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 23619907 1250 23618657 23618659
    0x308042402070501030209120d050702030f0607020307031d040f0626030a0302090102160e010609081b01050d020904090605010305060705160201081503010515130204031e02042d0c030506 82
    0x4600c0040c00f0542c860b070000c0106000c014610345c1d0b00ba040203659030a008070448460089440090403004608092103000d82d403180d4000030704035518201c14081d48038170a4500040400c880003960f07066102c441caa12494a620161003001860141c09028004110500804180071010440d00d42000d11500c0e0f0303600c00b90100806181060b1505a055005e901300d10308180c15030081c0445070f030b9104198204500105070380740f1100c1995240000c09044043c043e004203002c1c6c0c005070400d980a420448200403034100c2803170a0f07a80c40031005043e0009007d071b4900142d00906000540082c0700b013540202c0d058a00444c152080b07074850311400e540d103205105541c6821107055190720055070040b0309059000c490409400440260070002a0848408031a9040030100c4540b602003181400b043c80c01400001c44070444c90541140c9a03004420005c0e8a105203007500b100d0b40108541350743d04410311a440c032194010071030131054641e4018480030124484107514144d000c440140c0320703010303280c02000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 23621157 1250 23619907 23619913
    0x90b04060323030405091501080709060206070c030216081605010810030b090a2a080705011706130c08150d02090a050402040905070807080f0d05030c030406060506040308042402 78
    0x10300920700d90703041c85031942c001c1a000a003c0040c0a899021105105e0300d00c41c03d0001c2101003103130001d020030102501e0441003142c44038050000d075400145039034015445050000c410a410300c1c040346032241c01c545030114100a580009101013000842c081c50454061843e0350264840004403442e420844a001d94541303800c10400100762580006504900c1540c2038503019941038030f0712040143c0c00c00880c01000000c500c1001442c00c00050000503015a0004d400887d242c500005d10714040d06400b12140010b0801052041ea50004a451070640c0442d0601c02b00c1d04400b8080d10001e0116000b003032a48078280040b129250404410b03405540c01840c600950329860034040092500800403604030369174640301c102007901040850020721300c00b00203050203410310a0150409041e2504840c241e480f454140b000030360000181c079130003040c204015440b6a00e40c02d100016015070f034402c5811810006000c001c0c0452400108195a0304d4002c0c5101054520344100c092124a565000160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 23622407 1250 23621157 23621183
    0x2090604050d050705090415050a050402012c0306091f06030201090b0a0e090103050303070e010201050618090a1a010609120209070e04090206120106021c09030f02040204090e010501090b040603 85
    0x32801e40c2d071034510b090060040740c0c051501c8101103040e013642900c040c1c6607001070f40300e001603042440c02801e60154500d0400e0003141001d034000b824403c0c4220144809510814000c2242c02c2020300c0c041903603000804450301410110343c05901c40c4080d00c010540750040c00c0494601c9440d6010307040c110b950603949c144105140c000b0280c1c1542040c41100100003000c215240345694041343c0d18040c5002e00c000c0c580d0307410840c0d005030010004032512810741e4142020032440e982c8514075034646050380200d100b099075030aa58a420001010002449c0080354812088000b20752002c0b18140d0f0807640714801d0554840003101240500080001e41c4400c6001c00900c01902c6800c40015045001c0c00c00b007036425003580021007a42000c4d058642070101d10004201e850341c1000400d200090411981d002a58400300c010300c280300c6808003038071010401a00c8411501c440d0704031001030504040401c40e480e503215440f0b0281c0028801c0075a5681021101c644514261251008482d4000020180d40e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 23623657 1250 23622407 23622409
    0x30806150304170d090606050a08010618020f090904080307030b0111030307030b1c11040507050c0607050f0d0608010506030d03060f092301060819020906040902160501110c100209060405 82
    0x21403101a0003043c120802c1c0721168401c86a4050344007110300c00e05001c20901c0c2030406008100307145034498021a17040c40420065820314541442900c0031002001d0390380ca9000e071801c02148207029105810510107410041480074010141d4040c1081d66000c1c0030040c0858011601e030405400400c4c12600f0400c0400c031458004e030b11160420303401610480c102200c8200710000228950070540e0020700120052079680b9051003420381c0070b24130b810311030b0070440c000413142e640750001403540080c402c0000741c8202030b181c00015207891158070b4005000058407003445501078071094030f0a03402403080003000311105d80240110800d0ba10345034000e030591840c1c4a802c0b0003410f504849031506c0402d5003084c4918030700e14182c250182c8150780b0707081c0413803c04002c009192002e00410300000351050003140956920717901103404440c095178002d40c42d1550740d0612507031030314003400c000c020f076207000b56108000814402030581e40c14688195145460000d214005070721800707d003168003207010402448a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 23624907 1250 23623657 23623673
    0x60105091302030f120403030801080609030403030f05130306020c0d020114130c0305060a060f0915030b061207030b0105010329100909020a0206010f08030903070b0c01020d02070f030806150304 85
    0x201c42e00007030850312207800c80c41141d41000d115441207020070600080520505401c8003c1600401900c00104941d1a000e9262a107a0095010042c1041881d260000034a07100e0070a940342d680c1a0701180c006a42e691400c54002d500a074524082406040000c042c03050040c440c22050a800c2c0450b240300c0d66031104001020046104204d07a80840703c2030210104a003040418801d5101813070014659040120091075102503900c0025442e040007025031340c0345090740840c02140c0d40f0858880d10303619040c00003203030324030f44400030701c110f00c100503000081c044102c030b00700c0c12600c0a0720304101000010140c0008200080041c4080398060581c078051810701d28003605511040d031602500080c0c540c00c044013660302c52410701d00182d00940c018000c41818008490041000c032000354900364400d00429121b13040c6108071490000c011130101a040000c2d01128054605500210356a019a00d400301c10740e10300100580004004200199007800c00c0a14144841b00702c0b40202d085036500d80e20300324 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 23626157 1250 23624907 23624941
    0x501090207020f10080f0a02070807081e0c0a0b07030605060c0d0801050117040221030a0e03240601030c02010f020a080f0603030a0512090703060905030702040c03150b090a03021809060906010509 86
    0x286238200f04483c00705421001401c40c03580310b03550540da00d0703003c2c1c07010300502c19010f00c00655080042000305810100095143c0751954400c1c0221120b0b500c0c1d0030241c0c014641780c2d003c0f40c0c0003d000140b0074200d0202051002989600b030712642c600b0b07601e9a004588903000c80c1021032150140c0350119000d80350005402003d040303072a142407500301c6010030450850b04203d4144010542c54030010b016072505008203481c210141044041c0b40049888816031541701601d5241071607565500461194804c0d000300c00f495114600c190b590300101c0340014091171084031031810405446010071080d103030110490302c4070b51441c2d03515401e1403150107400482e0700010340321007007902c15020000001001d40c05031030b2416014401031500c500685c010700080c0c1350342010700c20405213040340e40000d1505540290f0141c0702c1800d601e680307900b500004207104400c0e80d0400780d4090452845059246040043c1c1403140040740240c480a4803440310507a60f442c028018241d1020702640040e015440d107000b051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 23627407 1250 23626157 23626171
    0x11060709060302180a0e0f0903120403030504020a03020406080c0108011208040317071a040302010b01030b032503060609021909060c03030b030a0c0905060a0806090a0209090f010501090207020f10080f 88
    0x14010740d0200c0005170840a01d41c824590010b009040060321303814500425030000303118018524000b0071492030321059200400007010702d95546e0100c0c0a64988948500107540e0140080001640702c0000680d0342400155440c0020702d03000000c00c11016a1076092541b44c0d01c43d4440d4105400e603582c4280d00d149818269210503001e000c02c0000c250791540e2400c00c040b452448070201d09040c10020309617141054040d06143c10100c0389500c03501c00040c111000b1015200459032040c59a441c820312903600d13070020f0003a604109001c90306501c59401007060b4404150780310301b852010a800d40b181384070f61290101288045804902007402604810812400141540d10641143e5940f1940403410f030171005601d0795500c100001c0c1d0a1051410b03000c3c1503090300420040c43c01140480e81c0da03001400081c0200995008203425503020046840301c0c000c0c21000b888190b8665960000035000040181c0c85001c584000108078101270005084511082d5107c0100c2d03aa20089100034880c003034196 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 23628657 1250 23627407 23627437
    0xb010b0a0c06020d0603060b010e0d0204050601030b030f010501080c150409020d060306051e06040b0904060207050a0c180c050307020c0d0507080d09080105070509011d01020c060301060201090311060709060302 92
    0x121000030b4403480200343c040c4100750300103250341c29802c0020880d40c4440003541400b0b8205041c045030f5a41039584510a03038100c031301240d05c0d130314140102c02030012003442a4240c40348820304e5424050640115050710260b4046030b039040c60341810040341071040c00880001403010841404034110341c0c0c0040a840c4650400418440d0b030300d503150001c0751001c441002519040400440554051088a0340c003ca8201c909218140215001032103468001e0f1006084943c005030f06420802c060101c61860b030b4100c421901e1195981007a12484884c80c2e2241d00b2680c603201070240030038082e00940e80610740300c0d0f00500303440d40c2c103400f44680b80700c07080703001c0da80d912130040000b8040c00c4c01c104c0b61342d4401080d581d40174420f140007482ca00751130002d086181403240620021842d070340e001c03107180e02d10503016000e11400c084081c0141d0400c804205413540000c070000000c1941d6405400030340010b0700c640e0b035818034000d004003248d454210070b440110008003250810005144203801030002080340e071801b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 23629907 1250 23628657 23628677
    0x903020c0d050c04060f050612060f060a200114071206091107050c030601060203070f0f0b01061d0d0c230a08070e0c030105010c0209090f12030a06120b010b0a 70
    0xd15181e040d85088885500c0300c5a40181410f040c080d48000384402e00c05850191f003000000b032600e0092004158060901d0400558a942c801040d60400d600c00b0341040d0b07841e03c254800602094205820101e904002419015040310510840c14030302c00d25880c001c1030380c0300e11608580a1a80c441e100ca0500d44480b00030030010355900c00c1d44d204168120021f541c921580c5080c80c00c1103a6a94000d10a40011004014154011003103441c0141d0048010500340c0b918503010700c1c0c94007803900c007805604900c0d0003c40c900c0e401c0300031031040148084110010b00384103c2000041000114010b000032043c160400a02e044068070b5144035050400340c4015500d9500811711b944099801600c4030b920150040100c4060980400c3d040090300c2d40061440d0305100c00030b40580904bc000034020f034000000206d0481060280880500203901035624009681113801025001035515200031460500006855075007850680c0d00303558003076028285a0300e01114031290b6000040c0e404280122118 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 23631157 1250 23629907 23629909
    0x90d021f02010501050102070602030301030b0a020a0203070b010305070905090c010906050d02091f08100f03030c080403020d2d02030a08030a1103040c0f050d030519051b0304170105040c03060903020c 88
    0x1100c03500c401560001655614040c00285010030540c408000c1d9081040140046034003114415800000369902607500c0e4030821040f803852007400005032040103400004800c000010466004851075040e040c4100e45808060320307280d02c2c807204e10501003070001c401040600e00138009490b01e1061070000506090728080814207403005010b40c1078100350005c0311802d41d0741c2c00140f0a13421900704120802501d0900c080008040280c0c000581801209100c1d40b0030440f003841110701443d80600f801210040504d0891a20b40c071103400c00401018440411869941405003191996002001440500740c2c17502e80d1106a440a405101d410b0744a41c0341d04c4c408464000218003491060741100021480d0018800340d00703840c0d40001c1d216101c002031110220f80c2c04400d941e00d080000d20f140f61a000806800c1d00c59200d80780700512080076210041110310400300c003500071108a2a41e00c501c0400400c4400d00b210400c68004040c0b9121003028408500160300c0090810b2290045130840c1401d84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 23632407 1250 23631157 23631199
    0x2120a0e01080604110c0304030b15150726030403020f0d0507060504080f0f030f0703060e0a0f0e010c0903050601050603010e010e0403020a23011802030d1107050a0303050705060705070503090d02 86
    0x9900855a50300c0007402700704000d2940d0011b580019a41c0c0c1e180f060010351130000e11001c40a410304103e560000c9410b20620110b0a87d1880003c01281c040089100204880071700703810031613050700035006900c01521084804903d68020051983c1c88034904103240ea180001010040c109403442a0305011101603081e00c0c1000305105e25940e6003a07034807483d00000d445180c18004255108160a1000801500521503440703600004241c0000c0f0740c0104000141000740380d5455102c2d100e40c01c0a03072950240c0e4014100c1c6d026280500281c5075640e890303401b8404030340300a01c02c0d0352a00301074500401c001d210218035281c100d4131910680f0a8200162035841c030080b92060b03409100e10a0181203680790720300740310382e00010402e4450940000b107a41c001a072a003101d07000b01424000c0b29610020803c20038450a805401c0003042811003a850f030900401d80e030803800d400c851511031400421042e5001e6410340d20401d038424004e500d00052842070164010010400301e806c034240b003202d403400740145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 23633657 1250 23632407 23632417
    0x60c0b090109050d1b1a040c08010b010c0201140904050c0310061106041101050c030304030503061f020d05090d0f060e0d140706020a0507020619030b0609010e041a0a0b030702120a0e0108060411 85
    0x40c3c4c0f011241401c7c182056040e4090903801192a030b071400c6c00c90462640c208a03c8540e264090800c1e040d8058184030711400d500c100742e8025400361904081145c10700c9414091341c01140e003041d0001178691140401c1d5507600c80c0b442418000c0d40b03c0c100040c001041c280c00e1060549042c50000d041840710354281d46550800e58003103000c17410110401000c0c1c10002030a0f14400c40c41d051341e180580c08648003a4903440c030f00340e8000421000145e9950951107403100c142a19500c400031015403206410210b0040c811410041054000c41c103070801c2c03091203090210290300030100240e16040c5503595202c001e41c030046101051110910a10700569196070140221003a40501104940250000201224110224107203e03032814040d8070341e0741c0d038040009130700c129041d90300285030180030a841c2000035030700e02e080c0d034025007640021038001250f6015500039100c603000c403803200c140411803011a0152080d07034000030f828a03000917210b602c150000c03600030402030000607200110b42051407032a030103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 23634907 1250 23633657 23633693
    0x11070201270321030b0402041d04020616050102030405070602060615250821011208090a03051c0201050106020604031713020a061d0f090705031b0301060c0b090109050d1b 75
    0x100c3d000f440660140104503a2030740c202ca0442c81c203070803c4c105070203000b80c980d502c403140c4402c0383c00201107468100c0ac0f6483d400c80d1681000c2c00faa00d40c60943d020798011a0102d6550144010000d001400016102d0046500800c3c04207661000c2c86010600d41280290092940001c256948420950302d0007440040c011660307555101d45000785410202e260354013842111015400401c0040d0100c007644d89040e07070100b10256035002880014242c6400b9400c0070b4498000c1d90280311004000c01c0e040d54081c56650002d01131a03981d00026070f01ca86c0100c4000e40440d070a51050082d140714240307603541c40950218040c64040564010440c55110743e005840070502c3c0c10700d00500e090314507540e0401d8507800c403034403940742081c840070409100024100500303010010003c40c15140700c000c1903001805406001c1b030744075a0354110040840306584c1043c0c621426060204040040c1802007000341a040001003400800100c000c40d10303061003030018480000f513105010700040001c1c0a2b0b013820f102d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 23636157 1250 23634907 23634953
    0x160308040201180803030c0c0a061515020a050606010c030c0b070503070207080a0510050702120304050102030106030609020c07150e030601090b09090d0f0e010509030d0909110702012703 82
    0x90540700142110340c03041032282c40003992060801141100004480d03006030070b01c2c5101d031544d8540c0c158a1902c030115500422581c18503e0181d60410100c0d07401d01100c000b410400303003038000743d4003d9865035140e19003d4800d40152002840d20350240d0080300c0e68074800d103001100d0202c981c69250b8032407401c1c0c80304e0b00024800070a1250080e8104010700140410038040c0080d441c09680d601e07900c504c140c2d101c65605840d180042e00c0540280604d200121540079202d58901d041e1410354000e40c82405144003003450107402051000c4240700341c0d0010803101c1c0083c9841070a20060b03424082c9810398082c10842e8000c1d2910b000d45050012600030510801c01044800d00c0c4010040e01d0007004001030b8490b4010000031801039844000000c0c1c0300e800d81081c014481c0340100403100f600c182044560107105134041c0c0d003003031640811803400b00c900700c0700c1c108445250311019001c0c41c46070170400782c0040c0301054501c2c5000346d900300003408130a0f0014600395180e503039640c864200003040b8582001e41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 23637407 1250 23636157 23636161
    0x303060d21031a010207080705090a06080712120906050d050604021603030614010503090d1413030506070212090f06160b090d2712030c0605150a09060501020304050d050102160308 79
    0x41c007081a030100f480424005003401764102820f1903030302ca0b400d10030180300d60741380f1020400a0ba900da1106010380308890030f441c01a0b0715180c1c2c036001040c00c25405c80e0903421086454102c3c41c451140c00040d5207140c0d88040c0f81c091b85400100103000003400c0d045e40030341c0c01c00464a0341954100020a40c600c03035103020528600c1d104100700031808254103141807000801c2082550310f0080340725020b0130b031941005160a10060300349410b074000c8440600d040200407002005102d800a000d900c5103185900300c80b1099049011201e0302d0044841c540c1d0441d070101d417115250f251803005883d0b4440c40c54002c0c6802041500c40e84201042641c403134007180c001c1c08075102c0180d40054407515049180307646442071350f80800c041050603946c7c490240c003131240b00b5881c0704140c07090880c18922a00080d0501a90800860480d5900030740b0f0121442402d1403078000a161100f40900d8085880507000b65060078038180902017000b140307000c1202c095508100261000040782010107505029641b015118 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 23638657 1250 23637407 23637431
    0x3180114180c03030a0e0d05070b0301060c0b061518040209060706020403020108010b0702030703140f010509061f030b0a1104080a08040905090a0c151713050c0d050303060d2103 78
    0xc0b65000c14900e002c0d40003080158001034000c4041d02c116501528007060240307460900c03508181084d003003151025400000054410380c40405014191b0050002c0c80c1203444180420003c0b5010088c10800347d1401c1c0b0031004a0280100c010580c0f20700a40050314102e03034540080d0403075010100840310070380d000c1024019968881c82c000e001d0400d01d140da501e80761342500000c2d80ea03040d44c84010000c8262999841200d1030501c0b201c182004014004d03c244d0402111040e03c41804992250082c1401c0107952510f456140e0000708070ba0f0011141400760300e81c030701d0903405008a4054078200c20b0007044009081001040481445401184090b0b140d41c02d0940d018103980000c0c1a400183e0701035010403010070462031542040b070b038005003c0031029143ea00140c0b28a948449105070282c1d04c10200403901011690301c600d11f51151094900444920042107a004880700000e0600d50051001074041e00b0019400600359014a00713001003201e0b04800554160703800000c01000940340c2c100c0b9501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 23639907 1250 23638657 23638663
    0xf03050d020d17010b0708070204020a0e01110c1e0105090a0b0406090e150d02010201110a0206010e010b070525050603040602070c090204120809040f05131202120318011418 76
    0x2d010342c1c81d1011000043c0300d100fa59480d0103002e515100d01000071110100021201110310b010f50150040d5201c00304004040d103400702c280303000c030b0100702545130399086524040703060012107600801c150940c0d0601400710090b1182440c0c001d05010003041229103d41d141e1195100420201c60b210380d94070705010005081c070049502165800703400b04180010300c3c00c40d80c008010355000740c8203248102003600040303014220483c2022044240040d443c14502c2c2d010a582d41650346c0d0008138601666600301c1c1381090302c52260090019040900c0e409000c01032165000390310100ca4006890312504c40d000a070159205545c01c641942c0d000900404114203488404018203018804509143c5030841000d0b41d0884044000c01c803440005107868907542d2540508039107040c0c0e8008101c540340441c080681d0440d5880143d82c0e1183c1c92014181d001e100149450028140400c043c2c1562104400d4141c08010448106041d5484e8402100c4806960100350310640f40f28000c850b0325510b010011341 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 23641157 1250 23639907 23639923
    0x80301031205090d0303020309070308040f030209090c01020a02090c0403060f06140117010b0901050c030d0504170903070e0603010e010f0605040f091208040c0305061608060d0c0506130f03050d02 86
    0x9010040c030003000c1d140d440e111160b04c800e405040160b503aa03907a000150a01001d80c000600400000c140441d82030700b0321a0217401d8038400c0e150a1040d032520258160b46440c0f804d00700340185e110551600060600050103a001040002c000342003a49070f507140406d0310150612102210717507071042000720320b04011405200c01800c0c2440c01c4a00402120100700007014011402c1480340050141e016921401c225051483d400c4166034440001b05c403208003038142a0b030306a5514070780ca65a600699100012505080001001440d0b4107140c0342c4003000341c8000409840e451b5503920340540f0104000c0c00390702c5260755100c5000030401e0034030041008491514040751440d038600803551001550310113075040b100c505800c00d8500f6030359514261000c040d05401c0100b86009480038400c03c590307103e0103510a220152a0460640d580074144a0203200b581310140600c0800c0d08100110705180000700480c1c642811507151454581e41d0030444c0801c4c0d68006c55842d4030140380c100815505001c1740e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 23642407 1250 23641157 23641193
    0x12030b09062202090a05130605180f040f081606050402090702121605031b03120f090c0904060b0307080303040b0907061202090f04090f05010e1c0e0d020a0308030103 73
    0x242c030b820b02d00c180002c18448048428032040307500254400c0c20355250030300c400080c4001814126408145180780b80640781c0c40c407600340102000111500d0b51100040010b1203000042094485682d9546801904150300c3c1c0c0203851030881048002c502c40074010300303016458060030340483c440c100f620511521980040c4400d0854002d400e9030b500684040f01101e44010302e40b2030355400070b0070900307219003944030708010b07078510303a41409840a04400100140c07941c141000088100d03540e03019140188024112001c0b17029400c0120750041e1841d00041c0e95421034000c0e8400240008a000800d2078110242c110403c10b070310100420040004c040390351a8840014800391429500d00803000e40700140c1d044107104003e4010403885555190345c040010802c40081090000000c242408815402e004a0940381c030350070708458088990001030142d40795081e001d1102c407aa41c0d4010100c0c2c0c0f00346084009a4032120b1140941c000d80d0b0340560300c3c40078500940240b40d0f25490f600d00900d00d901d07002c040c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 23643657 1250 23642407 23642419
    0x9010605090102031e0d0504050f07090603080405040c031415030105090d0c03050313050610150f050319020705010f020a08010603090b0105010c03110d030e070503010908030103080a0c12030b0906 86
    0x20070704070b903400f0003940c0c614035954040d1114600620310050380c078000e1301880d4044500e0b040410051282c006003a03002840034a081d43c0001d500d0700030460a890076030001501340c2c98100020400e0b0308065010703c03031101641ca00049e81d071840c201d003c56000c0c416100400d00031043c200c1d1156a190a00c14035802c200e07000c0050100e981c070317510043d00d25809090083d0a006c1d02100080c584441d0240c44410705600000340c5007a85071503420000d10198500403040007034200c0441d140c0c554006d200d003c02c4007070743c0e0301ca8500303680d5100045d01d0f100d94212103a0189540078402040021804d005580054041401c0944c5070b4443d00700080150005a00070b0041600300180403000c03070000380f0328905640d820301e4540422415400d040d2590550001c2c030350124414140b8070002194568005103050144400b540e2005541307200b01800c0c7c0f500000090203d1030100010030004032000000c3c11440000d0401781110313003103620351914070709407081a1401300e910f505019150746003801483d0780c0a401210300d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 23644907 1250 23643657 23643667
    0x3020c100e150f0c0304021c0f1205070308010e060f040212010302120d0906050d06210c140102030d0905070b0a0908012313021216080105010605070f0b04020a0518040209010605 78
    0x54203220340c01805440f002c1380c00001203000c0d03444503001c841da03000040c00c6c0794004140c2c51600303138200b2451131001c0c2c0c0d2007540303050b0365040a84910b04544c0c1050701961500e40c00d908104140704000405050a07500201c4444110383c0f9031585d0001d8580d03074103840e8030400c0540c510300602c8080502d603078180b180c6812801030010282d4000f010b030300c02d0b1502d600c1e060317889800402e44c1c10010420340c0c0191f01d140003006603c00c1210040e03030b00c0c0d1101c0c5202d030803981100ea0b603ca0840b4142a40c9042007800b50301705004080c10055250300081d201c5d400b6204440c00d550360342a003e00e10758003145102000072440e240c01d002c1c040f000d000d1050695801103070032060244c88144980f0448024240e9042c40f00d41c0040c0d14259952200c20004205100080d240c0001c06c00080140c07010b09880b920742c0f55401c01c000040c046004006480c1c000e0717004030007184600034691f6000401035000740103d0740400109004105a21001e0714900180b41000b280001800d00780100302c001041680708008000342000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 23646157 1250 23644907 23644921
    0x402040503031e071e030e01050405150706060e09060108010b090c0301030212071a070201081015050703030f0c0e0103140403090b0703020c090c040e0f01050114030703020c100e15 79
    0x31a0b00fa03040c151408448800b61005464440c8a04c01d0302400c980400c0000c00703100303144c0c00401702d03800b0f119403994019658a86c0040d541c034020ba12900382c0c020300c40501a03161a800340000c0c0f500364403800c0d001079001c0e00c070040403102d00000d80310003159a0010b8014815424248903100b0050012284100c10386410b940214151105000090044c1c0941d1840e0903507030020040c00024241c5405104842d4403501101c032480d40220505034005800301021030700d100c101138801400d9030301c0004410074149541c48159200d52148108408055481c180741c1403032010f52007441900f00c0141d584007004140c050004003174401d50850790240c80b0743c24080c000066003120300041110900d03480b20b40c41e0b419a05042e42020190007440d50441c1c49076041140b071110010080003560100c1d50000c049403101d5500c914820002d000f542e000c100c00303804504078031400802035036002c01c4603e4050b284c840c1001e0514107010580722690310094803403a000020a00601c0302c0c2c4140814583c096020f0b1400407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 23647407 1250 23646157 23646163
    0x3200f0705060705010e0708011e0209150f04081c12020307020c1c08030f06030601150f030902040e0a05060a0b10050f0901020a0b0c190314040201030b0f1e0f0402040503 75
    0x1100715072042c0700000e40601000020b40200700c1076070055040d509459030300d4200034003800b17000700030820400b088000d0802000240c4266003848001400605007001205000c0225074840913441e10322070300c00d00c40003801440421a80208002060b5104039629050801406903400c80c8041c071942c900520401c28001e90014909021042c201c41003840b140c0c0803140d4541c00314007080c0261003044004200072100e00c0070b400d41400341e0700c242d040391066070b6110440503c4402007002c04000070804001c10070b506100e900b00300107060006000003114802246c88078509100d00d60100d506811110410040312400c0c8921801d680058600c0d020000d440e140c010a103104901c17100e018464040340e100303420b91080000300b64581d07104d03003070114600303150b115018545c100310380004444680d0241c3c000e95034801d01411030080c404210304032881d101c030381c01900a070014426090f000404440700728590780c2c0303002c150440516030822406c2d0810800c4140000c0c090028030013805507004101c1007126072400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 23648657 1250 23647407 23647409
    0x3020907080a020c071707050a0e010303181205060717060a0306050408040e0103210201091a0601020a06020a0f1701031a0c0408030418050a06050a090b01020a060903200f07 76
    0x68500030071a070340d640725540024040c030f484d4082240329416002c900200c0c07030f007140d100c2c210118086802207591802006025502801902e0207003a0b02401000000e0089010300b07044100301c00d0040009071107027544540e41c09491015a050350101050100e010b4000b080044030103d07003503521440c3c0c0b8200010925a003103600c40184a25528800a400e110000d0250b4000d454181114019035940b400c06005104845004034520b410100b2410704090051061120b110b6000c1d4900c18204440394000d55440001400107040d4000c0c0a28040000c5c654801408145c455489001c04947e040800030003011001a040660f211094014004160410560741c05ca00310104821a5603569107810826402250300c20809440041804100d000031070030a080c1d5030f051400d00700100e80d81c1c038402c08103440703181c0300705900400c10000034090b1841c8c42c1c0009024010600485803280c00f65501d180c00c070740580d001640010808401080002c15103041e24418070ad2401c000d02c071031605e05032050f407a2026 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 23649907 1250 23648657 23648671
    0x20102070620060709061115070e180a0e010c1704060507090308040608070e03060403140313020603011e0602030c0c09151002010b030123010308030a180303020a0206060901030209 79
    0x41182c50b8404910340b001000d03111108003041e42c0e198201520701801d06042800f410000ca51802a21204124005110b400c910505814241e494075041c000751440102c803104a5002201c100c816030800c0300c2e103c403940c020810a40d0006105000304881821103800c1c414210800460411002841e10803002c05600144c1000002815840318401502d00765803950000b088242c0c0070030b0010700c0319042220321317214100a88921550241c3c0508140c0c0f103d1080310700030040303a01c140c0c0000900c80c5000246500485a00c0030120031100d540000d455600246e201c0c005e45e0101d0501c28105400410b0070340000c0c0380c070340021810f0040e0807075507075101d01036200c0042c0240a04030010f5080c010120a901300800d02401da10341444c841a402400f8018815059010390700707203e041e114810f40c000d0ac00343c0511a00d12a0b0380307146d0841d0f4402c04c42d584080c02c40d00c0700640740e15544d0201d4106030720407605a8401d0310010781d10000d81d28083c1c1051401803489106241140040015882d120302ca203030700000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 23651157 1250 23649907 23649917
    0x201080103020609040e060a02030712060503030a0f0e040603050a05010b030a020a1a0403020d05010504120206010b1b03040803040807080601090501050d03200102130e0610051e090301140403030510030201020706 93
    0x41c03090007140c0202062801075581f40310390b109211812001e54015401f85005a980d02a0600080a0354080d01d001c0d02c03c080d0542d20401040d01c800b48a024a002c000446142228002d1000d0340001d09451850b00f041d12960020060001081001d108171703105030360180d01030800c50905400258000301035219075001e03040b680d0001001c42010ba0304480c065035005020b489509003c0c1811402018200e6007151005448040e10240303c1c00021443c1c100d40401d61074a281c820340c241700101e10032000c0c0c1001d4041c44103010200f1182c1061000d40f018203035860045c000f03603107002000e5280180c10381c01407207860300e048014001b60710303120700d0611981d03018108001501d05062442003944400d0794401c80c254404a01890b0007003030300701e0b241d04075184131001c0c0340c0301e4888408108504820b03280500c0401c4081005000c0266403a1408210800e50010a81805040b00100e070944009895040308440780c48208410036406119141d005400704021000311810355001035a10300d618095401842 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 23652407 1250 23651157 23651167
    0x2071e14010c05011e02030105040b09010308090103020d060312050715110f0306030c0d050106060e03060f01050d0f0f030503180102070c140a0803040b0a1b0308040f060e010c0c05070603020702010801030206 91
    0x43c094100c60083c4246000150307405840300c01302c00080d0001e02641d44503a007048224034107890b0aca19822306980d0444061807420740c1010040d4000d41c4407071000300280344c84090000c0811510704416031492495142d0303c1d590040c038581007614181d0008640c501303a14000c0c40c849418034520940c1e20414244040581d03c2d150b81002920300780b95240c5081d4081c8454600204002064102108448075512003100c0620031200700754440a040790008c4ac600c0741600104103528100485280e1140168600f110301c40381600c641c2125044114160003143c000001c0c410f14a20101e41581c040b217254000f12308040b41a07490068807440d80c03103403a2155581c00740301102070f981c110f41e20000300040d4003200d44d00c070742c1c40f0980703030058100116240110f1008844280b8034014191021007240e071590b282440c0355181c1d07944404803007004030b0503500150348903c0440500000d1182011000054552203e20041c1d45401860400306401070710405005201c1200142d8005030381c02d056a41c119030082d125 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 23653657 1250 23652407 23652413
    0x5010504060c1d04020a09080f0a0501050112021e0103110c010504030221071202030f070c030b0601050313080a0212040303031a0103110d020306030c030604080403031407080702060307090e0702071e14010c 90
    0x85d144c2e48c000441344d02410031483c440b03581c00241003010601ca00002d100a03a80c0e101c0c256500170b9149400b0707401502d04008540d420401c1c044564040c1c605040002c0d0880d1405a061007e4101d090010741e542e545005000a00d9010440c8144441d401e10054005036001c442e81d4129000f00c1500070403800c01500d1400101e0700910527180c00101004600b6104c2c0254100a4402c10040c881a151301d010301010545552042c07044070310529000120f031450380000c4d52484500d601c6010040118000c4000c0c080064a100c0020030046019580c04103c92480f04160310440503c501c00d941031515004010b5100f64140c01602d00c00604000c0058403942d0301400301c5e0814014491040c0d16000d00d00030001000040350241c0300782d038025943c0f007103040075004045200b03104130741c00501110024400e800040c0303043c00c011644900c0526242d0125a62402480c03d02c07082503030340001503049000d040c0102d014040010362041501d01c007000005142c508443e84030603044404e9410800024028001c3c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 23654907 1250 23653657 23653667
    0xc0a050304030309140a0b0c040321090f1502010e010b0a230301020307021c09030506060d0618060608150121051606080403030e0c030d08090703020a0305010504060c1d04020a 77
    0x1030503410135440f50031038104800607902e0301a006c0701110700c8486c1c0800b045c0c081300e2a605032800d89500440364400010895125014020001d202004001c8841c2d4040f07150042400c00b90010b00c1c90032042a030a20000801034295280c42c07188600503807415104007166034510700341004a444100368403c02e6404020450403060300110700940560000043c4403901e07074006480d01d140c91074546140a04e140c480801c070b404440510014155a110401041241c6001410741016910a180c0041d854269020110400190007010390f0318940e0b4240401c04180180322951018216401001c2c896041c03801c00324221308203840c2107020800450fa10310030800d00300072881d2940510010340103441d9480b0710040100c40120380480001c0c1c01c1c008881428400011032000f500c0008000d402402d4522034125510700009100c161580b00751080040541c82c1c8801c140050b44c000c000100712440c160a0400646201400100403c00c050554070540c07800e98405920411003110056640d030000c51046403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 23656157 1250 23654907 23654921
    0x203040b0711040507090609180902130c1b020a0b030402010201180c030203070905010803190207151706060405010f05070203150114010f050a050a03020d0e01060f1d0c0a0503040303 80
    0x10002200054410a1240400380d000b8001e00486040c401a0f40b6501c08aa41841510620303003c503550304030a00000c0080c0c40d9441501c47e65650014104100e500099514544041d00114040d950308628040c6076000a1184002e00518614200d02e030842d03012820800c05442204131601000c0080782c1168400c1d002404503040511070215808954204030501c64151701c0228031910400c2400035032030000d8052503040703600a20255084c01c040101a400a607040e180090450082c10707400316044030340c4038110285103000d60720360b40040c0c0022200c16126078007400c5584228401d0200b04001e81e80210b00501d204010702c0c19a44501c00b034404a4584110144c6400e0710388002000480d5890b000d588000070814244ea1700000e442c0c80f228141c42510030902c0503c0041e504214440c51180250028006c014141000080340001d400140c1c3c00c50301076420900918010801c1000048606456026105030102a003030f094103100c80c0840d034601c220f050002c2804800700c00501450701a0380f1540c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 23657407 1250 23656157 23656169
    0x30709060b1306020610031b03081c05060406050303090120060403030b10110607140408010204082a060a0806040e0a0501050702010c03112a0a0303020d050610090302060901020304 79
    0xc0309998541041503000d4001c5182841c1d512294280042d503d032000980c3c44c010f03580b10518100c070900799200c40f0000c00000c8940a510407689000000041c16100180000c01c04140c81c8550258807041c5c41003a140c01501d21441181042c0050040c3d54010040b9164031a09003800c50880c1109120aa030082082e6000001070064000304824141c043e00801c454080403240361603100c80341d180c10344041c070801d00d03084c4480d844640084e1105015440c1d00c06600500810300c0e08003642c917441c0c2400c1e07170700c07640007480c10b0342103603004602c000881c4194450501401c140500b611501001044d114094640d80c2005c00c0002c0340407a0759038031554400812f850400741514079180950030103a002c3d04040c0d444000640c079149076803031034501c170748680a2500c4030f405c201403800c00500c5a401c02482c8444900f605500320840e01a120300b02000b07a191900e100382c40158460108a80c52030803503100420250241d0312440710240c60f280d1000c01039060329411102c054452203030341d004034654090368100e1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 23658657 1250 23657407 23657411
    0x1090906060302030402090a090b01030311010908070606050907090605030604111c0b01080a0c0e090711060f040b07050f0717040f09050a0b0a03170c010b060a080f0105091303030902030709 83
    0xc0341c8650305800a40c850b900030346020304c0340c1c0c0343e03000c0030b20854681c9080a8101903401006200103482000c0d00040c8210040010540c3c108d20785411001e68040d0344205c40d2680c0d02d4000300040c1c180800b00903400201410400c1700f540c07601c1800380981c80003d15103482140e070b4040001d6000f0354201aa4807540c0b0458a82c28510020440407000740b0380a11101d021600400005a080020f405075424481441c3d41e0342c13400a500100303020003404044c0c100360034445440b012a0b4403650400006101d1032a40c0505481030500e03080c801d07650300c809884081009410001510000111700c01c5a405c282d2000201c030503205c08085c44103850086030401004481c016000052801280d0042803f6400c0171030100070040495040192086c40d91100400280105429002050041018102c1d800c9010000300d01d021801e40041c96a500284040700441c0740e540c148120100d910b03824a01400040e64000541c1c102203c0d0682c8854600d08020300f00340d12414406d08545003840400000c00d000e5000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 23659907 1250 23658657 23658659
    0x70210020a08060102010e0102090d06050a0605030102070b0f060604051f0c080406020102040302031005040308011205070b04090221040b0a0c1107080703031701061706031e010c030e0304050a060e01090906 90
    0x1c00509050750f42c2c43c010340c00c143c9a80b4000d00184229041580001c00040b40c072802a034604002d8a0003d1600d6826950707008002803585081c0014080c0b140710b240803107002d180492810350801d0340944101d000b400c00380014031070360f15548000f02d00c220b0380d40d81100200746420b004440c01c081048000304071110201e400699103070150003030020f41b4822010b44903c0701c0c441c1c6401085071000c03600a400103409500400c483c500d100300291105003d401980c10140d11103014030301c182d02c507034000300380c01d0b5000035020040c0308a0140740303800781c4126944800701d040c80d84810503403c2000e801d4502150381e8503002c03580c1c6400340800a500c2180201942c0042d651215101d8880003140300c20390118550845491040400c920b20034142d9085450b024082d100340050803590f818010040c58051254001501d01d030201c0b82c80f01c0c0d00b503c07940c0c0000305100c60a03400007015550340f0070340c600c00c0794000c1c041400350344ea0320300440050703801c43d1801c2c0d51600742250040b81c00c0c1c0440c2d4000e0041d10303e4108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 23661157 1250 23659907 23659927
    0x1507020d0c0f08120a03050c0706150302010305060609010f0e040b03010e1608030301080307030f050708130311010504080a0803060406050d031106160c170f0c0c0301050112020303030a0507021002 86
    0x758204071141a403002c0030103a603510310305440f503030189001400f054080001d61000d038066844190820080e800d903906118941d540c94048910341104a800c2849440c0300b00215a40f6000f100c0d4045019540981801c01307200011340b0440404151200b0b1200041d580d428030340f41c542c071030610440c0003002403100d400d07014041616140404005040150b5150010030030080000482e4101ca010400840c1b900700b00342c03011200b0305642c804107001c01078208203103408500e0b000040c0c03081920311251959002e107517241c031a080842003000705061000920040110401c0440c0b006065034120b81e0080c2c1d13964814001500500b541d41000d40e001120316401010705501407c4017544903481011140c0c50349a0700a12828007071060083c4000511030030b00d000004a9400c0000f200d02c600c0c2070a01c0c1050340d0740b6a800714a4000100380040340c0d100f4451841145400d0042034010a40c4a00d4000c841045030042926803100034005500d813911600807500d040e10800c80c2541200480c0c2c400c54032000505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 23662407 1250 23661157 23661173
    0x90402120118060302031e01020f0d0e0d090b0a030b0f030106121209050901030f031701090b0307090501030c0302120c090a02090f0906061c240305100e07051507020d 73
    0x7004444244001030000d01e101c02c420310074002560b400400600100398140c40160032404626542025550240300c01031a04a1110103005a030041d03040c0418190660031006203000c0d4060740d41c000b0040c0154081010b80a0801203c04c401c0d518a0007040f91503440b4085030181c80180780860b0107601c0d1010004070345120003040b1111b1489034040b9880c1d0462140300b01c0300042940240340d400368030352004100103454440c1040140344242803c110200f012a444071162400345d000c01082a10765101105900d010300c1840090020154100140d50440c1c9452240e601c190100a00a00210720000048030042100c29075008000709041c03407616116214402a400800c10310707000d12018501c41c286403800100c5513100d08400b0341140e040110701a6007010201c8811041e00100780c1d41d04800001001a03158182500681003810152600c0c5140040c6885980b281850007940340c4405a841c84602081e128102c560850705035032404c3d072504001d0340342c0c1700d801e400071741c03083c441c1108004000c861 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 23663657 1250 23662407 23662409
    0xc030b0609160f05030910050106180803130302040b06040816030c0501020c010e040b040b060f04030b0f01060e090411040906050103020306060102151b120f09010c170a0b060904021201 81
    0x6840307008040d1200e9424000b4000000d50030b03808118403000c0040460b114001443d44685050704689204003c0b00035002119801c3e04494002020244075488401030b500c204002403c0080095140407899000c0002c1d8240034080207200b9915000c3c004001d80c1c1c0d95080d03501030300c00c132020341c0c02c845085003406200c01c0c014482151b0044038410001119800030400c0b400c4100c040e120081103030b01f0882044010056041542c0d031080c0e075840e1602d00d640b075400290244450148000ba610ba0450403e1307190002d00402d1019983d0a040051007403560042300d82d2001c030710658100c09542c54510340a440038104a6549410502c0c0201d11410712110741c01660480b8000c2d01680e105489103001241c444400581c1080c85054074000316007000c0714000e0604100b070310310240e48d0501c1d50010107041d90503403d440648034075071058180300000e0303001c0c452074140105030b00342400003010f01c1d0b80c842c1000b8401010420855981c1c0015507141d1140c904031145684010001c41d924120425172070781c00c20003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 23664907 1250 23663657 23663659
    0x307020705040c0c0201020d03111b0f0601050d02010507080703031e02090a05030303010b04030807050f0d02030a03050105061201060f020703140307060f0b060301031205070606030606140924030106030c030b06 92
    0x4011103210030f9030060b039003025030940690140a40e41e03035101d402e40103482c50350b00b90094001304001418000060b03c00e0840744002d814003901551520040084c645401a040303144148a402501e80050f82c00c03134120340b20380c2c0d40003020f075031503242a06040d0700030a04c28a8041d11501703403170f2403030074182c005900030514904121400a80140c44805051307076400240034911500740d00700810301c003050590002d0f14180c0d106008a81e0301018622006040030074400350b840241c1e0020411400d8107405004603405450191181810841c0d0781c04480c14201042c89403c052240004198a0044c428800d4034040c542107503881600c941d11302038031076070ba502c4000d0640b0582d24040d0a140011014007d1212928000b80214196420354551250b01001c1e0481d280501c9810008800003881d14026400254060700700011942d180001c3c2000f0010b6034188184240880030410044c0e0312510956280a2031b9441da014494940c01c022038010f04080e08080c0443d0141c207800030410819000b95441048 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 23666157 1250 23664907 23664911
    0x30041202010c08010b04060c0f020a060804020a060e010c120201090c06081006030b03030f0a020709050a06031109090d030c09050a090209031606020a0209070306030605070206060312130506031803030702070504 92
    0x102c202c000711182403080c040c000381c40c401080200030322481030219030700290049281a48080701c550018080170880d52052000c01d198000304419031900742d211000600d0f460402c450913541c0c3d140000c00210207201c008041104c000c4040718810310035481002004c0d4000017020190361111405046010100c401307080030900b103a00819041d00c81d0146149410002d80150300780134201500292640040c4400002c42c403881d040010b107600d940c01750b203015502084c400104e1a065080c00700038081c1d0b10100c1409403404d8403d00a06900010707001c06004124039001410600d2803200319001d00c21a88850791103ca00100854490b00d550300401102c80214221524200811080c0449030640e10441c0003580006148034054142130800c00d80c00005442d000030010b0300c1c2d6442d403045035010380350721006034880d000b00940342c20104500d00390008040081810f001d20142c4962012400d4000c1c075005100210108890491820150031a44c01d0041601d45900e810b03d8020360346c2025202e500e1040d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 23667407 1250 23666157 23666171
    0x405150a0504060e010b0c01020c06190b0402030f0402040b040b0d03050912060601051b01150e07030c0905130902061911070905010f12020d0203030d0c0915053004120201 75
    0x1c5043c1c455101118406800514981c2c40c003601a032040d000035072074100b00d5400300050000a1414000e40381324241c840003410040f40601f0b101d204644c4d0034846180658030410502c00e128403017188241c3d020364112170125000401502050142a04012881d042183d80d1078043c100b54125000d0100f911054910402c032407041080315943d03103001d4802c103000c65002c202404103c0c040e04a446544a008000480c041450060700b11841c0c4480e0700c4100101500d5041c03041d090703498012001c800200740740c040351b42810140081d04003140c50030100051a80c403500341c4119111a800d50742e80000c6111240080040030002030880c41500c00d41d00f0341c1e801445804906039185204c0c19050342c9801070381c408180c2c201988c4030b42e4007245000c240d030320160120302d01c001a030301040207202d800d0101ca00420004020140a0440b5486411401c002203031003201101c5c0c2136000090f112008003c01480c150301b0500281080f07840b101d42e8940065446c89000c200a1107541144001408100d5000708400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 23668657 1250 23667407 23667409
    0x161d09060606070b0403090b0a11010b0102010e03090103020a0c02041506080a020307050d0e160b0a1808030904020f070c0801051e040308040b060a08030d0906060602120301030305180405150a05 85
    0x31102120215031000041c81200c0119001050031540140b02c0e0810034480340d1103d120a003103403c82040c4000140210041c6451031800703000b040c2420ba000c0c00240b04108014a00584a0082c0b002d1a41090313404254008010302c40e0801d400745540150040142511800110b0703583e5a0a000351030110301e01c0000b00714000300c2c51007100d106420f155165410004460303d0003018107100a0b0254403481a4200d03610743c00d08490070040201031020324182d03568000e1001518820030441c00800c4498905800c0081007008004c50f40c0c2241c04550059031501b40b5403400c1000c0c0506407001e0305014600300702042c000c1056201038018909076000500c42c0848404400601d201220014006486000414002824182500e0700104d00400000001d91540d074003070300d1900040c060081c07290311080f8800034803004d0b00c150805041c1d24400f82451880202d6942e52070300c41840000d0400a00241e401000c00d42044a01c4096000500034095420400d01d007012459031003480a20581c0d20000c00125 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 23669907 1250 23668657 23668663
    0xc050303070b041e02030f0601030b15031b04020421050106050a0b07021002030f13050a05120303180c04020309011e05010f0311030c09090601061e05040b0c161d09 72
    0x100a500491542141c0d0382e40d42c0e204c0500650132420308104454841000050740c062100c03000d00b0001d01d00070661076246080440b10680301600c501070304010071005601ea914085841003079258810f140518048424021900920840d801000c995001a0814a44c14003001320041482d0103040280f15840d21101003140c000c84904c80c1029018040010314018106244c209200881c03500549050038a00c05042c2403907886510640e103040c2d01c0b01b000f4080392030120242000f503d0300381d03170003c2300e000c510700982da4920010b0120000410800f0350004255000c0258000c2ca42d0040c00c15034603820b14a0711203000c0c003c80300b528400041913200e64040f000d000e2249a040711a00d10850004074a55180d400c841d045204c201500b6000b9001040b45a8592401060203001408020302c40c80d80340c210010441170b1168807031104085100d80501c081c2c0c1d4000140c0e8140c0303a407000c3c041d43e108a402c052918040c3c541d5214510b4048008000600102001070000309011880006000d60b44140b280c0d44c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 23671157 1250 23669907 23669917
    0xf0a0302100b04050c1602040605090a0905010e010507020307030c0503040f030c06021c08011404061505031602010203070c0212150a02040f05060909011a07060504110f0f010f11010f0e0102070c050303 88
    0x102d04205005030f003030391446d40d102103e01302d0000e0000900079459902281c03200b9811a0b40035042ca03106c800540412409110b00c914411100c4001c11003810842c200039140d128924000e0b00b044003d0b41c1050610805008031030003060341e42c11f5007481580c3c914048600c500c052103100c016000d124802da2040c020800c003480c10f50544d40e83c070100d503030800440036080300d041d042c400d4016507180c2004c9a0807440c107043ca0202002611071f540c8030b207080203440d600c1c103c080b8120011a4014400d0080482c1c0156401110301d90440381c02c10184602c00c0200d1030191050b404002d90143e250520a0315060b07a401030007610010700c0e600940c503440b0001e11101d84a5480c2e01d43d005445040100401490368240043c00141d00300c81500e4036905407500c03400d40750306403010340c3c00b1807044071600054902201e00359940081562040d1080344000b001a00c40c18030310b4000c10502c0038000c1c070305202040c00c5d40314081407148841d040286120f81c01f0000e001f034201038000c444007650140046114a00042038070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 23672407 1250 23671157 23671171
    0xe090601150c0215030405010606110604020d08071a07020f010c050306060307020307021810091a010305100f0e010e01270b030a0c09020304050616020a020d050f0a0302100b0405 78
    0x1250607403078070008032050800001020100001c158811005070345004c20f905142c1d112150098681c2014180070317085072240d40c010810302a50500c2800e50701da0120708141c1c0603030100c0c0c44140d803d00c3d60a0000c0c3c203100300e0724014100c0240c7d1000c1420a208010003600900d800c1c1d08482243c0d000303142860803030303480400d64404140c0074400207543c1d1910000440e8850001d105407030031701242e0390108100a540003020b10300548034008220661041203030400c02803410310000c0c003418010215980750000c1003440d050405803950009011200400e01c0300000b4111110404078050303440c49041d14980c02800341c1007918010100000d044000c0301030741c2d071800c44910260203485010346000d00c020808641c4041e058066145605e0103c1d00c0b02c0c9089004120803a00903a0760b02d080c0c07030020700b000001882d0501074034a90f0145c401c42940001c03541c003800e0b0305590501421049040c26880c10343c400380c0b414090712968050100705940450617900010004809020015401b420081592400c483d03034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 23673657 1250 23672407 23672413
    0x150303090a051c050102040b04060807091202010302030411100309020310050906130c030803070305060310090c18090c08010c11060105060712050c30040e04020f060d0f05100e09 78
    0x1441580341041c400d2890940c3d00030250181d00084e40c5190036038205a02490000c1000b20302006103d07088045250305c103085103003840445040c121050712608030944080d0406901000040400454820300d2640610003400074642416065004000d000e601008a000f40139840e105400607030203010750b40c01210010702a20705030780c0d070304503524242c020380000b592411002500000030468440c010b6006d5070440d5000304103841c01c0010305140c01d102c05040c491131841e042405002c2260841058241c1d00c054240350a16080c103021170303002d44080e00d00501140480d00000501e048150301c00d48200d6403e4864000c2188140da1844d1601000d2058a4105408002401c0010380405801c0100102402c3c0300d801e10040c40342e0305140940d02d20a1401c0303150400034104596a8ac422803034510700044455502d0142010002e000a00019200900615504008146c40d40d01e22040d03030540200440100420702e5003803501405480306803660b0000182841e40425140702d000d4100340304410207401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 23674907 1250 23673657 23673659
    0x305010e0a0504080d1a01141905030702010f0e030a11031606090201091203020a02130209011218050a060b0a05010903121101110703080a060b04030309120807080d0203150303090a 79
    0xa41020300b4004200702c3d1904020070543d000240700e403041405902c002210011984800000503002880d204214403204000348203100d49a041c640f200591402d242c82e2440d26902c2d56401039000d88410a000300c1160308152084843c0b550010103004440c0c142e54990303100d080c1d641038140d2030344280d404c810344004511422102241035074000152882c4103251202a82d5983d81c40d1400f5600d10840840c010313086042c5200942c9041c075449104003030448811072804030080000b81041c0d508a2102c000c560302d8000c4140c800200700c0904807095000020341c0c49100c5a032510314000c20790416080d00c51000100d021071107512400e0184182ea500c00d61850300341100b220140e608000c0b580c000e00b01c1d0343d294440c02c81c3c5418428090911035101e034461400c1801c0c60004d00c425920aa0444507001d0018442000440e80c4410100d04960401504009201c030500702680680714500c006031100c3c00006202d0700442071503005520403c1c0c0c0420180400507075a00b056224810300c8141540005c0550b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 23676157 1250 23674907 23674921
    0x303030b01050f0403050f0609010c170910020c06070f1b020f0406050406090f060801050c03010b13050a15080603060105060306060903010b09090105010501090806060904061a04110301150305010e 86
    0x84214080340c0c050401c98100102d10009110b20b43c031903002121290001c128149008108000242e004074804000b400301101d1b951005000c012500c0441c403107022000003040740c45409000400003007060000070340d920300c4060042546d801082d0751403000101c010589804e00c620a01d0b03c405182400c2d18a06001c0c0010380802c01190b060b0300030964480d50341c060000e026a518400c2e440246291340d800714a0401364a0101e04946540d8802880c40e418042000402104501100d040d90a0a40a16240d4261000d01d02c0c01841a400c00340e081081c030400820350364035030a400c4140f0754060b40c4024060741c1d400181910707400f00788545070b080756060000c1201481c100c005417803200000360000810b0400b090001e40700340000e0b80c0b4160580d540e0b00042c42107580c04091480942010401409a41400310108114103c0104040d00e01c590342e4020102c0c059a134031500c9200c540007007051143c203110b88200c0810b6402031190091500c5c8081c041800203003e0b01550f0704031900000410301a9071070807 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 23677407 1250 23676157 23676161
    0x1407060e09041505040308060415120f0503070c08070302151306030c020c130b03010b0904050303060105070c05061c0c020a05120309120c03030402030d080c0a0309140307080d0507110601030303 85
    0x150085601c81c500c014010f000c08014826148214042d50341c40955042c64028041282c82c5100030403500304082c4020f20190f080c09803003520465001021519404a5050003411401010401050310b00c42513400a448100081d51409480c0205d810b113150800c0c1f00382622640c442c64680b031540b030b20034410800c6450f00983c8075524204081c01a501c0d022aa140090680200706503e00c0030a40d49400c040860304013449000000482510044030b541040d40710320303a4a0000500e082e04104002601c1e000b001200101c50000b081701a08036600ca041c0c402b8840c4480300d203103031030005e2140f8014106511500c00258041d42c3da81040c003404251a44c0101c03400fa545c40101000054890441e409c481c03072101d1002043e0780250400035544a0815104240c181904884141c1c20080382805005685400d2812660640300c1401c5c002030312045440d02c05015000302c54060650700010030003030244030303049008201e0615240c004001680c1c0e01442528480c000b0103090b80b160f400b0000500c0008e01035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 23678657 1250 23677407 23677411
    0x5010c18030b13020307080f060a06090204061d040216030f0806040513030c0c0e0108030a1409010801090b030c060a0f0801120c031401090203030a0e0102010f060311010e010e06040609031407060e09 87
    0xa0f056500940d12011f1a6140c800e1001c00b40c0b11903841282040923600d0030340300d0400a401031880540c80c0074030302140200850714240c803c80d000e81c0f0119003014659101d604580c41002d0fa80081d401000f01c40c00c0c0a0310690740603640e000401e803e440002d00360301c0c2070310800e0b20500d5034845a400b00c01d030585044540401c0080220f40c8203503e0507002c203c071402111514024140319004517036400000b41b0080c0702003c4804210b001c28400d00400c00e03d81e03000501507041d1041c0714070004141034a43c001078a41080c12000365001000010700e50142030b1b20005a00d01e85819849061460345d94645441d41010b144401420310803105c0001c0c4001880b40031100d032600090000030401541c00d40002c4d045601c04603600011505c0f4110341d42e2a0358081c00790101083c801c04c0708000640c80c645680b2004601c4112403410051010780c41c1c1071503030017001840c280701e5002e0700c0d507900c5549448020f04a58414042920421450b191644119800048c81c10540c1e42d40d40e40c1c80782000c03610003840205240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 23679907 1250 23678657 23678659
    0x1c02010207051506030706050903060c1c050703020c010614060f03071e021b09090a0602091503041b0b0307050a0315080609070504050702010e03030610030204050d05010c18030b1302 80
    0x204032450214100700041c11040020f404880c0c03050610b0420035262442642c421400d2200500c01c0101a91300071480c90361045103079000359565013081d650358070394000f00321910351018500030900a820b0342c164041c00c01001c541000b0085103171030f1200e12114110207108079901100030440280d0348131002c0d015603040795880c03d0404200001c1c5031700054a1940114070f100580c0b0a00000402244031000520b03c004169403034519410042410b6444001440b00644016000540c524594441c40070b19181403460300005500c2c0c0c201490000954800c3c1d400ca80f80c5000c1a45d00403a0ac0e030950021a801540e10b61205481d0030880e08050f4054580320003030b9203038941c04031000210a00309214641c4500c2810340504220750a040800c01203c0010b01710104580c50080044031003d400400c4903004503048a100c85030325003003d002c83c0039108903000585c011740901c1001c0c08200c015005031002000d40d85a01842c0d44048501c10041c540602c009040001c510000c10302e1000c5c1c2100703404020f40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 23681157 1250 23679907 23679911
    0xb040206072015040b04180e0303040602070c0e04150c02030f0711130b2d040e03070309060f02030708090609040e0601140117010605031504020318160311100909140f090f1c0201 78
    0x491406e240d41103400c01c2f24140c0321030303130001005030800c034150031448040c084d0034443d9410750400b9101c0d01c9256a07001c030110b0b440c40da02c0701c0a40100f0700800550320140440d80711140e5580b041c3c0742800503000c641803141e0143c00101b00100700b1008074080c1c4116004040c00aa481000012f540016a1894400081200d0038404140707001e884d203004454079918200300440c0e035083c4a2038001c00070203459204804000d05240b89840550380407048509580d00045000c1d16041044c0008465200d8898030329807061921a0300003401601080c5c990407148511280e040103052103005560f109103c1400d18044c0038108010302c48107000340007a581081d0803805550966034294041402c80e030003500c00e800301100d10703c101c141d00d6804201400680a1040d280303010750340b071581d544049203641440d1910881d41a00d062440c603100e00602001004590303420311901d640645182200314080e0307960749000d02003800042c8440b034005100361221546100801184480480a1289404c01613000c0d0443d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 23682407 1250 23681157 23681171
    0x16060902060301090218010819020c0f0601060221040303020a120c06050c0301051003090b010e0714030106090e0601030e0a0b0c04030c090c03050915040b040206072015040b0418 78
    0x2886100181d4084d014004005a56540c4031301549019806580c1550420400104024030031400b01e50f51500031100c00d001584505240b08110b0500c100078480c03860b01d05c1003000018100350f000036414001007410b40314401c008600c0c00052480d02c501d00020700940d0080840d20b0001b082001c04202034001450b00d4801c085059403000240c84056a92004203400480140402e15152000a0003100707142420414003040e82c5d500e00d0803036014420765403402c500c2c1d000511064040c0e0030216034000c18480191340da68442c9000341103c10a07014400c01e00c0c1404000840c80d50080c07180905040e4808010725441403180d40d0b100504400800d1105404001d020020000e28a00110f4019143e512400b00301c41c0c10511004045810040045019600640130521103405808003a5000b98010010030080c2c0d03200c1c004a1200d1154038001030400c01038011200f44c00c0000c4040a045402c1124180095006108084e10034000c0d401203004216041000700720700300400c2c002000d0100494000305081c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 23683657 1250 23682407 23682409
    0x80705120403030911030a0b0112080c030f0c0106050906010c060b01030f0c02010203090d0513120609120309150501060504090b0a12050604030e040908250204061202130501050616060902 82
    0x6540070341d400c40209484a421208008011141c1c600340c040036402020140b070152102104000e06108411a030350603030340b007541403100840444403101ca000707003225900e5030b80c000c64140c0c0e644a048255615440c045001c502031400c2d1840d28001d58050b9291308007090076841e014018400740703480c10f040c965100221001c10341140640440e212154000580302d02d40440554103080d81c5c920346408011007048000ca07071311150030b2880b0649182c9011190700140d24602080101b5a45001400e0b23603114000152003264590001c00740e0300e02c40d6000410560b09200c0d0703601524428040c2c02c0100d03406000c1072140e200242e01406c107085c001000340c50500e5a946400801400720034040d209904214100800d06800070150311001c2002d803410080384815459408250280d600e649180c5210f030b50090008142a02da0700701d62a030001d0040003030b16515440004180300c2e4030f5049004200601c000c0c45451701910980303040340c0025041d030b441e01078102403656092146903011620315a03144050405 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 23684907 1250 23683657 23683687
    0x50a050a05181906030e0105070918020d0f05071d0108130314070501020406230403020d0303090510060602010c03060f030f050f15150301090c17070914060f0a0806040201080705 78
    0x480160690852a2420130300010b0540b4a241c2c140095030f8104030501c01e03044c6e40041e044040313529076145140f10390400c681800281c4622200005114180b0710b140381d000311250b0145002d042c041d03c4080400a10710416007514000490f1607010607074200010b01c06416004580750b1103482480e2a00c001d403c92144080c042c1c00041c070a0301d0607035010905100309074202041001c050302c101d24918140a444014190500c11400024003d1941890302820140250841c118050b444401d0700c0040780785c0b4520070020f0200e0301c6510b00542c02e0400d0014618007d10900d0243c8145c2d510010407941542c854030f0628120103001c60b81e0f441406041d1142d0a418010300307142080d2110400c80c6424002c0d0070b9007050320f40c181d506100c0d9240c00c2c542c000007141e221003081201c9402c030303081c0c01d0b01101d0310089041601c240e01c802111401c0c91040d80d00880345030300d0b80d40f282c0000c4880b81c41e006001c40621001024900034440b481d4403040100d0003542c09048001d510003200e290081c130b44205051580a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 23686157 1250 23684907 23684929
    0xc01090e0c0c010e0a02040e031219021c050601090b1312030509100309050c0114090d020a0503010c08041a0903030c0306130c02030703030e031905070602120f09010507050a050a0518 80
    0x4458104400d4082145880e003c1c2000c50344858005605200140d1082d040010000d8171801440d0501401c0012f81599034043d58401138190503e60b01d03c400c0951808003914044412a0018011500114000407035074295026051261000c450950810096070160b101da0f01068080c040284090706456855942083c2005010b82d1b0108050f01c5d40d10300b651a00d41e8003114541804600d85507030130490011070584500210407180d4814414260000c11702c041c0064022540650030a003481e068503800a04071400342d84104400707001e005010320821440c5d0000e9541c00d0103500200007064203400000060360300003400404400034010180400e80c00c84480c070a403140907800101d070203010700d500752103002030000668000d90319250410b82c810b00c074440075502c1001400070204000040c0301d02a41603d00d41070305000802c01c0d9081802c0d0403200d4920440b1484090340c03d260016502d41d03c99805c0e034080c82c080c2c0d2601424800c0504e800d49058204642d14440c140e24004042003507541d5000e040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 23687407 1250 23686157 23686181
    0x1e0312040515010b270112050705040e01050f0f01050a050d0501030609020310050402030c060705010f0501080102130b0403080a050c0109020a03060f0b03060103080d021315050a0906020c01090e0c0c01 88
    0x2110100c0d0b8990446180c820582c440501c0131418000d50940d0452003040c8494042c40e0740030070000c4414140140e4419001021a041142c42d0104000b541500074000304140d840a208604c0160390380e90804c0913072008981c0f07985c0c1051500b240d5004550288002d82030720346940c10034a0904c07a1040701001100d10903882624040e80380c1d0b10b01d1040d030800b8410701c01911740305c100600051506401080c0d680d054030044030b002e02e10004a4000b804402c0d840484407004001050045582d101d00060107074100000900d0106001e402c0014406111021181120b41c4410400d041034002c01d0240c0d01900480a422402c5d503ea10200005940c0e5401c0200510703c40c1d41300046521a00c1c850108881b0004645800307079001d200180049a00c0030281c0e14113034608100035035194a0050713044240741c1d141d4401000f4003050480804280d030460041d02036210141d8490205587d1940c0482c0c0e142d50f1a0515800300302c00b100f080c0007605901514560084000b0106490000b05005450840318018851 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 23688657 1250 23687407 23687413
    0xc070f0615060503091e01090501060e0403090b03090c01120612050a11060403050a02060702010302070c290a0c020d06020903070b030108070602070303020d08070207030c030b0406110c1e03120405 86
    0xe2010084041e070910007070304162070500e0035440d2981d10300ba0303211509034001000301c0b10010700380340310304c000d400490186034000b00130300000703984250100244909440480100340b10120200342e5440b460281d070b00c1049214020f00b4000085401174a90003120b4803c0c0d0965901c8643c01304440c1690380c449900c0620407402840511618205802d0022100070050b1040c4002c10040000c80c40010301080f10980407a40e0581d91011407005078000e1050a2004105d02a03541000440e80321880d0008078140d400c090240780034004900300c0b030445c400c2541c0c04011030000c4400740c026080070f2050100030381c46480c0040c40d000c3d852000921309500d40c0d00480170b1000010041c00744420a100c070781c2c01880280005d000f5a4255900030351540e02c1c002c100010480780b0800100950320030000a0010754104070700500c10342c0c0f42e003801401007000721020361300c680c280809101c00f1102c0c00d0031030311421600805046111510441071700101c50700000b5840601c001d203c00c0c4c00305010800c03214043c80c030030401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 23689907 1250 23688657 23688671
    0x9030203030114060702041e0e030a090519031b0303080603010603020d08030a0e06010902040f080d0203161502030f0406051003030e12010f0507031b021b060903011410091103011d0c070f06 83
    0x3c58025500382723440b241c20580050020400309030b0042154400c2ea00b00719003102e52100754418613400c00c04960f002500c6003000700c070075024041200345844107480c041c0d9600101d0342d0301e18050501744c0d642480300a4001030100c0030800030034200340155070410351040f00411804e561929052600c1001e8001074402c982c00202041520840b01c0450300030709000d8050400d1504c1450041d449024503101d00c0480e81c84029960200984081c01c522030491010302103441e818000b44441c1010790440d0216501441c00780410309c41d8850318a100e0442e68140c3d20620709507402c00510007002c011102c0410742d50340303030545188001e51038006c0718807441c1940d40c0060100341c443c1c420362140d840181910255001030b001c90824210300d150000108000f6602941d41e44116000b11b40189001d0341000a2004254248281c00100c0101e030b500721001c11000f84034a500360322031303002c251000b842104009200e40000d80c902c0d509240d00c042c0d0004c280c23080b003820229561545143c204091720700303c41c1c00c4d540c0e0b84 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 23691157 1250 23689907 23689961
    0xc020c0d05070503190809011809020c0a02120109020a030809010201090515160f0504050d1a04030c0b011a030f100302090a020301150813030809070b0d021b010903020303011406070204 81
    0x2140c46600c042c0d2202583c1c0c950440e84840700a0b01c40c21100504004071501401109e0042000150081000701011995a940280c07815203820214508900ca146030042c83d00d2207400502440403050f400900e0580c5142c0b46664071141c0e54001e01195040d5500c0392481d601089080c4020b2403510242041c0c0041403030007052106094001510400a00c410321500101c5640d00400756404e80e001950078803d1100f0030704182d12044807000b9a500d002d0030200400c0304042d884001201c040c3e100302620003d80c3d8a440c0945101c161101c41048201024000a81d4484100400c02d4011494082000c8e040783c5a401140100d001110510720305500007004020304000c5c1c415803202e68030300b840c00046c1d030b003050403c1c02141c0c490500081d040000140200d421800c00780034800040c10408500b90303550040c0860030020b034006801400180040301407188460f071041c000c90500541c9030317028529580c200f2340542010b440c4091140e41103070083c816070b00162100d108074640690080d40010048141740 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 23692407 1250 23691157 23691163
    0x405040c02030307020613030207171606080c0f070f080406050c0c09060109030f05010b060a020f01110901080f0411030604030309140705131808040b09130509030307030c020c0d05070503 82
    0x30010119401082001134003503000c1002e50308450304102003c0d034400d0703d0070300700d10b02402908512100504c0401e06082900700042200007070540e1496108019030390b0600f540d200780200c0e90954190070410070900d9180e008001061014850a102d50340389030652500481500260440008520001698695818108606402144100c07001c4019241c2100002c1241005120007040300043da100382040000a401c0b000c045c102c06051161511810003000b90303036940142c4441c1c010b5190424a1281c00044021a18100e4060315a85d106489003014010640d40c018819501503072541e40181c1195000c2c041c49005a000c0e0360013042001241c10100b02c54948050007103ca5840903000b0042512440c2c01d012a0100c01640010103024035840510b19410594004140300c0001030086400202e030300150002c0607007540e08014a05000b100c050480714207480915283d4000e00c0010391181c42500100035080d2948162142000b04801040101c1000d4000700c0765608440024444c0381010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 23693657 1250 23692407 23692421
    0x9080a080f0a0b060904020307051209030a030c1d12100603230109170901030b031f0509030324060904050f04030e0f130c09150807030b0a0509060906010e031002040504 74
    0x1402e810049156410300181551240020341070050381c000c00040c0096014405880c5240381210820020b450200260b5480e6401051808007003480c6c80f558032081e501c60b11119614104440000c1c1c1080054410840e94589100078141c4500c55424884145005ca004001c0214841c0385400201c500c03032403c200d0a00c0c2120071000450b85004100004108080410341d242d081d21302d0055515480a80120041e050b00300d2140e4040c410031410022807541440c0300d9100c15250b40c0c0810217078885503102903e0348025a1280711000b503a800e00e09072242e00e55103191010380300414032840c000300c2001007401e0390021281d107250796a0100410051680010200c1603102d812260703003043d0b01503040020f807208000c00c4001c2c5055501c0c11800e50990052161101401c01075a5003e00003403002c400802c00750003102e0003000242462139105607800c2c1080d5400c10b403030008046844a0752220144454041d005100d42d0400520003492011514140003900149049400160303a0764140340c14001070b6958 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 23694907 1250 23693657 23693671
    0x302010906050c03160804120f02030c030f070603020d0f0e030a0807020115031b0e040803010602150709060531030209010e01030809120102070c0e07080709060f1209080a080f 77
    0x2080125110000d400300844510f005102d0031442101700500703280d81c15014075000125804048031441c410301082c18070801c3c5d10352086046848445007081850340341c1d1460100e00f0342c65408903a040c015140650007502800803031200c0011100295010181504d04080381001035030000111607821560104100744c0c0455540024054801c40030752028084a0900c005031000503041c0b440f030340041400a4400080810010410550070f0504150115500038441c203009446103030b400000c4405900c40c2a4882c1d6600d4880d079090500c2d00e641034505621250700070400f0104540c0350840b1036441241440c6006114aa024019003944107204600b101070b041101c0c4c03421003400400c0044c60040c05c0320b510340c006454020b20410340d108554064095004028010000d0303940100303d00381c144202622850362540d58482a0701c47d254103803400741c0c190141c18001a20b0b0948006510f01840195075140002440065225440d480300e100381d0700700340c10520001c2c0e842400d00442d014240055070300001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 23696157 1250 23694907 23694917
    0x5070905030309010c0f06060605040e01080607080c03040219061206050d051b01090306050c0304020a05010305071e050c070b030601020622030e01050c1b090901090c030206030a0213060206010302010906 89
    0x10500300025070340c3c01001a01c50420464000710b03010001c9004051044541c0440b00344502d5071215409000d54000e80101002042032100002e03001000048103401281d20b5101c1c802c0644841d00c2c00390075988002d0090742c0001030310061902c501003005410006000da680c0b41a500460241c410301a18010391003140721362404100140445c4001c1102d8040c1ca0004181400f05d030603c00041c1c0344e00c45540d00260800e840e110402c014500c2c502c000b54411340c07085410600380c0f80c4560040d400c548094411600150b10a2408001a40000d50b45010b00440f81041c50905050300a41c0749440e140e07420002041001001b40401960100400d03904100b0405c480c1d0035504466150070b6050f46900c001404200444502d4819640202e0031208000401000e942c1e03001d000d89102c1220310715949055009180540002d440200184203a414981d800448080d0840c5103801300801754001030104200580d081004000103110070141c00300400c0260094006d56142d4000585885000d41c0081c052103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 23697407 1250 23696157 23696159
    0x50d0e09090f1c09050d060e01050123090c0d09080408120304030f050313020a06020a020120030f0702040209040204030b0411010c0b0a020c010f020a020102040906080102360301140604050709 84
    0x140400e1141624020f070600000a9010480840f5810000da01558020b4082c242a40034060b107a000710151801003402448241d90315808030800302d44406c2401d40c0840000200c0c1d5032480d02019468215110110360f03802c0c10800c1594038111984200215110100010100004d48d01031182e8891120741424003400c520b000d440240c81c51001d203c00c0700801034004001517440603a00202c4040302d030040e02e134800450b00d0390b80c042e554031066181039010031200d60f50423510303882032050140f070780d901d9201075810502a903200005d650031000040b0382c89502031003061580e0321580b0142c1b0065015039060310f114285420702d4512043c29201407810000300c4504840410840130645400000100e00142e95031445034140b801400503c00300d0900500001d60703400e80d00e9054028006445000d80208699a030798440c0a00305e10400b05940703054000d0201e20510122000984129081071485094900070805c0010b42110140c0d00fa90745961041c1041c0155414141f01c3c1680c0400b050a001c00300c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 23698657 1250 23697407 23697433
    0x301060b0408010f090b060d0f0c03060c0e030d050a03090c030b0901051902160209150a060e010e01050c0a030305070c080412150c08040b0703020403170403021009030f02010507020a03050d0e0909 86
    0x781d00104405d0140012023244001c01444600d039900060308043c0c80c0e0743c2541c6030b25048010701004445000020024081c1071910b103030101d001034405501e511051b00e010303a03603041640a46a0a241503584225512001000c5150803008a01c11041ea07400000e25250044010f220445211a0703420a544188060750000005903482000650110340c52001580c5081c00715038240391090392103810000d502c0300003c2e81d90f0011180d0440c00303800d0700c4401082d4055001142c52b409403441004032a400380030340c040844c0c040d40c8035641010a9190910b2008078540320004140d0199010003410601d04120206014240d0b4048040207442c54040c41104000040100041405080600b03000030500116614900950485004507403141080e8014803600c640340050303803c035220a0707015101c8803c1030383c55188a240000150b039405010b80340d4a015503001101d5580048004038dc100c514180c020000c20344c10402e04a4810103581c0d0414129080d605021030307600080d0a440041d0301003140100d02d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 23699907 1250 23698657 23698673
    0x5010b0301030c0e0c09030a060c020c010c05060c181e0405060603060303030708061c0308011a030c0406050711040513060e010c051204021f050c06011e030303090203010b0301060b0408010f09 84
    0x803144c210a0091359920345101031861440384102c072a5152040c0c40702c0c8401c00903182c011180020362902940d030803503160001510002e0541c0e000034000d4001704001168084000040d1002059985044003240c860101050745003140082d46120051929841c1e0800e01c0c0c5402042e60050381922001d04600f030840209075240405807800c024049484c0004002d80c54240c0040307141164081d0a0081a0441c20098134803e000e00031941c4040c80e080b01046a075a404089030301400350340030302d030740307024608001101c094020312012100a000300c000003840f950749010f024010f01e004400c0b81c0c00780115162910468051044ea82403603418407080360402c0342c00c0300548080e0214141d003d051940c86200241e070307900009143c0510606200700b0501126444005400f80b0f410007412649141d80f6454850905004e0202c4c5d00064525604e061000910036001000031510280c004546005003800213420b550311500300040c26031011904000c040000d003d100031403030002c03d0801407841d8a0b220054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 23701157 1250 23699907 23699909
    0x9030c030206070f0c0b09041b17130204050f2401020c041a0402030103080304121805130e06010b030601120209030606040b0d06020c060a0c11060414070e0115020105010b0301030c 79
    0x102c51480403481000344400340d2003492019601103075016520b501e4107001205a080601010300440c40c150100e03501c03480d540010246804252210a407040c0480c00280b030030000203142100700e60704003941c100142c0b25400fa85018100a811078421890701c00101115201918440c040c60325403040040c855076004941001401c2c0706a802041c8403e800301c680483c078030000102c90308980300100000c00e006503013010b180154031441e0310300c800e2002c440c001c8030080d503036604164007005107001c00c20081ca058144003581c004000404031300e06200002860400e0800d92010518a800108100040d0b030301c0141440500075085046040594400c042070b42c4540041541e400b803503407032f026440c0315034450f84800da003141d1080d025551450440c0e0b0ba00d8440106035440d000f1a401e2111811800c1c1c080c4d0341070b03c2c08949090013025950f60340d4840c0419902a0880701406000d100800728420003020401c0e40030f401194848403a800e5504c900a084a2059000a01500382400107000141d61034141c50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 23702407 1250 23701157 23701159
    0x6070b041e0f050307020a050a0f0501080a0912020109030216030c0e07020307050601030c0e06181f0f060203070212070503060118021c240b090603090703020a0608010305010b0109030c0302 83
    0x2401690140552001c80400500301406a0214410780e4003000341c0003004245c200e10076103441303000b40d43e00e00c2481100b126500503803290b041d1480080c00694071540e01698403100307801010a005245071500340110704100807980040c0d440c0c1401c0c030149601040520742e0f9803032a10507001c489241d40c540d440000114040e0444040d20301d0301081d20144204180c401c0d15402c0300544209594910300350041c0621031203181d0f00c3c950020001765140c5401c400c1c44454040003d12480a5590314011540d50744003050400500800e08001140000002c4c03151405000183c0046980748805c0c010041444a503171004415580483c00a12203070700c001c02d03d241140c9210101d8a00710300d9004066004c0d0246c949820752543c0b9000d00e8880009464002c1c208020040c8031b24802025180c929512102040c040c5200c0c0724000c00040c4003a003406002103521490360710a4404841e100c0c1c0c00107030750f00d030f40398003000c0003a4031000180f0038024203115581c0303007040074240025900e207155034424618070a8400a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 23703657 1250 23702407 23702423
    0xd0b06090a03110a05030d110105090109031710031212051003050703021003061a040302040b040c050307050708090a06030b270c0d0b0a030804060e0105071a0702100f050402090606070b04 82
    0x20203113a116203030980d0103008001d0a5880c51480d111004010360030654030581590300f0b080104191107010322550000725010354986441d400c04421550a04c1400781c0203500c0d044c6001c00000c00300b0841180b46040450039610700d5042501403a440c400e40308080c08117080701e400305804000040001a10800b2280d05943c074007910106600c00707900070800755000803c410301002e58002000c0d040e034002e1090300d00c2202e007000002c580f9014030085400503000007011403010004075202c40d000384090310300944104911885c0c004282c01150280c0384980c8030744042511048a003015140c48955107a810181115041ea1030000109100744210050f00010144400141d40180c46003150024417113414090012032200760303640f80c24412540184545800141d4510f01c2403c1988240300710f422441d00001c0701007070040400b1640d0309001c40070340b000040d881a1204440100e0b0780c4c1c05005a09210400300013100d252078014000c12182c0145194861201000b403d40010300c085030f041e401541080171 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 23704907 1250 23703657 23703683
    0x50f0405060a15120204030b0412030c08180c0303131d07021203190507111c0203030c09011e050403051b0105120405010e0f0f0706080603030711030a06110d0b06090a03 74
    0x810384c0d000d140307600155041070002401009101c0b20301b078200e0089100c0c1c400e294000d460000c0c1201150341150560780051042c402181e02c0e04541d000e46010041c0400c2694882031014000078610f5220075042c0702407075019481000b6101c0c030651b046441032100b03000491a0f01c3c18007802911890725040b50a042c0e4404400b00314030391148070304400c3c403c074661010451400c003800080d0811503141e0440c4041d205038400030f03030711402d1203a5006002840390015401c584036001010090740003161039a041003082c0055564031404080c640e080c1e0707a60b1307484043d078480c1541403150520312403070f503452150800150b28040f183d83c0b0030304031013441510207010304a80d115480c016014007405800c94a0b54458004c440d090b81c1c0010540f0364a141a40003201c0c01580d4a603002e80302d01c2ca00319142d50b8180c0061104a0104030800d00c060080c0c080101516500c80e00c5a1b1138200702e841c0361a18201c4180085461803a041d10791203a002e2500c401c5902c0741c188000d0b00d0000303065540a000c01004810b00d048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 23706157 1250 23704907 23704949
    0x30609060b040c03021e18010e1306060f03060503030a0503060108040c17030d0e010e06040f03020709050c040501110105010b030a0902040609020c010c02070f06050301031103031603020601050f0405060a 89
    0x40324481c6010010310a1140024001008001e50400008440420315060070801d1105c0100100c3c0c42c11182040c161601000c0c02d0015207c403900c500c0c05903001001110b1001d2074030203a228160203000d40761500540342140000003411200141c0159019500410980c0b001e503411000740c84d40001d0920741034013640c1e46c0e40382030340b10480140c2c0000c00390908408480a82d0502101a00681402480c20405460309120490076511500340e44038050f00140040380100c1c01c2ca00d00e8402803030180c0101c9202c0b0355a680c0c2201204d404480d540c000d000c01240038040386d03034044088046104410001d000f03a5062802180079440040d0280305007941e01c000324411500d40e0f410640003040104821501e0b12051403095010b0140000800014010b158000c40e03880c80b07908250042d1045540d03200c0c11030782141d40c1d4000702021414181c0e4035101c1030001f000010448503680305618030980c080d200651506090007001030210014a106a0804041045c941c80f0141003404842a0003242441000061 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 23707407 1250 23706157 23706161
    0x60b270307090209040b03190305210f01030c0b13051309170904110301081c03090519030806060a050d02070305090904060507020c01051c05060a050a0f0e070e060403060906 76
    0x500064050045140c00a2903402d5540134003410315080d0b50600c03503802008105519017240e040442c0342c10900741103440119220f100681112007643c007502054928101041000501c2103580001091a1030010720810104c0d846000c001c1c00c4065a203810150180400000c1c0403203406103501441d1101c05818640e806500510392780382d001120040b0701c0d07107010500042a07200030706c918040da0078640310b010701c1404c01b02100d04a410000240c040d01c2001510742d06000d08100c0520201030311101c6407008110b041c0103030094a1191a07000e0032080103407601502c584070060100384904010301c464528681c1040480703180034036080f8010b075185020714050f20b85000b8411119003000c0700400304800c0264992005000b4203003602103680300b4440100444091203501704000254143c44490451a11070b80c03c07060300131200500340e00e00282c460011400e0480903920200e101d50000c9010000b080040301246e801440502d0034a00781c036891000700d2020722942c44014940b40e9104000e100f0300040b5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 23708657 1250 23707407 23707477
    0x80a031404151805190b0913050c0304060c0905010504030201081b03041202070e071b020a0806070c020109080a0503032703130602010b01030618020703030e010914060a060b 76
    0x60b5900250341c4121800090003450035a9a10301d10095074000824640b074800000356035a400d1160b075583c01401d01d0065000c1d134000148403a04000c28512580c05040c41e405080c0c4110500d60510703803223181a0402d0016a404d18001509200c0407900910a5136442422903095a1b02800d00601c1c6444544185003041c05c2c104c10329080c61004170501c070801c8501c1640720b0b01c406181c0c0c2221082900c0e1007441710048000d54400c0045405680a4483c0703201003180441c0b480e0008003c122500d603142d00c0241020380072039000c1c00240c020750b900344c02c41d84c0103100c1c10081d0071030fa0300600c070a801a640f03440d901e200180c40381182407444a0500b421794020004030007041c0c0820103894480102c85040101481c40c0d000e210099400c1c4494140554440c1c801c00d03080799032800900700e0001d075919110000b98048403059007015140d941c01105030382c09000d400c00f114814125020700e440604442070502402a00c1c101e286400c101c030801411702e0f10001c0d00c1403c3d28640c0c0b00c80d034a0840b00080501c103011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 23709907 1250 23708657 23708669
    0x1030e150c030f01060f02030415110d1112040302130902030f0f1005150f0f060403080c0303010302010314090601030b06060d0c120b0a0f1406070b1006020c010504080a031404 77
    0x80100038101c400030020358041e02c01d0a488140c0c070790b00c0d1003003982c04080b800d0b03a400047c2d000340010020310360107903100e900825540c1404200301a003881e0040c01d110450008074007007001c440384404088030403c03d6910200c14112010308060660b070004410842580c3e50050b19500c5030103510541d5070511154411f031100c202115030200c00300031666100c480b4030703541910451400f00010411240c806140003154001000c249506012004100c1d200301807000c00c94005401340400700000d4541001089580581002903403658910702c0010150390f110802204010308450030301c00d00d0f4100007882d40c1542d5100a40840903075582c004607215004115403600428182a88200314030b80001d6030603844054880144440c5034040c090111074041071090021504080071701700a07030003016829541243c0d006001d1450720105448540100a06030b0341132101c100030300020800d07a5010002c1d03064102080c2400760502d4900f030483c80e2a28080d502c00707002c0c0841a072404148103080d00841d005441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 23711157 1250 23709907 23709943
    0x209060403051f050603030304020904080c01060b070b1303050f07030201090b1e070f02030d0509101d060f04080301090207051005100e06180106140c030403060902012006010501030e 80
    0x16807030a040d030f80c480040b10446038902e800c1c182584020305502900e403254002400131880c58550340d0a100a610000704107a40e400790502509030000c000303000e000c009101280c6030b81d4a483d01d9041409441318081c16059030102075484200000380c100003602c000490f62200a0f80b1001035007800d81c00342001c0750740184400411010012191428240da010341100031001003182d50721000240c44c0c120084c2105000b5034801d01000c3c4070104240c0003554013186100554100c1d0b20342c00342c07003400d9032040c0100a001c1250040c1c44c00b4241030401c281d9a000c4560b40e00b441d018182174070b03801001d10042c0204c4081940000c0c40e5007c0c82420003c45040b42ca40e090100502d2905800e090f1303000e0b8050042449118500b0046111883c1080d0066907050005900090a900e0030301c0070387d030740300e41d07003d80c0c0c00030310010302c80641c0c82c01c03007403001e000114020f0358003180f04540341c8001429100c1c0c505010038070900d00042c0000d880d50010f145810b5400a003400120b000c4802a0103182010500c2000396040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 23712407 1250 23711157 23711159
    0xa06050c072001021c03090503030412080a0504020a0902160b0c030603100e060a0b0a080d1806020a0b061903021509010e090f0c09010908151008030403020303160602090604 76
    0x30300200081460741d0142d1200307a5060021488640198808000180140c0c01900d80314000380d02c2c401203100003400340c18002584003040e0703200d5045401c122419a0007c9807280c2c54541550060f00301d1b68001400f01041005181a0b030010311880341c5c500813a414150701140603100354001c14061540705401c61014855440d1040403000300d580b04441e824000e004498510343d5504090189903440c8440038090700065840c401448000c05900508945c4040603c100054850083c040300c84121069550b000c4036005c4e205881d081d40c2542d1384441d08550040503070702e0225004446990300030360103e480c0210142d41085440c0d0b18192a08040d601c1040e103c1400401003c0c0002016114420f0305da032101041010308004da407043c00c86984140603c0000040d620100c05d00051006800c14103194405a0f01c0b0401107180001e10019028020f10110a000c1001420209031000300b201c000110b291070705540c04a0b85038000c0702583c0f40c00741c800140000401200f50152054842c002d40313826211 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 23713657 1250 23712407 23712421
    0x3230712150b0d050a12020c0d02040203040203031c050402030106050d03021c0201060b04090203010f0b0408150a09060204030501090203070e01060f0528080f0a09110607050c151b06010501080402120a0605 90
    0x207203902c05c0080310b920000782a0351301d409002007003551284100400300803e0361015021310010354030041080364140010420140014400c0014401d14141001e00081a00c1c1a1042c5402c4507a507420061040307120589001c0080d41c009000c00b0490065800100e030340841c1352090740540515000b1140c05000400c01182c0c02c103490b8041c40c1242d1600b4000b80b0010341d601940b64041c469805031500c04e400ca0704042c807000c070035100b54580002034500c0c0041c0405054803800200e8005400031100c61b5100c030308510640c03508024000240114400750710465140810140001d0341d0500d15505109000c100310317250b040003110820742415003d08840a400e45018000c01e24081100c020700200c2d6a400410ba000c0b82074800c1140c001e900424054115150004002c11500300400c2140d9502c0385000103c200d403500e00d031040d110a04842215100c8030200003511840352842ca0015541d804000104a00da9004403003e4010383c0654a40b4022903942c0c902c0c40c00c0c50040031001d080c0707501780f40a1141c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 23714907 1250 23713657 23713663
    0xc02060a030c1202040b0a180306020414041b020c04090201050d09050d09120201050a1202130e01080c010302120112170a0c020f0301020309060402091f03230712150b0d05 75
    0x20040640d1070f4040003030020042812801140900c6d0704150b000d119640c807550182e80c1980d030312800e00440091031941e0356604001d9a20540121040d204210300032221070074940101640612002c408015840e501003001b5590301c0319071102407050b40c582c0501c8007564002c404840510307488200c14001d01d0a142000343c3e407006050300140c000f03a521440000e00300340c40c42003600b4a55059666514040030714100700c64024580d000640c0c442d508110039500001040000c10007001c2c0d038614a8141d615243c0c030781b82019201d0750035505250041200d022205d030303514031315030648600c000a020180f14074103042e8402c202c150308920b041c480c0094102407042c0c10134070800da020701c212004420070a40348141400d0b4002074455060a40c4950040740051038a0341009601c45032400c0c06010f41250010303000452803a90b80241c4a60208028000304103a06c19090551039019000600c1d51601c2e0000295003501c05500242000000345000c00e80f40560350420140c49100800500407500e00c1d04119072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 23716157 1250 23714907 23714921
    0x31606080c131404180f0501051f05091308071416061d0103110409020909010b04031a040f0b0403050306040608010605010e0f1306062a020d02100c02060a03 69
    0x49991180020030159204007280c1c0c1c15040030b420101a03614190207078260030a000c04060340940c0311081072603140d402511a841c8140180c0d61055082658101a421180050025200c4c00c0e04040c568400d0004940f50104688058489001e50b0342c0721b801003610140c40700c40040528100059441c00d01500c007c10303c0c000008041503031003131580002000310b810080c2c400c04010031b20700414078060300d1500c2c500c1e521003036041c1000319034a403a1540c160032960241d00148182c80c0d0104a032034060416100d004d0140c1020b0020a00c0c2904540b00d404001c400d92030024101c0c004100020304120300d00c1034200c44a0790000106901c0c3c10985009061074008403030450185150090000b2000741c14050f0b00101c2300180c4402031a030310f5801c140b00b502ca03800182a600450355040840c0c0e81c003510712492005020650b00c00071308030387c1612804404006908030882c00c1035508444000741c0d407806a25403283e0b504403010b00030545e051074140d80c14210103034040e42c020b0001c21962981c1c0d401d41c106c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 23717407 1250 23716157 23716169
    0x3020f0303041703070501060806071e020705061306022103061003060f090603060b0118050111070e070206040201020d02030c0c010309110a0305060a06080604080a140408010e0705010e04050f040803150316 90
    0xc408c00c1c5d200d80825035149400c442d040d002400c040035404c03140c4020000021210750610555519076240c0c00811150360000360806151046424104522907060007030f150303a07250b2a0101d503000038076405440442e00003c1d0049109a602424068510340282c0c8244000c1c00e005034001c11069442404400605052100f511141d0910105c801c65620541c00b92580004038511141510300340001116208500c01440301d0300e210714440842d031704002d400d142c1e1251142d40c0c001c2c2041e00d4184002410590490120320542d0b10600581c012380b14003044010080c002841c00190003501c60516a03a5042000b0320241c200c100010080b0910001098203813141c40020703818440207a070307101000c1da1118200d401410385181402a1b0b01282d00c2030340b8a58065021854090510303848111490860700b00351004400c80d84617404c01c20032540c0080010b044800111404c010b2403400318445200703600000e100402c580c00000c0011151180040392080303006000e021603030400c1c01400c80e0b800390342e4140500c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 23718657 1250 23717407 23717411
    0x30604140a1e1502120a0b010309020301050f10050105121303050712020615100503040204020318240106031b0e040e01020406031e05060d06050a0902131a01030501050a03020f0303041703070501 85
    0x640d8006428000c6941711130b05c40c1412540c0f40d4402e42c1183c002c0c00c240b401d8a040589454000340903035024082d942c0601c00d2600c11605a007028a4040e2007440d03182d000d503040c01800e0019000b081000714003d988596442000c0a070070b56035180444207071184080040840303411118200c082030340042e8041c4140c8080d42c400c0e240403002010800000208119a4005842000001c00504042e0040c40c0c0000c1c4a01c1510960140c01181a0034422410070b10300300c640e01108102c0c06180464240c0b4010021810200705810401118100044507c0e00c03107000e00c05103680401082e2200c1d0b02400084000c03000864640b030f11040c006000d403c07005440b2218126404071180c10504c02d118090180c0c0004200100c0d82c241580c40c0d601401004041d80d204940c2c0308140360250300d84565a114440c1340b62800078580d11f506041e4a10000c0300d5180d02c0c1094580801440b01b03407155000001525011241c1c09a20884c1b44c00003881c6100e02c0d0401e65490b40501402c4801c90000006400300e01d2140000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 23719907 1250 23718657 23718683
    0x103060902040821070f080a020c01031802011107031b03020a080111030f180604082109030919080111070515040b0a0903031b051b030306030604140a1e 67
    0x1a15040e03008034003c41403503400030444503070805a140500011110710754a002d0070002d02d511506010020074809079000d520009500c815540d0500003154148001d0a04000e0000b20302c046020702001d40070000d050140581c540a040c010403c410b03c001d42c1c0c020b240001c600040c0d00410003e10051004038024440c4c4500442c20410602809124100981c5102d04541d5007960210030740e00003400e108106c0c4595000a00f4402041c000c01e48200d019034425559030742524018601d954603c0300f01c43c00c288591013030111292002c02191288242121001c10710b0900d13001060509205030710801e03c0e0b40c60000d90006507251040034010b4140a1425100040d04647d281610f0410843c0d00400d120b0900000030280c22895001850543c002d2030005284038103400b010600c1e0b0710403c1d0803800701d10049421908140801109003912804101840c21401c0103c0860382e5841c000c1d000030500380102c5004800f5100c10031024401caa00501ca200c50300d5a80103031811079112007a8250b44840710140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 23721157 1250 23719907 23719919
    0x182705010b030d0c1106030c16030302210907180204120506010e18030a050a05040302060a120e030408030f0a02120703050324010c0201030504030e04020f0903010501090c090312020a0c060e010306 86
    0x1d10001081e00001005d441020840c01c1100030b81c030081054102440c28085410f071b034008a0074000804d41b0039100166141e5904408240f800b00c000341910782c03107005104100c0300c076501050103c101c4501114034008610a6061007020780030b1a0420314200101848543c144a030010303c490494609110b18400c58a4824004070300c07500405000003d0f52080055a130354178070560040030307a10340a180050500e80c590b4009955640302d0700312000052050107000301c0c600c219220b04600da000c0000110301e041d180c003008584034042c1401551800c02d002c103a54031064002c2c440000400c8e4001e01c242d03070b01c0245140260040d00107848026440c0c0c0c0c80c6604400b594500c1c844020769420507142c41d00300c1c4410750300442c0580720080045080203500008020542c880b8000fa15044aa00201c661141411001c2c03500b1a03105900090f01d1600f81035404900075044083d1000f56030b0030001141001e100c0a009a140094507800200206540c2400040f015400381c42d60514203003d03a07090001c17540d50340b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 23722407 1250 23721157 23721167
    0xe011e051003030c06110d020702010e03010c0c060b0607050105090a06060905060a0e04060b0a0609031502030c12040501060803030408041409040206040603180203010e010c0f0306182705010b030d 86
    0x1c03a281d419411403003042c00424060400411a18070503e00030400d015008402c0d091a040070000703040241d004900c250440da046000e41a1410707080d0003c00800003017040007000310402c020702524080e43d41d07149003443d856001c1224052078020000f409141044080740d0381c1c0c0c4610f10000e8034034928210010912142d00c1c02068020b00004103804007503030a25200174a81d0380054800c980031a035a600da17114640701d15074400d00400007512541809440d508280244650360540b82034424410000c010710712680d54140d500141d0b1804210195950728900107006000760742240c42e139880701000f0442001407840081042e110b05103110308405c1c0c142c00034042c20b5001510001e6004605000c28030040d81310b40d110175898080f42d04100380c02e05507600800d007120054141302d807850b5101c2c0911840c045e00000307549180961441c0c00c01c54646042a2602c2c90b2142c00001c5c4079154442c44e1807210303601d05d0401100070318042255020407030414940300e03000f00745480045010b401013242004040d4016 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 23723657 1250 23722407 23722411
    0x2060106090816060509010e03120a020d03140103030c08210612030703020604061a0a030c090506030d02070605130306020c0705010207060c020603061216030b0603100c02100b0a090e011e05 83
    0xe5030280000f90704010341550260409030701c1c03904026040100c0d40182d601000031102c1075100d4000142d940c1d1000c2d100900b449000080b0f00181814400d000e003a003158002554111f941514103c50700203d20320344840c15100e200c0d50301022030550758803221003403e00302d00c040c01400111030104e0500500041a600e9000d4001c0240141e00940e001401249041d00b251340d5580304c0540c01401c3e542c8101c00219a6441e5410075504501658410302030300b243c1d8804e0903040302c4110020003000c60000b0b40250340b07000c14040c10080000109018100208008004001c1d40d4031800075500c0c2d18241c01c40c00e5540c41d40717100d0203005104840300080d0f03a41c0180c1c081480306801504041c596030710340061002c4410f031240d81c20b6003445581c40c03101c0802202d06281018500c00d0140710300600b005000c1501c3d05a038900c0c0c04a00500c1c008510a11580005440c0007541600102045590850000803d0100b60f03a00c2200d119007070981c40140e0f080194032080c10b1011042003207890400c02d0b02c41c20116801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 23724907 1250 23723657 23723683
    0xa06060804020d030e04020f0a0e13060302100f020c090106050a0801051014090f06070302070f0506120a0b0a03121101050a05090a030804080c031314030607021b040912020601060908 80
    0x142d03950210100f4803c1c910601748490241000d464103640c1403000d082c60748030108020004030f500021410743c0c6003013200b0000d1400100011b1203d2819500054074008400c00c4200030f220312400003014260080c042107040c0383d80240140b44035070350341c080500310b9400340203c440000ca5101c00418241741c200c69034000007203507a4940c1c0c0340619a002d00406da6001001103a401101ca8a12980c0b550b01c402c000c001a0b80700e903010701555842d100b054a8006695000749208550034030041d02c0310503028109a501005d001c0c0007140d544444030201d15664490313000070f04601d00030b202c04d01400390004007421050210200800440d034507035500c1400c60b40c0c20385485030f0940040d00d0142c042445005140d411174060b0b00c1540c502816030384100e1a46e171141c0880640766048101c10403034a444881c000003010310a43c00f40000c1c0c9003000c002522030048441e006110354108810182c0d07a05c4540c004101e1941c422140c01300041004806540d40c1000d125800000701c41202c04100d1000c04242c98a08500d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 23726157 1250 23724907 23724919
    0x71d07170117070308070606050a080304050f130e060406020a0e0d05030706051f030f0606050108060f10050c060108070e090a0b0402010c0f060f0c08160e0f060c030a080a0606080402 80
    0x10070b01c2e1505540b2208808248001c0c403070588040302060500c0b0040071070601c54030000642c00e01e800f00b8009107940390341c03160349540c205020422154480498821102c00105c407040702d00c0380d05480351401801030704122000340c030520003000108511603000340130b00d040c80d4982d110312080c4401080080598004010a281c0051100c01c00140d8140c020316004804035440325418080140c0d035200a0301d00d60310503584200090886420f01c0041d1141501900d030030305e091031192800070013080e428200101082d0007000c0800c0010070803441031090700c0703d2580c0c2c00709844243d65102d20301f40e503460751805100118060100800c400301380000d51041442c3d81311480b1007080c2c2d1a0313001560816a24071080c0c808034525054080044c09038030a1406410082c040080c001a4200008000d0100144000d54003030f030100746102d1203074011401c43c01040c0200c0307858441e0300120011039824028502901c02600c40400c2000c407040e00010341c5d9106440607071007001500da40310740c100d07181030043e50041e410030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 23727407 1250 23726157 23726159
    0x30a090318061b050c0613060905040203010b18030715080f060102060f0115050d11190305090a0b041a01030f05190b0105040203060d0c09090201090509040b010b030405070503071d071701 82
    0x10f4a0780a03115401d801001525110003c2c00c02003082e030380c441d48000c500500459010702c800d98010010340b001c0c01003901c046003158140b04205803240b0484a004c1440709045a8070300003a1b44c100305e500090b101001160920405514020740b000700b06851651382005188000f030800c6d48001800341c42181e103040c4010040e4039004600f904060340b2a10701d010004204510f21850196000d412001c03d031003c107030f550300c0410074000065803444101c1c1c90205420f00c1d0070700c0550300b000509240a25000b01000140e44ca4500d00b1a601020b01c80d0b505c0c0441d0b64800c000014051041c1020203007a01800c00e450745401c5280b526003041c45890741c02000c07001c4e0310740180480c0c00e0030b6000d550702610250160845802e2a200c0d056800d11541c0700c15542c0e529107480c80c0c02c650f0f100640200909090751400b403581400d603180ca045190500a040000300d0200014081c040e08112460050002406071048283c82d0032001c054407510442e020402c00c1e800d0301091000c1d106541c08012980382840c60b400507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 23728657 1250 23727407 23727437
    0x40201050c010e0303010b0d0c0801030809010e0607060e030403170f030708060f0301050a0213050f060412021c0b0a11030403090b03060102070305010204090c0f0207030312020717030a09031806 85
    0x541181050168965030f03001200c40300801000158003130320340582100e40316079280a2301c4040c0c0d401c000c0c02d6420030444000400000e40c152003a10110b46003400e165a045442c000810b91ba40502c2e000504840d0030a001084814400f0006000b41d9000d43e09043c0301460187c6005450701c1004d01416240c0c1041000030715080c8280540c0e41c0105008141612030703540640000e080d207034252a60040c05500280e111080e16010800000030f0409030380c400001011900040c0950080303101301c100040960700060115650301d1106181814242c605000c00e5240b4101081802012500f07040e00503d00082d01e40f1905c1010142c2e485580c0c50341c0d5101c0224205001e8407507a0300098030729415442030400100000385c007030015001610900200007118040c02c600108400543c50710300c01503400094092010a81c000e0084c003544104480142e5201000d29118000306070750005503101010210611401c00711035040b20040f54026176401a014040b00e214005d002c0d51481100041401680e102002d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 23729907 1250 23728657 23728667
    0x1406101b0f120305150f010503011503021309060f09181112010c020115090501030b1b0d1b030b030706020c0d0c0503010501030305130b090d0204020d0e070f03150203090303040201 79
    0x541d00c500c80003604508103940d0440e0070030900d03034070030007107910b82c000c100b04c056500840b000300050444100856241c40c8002a203544010b0044400192001c1c1207440c4030b500a40484400381c0c440b000005046a460701d208006000309d0250031440074429800003850b040b180160200101c01c1d201054000c1e02907613444000000c0215001d0b082142c44140f610828401c0c4115988641e954001240c1c003030420261343e105d80061f402400c1c0c25450301c40140040f4a20660140d0310103003203d0a01c0104a2940342ea1107280107540b4034031406810800308042c00000d4800c0480c0880181c2c40a00000360310300c080640b01c8006008850045e4081e9404400d9841e0840c0d030040150b019404154119440d000400d0a40d10b0036001540803560020701144011a41030407000204079600e081c03410301140c3c10000b0109185210042d10a1fa000b0887c030001c4010383d841003080c18188002c4030302d6241d89001d40c4044101c00d11055503807128100040c040e0304201e000f200d1013006e1303c00141d8503540c0e5036401511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 23731157 1250 23729907 23729957
    0x60d09020a051c0b1f05100e0603010303050a02010e010605150901090302030a0b0108060705041508090f0607020f15010f1e0b030a0203060907030e060703050a1806140610 75
    0x684005807540000da1900c401522010001c42d60000d185402e403d0300f03100c0f0341180c4c05449401c07180c21201c0d00c00500455075407000152601101e84d0507035025840c1c02220302000c4d0031003031580117000100000c10103030000014081d055682c3c000f1301418070340480e65401c962041c450315800c048a1400d440080c5142c82c002c00d44000c05040c16512a512600030030b16100041d81e080300c03191510001400040c60820036298018518a8400d292900301801c3d6415010340744540000d02042101040408138140883c1e48441d4040b02203c94a141c88400259030300000c40511080d400340700001c0c44032100002a8505031544050600c148501d405649424851038070303880c4035528018140403030031803200e20007140600c04400c8007507100c3c02c011080280f400d00c0a413452081c10301d0070340100041d0102046407503102c0c1060400240a95482001402a00c80301e8502030510301c00702d1607070040190782e0340140c4030300c00c03c81012105584d440040c480c41803201da071a00c02084561010f0000d81d124821074813 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 23732407 1250 23731157 23731159
    0x60c040e0708040210140d020f04060e15090d020d08030a0501031110020c091e040305040518041a04110301060303050c0615031c020c0a12060b0103110a030902150a0908010609050402060d0902 84
    0x80c94000b00f91f60420482e081901300b03e400e00350008003040707059441801d00c490031504a507424148546401c010350a881001c2503079004aa055121105540e100d001041c0003e400c12030741641c03417038102964001401c0c24081141c4a0b40310034642846424030102114644040f038008200010030b003000c00045d031000070245441140710f0019080213034490341d4644d008510a8a4007078130341d030800e0100010b4010403040005040072020805c0085101c9040440304503003103d520103c0c5449609004140c2e43d003291199426600704440007041651200080007030b01c01040c15200d40c1e482d5440c035840c245020f554803c3d410b500c11404132a880c01100800e100000036401220055128000401d000d48450703400b80141d82030b030f401c0d9101803004501038010588402d11b810000b07a4480c44a102680c01020700d40010141d60308035040454803407007280b00703c2200c411403058a500c00860000c0000b00240245a0796500b01100010f03505424041c86018640c010034040c10152104550782c001d02d5110010703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 23733657 1250 23732407 23732447
    0xf030e0703050a080406020d170705031305061008160302030d08070203040315230f010b0706090f05010b031525030219020c01020c030a0b011e08060c040e0708040210 73
    0x40000d4040104044052060001070b44552400c06c020b801d010b030702d003858014480e41d00d107080805420010055800821810021f4590b286ca199041501071500c1000700319100b80710034041703040203008c1d0940499410380c1c02ca84e030720764120300d10440d084041d11000f501640040c882c40c9999000d460750f59880703111441120700b000c0d5a5229074003001c55400c602040e181e55a1050b20151117607044000000c0e4603040c1400d003504110300790680c0b4940510a01c40c01d01030102d08101044110341041d00d1540e000310301c42240d42c84a0401c1402006600582c1c0d11a126011410700300034507980300e291184046480440101d0300e1030165031219500c00046c03e0400d139003003041703240c03000745e402d0040e01408c004d600400325040d8042c0064500841080c40070f200785d00c1030100038005490090120f0640310815008140c2c05c0710030070122080f09868100c45400d000382c00800c038441c40301c40040d0080312000c52009100391030b030220a44040506a0780a074200d04402840c104503030092484401200c00308140c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 23734907 1250 23733657 23733659
    0x6090d080301030b0414030304050c040b0111031c05090a120f03020702040c0c06050c040e18031309050402030712111e10020106091103010f0303030e010b090108010506040501150f030e07 82
    0x103150160388260002c4642c0e120f43c000780070030b22044408042c00c209400c0000d51550400d078540c16502d001d00b40700c081c86940c441d04010660703441403075842d8140c1c124900310f944841541803600001444d80c44101c203417603c0c040000b40c0c20240003031050000354029481c000501d403910300840b40c1d8028030802c2c0c010701d50200b00c804c006880380e1080c59900b00c016541c154020700b09207001403e8443c0580719024121081c081800014118621135403c0114030012a101327042d981c038a9801c0d4000c21011809030781080400289050007034008904c034600c220180e40c03001d81c8031120030200a0180d2800b0b040410703580d80c40d0559040142c441e8190842100c50b000c000201d400000701404081e840c00760050f5100c41080124800302d000b05110b00444401ca14213540c1016445500c2081a100150815481e0480090f10b50360030360050380ca080d0007078915440d960310f41d9510380c041d0500b541e00074007070b901d0200000b40060b00f02c0c40c03407108058999601001c0400c554401c0f8040c181c507440060041c050b500e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 23736157 1250 23734907 23734913
    0x1170705131703030601030f05070e09090f010212040c0509070804020d1401020d0c02010608010c02150a020c01180203060601020c090a02090a0b13060207150801062f06012108040506090d 82
    0x4140241201c40b000350360383d00c1c140000405503040c80001200c3c01d070404e0188200b05070012140078484c14240c41c00e0a0a90390024030710314102041c84950825440020384028018039902c5281c419401030098100666541e41403001c1d0f0001281c41e00001030070000420014070780341b514954501d000c5c1c03420320780c1c807040034201070708a0b0f100c0d060005403141e0300d183c14205190280180c030000c060f010000c1004114a10b4065102d61150703804da1100d078851400680b003110075038162200c0300f0410b4000c00558009100b505911680e442042c0d01c64455140011585d603c00208a6170900000c3d04299a41d00c0301d16440000c0c1d0040e0740c50a0340401f4201e400300d00403260001034101c90f603200c0b100080382440c115002c0d09120707282c1c02076601c418130008400719054103c85054110386c2680743c0302d0032182500c808070501800440c00301880c0d40b200c10340d0030074544001500b0750503074070112550101c031590503a99100c050240300307000300300003014031080005140c000c001e00b9000c840901218003960b01030ba = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 23737407 1250 23736157 23736179
    0x40b040608010609061a1213060c18080f0d110703020409060906062102060315060307090602100204030201140703090e040503070507060503060904230307080d0b0117070513 76
    0x1c1c205407066991960308101e04101e03030103404000d0003130582c0000f0b41c00f0302c3c28440c4c8840c460301501a40518548012880c443e8058150000b83c5401074820042d20190400c01030506441c83c810804021a41d0008030721540041810311000346c2d08002003100e0381d9924415580202400014407450007407000000150b2031302e008000c031040c425007000074941e01501d07103001101d102e50046c080070720500081c540105140d12403289407075011190192655100c22141c04c000d4203500841fa0003080c08014842c1d8a90486114801d892a64003a9010000819001001c80c02103200281c00503103880ca0164080608000401244d4000e14012007040e8450410b412080c2013500c01310f0b60760780000303034810902034140400c0016110078a04580f940c00c0010015010560141016000e08600c460010280c82040f0b00c0030380b9464410183c940303608003804c100700340da040f5540811030031742401441c0304150310403070001d41b51040c42120b48081d40c0303604404449541202200b4400442c10500102c1d80e03504032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 23738657 1250 23737407 23737409
    0x20c0313030204060602030c060c0c07050409060e010605012102030901020c0616020706021915090204050c270a031214040e04061401030c0504020708090a03050a0b0906040507050105030402040b0406 87
    0x111880d8a88510714410300c0304640b8294884021504240700c140810340f404614140c202d0f15061043e038440c8101140341c4e0804032941d0055a2151402062104020458020384400250346000300310496a5070010b4034400e21380100c241a4a0f00c200034034150403d50b03405581c00002c004001420029240401482c01d04160b1300440700c5020501129403d030390421160000d04003510160520303401107646201d0304120030034010704101a5a410007801c43c01688102500c6800070800e2105042c05880e011141d4000c03454001c001030b8192100440200d280314100c120032016084d004190b00c0e544400f0164000703041d46c5000c2220700720280c407403403c3e04005000604000d20728450351303042c580b0700b2004481ca10701144208448000040000c0345c10091400700300c6c0c1094601580c3c5400340e180c072042511510413042e50040b000760001c03050000009a50b12001d00c0303822040050f032100b142c1c443d51404211002840d940c0080000c1c05154400d101840e0010301c041d00114206901100113401d407041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 23739907 1250 23738657 23738677
    0x204030b0106050301080d02030c030d020c010e0a110f010504082508070e010906050d030c03051602091608060d1e030e031507020706050c19021903050307231c03020c03 74
    0x2003c0011b016805090101e00386940030b9000840c5400b0281007215260701070344078000d11190703004c100c07040003d8081d002008899040c006591014001d0703e04115201d00e0245418048e43c40d59240c1c001a5009504660941d2510401007a00004103442e4400806103010050000c0740401d20028444004100c02e4020300507884e490929503040240700011103050ba44454030550002402001180c0c0059000115030381600d40940ea9601c0500031070110103100303000a4006200c00104100110941c0075480c411110359a03a1070b40342c5410042201000e032030390b009050509088008540030407420070b01d010040c42130130150900005030700041d0400d07541c1c2c0614a0010f6844003008021541030110401a000710309043d23041140721861a9614030103512508d90201d281c80034a0159a00c500f4142c08803040c0d02407050550383c880c50301584941084c6000c07603601c0c0c941c0c0721860440107030a0010400d40500c0d0300030b0883d030000c00700c000b1310741245001e20000d25508120311000108140001c1c009046 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 23741013 1106 23739907 23739917
    0x103120c1e031106010603091a060406031401050402030d0908030409050613060b07120503041205161211070e0106080c1305030307110118050310020d0204030b0106 72
    0x7691601c88400e40804060038400c056000804454006025090b5840c0d80d070780d10429010340e004d0b50700051030388800ca24043c0301c90322141201548804000c1c030100b5415941d49400d4681d060341500c02c035213a512101003000754201041b61007103204061420f03c66482c6001c01460703c0c0c0c003070703402581034203601c0d074002c10481d90f1100081c0c203c8207c0c6000402c29140c3e10021020aa84110000ca17503076421844820440c034010802d8174401c030b41000012103c0b100740042110f2551106540d511105100c114280102e4000e0030380012409103507d80f00032070030400b20840c2c644551766005c50300310420100140106907100d0405900103556250382c5448801c03141072956510256040705d5010300c008100002806529845010282d5003070321104048214030b0342c20f0840c0c010714051140c00d40d00144070f00c0c8800500d80d000b8441004000c9005080c2916560340402c010021390141d00055 = true := by decide +kernel

theorem cover : BRFrame.Cov 23561157 23741013 := by
  have h0 := BRFrame.cov_init 23561157
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23561157 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 23561157 ≤ n) (h2 : n < 23741013) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
