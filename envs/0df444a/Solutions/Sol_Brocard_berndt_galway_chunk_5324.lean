-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5324
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:29:40.490628+00:00
-- url     : https://prove2.me/submissions/5925d16b-950d-48e0-b10c-430621b3ff9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 957374100 ≤ n < 957553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 957375350 1250 957374100 957374111
    0xa09110909090316030f020c030a0606050f0f0f01030b040b060408010501060f0302160b04030216090f0e030c1b060d0c03140105100c061518061401020f0607051c 71
    0x2040282600090a1140150007160000300301010200c1118160748100c00320fa40700c031201381c07021640c140c0340311005010340c421100b924001e0b48e0100320064010303100d4100030400d1400c20b02444210750004004501a541290032070650f17a403009900c90100c1c0d828a00000d15a02140002c2d0217002900304180e007002000038003048d03244040d0045410396241e500e500070080c8120704200c00724070580c01503e9203844140038072000a12400700340c0381c20074000d02c1100ea005c8ac0c120b100d0a981c0380c8580c0114a0309607510503a06980340d15004002000006d10055428100d0310711f14591181003129009082c0e01c0c240e21803030842c0e0f54690070b540d14070010020400240b009054042c009105061010072064491000000c051a05000809a0100c00d940e406e04201c0b5540d20b0f071000d0891130240c1000031542d81d801240700c4d100e400c092900d003075850001103421482d00040c6413401c4245c0c20900c0c119007182641c8140014001210340d000280d07460420750710234030103003810218a000b18a4640007418039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 957376600 1250 957375350 957375371
    0x6071d0d1e110a030f06020a0915020a0309050a0b0415020f060a0204032612180111040f05240306031c0806010801050907020d0e0f0303070c061407021e0a09 69
    0x1079600c1294900c61640c1d81c59402e403800c20071402c0d880301c1c8001007949006050000c00500150050310344420039003801c2a800d40c8601d81050300c81307454102d00700181c0c89415560240b40c1c2c0100c2c1e81d00105000e49444400701d0a001c0010304900c918005c03203000c1040402502e041038800c0113040340700064542618a80e040c003000c24000307540b152000f0f441131804c15942e094030003031710400004401d0030350101c0c80c03030408404050b0142040080c554010301e1710044261001840a008014000e503203003035616962410208150384058a80c3c115502442500c50f18058070881107807440b60051400310403580740c3d9202c0e40003910b8903030800e01a074600810140c00c031503079942002c0104c0c0242c030b0036220f0300010b0380c90b41d0501210140880352500103900c0304101544281c002c6e1541665a840039085800e40711240000c68590782c4010011103030030a80d41410400c0c0d07640000308101d5038440b104140d150420725000a506003209050000440361803829003411546c0f0030f103c1000402c00c009051080001c2c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 957377850 1250 957376600 957376643
    0x60d180c03081308010606080601080a0e0304080f1203060a1a1e0a081503190f0f0515070203360a0305010204090c050408070e07052b0b0306071d0d 65
    0x43d2404500e51000a8400304d43c000041c060181981c3e115a1100d0301c550b650310044601c900003924400034180e469455550092085c001440a065050002c0c00b42d014000809807030b060003001d4000d0107080600502c44079940c0c9261a100f2030340c80301085280701c025103c50f00e0341c41c881d000c05040c0000c8901c9001e010410728501810702842980ca400d5001d40d100708210210404504019500d030b00601c40b901e90300308440340d980300c2090003400d50750f00030034250351866140c058068003a90396910200800204e0031148000c954081c0082c40998100f4500c101d030052030101d9407100801c580800424010441d0740e600320914051001001c1041d143e50720309000e030003903226020f950170a904101c17106124a008004840840f501c1c20010040799241940c001003480004c0c25a2040080c00c1010500c07103504013003040400d5142c088001e0440e258400c0310340440d03000340e169074082d412403420405281d400c500b460b021000e240f051055603e01710400600030038400217001b000c010500f244e01248054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 957379100 1250 957377850 957377857
    0x902221401030c02010207170d020d0e0102030402030609160b1605010f05040201081f120203160e1501031b0311041503060e0a0212010b0702030712030e09070e060d180c0308 76
    0xb0b0b2400c200c40010950102d090303101e0002c000d00025400440350400303503c9240107150951384c030b00c401400c08142c441c01c1000da400024400d1a41e81d008402d00c02540b60034440c1c40d811030343c10401090b0229513185001c007906158441c405000d4400700b03003419840c01c3c90401d04080c0c2c1d03201d002040201c003040080002403005036070603400074a4500006201c54070900b040b510717281d070082810300518a0100100800141604100d805000d00f05064150303040c00f01a01e400b81600d90b1540d01c6910f041015080c80e0003402480b14109030405201355008010000c2405420406180c00300b6250341c0c03c140c03410b0074807640d84290180c0350400e0071941da00781e06601c10b1066401d0024078444075126100c040040c1c0c00b41d00d44c00b000640e9080c00401901205000610b900d03840902176410496441094070710081f00c184040e1301064014400840925290144903404829818181c4200e000100442c0040c095000340c41440356651400c4041e400b0022500000036600c400000061510f07443c20842642 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 957380350 1250 957379100 957379139
    0x3061d040c0504050106120f1d1005060904020607020d02031c02070612020702030304050910030f11090907082515091706010506180f0904030f09080115090222 70
    0xc1c0d0000c004240c03840c16014050403180c10782c0d075001c00202402c9043d80144045407140c1000c6960b4401154200b000440c80d41044818070007400062009440503c1035a0000740002d106207000410017005a58250660f2400750b019141040e02c100c007840402e1402c0c07031682c0b504200140e000350040340d040d4006500000d0b12503990300e0440002141c06030400b0fa004180c0001d5140c1c20600c03007884a801d00c80303a566807107510308806529140c0c2d2a01c0c4c5c0c1d1074110b1010000c2d111a51030018240250034030b08125500802181c0044c0031031444d15001c41d84442c00f8207040084451920401440001104801805002c00460480400c01110006484210b0a128000071b402d04030010f80e44030200801c01504035500a002145484110300204291406e45007546520807807003990711106449002c0704900c11407007525075850002585202604050351503000c16000c0e81042200c1c01c6061405100004540a00c0c40160b06c4070481d00300640418011840800c01100c1000c0c00240f8110504c60141541c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 957381600 1250 957380350 957380363
    0x90601060905030a080d1509020409060608241003110d0614010906050f0f0705160e330a0806070c0221031804110403030c050106060807020d080703061d04 68
    0x66a4940600d1346420210b00060b01d11131003402040604911504000c1c40d110600b450b20108a44881040c2d0498116400136010607684240911803540c01564454120311a00176419404050081441d49248407400707940c0280a000c242220382030180e0000840c15a4000046807580c0e00c900e910750040c4018854034945c141c210300721083d00d5007d0700491040c0d403031075036940340f0302500c0883c1c0c4034941d40902080c0b01c03200401c00020700403a40134014a01d150103c000429a840c1c0b030854803144462014140c61641119a03014003a100341e02c0c0e40420040a4280c0b07106614003400c000a07000c50950340c0221018010f80b010441c406034000c1c582031505200b210aa0084264140c5031102d178400c145034038484d44c0c010088003e620000b080403046500005201088600c242c110500e0b035500294801c4020a041c6240d03401004000c0c0180320161075103281080561404240095a40c15035014510a100c110404611000c1c4a608a100613050348100c000603080300e410381d590003590440d42036801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 957382850 1250 957381600 957381617
    0x52202011b06270b01150e04020d0f0501050105130612140408030a0c0903021020100603140a03080c0d020c03070f140d020d030c05090904050a021305010b12090a0b09060106 76
    0x43d00746448501c074000703801800c0100309a0800380c404d1104001052040140106800100312580e210f000a00086004580c089070005c00310300a103040e1501a00040d061104c24400442030707210b98456172013199150325080c0000000045510010324210004030080740000b0104014003030038000550289404d2a000c115850218000321808141d43c08000d511a05e111301412003288078810007070710044092800c0380d58980c2d01c88164a45032100718a106e10300e885180c1002440104404500ba40707241c50054141e40c0600d41c7d0013807059030000d11007404041c0102e80c3c01c44c10030003139050702d8070701c1802c3c000c59a8400d05403c211240500c9600100c40000e0241d18041c2440c0000c1a901c50800c1103030002c1c5183d08103d40250702610180188804014040c421010f0541d625080280660301807006040e04880500500240c0031150090840240c10000104207940101044517000c104003d040070143c0c50308410f00341000c4545801400340032800091000195010410074122410364991190 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 957384100 1250 957382850 957382901
    0x9150d0207051605090a2403030e010f0521040503040801061d06030109020f0f060c0601121208090d030c0c05060703050609180604111206010314010b04052202011b06 73
    0x1840f003d01c0c01003d0f0003011000104008401d01d41200e80c00819141c20368001504107a184080c4002950099000034203041802c842960440c81d102e540d06854600b0b00d2034814144c0880e00d52810000c181c08015100c04c0c0080c0502c0420310039038010f0301d0300d070b0000d010965032201e0a10b902c012035101c0400b40d00c06140030403150306d014400c030618203601170f1404200107401000c210014624041050300000100880e072600c201c1802202e001c0c00001001c6071340c0040900706000300b072000f104240b041c044081c041c0046040001100c207800c8102e490080381c2d003010300720102c0d0007002481c8024030611172441808400c0307425810060ac503c8055406900a50b108561600049060250301100d1382200c0d021501141c20780030a20413002020300510305c000010f401702c07480c01d85c09038800d035891158844003408800c000e008000e00450300310307810300441c24050a000f000707105000e80048420900300c1158210f900035500c085030354501d5030403024030620504080d0701070407a02c0c03865040504880d01a91 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 957385350 1250 957384100 957384133
    0x201009150306050d170f07030215130302060f060307090e0c0f010815010815060a0c1a16030207050705030715080108120702060c07050301050411010314011a09150d020705 75
    0x1411035000a040104c1e9486544176241c284801800d520012101040842c1035104c00310003d124080c803a0b4010704500d080c5110200e1480006050106003c0000c82c04101180d40060b003e50450f42c030b0b0007480c42c40d80754500000e240c162030341e00050201d401c01c030140710182d030b000c2a003441060f019148101c450200e4001101c1c2c136032044601c40300054000c0b4452000d944034601e01da5200055082101e9145030180000c4c0c5541c0010303c2140c00a450000700c9810000803440d41d1921b00f40d600805000742c10042c101080e6051282c202c44101940440d0390b1080c0a400c02120700100000340540307056035224001152101040c500c0d50020540c039000014610400088400c0000c610303698250a260700d903400c01a50745e0000072144402c0c400c3e41d60118442da420700c20280a10f11501640a00340c0e40c40c0c1c00034040e90740d20301813a40c00a081e00f00400c202c0404000c03040b101c5c84030b084215900c07000113002588441a001c58a000743c0000f040540402c01194028100d0501610464400380240403030b08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 957386600 1250 957385350 957385361
    0x9061410051e0903070806101203090306050903130b1e0412020d021f0e0f060a0807030f200d050c0301030c030816081c06061403042010091503 63
    0x180300140080156101c40245202d501118070140c0070b4481c41c09200d480028078203501900030901c1034000005200301c0c041c6d80115003000307100b890087c410701c0d549a2800b0b8000055407101400f0305450b4800a101144244103d500d6007003800d8152503200d440714030071807080d0030190307400124269800100003803204a01c242ca044407010340658030184015820320090810102c0b089800c40d9568800184641d44288400c0c0000071a5450340a0542d503c070401010300c070012201030091004001e46c40d545031303021401c182d008066080111315881c00381d0200d03006010940c228041c0b404401980782c0c1030190140208540c040d404400d000030344a44c0d00c0120a07120a210007003003900c03000c2c0308100141c00000034049802100c490b804000340b0944495107541d0003a4040c2504850070001842c08442611441015004038903128075201d0321080c400160b4072002e040503203001032002d181480a1040075034012907072070107000900d040c440b90340702402d08000303400340421101e120180c82e07107400d20900c601c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 957387850 1250 957386600 957386629
    0x5042f030613021512090706051c0905030405063f160509090a020702090f012d0510050a0801060833190f140a0315090507090614 57
    0x103415580ca50110107140d2250b01c0034200d80211401c01049070380d885150141c184009200c00f6030280d4604030308024103004d000d400c4141802010f0080f00b10780c16081c0c14040648201da080084c2c50000303400c0c981e20b50302465210310ba21060004880701043d03105d80010f505221102d5500c002103982c4044916008224150301c52110310b8100010350345038481c1ea01c5141409103041c16813412a04d50301080ca85032040305c0a00e170058002404500b1410610703995617025094100b0700c1c8103941070440c1300703400303402c8a1040c00840355070081300b081c481510881c00c0001c00d030060141c0d804100c1200b000e403a40c2c0154801b4404a072546000007a00f600030000140f1880b014a00c6604849001d0703190b00e0070380000301100d00354400c0e44004002a231200c1054258110601c201c015040e450308200e41084260380c2c01c44029184506030306402c507200e00e10344000b0340e540131411481d46c0c0414100c400c0202083c2d00080c1c6140310340100003551107800d5104000307607011820f080d42000801421b000900402a01c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 957389100 1250 957387850 957387853
    0x5090105030105091c0903061802032505121204060903021207050108040b0a140930070f02150d1b031b031e020c06010609170303060d020d0605042f03 66
    0x10800b000d01700c5400003104031000c17420801081c1d52680c54410440d9419001e0b80301919a8150b06000d500c3c00b0000760382010840714040c21501507080901c008501c03d4031880f80031717842080f182ca041b0341c000d0149601c0703607042c2d0306800c0c1c403507984020013052103015100c240d01402c1004003040300d80394049040c0d01a035406845010b200c0d1102d580e04000d6850092060750aa50385400c0c907111200d9901a0301c0c014513100e0001c0c6a0900102c2010142c49001c42447c01050b114071580c44401200b44151072549030407103045c2c4155400341c004615001d008155a088444000515107618245613001c00d40c850400daa181036000c807079072000e8080390100d00d002c130b0704404812a9100365034400c1e0403d1100107480210b038206840d100e0606001c0e40c2000c880000300d0b8000700010f101c00c1d5400f402c00b40c000e20134071040e000400c040f40c0e000c03600d0b403002400041c0a250748019800c15911040c55407040380380c0c01038081025140078200641c4110705910131141c0800c0300d1105100c0040c1d50401c1c0305800400030b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 957390350 1250 957389100 957389113
    0x150c0a09050d08040605090d0206180a08010e0601171e010606170c0306040b011103161e0201140307051303150606091a0309120a1d030604081606060b0c070509010503010509 76
    0x14051b512500110b0a03164010745d0b103043d02005807540e5024000ca02d0515645107075601d010740800c2040c0d081034119443e540e01d040a1050040000201030341184c0031601d0f0010791a02580700c0d1824451003100411030b000021400c501c599205610140840d0301e955941c020000e07581400b01c3c0b403044283c070202a0200c05201040c020318065000b0760055405062011050b04000169030442d00020520400c2c00f5000a11b2000e100b80030b484000000304000543d00107150541c006040031800c3d81a02207001d401200098001e4000d1003160002d440c40d03003005514a90301d107041c1f0400d0244403a0f0002c420f003080d00000b00c2c680544042020380b0300c404015542080112400911a0001007800610380b140139185507151100c00010185080155100e080070b2580c05ca00200600c10418410301035848141013002142040f01a640a0b08901001c00d90b414900c0c1801c0014003010b0b0083c01178460001402142000d0004080c41110001e852000c80c680c1c1e40c008050807030f00211100b006a802c4103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 957391600 1250 957390350 957390359
    0x1602010203060915030a020405131b0e040f0f0203030403061a04060f17151005120307050303040204051f080d0f0c0f06020a110f031e071101080702150c0a09050d0804 73
    0x10f0700b48040134240607084401d540519000201944c0007038482580710002007203040b0522109403030000d04458007080246005140013580108044000c00c043c0c41f003001c0e01c01d0300341000f4003100d80948841c2c0080840340c545072a0704010000f00303455540135104010807a100d6100341020b0203010308440c91801050656840d00504002401d43c4004203070090013603a0154001c9014646024041d405840020001605100912450414820107035910380d0050241500144000046944c003030b070305403400b09a80d142c0381c2200301140c50308081d03403010040408010a44034000648414400d00f156503d1910841b203100a0380d05000381c41c07000d00f2000c0310f54848804903000f43c000300811742e0a490082184040e03280c1090618280e03024102c0c50340c100140700013616941107041c8481d44903402400d850701342030340d031000920a0000c4015040c40541c1c1c0c0042c16181c02031110f03028800000260b095646400c0d5103400d007907841034940102240d04008082002e0804140e010b00c6642c1c820300c50381c90582071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 957392850 1250 957391600 957391621
    0x60411060d020d090c050405061e040c17070c030f0c0203060f130c06050406090b090d0b0a0e010e01230103080418020d060e240105070605090309030109030816020102030609 76
    0x10700c401e5086141c08200428980042c0d10502038402c0c020000450707210b08000800c03042e0b40c0301415280c800d000c8480e0010001c03004005200e090b0608480010b4040c03d400c9003030700c504440001346c0054103503410400c80050741110b02003002038820b03641c0b4080f40420700e0f02549c0c50604140041c4d01544110001400040b1510606400075007070003001c0b00c40e64644d030b680c0b815040c0c160840000520041000c20120340c0100c10b9001030000502e00c68202008207002c11603607407408a000d0050305403500032540e403429a6202c1001d0045600080c05160490f4030098060b100e4200ca0000c009030b9009030010642004021a068950099280349020b2074054521000031884e10490080eaa013002800e20f45940c23032180d60b0061003000b00300320041c9401462a41e0000ba0450030740500704502c48031880c540ea0040c11502c50725880b12001802d5203c46400314130314000c9a140c41d0b055840c00040300c0605810000180c49800f80c2e000b0381116490460b001c038244c0c0402c4da40f09810080c1d06001c40e07804c810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 957394100 1250 957392850 957392857
    0x515010302250c0b070305070c080a110d063305060f0a11071e061b0203060105130b03030f0705060a0c0e060703120f1a120d0c0f050f010b040e06041106 67
    0x6510001c01107407a014101c0596005c0c1c0c204401081000030038504000000000c84028011071001e030955010944403c031420603210f070400d208a01c40713480c0c9010041241d110101c034440c0400c0c1809040a2116802c048946030000507030085007081c400a00e0385001d000b15810841a8081035040482442e0700341c0728580d1126880c8281c1c00f602e64041120000a0301c10302c29084012080791107503141a01c0a09028003602d40001610b04040c40440542c60000711903044031016600041d140400003040300c000c010341d80f0b0280c0c3c18080002c040110658000150041034060800c2c4c41d203a840d104029170483c1e00708160b03103000c5903d002042c0e02da450310001500205000e410b103802200d081d02c00a208031030360402801d079025500d0b20364501d503000b8614501007a503801d071081880c01a1484806690b0804090303000d0030480440e0071041007010003001e07a0324441c3e02c03000f00d50f070135298040b0250291800c4184280100d1402c03c4443c01c0e013200040c03440c080d0350084618100703055888240100c650 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 957395350 1250 957394100 957394103
    0x15060515121b070516150807050903120d051023100314070c0302120c1905030c070305060402010305100e0609220813090605011d010212030109051501030225 69
    0x14165040e910b100c252001840420b02c2000034010103442e00c1c0d0007015a0082e908450140071041100180b030359004102c8a401282d2800d041c0e0701e40088100181c40e10840007504032000c48042108524018650072150003a040034000b030784400d0716800d43c02e01d812011451f0500d483d031454049006c40c2480344903416508041d160100b040b0b4413294200d43c0d4124140c4042d40000c40c010283d02c14550f050110f0048a400300024920b02410303000855070b00c1c0d0704000c131108000c041c1c01f1000c080201c20000c80d180f03424690140c81c2c01d540c3d24103200303450350000c0701c0c20b902003170900300040c1c03550261100300d005842101a80020320f407500f40074040d84950042024039141d0040c0103d1298400c2c07014400901d034860541150303070746e203040c0550700202590307070000d07426030300b4103100744043e030780010305210385071611500d030303e0301c1d25007000100d103400104111400b40c850000008507141400ea00f0061082c03030400c0c40320b400003054000441c201c0c883d440c103c40c908509170308590f20581d10b013980c0c1105c45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 957396600 1250 957395350 957395371
    0x605061209123a02040b0a080c090a060e0a030f0b0115020d1403130b090109030216060905120a06020406200703110f06070606060e12070e04030302030405030c0a1506051512 76
    0x40740c4100580c00305e1388281c0010481d54004101541d1203944185100e07440215000c40c58100801c903030128100320094003c903002d120301e8030a845c10946030a4801002980c000d4404e0194580e1400e207400c9541d401e000e51010302d00007141045100d400021100b034000c0507a9079120054034480e1000e151a00050842080c810b180c0e00c8140c04640d800d03450602a0101030000142400329140c013900e4486084401e81242c3c8940c0020000550401b10541c00c5a00030303201c4485c00800700000d181421381d81c0700300521580c404200852110350207030000d410302c0e0f0414a90a086180029100c4c1e8941361480000c00d580b50035280300301241016144008251806071045040440079524002543c180d5000a000201048180c0c11107250480c0403c64004501e8003400071107040c2501191401c000505c050107041d00000400c0802604008070b503020503140b0203440500030b1501e82500845d800c50444503c0904098003c161403600000071903500414904091820600b240c404455580043c0700b50b424 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 957397850 1250 957396600 957396697
    0x6050304060c121e0c0806090a090f08031005010905010c1104020c0705031c0801050a0812070f12080910271a0106080f070306080d030b04060506120912 67
    0x45414030700070030301540340f10a0780d04d030b400d003410030780b4030441c0c84500002003040320030424014180c89503142c1c150440941e41012400700c2450802e000c2c01c198111004140100000400081c44841c07800c0d54180c500990b00d0b070890700d607142c00446e22101021005040c03080780400c03c04007031810368000d24034407485000740ca0409070b03a10700180c28030341004044180144005010403480d43d021441d940540011141d4029480c2000b408075603440691400b802044e500007012810301501c4800480c2c0240d010b8041c070b1034a13029200092a600094070990f03850f00c101e140c0b800403036030140681407200321200f03103c1003203000e13425a00041e81c00d0903205541c519030043c01d00a2440d041000319020700a161954201402c0c82c41800c0070003800141200101882d180d01406101d0004c03404d250b07043d000c0d181c045017000c0004005801400190b018a902610005400302c0e025202038142d841410487d040d101038000420845c0514402d48400300e01c2502940c10804d8403807050310383c1c545200307004501d1b03600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 957399100 1250 957397850 957397877
    0x213050f0f10090528050111100b0109121a0a02340501020309030c250905060f040c03090201030f05070806190f0f050f0411250f06090b09030406050304060c 69
    0x2035403400e804004443da180c3da0140c0d2100307045200707200c0101b0003840c0084510a0b250102d80d00c610204c500710140390703204c40603041980c0c410401c14010300303035211000421050a15100e03048040740c025400070b891800c0001204450035209031401c0038445110b0b898503081c8001c0a08a0002c1c1c2d0440034042600c0d009148040f42c000d1000c1c501c1595030b540150f5484944068440c0350400760850040c4180b0300c10555a4a10201c0380500c08450b03111001040a880300000150a43c801001c095003041c038046409282c1c59268010011990003038a04000300c44604a40c04240d4804032400c8004c500304101081c0300d4104171400078482e45145138240c04c8952101c03605401030350715038001c504428802400380410b20b4030107200300994004907000c005c0c582d60128192698010f0300c400320740f030b0b221260701d20b0b002c0c000d0300c00340c0100395a010140d00c0010f1440d10b030642c01004807100549410244400044005800000311015244181c0307549095960360394400014100c218004e40811001d00c00615 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 957400350 1250 957399100 957399109
    0x170901021203070c021504060e060304060b180703241e030c0f0e010902160210050405130e0622060209040605090f0108010c090b04090c091205010213050f0f100905 72
    0x180150619a56606014080e0040001d00103d42c101e5580c1c50034100408c206190700000441440300e0142d60356a100d03691401d080004007869100e25400030f601c03807024038210005c0c0390024401c42d240d0b10108138890310600215a100c0f91032291105144030034000340b00442c04504001656225200302110040d10ba036a610954000d03a03012080403950010180607180c0b140c00802d001d40443c0c2421424407121700b48030145c410300800003034000c0c03c1248004111034820400c4401904001e82603020014604c060f0030001c100b40c040c0d901c01c40c001d070004985c40c0a02171a90040102d00840e12516005058a81c10001e5008c041e40e02d0b40203503100f80000e069110441d0403031041c8001240d8014642c94209814290341178410803d0421004140a202c42006002910f0a0f04c00944000440502e142010380e540012030304243d0360740908190f10030070400150020081c90481001862001d40e40d00e0138014040c410314802e951100c140a2040c1310750034025242d100c4200b0920303000c41282e6888002c035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 957401600 1250 957400350 957400357
    0x6050c0405151809090a020112150602160f0503030d0b040212040f05151b070c0f0f030c0b0915030601031b020706080c1e180433031709010212 63
    0x10010301c00b26418203d03c501da40200c12428040d94280b00d02c0c41c18405040c0c454183c250000e040c0005040d0007140207200d0b41c40b41400b02900c0c0040360b00c0343d489800103076403a580c00c80340c41c2d0008038000340403894041c00c80c18001114000740003542440802d14031080179041c046841ca40050b4244032001c10603080071130f1b460286010307184005044040b810410b0078281981203600e0503080c0c20003404001c3c0000310300441441c2101d020785894a0803840d20100008581c5d0058800341c4c0e4a81c0d01140c3d01052004e04011a1705c900007008079995224002103da02032040d80a611514909003d00031200c02d070002e5520420524000610340e2180380c0b51041809003200c9100142c1c8812010302c01c0940004030b694006071074064590815804031864010700700c01e200301c0c00c54074201040502420340803082da00503000e401081840343d20302c4c500c8034a01340c0d40c110702c11520007903000c8411850604241007400949803c40404420500c02c8020442583d001c40c001a0461080d1103440ca4501801e41c0503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 957402850 1250 957401600 957401629
    0x905030d021b0c090613061d0609100e0601050c0319030b041109150703140408030304200d080313080309030406020c010212120411030f0d1b030c06050c0405 69
    0x1a29803051100307011504110280010841e0f01c50510700109540380c00c110340c0d018404903401e00f03040c901c1d000107001418080d801091340381e01501400100d44810940642700f000c040c1d80e40206951403220004a091440c03180e01004083e00300450780d903500c103000606004016004592503c100c17075030350305001905c60300c442c00000d640381c1c1c0d80d034040c2c90240110100c90813100345843c10606154006a851019801440200c4400040d41820103029182e02c1c01500a171412081d20340d69079101060b180d920490f411203808004008400c001c114605060354414005080c01508a001e9950191107500161140e000480c20700509c000140084008500c14900c84010b9612685021800307849d001c100422a070541d040250b68400401d144000e84803d080ea0703501072a02d940b51803c01c0441b0340c040e0300704e180d00350207440300c000c200c44400180045900100d95410354450749805100d1180c1991040040010303007603140980c0442e0f050f030003135504402c410309003500c2c01d03648030006000078000600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 957404100 1250 957402850 957402877
    0x601030e0618100b03100e01060f0e1609291605011d030301030215071106070317010f06022a0d050f1917210a2705060118090503 57
    0x100c4640d054002d01021843c5150b103007003407101950040010391500150a0000340d0140e1b1400700e201480000d411200c01001c1d040360300d00c00ca6448103030310040d03404121800100201114903091103a442107c5400c00c07035521000c00580c55856600a1a400780701c44003200c0240000c0c040b44441043c61464842c40078400c1000081d006049508901521032414408600d81c0040c0010809038036807a50600342e80403540c81c4155210344a00c0c0c0f40f816001c0302c41449400160216100081507045242c800011040a030808100d81e62094111800761450045000503008418510342c0c2e620346d5000b0013080304885119010342c4041c100400c0c45101c01600584844c2c1c40f0114818818105000200808010654180c60b13a4403e07110940350314085003030202c140100107243d10f001c451121200b400d20042081c41c00460804241c4900504803207043c3c0f22001c04030440f0b40070040103402407001c0e0f00d6031000241038a40e10740200381d5010304680d04244166900c50b61008001041030004198405880c1c9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 957405350 1250 957404100 957404131
    0x606080a05010614030c1c17032a2a0610170316020f01050d1401060f050315010f020307080301030515060f01080a0506041e090201020f160506030601030e06 69
    0x7001420b580842e840940b4126a041a250141c0c402089149445038244d0300960800343da0082c80c02200d000c148040c01203681d02048540042004e030003540944034240300d22030f484c1105140101c054001e400c83d01414002009001c0d059030f8440c01810110301103c44541500800c03e456078103152040702c5840b50185003000500c090710700d04c85200c0c5031146500085080c0901c0d940c1261548a41d48000303803061019088012440c0e2145003150748824002308180040c90526101c000201002e0140d030340410443c8484a0b0b185200e20184d92180140994500c1041c40d084015552486209958411404100700e04000319005a00940c0250b10a400500401200c440400608100030385464413a400c121400702d46c903a0700000040c1c20400c1810300040c0344d100d6000250041c041a0035000f942d18410300c4004408005900000445000381c080d034043c1e000c0d0450264030303640480e080034a4600d04500621080c20084051640b046041c10b001070b411051065251138000b04548280f04080c410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 957406600 1250 957405350 957405353
    0x60f0d0615050307080c0c0a060c09050d081617030702150f0403081803041e081002031003030c020102120409150621020d1103040b0109060503060c0306040e07030606080a 75
    0x140314240042a50300d04400440088000041080c0700143c84042049611004641c20b02151384c1226480d010700005c484031f00b00f4902d0000041c2c0b401071400070204856100020346d03400c0103c03140400c158403140591804082c9651030484600e40c04050343c04d0319000d80c02100c12035500000314021703225500140315690030001c1f5a40240c00c000c0a0424a0043d507083c800001c0e0032114041e002030000d030050210001d0844c519146008951003990381c901c40030020710b03403040d640380410300340c50407002521000c6000c240795205a03c81600c1c0030a81c02810402040400e00ca072003654100f51051041d90549603104614070920b0700300d03800511300c903603841c0500c11711402c503408600f0043c0480e05140420b50b00112448200c80c0c008060512038a0300041c06580381c41076036011040c860f0040400c03907201e00740303810b1a4409102c00d0080100d280e14208012a56140020b002c0e44280c900d81c5946180d81c1d5940c0c18800a44141100104544502440070000a440340039400c0a005510010038020049 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 957407850 1250 957406600 957406627
    0xc0b0403200411030612330c0c0c010c08040e010f0617060109060c0311010905030a081b0a03020706021608030601021203040b07050a050d0606050d1b120e0a02060f 72
    0x20380031541c852460514044020030b543c0c0103403640400c00300c42c400000943c109520382002500300c0c0e05c0b2142d600045442c1003860040001150345103d0654002c06581e50020001c0140300e900790002e090750040c040c090035503205002c6c84100c070f8030419a2900b050380e150f40c540000d40c800e8201d54010b654881041c00130395031140c01000340c4440200d100d456801d1800c000303031001050b0b01446c800c019072a041c480030700d405111b00307225006002c0020031451000741480b6449400400c50703031000560f9100462603850481c0108402e02011a40d0640b82c12a2035000b50002d6108031001c47e0056000d00240540c1501c022581c030400780a40e03601030303407860f10030b000a08140c01c50328219205241072080c400403c802443c5d85a00c1040d505045548960403042a901400398000841c5000d06042c404100c00e80e00c00e000d05288003050b0700600a24038500804040c010071503040000060144c042c181082081c0c1c0c004a031050700d2141034500c0b141c65a008181d180e408000c1d06850403800007410a9001007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 957409100 1250 957407850 957407903
    0x7180807092319090b042d0302120d0b03031303020f060c030f0f0f0d090c0b0406080a09150c02010504020a050a0503070e071707020d14250c0b0403 65
    0x3890400348142c8002040420303007810380600f0403d8442291405443c960030340e036102880030f40d08031034410800d01d0301c1c0ca07001c00c0a450f03600c8182c01403401c0c403071107102d06019194101c080540c950060004900a4a0403009980000a00000c0326450784820038070340e207007032008040707000030640413441c0a4150b0041c019030501c4a001240640030401c8030000d021f00100550b13050990114950783e44001e20300c8a00518010394a1503228800009800da0584405a01104407076101c0d103104107500345c1d1402d078040d240c000d910444020489420010f11441001d52206240c01e114040c4100f561010301d400200321058081c002c40541c0d9910284415440d0556036600200320459140c20301c41d08110110b41c458085102d41c106140419022a41183c01800d000700084174014104900d8501510000d5444200040300710114443c40000c018080910046441410841001c01000e41c01241c0c0f141a008402006407038404500c5800f00720b02d4100c00090005500603a002055403c025080010016 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 957410350 1250 957409100 957409121
    0xc0a0e03060c18191d09010c0f03200a050405090114030a03140c0102070b04060b010c0c0b070302070b03011509080a020a030b0604090c090e150f0408030718080709 72
    0x244140104000c6054000448851810441104143c40c072900003041d020324240d4448500140010404105561040209a00b41c485200381800075155551501d00300e40c0880060b00c00500410303060400c00d806034004000d0700308800c0801119160316241c42c00160800c1488100040c0d0000c0d0030051454401091405800d103030702014140340718180081c0d5a04545c5c5801000c3c4481403075000844007030780003a1650394014900a55561106190007150440201c40480d200751138182e80e00340300c2d445441e00d10707802c2e0341c024190468107042101c1d000b501c3e006140c08900318800c1d418003041c0c207034807100990700802d0108100e1a6500d011180a44803000b01c2e0840031250317000f0845000580e481f208080e04507a04018a160380740c4401020401510118601500c02010880c0000c0c2d01c00c1c17141d100404411454080c1c81c103a03059090010010070083d0789161f507540e024004100803606c484015904000e441c1001c030000110320700007100300c10030750b0b11007845900000703020007824049001e50709014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 957411600 1250 957410350 957410353
    0x1009060e07140d1b080a0c090f14041416030b040309170c0f0103020d140615120103020603070c020a0b070204111204110310110c010e0d0203190c02090c0a0e03 70
    0x50140901050321040c0403000609038080490341103020600d183c007104c1c00382914000f5607624050604111049110b03500c100382c0b003145003145d415540700d020301c81e40ba040f0594102c0000c298485841b550540c042030001c5540c1da00408110390800007900d4100402540f00c2c8404000924160801074418506540319105400d181c00b1150003818009c1541ca649000494020140345052030040f03000f07002d4a62101261450412461040c800e52103046106200c00c8402c0c0c09100180c1603040810300410702039580c8a024000140010b1800701c024503400304540ca03040713803a08111b40010b03c003200540c1c41100c16075400200042581003e0040102030b039007282055150104545200f80440001040603203080c8192038603101c035a409005d03440c1c10040710f007003d02207480e1601c1124595400134100340c0c115031801503506030300840400c03541548142a00a5820804140011b060440d2506070001c10440782e540d031030300182e0311880103902500540800c5900ca4400e114050800010700c48014801d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 957412850 1250 957411600 957411629
    0xe060f0603090a06151220310b030303041a070206060f010e031204330801061b081209060f0f1305210c060708040c120201021009060e07 60
    0x602c4001000807a05510010000766910403007009800e48603d50007510701c22010300504001d000e240129001c0040060351038045034094a800c0040c0407517500e40c560003200c600e20403041c0074101104414882007840c0000f040011502c000a0b0640d4803c071400c9030b40020801c00c0000f01c0c0403034810789510180307600041285041400000b01301140400113503040000c01d00d400c00050310103001403440706031303612865505c0d9522101d131000044038021828034070310b400f0a07141c2d980a90038403108803804d07160b07103848942e6400c041003151007481c1801440c09100280c0c1414000941100060540e01c8113912801e08509090310742504000014120f1000840024144140c215005d0746458103c0a0543c0d0404e0901c581c0c904203080006d1040021400355410305181520f004100c000c00722110600192500d65860b40b60545003520280c0380940100f80d266014042042031880c5984c80d580140103c0e413401860306141c0003940e01c650000c40d140e030f44034109034807507980400c07411000d4809550000e44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 957414100 1250 957412850 957412861
    0x15120204030c09050c1b0d17040c290a0f03050c090102071e030512120708010b1903060e0a09060501050411070609170403082101060c0b040303060f0e060f0603 70
    0x1604200d010f031250503650750020994224196044030001c092140320101c2c40312145030f00301d80780c91a6065503004180042c400407880d010340303542c19224aa000d41152103850900103056203024040ca40c1580c00001c8094082c81c1262178805000c1c00405540c42c0105214045070080640c0c0b40501030000b04e0384e090240d0a6142c1c4c0100e541c1c806d841c4103203a040404052003c1040c207a400540c006010750141c0080f200c0702c20006401030100c08038540c1d1400250f162200121410303403003446484000c920a1250b107082d0802c08a00f880480391b145800300c0c80d5912070b4440f404840c801c3e078041c620f082e41d03078400b282081b0340c5000d07040c010001250100845518215800c01e18460701800414095845021900300040700c420052144c2440e4031480d150f035228508070724182c2c0540d81a05c51001e8130a412001e2151110045c0e059803459500c11606102540d6106060a07001e0800c40c1415111040810b0a01d4103004650080007034030031032007082c2051001c2c440c80040143d00302c1d0150500300200700 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 957415350 1250 957414100 957414113
    0x90312090916090513060e06060306100c0c17010b030106061e180906060503040302070e01120209070905031006030c05301f0507030e0d08150d08041512020403 70
    0x103510600b000610388005140b4102114022003640005a00007100054803855000c550700203015540c102c003c0700c585403244c42c20480c1c10b00080b07411951200d07000032403204032407043c018165003921440103125269140c6407402e00c25a14090100d11903990340c850304085103400d0040c07000030805400d0481c10b4440326102c02c8070650159a999041c80b010a801c80d20408505201da0b004042008040162603219000204168015141680144200000403640005400c2c0103812250b4011123200340c015113609102d1542e41c01890201400319151001030251418002c90181c1e10510000148290035441c04000b658050307049130380100020b1038508024050400190388841c5400000ca50319082404131a04d0214407000b041e8022140380c1d0202000300c103942000303020381401d880604c40d000e6001c2c00641e8850001c0c0d03481002030340d45404501050441000c0ca5441310002c2d10141c0903e21036103403180380741d000b1791044001b0340305a144103c030b41e41d0103582c0c107554450300c00c41503280501e9070b19100b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 957416600 1250 957415350 957415369
    0x9070801060e010c0c1701050414030c03070f02060c01060e01170f0613151112060906030d03020c0a1b14010c0521071506180e1506220209031209 64
    0x45062242c0300f00001300744000c0f40c1c942c0c4020660156240c0310103000c50074840c044d080686081303800c4840c0301c15500000c803010040d00c2410081000950038421261030b15100701950100030f0780c01000c104841d5031003040070300812001c3c00c29512185100d52510741055541030010b04001c01c10b40000c0020301c2200400300d03009801101c1c00400110f1480d10b8244403080b4802101c040481904e042b04041c1c1080000d0094400e9111841904d81590784a60612001d40c80459000b64036410120710318900700c0c040c1d406001c00300400412240c1d80301990351810740f45c18007100c413000700e010170120070454991041c5c0c035035003c280203180081544100c0c3c2e40d1107aaa00060649100008064001e101c89041c410140c03107280c0d0b003103074180700315146c0c0000d4480280f080b4016a0030f55090403403680c94210440c069802046c1205004103801d001c4c0c01010041c0d100054826607100940300810101c1404410344007444251401005903503120800400d403038180c150081425070001807240c42540d91303641d40308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 957417850 1250 957416600 957416627
    0x2041805060907062f100603110103020a05090d1b08060a0c0e0a06030207111c02040506030718051308031f120c0b030a0b12030d0f0b0d03050d14150907080106 70
    0x25007124a155170038200c0e000c1c0d8001c0040d05c602c801c1c0e006007100a400138402c076402480105008031100d40114107030711034514603901185080202141c09d00303121907000a0309005001c2c02180104600983c3c500403c2c0754030081c82076004400340480303c4518410703a02c1000040c18000c83d0395001d131021801103d210300c1003400340355000c0303801002d00c00000c4884180c42401031000c6042107034000c0616210300b140c10140e000f14a000300150540c18001000c0c01a5131031140841e18600071050300c0c4000e404010000c040120350b648190b400520f103100694040d4a10342e803100201c2e0030b149400e07040309515500039041201440100c4c804180209c00000c260b40c41c80d80750310f58035a99100d100300034082d0340380c06030742084d50103c0d001b81c44c89c004409040c400c40e10721800c2c4000c0f800d01c543c01c1c09a5403841402070f40300059080000009015000525144840820205010b0403007118003a0b5030700116460003040880a400078075600c3c09034001a4000b0043c24140d0240d41460b000a200300e50b0044d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 957419100 1250 957417850 957417887
    0x50601020c01120209030a12081b0906090d0f0c1a16060f24061b02030d03050405070e0406020a0f081501030515040515150a14090d0204180506090706 66
    0xc1a40c01203003e03030110346415402500300c400b15500e031300d855009103210440e501c000540035000f0440f580462501c18440110702c600444c2000c10110420030240d101c0100503070720090002c8444001900c0314400a500c501035204002d180d80303805400003c00314100028003a01004110121400340c0800310741c1a0315400000c00205000c0c41c0c4403040061401c541c2c03546c0911042c02d005441e10460f15203000c15121550349100920a685108102d0180100c400a51540286400d010f04922950142d80d02c64020002c407081e0682c0c81c82c0d540740c8058143c5003035400c1e54001461034a9503803c00d101441001544c58102000d11b42110100f2101210107449810983c403140403548442d031000d1001a5041e009004101900f00407014845c81da8102601901521403050301c81000c165800640e80c0c214281e0f01c401001451040700f08055a10183c10241e01840c03403541c1c440961154410700e140c08255245007800c10009081c51440c03c0d500034180c0403240e0103490140400366221500c2c1d00305007507145 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 957420350 1250 957419100 957419117
    0x5101b020d0209090d180b040510030615020d17010302130510151d06030708010e10030c08030d1406150708090d120e0102030307350702010204061101050601020c01 72
    0x10001d108100348140c0690b1082010043c40450140801c500c2d051950741c2c1c85070300c80060412000080d0505e1071082502d068410703c01009136081c48011080c0c080031a01c0d0000f00c41c0e843d00082d150160040446100690189450009041e0070010900c01c01640e41d0038000607600d50703800203d100d407070350b25542180d42c0c0f2140480c0da45281010302002030071105081150740e03112000018038201a22010100381c2c0c46030200b000d260b0602c281201d002d2660b075500c07021a41c0c2006e020511103007000d001107010818200e40000400c1c5d55030060302c040c10312180590f03682d138034081ca102c0c10b8170451b13640100b8540b400d6003070141d0f41e625104400755000014504075107440341d905110543d40162411560040303060114a001c004600e1160341d00e50b082912501200c0e5040c0004903501d0000302c0d640f10200e00c0504011406500794211400030f18104004030750744032200c40c0f10b201e03514400e440784000760390081000d004464120441c1d0800001400003000107203040d8000030f59503840f04803850706001407403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 957421600 1250 957420350 957420353
    0xc13060c060b091e0609060904020907020a02030d120b011418030a3c050309010c0f0f060608010b0114090103020a0c050303150915030604151e1505101b 67
    0x81d0030071a40d0040082c0301c11504e01d0241136840d201e564564140404c4515030001410364540b0941c41c0e4052400582003246030762300c690034420a414090300070740c00e42c4114078100c00107035400c1007070600c40e0102d55946400c00300d03041c4020095600c4481c10368140310102c0a82c410100b0041c040d1002a0100300c5038410203952039012a0608550380da0140078000d0b10501c0d0341010311210140504030151220f4135180e030307011540b500201c46141c0c400a060b07400811078503d9562040300ca211400e4040d0001c1d40c000070280d0340c1d24400d070480744000c44040da2641002c00144000384504e8940c08401c1c01c02d1055000e00d03098115040c8076000d40b244c181a40402c08440440c861002d201c140c030791241c01c03281d80f03043c900607104540c03242c000d07283c0c42549810009002c00805840b44c42800d00080c0c024000c0351203035540c0c80c6400754054854403450b0b540b40043c0a030118055814462044404030005125644440b00c08141c001ca81041c1d005407000e0300b1140175070f86c4c8082c050507040020101009045041d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 957422850 1250 957421600 957421613
    0x20a06020d110c0708060702060c0d090309050d06061a0903120318070902070605150d12030209030d09290406180308030c090f09100e0405030c0d0f03050c13060c 71
    0x2d220324081c20a001249900503c100022500c099804080c12120160b07100103049a580030100c420816a50b01840002c44a0710940c1013440224030074100403020b1901c2c1c5011500e100395444003a203a490b1581420404840c44001502c481540b1f07604040c50a02c42c140030984d1106009039224100300000001000c0312009448002d0011054042d610643c0da20340d6038401031b4101a200342e80701864074010489058815030b0111060700d0140070904e9000e0180c0710500c80c50b12a200e4201855001c00c6464680d6800f070150003200c51664071482d95050401c1c0c1c10f4400142c0c8205101d042542142a12020200ca2010ba608894940c544200100124034010040380c3c02d56000421203840403042c082a0400c004c064110480c055480c4c2501082c0e4900b000070200c0190f0f0300c0000c000d104001070111035052000c10b0351260007441140d1401c51001e110f20700d8281c01d02e00020000e020400d001c441c0f9030781401029000010f80c00e00c981000310307010211103100b03c42d105080c00d0001519459041048 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 957424100 1250 957422850 957422861
    0x90910030b040b19090f0201030b04150b040603051f0e041509030e030c030a02010e1306050a030f1e0b0c03040f1202160503010e120c1219080702010903020a06020d 72
    0x52042007040349041500d0014014030003a207000311605222001c0c07070203856451141c503032801d4014003040b80408a940040d00101540b442c41c64000d916a00c03201008110011598000c04030710040759511403600200170103c52000d0580811810240088110405440100010355828101c441c91170340301c80c9011000c903803640b900d4044090030b100c01c54080c16000400110550300680039500030301c4d2004c0030192120b11010000740401c031003200035002c40c02d215040c03a20b00451603000180c020303212000290b078a80346500840d8401010100e800c200030394025004a450000b0701a00c042540503a0341100b9500003e0100702400303800b10011301481a80000c00f9074580d00180c0c06104441907000c0252900002c9080071303099090014001080d0405120302800c1d02c40700d401401450058040f4104070341d00100d4010210300c0b400581c0001d00c0c1c100801001007120503480000a2107007505c018000c814000e0a410039649444407940103c2d80110301c0342c3d4426400440140d17200343c0308419000409 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 957425350 1250 957424100 957424103
    0x711070e060a150908010e0c091e040605071202040b030601031103100e0601030b060c0106030c2c06010e1e010816080703050c0d1d120a051c090b0a0b190b09091003 72
    0x10b0170404544210400451120f055000c141c4111a440d580d91510058081c058001e20482e02822b50000c0d000c24003583c00540c00c0011441d1848076851080c4050041ea0411b0300301190110700001400b181c1e41c1c15118115005499101c5681545000c814803229a841c92184148070380c0c1300ea00081c440ea119a00004003080010107042d228002c00078494000c4c03220303020031940d06081c180d000c2529107080081c910034492031a82140c55114036400a62403400260010b070501c111713640ba451155980010044c1c140781040d42c440c0b22048128001882d01c0b030050304ea0600b944c3e0b100208581d0036402043e0550240c8079045c0412240c54000000e40c7c13511400508103401454107508601c54030402c6206c0c0c0c0c840c075402c2d08036500301d00340311100d1129104000034500895070810409100c03082e003120940075407940c40e500003070443c4141ca400041443c111080380f100c0b90f90311100d8441d49042840030802601c075001e05101c05081c841468160700c15214174034031070090a000144290206065080070310b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 957426600 1250 957425350 957425353
    0x30316031407060c09060e0319140d11120f04060c020a09020d0204050f19170a0c0603020403060c021501170307050f15070f0503010e041a0711070e060a150908 70
    0x442e818100300d40201803c4203a0310000302e5900c40042c0d03e038840e810603018850b00501a0100d009481c0182241c0f031030140302101c0f605800a0201c11000080c00801d007002803c4d21554958480c0807009402d014032031016002c0d43d40b00348405003581d00b6040980f4103640f050b04150340300d1b841d40c3c00002d249050700e6001c10100c50001542c8102d847e441e4000d0012140c060703804100c5000340008210042d03960204505a940030018100300181408208815405803841500c0180e46580c880019a0790143c0001012940014013001000201e00c41d0501c00b80341803015098881c81c5c4c8101848911042c480d5940300164503c1c1c8141a0f003081c802c4a8440d540702c8106d40d43c84e101c00c0640ca0301d41050b09407102c0c2040c03a410000714007a0003208140248011a501c0c1440d40e030800d00426034516029005803180940001240e0400224901c0140100900c2d1110410489000c41c2e2900d4650603820044602015205101c0a030710b17480d03080400c0d103105180c1d0f6908445502011504202c40c0d60158406 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 957427850 1250 957426600 957426607
    0x9050c070f03020c012003091c0c0e060a2306030702030d05010e0105090c12040f0311010504050c041d03040b0703031407030b10030c0509012016090501060c020303160314 75
    0x70140c001a001c960f0384e10a0302c40b03079910001014030a200761140c80300f80010f60000c0201107150320f006907a510120300d40a25864030f1400540b254201c42c51607820000c0462000414070000b4038090088400402c0c04462800209900000013054615245640ba000380300c0800441d49150090007030358151145080200170940e561128100c02c81001e1045601401152000c00d05019002c03040b2a02203060720309040311074513103554103400c400b11082c095040080d00d5025500040e020f0260324001c0f0b0084009126220003202000125070215100103c4542d100c1d41020011401109550845040384101d03900d4420390305041e0b014020b65600180140c0c3c405041051543d0160b214071800482514085108100d4660a030100d9002c00e11901c08038005200e400041c0d03200c0e074000e0b03010385000f01c21840d0407161b2500e540e1420701107000a1509021114050215011500c901c500415191804945031011500402d44900c540311080c8101d00140e90002e040c140200740e4044007403a62681d4555 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 957429100 1250 957427850 957427853
    0x1b07091b051b0309150d0608032704110d0912020d0c020609040905010501150e04150b0d063b0c0307050a170a0c030b010f05180a0e0a020901090f0f09050c070f 70
    0x4140d1710500b09401047d1074220081402c50001082d1242c59904000f200d01d041950107081e05004903000510754015200c9241a031100301410141c06800081040465420014980586000541c000c0c000031944036060035941030b030703102030b40c90181c54060380c200356291010004140644001c21000e0000e609003c000121141a48062030700c0c07132285e0f82c42c0400c15403c0e004202c00c0e541d02c441148540401104180608803041004116459560800040a9507114000030a14111000c903660b80700710f20462682e041381c01c0554451314a032842816040d80780500c5001c03401d0201404c482d08010020032200c3e41c490180300f5401c82d03110807051400b900c0c60040451000307004035280e0600081d081c480030781101d501032031203603e0f0004591101802d02901c039612030400c07000d0f019495400160708600250b60685900e401d8003d12541a015a40c1c01115001502d910048c0d40500000d0003075a004008140341c3c00b0301c010a40f2400c0c000450161514590300900d405941005801054000901c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 957430350 1250 957429100 957429139
    0xc0609050f0c01120204030b0621010501030506010f0b040503060406020c0f0f0a031412041401090f0c0e010b040e060d140f0d020607020c0d060b061b07091b051b0309 73
    0x5400b902640c0340c011403014244400309038050f0f4070008012114010201e082e618119100802201e409980f400304841c2c916909401d42d030b800c2e881a581500601c005000110704030711a10040d00c00d80071380528262030800805d41e1981c00070f1000c0d140030b82c04588400b041c0818450003043c41c01410840f5050303400400100e80358000d03400120040703400c031440da0080000d1081503c920f58520b2031080d10554407510355181e140921080c580c5955a130f010203000044007405541040382c010301d00542654103010855002c03c0d81078010710204042400100450054400c030076038031000940c1c2c4189840c1c4140713080486500740b018180158020074003200b81450b40010100401105942100d20907246c010342030740c079480310f111071680013800b26100c0340c040b0b074058100007065503000e001c03207241c0303070400010199100120300d10340d800750481c1204201e0605580504103044040c014000c61540288501070a10301c207048003030041d081440308001d040380d01172007071781c2c48200044c101080003030b130035145407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 957431600 1250 957430350 957430363
    0x330503070806010309050c0f2704020a05010207030203070b09030a061107020901210611130602150a110304020907030618090b0c03040203060c030a0b1e1309080a0c0609050f 76
    0x840001c0c9031400040c869880b81c002c01007219008000b411440001d1030070702c40b4a50f02c0080050700140342880142441701c02c40c504182001c130b803804000060031f040c03040108820040c2d01640c11940080d00600c096035001c180fa10407170700c10106882d0b45081c92004a814141c2c0214083e040ca407500c4203d00b401e891402c001c02505208599a0300541c0e25040004050540548211107013120002e103940001d560b980014031100400d2107450920362526000e50080c5269085000140c1102800840035464500c0c881d400c042494424003000114004203840c6010081c0080d104420a00200328420300951051001d400140140300d0140000145880940004d2004031040044440004e40071800310055a000300d42c020b01401058840350150019900050030100b1030a640d026020403644d10708642a14a80d51000e10b0342d242281c4804124506a51007451050f807810000c2c400300040a503822500c42e00424140038081d80c0c920b0804000400c1c0c1d08400411034800d130007100c2c1d505040001c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 957432850 1250 957431600 957431611
    0x3010f090b09090c040f0f0c0c1214090f0111010c110c0607020f040504020118091a2e0c021206060f0d0507060c08072f01030204030507330503 63
    0x9100c000e240c0700512281440468425686030403030b4840d2002482c1540040840516075400421003141d11440342d002ca8148075404400304224120210400100040054103141c1a0618406042d12001c000c215842030100940c0315516a0b00000d03910382c01910130b10300300d071502d800800000c1403401c03000c0c254880585510700305106075508510075241000031900c02660140c11505810502d4060002501000e08104d05000c054141c130140800c0f540d5114004205500022440300341042c4103046a41c2c4c820303400c9001301050402a4031315105c03071326220302030078020034405030741d5100980031030750800d108a000354040c882d101041c4e03950710001a0760740905800c69103010b080701042c3c100100c004818000501c550041030040200034010010144442d0046698900e80716580d960000e40d0090380c6e0440d818600003501d00501c00800d1108030b4144d03d000e00301146004c0c107507240c580d66134105209500109030003640f840d468840302481c0035440f0001201d01d88100010380009021a002150b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 957434100 1250 957432850 957432869
    0x10270c11071202130e01140910050703050f240a08102409090503091c050c010503060a090e010b03150702061003080a050d0902060a0905090c0a0f18050603010f 70
    0x710b01040c02c4080342d0225640141200350000340581c48201030094180120b109559462200a18000340080c1602c110304690290881c83e003200c070304004881380500b1a2f802c040c900010092840105110160000685c400c1100d11541035041c0390a04e102503040c00341c108504400000301034200089190054004801c10300ca5203000c510125051700381c1c0900500b2180440604020f01540b6034480c2807658050310541c0e00c0d241000d00801c21881d0101108079002204c0d42081c0103004d400d008003500700c442440d125141d400c1100025105008600a251009a8440400b000650250f00008000c0805030603900d00d0018042240f28074402201d400016000f000001100215410100010b4980c1f00701c40e1400c160420f5000c0f2804c3d0020950125460fa0b075880d0417001d80e0f6075038041e201131440d40d507501021901f4202400100603024003400354040090045045481c2c03c442c60310200100c514082c400200d404003d43c100c00d5003030b400f030303500800000004a6121a40c120b8801914125039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 957435350 1250 957434100 957434113
    0xf0818150c060f0912180a0b1209010b011e0315091401090c02030708030403120608030c01110c0615060f0d02040f14280302030708011d0610270c11 65
    0x22103880c144102d03400e041c642c2144441200f5642c203200680784c3d901382c101c1150172188212007c00c0c0440c8064002d0b01404001040486481c00c9025007a0b5101c040c0c2d400a019040401c00060149100c111640724160001c03e00c0b146268407c1d4840c0f10b001041e032094600e1240e41e01c1c1d56000030a081800d64490038882000440c64032068024805d000701c8a40c011882e289094442040c50b0300b01610450030440c1060150749203107054041c2e000079021900103503949448203198107084030316441c56110b10319028807a40f07080c44000300c2c400340c0c000154440c0401103400f5000040c41449008140c80103104046a00708207035031aa8090016a1026028008255154106e4400d1400181da41d56030090340c11244903085412107401107445298072414006080c1c03260b000904101298012541e66903450714240e041c220040703044025406064050111403c101d40303407039603090840c000e40c142c0c0780d00301a07150701101040c525100c170300740240c00400c1404a8148000c0032400040910010ba1040c3d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 957436600 1250 957435350 957435361
    0x40b04140a0c030507080c0403030f1413290d0f090f0c05030714030a060e070503030c03090405010b130b0901050d021218070f1e030606030503040e0f040f0818150c06 73
    0x1044618000c204403941d00c0d0800b072075554111125141c0142200400c200f33400340d1004c090003c8090141306806003050080390f4140540c0311170202c4490003001900581c0e010000c01042c0250855031500328502003c2a040c0d403594000000c0d02042c4401494600c80700000c00c1404180b00302081030f12412026901d50030b03034032813903511810b44011030301d40e140d0800c03494200001d526030310001a818008040d070781c0d4155210002800c50b0007196200c3e1b81508001452391042c84c040c4209800340c204c4001040c00e1011400c0c14001d0704825000b0b02c103200b04001401003143e8010829100b003800b54003000c0d942d50b0000740d00703000c58027001d07100e11910042d40e442e00c140348140401d0500c01c2d034980c8420040b485140c071080c0880184046105800f0009110700400840e00c50300500c1d000e54051750080d640c0c0c80c50000b108101e03d0008050803030798036000040c4000a030300c208500e1156604409400d80b111241280c0c000781400c0480110307881290300e44c00303019010100300038204c01115034060390080d9541 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 957437850 1250 957436600 957436607
    0x13110105072f0901090207032c19050a0b072906040b0d081201260c0f01050d060f06120204030506041407081218010c11040b04140a0c030507 62
    0x1040001800a030801c09404121031650528000000e100200042e840a0310004910500c9080e0024520180c000030000207040d08407220340107802c0318880031141841000b522000c85108203001c035104144514882d1101400102d640001d094005e22140c00142c0d5551540701942c08038104a8000306960340c21440c101044099502e0901154400700041d40d45004103c014000046010f0340a0190203081021030184c0c0054444803a07560b030b0041241d41480f40d924864464a440c0701c3c1e8125221409041034000030810350851041070720081601481c04005a40303d0060403c000d1b016841c00c100001c4080310b0404080403120301341c80700140095420030900036072060b030101410a600060100300000d650b421441d078100303141810b13509940e854044a40c2808240a40e00e2012400411703114000312281080300c0c0c8014003401d03c0c20140c0302659031080380e82c6070b00c1007080c401da030b64445c5082152210b030045062001c0c1d90010702030518002078100300500030071030f0358000a071404c000070b03030007601 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 957439100 1250 957437850 957437857
    0x221d06100804110102030d050406021b03030c071104090f0c030b010b0906040e0601140c07081c020c04090212070e040614100b03100330020105060a03020d02150313110105 75
    0x825500d41d003882d911515900c000c1c00c020403606045201c208516030301200359201340d40c003892003080056662040d2180c3c04080e00122200e5080a81080051201e0a20756004036092140c0c40090f01c0b04001d055030015008020004000e821000e68000040c1088002e0b0031791010303179200314880c3c0b00300d0340c80d100c2407580340c00780104c07458101c4800c02051209403aa5404554082c0d8145001c00344040800b00105240e04003011440d4140c0c0709040521072081c4c240300101c0141c400c650380c0b000e1108040e10096440c02462116070043c2d03a11840d2000350b407109400c2d036000c0d0103207d0407950425665410002d0400c01220706443ea54580504400700c0360210100a014064240800b020542014241c45041e40090100c0025440741c00d0008002000000d40d40361801d10100048040722100703c8036802c03502040031100c02c6901d040304101d25503480300c1b07040050f43e4040d11139552098491000c0307100c03c41c00600080d62004040100080081711004c100c03881c91090050482d5072a920700156002d01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 957440350 1250 957439100 957439129
    0x314010b09010c05030706020f0a02072c1320031c080712091205120f04020a1205070b0d0c09060f02100f18060203100f0e010b221d06 59
    0x408001001d00340d03101d102d8000402d03014030140c0785060520350390801280d010700543c00c40903501003810040d0030740502c0060010030b0004440028001000c04034150300d040d11100c60154080f2402240e030b0102c020000c410f807540c0c0300d209034914200001180301d000204102c1d0078403d1050301c0311862101c020070855655240740e0b17100c180f032a80359008192012803e04140100300c41e40c403030040f00070074480640c468030703d8842c0d01c50304da4910031034100011040000f4880ca6810901006000042e2100d4405804440c1c9039464900740c03000d81d15040c1e0400f00b0300d078400c81020b5008183c0b403a03c00401e41c4218000c0e0203d46500400325903c00096800d071000e01030301c40c05a0442c22060301c16008a0f00080c180d00c064801c0041c00800c0444901500030825000361b408503170110400031206003030034004001e002072180314100c0503d0a04480c0c10303100d05014100701d41e800802c001c1d8400300c820a411a404c2d40760815109084d444007407409408c42d0081401c0502240040400c00505080d8818003841 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 957441600 1250 957440350 957440369
    0x90f080708030a051b030a050306092208030601170916080d050d0507050f030907090e0714062505030702090a0c050a2003040e01140405220f0b09030a031401 69
    0x150460140d6090f0001c4440c091400e00c060844140c5c1007080c0018080130006403544c07920380c1080c00500580c20710003002c6002c0d205000542907440200003542d4031305240c1c00851075599540700741c0100d56025100201c04107812040e0b0500c12008070100d805102d003200b030000241880e13030762002180c1d03d080ba10600004030b0420011170081c0754040c0c0006034424581e0800314500312202d0307220380050b8001c0f61100580c0d000b4900900c0486024025000c00d41c801c00020a4903e060500150343d50703036a200d9141c41090700203420101c510001c1c103c1200407607009003418400c0e845040c216185d9000800482c440c028100020303003600020300c00c0d0901303004540e80300d03802c1082228040d2031101001c41040030b500500ea21703101c26684201b001300003a10303040150407201d514091030074207013817082016244034038102000c1040c013003203568000030a040e4001c6207144544a9003060105800307003240103054a0552400c00c83c0743c550020080161300c6840d6001c02c107140f988852142d5048085c01548861b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 957442850 1250 957441600 957441607
    0x61303030b060405130c09080d0905090411030a050d0e030d0f050309102423060f0d060e070f030506091b0c010612170403081c09020d03090f08070803 66
    0x46442540004030409018040e20b143c075456800140d040107808081c41e41c0c05031107603016111103600446d142c3c018403219000702202124214064949461401514080c40441001800340003c150116a98140140a6400b0b504090800a0701d0722154424607010900c200306505883c1000190076500c45002c0e651a0212060300500329109d0b4000740a500f0700e4840c02c140138064440302e100d00034001f040301401ca210a040c2100b0103201d10560350020388128114000e00034500708000311103001d03080445a140d0388205100054226004d80d1041c06155440c0810100714418a210201d0145401da19000043e041e0000200c00b581c03011200540c1000c90b50f40401c0c0c1840107218000601540302c001e541c104010138202c2400c4800e0360748152886030444511006000108a251001d4070300c1c800c2c0075161600315141d0160780c4c41607402440c09401034240745a20081642d012700c3c0300e0b0341e0041982d0801a1181401080240103000b50b8105091441d40040c0006001512030b0440e0891000b8604 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 957444100 1250 957442850 957442853
    0xf1106040204180203060f07090611280c06020304062a14032206140a020628020a090801110c1009170406020102030702150712111312020906030613 65
    0x81c046050083d41c40810b02d0300d00d140103039000d015480c8540141595840305281805000b00016841d40c032943c1030001d451001d4040c40c1012850680f0314007400e507191140c144007569900c40010150700a40b01c1c02214102040e00760303010004004850161342e4000300c070038110b100711111502c8c02c0f949024008500c04800300142c1450181004408010203482c1000b181c2d400c04420300110b9440846a1000c4610502c0070f10f400402905000500100060814100d00006540c03240060418910b0160500e1001031310b4944035105070f82c01003840d1095489100d0210040c11006080c0201c851039420007907240c20000044041d958412540c10003000f062049510f40d40c01000c0c90f50042e0f810617080d040c864040c1a080740140001d100c581d000594038035100d0f9000341400000d5100c1c040e03442c1d00750180700d00340c4c0e030043c40e0b42071242000703000007010752888817821145d2181a1216080011f03120340020302c6a25000d46154260080d2001c41441d0703603840405842d12400c980100300449070081000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 957445350 1250 957444100 957444109
    0x705091806060618090c130f05101707080402130c0309120f141e0307021e0606010e09070e0a12110d0317070509090c04030615080d1209170304030f11060402 69
    0x1504010a00003481c031f810310080002c1b016107400c0c0c204000e003003560b80301008181400f040c68013050700c1600d40122580341030f0039601451a005081502001071810119066640c0c2150581c03004c0e034000c408002140c3d4001024014000542d070940703c643c07581c1050700c41c050084803200b1a440c80c6682e04107010f0320100250400380c0101050303101d50310b41d03490125510703640a00218014034241d00102160700003a0510004002e00d003146503205d80181d01400280d036044050300c841c800003256241c050340c1e24003004035000c40540003882c2d444440114000b8800d1241148141854043c1440300020194442400390390105003500070000340d80428459041410000116000261441c009141c64442d030002160004e041c0c030100007040d000981013042115512882850030243c1500a00700b500c0c1100d8141c9510011503210248040394110498645031079002540044d80000c840103e000e003040b0b44a083c1d00111411004110040c403c0346290303014444070034094500c640108459a150703820301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 957446600 1250 957445350 957445369
    0x2070902250602091504030804150c060c0809010609020414061b010c2a0b240603100603050106023007080c0a02130b03030316020705091806060618 65
    0x41d001c084124401c80ca00304501100c241410340950380c00340c2c03030f0b03440d010821881e00500c07400103000b40c0082004000064620701980c0c210b90030380c1d4000c43c1d0703042d0a45055540103c0c0303003001000c007858840e82162883d0008280c0b8010790480b00200003040d240c8415508071f120703c0c0110912b1000101540c0e40c80c0c50220003c2c1a0741e07500601032000250340c0304c0600c0c2076035143c2c01c0d00300210715200c140c0300c081ca6000000506c1446603200810326040c40b42c03202c03941c0c400f019119503080c2010b00303007102111041804101c400440a01460b0780c0c0d05e01011340450701050380c00b41e100000e00389400014214030000326500d8404003444010611403401c90700c0f22241240c10b0010032010b00922014001c10782120180c0f02e48075400d00502a00040d500c1044640703c0c5c0c005080145500c2e08003440007584000007a2031303000c4030104454106c001400d8040c8d281c4105640050b500100d8001000b041c9814071b030b0b00344410350010080b42c0c41c0b80c4502c170400c5124050080d046101606030040f15443e80380a0ba04c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 957447850 1250 957446600 957446617
    0x12060a0f02090a031b08030a050726180f0d0305030603060906010f1203020709050c09030c010201051009050903121306060b03131113110915030912030c12130b0f0702070902 76
    0xf040156600c06d0554119040b040c0d000000c104049500346c00d00c0a088060070700302c0d090200b2204442e1655200118034003441c03441c880010351a544032081e9031070386d40b44002c012000138070440d4103a5031490010219441190440d0181c041c1101003070b010f90001402d541a030b212035900242c03880c1403403090b200481d4600303425001c5100c4e00c50001040704043c420b0078042d00d5058201a580c246201c2418500b5181204050440e1f15040401c000948410300301000c2e1130f003c40300400c0a4403040d00062441c01503100d001d00306400d19060044858400103800c414502c929800d0101c0d9540302c9440ca014007086600a801c4000e6680b2440010804c12036a44002c200400640c4810007035004030040350001004c50a51580008060710b051400041c08200e00101951480c610305c0c18100c516228407003d42049682200480800c041c905044c0a6030500c0140b510310510324a088601a100e810040760241c501d00d0728600800e200c01c1d031802c0c1c41031161015030000c0c01038074944610fa00007580070402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 957449100 1250 957447850 957447893
    0x200a0905030a0335010b040306051006140d090b01060305090f0f0309091806011710020702130c14070807060c080709171501080d031d06160e12060a0f02090a03 70
    0x11403024544104e02c22030b0107010101c20b00b13500c0718194900b943c2250310103402d64051442035202080490351150300100c019041008640e19428500d0010300070304400071004250459031000030a44a91603071141e481201d0182c211980103048600f600d44400083c440c0d0740003600100400d090900780140342d82d0700101950025580186400c0f8004d082c24000e8100c0740618400307c00100759000104100714501628000031440e04102da400541446411840d100e407058444074503004142c02051140d0207104506110303941d468032071601e40783e50f501c09002141c1491920a848544520072100d40e0711450071515103030f002d81d0910f003003840e503440ba03100c000a10380f1502c500c1501300480d60f28a07500a2420000414600c5a00180a4191141d140c82d2840200e03030711b50b030030303031001d03000518141c014010414580c84202c659004444104c0080704580d00100202c10340c1c51002d100207040e40c40317516140300801800d1b142c032400d41c080c0d21031042030aa02c20040308083c00881e5072311061504010103c0c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 957450350 1250 957449100 957449177
    0x12030606090d1505070906080f04080c0303090d1403041a04020301060819050d0206040c14130912031d2116140607030917090103200a0905030a03 64
    0x8100c800c8025046031008520a9602481c65070f80c000c10350061a603042442640d41012001407030004010070102070307204098046414018800100d4076081211029a9681e1504483c11503a80c0400300008001400960107040b1402c07400043e41e004e6644000041c031170311600b036003044880101034000d0381c0c1135507103040c0016911810094021000e04001c5022402265400e0a508042d010b0f80c0b00010344d0011410040000c0b6010300c08425141c6161380350902c1d00b01a0003007091000c0c1a032034240e2080c41d0181032420303c0450315218210548541c0e0134062900c03404408810307489200010200c070b0b8006900394104083d07110500c1c58602c00001054140071820008400d050b2100700250380c2c00c0d0746070341c00ca40e940300244011944080310b802c051040916a80d40e40381c1034418160004003800d00441d60380e491f07038840d8000092032120b2581c402581e00103940c5800d943c0d440000e000c40441c05810000425050100310b102c0701039019140c5640c0c02000d0326440c00d6100750710030040640301012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 957451600 1250 957450350 957450367
    0x5030c0c120d1509060303021c18060c050c0f03190f021c05060a090206030114120a030f030f1b0e061c0903031404200607061404030207060f0212030606 67
    0x40c000b82a0b035521181001c651001142000524400c194000c4413400f418044103001198002541994201102c66624500346801000302c54601904040c1c0c0c404551745800020a564800f4014120501034019100b00d10303010410060000200860aa0107402000440102c0e00d100c4a8235040305020311a00140d214841d400202c0081c0c02041e45a01c2042d052001c000b07005c410400150312001520341089003039165000205036002c1440f410b50121b803645050504c9440c3e815031400942c01e00781c200ca070390585a19000d00200c0115149100291071301a07108520720b0207000e240300004200d034140b00f6903140800111410291000c100381c00c0351003045441080d140d8591403001203200a14009046000b610340201036504105200b08081d00d040103100101d030700c4001d801e1842145045008000900001040c1c941c059041c014019920300a03042d103102c61a00c410911851280d8250740c222603c8200640e1040d420f007050000580c0900b40d10405001c00100464000c1d41c010211810322102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 957452850 1250 957451600 957451633
    0x6020d35010b130503210d0b030a0b0108010b0a0e01030602090609060a0909110304051b030c12010504020310060b03131104050a1e02030108100f061a0a0801140105030c0c 75
    0x82c0d008404220002506142d030301500081c0101402080300502105510307400088102408244100c12925000980b4501c1281950240b00480406419100d020b80c1d981401043c0c05030902c0340580550804443d01e01c02d01c1c20171303180403e49020700503d110990030740d03d0b40d000070740041c2c40480d0018402c02940300349076a00800f400c1d1034401c0781c0d038950340716003048000c02c2510891071030904150b1091043c80006900421348040140c0520044404065400e00083c80d02906201d125000b4505490b103449040d0190083c61089000350300311080008009501d008607241032140a58207081400071400c81002c071288800c419025502c40800b5260b40800101102c200741d6500140540c0c0e584641070210703011101d4000702d54429011819580340c000003e8540c6400074000040d03e03501c0009400074203040e03000d0000350490103079000c1d41029016034007069038841c1d40801c0115a2000000030101481011604c1c03000c2d060b50b9103070654a4102c4c0c00e0915411041180c02c0c5805518201c0d14001403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 957454100 1250 957452850 957452957
    0x601081216050106030f1b0b130303030b19080102071a06030c090c07080d050a0e1203161e02030306031522020102030c010e0c040b0d050607210e010506010906020d 72
    0xc1540007d8010244805404031041c0d0b030010152060a024803841400c6201c03d031412a40c040c2030204d503965003600014103407015030010501e80880b980001c40d9080e4154060440c80e44682c40c0c1041090001102c5210904103e40740c0341d040c0d01c44c60740105c15040c04024140c00400010b04182410301c41d50b80c405aa810800c80002600d80e0f84041160211160140c040c0101d400006412607103400e190000c0c0610005111a48210a00d884510725034070400549240240786130b443c01c07250481d03401c000d441e503000317403032091191065030b1000840b43e800300c200b40d000d5042030400c10000d818804140c41c90900409043c4d06500090005100e5100c0c280035004a207900140509400081c00c0c2c200002c850f100514107004a40480741103000810004a841c0c2240783e508002025000180c2140130b0301140180d507244103400e240802000440c150003c9001d05d400341c036001c58640d21110100e0f5100c0307040c41a20005402c01303040881200440c3e00c0b12140d110050010100c010100102511242 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 957455350 1250 957454100 957454103
    0x12031e050d05014502120106030501052b02063106020a030207141c0606030c1409070e010513030807120314010b09012a050601081216050106030f 64
    0x200005070042440d00684281400b6103102450f281c07000e06103074054050b203141040303051805a5210340300400007010110107540d40210f05400c0d5500e402016512800e1036084c850000481d00b440c00201f09440e05800c10284103e00900354002201d8002d9010031135104020260780041082042030105c0b8054224090220b01c035460640d80c07400342c16882460461154451021908541c800390000399006c80c910080f06d8540e00321260080024002903e41d070101c6d82c01585c641404401002001810b401a000f220300802166500a40c1c40203003600707585040622541c4030711841d0015189034026075510503052410324265050240d0780a10061240b50703508180c5400401007914010003c0d02c120000c01c0c0103443c0b9040c8a4050038103100b00440106001c3c405080c400801e00c4041030b440f940201c00050001b583e520554414088116042808010141d0301d42c000c0c0b600102d9800e90018501c240004e629450034580040d0440200c0601020f10080300c9954a6400010101d98580d40a40260b0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 957456600 1250 957455350 957455357
    0x302030c07020a08010506030f011802040b060408070f140d02090c03100314010f23010512010e060a0b01170c03060d1b0303111005040203061303030f0c0f020d0504050a12031e 77
    0x900700303101018278209107601078403026814041203a14280503070410207c00d95041c1c9000c41d040090303100040b1580142d800001c074502c01c560b00040c1400350051060225882c0d40d480c030107030080000c01d00a210490950294104180c00301080f80e5402075001107500100d17039403c9010031a140c2d41d41c4013102a010b0215200c80c2e44a004040508206104540c010031004840400891a41c1d890502c25901403003245d100754460401b14421810a40000d07002003141000e4070120300d0700d004000000d02d00c1c421514001502120b01280000102d55505d005900202d00c140c00c0d580d40c44100800f00b0141c01048414a000c550a25460400c00c4180c2010b14403d49600355440c0c0251100d0346491034140045408504200502c00941ca0220700e150f00980c1071444800a60000e04041e0007400c000c641c0724040c54641983c40c6103056000306000d21111503542662986901040c044130640218095a03a00040b1044100a4907045401c0006094800e0a116800e9003200f00f01000e43e222000111011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 957457850 1250 957456600 957456611
    0x31207081f031b05120607030902060706093009090509070807080105040204050f13060b0f0907080a2003151c0f0203070f1202121e030712030902060a0302030c07020a0801 75
    0x20f102c1d00450a0018240545441c80000c50660100da03480d00050660030615a07074229030000c5d5128602210001c036081320302400141020301e00381c0001c040d907480d07200003206a039404003900c0d41c0640485142d80c0c01c40c1d42d44025030f42043c410000034400035124403514814000f0001c2d0a0320b050000400901002e00001400d103030600611061b2403006100c1e044000b05031301003107030022004409030314440d0032070070000d4800304103004901030031a24604194000c3e038000800c81c2c0564003007905841201800010321461890360100003140b01400c8100005030070510001c1c1c0d42c19072000d126008000d004000600c080b0180740c00b04c80080300c05209842c0310340061821000e41c2000c2201d00001c0031303440c12580d81d1a14046010004541e4844020721a2400c1103000600b07800401507035610b85405040364282000410501d60b81c3e900c4080100d403544100c045c2000c1003402880750141954020b0015481e100c0c0c0c010017200294401803000c071120109101080140c2c07294036211000d408081b000058 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 957459100 1250 957457850 957457883
    0x91206010f090204031e060209121b0319030507020402071b09060e04031d0d0b130606090b09070f021c210b0a05130204030602070c05090108031207081f03 68
    0x30099242c01580714540100303c2040001c518214150000d011200340307200780400340c03800f08040d00c80c002d041c0b079005802819081010b0f201291180342401002c0980418103001c1040c07503110340c1c465050034000300c0138070301d41e0340032a0140008184451000340300604e171040543d642080c500d062500254482c1c0324480600540c0c01e28894403016269040c41ca00c0c0d00c0c50a0f0b038009021500c0140c110b4070304000c401650b5030645030940c611422aa208100c4501c40c07a14030054120b440c0c1c0c0b1301054400c03c0c245440041c2c000414807484c20900000313000c410385035541d140e00380c07800f00e130380180c5100f180700302c140710f04200001c070840084541103176680c0c0620301d415001c010042840d158988c04c8080c03401140c51540c0d40c0380087c071800c40d141078805001040c1c0c80ca030f01c0b800074040e40d80060107441c000107504040104851007a0b003513520455048e1a140d8070b0380102592070240d000055600c1380044042250f0b580180140c81d406086090030f01291030035000345a10101450380201ca0200030380b4070025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 957460350 1250 957459100 957459119
    0x40f0917070305130f031208090c30010b010905060415051c4101060e01020322050a0e0919240c120207050a080915030c0a030605010e2409120601 64
    0x2040c7e1440c52030840300364200003404070380301c0c9180e0444620400d00303801d20711600c2e040880302003104c0031981c4e1946416095600b110740681050250076002503040503011074580b402400380d03001d880f9080c020303900b50003c0d10710640d4980d000c0310b2100180d5004100c80060380b030140c00b5000c509816044400da1404c2103020516540300e140f108c0c0c540151100020035180100001d28904584240c60500d008000250050b41144900b03614460b010840c07001c08060f003006182d001e411103a043d64066031255580e964144040019107107150f00e60008068046a00b014210150086003d01c10310603085c0c841080514815011103622410b681c0c0302c00c1c044201075004403401c0c01d030100200e815031504400d6954903031140300380c034001403034024041401901516440b404121514008600980e2401e001d0a0340c0181d400224640d40002e003071100114007540f154100490740318001e88061019588006003282c4640d9204d00710240240500501e00d10340c0da404684100c0150103405484654181513841 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 957461600 1250 957460350 957460373
    0x605040e070905030d140c100e07050108130b0c040f180609061a07080f030103150c05070317060d0b0a06030506060d030c0b09030c0a0b06040f0917070305130f03 71
    0x220140000a0803c0240c0e0301c3c003140e42d2080c0d461601e85118014a00c01101c00203014803002c04995104480b03207007582c20516489611044a44000c45040369900c00045410b06400c6580d035402a0100c40e41000240c0307155492030300319103405203103410642c5407485915200c096501c0b40ea44201c02100320811130b0103610542c00139001d480710501a050600c0c4032024013000c0c0d801c41c40c8004000184d40400e00c13403482d081e10075450b0542000c50380c81d6034a050840d044c0c0303c0000510301081c076000300c0c21004d80c0240308031580315034903849035501550390180659840400820194200440c440c503d400240e11125061090034441400200c030350450501c02d10300140100200d024003015040b043c0441c7e080020980340365844806c00035a40e4480000c4c50843c05200d51070f054a00c40c1c1c0031a6000c0000c1e8400c014820380090720104903c0100d841254240d0320010009402c0160821410126000400003803078294080e0402c245040401c403520507148030668801c07040440d2050b0b00340200000305164 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 957462850 1250 957461600 957461611
    0x91d061f020c10050903060702070609090507020601150e030a0b18070302031002090a030b0a020a031a0f1201020702062118191103030307030e0c0303040e0a09080f040605040e 77
    0x1542028403400c801a507901907042200744280e11801d8510034241c411002c5585d0303c03e0280a841e82c0382001d8038060760b100c166020341000316003055000702d00d032542881503600c14102d55000f800580d00c0c0c000100b8140782c48411507000c011105194401a840c100242c0b01c0c114803624501d041494191501404120300d074040d198141c020040400150f40c000680d124080810b000069490040d800000c0440415610013050002404200503801d069a0f000c3c2000c200309480031f0014400c4c400c07000d440c018020130713003e612135030007204880e41f42003079403050700801c1c0440c0005144c16001d40002e2800d408c05d8036098941000f101c03404130300d540e022b05150340000c11392040b03c88a00404100d80e460703003407107401c11884c0340009002d032080c070456075110651900083e081d40e41e80d040c1310300c0080c09000c1c559400304480c0b003040407003c05410004100d504580a000c0c26000f6501e40f903550801801c4050004c0d1000d18040c4900d03004000d44100400003004d813502c0782640c640c900380200308201c038010f20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 957464100 1250 957462850 957462889
    0x819080105011404080601030605100315050403020c01210906020d0218030111041a03070309210f0e03070b1305040c080f0f100b16080414090108030310060f091d06 72
    0x10400c40c82c0f1700081e4840c1580d9010b2004921503a0381900300302301c0002680040c10701d43c1c00c550032541c0340c5090381c021801030340030340d090340c403200d400d917005545035110101040e0540f44814010390502c01c40342e0140d1101d5124041c058502030b03126000c3c2046e07801c05255148000c51504030b5904610f401d21505141030342003500b43e030a19180c40e50b81c8258040039845a48070000c008000382c42d0b28030a51100c0ca003180e0010300f2f43d2100c0200c146030450010042103403408200e5142c4024242405800c401d0740031413005009080103070404000181a400001125a40780307505940404d00e6a51406401c54a40c0c003a50356649030315151011100b621070162440d04c1180a000500801102c40c5205d041a01e00440280ba038401410a8001c0100300601c03002d00f80441c080760104d00c1d060750450103c80d068003203810001a91b2039034001610717440140e440701078241d00d41d0b400b04241400380c00304a21400082c108414031640d81d0709000845907641100c0c00552080382c08201c01483c001c038549607000c00448 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 957465350 1250 957464100 957464107
    0x121d0c011101060b040b0c0102120124080121020409020607050105040c1a0406113a02030316030b060c0d1e02150705031b0c07031124030408190801050114 68
    0x110403400d00e105d1400703040d407486000105500d0490003501150b51401035806810742a6070348071998180d10800200030110712400f0103c800560744a84001810780781848010420048481c458210000e005881281c2050701c03241014096038824014155607400f94001241c0d5182614000000d5060b82d006a85400440c10804e00a040f0b840140e505a804038140044084440040c0500e401241e41a20210b031841d016005c02083e09180030000f00b40c288080000503101852040e0f0702e9010448542e41c000500700340c10270340345110350401f51021401419032890000c03a00e400134140410750241c14041206454106525007914440d07404038202031018060100380203800210059000c0c0401081102c00310100342c6144124010b02c0c1d180c3da6a8840700d580d5155100d41d503031501814401a5046401c91142c051141802c11100b0b8031415070304840d100750310800a0703501543d00701500c151600798013401b928000c0a8a00516403a2003c1c0c0c1d200c9030100d42c5400c1c001000d4400340d0071128455103091 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 957466600 1250 957465350 957465359
    0x3021303060914010c3609021801080a020a0e091003140105102c0709050d0f2d030c06090204020301262d122a010516121d0c01110106 59
    0x401000c46c24040180781c580441003c110450300001d0340e6040a1003640c40055010340000140304001c0d0340007020303264087da5a6926222208038002c1094410100354120b0a00c0e80c50b207894007001e6840401400760040098807901c1d16080301103010102c45450f950b542c14008503500000624008082c035880c1c1c2810b4a12941c940160084400c5c00035148900401c00310700700740d00946c021806490b003c0c1c076090000040781880328842606860a0f1821021046503d501d8403c40381c4140d40090400088408a5038030350301190407074616071066422540d24a00b0400580e52800118000c0480d210b00f1101d200d0f521060146174141100c409849500181d5840f60b00e00e000b0307490110900213082407080308850041c0701d9043c2003800649100d0001c0005440381080d241c200100b03121980d528080c50304950754002c0f98200c03401951700d200e00d51000407080382c6072480303034000c003440e800d201c0c0c03011461064015102821468411103003005400400090303100d96400160548c1044440300280b00c8280391 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 957467850 1250 957466600 957466637
    0xb151b010b0f010f08040203011b020d080c0f0f160218071205090d1b020a061e0c021e011106010807060e1c1b18230f01050103021303060914010c 64
    0x2c003c0e00400703014170400042c0556400390300c21146140c1c011020fa95405204100940301c7c100340c0c0720040442c220303201292075008603200b0b503100c00b0500880c00b890f18440b1052001190042030f018280c52005032140742c011380385d05a14040c072840882c800c4084d030400482c0940000cc06880010100f45003904215072544002031108a0805c0c43c11301004202e141c504c00040c0325412240650084000800041c41c6507114001408424400d1101605400101d2084800b0301d140318010b94011046100c100c2600c070a1011000c00040504160816501342c3c5859030604c0d00c240e004041039004508100312864004d110b809004404441180480d45c01e41c441e1380030804020406402c58120340c50300ca425010b40c103100005000420038a042e00035840310000040c001400c090400305814180070381086074921002401103c44854201e403a0f800d00707004400940101c25004d004848034030000020840521034102c0c1b041c02034603000003030041403984500350342142620b803041001c0c408030b2100300400e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 957469100 1250 957467850 957467867
    0x5120f070b0d050915040219030206030414060f010b04030312021c0b040c03060f090b060909101406070506190b10031d06071b03030f050115020708160303030b151b010b0f01 76
    0x40c100c0b41e145501c0c072600044611f82c048c9400007508608004144428480040b0068498240035004c032595540c401c2d25040305964280b05071103079007000784000c0c00028001c12140d8420100541c0040c144440c44204c043c050107418010381c03900e42d9070244c454107030901c0d000300c403001c2080707090500c442480e0011001112895110f40d03940181e80783c140104607500c04040300c4c00b0400c001e00c43c504c542450303602c801d01098148100da050400a001060560905205603130f130040d000070188c040c40c4d540c002240e80c1d5192142005103020f1b03490076680003990340c041423030069000b10756000a00543c03522950000d69a400c08200595203ca4204060030f5880b581145a032215010320002011007807030241d02521030f0340c800c840d0040c185400400c4000051801d04e603405055030886224a41d540d05258079030201d02c1411070501100601407011038000d4101300403650020303050644d10b40c00140c0c06103560304030b407141601416181060340d1020400740114103001e0000c40b0b00c103501b08051000030380010b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 957470350 1250 957469100 957469103
    0x1502090612060d210219020a03031b0503030a0e070909080702060f0922180b18030705151e0603102d020306121605120f070b0d05091504 60
    0x1100c40008210341c8607a03403c0004594011503940301000200441c3e24410850041280140b0800450b4400d0205c40818074244580181071800320f00d08540b421142448040301065145560050580024004200a500c15041d40c0c00000b980002c2c00481030a00c91258080c2c001141030000240108141c1b10032a0300c000d034101e800c0c66440c01f50404600c1d1900074048080e0b400103510441d00c1040e851a01c19130700001800c80d081016040c902003000d009960901d0181015000d080001c0084514441c0711000000c175400312400c02601d40c1c1e550307142040f203600d081c144070348980900040c5071400d20380750000c00b010742901c01c00317140450100e903464412040720100342c1c1e180e020400308041c1d107902c2440b0218100d02000a6074a0f4044840065402683c505005140d40403020380360301c60105010a0b00224160790410b030514000c20040c42d2594511071404900405060f082019010045200100905035107103441d004100d6405088030f0300241107503000d8002c2c00c080c21800c0d40342564141d00c079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 957471600 1250 957470350 957470377
    0x909023603070e102d06050418140601110118110a05030f100908040305010c020105041502040503030f071e050606030709110d1509020703050910030603031d01020a15050415020906 79
    0x801000004031020308824200008508882c1e030f01081c0198410300620a43d000c01d05502c0270403080c40c08400840d001e4030086520003a0b0000400c21540c402c07480034080000b6000045460803000c404006400c1400000304c5000e1032207a5049014108094400002c02080300071307003208a00040802e403254a00b4038400c8015a860318280200100c1a054502458101d0001c000c280e0500b000a0300810f0103850a07100c40014111005551905008507000c0e110003401031420f04c5058140451641c1001200721014862039186501c240e010303208641c2e450b80150002c0205007406802d0600b041503030380101c0b00080c1441c20600710805940101e07041040305640024403841580d1402c04501921f4021081c0703035000103403000070315070712801401c51140201c500d6102d9540440c01902140c42610000380829843ca224101050100e43c1d000c0d011134040c0103440d990b00c505c5d039490407080f40001219844a96078020311051140415014410440442e811441c003110b10b4001352440c02580c0d9012000b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 957472850 1250 957471600 957471629
    0x403170a09140105130e09011a0f010305060a12050a1104050f0112170c0708010b1f2d0f030e1f0c120c051c020a0909023603070e10 58
    0x201e03407050b41194209201c3c0204024501d440314803801b4100001d0b81d25450b290f00b080100c400303403880c0d1444480c580000812200f559400040190701818009100d60380c4211306d428001021646402c440890328403881c0038203801c80c500d03d4088119034541c40c1c40d50050349003104110941d507000c80401d040d01d0b14107070002920380d21450300e84454607152943da88004004210b8805405c0e0000d814000d07965180d00030b0040c82400301c24000344188005141c801c528a0702400b00180d0f008080b5031071441900c8400480c120890786029101c1200c0e2082c03200002c0741455264841949440b9403070821400310040d10840000c0380c4203154400d81d1880c0055031380d03503641e000c0002c680501c5820700152500d880500400d0030140c2c000d070080d006440d06100d40b02c881d035032925505005200321602140c80b925906c0c460390412102c80000e4120029000c4070b19034143c450048030384140600c01020400f248990800f50545003031500300816507109000c0d005012050245520440c50039406584071140c10130300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 957474100 1250 957472850 957472889
    0x1407050c0f010903081603091509170408151806011512060e0a05090d05070813030b040b01031202071d0703090803010609081b0d020909030f040b0403170a09 69
    0x8200c190303641c000480d8070300f0055a0030103421030107044c45407455440d0216000a84082a0103640405034001c010130140d1f00c0c04401c1c0c2007039900c0b2401080c010b940107442503c2c1100ca0420f6544160801c6140b980541d404041248001059507400b00012209501d1050f40d040d150f9982c10060040210004032442d41d245034521511041e000d60754124800d012440c0e0340c0c03015007010784090b18110a210b05140c001a411180080e1180a03042e06941340c92a01e402620790725816000076080300c400104014002000c1011400c190340580e0044016030030b107524500d000d0401600c40c504500130341d0070501c002c0044801f070301101c24821b041000780340c205940702c02c801c400500b0529401054090301000200703410b94418600300035a00c001c41266030b4400300503008e20b40304001c06280e640c000301c521190070050800b10f0081e60841d03a000c003202d00745260a00c1304895a0001e41100c9003000d4045010811b02c540c0550031420050345164081ca40140b003d8000d040220502558034804d64181c05400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 957475350 1250 957474100 957474103
    0x515010c1520030402041109011403040f060518010b030127050f0d02061504140a02071103060c120a050c03040f0c050409060515030c0307060e04020c070608060102101407050c 77
    0x200b071070002615103100440c041c000c8096070f800682d01640038078038000507040095000c604070748920740161610804003100c0000d4040a83c4028000c0310031a06540032140041d0041c02114080c03503400b5070a138104426610010308482c030f1541003038842d0381401240240c0000b140045600340741514800b205603481801d1403854086c0c26103665215104102421070560303408039800d401507111042004101c81050104010f5500c030310001c101080d5940041051000345600400340307184a1158000b148040350b0002c2c0c10710038100c5690780c030368000090040405c031135240402da102908a000704494200f100081c120303400010701c0100110250b0141c0014004500480360041000070810301101d038040c605000500b2003520b502000d1410030350307451000e00e030100e00d5035a401c40c0600201092403a04008171440f800707407810650425420040101240c10500400c0f004d0022503c600d0031a00306240024640840e076030320101140e02d021981c03504010024102d03a041011450401e07150598480d80d075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 957476600 1250 957475350 957475361
    0x420040515120c0d0b0f0a0603020303031504152d120f0302030408030304030c0c0503010509100b01031e020705060601050a020a03050901092706090903090312020f1605040515010c15 80
    0x60364009101d120a80030001c5102030184981612004c0b04140e0b141c20b00351000351402381c04000e5144c1c00c10300004000c0703c5e5a0001e401400c50013440820b114001c0790540c219001e098000c01c0a82c6404004001101002000000d0030351443c48030300c0301c8510741160108822110480107018603581103244084c107200f00141c5004d0941d040903130340d490809280250070782c1d20384442107425040c0d80000048500c0c4c1881a188544520310181a2003000d8210702e5000b00740d10001c079414199a6021090f0306401044203000683e80f00b030380166143e0302030415502d4404020000ba04100d400c102e0384600550204e140c0d44c90703a0340341c01c0894440c2c0300c10006a8001c24036410148540c101c9600c006000c03111003018041003442954100b10740c0b80c6640f120300c241e52100f0300180110304091f03002c10000d560a00610059110b030304c180c8654112503119039061051507824404609450031003400f80346000c0c403845402058a20400014081e4840041c0961140e030401800200b5000100035a00001741c204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 957477850 1250 957476600 957476623
    0x50d11120912061f0504050c071103100c020a0b013c15170106030b2b02090c03090606030601030317060a0302061308070504020c150717042004051512 66
    0x54441c18544480c0b0a50b80030185020785004c000480d00004090400b880f409000e09081080146400c015446000b580000d038a00c02e9094410502c00c0003000f52944202031880340c1c56406000300180030304200700041010b070000b00b104070160726001c00000c5840080f0090b0140c400311001c1650861311800d28820b131561240844040c07072a6030341c080f103034802c84001445200c0c11f01803000342d803988011000c40c0c613680040f68015400c3c14503200301a044555021421030b04410361006800d55902180c10018140c840c8a600f2101000f0b00070000710520410f5840390b020390040040750314540300240174602c000c03a00320101c0901008181103890340c00d81e00c07000d5500588210341d0703070f030507445407405a203000d00c10740c050340c003a9650100312884d0034022100030700d01c13030001040054494080320540f0b24015204109200900c1c03050400302144d84400b40c81540203101d540c500043c02200d02d98245d0310550000d00c6103250004000b4082c0b4515101c102d103a106441e82d21141c081b582c841483c02c0300b036602 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 957479100 1250 957477850 957477853
    0x306030312100f0b09090f190b040605040212040b09060f0402270907080f010504020d0b0721020703090501030e0723120f0c0d0f0f0602040b0a0c050d11120912 70
    0xf0100e00004528000c0c0160350060314041003541d214220350440480a440403900d0400d00146036031588056006500488401080003510668881c0044c080360b01c000203a02070001c281c0c0c00c1106020050561590050500001e080f0303510341400c4140a10000600c0207100f84c15000000081d110504441401c0301c084400d14003081c00c0c511462641da500601c40d540191140d64001248010706004d070034007466000d820700751882c0c1c9550b20340314140c9001744503d0811040e141c138120908102407030701988101000340141d45644606006143e4000c03a04158107242c144210003403280c1c1c001030100c04403001140040f2509400038014014190054969944141c0005203403031100c001142011500c100d000c2101d945401003018004015202c0502500a011600c0f00c480450040600c1f4080786114400061a0540b508902c0312103402120781c020000301d07981e0421007008820403070400b22900e40c0c1800d40344103001d014480e40c3c0382c091010840003014041400c0c0303196120660b034039914000a20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 957480350 1250 957479100 957479129
    0x240d06030816060617030d0911030304331e0e03031b06071407030e0a1a071b12080c0c10180f2402070e10090b0402030603031210 57
    0x50300c00048800c04000b5241d940c5007580000b080211796660218100c00d200144d41000c0548100c54014100050b09680341c040603940c410050703400740010270107030032180041d0101024000801c5951104612440220504000400c085ca138000d40c40c45101810341c030031042e504403010001c0304c03406101101581c00d07110200340034018070380301c0040855218180f011100e481e900c1000031111101000403201c3d41e02c1e000c000305d0010910440001e0040380c000740c01d03c6081903480d11602e10108440440b842200008200f43c07042040d0f001010340314590146605100381e0814114000011040c140207107000400101e0344414842805580e040c3d58008100618917110341d0000f5000040840d00080481e09888011902d04100040d0300117450801c9038104c0c41c0103104003807a4150354107008090540c8505600000c2d0120b000d415144280d017142c0380d040400389003002180a42c4e00c0340c1071841c400c03801442001038640300002034540c140c0003d241c2d40c00355143c0c18102902000650441000c4200b06e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 957481600 1250 957480350 957480367
    0x1806020406030617210c070f09090b070201060503030904090f080d05010e071b02040c020c0405040606082112060a030f0501051b070512030a02040e0a050a0b240d060308 74
    0x1a8020411035410303088114402ca801904c558a4242d40700e840d042480c12141008503c50140f000341842d003980108941c016602c401c008000c00403580c0c4030f1641d06440c0d00c1100100028450640d030050550300082c0011410300000a840c1d00034480303018083c3d9a998100010301041d002c00c101c42c0c130b801c040071a5603a201c040c1c03031401400b424060070040b640c2d407202080d0f285116840d0b4804840348402520604840c0d9401c120240801103044011445408503403401c40d5194400c403070040c0d201e00c100080040c904030450341030044660b883d00020781030b2008020030f940e20008482e109021407203840715a50b54100010708000e01504007500701e908044160003001030540c04240904226419010f00000701c0010040078828510010542d40098260404242030240916001114048050308040d00c403c4a002c40741ca0880d12100c1c800d49800512281003410700c5445240c000944541e011011702c54180e0340780100d008464070074203100140b181c01601c0950b104402540e401000c8580d41e00700f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 957482850 1250 957481600 957481607
    0x90c051c0b040e1203041104060302040515030d05070302031801090b120403080c04030203100507021905060f160503160c0f0501020304030809071409060607050604050703052503061806020406 84
    0x840081c50089180c84154242d28400007003003980e140510203268078541c0c03142d507103903a100c1c003518440d17402c0382c1c0380c50000c001a0b60314003030540f0801c40d1509505002000c0410140b85c070010050000c10700400b000350401007613001c0103c4801c41c4c2c1041c092010101c104004942c1b41c030142c2c0c0400444400800d11540e21000e0032680360246010b6528018913460759882d55010307218a11000b541a44a140d90101c21209a0071856100100b070058440200c2c0c1c0c1c03403d0b080c44143c01c10080303405402c5041005400032604a0b030a4014940c1c0802d03c00045030381d04003070020300c00a410341100d0305c14180e09080d00b43c41903c2c500c1078a41e1024115511103803030300d0914041c3d04140c4080340130598a40000342d02000c009040380481d90382c03120300002f1000081c1800084007000e48400d40143d02000781d00d01090702008132a000e0b0384202d0003040c095255091490400f40c8000180ea07541d1891240300407054003505040c4141c94000d18005001d92400c14400110ba8030154010304036400454001840c1780c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 957484100 1250 957482850 957482861
    0x1305031c060b180909010f1503020a09090f030c15060b041401020115090b0f0a2903040f12050c120c10090209280504050d0306150801090c051c 63
    0xc00000c144991a2615080201c0740600041d03881003100c490318078812807414050b5075030444924000040c941d400e242c54102a1140e0040c20750f01080103010400840c144004110001c04a401c42003000c010250b540a006900110024040010060b040801c1c40b50320501d5801441202c40b08014455a07040280394940040c81000035001d82515812244c0d4018012341502e04811400c40c0c0c455410150628000c00c2180a1140c200900b9403c01003030751034010300c0d0006022400701d966140c039455450714004440c02103501b001e941050040c44000783c100c0307580031074959020b9880540040440c008403090b0040740d0101004d41304500300512002848402044020048001d440c41c170354481702108251850403c00079007018114000a1070082d118407007000108412030380c1001010711943c0141565030079603096490b41c00030b0540312a829010b10801c80109148295210640c01c0f992018202c4001445811159916220a8100244110f046400140e030714843c00242c101030300342c0349000b0728 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 957485350 1250 957484100 957484147
    0x9091509210310170109061103040c05150a0f121a030f0a0c0b0d290406050a1d1f080f060c040b030403050c0a06060b13060f17130503 59
    0x140c1d5a203505a460390110201e81c450244a61104034940c03070000010610403440d0464090742d581c50000400040705070103074881d86c113440c204464880c01c09052943d50141c040d40514403c400d284c3c0c0d00e80d96090882d0986000e2001d0f803c200007044030104054070901a0016041c0180e03203003e130302e43c010883c002d641c001c00c94800e80440d1a041580d02041e940d4461110000d00141041d01c0300300050b5038110000e204544140c50b0104407110340605d1920f602401c0f0120b030000c00d423144540b000d41c5c2070074421a40101011a078490305545043d0300024811600141801d5000101d00000d0101e102680c1b45041d039601448500d0000756102541621803848514002c01c0340280e402086110038043c0559041c1e0b024248030b140f541d140ca40d01030b0740a0303000c035881c04124018002001c2c040703406ea1080c1d10082000b01816a51241010b1000728200307031541100c0c0c01d001142c90807055440d03024105d07803600000201305016030389441101004204008600600c0c3e480001a11018118801065800301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 957486600 1250 957485350 957485383
    0x304060213120b010803090a090504080c06010f0e090111160c03052d030711010f121107021908070b070611040306090b090c0924040f150801050c030609091509 70
    0x591725820b5664a0380304010303859906c40c2000006120b110b03095400542c211f842141d043d45005254230119003411001d034032140c2c152801c041c0402040230f0180540341d0182d02d000003080400c8251520149501500c00104159a0207070a40b0040015950510300074642100031a101860403081c4044460785800c1c040030b03110348650400060f03282c0042a540a19400070303040300381020260044490480035100d8604000900301d8500030082544200800e11000303980f020350b101d9060041c8910094404002890382c0200c03e003c100345400410701405945001680540d0b41c900d9003420700103407500350129100d62000040010410405a0081da00e05214404010032651340440c07054544440010190700003801c940010002900803070403c1014004103001a61040c000000c1000c403003804c031445924940d1100c0508003103104034001c03070003080b01d80020304c4185442c21003100240809820240644080004501001010310070410400c4520b54031112030f20708080744035036031103411080300c021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 957487850 1250 957486600 957486623
    0xe03190b10050405060a1517070c1106072406080102042303070608070804020d06150512280807020310020310090e0309010e04110c0703060606030b030a0305030406021312 75
    0x50f04044c02140c1c4070302c000078148880c0038540b04000e5030705c0740420b007288100a0462001d041c80c1e901300d00054011702c0c05176500c001c003490510b046c19128841c6000e0510884040c4803c000280030310356010900011130b1010203801c0184009080603000341d4011034200c0d40007150104520203210048103041424030000c0207108113031020700d83c03990040c0c000c00000514650002f070300303075000d20300054019101130682149140c042d21340200303c4212400c100307201c0030764050402c83d07890a524000800d199101c080d0150060320b01ea0000500c4100b0b1109440f14a40d4101c1000d008404d81550001174000d03099541020800c00d0301c0c0003d51045070b075050f0080032003d011802802512502c2504101c4800030351401013840b006490010801d07481a81c803503112400800021301800241c0b4021415038000c280903800c0d03203815001e41e61260803c0c3c0030140b0f003914020590360001120f00745a40c15041440d038070b440364103180000e48160119491003080c0c91600041000503032040300112406070000340c92 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 957489100 1250 957487850 957487859
    0x80a0501060306210309211208160c05031210080f010c20120d0b0117090d081f06121b0905130902040903020d1d100e03190b10 56
    0x8031001c3d40a04801c441c1c0001c10003100f04044191041e800d8004d00b00704050303e60b102010304100c3d0010b5117410700c203804140803400f040740401181800f00700c2800c0800c0c0918240002c00440c4d222044441708200ca5060580e0902006104560148010603d80c03030643c5800c106540c0e4000161190b01c0051044020480c8440818070444100968560351108640c61018140100d484042c0c0c1402850240e00782e038040e040039030030050100c1c40e001e44001c41c01c003035400d001611101c1c00401c200629041071003001406e0002240c1220380200500f4081100c1e00d4841040b070000109405440c00e0000b1614041350340b1350040441c209084808405006609440b01890050b407059a69200413032a648001e2105c0c0c034240785214100b013250807000500d0445500050207580400c1000d5002d80c210340c1445544681c01140529241256503002240402e0030001c1020b4012010340101088007040c10b90034aa5030a10103002180125941143d501d0480c1c00c1240c00a9015122400c0461440c00d0005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 957490350 1250 957489100 957489107
    0x140915010b12070c03030213062105101e03140c09070f141602150c07051f030506120607031512030c020904060207020d050a110f090a0911060a080a050106 68
    0x105202988100d448150b1104031003070300c61348420302003103042c59001d105040c4201d02d800c507501c0081090766100c06648090002901c04081c001c560031304d003141082e08001d500c1c20100c0a5a04a50ba54011022804500215140d10b02001d400c0209850920007a16801e0180000c40b501500c0c0222500301003a211400c0644498102492010120324608100c810806880c4040c101030800110102c50403051940059040508180c40004e07107070700460701d03a411080820410020782802d4a49458200080d0000702c400140481103404054a03400001c502c0d423a1078000f8102900340388200c410f2130030b00c143d0281c007407da4007820041311340304d40c0c40010303080307036042a0304100b0f5406031a40f00c03105002d80c0911140400040054481c0c40c1c081000800580700d50840200c421301400181085040c24502003078031a0030400050711414401c2c040c480da550b1100d040c66001007a0500004411842d807900c2d20090b040940115807210012420409454004a410340301d0450910104116a2605804d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 957491600 1250 957490350 957490357
    0x60105031203010819020103111b0c092202040b130203190605100c0804081e011505130f0b030f01060e06100807050d0e010c030606030c08010b03130204140915010b 72
    0xb4820ba40002170100300701c80c042c000120b40700c1c018174008c9000b138600d11082c42c180d44855101c90740c0c581ca40c1a458094101441600d020400490701000203003000c0f00c008a000c14484101003c000094001004668036030b80031084204000d0040686100d42107056002500300722110010002c000701e01040f003500900c520002c1e200700800302c0c004101483c208071440c00c0046000c54058000700302c0860711400030050405074030b1000721400b4100c25005442402d440c100300c0070b20700082e94050140480e0707584100304400b01341401c0d00092801e240403061000f41c4900d00555426000d19610410340d99010b400100696666904145240c0c403a40184100c072401030041c0700010b912000411a0703a4414801850012080c2d2408107048c800c0d0480346007162903012185005c42d50f2202c0410240f50540101d0b0100090b504114210f0740c90012a0840307407100610503411407648641c600b0031552070b40d11080300b000c02080042c0c814a4010010f43c1d41e003603e8644d80800502d0b030b04c000107074407003078100701c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 957492850 1250 957491600 957491609
    0xb0a060e0f10141306140a080319140702130b040e030309030306010c05151608010b0a0906080c040e0f042622030501020d1406011107050f12060906010503120301 71
    0xb9410703a24684500d034815042c05828a60b4002070a26101100414a000e40c1d4007400c2c08010061500c00070404000901c5179562140b0119001446420541204000058100358282c10074443c80e10b0a46c100d503909208415000f03600802520861081031055401448000350070f0360b00300614054101802d80e680400c4500711420351040002441a5102d640d100c0000791140c0120358041050311002e4035504811244110340c5179001d07980070b03151036010034090b00429a00c814185480d50f0440d00502c4445d00303000780d10600c40450046034541d40c02c0412100100388521803a9818240845840401e810a99091300ca01410101b9603890460801e580c20310300851760b04440c41c1001014100102b54041010494002d4540301c0005c00702d10280000c0800c103d2041d070000302c40b00c4000105010910180130941000340a800e1032805000000d840d03002d9410450f0301000300102c10001030707211004c05803d025580079010921540910006001d81600e00440a4481403200c203241d200315400244507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 957494100 1250 957492850 957492871
    0x31e11060708090d06020c03180f01080903030402011d0d060207050105280b04020720090f070207090513020a0b0406080601050f0f0a030b370e180a0b0a060e0f 70
    0xc00102072505800f000b061a100d174201600381450680100d045400501032181a600c90b03d5510381d061801c03c191004c05102424401c80a05001c118182c1d00d010050000f0f041c444c0c504941e60480503005807050841030000c01c418990351940c58444c000e50081d880c11501c56007040b01141480207065001d0345d000c00c074100130f00c100c00440c0b02e10001610220425540150703080003160040340b80060400c0f0240700170403d1200002a110a006000100070295610703102220b0034070107104d5022440c501160f00680010546841c0c42030110410f080a1000030342c881c2035850300080d0717842d8560181080301c001c0d440c0d699aa40d9080c0065032644501800c102d1918003c11859280c0202c03d00585242e2081e8540000c4910524000c251004604040641d0001218196841e02e21840809495014004040e1540d007890000d4030f20300030320003410008903500e80b202d503180034003000c00404004c80c3e008401407156040030807004004003014000d900900c100d800009003040d04c00280103010300603c54 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 957495350 1250 957494100 957494107
    0x90f020312041a041203050d0605060406081807060203030c18030f0109150b0307050d030e0a08011a010c020906090c160b06040509191e1a1519061206031e11060708 72
    0x51b01210385920110f400208a540ca1101140381e0b251800036001034061601c80341550706045024041403000203209030341a5101c60b109000e6568040280c03604051500b03000303503c50102206103030042d44450406a018407a42510040801c815000310701014003510321256090500c0c4141c2040d01c000d068030a030560702089080055043c203440b4101c905000f458030043c00a04038002519802c016441071146039100c03042c10040c01c02007924110864800d003001501a412036010a0108500400a0b0300c9140e00c54000354208241c0302c125440c0d00c10000b010046000315245c20392075640c0130f50b0020301643c030b400000f40140360b00042c9601032500c5499507884204095803045042644041c013030b0414507498943c5400a070480d00c3c0c00d1034582c407a81c0905a40c0c506001c0c001c100500398a0b465101d5008030301c4518501c084000c0310419100e4070b01d44a5a00340c803e44000c1c0c060081603000801e0243e40c0d50b030b130b00c4040401048240005100f604ca40040d00011030803c1414041d15038007804203003080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 957496600 1250 957495350 957495353
    0x604060501060f4a041a1804020102120d02030406060b0301030807060b01051c0b03160b0d050604090f2415060e03101503111012090f020312041a0412 66
    0x100030742c0c49021340d010074044c40040c000300703d0111361945211140c03091404240d03c0410746001d001d12034403240c04186944510754002c0c0018291449810145109035076100442d0540e4401c2c800805622048602503994507820782e60b10380290701c2154192603052920002050207040f00c81140d040369001080c042c01e060140e2100c00c000c240144032541131060030441c0606150200b5612060101070f80c6000501301d51035070925007401803040f00e8242c0e00044090038065020540700380d52510203402c0001803143c0e10600450010892240040c0c485040d004002003088045400c51300c40d1061420000031280c908002007054410442100311080d0042d0f80a100c01841403c00455440c1c0c014215080003da50700204100e4414041403404052074150520521082041e0b0100021041e01e01501c4910702110083c4403c13000300400c808a600c8071224000d20448064801d40d0f29001010f80f100014980d800c082c10794010b1180d50300c90303030005180d18415401042a5400c40b2810010802c122885 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 957497850 1250 957496600 957496637
    0xf1006050315040e16080f0606101b050c1f0e0409020f041104120302010b0111030f040303050f07020315061206130227070509040e0a03020c0603060a080a050604060501060f 76
    0x800c40c0c0100c0c54400c0251a0780301626800c0b0085c0100001d9000d82884083c03800001c2c20498010b003414051aa001d4200200a40c4203103807481c900d4140468401802d07251400b40c0c2445104601254404401c0030410704a06000d400482a800c0c81d4a400e441c0e0181c8005000542e000d682020b907120031205840c08440c24282c00c02c44106070000300281c40d0946401310111080369441c0260300503075445101d06140d58018484503851034120340150300b403140104600e100341c070560000030100f02011031350051881071001502c0100e03078020140d039040c21041c1440000c04500b2102184038580000c03c02442e4100820000d000b8107203c0444606a03c2540031301c5042041145406a004100360304043d40825506044d40514101c1d600c082e902c5211008210030b44a2414a004c0180c020b82e642400203038000039403140d074031001d80d10310303031241e613070390000341110320700394803946180c00780303003110010071901042003803240707200b10700c104000e90b202d01044a02d0098603c00f02c0220f05444281c00e5040c60 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 957499100 1250 957497850 957497861
    0x15020a0218060a05120102040e0c13092a0f020106140604050607020d0f260a0806041a0a030b2e0b1303140606101e260f100605031504 59
    0x200540b040f01c560341d070740001c0f82c4014a0f2041542c1d00ea5130210f020700900341520344054101d2080038400c0c1c00e2210345407a40740001e40310700c00c0c1e445a5588079010655102103040c00c8030046215020303801558041c0601528101448080174015481c054001c1207000907803507030340c40026025000c0c1d804e103410304040c084990701c428010381c1d01840b9100d0100c009454070811908040c8105000c5446d41c03072285084180d030b101d0f071207103207003055041c003c600c17102d0f41c0039407000e911180c01c880110b65111004443c85118070100306a54104130580808000d00030b803400c000340107900d00d1015810003407116451784500e13904034034203101e0702016220400c5800c054502408000902502c9400f00d5607490fa01c8520009162514150b5508280f04000d0303d03140c42c0c0d050322403004032418180d841800840100d0b030a078044907440414011012080c0c20100b074240400d940201090046000500340f001d0003030040c1b002141e045c08601000c031070214003548114166401510b10700b40e04d60480f5030f040200006000e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 957500350 1250 957499100 957499111
    0x210c01021c052d070b160824040f24120b042405040b070306030320031e04080f07060c020d150c0e010e0d0c0504050c0d020304060615020a0218 63
    0x104900c212002c00c0c4040011035504810703180043d41e407141490940c0c0a0760004061045d11112480036001c1d50360081c407e82d91020010726034030280e10520b00074428200205810319082882e190500c281c02003d2b50200c18100c0407410003149800c080c2007458113040b050300070344244510303074808a0006000f03201d40640040c499981c0402089500700f000716442500581e00b2011071325a070a02040c01944401030b0707007003641c3d890f09020300c41c1145c0340605000803030710301369820114079103c8401100d4240227480c00c082019031a8002e464003800c407004070341c000c2c1c02001c107280943c2190003400e000010341c01040b01c5454850b0344602c0115020442d10b503400e0f95094440c800324590041c21000c00388109290f81e0400c1c0c440b45106095000010035445112201c0346c0a003d40050020101c1d11028028049480458010926548001c0c45044500030080480e0f007060022003480300f00132443c0c00035800c1d10310015040103100440e00040b80e40d00d442c103c02039041046555401601d500d4051402e40c400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 957501600 1250 957500350 957500377
    0x1609110306033c03180405060904171c0c080c03040b2404021303031b020d0f0201051201031212020f0313050705100804050c0607210c02210c01021c05 66
    0x40c0a42d25919051143c11140c0e01c8060b000001c0c1e4038012111704203690300221040d58204030310f2414502140c003400001c2d00243c50141c840d0084540c00b0070300d600310743d60b0714200005180e90b11590381e0002d02900b90861002d01080e00d07200060a82034081d429a4402c40d0048508011511110071508038003891000c01c00c2c070711280040d0351f000c0340c50303e0000b40a000b8221a2a40c0500c0c41c41c20010050010031000c01007002290954001590340c115501410a8014184070605401880103039964414007000134503e030056000003040c0000140148610310282d103403a03141c0d151140c0d8038000c078401c240e43c4402d03180c81440825802020135001501151081d030032a1400c40d02d80c030001d03d80c1300c0d80480a07000a0155410001004010b001c12042c40038152080d0741040385544d5400042086c03103211130b050a490701c100d142414030030f00c0e01100c130940207484d0182c0c031880032010324404034202da600c22443c465107001c0000e82d4070020b4503841101c1800c0240368170300080901100c190b40031040c2640d40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 957502850 1250 957501600 957501673
    0x706140d0c020f07052d0f0a080604050d0e010c0f0606030b0108030d1805030405060d0b0916112b03482f160911030603 53
    0x49040601c101060303041c0310b4008000c8907645500a03441c2441c540c1185020b18019412200715922103840140f000a0f1750103425075060a41c000300300d00c0c012542c090b6a00400704074000607161030200f601402a03024006030741c0710f414003140c10358440c140384504c140000d6100307000da070100d030784503452540451003807102142e450b80c0e07900c0e40030428000780c000000b1a000043c008240d54494030030745565918000d503041180d511a04c49544a000314481c50f03003e4100051102041841c9a002035198030005250025a080ca114003403003554081c0c07008800314600c0b50306038410030400206e14444c84a041b1140121400f041445000c002818410000b030644a00524507064030824202c458100e4000804469010f64001c913501c0151301d07034150010642003846004c40700d61109450440303188940c280107601084040034041c00c016498a886140070303e0a41000701c1e04010740040071140e40382e00034000406140b030b03401607500c020381c1d0761a410360021004d810b2a0b4040840900310390100c0c007241c0346 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 957504100 1250 957502850 957502867
    0x90a0b0901150f080708010e0705040e0f030f18120604020f01050d0603080c150705071e050a0b01080d021902041a03070f08060a020301050d060e03040f0e0a050c0c070614 75
    0x1c001043d000140303103d81c10181403000d150100803078001406504001d00c180303103440070025120010f60040ca40260748805400b2164a400c000c0542904845e10450341da503503c00070070403a075403c5000340d00c0c40300000200d807907483d00c2e081401d9031200140384064a16925650b0810060f808544a05030520509110700004040c46100d00d800840c096207007145c1e5548180285410508800c20a22501c541c84080c805491b1340710041d02c000d503901000d120410046078651034503403c442c0fa0010824440c000503801040381741c20041d07040701c50350003c039403d000030b0b1401680c03038010307194075440c1e00c503052138803640545480d0304020945a00400703403904103400d0001080c20140c46030002a000400907104124040d010400d09a1017685120118219410040040d20707440c2100c02c040c014070740303c546050a501c000e0003241d004007154200100141d68030010421000b0046803015402440c200c001030b80403620f0412603500096000c0a00540d03401d10b141980c0b20f21055a941d0315424040c0300d07840 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 957505350 1250 957504100 957504131
    0x1031a150301050f120a3e0109060e03121602060c060711010c05090d03020f06090c040b041503021512040606052106180a0f2108090a0b0901 62
    0x40440d090545030030303625030602040c0522090031030316450068001c102400c02101c5c0115040d84215407010b0360103c03000b41c0c054a200704200c02c005502c1c0e45032089440e08200c0108181600c60f4800a807503c1c5100740e80d8280640746007281205c11501740d048001c00c09840650b0038001e1071000858201840c2c030944a8000c128543c12922826440e68080d40600c8103c035040030802c502c00466500030311510444d11001043d6006004865020b40c10160b510b40070140240b00d04161018400201c0b541403802c0044681e5a600d888807660081340b802a8080103420301d800f5980390300071860000307402c1920750b900b400119540080002c240300002d01c201c2410305d020710300050189000307000203d94242082c0400013590401181700a440204850004003548081451a80082c0da109400c615006e2032117000d040154005e00204000d48480454007006800b0110a01d40d0340c1c000040516820843c40a0b15048025070b0148010f90100f8803040015a04191300c6502c18550000803921149407841030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 957506600 1250 957505350 957505369
    0x11250b04050102120a0204151101090b0c0340080d060306020d060506031501031a0315070f0801080a0209040c09051303020d052805070804080304050f01030b03030901031a 75
    0x8550507500000e81c01105282050b00e139030050b0b5001011894185041aa540842d200110410520442c01c1c03492041490030b40c400d0351426000081010286080c0000c2c484980c0201d48030b16506485a6102c400031081c043c142641c0c010b0310a0525586442040061a03420355001c200ca52031000c011800c6501c20034040d070f100862290740d01503281c0f14007601c1032040c5d0710b80380c04c0180669014010403503e00069111000c2d90032080c00c00041e070304415403446848a61040c100c503058400e07144043c03038540d11307078070103d101d00580c0e0307506245408282021161600c007881580055030004410310050f1800c2124284c03c180710300c020380341c06a5901c01120986608071031824403071103186c8002c0c09054062003000251001d40c60254034240e01c180b1503050034008040b000048c2c1c2010000e8620b0395000340308a0303000d1600040440e032642d60b100f00d610340d242e006c0e00940d8020101e0030460b140b00e5010b401012403001c0004c000d107081a261800440c0200901401e000b40e00301c12420303040386911030035880c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 957507850 1250 957506600 957506603
    0xd14070312080a0b10020a0b042d0209100f030b150a030302010b010212130909060e0604080703110a020d0b19060609060311070809060a0215070903021311250b04 71
    0xc04020f4a08601588100e442c100b6409000b06840081119450344c04a541150036038004101c01c002d4889043c070303022602c5401880c013164000003240d04d1400c080c14800b100e4182c402c03607440001d6900d011282c010b2002c20301c140c02011118000078000074850324400c660008808000e440b010112000141c940a260742c810380240c1d40d10943e0440c196070600c2030a42041030188224900004002000801c203a00c0c800c10040399501c18001040040380e400500e2402c2d12002110140e0900d410310401e20f5109d1b0b103048002c1a908000c0141c01322020600c90741503a002407a1101d2500d60b03486403014644010041c06411100c80300d26045000548940e07400313001207550b80d603100e6060050240803185070003441c0005035001c0c00071100080c8558101d41040c031095070000e03101c0c1d00c6100203a103070000b0005144070350041407080040850b40031000c1011240226010705110040c041c198003107440b503070000740400d003042001240b5200b08249202c420030484a0501c0070f0341007501c0364601032406440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 957509100 1250 957507850 957507857
    0xf07121a180903160302071e0518040506070f0309151a0901030203120c0307060e1c052106010e060c01050f1e06010f140d0b010f030b0d14070312 64
    0x600301001d0a0268000c0030100210345009040d041240d4030980c3da0064107135041d40c480e070601c2c001c0200b41c82440950000d200c00107030021202c1044100b80c03d4080700c0d01656005602e40094400100c0500c0e040d103014a4009029002580b00c800d0211070b1035209550740c0c400d02d500c4540520010340e0510005d4226980044001045d83d449510014403540e0058070781c0c8180b08070401400503030b83c0030074100301c50082c0740c1e0181d03074808003400400e0440c0900c04015101c00d151029130b1903001c00108603000d196007203600e03818401d0400c840503a890f0103800c0402c1e00000e01006003d11440a40d0f14145c1c11402c141403401f99013120034006240c0d58444110b45106075103a400740600d20362103000d5550004815171180d195a400804600311303841f80207040b1410003d48000120509000e14100c0e00000b0109100560700c02c0d0315203031500503060055000340040c40ca00544d50546100744140c0d08000030040400c400006903446801304041001d05114907801a0b4030000005061412a00c0704054280c9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 957510350 1250 957509100 957509141
    0x40c05030f0d0f031a0402131502031e040b07020f060d0207050a020f030c01050d0b0f1018170703030c060e030c1f0501030c0509090c090c090a0b040e0f0712 69
    0xb2000340600c152003166800e0504149066030344460821900c443e9044c02ea80040c0c4444409600d008135023410351142c40c42c41084032182d00415401b00050170f580d54242c1c160340591007000788d65600b40c4168800e0048038981804440018602448640c88881c0003e1042e800d01c1030300303041c841c2260721880c011210741d070091f030b0b840045040c04d910104000310100c020b130a1010001c000644548601c0c01c440808c80d999a140b04050341d541d110040ea820b074042d0042c02c540e000010f000d4803a024461030040d4038518128000390307112103108403a40c0380d40f270040641501461590b068581900105080701c02170b41f1a42d11505480042018140380082c1800030400078009114100c081010418126600b42c1000c1c0103001148202c80d444003281c8040d504070290781e80702c8a481d41440145203003140c0c003202c0001407003c002d034240e010f000108022034180c0003c5961300740505c410303c01c6100e80c0b844c052140e00064103000c030b0104280c0d07021080d030074100302c203084400d051811108128151003c04a564 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 957511600 1250 957510350 957510373
    0xf06042a1106060901050d1e0c090f0f0902030705040b01020c0d08090a0902030c042d03060606200d210606091406090901150504031407081606080f040c05030f 70
    0x8200352604100f0585019210794100004500285003601010b0b2199141c201011026450700840c0c15030143c00000304108503440d120010050710360a650904000d00301700031000f01e0b0b00140704d03001590b0f500070300070008036140a00780700c05003030321504a038103500481310076145548400c80c10b00030982c8281d1200c1d0b40c8001d90801c05c5244401070f0881c4106500c18010400701501c403170200d400b034407144039907043d00d80d42c4080c4c0040103102a05070b802081c194240000104140e6422030020703100d003a00c40c403401000b01074076400508072030000442190721001080010324010741d10413145452030b040800110a0b200701d100c0c1035403403a40c000d60008103e94400c0011020324101da0340c008800300c4040b031600b2003040c0064010101801003840042c3c1080000e0f144034040e0382220010740e844002075000e00d40408540d0f0302c80d07001e80301d0b84009020700d4151048030008080d455055910301c0d11001d045442d40b01110b0311840f4014021907100c0203000f40420b040c0d80800c207141820303441d0002001101c100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 957512850 1250 957511600 957511603
    0x80f0714160627080f07050d0c260f0f07050715020c010e0f120123011a03010305280c09020706140603070e0405190c1d0f06042a11 58
    0x18600062841c8446503ea45800002c0401926070300b2030119512140500c030388038070b64800c8034002000351080100d01c05000e600003552501441c02a01500201038070710003401010f0b00a042954040d04007040610020001c0783c0c0038050102000d80840c1c1040d100366103062410712141c0021b21140c0e251078110010560402840540d9a400e280c9090804000c00114172a01003481410b40b0404400034035100d400001d60014540049807440c1003414010281140607100e020b00500e5405401e4074100140b4100c0402124100c80d8094000e1452251081001d45104030402c0e4041800060000c0d032004915240ca40001404980c50300581d5410140341410840320100040000491100100105658045441011a03a1203090f41c840c603592403400508000d2010329040201c40813400c5281405900864041a54004924031403280001c190380d20100d0011180400034042c4840060420f00f0305800c010381c031400306d017022030245d08060304011284c0d07051022030000030514100000441030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 957514100 1250 957512850 957512861
    0x109050a15050624030424020405030624012109150506031609111606050106110f06070507081c0b030d0801210f081206090f07080f07141606 62
    0x1c045034800c0e813030301d081c03a200d1070962050240c4280b9444003000207814492565000d45a41000c0c41009001282c440c490768000d4105015650081c40f40d81c0000c2e18502d0a01c0411107400e520740303402c5040755010707401168001020450808110941a112030020407203001d1580c15502c507005020030413031104559401c440c00202560300c0395020400a80c071021084510f0020b84185190120762405080003942c01840307000e0100c403c401c100a0340c4401d008066100324140c45c5142d0740c1c81500f05424100d603564031090b03030380c0c1302d9141c2082d008a01503501540050034141e2248024078240400c9100c0c20003146000b400300c2c002540c4414090b05280340601041080883e41d01b03014800b9418021903004421380e558a030401c0030300c1c0e101c65000388100041c41c0440a58020006943c58601c1d09000320307282001e5810700d0146072000d02054001d0000101c10b440b82c0710503520300000d40d072942c420040320800503145000b40440c061450340e80b001410000d200507040d000e6400012011480c0490440f003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 957515350 1250 957514100 957514111
    0x80307030513320709090203010b011110091112010e300705120406090509060d08070605070905030f060f0108031306111515151c0207050109050a1505 66
    0xd07103200c0c032200081c43e01c0e001c011480c40d540e8202001c82802080000500c078242a50900b611683e000011103008540000801385d03c01e40003071113400082c01c010741d1074010380b003003c5c0310942244018010384003440e0b00001c44030f40250503402407100000c0c0403c4034200841030090499441d04507982440008100b48041748201301e110f0024412402d010000c0c0305060f01e0400b00941000810b1030510604001d56481130300b0003c20659201c0c3e40348000713019481644a50360140c601d00700002d05a1600068010410b034020070b115141c080e2603914000140350040000342400600c000104040c1c50403c00a41c04d114020024803480c01c0100b108280306005a01645680d8004c110403818034221004e080c00b01c91540c00c00340703c20071072210041e0820104081e0300100140c110100404150541620440d0210030356a44034440c2d400c5907c0401c030700c07d040c07807150301f8440802441c0780ca06a59004046081c000d00c0005080d9125030b482c0d6042800d00034040c1d42c0c1c1079070802003445c012042d20607a50000e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 957516600 1250 957515350 957515371
    0x3340b0603010c08130b1f08210f030103020906010c05010c0504080f030c0c091e070905010e010201061a0705150a0504120305010303020d0f02151008070603050c090d03050409090803070305 83
    0x5280050010030105000d20004004041d600080347c0c914207502140c8251103d003000f1100e0164481034000c2c0e44040c540c50003040050407850010100205104031480c1002610b83d0b1b0b40703143e08640a008003003002900c0030b0f04006c2c5000b00c0802140c0b081c03040c40b12441130350f40e42d03994803413518195510b031003528605e007030194008100b0303441a0341000582c28000041602e004030a80c0d2105006030a0311031202400340621b40001c10041880c1e403040c05842641d00981750301d040c50764544012402c941715030052103402203040d24030381001b03c05c41c806046102e10880c00c40314455080480a021100c080d00c1700745120341c541d400e00003041001ea0186856000b51f150400c410362454600940d0b400c1404013100502c0308095000c0c4c8028801c1c40038000c01500d40980d1001c0b400e01e05104a014606841814824080d441021500368482d0185034001d081c1c0100c040c0c20440b8030b50070001c1070780c1c6000040f4240101008001000c1e2070b47e006044042e402060281c2d22894940350280648030b00810300c0b03010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 957517850 1250 957516600 957516617
    0x11406090928020712081f060e1201060e0a0e0604050c012d020c010306060e092d0106050301030c050103060501050d051b0c03040906060c030203340b0603010c 70
    0x140c5a000364564000103050304a080c00c00d000b035008078121482d5109080c0c40f0700000b4908103108031081e00c0c4100e802c080d920180103658400004000c15101d00f0100300e910b01c1c4000420500d8810043c0140c0300400900424002c40140009800c465556100c498801210010489614501d11400ea04c80c09010040e182500e0a40d035215110000300360400c0c14010805250348542c004001d4280b110030809604000b000d81d20b240203907171088040fa207a400241007410114205205e520844071049014011041c0c0303807a00c030900011958041d800040d011001d04814111000b40d011a40c02030420380c44540c1d40f5411800c1c0021036102540003981454142603080040e0b9a1000441c3d2080c4500c0500040640301d0320324070031f0030241440181a19000104414200c0070003c8000c3c0200c42a00404004072075803900295407080e50f80d1005005a0428000081160f081e102e40511810242c3c030359112280062062040c0c00022010545410400c941040464142442840795050150410105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 957519100 1250 957517850 957517867
    0xb062a0f0111040e04080409020a02010207140c0f120f0613031112072a080f01061a16060204050306010b1b0a150b060d0c080402030715171914011406 66
    0x543d1180d03126a00d82840010001070500041c00140d43c09070464840035595000030400003030203134010780000d5407203201c02811180d90200000e07108440391b0002c0e2040810480705800c1008e45042150704500a01414003603080e0004103001f220f210f181500100c4003005118207004100c61420303194001c5581c0440c070202000360820341a510040c2c4d001c100d251700c60036501e503840d00e40c0c5207068007900150711040021400d0407022880e006e02100d41c0340204030b1a44c0d906002c0c207601a0f01100320708030682c00c08c181c070803034102002c1c0e050107030b4010440545050f81e03950100786058006d0744600c0c0030007400314010328820030072100c0140720003003c0700a01c00ca42585d16904c00c0d558074050203009140c0d5818010100da00e400058940b51071450404100c01b500002c40504000001c84040340320340100440400c0301400c6003200c1c0c0d40c0d8405561407001400b11a1075010809030041c240c20b20302001c0c1105100c2110160244038241c14000ca0400c09039450440c00e003030500c20661140b80b01e080309001204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 957520350 1250 957519100 957519131
    0x30b07030c02071802120403030c140304020a060c0f0f030c12050306030c04020a091a071b081203100e16110c0303180103090212010c0e010f0f030b062a0f01 69
    0x2404c0d51031401002640c0210203107000006d1013064003c01d00c841c2458100820b041d013540c0842824412916000005064503415000a1004480c020f40c4003d1610040c0501441407203404551803242c20340b2000344001c0d845070709103412181412000211042006410011014130102000c03070542403803801c5003403410000381c0754001411054061603000c142c407840903108110b034100400c00c0c42500300c20960f852048003015406014140e4100c1151038180700110300b03c10110040320440d0001d0851714044010100081e030001e48024901c0c051100042010b000c00c0481ca8010407250341001c08804032900007803d40f40101022850f01c3d004208410352548012040307542059a075066180d520402e40010b030000c2c400071801a410a150801194044405610001041c100c1d41c584da02103641c40801150391102d0340d000b400018020300c0c100f644050107604030340e05141e0024034090400984045240e50018008860f1200e08103c182c0314007095014400d4070341c1007a030742c8000c4c44226243c20686 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 957521600 1250 957520350 957520363
    0x409092f0108040302212101030c031403091216090501080a0204020705211b0a03050d0209040902060d0204050405091504171c0911011e14090405010906030b07030c02 73
    0x69040c442002c001a00f00740c8240000d611801840503000c800c61042803820b81c49800018201021002c145038003050300207102607442c1200c0d8070011600400e401c5a40f103a002400180301b102d11480140400540342c1c0d02d5240451041e09403100500380c0a80d030380d00d064003a500503071006218529080052200100108016000980582d00545d50b0150392030211325240c0e2110f0b10f020080c00d0f441004501d0300d03104000340481201d100c411800c0c0e91544100c2511020040c1c0d00901150302040945503010468000d416140f10090000030002100c4c2c010604a0f84a5020030201c1c0380c1c0060b042c007941ca000d103d5213401002c90b80040403c1d480d45a8481c242481c09072020340741c5641c07100340707030b129960440440e141042c105a5054040c0701303495000700603101c4d51000726030b607070400084954554400c0b04040542c00050103e080002200402980c01c01082d4002c900c2d8a00204505101915107010317250081c085000000745a070b107107082c445d04a46004d080007003014100910582d03010780c0010714 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 957522850 1250 957521600 957521693
    0xf0408030a09020a1703070b01080105160e062a0d031a091b0c1b0301021905090307051e03011b2307061a0901060c020d0f06060803040909 61
    0x580182c8900014408506951245200c281d48950703010010700040060100c0b00e200c0c2c051541c80340d0300c0d07411942c2690300c125905094203144581d045a80f51182c040170a0f6101c000d02444d280040f52030300317076149030060008580c1c040c080b21180c0481c1c400c20465100410302030f00e420072400341c4012407001c84000003d41c1078450700c42040496002c492050f1440300b040200301107140d81d10040640c0301d84a01d440c01c0d821050960b0510b4100e5141018000c8804155181d9180410740800d02025501504404101c680511030143c020920340c540c0c4a40340c1548900981040708121540c08060a4501500034560800480c0c101c41005503000715031001d07500781203150b03441d4104411080c000c00d4052054043c00c0e070390034681c1101c0d001442248215920400351215030507030b80c8602c4152104111840000c1d000425110030b040482c481000c100c034003511800011079001c1c3d030341030300f10320f1a04260085a2042e03034540d444001c00842101c13910048100100c200442d000015149074800001c80c0c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 957524100 1250 957522850 957522871
    0xf08190b091c18050406060507140c03010e1c0f170613110304060c23090f030a0c0609060c0c090218040203010f060206130519170715050f040803 64
    0x209180400074448202d00040086401c801e40500a030700034001c1c0b01020214001505140001c551810903015420a9403246e40716540f80a8072a40c50314841841c1c401015002c3c050003110507990f82e0207000c0c2032049860718000b06007111145551f210384514100c1c81c02c0070300545240119641e60001c0c240c12500059503c098281c0ea90031f00403501d00a400a0500c241e20700c1c0c00003040c890102d900241d8000c5003e030303604000105000100b500c4100902c41220b0210040c50002c500000c4001300800c7c4000c1c018006548071203d40010902c3e00800c803000b242c0032408a5002e000c03056110881b64000c18080c50590240c044c0340d01c42001d0007425001c0c24070281c0c7c00140690028203945020b01550b48040c10840d620341e564210740c07034040c00030300034480180605404546590685240180381c0c40d04440070349400e8101507041c0500c51440c5000b201c503124200001c8000e00865405041c185000350304087d011070301d0700f003c42c0c210742c40201414452044d040601c40440c00d900140ca90020601c05c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 957525350 1250 957524100 957524123
    0x7031205062805090106120b0307140f03210a181409270303010501021002030f1f030c0303170c070c27090f020108090d0e010e01110102030703060f0819 67
    0x495540c4620b009402494001140c03000000e14180c1c00300040c1c000900108003004500005010140c480349ea51142000442c10701480c030240785400c00d0300000401e0002c086401d0b0325400d801100f000041040f000d806060045088103809030840010916085201004030001d401d040c102d00521035040c42c020f01030503924000500025050701c2c00716080c00e286204103101d11501420b29070741d501c240107003401406445c42d081e40c40d104034006c2d82d0103050fa100080109035112002d200c3c001c1b0383c402d0700b401071504c1004004049960906068040e50183d07440c004404004440c00d0440140a040c0e4801c500b01007055201049202c4d40c51810b5880d18602400e40090b07000c40040c0e024607144c0700c5465075181030a008100800451000c0ca40703403007a21078444076562071100c180c0340c4200c0990a008034540350403a000c1d2f90f128041c000ca40311014100300088945140a450132a0000c8410201190342c8030340600a030490b803c143d50050203941c000f44100c02904248030080200600d00910307062943c2c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 957526600 1250 957525350 957525409
    0xf120c071419122106090c020a03050f0f1c1b110d0f110f0309100306051c0312020a03090b0c040b0d020306040b09071d0402031608070c05120703120506 67
    0x4d00c45540c3d411040a844a150728000210070b00078040341c130a05144d0751806100080312800494540d40341b40d0551183d5041c2015000180080d6001c0291416443c00070400d441003500901d00200d410710584c50009160909a1011418042c0e1841e44a0500c802ca6030446101d450000d01f8030b0806542d45001a12010308900644424000404126180c004c04818481e4184008003402020a088407100d1031008044403d404458480c050395400c444412513020200402410084505105c0d2520170000e0704482101c004070382000d4030340390009807a10b02100138800d407552055086603005a102d450302d40f400b0714148451050501000c44260080700051542d900c5902440c00b260001d801120a440c00d410010f1007030350b03402d0034100c0c503481c52280004181005e100340c900c200b9449400c003c0181443d0360907299640001d00c1001000102c5102c0310002e101842041703501c00c0b50484183d207410b07092901a0020b40b01c20b04d000c41d11840d010402502d40c2e5402c00060000c10001800d00c4800d01c2c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 957527850 1250 957526600 957526607
    0x120b04050d1b12110d031a0901051005030705120103080309011a060d0c0203161101020d020c0102070302010806040b0409152304081e0c0c040b030a0213020f120c07141912 75
    0x241e03400c108130b40145000d00078002e405420604480c00c0c480007082900d13020380b04010000200b0b0062a81011241544103040c40c060701c015600500c0a003001410b0100c04024081c8a070000d0700300300e680000210500c8480e034424096802070740c4150001d806807940b6007000c034040b8000d05181c0d21410f0385074922030000b5802882125040c0b0705003d040d095260719801c100700e100c140342440d14010302c2031a42229413644082a0034103203920582c003401d074203855a001182c25200150900b42c0c06542d0740c100c02d2940ea61440b40081141c405d51564000490b4404040122130403841100d0520180110503034411020111103940142d000f03c1c0baa8403180e0001d41c803140701d500c0c1d07407604134094000130780080503a0001442849400c8216000c0c0310f150304610505464243c2200000d42100102c1c184080b400e100e6009090001e0b601c003900c50400340071a40b10749814005807181d406e45500000c00300280004403d500c44080d0b0040300401820540c085980741807440024041c100340340320704a0301d221078417 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 957529100 1250 957527850 957527867
    0x3060302090a06030302070602060c190e0d060506040506060c060c030a0b0d0302061b2109010f020a03091406010303080106110313030b07020d0f0f0c0606120b04050d1b12 75
    0x2005020a141403074002070ba40c1c01000103010075805032086c180d0001f0034620000b1a540b244038010707201420000c203161030600e00310b051b03800f4005110340300e860602d403500c03a9600c0c0780700240651300100e031508040041c00700b01ca02c05090755004190800080d841503e00040281c8c0103810348000d00d60304d039140c84a10000341140310078194404040301c0801c0c281540021003038068a2491060860714040d0407030312003a80b1a14030303020074400005401c5460f180407581225404000c00c2d0010a5412046c42200120303486031f40c2c5580400e6031441d80d54140058840b0b0003001e05158030091400794150b48014100c0d002c144104002c1081c80c00200421080c24020345080d102011082d250703981e128034004224607400c5030000d0052080c1c1d500076154910900c802001c82c1040d858406054401d900100d0344040308903010780b4402c1d110140091102041c14441c5011401a42e03c8500da00305860702d1030a1a40b05034180e004c02c00601c145500b03140e0b0901207450f603942d01c070319030303075444000b501c025500c200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 957530350 1250 957529100 957529103
    0x503010819080d05010e0f011232062e0b0f0a03020c0123070c02011d0406030506130201091a0d0f09050a060b040f060e0f1b070c09060b1216030603 65
    0x1421302c3c0c00003d01d1104208170902503404a400640140c0e00d0b908140310601c481748000d0700e0600450030300f0340000e54041d0a05039403061100010300e604103100303589251240503205410030601d00e4241c20391000f80080040c074081e03c4400340142c1d041c03400454000030301402c1e180000041000030441e265030f0281d41240c0450300705c24024080e0352481c1d1000340380f070b401d51032501c42104660b000040c0241c0c4203003540f80105505071601c0e4282c101080c2d00160f40c503015010786030030aa40f001c0c0480810b404202d460f101d08494101d9140b540e003148001042c003100b50f40003c132199082001d002c0346020309030641d20b064400f803000161841580d01201c000e0000d0b00c001920a006d00c0c0008414810369400c403800701d00041d05e05015944a0b0100c003403c9440c07510030390200a02240100d000e082051050303540048103982030000c803114031080382070799a21680c0d04403042c514604040041c0704c8103001303090090032240105803c009103444aa4a001c03002480040007814501c980e0b06124020740c04113000d075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 957531600 1250 957530350 957530377
    0x5120903030423010e0f090a0f020d02070b1e22020d081303020f0a050d060507020c0312040618050d110406090f020304110301021611041803120c050301081908 70
    0x404541043c070a40701642100c41d400548600080b609034140140c2011041c0d0024152803080c1ea20907104070010030f0312004c05066a9002c00a8914541d25400070b4128280a4043e0816a00300081c18008819800782009007840440c1d04100300c1040d0400c9041e400e540c0c0ca462400303007130024800502e2055280c0e00040034200c0125003111072080700300110301903d1090311010300d046800380820822504510940d54005203404056000402c55080590004c03024011a6001c0007040b0009040c60301c500380c0640c4076600850204041c5600c55900314002d030790910030041d043c2c200004101480c10385e00000d005440800540050342e2220b90050f0700a11060800f0080d0310138110180c03001c3c0d441601d0a4940c40d284030315408180c85c061080300d2100c3ca03400680c940342100c55862074061820201215400b6075a440156a01e980c81071820103a10710950324030302c415944080d014111900300b031a140c00c0040510040c01103120001c3c101c2c0c0c10309482a49148140c0280c5400c4055220750440c4d000076 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 957532850 1250 957531600 957531629
    0x2d0108060a0f020c0316020d0506181c0905010806130e100b0901080d120b03060f180a020a092c1608160b09011b030503090c0904051209030304 63
    0x28010045010350180322082000d1054601241100041c4c0c0510551072240e84c00030030044000c2007041420705055403014281c1190710507a0b8585038105241220403030061940032200801c6c8980c20320008012101c0c41031203480c140850007006102c2643c034021607040c00202d2000c10309a50314003150a019401c0c0600600c40c3e041b43c42500e503141d00d0b001c030804100d241084c0102041d440c100c0303882816901c0f058010015800454000c45001c003800303800081503560f8010807103142c6c4060240c0c52141c1e00000080b04e140c101010507086070040f140d2070380702079003104643e28016a20038098004486241c20086005210129848004240c0110712400c010f004400c1800500000c01c015030704182001d0994241965050b01c1c6d80c82d04407420a01800300403810081c050500c088024041d0100c040c500b10300340560450f0181d10b0080042d40c141c000c03a2000c0100801c0810801c44808480c00070b8a5160031405c1a80e10b030340d9070300c00107148043c030004007140c0345100303840070415074000b002c099540059 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 957534100 1250 957532850 957532859
    0x3160609020d1b0f1d180610050f06180111010b0405090c12030c03030103060903050919090e0309010203270d08030708130515060f191403152d01 64
    0x300303191980307030030f8003000c058070000540300851800758000c41c4d0240d01c83c200300703c9001701d41500800005150302d85407a80c41011058400b8200f00c014840e1071000b2482400700e042408110b02881c405a1081c0315600c1005000c0e001d0000d042010344040d800e003130900400e00e05807801c0c1c2c05001c0320307001107410510b00000c1220f121000038611003121001d5417105148190700c0b0b0f1180d120710074804200c52035801000100001003059000c0b40070540649402c6050070485c600107900340c00805031500c2061210081031003003070294030507400c031040807000851030311600100103910b034003543d010b01e16044510118040c00c07100e001c070a44001440209030401301003551074030050700c0d0030031b035020000100780341d00080b140002e0200c80030205030000d0003081c1c6441401068480b81070010425034000d00d0000021000303407521101d814988000120040320607003030420a5000d241c500c40090b00c05e5108141e900b04444042a0403a00300c00705807411440d103140c5061103103c031485202c4207030362117146000008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 957535350 1250 957534100 957534113
    0xc1b03030a0e010203010815090307080307030203060406080d0c11060705010212070e031603021009050a0602070509130305030f0c1909060314070503180c1e010801120503160609020d 80
    0x510030701440408000c00c5004581ca0381c00c0b0f000034014041d042e80300c85c820700e601001c0040496407002070b0704100e9160450703a54810002e908251402c4000c0ba80100a00c02503240601403840a0441d9030000c000000000100812100b44c900002c0c10f6940c40d000c41079000d440d10b03000c40d292a60000d009540d20340358901c0803a900e0004480035030000b404107034808080d1502142d1b40d900742550324162610746003103408129002039402c1101b03044c07012800000403192943e100c1e4000512080e00a000464a03080038080c120304024007902130a1f10074404e28000a40120582c0c0c0c1248054200740c98035900c0e081e007542039114810140e00b50b804d540280b11b01c0076134071a82c2c2200747d545d11742c0d040c04458142c0c21a0032900e50295048000b00b042130000454100d100c101441c603208540003151030303010300c5002050320a07071442c3c0d0a044081c42540c2c02c1805580280000b80100000384007801448444c0d262640c4901600c608041c003101151001000d04c03d06400000303035140c00815031142e0700150314144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 957536600 1250 957535350 957535357
    0x210020304180c050406030b012d12020c1902010c05060a020301090c081509100f080601140a08070506031e090c0301051308030610051605160906030305120c1b03 71
    0x158049460402c1c0c0e031048540b940152440c00038562207640c01c0a00700720742030380074040081d030580c104280b103c4003140301140b6041098031401401107e400760004080d0082040b40c89090f43c0b00a1401008601056500015a404074082c0302c4400080d05c0700500c0101d68040441501625901c101c100340b11801416900a50481d000700e1401c000042030504140c40d441310440d520f0300d6072800c4110b12182400c02040c07040d8050321010b4551440780e00c1e025074840602d01a00855000d62180c401807040e0306412138854050b1200b11a81c1c00743c1890b014006503117810343e00400380614800301c0400e840c0c105030011090f9800c007118401d1006e25001c030b00166070340702a50010340300e9800c0402023210500c0040032001110b8210100e94611355401c0300780070310f000e180f5171003604104041004043ea503550010001d00d99105501902034400b41c84007070000103010b90060b2089034942481000080e4000048a080306030104411103d0303a6007101400c0b0742e00420f241c452510781600d420182c8040044006e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 957537850 1250 957536600 957536609
    0x3020307090509010b03040204150909050f0705010305010b0319180f030f050f071728080105030304270b040c0f0210090b0403110a02040f09020306071e1202070210020304 75
    0xc2039071082c0e4075010030102202c00c1c400c0c1c03c0d8000341000070401600302500a15422900c41c0b00030000340e6518507a031000c41c0c1c410101074502c0d400c5890200c00c1c1d880d003408001c0040c0f20900e020f005550400180c149148406401c030a800c16440700c0100b800902034116a150b00c907070003108003e480701030034258441c4002c840100d001402c4080c1c81c0318158061030581d0064024101c031581804002c0e0341d41070303182102c0c041c60003286e00c1c24002039200071012071513281c4c0c0344105400066482c8080340042c0803107006810030f900c00d40051009110300b0074001c200e80d5080182d414038140795500708000000801707a80301c5040c0c100d42818954181d40d078202402590352002039080701c903400c5076181000c04035103030280d00800351a000c10210300443e22070f4000e0340c103106c403030425141100c0c0d40341c0c001022680140085042d0b0341c1c48000383d405600c0d06001c1e4030b030301c411300e41010003000c496802030201c00901c44500d0b80600a40a1043c80c0313500860b81600c0e10568060a01101416440e101a50342d4105201d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 957539100 1250 957537850 957537857
    0x80a0f020405090f070b0f07060f060821030a09061e02030907060c0804141302030103060615020f0a240f150501050c0c0609180a2405091302190603020307 68
    0x3c100d0092002070074440101d0040c01400520341040054190707a4130800d0902041c100c00d02140001c5003003032003545a000c0030040c2c0080e805213030004050078401c011b00101008003208419050845865044035408078041c0d00004c0d80b90326504d4403000501740c100344681e640d84558a4460340100340d5000314080d0b9044811203001c265211403c035000200b4080007000360390148010400e200403410302c240c0d10040200391150140c00380341000c08a07042603006440c01902c442d410003090700d8001e0300454000c56032018003291a54a0382c46542d8828034030009121a4510b020103140c900103640502281d200704c5000e001407040d6a00140242184800c202030f41905050001907540c05201100c01c4400303040058290701e000c505c00c20001e5001384a80907000808000e02107110b20f074004d0054801d00d081640090f5007445060303800045030941d00c0c00b0103000c0ea845402e00040c0d50700d54a482e1b1090404218015540040c40400c2440c003c104027030b085074a114030007054241c0c158000c1c510490b41d554 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 957540350 1250 957539100 957539111
    0xb0f06090a0b180a020903030f04030309051c1101020c030a030c0215031009020c10020d0e070e01140402070203030c01021201061106041a18070b0a110106060e09070207080a0f0204 79
    0x903403000301d03119048100da01807920351121208040030f01c102540046901c00c01802c00c40d010001c00e007181d200041c4600d00000000d014410581c1020384000501015507120904101c81121000c102c507101d074001e020384005141344281c43e8820815107152010180c16180d013100c5526018001c1e45250f40d08a214060070286103929284d0002900d120740c9040c079400c00a81d2414006900a500101000310180501c1c000454107440c0750005082103044202c0c0040d010106440b0a41400b03050340003c0052070688004004100d1440c03402c240795002200c00698401d042d00c00240380d445040c441c1c0240d94004110440010302005c15681240c0321a240c2c00f0b009404c1403546a01e50004690050004d840b0700c5650603405c1402031440c0c0d111400c01c46078002589514100761510410364032a040329000091103055503607000c55100070003c8804008c0c02840e00300840030749101002c0d0f10490150309000c0000d28814420494400104503c40a07503900119504054040c03a130304200c140d000b0390501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 957541600 1250 957540350 957540361
    0x1e060512010e03160f0c120b100602031e090d14120702060a0c11120c01030c1b020d030c0b0c0d0c11060402060c030f130f0602030705030418090b0f0609 67
    0x42c015014445000350140d03160840d855400020f8030340c4901d0031740d146035007044502c0020b9a4a5010f030040e04002c01c0e860030200070392400c00d447c00c00051560f0305498014404002140c1c00000f0368249024a1085903000c11100340741400a0048642c044c0c1d008440001c8003080c010100f0311240710134511803c1d101040074080b00e100d040c0c440c41c64025001b02040100d491034510407420084254896a56524818846400600c840302c002c00c448200b500003207040c0200b5030701031082c10400407041c1001000420400805516101c0300c0002a02484020706103800301481642c4a449059100040c0c0c00a41004001d0303001c590454120354141c5854031300b811503224083c20000e240c7c2c4654000814140c6d541d80c0c02d109540e004108401c055100500020000418400c00342c2410039003034010b150300c030303242840a0507035602641c07083c800c0d5001007091034081000071049605540d4003120309520401101e181c140100031300f2401070100d8405206009640c200781403814020315044441e41d2083c0c490 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 957542850 1250 957541600 957541603
    0x7090c08010b1204170408030c010615020a08070602130317070203100506060702150d09050f0c01030c050d0c0203070606140906041104092301030c0315050c030114041e060512 77
    0x101d40c0c40020f9a108600040c000508190002c801c0816000b00c490a05654034051450340d0064030903c0c1d01e51351200300510003030042c18600c00314400c482c40240503041c002d84580d0554860840081c20f8a83c0010b0004650003010b4440c038001c40d40100c1400e40240d11035a102c01d1030300100c408034440d0081d8502400c0c003c1180c020103000780c6000745814503020030b81d4200a0010310741c0c200c0164210090243e0050768030a44140808076010380d028203480c0780051052406c1042805004c1d060501d0a040f6a00c5642d1200a65002c0c0c0400000001c21328140702c4181c0c075600402c1c10040806003001d101251010a0039840f000303030442501c0d4500952a20702c204801c1c0c46089580f107040410501041019200702c1d04042000c000280710000d49005100d003952503039000341c1003500c12a140c40e07420030412668030400741c02070200500800c090705040c0340c200c21620040c861443c00c24103c911114007581c0340c5d8400b000b4681d041c4400c091150190903480c0c0500a02d00c0b40602c2072900c0c2088101a200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 957544100 1250 957542850 957542857
    0x602070e090622020d02120c0102120c03042105030703030e0c0a06020607050906040e040c03050f06070804080c100c0810090204051c15090f0606060c0b0c031807090c08010b 76
    0x2c030003128100b2440460b51030032500f0520b070b0041e40e100c0904a0000096115582130349400d90140024100c03d02008002924040d40710350440e861860070407419540c2d810100643d41640c48041c001d8207106000c00b42e0680703403440f44130040c3c028000001d801041603050341c41109400b6000f41070b00e0786e00b4422130410072100302502c00c00e00036800401c0003411281c460300003001d170601d00808443c20161102003032004003034102c40440e0030020b401401c4c070a01c0f20421203206c8141e08040108500c0c81c20880043c20040040e000400049000c078070070004600900c410541b05403115800c100c030048402d00100300344000e655880c025401ca801c08504075240f4002c66043c5c035400390507030b0480e0f40310405102611060701c406641c10300c0c4071502d061280105001c2d250100d801280c0f1410010520705100c401c841096001c007043c004140c040c02c0018404003c0564040b40c6500748035280e5440c400081c0c5405540c0d44103100354015440007090521041d408035222000030340d0750f40d00507a00c84004400301d10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 957545350 1250 957544100 957544111
    0x3070605011512020d09081207020610032d06230901060e0f0402210c0f1e010c03030b0d1a0c0306011e0909061206051b0901030b040b0a0602070e0906 66
    0x40d288490019440f041c2e40080c0440f03007241a0004607815503880742c85a170303044200d07503080e100c015906121210b0f80c10400903421a460714203100d5000c0c03856440945d0300c068080d846c10141131000e0315032207851000340300d40341180e001041440341d0f1820903c451540b400c0c0885280c1001c07103404c003040901e64144655019507100d801001c000e5220600e881d007200100030012a440385485501000c0741c01105642c07403801d1500c800070004081c1000410184402080e802d501803c0d10a81d0100399556000c02003204850a090a81c45040281001c401402d03903070f00e1182d04101d070001601c1c20400074100300e038405c101100400e1b1030754840c504540102e1109a03034941c0060305844400400c3c80c4c0c40602840341c05124101030b19119507a500d158280c0b140c82c1d00144075902d02c010100180a180d011b5580d020940c0070740341d4640c041c003450301c8200340685107000d0704043e5180707203200190700d072940060f0380101c1c000c01003107107140e41d040001d5842a03940210680c071403041f00414180c1c40001076060203030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 957546600 1250 957545350 957545357
    0xb0a0c0201080c0f0a020607141903180516030b060a0f0e09030d060e06190e0106111e011508070605040603020c190302011d0a0b0a110c030c030706050115 68
    0x4155900110b42c841c00241c81c5002c42d00c2d040042c08580701e003280052103625a02c1d000340c04145410b810250244002c80c88280c0542c1c0b040054582c1903242880680c1c914056050010707005881001c480c00d203220514000340148903035180002e41e4802800700d02c00312407042641a00c507030380d18020b1203051607251003540300e8810030718000c1c04940c0440344002c0e1311407030140407281011500181c40080d1122540b01520000d5032400344940c07800d05c01e0707412103242500940d03414100d02d81101d003069181305105000800140060700d550f400c4040c00a420307010076091042d2107402140300c10600030100d500b0310b02d054a814040c0007410340303008103c81d400c5490075161581441c0c034000c0203a0195110b8410b005e92809032740c110079a1090a00c80400d410340c02a40001801d454480700c0d200a0b0f01c941c19103d4081c1d0011101030b00203510381d16001e0b40003000d5000420303c1103912200300c00030b0260b600700c08802c0c000070402d060305040c000040c18500780210001c0c02640d0340c1d000c0f01d0031103429603100400003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 957547850 1250 957546600 957546617
    0x504061410030c11300703174c08100507030b1906090602010e12070f0506010e04050606121c021227040e071a0d0504050105100b0a 58
    0x2440c000c0d8081c45061200d404e014107000c00c84c1c0d8201d414030b00380c02e415035150002042c1442168605d58012032080c2291084140781c0900b548029240130403480c00d40786112009000250364400c4000c1d90000c021000c031740d49144006404400d400d04508200700c000c4170044400924184401c08e020000700d41482001d450362140c2c244090000d040c0041c040350034151142c003118103d84410f0317107030201c40070381000b01c12081e810000c00500445e45540402c04582c140710304141c0007040824084000c0d4a036140203a45d070381e06481c0840d40000d00100c05080ca0040f8000010000300d4804a00d105074800d03025149e00e42c0d078030340c100b241030070402291500680c40422100e002c68038118a40540c00500d00445038901000078840c1015413007400c4480b07055598600340c810b07036620044400448802110188400c42d025051581d8130085481070451496000c0048802c50340d209017265208040c021041c000b80c0b40c14102240600070aa03052400300b108210b0000301414250103850f0a1000b07940c51110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 957549100 1250 957547850 957547879
    0x203060f0d080301030b070302070804080307060f06061409042d0e010603080405011d030304090207020901080f0a0210121503051005010b04091d0114091b13020309101505040614 78
    0xb42008000c0c002070608d9400c21043e00841c0905015000804080000716907030310032840c0c0310045d02c0510a12010042c142001803180940182030340d012480c0100342c00d521142c1103400240a010740400b40d0140313201580ad640c03843d500c0d983c10700c410251655400c0c040500c1c4400502d007200d8262001801c3e00c0b80620040c080f40d0311a020502c0080c1d02e2084105822614200081c10f6901c0f95104000c0c0ba030b80020311a08500740465014014540388010704038400c1104402a15481c448400034450820005450002c83c043c7c05000210149a0810041c604070500c1c14108006140002d80d41c034451120a107442010074000c0505940344012020706107458401c103200500080040c1598588815000034089202481014400d140442461203107003407084245080c40b07403488000703a041c9e1176204403460720b44540b107602048041800f00103a41c3d40d5850b140a0074120300400b40581903061036116400316071044c00d4401910b600f25010405182d4800e088030601c040007401540000f03840581e0f00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 957550350 1250 957549100 957549113
    0x307061409060d0b1e0a080a02100324080d030e16060e030a05100b0f0a060c030804021c060c020105090313170c09010803182e140d0203060f0d08030103 67
    0x84040036001c0089804030303201002600c0412040c0e91529a03200b109003240712403400101900080480c60f001c0d10640b6100c1d00401c413022840c403814014507444055007063306025290090340001c051620203070198440c1c85079519a100180d003000000c0c1040741e241e006d1100807411700142d40c80d840d80040c9552038203105071885070200030030b01c0e458020741080901191007444122130050048500080d02041c0c10300308204256501c80d4079010301ca00384070034010140c200c0001c10f81a82c241c14000215030b524030000700350015a1415205001514880350204a07054110056802c2d443d00240302d25035400c0021523584c041e6820800c42d80c0101c50041090700710b0600080442c10720300c1e042d119444102c1d0301060600134203034812041903000181e03154410020111003400c0c2d903804c81e51022020b5400c00c4444c55004508649003072144203031a11301c04640a40790148007460800310b00c540300c2001c200c401c402074000301d07081c40c01041c018842803070300c0c0341203c3c11400b065031240c08a0700390f9013180c8851 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 957551600 1250 957550350 957550357
    0xa120302090907183b1009090215040b1b060712410601081b09010909050c07020f060a0c170f1602130506030606010c020f04050703060302030706140906 67
    0x1d8085244000400c28400040710070b45e070244100c00c1c020411200030b170b400c401c940d0b15201c0d100014200c4030502c810303034403056814021210392500101d5420542d000040890f110300c2d103100009540000e0000700260898060450804c02c00304a401508040740129107604003281d01c400080c00103e4100800190307035101c148032848002e249060400044000c001c0c1030744000d1854046100c45e0740b5400c54241e05000c1582c804404e182016590400002c3c40c80d0341d0548040d10091503c011522080b16445105441c000f0440c8142c1401242031070040c1415a52141105034050213003140303ea141030605c4005c0b00c0b2080c00725940c000000c8a15190445005d0501000708480c0c135041003401c09815121001d88200b0310310801a800c413112910410041002d0050701000c01800c0c40c0030000035070b174046105a4048020f080c5181c01140d284009003450b140e8120080c0c0c032902e44414410040d0303040c1d0002c2c1c10b0324425821114240c0d10780906480751880240e000c3d041c1c01041002441c24241100075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 957552850 1250 957551600 957551627
    0xf0b0f011b0c080f1006230409050a0c080c120c01110708060403031b0206040201020c12070306050f0f06090c09041a031b040f0b06030115090b0703020a120302090907 73
    0x803919664030300c2d9199201c21000354820451580728100b0410f0562050040c20f040120b607550800081e45464086d12454580a82c4142d1040300c1c0d06141c200307919990884211581c0c1f21056a50000312458404c40040060142540030320032111746681504000d81c160701c0b5104100014885011040c0045a101c19810030701285409041000a40c41c42c040041e180034078869200860103c40d0610440b640c00c1c9403204090441d070107074040c4070260b42c0209030204054010f5400c12121381030000407034071300803c1341d20050043d4900000c0010950350b820440e0f005039000303c241450b42c2c5414040245081d01903a02c004c484804100080031440d01d0340c421542c01c1d4218040717000e41599500007a0a0051404460300e080c104031000400038070f0a0f1040040c44807018a04002d00744000001c14403601050090003c42c41c01e003101c7d80000c9014940100041c01001c503920f9452a4030b20b80203449101102c030423540b911441c02c580e8902402030080d500350120141032607280741c0d200c1c00d04844400c01c0510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 957553956 1106 957552850 957552887
    0x3020a0b090f01090b09042c01022107120e191406060a06050a081f030c0e070318031b0213090308060301020c073f02040f0b0f01 57
    0x140d8400000c1a9000a0318080f19400230203040c14104003d894000c40c1c41801e55003001c1500104042c3d180005600808103100b1518455030105540301801300c0d00c1c244440400c0300040e40030100000c808001c58800d0052804601c01e980c042590645001c5c007094135201080b4410002d090304150300750380c216826850120010200c0c02040800002c1140d02404100c00e031021160031515801401040b0308540c0d030700c3c0b40680c0c1003006031042c6da03044c80701c107c005416540244100d406c1000302d0200e14043c03040da59001c4515148040502104081344054040583c48424050f04d0000c002c000006400003d41070250038100020324151182c1c2c01080f0303a580303051003c07401204075442c1ca904035060113042c5c0c0300c10544600112401d45000410305450b018038000403112903029009450410001c103044803088155082c1000e129048203140480340025445206110025902c0f543d = true := by decide +kernel

theorem cover : BRFrame.Cov 957374100 957553956 := by
  have h0 := BRFrame.cov_init 957374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 957374100 ≤ n) (h2 : n < 957553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
