-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3424
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:37:13.997737+00:00
-- url     : https://prove2.me/submissions/04f512c8-b5a4-4672-b0cd-8bb52ebc466a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 615647482 ≤ n < 615827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 615648732 1250 615647482 615647489
    0x3010b0102100507140a020309011704020f130626060c0913050a02070227011707050d0227090c010906050a031d100b040b1813050f06010f0314011401 66
    0x203003c66560340700d1034190394218000305183c8040300002043d04400341d01000404681d002600d442d1008030403103003d44c41d01c60302100d0081d0420702ea96150380c618a410240b00540c0510120f010500302c2d1291181151000500d0074680e2030300c100300145251850520141d64481e003051003160400e0007200000315103807183c00ca0702c06082e50345c1010441900c0315030101d4005d56006007030300c5032400d17281068004408800141500700304a000002c581c0c0c0950380756001a82c00c0d045c00038041a81800d00304030141d00012004c0341c0c020040940c100e000582c98403802c0040701c1c10020071b5160f1425040c62810220318000340e9041050150041c45007076000815541c400c000c41c68001282ea80d003245010780500740300c0702c1034114411448a08000c136000d402807090400305460501c90b80990310700303000c120f8160032400c036003800803000002d1030220201220f0151500560840d8401c02c4128451403c0000030380000c4c1900c150100305009110000d100c82104040310300c001c00581c9000f035000d08400b1410302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 615649982 1250 615648732 615648763
    0x22206051804050f22050d050408011d0c060c010f1109150309032a12041505040f0b03071206080606040e15040206030703060f080601030c0e070804030c02150c0d030b03010b0102 78
    0x81031a01500411902d170400d89521004030344007100800c034050305a41091068164560901084c0220880d184200241085141e0004c00442c895003040006942226130101d42d650f60f02c9158541c0710981e80280c54022180000c4165940c09000a00c06030494240c055075913420104180481d82000004a520001c080b040ca49005510384008560603401c00070448241d12461100d403002d0140c02c4010306c2142d0407402103840034034018900703807080c4c0280e03c1800040c020b600e500b0003003640d2407401540e200007185007990000781c0c0058400125007a5070468005035004e2410041c05080502c00c00c4100c15442c3d009108024034003041b801c0b4018014802409150088041892640281c100038041e04d0030b0101005442d4480400c155038400034030003a600403603451400250381e40e501c015940102003955030200c40c3c1c1e0300e907242a140304034400c5080f0703040a0240c400016402c8900058032251144030082c051905021030001c0940341c00c4100340e0310030b03450004040810303a000140340f411100c016 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 615651232 1250 615649982 615650011
    0x1202090a0b03010906060503070510080c130f03061b05160215090a060c02210607080907030b010801090c0f060c0201030f0e150f07021906022206051804050f 69
    0x35403403a010380044100d81d6015030070720407190104422034001c90107980d002d42c100c0e510309690384208460008858110404100790b003001ca204130b01800700038151a580c4e5043e12000c00e60710700d160325860f50315600c16100d16690714021080c0c45a2400b10403003d00980c5082d60070301e0f941700703d19101041008002071040c489249151601003d5105440300c0e554010590b04074a940d500000c0c0c141038003100c1c12481200c0f010000094091000700421030350160000824495070707041c405503140000a080c210661081c418000f0014001404260280200000108070030b60f10740b41c181d2402204d42c0042000c030410b020184035259101c0d51141d441b980901e00840d44454140d0f4010091042500000c0d42d0b024608442c1d400038900e9105030f00520181000d82015036a007c412601d98010344c0c00280d284141c282c5010216105401a00040d800c84040002008400c2401c040c4040583d12510100d48045600c04011004030404204c20605a8080c051890142c4220050603001800d11a82d604207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 615652482 1250 615651232 615651241
    0x7050d020a0c0b091b1009031e050318040f0b0310021606050a0b030f0304080d08092407030b030307021302071e0813080f1f1404110306070801120209 66
    0x1203910145040d000107000c07503039052190449465010017407120b01003041c0200000464106220761031182034a40d514501c220f800c0d42d60b81180300700d1900007403002c0c85004030b40c2070100d481030008204241d001c505804010011905000555404a0011089610741011540c850310089851148950004c600507581d4024031034143c04804643c1c005401d4034030305010882c48608503800142510300c11011135404400701481640e40344618003500b94190072940036401c49500038094590400d200d80d0513036852141c0c00b11820440d40140001000070311040052060958251090507583c410030b401452404400d078011403998080c0c095100c10003640042c03520184018420742044200c0140030391038075664039003013041d903d4000328400c004084983d1400a0b00100000e500d404000f40343c00036207007078007000448182051801d00030800054840d00c491840c6010803020f50302c12849521800d0020000d007042c1441d000c0010400d40a004400c0d0046c4141c880f03c83e0066000d5a045070340c55140d035103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 615653732 1250 615652482 615652487
    0xa1b0b18012405030705060c0c1005090d0b101203140a030603080d0903080f0403020a1725170405150703051e0c011505010516020409050a0c060e0907050d020a 70
    0x1d10b50184540e50300c0081110744900c2e4459150411114110120340407039480d8010045544140d880c0b40e0425800340b903407041c0b10706083c1204a070800705424440d00b0000300708085074000180ea0021203007030823000c00b0821042020102d003000342c8030744805142031864a41e0060301622519125080c424000710341c40880d28402c4c0c220b18080c5501c00381e03443d21025100120009003d50003030440100305004006403100d240300085a03c6075805070300074220b0103910b88544503a54440740350a0120b2004100554035040349541070710a2a40e001000614072559040c9050596074140c41103c14880800c42040140d40b91004d041403405110111030360f0b88554038041d511445040690300301d5216906d002d10404030703054080c1c64118060030003404954881100c40d001921903001d0307180818000d01012910883d648106141c661001d0030003c1c0000e010b4450500d0500030b132000b00c80607103e029086c0105c03640a5208420000c0694041c2d0072810300788406456400345201010a0396408144220003d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 615654982 1250 615653732 615653741
    0x90f04110d060e15010c0b010605340213090209181606091403011b2f0616030b010f0c1a0a15062313031203020a1b0b1801 54
    0x15006007003080300b103a54000254000b03004980d80c3c582c001340244440402d500504481c14400d034040c44500e580da080c80e4054130240c209415415440500c10b0700c012614000f004e00004004419040d80d0f0f00f8103c0e407041220f52225110301c1110b09060111030300c0140c4460070101c1e0024204a446416809850a102c0c80d00d8403240001c61450028000000c2e003d40113000341c0261089074040891000c5444240741c00d0310f070800301c01042c2681c84040121068421100f070512501d0084502401d209015285100404c54a0800c0384a801c0345090100106c0c0607114030901c01141c0c101801035000640020303050244004c12442844000104c0c281040440c0c44003103041c5200d41507002142c241031015100416070084008101c410000c004161140200c0030500382c800034403411030b40c892110f07181c0481c1c1d82088450303039151400c0403404030001318000c2103115860a01e540050b110003035404010008003683c2104144103056a80b04004501030346800c5a200c03008402e030228441d1907030308050040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 615656232 1250 615654982 615654997
    0xd020d03050f040e07450305071d09070e040b070915020a02010306080705090a020f2b1a03030d05070e0303040305070801241404110304061d0102090f0411 68
    0xb50000070080344400764003004038060107182d962807031072079800c40361800403000340107030192070a12102c17a00c848034041501070441e1480284141c11055565603d6520313109954200b90325070b1518030700c9448059489800f00e68040030350402420401d20344180199a0300000d0005069050a080014485402540720500820b0308881c100c0c450384213560004d49030300d90602c0490001e82841800600d030706000900b14103554005040240c00e440e10400034000350700a920721700c144241480f10b1750410060310aa00ba10001d042c46500d0381da145508580121a5008c00483c001882d0080540700e0b9100001552002d00703440c54005240d46402c0303010b840810080f0703d2140e0500c1300080c00300030481c0c04240f05c0700301c80e0b20348002c3c800500070321b444405040030400660300a00740003c04000c800c0003c0162001c640002d0300000b08030049041c40003056008590688000d602d441d0440364021002885034800786030380c4002c60414101000080350008007041c000d10590b02c0300c01e6202c48083ca107040740d031036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 615657482 1250 615656232 615656257
    0xf0a110307180f0320010206090d120603060c110c010c0f02011b050105090d02061005030604030f031104091b020105010b0301150e0405040b01060212090a21050d0e1306050d020d0305 80
    0x4182e50b171400740c1c4552102002c82803500e001c00010140f55000013410303809100e420014144195000b842219541c0a0740d04983c800c0ba1a44000404038070a407080c500c03040080c0e42c82d075042540200c40703949400034606040781041445001c8001055229040a1603d942440c5c00394110700341036400c40346401e030500c01038501e5280505016402600140031000c101540e025200705940d50fa8000e002c1c0c81091141a4154020380005030000384180340a0018174000d050002d1103420b609a07105407a085030300211000b41e554603c02070301c11a0306041d080c21000c1403000b44103070341c14100804064001845500030f48080f03c070f4000645401403d208440e080c01030420000c070b16003420300c60f0f41c0200070320985025004900d6000d0481042408644800b03102400390000186001c064064001560044a550b00c0600c0c100800003581402043c8400f4010354540340702c5507128041148503c424000311040900d0180100426110511454040307601110001181d01080c10151340c01c0c892a03004290 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 615658732 1250 615657482 615657509
    0x12060108130b240f0a0504020918270316030e0d061401030218130201230c070609050103150b0c070e0f04031b03082404020c0102030f0a11030718 64
    0x140000301d410f0118006041081070b0f150000d02000b4041c42092000741e140d0881d540010501042c01c05400900746210087e2004d40d020702c01040325031518000f91000c40e10044402ca00d000851491103014040142400c0610700d841a12841042d01a10b206801828808000403c01060341c4010803040b0842c0c0020051040303400ea04011040e8084c00d0004074401d08050362801581b0b0494100c99129507180c1841d83c1880e1050740042d100c030b21004411400d88034002c8042140880110094030780d0710241c0c002400c0c49420507a004d0010805500494105490584680310349911541c1d50401c64806400c0d00d55150000c0c2e030003500b0614035030405807801c003183c0d00b4031503807506031842c29129901135582e595611070500462804043c0c8814064005110b050110f4a06804ca8059903156000b0b02203c54029003090045016070b00305401d1149140d6000c8104510001001e502580c0300b451102d0800032244408450b810500003c0c00e00b000f003010b4809810b01e065100d2900401a1454482800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 615659982 1250 615658732 615658741
    0x708191404021003050603120705030d3e07031202040504111b0604030804120c1401090309080601031703070203040801021306020c0f0312070f0c09150b12060108130b 73
    0x121244161401c0b40160600044488118402d00c1446d0003124020050000304614404281140d00421010b4a150200308040c4450384007910a0722600309008894500104c0c50484540e004800b2064174500c10341c0081c52150712105c075004554107640d0600307140404159200602c0024000d81e000310780c0003482d05082c2481c600c013403070242200007003140f110364064407540602c6440f5031040c0c0740240031440c3e040100740001e05150207501070115919001c0340aa41d5030f150290381c40e08125000e800ca9555403408018140d0109115024215120041009504d9603980d01400124040015084c42001c4003244066100384121001054034000941d120000c044030600142c1007846480050300c0b81425810b410b0610717991a0f07440c21002005448211440d500b09c103881e601642c0e048400006a204810005401070b0940019042c4d401c0000703002411000f520760152019088008803030800d114440c0d442c070355106442d51083e028a80620184c848030300c40700c000c1a21590080c4095141004c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 615661232 1250 615659982 615660011
    0x1020d2f0c19050a0302010e13111305150307030203100b03191b0e040b0a0909051513050a032a0b101d010504020a05130308030702120909070819 64
    0x401c0120086501002c2e07800c116110344080c41c0548606504a08042c404101642c040c0c03400d0780700100301801c0c7e100c1104100010404403140500c00780303000366001ca40c40c0040c4c1e004800724400303400240d0340c2605500e00c0180207000c2e4000107000004042d000800200110a030368804070007010141645a240d0900081c03210141941d0040d0b90b4140c3e103004210148195008526014502e27213844000d03d111185081c44003401050401907000304400c1c400082a0015100c0c510615028202404001c0170349800042c100303001a02c440c140b40c00780c940b0000480c2c5e021951480030382c0c1c9400c0540c16511642100e0840300c01032002d0038090b0030220071080901450b2100f451091050032400345030381c4c0e00c91401300000c3c02d43c42640c20890a0030001804142440e034014580940281031950800c410320000000d1030401c0c1d0011141c100e400b0080c4144590100410540505040c032014101221240072a81c0d1640c0280700b58200700e02880414051000c0e540421003215058400b40150a0105e01c1f5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 615662482 1250 615661232 615661243
    0xf0c0a06180f20030a03170a050c0d0203070e1c020405060901080a06020c0307050102040f031104060e0a050a090c061d0604060509090403020c041503020f0406030201020d2f 76
    0x369005410400c2490300c080900c038500070709660090031041d4a41003070b101c5800141c180c440c5042d5514004000940503079040111514141c480d60740c0009205e4582080000100c02800c0c8281d041d04041c144103041480302e05031003030034110040040e03c82d03071030b944101d808242c0c0e411202e410400b25410400316a80d1407800320600750082d101405144c4455041c0074a0705000d00c164074441d041030350303841c000a0f66500201b8070020001d003200d0400785103480e0642261b100c2ea0002165400070317001042000039460050403941d034100c1d404c110303643c40c00d03841f40c42c0e5030801410141100c2e40c8000242e4070303142d03aa000d08041a080503240c02c1c1070303032291800381511a880d00c0c0c1b07014901031341c59404404c0ca040707012a0241e60060b50752a09204540742440007a00c0050002c50a42c001c00c612013190f62100d02c141681da224541181c803100303245006024524001b800300c24056400c0c60000e00150b41c0004504880c030741540741003040c0755200101421840001c10000345201301000034500c400100091 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 615663732 1250 615662482 615662503
    0xa0e0702211306111e19031e050a09080307080702130222050406090e1c050f0309071403010e06160306051201050403080c18150c0607021b04060e0c0f0f0c 68
    0x89484401c2d108201d0341004100c44001d251aa00c2103608003902d4818030311b65022244241050350b42c1e80c1460805c00014242c4c8a04d090001d4404070f940210301c0c0d485001c034002088444080c1d454401c0c41d03220b010141c0700340c07017004e0b010392485000b1003545400c942c11241c1404c0c00725004560300c40c503002081d0314036001e44a40c40c4214100000854040c409210f81802ca805080040240003030844040d0b1541c8000d00c03d501c10b10009101c405044400d4800941c1300d481801d0150400342d003000c44900014020030700070342c007903807411541009071900021841c1e008098011280d40010303044104a02070100c5402c40c039000421415081c14a1b00305401590107580309888603119942d41480080f024011040d01568662210800a44d00c2c20019101d007551840c0740b44031881d05490300340380c0346000800ea80150050388082030710b0581044200c50201c1d03454082354280315a903d000c408115a09014201d502001c2000452444152541c0c0803100c80158810640d03456442c1d00c20b406464400b40b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 615664982 1250 615663732 615663767
    0x1d2809030e0604050a122a1509180f062c01051507060504083a0501140616060e0d030f05010302150304060902030106140a0e0702211306 60
    0x40507042442c01400741d41c142d41003d000c0003512840d19142c2810040c079013900f512940d21f12500100341244600c07859101000d00000080d0240c40d1007a0551031341e81c00158a42000040301040c480f200041040244941d10b030400401d0b030f0007070202054001d01e10b82d4800350b14960440499960342100d41c0c4510080100000141d0f1a07a0340c0da1b09006076020b105071005015002040b01c1d40014000360702503a04603001d00410381c1460282d2041a03103c1c4220121114280c4003444c0400701d82c07580b80c031800041c030b44041c0240705551400c3c2c03141403035036055802e99104401c08220606c07402d21090105c554076030040024481220301d103c490351240c003828001d00029047c5000701916203454000e441c1240e5028207880080500c0003e5201581c00180084406544800501000da40c003402040f02034104440040a0340217003c080219680e0700f03500925824141d48100039403540c0103c2d0181c5000308035030302c4120055070301014800522030382c2a0409812510100840c03442d9201c4140990429001e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 615666232 1250 615664982 615664997
    0x309050c19031a0903220b130302133c11090909070305150619141002070e06010806220902131509020c0102040801020c010b01181d280903 61
    0x4070400e03c0108801c0350407055503442080312401c4824800300b40c6454549149070140c039907445808070300150307011081680d80d880c1800c1c014011352920a08030031401c4000c8808200d07181071580c04401145070280740400812401210102808a4080a07005407200842c100b0034109521048006034100103406400b42c504040040c200f41c03000260170707003a00d030040000c1a0301c0303141d081c0242d41351f240201904d03003000b48900803449c890301d10329074240a06060400d08020160340010f1042e17981c645401001154080745080118a003510040c2c1c1e040b00080c03800b070b4955511800460034404428618142d41080010b44004e40e0b0348030b9100e016528800c80d00e6043c1030100181000c242d03819661b01401c12841184204041d50b0564000e2002c507480400241c10f05603102046070890300f05036116501030b5110341c00c00c8a0756074000090b6200780c07092941602d0f0f442c1002102e070b1203094070b4100202e1001070300d80071a0800c01c49010540c09410f20300c0550300000440c1c1e00050103450141d0f0220040b0340107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 615667482 1250 615666232 615666263
    0x1a19050918010c1403041101030b03150712020f0306041a090907031101110d0f02010b1305040b010b070c030809010203040e07050c3702131d0c0607080a0309050c1903 73
    0x13580c0c40c1400d280c4041e64160841d112a102c1c0007000b120043c105040c9552103048095a48040c441515444203141004040d40f8014202034202d040814640c0400d0340304000d0718450b02025815660080e0b410b49000411108840ca1a00205940007035150b02401070300402058480004480d415684200e0280c01c44501c07020040d5600340710091a00e4030b81d04003400c0110707018464003503a0207000301ca1002160504503480490707903880d045500c3c1c01d4042e482d00100018001c0c034000d00b9006040c0036000a20b042c655486a6050720740c18000180502c1001031000e05a81c405c100303603070181000300c2000f01383d42007140f000781c2240c2c8008021f40e82401014490903140c1a546400e00112034944107007400c9a0140c62030642203590078400700d90007031845105500a02c80351140ca0707030303103124031f2006400030390000d15003490007651141c440d100f0101000340600007100d140a03524042460300300811503180901c2e0450030840001406900900e00c20030a0045189640244d0100c038041c12450042540 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 615668732 1250 615667482 615667487
    0xf0f0f060f020f03040303090201020a061a0913050303042604151107230105041d0709171203040f150b0a0609050a030b070912080a030f1a19050918010c 67
    0x14112030f90f4615205000080200e4040d400450540d4414815210410101e540f03190444004031071041e00051881189402d03030518061460b0030245290110100d04601d81d1060b5480c4801000204011400243c0d10071406080c0118482d901d114041c0c81c0d142e0340c8136040f40003c0482c03100f44c02c0c0041c1071045004003850010900c0d800b90f030301600294510794020030b00c135090020a40020f60400c50108400078030ba020115498086400c2407080c40240d003055a00101100040d401c45c6240328006180303c0000031000585010210340003030100c1d00c80c2c0d2182490b0304014100365020340308054070100901111001d92000d02000b004503412104141c682408440c4013109014851b0482d19800027400464001e50889074009400e1502e5600d080c0c5600c51107040555002c0300700c901d04004501d4441e49500760182001fa1416008100010a038110b041c46403d03295030784507402018000c074070720410f01c9400302c5c00000e0310300039020880034180103404025541480f0301501c1079510307103180f41c05c2c11071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 615669982 1250 615668732 615668737
    0x3050d05011e030303050c0c01061d18030a030902040b180105090a020a0206041b120f0221100e2d0f06041a091504050604031701051c0f0f0f060f02 65
    0x340b02d10100c11850459034103400805000d40300c03181518040c401a880d10000340104c1001e050100c0c5c3c9840e001a0b00d03001101c180802410920741c50004005000d40e040d4000141d401d40801e600d00484c400d1000c0c0089401000402c011640160500000180346c0781400c248a048400a40e00e4442c2603a071098160120b004445091005800c910041800306003c001d8150010900303c4d404014142e65440e500c00f0304044d039900b1120140b80b190341105500c1c0a040c200118081000c1c80b12a1400503400161a40e4010700c00b4a466035503852044860b80c02000809403c0340054145036001048400c80000790310b41d00c65000b07942c45000b003100340b1201e0204e0424011a40030300302c0901d0344110120b0310103411b0000d03d562414850b00340e10f02a1640c40b0040907005502030b00180013607041a0400910442c0b4404207140c1a94004004002c207403035101058404450300c446d0004051558940086962145440034204804140c5008280032000681ea49081c6c480c2e001040340380751400c2400180d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 615671232 1250 615669982 615670019
    0xa0803090d0219170604060b10210e060108030c070506070305160f02090103030c1b0308031311030f070e070201050f04060e0312070302131a03041202031603050d0501 73
    0x4100c0c04507070060904115540c014203100000d03d84043d120580c070180030850881004959208030148000c0c014144038207480e0000c103076081c1c55000400710028040340002c100c4030402e00c0280c0201c44170040306601040c18050218107448041d40d4540340d031035881c2c100281150071802050b000069525103c000c442c000e07503040d121941400d40c2c00a00c04400d940b8280300740c42032412047d1090040c0d45022240c0e003e140f02e5242c0a14041b40d60801112809694045001101e8100703400c0c40412032800a8907840300481c140c0c1000d1644a103040300680011003025501881500100d204024000c50008140d820640d80a01c9a68880c64200c1c00c1e2101038400c0704050703003484007103000b040558100b10004080380040f6441c00c6100804407410000495100000a0707000c50810300c65800079590b03074010165036a0820703008007000c01c040300703510001d070000f0301580c0c0e42d01003410164000c0c4140d560a5500503041044400300b41070250259100c1200d171505589001d00110b0700800d5441c51081a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 615672482 1250 615671232 615671239
    0xe1501060e0405100b0f0d0e030a080f070c350a020d09060e040b0d150e1605130506030a0506010f0305070e0705090111031c060806220f0309050a0305010b0a080309 72
    0x2c2c41d280c20038a105c2a40200500b031541c04040040f030b0200962130149801c901d902000656075038182ca40010003071407014004000401c0d815090103411a84160303151a80ca800c1350641070303069580d0303a805220034070160350003611030841140c92107600c41e140050124640150280d0b005080d00b4481118a2030313042c0a2040440c288110184c8107003000d030f01c20038100d0300c0644241d2035680e15481e4030b4840915880380d0f400140c0c851103c4880001c040c0004611842803130b8050125500341070001c0c01b0030a501454200707040d41c03040050b107641d50030840340c02d00c540c01105552141d42c60390400c08004490340000d0344ca0707125020000a0115044861521480ba03d6440c542003c0c0901c0c01103504452400d091400751005101c488126215003c014202080044001440c9031401e0342c803d04020000703046004003e246c900f4140e00c10521740131444481e9114505e41c0d69020146002d5a030000150001074101c06220b002108000e81540707c1400c840003104c4c1d8407100e5603503103111542e83c41200d060540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 615673732 1250 615672482 615672511
    0x1209050a0b22051c06021e0d0e070b0a08060a1a13050a05220e0d02070306050a02120105060a0203360d050d050c0c03010f0501030c1e17010e1501060e0405 68
    0x50a2800c0d0500e95030600c10040589015428941c100e814031f490342c208850741c1d000080003c522042e40c850400c02410001c06070100e2444d010101405020702c0d01490107010070100000c0907a696032444d44040d0101041000d43c03040c4241141d2121381040020007000300849101045600d40442e01c1011500b0050a107642b80b08890b0304040c10484100b400c940c0076840307250610110301c0c14405000b0b0228140c4c01416200d207581030400a44101070310500801f0302c100301003400c21880c0010a07064503000c3e90265662000220f0032403071441031305095100b041d0034910010148607050a107d01804586141d0050070100600300624000070450042c000d81c048103070a03a10901030400780070180d071100103884208016002080c250f03910307404800c07000c80c1e480005204010980804202400403060061504007106490802c50071640c010440c0052a01112025041c0250000801c4524083c140c4a465044405269400c14203003d00404580b00b010202c200d801c0034415144107185031180042e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 615674982 1250 615673732 615673759
    0x1d1b070804061101090507080f010f1505060c1501090510080f06190e070b04151103040909290105010f020c011704080f0f04091104080a1209050a0b2205 67
    0x41d0600010fa2500e4020754036184290702103042840040000e080e1640a010841032810807a421146400c00c3c000945250588600d0111944280c1c2029900b0680740c243c0e5601502180502d058a10080ca60703e104100b0300100300e01010780c103d84d0040d40481402e02940e601e40b0103035a10b4200c1c05422103102e0340710348005640591b800ca0386060314400c00900041040c400034405044c0740441d04100e480c9000018108081400b841c0b48003506030440c03502e078500c00740c680b4802c3d86911562044d580043d07215400e07101440310a0f4411030b400849004520344101d203007018000400c0f800d205450205000800c21005a03002055030701020130140c1d501f0038892082c0080000b25200a001603544000a01079450103116030001459070250f0f5440307898031145000c4101e030a85800813240003d8500074402000f0035880051507140c5140d010300c01c0c1d01c1d61041c5081c1160550301682c05254081d0a110300000c40c0d020b01401407901c0d080304080c03a101c10647c2c5020300e2141141b1301c6002d0b082020704c503091 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 615676232 1250 615674982 615674987
    0x308040b0a0221100e01030f062427020301120803090c0409032a03081513110c07090e0606090c0f070321151a041d1b07080406 56
    0x890703001201403001800c040c04102c0300c400d1514030380c0d5003200c1407401c501403180d511082c0300d032100182840c1815440d20340c1036136581c8100c030410b00302c000c1125460300000c1c00c3c240101c9060030911000300e00042552651640102508018800380603040d002104460000280c14000c40b4180c4114007005410700d0121f61f00d01900703a1005003503520785c2c0500d50541e0303010350303c0c2d01801010b18025030300c0e0050116540d003030140348608000380c050408a030004c0480040d030404801a40103007114003106140760107034085828030540c2070700380d0401464544101d0205c0140c4007d03060300c400c1c1d1821260a1a202c0c0507030703401c82c2c0c407950200380194030503800500c25141050304107a000c01e001d07001c58140b2a88612210703854104802c00c401060030080210f60300314500741d0841c0d000302c03c40c50501c4185400c1404014000041c0280107500f001300c021514599110402c8900900416580c00c010a0503002d084113100020341e44211100a00c801c102ca410040070191178905400002da40e180a14060b4107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 615677482 1250 615676232 615676253
    0x1051005190b0409060e01080633030d080a140144070311060a0c0605070512040c17030a02030904020304020a0b120f0a150b3a0c0c030804 61
    0x1018000c1c5a420300c08074941452901070030040c10543c90108405007404850284190140c011084581c0603a04200042c0c0f0440e0404980c07511051559400904590003803850140512405405204c4c0c0030a41c044164066040b51003200620b10400c01d040c06c2103641c8040c20340030300c80c1f0b01101809120508500081c5c880070041031025441d001030707401d44952080040b00390b0904c01581c50300060001c00902020400d40409018101d40c1c0a140c02d114100260004281c2d010291980c0e56400007c1e040c0c41c000e000311440d61441401144c1546414686030407000c9030350248800000400000c0c0c0e0101ea030010681c2d241c080280c0145040045003010300000b50402013080c1d0748010201e80004a030522180180140c003010b0312200011b1030409403100c0c1461020380b203007010b2480c000060201c0f249694201c016a03226004da00c4d62180a1039400c040c1210714004000c44101c5500c2c0c00c0302080441c100c3e0140b100000c403050019050520060f2508402000041c000c030f85a58005000203410b1000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 615678732 1250 615677482 615677509
    0x8010807141908160816050d0b040809060c010e0114010b12070309020a09092d20060c0703050d08040c061803140c09010509010b190c0b040f03030e01051005 69
    0x30160b14071940c61100340c0c6460307181182c98880f4814000140010a020300031400a4000e00c10307040310b105c0c5130101050702044602006044600b030030012408212480f41180d46600000f80741640354000a0b01e62802001c8030100522190305c4c040c00148803a000702340c2c440c100c454001440b400d003201c06801200f1080001e210000b050ba440d10030354016654442408003600314400002003001d1181b41c40b03481449019080490210480d10480901100c9101c0c00071465204003803006400c0c410f400c0b518042c07044026198400000300311800904400075180c0110f9003d0b00c101d42c40740080407000d5989810a0320094000142c8890a104d00c90245000d0700340c1e119019051007441c1d5803500c6e08020040004174802c015004140e2198081c41c25030b0515014007400c07143c4501c01d51420048aa00e40b284900c2c0c030000d800c0c0120b084007014094000b150010ba0800800d4080745490700e00110b991a0745082140801e10701045074042900c141b01e62803007a050288140310103420702c820481c1c0c0300b04204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 615679982 1250 615678732 615678769
    0xa18051f0c06230a0b010e1309111201020c1506010f0c033b031204030b0c040801050a0507141215041d06060301061a04091107120f0801080714 63
    0x6030f00301004040100058484042510203030102d08040c0303054403e440500015504000049149613a281c1d50000c803411440140007000030f1014486c50903104113440c1464199000c1d90a462584840c1e030190000e0902d840300c0317825982c4920400100e031103001416034109001440c814000c030b22260084584070b44003402803c0424031080e0b1071800c00030650709120900441c1a0308080103032161003060b1a0150024100e028203881036034003128240a028501c40641002c10b101c02282c0c1003040c2c90102d5010b041144001e000f1850400c10b010041c0c542514031000066a854407020540c99a0054805100c0c52040090854492203071102140c04108401179109542d2565840c203152812041c1c803040e9102405000b2600c0d142c010103003184c00b83e47c0495109004001d006080b2110407007201c0c00ea6515400000ea00103500c007100c00b0a0043d11001060040c00d60f0000c00d205810418842d00000c03980d87d0040f4030382e01c030214645c503050750344550007200d03102e011070307480b10b26000d102c2003095003060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 615681232 1250 615679982 615679991
    0xf03060d02060304060b010f0504050607120302041d09191e051f051f15180504050703141f03030309050a1a0708070f090506090a08030a18051f0c06 65
    0x70340015103558800d690860300c2c00d59034000001da07540c120420105094541c00c5c41414a0718000100f603440c82401c800510721000d142100d0708860003541901c000e401e459075001072610b421045000d0840c07050381d03a0070980c442c1c4141f80da40540e4202d1a0010300740c0c480c1c101c443e0211545022031403400c2080e006c4505000c2c48038810450100c2074010700360004c908202240d0b40c20240c3e50003d040d0080b000507a0b50a8541e601030103907040c2a684491082030a290244a904a4031120b24034070015801055015003840c05220400c1e502d0f40100000000f503c1c0f4811541e219041070141c1071520107001d50501c14500700400100c0c0c0aa40603281e001d0142042d640641810343d6100004e0b140710301461000319441040c082d4071940301300200d500c0a100c1c14a1210a0000040545216001e00c0b41c90300c80c1c00c0001390080c8503100c1c40b401c90000c0c282d00044a0322545030000103031402d1034180c0100400300f1038480c0003411b1702e840c1d02a1402180018101d48641c2c130b03440340480b0014074406c0103031529038a8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 615682482 1250 615681232 615681259
    0xe010f150e03341406040303110c0307031a0a1401230a0608010626010308030402030a050f3306040b0607080a021e0d0906180b0c0703060c0c080f0306 66
    0x149000169024007108090620445076032003030f10b8a042030b00402c1c9008125038481c03605459040444058a0309030820351961090645a03a1410511840a40d014010200004200f104645480c80c0c4200500110102503858982550442d0000d204060881c01d9000042280340b5400c1650303040d50b03001007010000c0021440204008424a604c481c000406030390040048961000d015107105d44412550303008009540c0a0000022040c04040c002c0100040403c0071503a00704035086510740c1c80401c0c0c0d00f00b4614040c10700d881d2402c801c201820702940083c041d01c0078881500b2000120844039440f00a5240c00003400000c0850b505e465070007210820550b00819001c0010b002c4950f941e034010321071480c049181d04408494080c101d42c055014031200030f5490f4121002405072507461074044029a00381d54420503812245d031128080e51000502c540000c2d401041c00c1007501d0281c0d0061002c0606148102c8e1190203207a0080e02d1018203204003102d49c00c400c0e00235500310000030840720480d0603 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 615683732 1250 615682482 615682513
    0x110403020a030804050102160f0b1c050f010303080601020f1203150d11010912110f0102210706050106051306050c0a17120702120a05070c1706010e010f150e03 70
    0x2450b081079070b0f4124007180401c403d6904008400c03110700303440d0b258190203182c905507006079102801024400312001c01d81096190800c1010100000849418010741c2030985141405007000e0000b030700000e40502c0050719a50002421300c81258403500100345040160000b1308682e0030240c000b103070444195011105554030380128580c0740d40a2400d20780a000c0d5940050a0b02102d503102d025408007038028600400c9170080b602840304070a95104282000c120700407400e00c030b02407010100652080c8103c102c1c3c10b0408000d0040303d88180f1013081503981f0741c402603a490003001001d9050f070310b03500300c28002280b01d40e02038508250600101d911b141c807250ba071804100c4a4440341c11004002003030a40800200e010740719040f410038005410195411420300d1070f5480340882c1c20f030601a00043c030f0380c108942d030350100f0300070114050a041480d0601e0720141c0c81d420284101c0d544104500d0001c03410700101c0610b0001c0381c620b514001d03d00000244151040c081005040b030f0f041c090f44282840442 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 615684982 1250 615683732 615683749
    0x40803040305030301060206070e010e040f060509101e05091801090605070503041b030510180b0403020a02090703050108030d0e0319090815130b090304081b010e010513060311040302 80
    0x5201d6400f46442e0f6042841c020f19200c402840300081109407003d0302c0c15030340c0000e07032003a000009031000305103201215030000c081c0071603a001da5003201a4a041280080c140c1c41c42c807081d030756400e07040100c0105400e510880d410090150681c0301c405a40816080c03584035200c02c2940c10b6450022404c0c11964a59608690080f030352132010440000400007080300011540800000751450303ca0285e086840d00c40e5280ca05210019844d03a039042848a0b654500061501c01680016035450528207480c000707444001c1034404a00681488000c2070039107000c0d00440b4140c860000041d030030003140c0d8411a014042d070300c0c0701d01d451340410041c52407a011b0300821090304411075141c207528540740000a918000c1d510781c16055440d4444140411105218078420085030412410340d0182c40b0685107500f180301d07680c050016445200b189843d81900710b10040c120709001d81782c1562565003400152068030680d200702980740e45481080c0300342400780c0d200c80001e80d44036070418182600c940c0403a0000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 615686232 1250 615684982 615684989
    0x91a090106050a15080109051b0723060903091005090306070c150b01050f0a0203090a0306060f060305010e060d050c030304030b22031409040b04050109090210050306130e0304080304 80
    0x40c0d4480005000d28200801000700500801c40d1010700e003a6080c3c00100651011b008400503103850f14041686000705001c9a010140940c032100d6441400346025032076003450360744191800c40c00c00110030f6070010200340e103482003d08102852800403281c0c104400c09084240007414400305201d4911942c500704681e030700c09d0002c0d8035000e001c106103050213104918050000006a0705102c0907041d00c1c0da000302a40d480e030300801c80c05030711140f00e054140d0940c080c074101180c000b19198030000522034240c100400b25004c050b04c400c0351944600b0100c00707841d4240100403081c2c1c80c9901141080c24a1440040c031a401241070324a000c01701400030f411036116030700c2500e199071140d00340301c010803108909004c8c0c1d0040c01200705400c40d03243e802400540d400c43d0110014240400c0e2443c5a0711079800400702c071000100104a00d60715402580300a080100044e405110024030140301035000b2812223008440007050385e580c0c400015080300140148405424140c0014400040d070207404202501c0a03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 615687482 1250 615686232 615686251
    0x50309120c12030f0d0c2d030e010c0c0305071703100911070f0f05010b03030415110705010807120e0d0c05060a2a02030702030102070b011d040f08030c0c070906150507080d091a 78
    0x20100c7c20700009041d1107a8201055450345085003141c0801c0e042003e0030540da5041c1445078440c8114146111030a041034080f800300080001041080f218480085003a54291542000407024100380300b0303460301854400400009500030703548041411306d00f2503c3c215202d00c0c0042003040d0054003081c11504143e000c003030598102891075511980141024010b908010010b1031500d19100000b002c0741c0d8044c100400384503a96084048003a070329085440b10000c0207048500c0c2c81c0e00d0b010002d0000074030a009941c940241c802188100002d80a07001011501500b01c0f803842e19070710080c641c01020005404e0a51100300022001614203001400b405801149040c010758500349041c11780c100080d56203003803c0340740001c0000145100c840342111135040f08116449650380c0d0fa1102051040a210050910519a000900260907048841910400c04100c2848140028281d540d40241321f4020324044080c04111640d00055100520b0715005181d1000301041c186580031510300c0540300c0c03405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 615688732 1250 615687482 615687557
    0x40e131703072304060f2d08070806030c04110c01181109190f061706070212040302010207030f02061e030106020c09061c050309120c12030f0d0c 64
    0x32202d40010341d46404a180f07400c50b640101030449030b03080368880c1e80030384c43c28000c0c180681400d0612a0880030f1005202000400c160841ca08490780002c42d5a4641d000080061000450903441850283d018000250080004114440c20000603142808046110740c2081c450810400310074014981c00b000d18a500d112101c949040c40340340141c000c0d4010740030308024014031030341761180281d91b0102004258000b034140c4640301e4a10140500c1d138490007943e020f589440490000218405020340c4032138007210782e61560194414110f009038070002e8096044490100301188006038005440c0e84000c10140c501950700007992500401c80c50400d584038030200c014040d003074042010200d0030307034112007070280352500b03200048444142c50224088400d44a490340e04110040054540d5160001c2200030b81d02c00402c0460380c1c41080704086482125004140e16228002008441c413040c0c0b0501c5141c42c0581070f00141d406000c10600300c0c802c00c46d030642942d00fa0f00c0708800452940058546c0402e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 615689982 1250 615688732 615688741
    0x6040204080a231204230603010b09130501080c090106030b13050c040b030702030a020f060f011203030e01020d0e060f0105010906052203030807031524020c03030a03150803070503040e131703 84
    0x80c1e00f4500c0c2032003141c6040030040c101b00142d9a86082d2411100200c114540d644e102c40d011908410781c0c02c003007091071403c0000101d407000340841e4101c0b00301001d880f10711403a80d991780c04605071a0104100e41c0c000c241381101016200d13164100a031700002c112800c0f840c2c280e8030000407040d0340c81103900d0401a0000302e00103030066414040541c5118000008000c61308002c2c070340040014040c400d0400309030040e0098020103001e600112490810380000315103a500300d81e05030b0054050562180700718040c0c40d0015110088040d40d19040c0c50040c2d45005440341000d109480d55400820042c151401c13003002050700494000648001c1c40c426903c00c103260030000c5015054850f482400ca02821072440280062074015051001240c0c0a18140f595198440c03001e174100115503200e9078142c040014195903042e015080020004595031217403506179560341d8a42d0700c038007a403c0001d000b5003040108021008034010011f81058600c0250400c1005030350300c0d100d030b00c0103101c40380c0404d140c08001c11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 615691232 1250 615689982 615689999
    0x1a1c050a0c1d09031902150109201804021605060c0d050c090f040c0905060c16061e20010515010305091209150c030d021206040204080a231204 63
    0x80e07204405591a03881d030704020303843c1c94403805180c01d130103401004d0380c48000003180300300464694201402e0803405c0958541c4d01c02030241c543e10201c0c1442e0f00c1280d210310312509201044400031421450021024403c040800c0003075030220360300035103040e03407a416080032035800c3c000e86010b00c18803510655500444d91681c400d94034001c00340480c50901380312424950300c90b0206120840c500f16000501c8880e0010103950940840e0040b0b40c12030800b15881b0a48140018402010601c1140d40c0c3d020941e40c03281100c00807080c0c00032507844040703c0030449910303018a01481c0c0303200744204484543d00c40000d10508444c0111600582c0040a803440c4085580610403d500040000040d01c6040540342c0e030400203229600c1454069140c0c0c0c1004d043c0c00c465071069588400e802420341c1d540c1c41990301000081c2d00910340d0b001442c0c0b1a4000710380c01e4030b4103200b101c04407a8010f001e000003040545910301c0e01c40e904111004000e001085810f1707580300521040003029807034003d06403a1400d01090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 615692482 1250 615691232 615691259
    0x40201021e03121008012d05010b16080d09110117060d03081b2107090f06030903020f030c1f09230106051807030506041a1c050a0c 58
    0x14000c8400c4404001d030340c000008400c80b4012084078002100e0354403900381e08403200701a940150b829501e01440c50002c60950809007078601a540c02d41500e006141e00c4032004c5810030301ca280901c06c410018804481c0805244c10003140c0500061404e04410307081c103a0a40f000e002085030b00483c401884205c41da0000c0c140c281d41d20f5801d084082610f0314001050248454050103414040700c00c0c00a103144190350803110600c9054454240c81d0741c3d480d024000d0389601d0705d181c11405480a000113060a02c81e8600008548040e0b0710540c0480c0346c90001d50007070000e11420303021801200142e400f0a10100010f020f140d0829008041603040050b50002858045002c80111400c0880c0380c00880c41a100d4103c0d189618254071800b248502c288a0040160380d10080d00021186900103052403800611407103180c10792000d20003551030030204021510800d0709815441030140c0c9124090400d07040d28290310464000541d01982c03103490741841c1030740e01a000c803505134203031205106200c2011072 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 615693732 1250 615692482 615692503
    0x160c15090302130e060a0b0316080604050f0f0312040206090a14042019110a030314220803060a05030102030a2c060c070609060e07090c0906020a020d1103031204020102 74
    0x8040120070181e1100c130740c45840c00382c0789402940e2281349420240c2e83c1801000e00217a182442c03100c203a9507406489440d0101128152107a000301010880030b500049086040480f0a0015501d4414121010282d0f100b024005980144041c04048000c0d00d68015880190030041058440540344034100010307118800500b19491a010301002c12000c441d505552a01d14038028900050804000442e1403030100c0050711001c0c440d00e1200e106043d09036004510250781d0b10f0030700c1d4569403040c02940c10a83d08a4203070029208440c051008103803084003650300a9070007010642510b980d88002400da810503a1b10800e001c0d03403038002503141402a0070042c01c0107606501952503403040081d041d01c541008290111036040090382d401003050990114201c5540000301704012810180c80503070701c41e41030142c2031072140381c8240101c00e9400f54181c0d0f41260350a90081c94800c06550900400246050781101d00360700c110007080791540e051024140c1140001c5480740c89241030300009150008888 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 615694982 1250 615693732 615693769
    0x1003020a060c150c02010905060a0902010e010e090a05060f12011401090506090112080904230a0536010203010305030d1407080a0c020f070b040f1a160c15090302 71
    0x42e01e076000411a400303540c3c464001c1d2000181d04400f03800203038090800e0300c1005000d402180204160104594841c8040300d000703076140c103010328228005441d000b0207001000d6200d465400011000000c5400080d0b0105001e80b0405019041c0b03c0401c5540700c060941800d2651550500300309840e25401650040154500074003950500d1400b0542006060080100010802c0002824020300d201200e4050801400405c08850465283d03401c4052160018031000c001c4d60208000b991140600b901502603a0700c642c400904103580c2200c07080040e102903c0040c40000c01c0856a1002e03c0503500030350041025594400d111940c0c8400c031055210040c152603070040511030781c142d020800580c041c2002500142e001c001c0e00c1c2c10707450311060006403030142c4184800031038aa552040070b48111800140a20b00c034640340e4001030000580300d24141954241844000fa4054054200d2205c49005076004013500e0303243d006104640e41d1600b10403004c5106602c0c10011410604141d014503402e58 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 615696232 1250 615694982 615694997
    0x21030d1109010c0b040507031a090f0a0308060d1e0c0f06050408071505120403020f0f0303091c050d0609020417030702030703150b060d0509010e06010303080a1e051003020a06 77
    0x803070018041c41c0200700d01500d4254500001410072004004940144d03800c011000d500f50f501c94401c4000e0350303040702c0940040c0100c0155030354100380060800000c0340e046e103d20f981707a43c4080600a0201d01031405441880c401d40c20f48886900101070701c40e115009489140c646800c0003184000100741c5d03803080d81003120401c01003182080c0410b9100a45058050f01e038200929000221010702030612440d19901e02101440101900003e0210700c060110050300c0d07014024980c165103a010032245034215400840e82e0810128a041f2942c81e0010319091890500d0801e000c1c600c101c4da020380012504a50000d000d10181001d540c40d03145801c0a48001e6203000c030701c0c0c0d021075103d01d1284001081a0206590009040305582202c40d0482c00904442e40766035400e036040c0f024140540f410480ba510f0014416010030000c02c880741640d030940c44480c0d240d2a9582c2c29001003045c1c0e00981c000c49041d42c003030000059103000b2203005d8107003441146041800c40c0100419603941d40e104205203d4071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 615697482 1250 615696232 615696247
    0x180612010e06061e0d062607061407110607211808101e0903080a060f0303021f02070b0f0907061b020f13020f070b01120b0a090221030d11 61
    0x858000200704130901200ca4543c11211002c40180c0395541018601022510325026000503800d040d0742c4d05a180d10449450b84d5071a002962800040c1416180c0c00404216184c003195036220001d03015a0050811483c2181c2516174a2035060321100001d6020440410307a22681c0d4005a071400c510211507600000b0b40c94000140d03640d07004495032800907034450442009503a0030300302c00484400c0444040c050b00030729140c010034020085031603e0031706182c040041106e02416001e00252941900140844010850400343c04080e40c0d00d4540001e400700004c2002071403107000103008103410704c5040c01600703141f0442c0d42000c156402c500104080020805402110b10003991000b0342c064480e251001c0407980401d682841c0c7c0364172040c02500010f400741102c0b03030329070040840c0b40c000c0105001c207988a02c058540d0034103461010341170012680104078860b009030701010b0f00034401490b660080004ae44003443c00a07400c200e655440d007002ca1807500c550841c1c000c20318200164040c02e40f50808 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 615698732 1250 615697482 615697507
    0x906240e0612101503060614040b0301030b1015050c0d171303020a0b090a12030507140f0c1b0111160b0708040e090a0201260408180612010e0606 64
    0x71004112a40c0b220301010598404940b098400a00140c1c040b1103488503921001802600c064070600c000108500b0700c2c80c48080c413480688003070390b04040c0c001d132443c1d10310b442e400101100540185900c0054100004580c15113800355000441252600c036103030b42141e8a80c609100c05e103841c8005104800d644901c03007041c00742d08664448002d94001040da0501c1c00c0c01c03803600342403820040400c150907041c4015040d00040b10305502c0d10401032a00159039003c1c0c103e080d21000d50350356003c60810081401d210403003102621031280d40031310580c00d268003d002c2d51300d48001030922844c03103040000c040076256070100410509811181c001d0407040501a0702c00350103d440e21401c1034800021580740300304055a01110010201d11400302c289062103031440b52641e007100012404034250072840201400802200320b0340314002c001d0b480f0b555503903440c7c5080a034401e0080e01f50340740e080074951880e0303503840700945405411003088001da503050103240e040d51000548114403842007800304400c07002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 615699982 1250 615698732 615698737
    0x601030209131505090706050403050d0c0f021c060b0a050906060f16080a031406060a03090305040801180b070503010b0f1e040306090c05011103041406040906240e06 73
    0x2503064038400d81e25501d5044101c041c00c0c845100500402e0841620350915189400c0395000f01000d2007603d4038103580f40e40c00d485501c5644401040c0350410501018402d0041c5181c070fa082d40621011500240d040c0d00203811200c6007660355070a54030000455003804081e00c1001c2c2026003d8030070101c607030708000c0001c0700c003800145818441d000015070300708003141d4241640c0081039052480140c02c0094a00304085420040200c40002e15184107140307203a00b0308080703d0243e400513003060714004040004601070107072014180d0500c00d0402000410f80c500b445045001c0c100a000100d44050501d000c03282c0c3c140103003000c01000000e10051002c1004c103001c0f6645079029000440d5030304052000741450751501103280346402d801250000c1441500d4000000c05031040c801c102c0803544070401501e0b03014803502c04203820361040c0003d2090701240c61108500c103000516440c1040d550f4200c0c0e100340c07000c0d07403c030120b03040c1c03407810721803031050010156054034806060200b01c88618034007081250 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 615701232 1250 615699982 615699989
    0x51609090b06070516080f0304120312091e140303150108090a170c0d02010c1407060b120309090705070209161e0f0e0f0306150604080a030207050f01110601 69
    0x1035695581c1c0e44440c2d501c1400302c6500315404800d4603000c8841c440340403011811449180224020040400508400030048405660362680d200042e0384480c0c800312111581c80c943d0030300340740c1d5403080000405c1c0f004d1200c0c4211076a07450442005e01c00f80c034100d100560840071000882d4810700a105040488519000501c4001e280c43c4059075503a0b03401e00d140c010031000181403c3c80400c3d41c0711603600204020561a4070000443d810124021310032030032100304403081400541000c00c2c44013085d035803000034080c0c0d5001e0140401c00d0b4130868001080c0001901c00350441d80c1c0005440c24007803c00000c0158803602034100355080501c0354000c20007110000307041451a54a101d80042c07024080c001c00c00700501c0143e842004155185800b030039400b1440044004510484540400b038a0404101c580190000e07000e0305241d11400340311441120305452140d840b034824032011034200030400411803400c0c020341c0101000d40c40d002c01d004420340b60910301410400d4042c05594a0340000035084d044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 615702482 1250 615701232 615701249
    0x607080a0e0a2918010507080f0a031d0a02010804030305060d0b0903030708072a0609240e0c031f2403060f0e0a0308070201020904060b09030f2a01090f0612051609 72
    0x30361005142a807174520407088071030030004020031038201256250b0310081d6240460302ccc010324a404200e540507540d00c202c43e030081c0060140400680013034441d80040f9003050024180a441135110740e200202ea400442301d006251744080108070300da42e0300003180b60b00501181064412010000b4140f001803144652816001407080a88030030019503a22000da0300f60040c0303c0b14001d00301c00c1e4000300101d400034081c07403400d402c041d05043c0c244000319071425070380401401840786c03480704e640510a184008031282070140c0d40703501c175080030b031444190a0003001c0c004125000c080c1c2140f40c8501220900881c00c2c1c2d40a1030201c16001e800300020350b15504c0e039010b040c0180350343d4030010700324060b00ca0005581c3c3c1250402074001110300d85000035141c0280d0413400d0310300303100300c2d4822036a4550134028141c1000e140001003030500c1c0602c10000880c0f401c185050f000c02c90f2a4003558901e038400381d000d50300090321910700700840882c52040b150440410b844070300084c4c8040c0c8000700a0b01075402409034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 615703732 1250 615702482 615702487
    0x10c0b011403070b0c01020c0114060604050120030304031e031a130f06090b0103051311060d0608011e1a010f050f040f0303020a0c140607080a0e0a29180105 69
    0x40342e07030400c5560002c0940480c1203650303228054019000c0e4214041c1441e4075824513032000f10103162003801503c5281c2c06410207041c0382c90b0a004540300030120f50300401400d94514100c5c0520010710007144030318003980710100040e90000407148840030b209010700801d40b9201d00c0c3c6c42170285d881c0d10710064080440b45183c429000b501048001c00315010540029898101c0000e4610015001040f00030400d0f00d0820459443c0c004001e0b0500c04031000500211070030703520000c10324000e406499101c2902a0010303100303854000f03140c212004441c10a502c8100098140c68a10540c080d00721025009400c1243c40c41340a000a01394021141031300c028000702043c146402800d94003900c0c010114221158003055030b0f820044d44850f22030409403040100c00c040451a0b100100b030350f4500d280f01130010707460101c4903110b0f100a600012035400411500410101065450700c5a980150280a12452010300e440d90f07d203c500019400c040c060000a00c88510718041030541550184001e090469 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 615704982 1250 615703732 615703769
    0x50f1014121507090602010c0e0d03030e150703150902090f10020a050a0804030b011e06030c050d05100503061803041208040f17061003110112060b0403060203060f010c0b01 76
    0x905008102d01c2d811010340c0000200003200381c1c0702d14058211205600200141103003d9070442d000c41d618611144c02c41322a0140c5030010380300ba40688020302840b4142c461069440340d046c2c4414006441340c000184d211001ea42c030310030340992100000c0001c00c00441c030748480f0030041446c0c21075a420b414401c0506044950f0824004d000450070709e5442400d95025040e90303d00312950b074009010644030720540e0000841e071407043c43da441d40407404890103a4040b6140031400c074090180c14295008000c400d009001600c0c0c564054180512442d410b0440303081e00782001c3c1803501c44000c02d4034080280805031880c6800000c001c0307905484d164842c5041e00e24035800c01400c02d1196038810440400102c000003003461560311050aa841c1101c01d95070641c4400c0306400301c4514500019000c01c0d00c110f501d04596000d6086003494600100c2c000c10443d40d507070461009504164019154240c0000811507a0316007502c804000c101c007400c081c01c0422881c2c8030f80c0740100e81401203908541c40f25400c503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 615706232 1250 615704982 615705019
    0x70804050309030a2906031c0306150c05010b0105090616020a03240510030b070827010c03060f0f0b0307030b060301090608060612100b15030109050f1014 68
    0x1102500005411690840d2842c50441002d007183e801c0c1240f0210407489101817041180c1810b0b01414000b0014001e10b50082c1015424801f0104200181980c03800001250072207000e401d503030101c2a46500030502013a05200c1e0948682c8c4e86003504000f010443c80500783d41d41015114100c0c00c41c144003468030000c2c0301145c08150103400c082c168210780c05440245849100545d081c0400d0402c0a0000d516007120705950b40c03449010003080c1031102c2d400106040d200d000e015074440c10a01410500c5070070001c050301050800210020565110070816020070f401d4020000108101030044002c1803a10245c920302000c14000c940d01c00d1400400700f07a0088c42a0080184041c0041030140e032541c0d6803914800030a12031240e1040c0740228400104030f45001940380c40b4070128180682003010400803070788001c0510b00985a802038000d1120380c000c0c00c1660103580078080c01740d0300250500748880b038203c02040040803003004e000440c0041c031a807000c140c0d14484c004003e607442004400b51411a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 615707482 1250 615706232 615706237
    0x180b0406120807120215060103024605030108030d02070302030d0e01021905090916110a060c090503071211010519091401020c0913140601080307050c040501030b0708040503 76
    0x7160051420121400d01c00c5500040000c107200e461402d140950b640d600783d850f42441d030300c6508034000a0000450b254040e4000301403150f000302c406110700e00c00c020138900801510704d141d2600c030410103034002a101000707102d200c400c5960403d60700790361404040c0d503aa445501030107180315402041107800c15001b0030a54828107600705040c04a00250724080b4005d421200107080101c24044001c48454081c00c01c80d2101d4402504640040c0e54400d07401e0424428a181e000c05c100d040200350b02c0e030610900c81503030400e00c540c801140f8250b02030001860503001c0d0b00124440c0d0040d0000b080320701d040c00200160168802c04c031160141070900180e9603401200004070550705105144190207901549081c00c0c0c80c010b6414040c0d601c1e90388012a95800b000c40c1464020401002045000000d42c90003050329110394414401c1e440b01c00301160520340282d014001990000c42c1c03903000c005007489408524001074408002d55803442d110700e105208003034a08414840b8003c0400e0a100043c000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 615708732 1250 615707482 615707489
    0x4051509030a0f02030c01080c0702091b130503070e090d080a020d0204031109010f050f04050603030705030c0f06070c03080109090203160b070209060303040b0a140706091101080a06180b0406 84
    0xe49005001a00700040000900e00c8100d1180c00360070806c0310f042d07020308000c40c0521181000c00c0c1c1405010303030a000503240d01401302d00c00303400540c0745000e0100c1400b0090840c0c03002c404115a41d14a4803040c9850302c01c10f60481301ca0b044401003004880d4200142c41142503880b45807100d46900c1c0c07140390300000e104581c4801d207501d000140c0801880602601070158880540303024000760b80e10075403510056014045c050303216442c40d490035140d10b40780d003015412600050030b89280280594075245941d114600224894018890350b00c040c150601c4031690203401424486800b1015a40082094505004039244199107409400c195201084956090483c805001d20465140c00074803a50340c0004004910505e103810001c0c80764200441610308580000040da030034000300a10695468080c3c400000b00f80c00148101740c0850300328002c0480309401100c4200c1c503456040c00060190310b00a0041c0130710350a299042202190035003180306100c64120001800c1c10741000000c000c1c0111f0390 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 615709982 1250 615708732 615708739
    0x31091205030a06050627090c09130b0a0f06090608042120060a0e0f07050f0112020a2604050a02090a0608030316020120120421021501050d0804051509 66
    0x901828100c00d10546c4255180382c00c1075600b58050f800100441c0101c115a0710800c03c0341400b0311889805c198070b003d8020044a1400302c0d00507001404900400074591200894501c0910704000780d0342c1041c0c210340038013503a00d0501e5261420b07440e00f0100c1c00081845c44400145912501400c1c0d2145540310018201d441641310103010922490765601e6041ea0359584042c0303000184001c00300001903810b400700e0290042c0901504d014100b0280d0307040040160306100d000d40016000203100d00c01401d03615403545a1640e5100030500000c0c1c40c001c042c5065040410410501000c10000500010b40d04da044515004540d03c5a0140000e81080d40c0240c0d2648404000d02c0690700360f104000d5115203803507000700203c05407181c0c00a41101045184406600108643c0d40c69007110100e0700e40c01030007041003256030b001458219400003049204040143c0140816810b90302d03c035400c8500400049801016001ca6621910420300c900d01c2801d104003050540a0190341451090b6140c001008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 615711232 1250 615709982 615709987
    0x1030b13020909010506150403031202220b03010311010e1e01110106030b06150a050d090219090203180102180d0c0509090a12030216061a31091205030a060506 70
    0x30309260180c8000c1e980e00c0d00c80d20000e070720649845031f00001c0d28212900740c0d403903aa28000d070b10401c2c0d00030350000208202400c02d44080d00d105981d580c43e54401400316009040e5a98914182040d6410990117454100704803240c5510076070381e910203c2c0d900064072807071031502c3c4042c510040c0e80b0404144100ba07003550070131a00100313012001d0310180c41907005803001407120358541c0d20803107144202150080410400d201840341d84a0070342c44070041900c05080a04025201032880451041c0e603805004281e8000003004000b1200c1d58500c81403a00640081d410180c070104c0c0e4055202c24040c2090041c88800b07500801d000e005401a0014038010300048514101a0f020544030120a1800d84c0c010f05403070804440c1c02d10070304c00c0360303032201e030681c0c4141c245d04060b034840021f4904c00001e02120990030038020110f603984443d102203551003144048040704401c10040000c0160b404511850b40340c031185101007910282c2d24100350410340b03891581e079501d042c0e800004250a0b04800d4105101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 615712482 1250 615711232 615711241
    0xd12031e06080c090f0412090e1602011a010e060d020904020a26091e0a0b0a0b01020106080105060901031b150e0108060306040f03052b020a032301030b130209 70
    0x4070390080c02a01d10740b000742c1e2180b4110f01d05202d0300c2a801d580417452080c1e00000640850340854804003900444c2c54100686655020180b9840c00309072441e03e02c500c0c0031140b016105809120320702220703014489568034495000006001c260710000d49074000c0700c000410520140d07883c0c1c100c0382c2e0f40c00e0052045455140010b0010300c505d0305190382d607010300c8d8006c070f6450403000c10300d5109210741038210040040c294400c2c0c400348140035042c3e0b004850302c148088140041c00585c2258410032100000007421003000000a0940340c0135403040d0643c1c1d1400050051680b903458442e41542d4000c0003029000c0c1d0088018211280b103640006002e045420303010300d00f20f5201a070303407031894400d90315004140c4805042688030042950014a46202c520134800064003a402808900350781d0203500c42005a12003003010460f0082d2486003400c1e50029000d0701031a01403140b955a105610040100d00d801d000f08000000380c103000141031207500c41700040c0c00c40106620001100c0d030280190119090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 615713732 1250 615712482 615712541
    0x703020f0d020c160b09011d0909210f090f0117100f09020406020a060b130c080906071407060908070206070812070224100510020a031202090d1203 65
    0x281100d40f00c6001e0340e12088122009450301c00c0a4851040d8594900303118103005442e462415500c0b404101c0c218100420103903101e0107628400d610003000f8203c0c450604117540b201d1800091440d08d041814000503148009140554070070550507038104092408820050b5801e04001000181d00d00f00030b403c109058400d004071400700d5250740c55822219456942c001c0c1031740a40c2c000d180042e8862180e44c4045007040d0400070100c0405000c5181115000c07c2e01400d5403100b00200740130a104c10b05004144108110b001c0e4401c1c45441c000d85c1d8440068520b107160310903460090000b81c5c40307d03889818030086004807440c60341c1c010316860b500c12051a24401541041d1070341020301100d0b8001950890020440996503414070f05d41d61400b9000d00c0c41c2c41d04072440a403010307134110103040c0c0216407512078404100d405c000303076001401c103a0420324000702a5041c040140d00d0541c014000400c6513160b01c5200080c1a80c06608a4940b0081d4002200240201a000c070110080c8040d480602c0342c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 615714982 1250 615713732 615713737
    0x10c080706051905070201020405150d0f050108030a08100509061002070801021602030d08010303020601170120090a1e030f03020c0409150c091a071707030815030a020307030b0703020f0d02 83
    0x309094040c0080e40d545c0509070300303c3c0111310509403c114160b01c1c0d0380f4845102c0c0021b0200d0030400c2c1001600603502c602003011904260020405a800000c640c11415048120554403403210852504c60300e0404010505415003c1c2c605400380f90b480d841003410030f00078000c11014021110086445154001d0986121810120103a01038081c1c401000d40300b43c458100b86068a4050300201a16468440a4140c100400300d02104556944000c2c44021042a29540e4021080f0f004183c55000d580104030715910503034400c0a01050343d01002507019003500007881100d40211503203803090800d0405a040a19104011394400c3ca4000600200701c02d02c4044011a48800030030446508111001e03185446680a00b40d002c005080801d422000981d000b46045403045002440c1c52448020409a039000081c0403000301300c454007084240d140284034400180e00c110010000c1c0400c6e60007003526401c40c4d00025102000f4040006e161600030f80440e29809042c1411583d51181602440c00a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 615716232 1250 615714982 615715021
    0x5100207050a0213290607020604141503090604062a122004120314130e0c0a1d011b141516030207020a050a0e06090106081302010c08070605 62
    0x120080360f0000700f84c0189104494200750302034a1186421800174444203400000b1070345035442a410400100140c86044c040c0004090301201c01009030700742c5041108030080d607000b42810300c406004100c14000c000030004c2d003003600704000041400c810112030046120140242102840c10b03195111815400341340c003070f01928030b0901040741c0c90000200003501480c56001e41d600c51018003044c4122075502c1c11b03112100c0d1007802d18505008416884002c1354001480c81e0920580f1240108620200d03010080d80c8502d000140d03c0c074103e441b40000d0403c0d600c3c900010b01080070450120700c9239000b8010005101030030b408007414105a031500c0440d00c02c0c0c40b03000013541e0181074400c80709162600c14090060036814880101c074104608110000c2d006a50141da024000480c0052503884200761700001c0d1404172050201c525020b828080401c0040e4040000c0089076810402c4890000d50091070969091070400c080032524144078015008011010740060b00e000e051010028804e4000301c2e01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 615717482 1250 615716232 615716239
    0xf030f02101a09060406030c08100f09030f1d0901151704031715040f06170d0518150c03071a13060b01030f0906020405030c1e060705100207050a02 65
    0x200324071444580180e90182d1000d1100c4082442e0707060440c50310421a6074402406440004c2c4030350740c0e403036049407847d10750f2004515400000040c203142001c0d0082c070903403214007001400301c003480380e800401d49805051064200711030b0010082211402010000c0c0303444005048000a5071101400140300b01c07200000c8000c10214504a940e07000d49040e41403003140c041d00c0b4669100759119030803a45000c001e100c001c0c01191000208015940c9204030f10b14481698400211a418400c8405960041540808640e40030322915601c00f07078000122a92200a0544251001004004140106405041402e00c1d00011410001c0d03524000090301d145405402808075009034a02c004030310210a03107a012711090085050700210760650070405280c2410300d000181e00f4849010081102c04503030b0704440b86500043c00b00444d2604112804141d00704490007500c6060103c1400081080580c1080c0909800700e003510900c0410b1181010503e50b4002c103640e68000340c0b50083d01e40c42e032052704034403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 615718732 1250 615717482 615717493
    0x91202030d0b030109080405041821080f16030b0402090411180111060f070c050a061a01030b0a03021203120103141b0607030e0312040e060406120512030a090f030f02 73
    0x2070b1071505010b40c220094100e0002c600d0141884180405072012034094000c540b8028400030000340f0010004c051080040e24840c590041858011b0541c1d1001c0c01c01800c0c4032130842406078500d02d49451195941d658100003030b6000103080860b0190049000c0a680240350030914403401920390000d00b6200000b6459800100b03080c001503402580c5842c140d80258030241c00910031301600389065030800e601e4103002030210355580ea807600c1c002200c0400c80704541c0b0707102501c44040075141c190781494002d00301403002e0401c032800306060000611021303100301c95494608849444c02d00c11920a810081c4040e00c40e517071a82480741160011340502030700c81c403500060f5030317880d01c903070700203141046004003010700d030401074ac030103e4046440c00515a071501076402d0302056135031081c00a00c02080304002100702407a01508001c103d482550155510024041c1442c000640c046a250301690f4441c030069100d0b01c4076000386d0010a003c0e00010000c200030101c1c10145038004d01c00c0c50381d80085900301c42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 615719982 1250 615718732 615718751
    0x6230a081603030c0c030f060c02010501050103180320061e0114130e011b0e0406080f121803030a050408190b06060a050c0a0c031b0303120f091202030d 67
    0x1552600c2800031401901d003000001e01c0040d1040415000c100d0040d01c00050903603c03500e804a1000c10004203c43e41c9648035440306039160280141401003c003400d00f009020a034900240581b40d0092008080101446002c120f0b0b91101001e2404110300c003003160070628000d61402d1300d84002c1c84076010484925030000030803060104811602883c0a0449040043d03840c1c0003001034540440910007954071440202c03a080c840c0790b01803c99181c03e580d0410302040340410300c0211982600f1010b07081e0010340082c0320301440064a000700058010200e80d80c2c05100101e1040031a403264529894040000c0060a41da032020140c4161040e0344266040d96141240240841c0314145c0000c014130991400150a4500380d4064030881d40c05040003071500751405105030802e1072889044a20144d0710300140103003d5040b022040c0400d003200d503400000d06545014101445164010304070b03a40baa000c01c042d40006402c40191558054040846910082e401a4681c1c03c0484021020ba1401c85d09a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 615721232 1250 615719982 615719999
    0xe04140108250501050405120a0506071e050315091f030305030a0e3904050108161706041b0b071208070e1507031412070201050a27050106230a 63
    0x107900700d030f10585400d45000d10303000a1110482064007408014056420303204017003031046c05858821191941d5070b036240c90400c03186101c988203c000603420001d0600810100030308401c5113852040084455126540e150740a268001d600c4900403000341d0300b0b001c400010140c0010207580030b400110000d018241486c3c4402d684e07a108044642c0f0720107480444002d60700580a1044120102100f442c0304204516002c41c082d46c40a0b4441091a4801e06041c08821424a03542024080d800f050000681ca1840c24654481c2c2c0a800a065a08440c6400f29200810300d0b084008044c9900b89035102d030408e080c00314854003104400008185110005480144680c00b4418540001084081ca1048144052a05401107007044092292070244101c8144660003d441c2900070003500c084c46213801c4100a081d6400585841e07141f03800c08502003401c042e40403448051401c10720680141c98480d04010f40540055480403019015441c1150500c40d294990800d46610a07a01114165900c0c510b2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 615722482 1250 615721232 615721303
    0x40504030c0b0a0b030a03020c0901081603120e1305040b090606010525140a0c05061c02030714031e0906091903050d0c05040e0a0e0d0e04140108 64
    0xa00248260001d040014281c2c0880c1d5001155a00001403520076a40428a006e0000302c099025900103d4411002e01c0d01c070100c41d02400c2c844000d8a280c0203110490701d4050100d0100605854000d401c1900b0a0f100700114258400000c0119900800740207101000341419202581c00c100800001501d40c6400603400d805040182e503a1890001d4070103044c150071140e020385d0404280f035a40c2c04404601c148102004002210024040340303900e600c0c0c480d0003841c180c1c2c001d43c040e0700e0505c030040304554404605010f6000074440984d980d0713103404d81110f9401d03406207402008680030080c0300c083c4508440210022411110551950f02d59420003542c0c1c4504480300c1100d07501c5148012403502c4003182c1388024500c41c1c20080e04042a40c0100b8080d12600350300500043d0b801300d000c1099006046110303800c8607000f203040040312401c1c103000e900c0d0300b11480b0800a01c203c07480c0380300194130745a22068107543d07170b4050075641e540c40e01e4080f42c0758181c4c044001107042a99120005c1745131520351 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 615723732 1250 615722482 615722491
    0x10603080a0f212c0a03050a0215090c01112a0126190c020a1b080102030112060506060a0e090c04150f0323010e061c0b0708060405 58
    0x4090601e6407000085a14a0546040d20100540c08a103100d010080b2010701c400d510f0341c500003040c065484800d03200c0182442c0c041268450040724010302e40301c000300707000c0352040e01881c1c007d50315140788600f603181004010202402c103001008118551f800411040440003091303036506255000303610300350707600e1031400f04042c80c2c2c51800d20b01c4200594510b1000140641c10f06066a1404000d0280d40418500f00e41c02554030061100300401c008442d500071401070098038041000b001c40c130070000d50350410010010f0a4002c0b210400300e14409441c507510051545e50000c1d0b580c0d40c1c541c0666140c1d0847e125040321403c1c109030106420b49020002d60750171140c00e644c1c1160100c5400c04102c1c425501034040701c1810010000480d005810b80d07180000301071640c07500f81200b90b00050007000c507200070000107181c03002190070f9060400104002c50458807814955407040c2c9640b40001d4000e002c1d03054100c5410300e50390080c400c0040038a1401d00c500a5611052035550f5944107001c240c50302201c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 615724982 1250 615723732 615723743
    0x30c02032e0504020103091b06081024030e030c0c0f0604050d110d0206070b070905040c05041715040507090b0d020616030c0203010e2104080601061202070606060305090f010603 78
    0x8808501a50303a01081d0f02070300500d07010461261b140c0768413800640c0302034500c800c248069800d0200c01e4006035180e070800484040242d015142110f007041c15604080700c0365200740100d0502c10300b00e20a810440c02003c450050301e030b4907200c00119540c2c0740011755010f40100c0c02c09a0043e001e01c0d0150075941150000f501d50000b650382ca5035042c600562045100d6406080c0b4440100580c40c1c20003c0d001c0e40d84906c1d007102c0c460030304031070107444200da540c0290701c21030801c5c40d04900380741e00200356000c03120890300c000003c680d801611814207494448514040400c14204810301c000000c14104071100c911040121a42102c2482000b40403420082e400160401c813001990401301029618540203190850a00d94194002800c0d150884c4c96100150f21802400c01150500c50f82c0c00d5016003e684610300e01403401b2002c13515008144601800d1000c0c5403007400600c14203404507441a6400380082005075118180500200415200d56269100b03801d944e0b5402d210510440003501d0700007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 615726232 1250 615724982 615725053
    0x506190909141b012316060f0b0604261501050a0623031509090d02190209070c150f060f0b0a0e090a0e0105012421050a18030c0203 58
    0xe8005440070005e002040c3c0f244001841c44174a1500b007080a0101440c00c00101046128541040000d0307c2d80444240e0031286400314508482d43c1c1c4c0000c440403200b03d10008806240f000164254aa10941c80504a805504011100c90140a404505841007214000c041e60b80f140f801b10345c00202102030181070000040001c1001d00390710040c59003c03100c080c1c4d09207880c00c50004105000c200351485000ca5219850480300150184440d91182ca101c26240812074001c1d0001034210300083d0110702030003101d450940a0217140c2c1034948001e07960304001d100003020112080000e05c003900c2001c210030700c0c803000440c90141502c12904040d40e16a00e400110030ac80081048004024181c00d00725907860181c0c861000003800f60380c1c02412100300f01c0c4901601c5180f040c1d103405900340001e08020551018428555a001612801e00c13a4614001815a00c254454006010741814031040c0c081c01084c2d0404c0680c812402c0300d11520940a0700d200c44840c0c1c01441035269404910511401e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 615727482 1250 615726232 615726283
    0x301030c03110a0819030905010315050420032e03050303060f01200705040f112205180601090801050601050409091703040c030519030c0303050619090914 68
    0x1940e03007030400b2040100340300d60203070790703805602e1400162807420032481405a91407414981c01941e141c0060600382000d0000c2d0000c001d01d4400e03081b0310301841d403080b55100080c8002c4502140c50b0016400b070101d44540e2401c2101003200c0b81203032802038141510f000c500300e8041120102c030003030889900c03e000b5401c0d0f0303d6040410022020f10380c8114104600c60440e105d20481d200200003440c000c0002510032035042c08103200640c2c0c0c469004400d41400c1c072403010700710034025045910900103001e640381140c12044000002100580c070107940000466000b0341d24549c41e44042d40680c200f41c0b00c9404040e40d0b034a4141c242c6800f11002030100300e0902c41000481c106410a5110500c1003924510240600304010301c0764106580580c1c040321180400d0080103010003071700c1c0800090943c948152192a030f40103042041d80b0710000c0c1010380740c2e80411101d072242d1f0300d40d00b1100380030b0002c0d444894840000500500391203130184c80e5028040200348000402242c10003149002000c00640300c2c06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 615728732 1250 615727482 615727493
    0xf11011b0222050a0b04110405030c0108130602070b270705210f06070f0504180f15030302010c1704020a0504110c250501050901080417041703070c0b0301030c03 71
    0x514080b00440481070550b00c50700351040c0b08861150451940000b105a540030901c0304961103401403070300c42e200070001403040384e0780012009031000091800010076039464200e14290310740120700900140c0041151820003490b04180c0c0e2040303141c06aa2200e606052241000036104030b90054455000034a061191f410107401d40441d00d50134448125142c2c44440e13120345484809031080000b030300030605110003160310501140000049162850510381800311280c0700038446000f2099455643d4800d54003980c07150490346c01d0000300e885100501e44c1c3c9080290280c1450401100002d82256880c0010000050950300503a000362408401c2802c0c0000d01c402400008602c1d040d007042801a05540d031030030000c4000711100400480f503900e04826408071100065005103052010500188035640d9102c051144d1140d04070300c24820401c030707d9003440365900c42d0b40c0010700710001c1d103449803490680000040004500c00c442d242081c81e1b440400038494082800700418540d0580700070400b064 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 615729982 1250 615728732 615728749
    0x60905060915210c06030a050103020307050d0b0106050a0c12120509011a060c070f030f050d1d210a08030105180105181f0e04150b010c0213021201030f11011b02 71
    0x741d00b0101c43c0804c15100004109070822201007001f551260700600441c241400014010302080e1451021003c955450700044041400345104000c00070441004082c410180304a441e60480032604690507980f10041694620010200301c650400d40892022101403040c4405403018a074010310441c1c15004004540c0d101102c3c45400340f04582c0d0219485040b003480c400118032401d88088035100614000b8102400759a00b202800002d900341701c04680c0000004011500803603100c2c0c1031800e03961445000003600610000030b4420100c50a0401c403001c402103041e01c1d4226865801d0598040c0c288580003824099241c12400c1d0f0222200382642402c2000d81181442c4100790510409061480d4525015400805051810014001401111580d408038115289014070070f203400305002070000410607200074010007100c0040d14080503150306482181e0038155140c1020350b03681c10100c0e40804c44030300c1a14003421000c044056980207039801d400042040304d0a4150000c16000c011210 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 615731232 1250 615729982 615730039
    0x150d0504060207020301060b12090d09031b08011b020c040e0d120609332117030403020705010207150c140309031e071406030a1e060905060915 63
    0x454090005100503a028050300000d082a0300030103441d10389e05290b5074405600038002071a02e400003441e04031440e921051010a907900112031003104040c41c00074005a03007455100d003185510702807080005100c81110490440c4160342164411820001003008031482415020b000c0d41c01031680d0100705010702d84100100302c0144c000103440c0d581302c246000355110030803401540200380300701c1172452401500800c04410b04600a10b001814800d01210981400b04440e000045842d004002c02407401c1c0310ba00c1102c5200d07601912410b2a203030181d6142540d0286038058051000080303004200043d84602502d40c070382e121421040a900c0340e40100380f0b030b00302401190000700180080c03a03d042009e4001140c0c030950240c7c0010002e0389031401d2002e0f0fa08182c00010055040c1d107403c1e074590007680d4101c1c00102c00000d01440600309014064440d058020391750342000c500113502002c562015105400594000c80d02d81d45a11050808811b0005000d6000400001c12003080002e420041c480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 615732482 1250 615731232 615731243
    0xd26060420030c04030201080a1506051b0a14281502090d0b060a060c0317060406031502030a14061e0a0b07050a1502031012080405100f02010b150d0504 67
    0x2000700e1000e034601d50003194924038032040080d0800455a001c203c159101c44c5d140d20401c4a001e554250a220141c0c6100f801d04003c0e02107454035517810030110705000d1800c6001227401c0e508941c41d04019095903600aa40303580202002011188480e810402041e80000d117a2003a41190750755000d400314032192032000455090140c002c203a00c1e10005a80094040d07801d55280d881c0100800c10382d03d030a908a14200061200182e0000340c00101c12510783c415400b001c1d180d940c2d21804900200707003d0b8006030401c120b814400035030700c007164029401207440140c184600101002c0c04481d520003601d0b166044a03030b21545c600e0303101c042801c94a900750700400001915655900385410340d0080003040d80e150700298141c0302000018200d12b683c0580c140301c154190f00d040004030380e05038001d214114581c080d0803220070411415000715405080c0041c442502c898080710010561411024801d000d03619100001ca00d0b0300d070600c03812000f5002200b125282054103624680946406841200c0c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 615733732 1250 615732482 615732521
    0x40b0118060b12060f0a0501020d05030a0b0d030f0206070c0f020603040302010e0f1e0613080307050d152603030a0e03041a070506070908060103020904020607140d260604 75
    0x900c4000c0c84010300710f5a81e002140380d0682441c9040042c40e000d600c030242d104155221007080071b641c02107000761204440e4141203840f81e4801143c0c0c1c001e040081025a40441d501ca11801010b820024040302e402d10741d42220000d9641d03070703016515200784e80c001400714548414104018500f040c02182d00c244640300104c0e807401c3e0080010b00e40000f0001011031600003034800b203c103d80d0403111020b03052240340288900e00789408035484800c0468400380c0b81040010004542600803000c4901d868040b03501006000e0200c0c0700300c0380c1c0c4100c0740240131030340100200040308090012204400f01d10a01301035465603c69091500040c060140d5020587c00103200c00a80350260400155100d02c81151550b0745003940d03d0800c0c1000001040c9009000104d402800281e10024030795042d40d0b070644c0d5814607500c541c000540036028507180107240012091301301c00d001e80c000c02e04000700481904c0e0790003411148420841d0500480c43e000d180c00039110005a09480c09030801021030080030300d0080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 615734982 1250 615733732 615733739
    0x31305011503050715020c1e010c1a0a0c0e0f040f060317120f070905010c060b060705010902040c050c0a02040b06071407180b37060e09060603040b011806 68
    0x2103030340840b5841a01c1ca500429030070420000108040041002e580c8044c08054440d100041c80c181000110a1a136030201550091243d000f4404840b10fa43c000341c949000541c6c00203d5000c001d4100da540307100c58100514040000e01500390300c0c40c03100b002092000c3d0b14005509001c000e01c44001d50020064583d0303400030201d14980d034401e00d442840c50903070385e80d01008e2180103480c56000e00030280c003550080030808215072010aa0f0180c409c06d10345034004070003c0c10140042d00b42440c070568049030015045040150551101c00a1482941c003401040004502aa81c1b4003400080c40c040390030035042c446c014038007944281a010801061141000f580d51500d558146440701c0700845a4080e0700c0c14861410310801800540c0582101440103044020105401400000e00c441600c8082c00c0348640314403d0108440c12624203540c1c00a503242d8500c00102042030315020140982102008600c1c1c0d410300301d0840e442940c00008809142c3d10b0050509070300e010800b130b0207612070741d02c0c030011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 615736232 1250 615734982 615735011
    0xa0b0310140906090a05070315020d0c110f0106121407080604031214010f031b08030a0f03051806070c05010b0d03030e0606030105150607030912081e0304030503130501 74
    0x900c00ca10141e48005152804a080d60b00d442c4001d00264a5944040403074400184002078460680b81e202c1c241d51140c0c0e0f025100307807000e0b01860210030070050401440302d52142e0303c080381c1e114100f00403040b01c0b682e0252404690880b440d5001d00c1034440d16440c5e00c1e801082000c10448440c0c40c4032001c543c005030380da8410300d0030402c042d2400c07400202941032a000e00c3d041402648038040c0c0c071145200046d454190702e01c0841c042403000074000804019a4204034a40844a50041c6103d01c2a641e0b02c000302080100350720a40c40d50781011034909400f05030545000c0f4030045062501c0c00052000c0d031540c1e4400c0d11614444201111691f49400703403c00903440744070a001d2801e1181c2c5001c03507080c4840c00c0711400d001c0002d20490090785080d04002c41c0b50304001d480041003100745c890380d54a20481c14202c4031849250056003050004400c11010440b65000034002d980780e040301d0f440d801289125a02542c417080d10003500060080c408241014001c45080e08120700c01e1000242c42d51280654 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 615737482 1250 615736232 615736241
    0x20a0302090a090c0602060903030402090727090c080105030a02010503101805060906030f06060103110c01090b01080f07120312180c061e0228050f01050105011b020303030a0b0310 79
    0x102d10406883c0c441035410458866000b5002d0302c01400507244600e407001000ea41d034040200080d21402004d0007141c260b07030103501c03085640e007400080e0703084202c0303695030300c031410074444c407914984602d415a03156881d4400e65900e81a210010040c01e08a490742e001192140c1002c2c05982010002d50310000c0c04600e400d020400303d50580384086050301d131200030098010002441c1500942000344070743d81c51080400c205034002c03401d0900182c03007080c4400038240b038040d041011407650318140c440001c0c0714611220764100c49040088411603c0c8400b20145c03140058401e204c038044044841000007401f5540800070801845800507240c41c040c3c0040030300444680e0300380c84003480702c441406515800748012801c00184071046030001e800c100d0095070751071841b40240b03285500303d038410f1594400c0b410110296420500726880c0164640405008000a218090119009a056a00b00e004d4980c04680c0560010301550031a500c0480040c0a0400c09201992600405034401e43d1050203105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 615738732 1250 615737482 615737491
    0x9030703060905070501030b09060d050c0315040c0f080d052b0f0f021903090501020903011b0809060c090405070201090503160c0b0309071a0d0c050705010c080f070c020a030209 78
    0x5000c07408814500f400c50628101d90070040c1050308181c01415507032124001580c11200594030001442080d041c82c5040051101c2c03ea9418003607860851440241c8410303250140c0c0c0142e0050806039900c20028800c200ca910a075641c2d60806d084aa21180c0548041e0060f4040d20020801414843e1941700d00c242c00d610900c0c40d080e50701c5005510000303043c0300f000070110308100114a00308200d40e003005a00d141040090816440305501e000300842901958448580a002804000740c400719030b1120304403002c41c21001424040014044000019041c0d000e04c1040c401c040c900100d100612000c0d000042440c4107542d00c900a590000d04100000c00e00c11450b500501c0c000640391808020700d40e95030740604900300050003070200104001c9400c03401c40b1040c0c5411341c5243c00269008501e40252202d02c81f0340ca00d01840d6104068010b80200001485070340200300441090500340c480010030303140c0803000c0729800300280c00c0d1801801c1c00ca4595000900c3c01001d16075a0340040d000100c100c0c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 615739982 1250 615738732 615738743
    0xc062316020a1703010806060f1507060b04020d0c11032d070b010816050a0e1609080303010b0d050a020c060610030f15050301270201051606020315012709050c09030703 74
    0x100400c1012400d20209030450011100c6800e41440d0702c000401c0341082403c2c035038ad29040047c3c5042044025803046c8038180d8080c2c4155100d02000c8071a1000701100c100400214800000444100c1001300456901001d00c07400103101324400c02c60703101c0c440400d0200c40390301c1718104190b40c04204003003056030081640c90002c140a00020f13854240070a501d501060154000f0b420a000700d09081140ca03520002c101c070001404120000c0441e26902c4c44d511104207400008000b0440c002c02400900c0d84040c840c2c0e0a00098840004440c102c4c1f1541a0212080c0c1016002c10034520f08820501d00c1000c8919002c07860080a07041d4104448408011902d050f98010080120341020f000360242103068500d082800350045103034481c07035108646d000341000030008000401020300c00308200c1e5107030468021901e91810300c0b10042c4900300201100c0c0424441d00d82c10401e0b0101c80710712000c0989d0a000e0780c10107480c1043c400c01034071000d408140c00348828021070609403810443c8100650017403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 615741232 1250 615739982 615739987
    0x3020913060b030304060207090e0307080705010b040b0f03030a0e0f0a06081e01031a0603030d0504030201050402210c060313020306040530040308090a03050d0c062316020a17 77
    0x1d00d0030700c0441c0d110340740d150300a400920040291035000724034081150b464040114044150000090551260840003000290040b4402d03007071000551210840e80c1c0256420007042c08000d0401c4500141c070ba0b0010740c1603101300200c01a06116800040908c0d102030249402d40301c0e00e030005507001c038450f000a000544800100700020b034110404000c200c08140817400c41d9415a1038410212011400c200c5039481c84c1d202264280d01c0030421100800704030401008a03040030315000380681015201680b14621003001240c0b4001c514050900d20f2803070000070600045403e051203aa41c000620032003280c0309444c00b22016803024002c40d449144180701400d0140c100068442018441c000ca01c070b01c4a4984010445480f000c80131030f8152a000b940140d10782e242131f0300080803451a0f0300000d14500031305d90140c08803500701092100e00751180b8010702103402809488a01941048103524080e110100480c186000e001d0301d00f02094240d1040e200c40340101e440e00070750752284604280090100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 615742482 1250 615741232 615741271
    0x5090f100207050c09041407170c0a140112020d0501060507150b031207050f07080d030b060c0c010c02060d022205031507120f090501090c0509011a03060a030209 71
    0x5000c112000c0888440031030400c902c944416585449203403205000c1c41850703012806028000c03c0000c43c040342401211051078a8010300c402d003030400080c000c242e1003004070002080c5043c41c0380c0c1007901e1143c121211008840c60045414400505624100503401c20802d16015114058075010b0030713498907055515140741c544080401c2c800000c003c4024903003103403941c0c1940c020903600c2c002151400e40382c0d16540c807400d1180c200301070207403965039a104043c40058011004204d11070403c815440801201c1d6070481842400d04c22504502d00380c0e000440680c01c0c56008803540348945001038011410000085030f1a0f00701c3c0e000072020070242c606001d1f03075a041101c941445018020990141c01f102665070407624140d01c0c00741001d4103200705c40750700e0134582d000c80d070000b85040c49101c01130100c0c6100c2c0c203140703000303003000c220070745036103045290205079420998030b1141210000f581600b0301c001421039080007900098542580000009000005a070b210028070f409000c0040c0c1c05003c001e03c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 615743732 1250 615742482 615742513
    0x12030c110102121e1e04030e03060703060e06040c1407050309130f0b120a0605061c0807051b0603010308160b0c030a0609061a07141c02070b1303030e030106090509 72
    0x103a903070407081030089104100003140e81e104000840c5a00d001175818944131484e0075100c8102000905805119034000c1101450f4150040e4080743c0d034110011a45880d164280800c0e500e0f12500500459000c14105880c90784010041045601031003d49080c102081c0008414000c4030100b40d00e43e1381c4030425604074621034412204a00c2c01150140020003030643d4407030300c50841c1840a00b48543d10320002d15a600c4a86600f01140c2040c03074402042c080518152010b604103510642c1c0030b11411404503c0300fa00c01050b4108480d00403c06402d50f0b103075940303489244e40070000103a25902001014000100740400300c501401c0304003201078880c0f41c10061041140d0082d808040e882e4100300c001c2203661207903501c1e845903c1d503002c50290f64500e80d00700040050881901e44070944100341c5081c14481d115121604480400c2e0309513482e40c0c1c0c1d030742c000852a004c0c095418803a05030084040000a02807121241d100ba006000494035541d80c28450003140c1040350211400c0d00000303c005001003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 615744982 1250 615743732 615743761
    0x121b0306090d080613380d0605060a030c08030c0c030303062404030510090302100b0105031504060503121201060903030909020a0318050c1521040f05010f0606170412030c11010212 79
    0x481414502041c040c0c00e80008446151f4507001824141d500e00118104e82c49484e44030001e160481c00303008003039590740100c07903585d8410111140140940f4096480d01d240100407a409080028002d034524071a022070107400241c1d41111440460042100000003a01070041102080445500194411140c20042e0170102000281c5030782c1031a110f4065150780e04141920b41116800544402c0381607200f0224000b00911b42141da07061250034500c407a468024001031044800c1034a0701100b9903604c0340140c4881000303000003000b06c0c903844803c0c40040382e65409080441c41c40c0c9000700700560501031700c00720a4205101a90380c0c0e04856070317400d80d9082a8081c1074032248000c5040785014921300107101c0004c1940703c2c20f106030f060341c0089414001c3c440301c1006031642007402001031404551280000344400c0c0b0030240445c030105812259181062990380c03107980c011200c05940b10458108400800c01a40304006100641018100075202407000d40304210314044c01c8181414104410f20350301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 615746232 1250 615744982 615745061
    0x30c091315050a0b030f070809010e0a062310050d032607110f0709020c0f16080706090e0601080402041e02040e0c070503040b090103020405121b0306090d080613 71
    0x20b40c4c204244200c2040d054481ca40c08030a80c684407002c0e4440355080d5025066035100b07600f072485488000d0090004550215500c1d0101400c4075a1103a11112449540fa50803103070043e0380140048204010f0030300703184c005070f114030910b401005803c0c8840180741e880c4c8910040090b04240e60b08100e0318580020828840c641d9200003440c60320303160b0700560b5446103030307020340f104442c2c02291244e00e000c000c0158049600e101c40c283d030394422400503141600c1146114094842c41428000204207008103020010307200b1300702144520b43d50701c50040da0702000140c0101d030065034510818038840c0190368824400c402c040301c00340e030315490508034070700440c000f9180d03500102d42000003000082d40081150121128030000300c5d00c44030b1800041c1c000340203c1c1d10464001e804038490300f1000360041011495a440101a413521056000516540e4242112040c08640c041540010000e009040c40c96101000514150030115680d0803001036980c40101080741c009048288124010101c1a10300c15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 615747482 1250 615746232 615746249
    0x609020a020c041b0c0528051504030804060b2202070203010e1b09100f0902070210020a0c0506090301091a0402101701180e0a030503160503010b030c091315050a 71
    0x120318042a240001030130940e00c14080300300b071031100308441480b4092070103e1034096610310001c44480d040449045010803580741c0203190700c0c1000c088036803074070b1800389425070360f0040c0b15601e41e03841c04010071b002007049511a03215551410800e801860214040908440140e282e00040c4141400d45010700720301e074030b80c0c0c0140304248000003035001d0180d030456080f1103011054030b4540444201d41495000800f07061002d0034007092800c42600104001403003501c00492100c1e40705001c0381c507082d106000409101c000c2c50100a43c0c5409405070030142d000500000c4e8851040d81c456058400803441c40d803600ba000c2c010041945840f0000b04401c40c181e003040031a09505550070041c440050140c4042681c541c0c1c09450251556402002a007128008407102d403081ea00b400307011354200b11800c5182031803043d030001c9003510400a0340c6c12500300001c0681151219075042c01a40c0201900d00c1d003000d1007001140740b803400c9001d45080100e05c00042c102040c24075040c0607035060980c1001c0d54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 615748732 1250 615747482 615747491
    0x7140603130b06010c060c050337150902030a14010b03070f050a090b0304050a05010506030a050309040203223c020907090911090f010e01080708060d060609020a020c04 74
    0x42105000c0560700003658009a244841d640e00c00040e0707007003070320480080c19151500140300d500c190081c0046004419150a24244500d100000710460201c20f21070101400064086044148503800400303000a4110b14005181e07119a03070b80c0c08a0300105c40c0380c8440ca4507a038100320751100b25880b19024180c100016451860800c2019140300310100e04002044000202ca83c007407440380361800041e10114905540d02e00380380c02e1840c5e85441d184030030b85095192102040d41443c0c00902c2c080003d520001950400c1000410440290001405540040c5850b48a00074ac83c40f1506000c0d85a0b01c0b441c400300c0f540341c000b2100740300d9881001d01e03011a1848040e6415002680f296a02032481c0c0c112131f4103801d03a0703842e041140e4080582e03000364196424210740d030720b0071b0200300054409010b0980b42005103640003001120056007050740c06002c01c00f210049500c041c071885000e64480c102414034007a019040c0d558000f2601c465204082e202c0d80417071080c0d1801da041c04901125101240c00740f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 615749982 1250 615748732 615748741
    0x3060102030a050708070c0b030a1413020111010b15070510062103120f0930120b030a030801081e0c0f120105040507030201081e0a0209041b0207140603 67
    0x7503592181d02c10b8401800707001300e054810010301c80c046880050780401044082070761341c03c1c5030450790802e41d10b04c0143c1d424054020b01070000081660302c154101700070b071401c0008503001500c403d02c5800000d5050354030b40480c0c4a09403103107151800c40301d6038070254076910302e1141411418101c1244c0900d65441c109601044402e201c140b0718180da00d600b98100244140701d140550f05404081054021142051b000c03982b2a0025030041c6015401512170044c49400122995200320710311140c0c1c06801506209000d41e03610031803251003c1448501d000502241d607000013450034228003c200c00141101005100040d024002e40300341c03840800141d00b0341781c0010301c1d160f224030314404500c0c00345001d403072032488658135201205280308012000b0070841c01e06e410115100c50346070000b46c3c08150244007282c880c030f00080500c00558020214a440c82e200d00c4042000380d88107804a40d0f0103922401103078050a00c8925412540c2ea4640041c640117140030802135046000c0c014041c400d00c400e00400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 615751232 1250 615749982 615749987
    0xc0d03050901021b0904020609041b120e0102040b19020f1219030c0906050c0c0a0e07030c020d05090927070602060907030302060402040b0d05030c0d1b030e09040203120c010501050a0b030601 84
    0x80e00103904450f2303035440d4205000424014180c400c00140746103e1020050003081e0000c00c104031003040142e040c040d54680f11041800e030700c924891102801810045c12481e00c0e41181c888070b0a60b401e20660708841d0f9201c050320710b8404820201c01100a0000d01140780b94511182c2c030007a82c0083c14184082c460141c009086185c2c40d1042d10181b0000141c0405041021b0207d203003820030003090300030140d4a0b00000d44801d102219103a010038035040c180750041380005041d8218040c143d48441c5004128018031460300301c0607041030755400c09241003219111170b008030ba6a032041000010982c90f440c000c0000c0c5000d4014190b60b40541282c2c4041c00803907804a5480c3d071198050300c0101314644d568021850000800700080c2103400003280f01c03501a100841c0d945042c1125550710001c5012400f103e21721501042001000300b0200f2034800324509001e085990f019000406075111600d0f0752485500e203078070a20602c080b59541e0030040c41103203000a07060000d4010721a0040c114a031040c0003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 615752482 1250 615751232 615751249
    0x601080604090507170102040806011d1303090b0f0a202802060408031c0621061401120c291617030406050f1510020c0d03050901021b 59
    0x300c60007103496082000601c00208107101c0201580d41e880c0d5600718454111034000e40050240c08514080c8100005801128025040300c00520340000c03003460b15100030b80b04214064450441c01c1c0800c0e6070002400f805040054903105180381000c96942e50441d40060000c2c403110201c4039502c0c1e001054007044680002e83d03c12102140c43c06915440d0400c2070301e0040211414020351005c00020302003601c6802201621003c0a4941c0f8009008215502c10b000d03150580540c0307902c100f41940c00c1c48024945030840040d940241400244e18501c1c104106041a00340c00c080410810b07512088204025040c03c18010401c00c0b841905151080c000c0408011015241d0b0403010030102e001820703801c89200007100c10758802600245009500003440203070f04201c030140e400714a02800030b84075520844c0d806101b00c0c0300209481e040d01003607041001d06040e0120040843c8100d00c4102c400c0e880c0d2101032003416002b501c0d447d031185d22250009251109014622503840300e1800311000c41c1c0c40300b101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 615753732 1250 615752482 615752491
    0x3091709030c22180c060c0c060f1b030c2111030c060f060102070e04030e100e0307031722051203180d080f031807151713080301030b1509060108 64
    0x100441d059480c01020032644c0c12103900900984002d039400961250405182d0002da40301c0c4c1c001801ca140c0d10a4241da010700a406107001203210b2421414144070007494002c0100d210782401c1c4001c144607114102000c44882802010028008541c404960080081020090024015403400596030002e50b140c100c00740920780041d00c050080b4020340c0c028802c070405000990745030b0351545800e0800a181003000200280650516400c468003e44202021f041d482d1016000b0300b01149199100700640695850000000d20140700111042908420b107032947d1310107041c26201c0c541403400f0000c0c061001420002194000c000d5130045403150042083d420800302c8840743d0041050400b00c401e4860700203402c4507440000200100d6120341500b0481501911044030440e0303465603d4139050311002d0203c040454034601c40b901142e0001006568840020020b9665201c03d545e83d003000364000381c00c1101c00c00e1941040040901c59000c02c1c40030130b41d0440d85144d241c00c003000040c040510190 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 615754982 1250 615753732 615753799
    0x8070807050106050d050c0901060e180c09120c0a050d1a06211c020303071d06040918030e0306010b0301030b1e0c04030c090209061903091709030c 65
    0x38460248030080d4022402840c1c05440c40c07908105c21720305180c40e1204000d55503c208100c8001240180c411a901c09200c6009011510081040550500851401001c8800c40a005c0200745c50a072564039180c00007640c2d1100030052210700908008030a06140c00560043c0542240d5101040304c0385905041c1003030201485403aa222080815940040e0b00290440c1c0390605820b1300101900192548410944844804500b001c50204036240e210641d1403800050b4038440d843c003012002c0140e20180c0d58024892031415a4882d0102c042e1080c04c1e410098928041070700405041d0441039103103998000301d015017865810f0100302c5220f8001070102900080d101c1c00040c0090f00d98548007a55000300f8004128545402e038a82c8802d40d0107400211001403000c0c0c00041c420200380242c4140201c0104030a052511004020004000198444040580380c11024012038246c0640725071060904202c0f50356410759100745072070103081c02c01040c01060203081041c3c2c02108104102c22010114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 615756232 1250 615754982 615754987
    0x7050307080c07030c0b04050907020a02030615010e0301060618061b03031a1e01030c0302070b010308090102030d02040906032a0303050f13080d030b0d03020a0b07140d0e010501080703080708 84
    0x314079091a00a0310f1300f000386401030401003c94210340c98030103081102d0302122020010303a111032040341c0781c444202c4001c1d09a0b204001199802039a00c10301049140d06140001d410420480040d0945010b03a020350b0204d5850400700001d180503024601c050415810010201601300241284200c640c503c007504051350703440c41e000f40c0440c2c054079550300742006240744109540a00503e44007c90f10319840e020034079180e03104000724024001d03160300682007002c4801030b0b0318640360783c041903000c0702c1d10504601003007100740000320203803028102520380070030002041401c5161621201c2040706203001000d03052a0618483d400c113956030002d82c0d42c149001c540310120800000d84078011030300d0410701691000300c00f05003034030b001036429a0603900d0755082c000096000e0601c0701110800d40b029005801c071080c0c0b1008124507010840d040401e40c40d02014500c0803051400058200e60561020b40b40c60340441002d0074801d0141d14090010035014101107895940d94200c90b1051100c002c021217000b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 615757482 1250 615756232 615756247
    0x603070e04080901051b060709090e0616020f100e060709260309042d06050a0b0c07120b0a060f060c0f020a0503011107060e011103071803080f0418020705030708 71
    0x1c2d4054070b4862a12a10118400d0980c1d511b15407180411151280000c0c4481c0300021004c0040c0500101c0445600c089c00168840300480091000034103284000e6100340c00222040d810108080c540800d4149000282100d0511003d0f0800c0c0c0c0241c540410821a50030a001d00c445040103800b02c00d03400710300d408104101244050450294032040d03580603240c15070a40070a20030301001e031200c86020007900e1a19403c11400c0d411201d0b00d020b8590805101c09091002152071401040301d825074004685455a072a1510382c0d0a41d00030b00c084600854003820720181030000c3c051400030707080c0152103d1005060100090024544180180c03800c801c00f0714280954680d441450050032015000303020ba40c040034904004e41d84040c2e0202c44251130071401107455501072041c268084500d44c000341c6951900881111001001030002c8490072050000100007000b41c0c0052499000c444526610785161412181c005140d90080700d90090040140e200010404012144010760000d0116180d01e078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 615758732 1250 615757482 615757487
    0xc020d0806040b1f1205011e03020d060b03010911120a030206060616080d1d0303060f040b040e0714010f110a0b1f230105130314240405060603070e04080901 69
    0x80c449041014200c500c4d0580441d8054030315001040301490901451766986d02c0e04050400104000c00703000d58a1200384018603041152040c481d003e9080403641194610001f803c44003071000482d10200c803005042c2c0141810a903081400a048001c0e24400080d51400394a480c3c00030852131060300c1c0011050000c403050030a0140e150b030446600c0342c5030341d80b468141000b00003c01c0d00071a008403841da03550b80a0000001c807441400082c25950606280300c051001a01d1401c055580c0945c0b20300030329020f00c0c0104009030041001039502500704403404d001620f004500d0b0300200402c1003402141c81813680000b02c0c1d25405a01410049565840c800c1410018a0041508201c074143c15400261811810040c8000d401120311103241c0e00e00f41070065402e03100d04502100003440c1030b541040403a51984d038884010f004130b8240e41142c40100c2c400c1321441c4c82c400342e114101217848103000134020b0400445a00c4441a0024494a4240070050390401001440201600300010b0200a01d92 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 615759982 1250 615758732 615758749
    0x603021806030702101a0108010f03120509010306081c08060303040b070f14070e072c102106080105090c2805091608220605040c03080301030b01090c020d0806040b 72
    0x10707116001c100440d00c0c508404141b0803c848400c0c0085c003540008117100b02c00c3d544500c1182e500c140c81240c00151040c0941311f43d0481208076050503070390000000e11110901041000c03021101100d05141c80c688c60207002008050100340c06580b082c0014040e0000400449901640090045051100c50b280400030b41c02c2100d118440f902580400080c00314030645002d0041100741c80d8000800c4180703480e052a142c000d591b0041e0750885001c1c01d6117a0402030201e87e41d20000d440c19003110a946061038043e6186095615141b1355211000c2101c5402849840e400210b000f010b8036400842900050071174010051000c2d004a1000c4681c41ca1407071003e0150003005e010b44080c54a15100c0250f040841c00b2100b06070202e041364000134500003585001c01c07c0440c10110041074412a0340300d210051400400448581010302004000702d10850302a500840c40342d0844103903503052041c180181c802505520f0103640c4001d40310080107401040c20340e40590252000101140c0c207000158a20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 615761232 1250 615759982 615760003
    0x603060604150503010305011b0c030f090b0310051e0108071218032f07090f02090a260607050702090405010b1002030d0605060f04091503080a080703060603021806030702 75
    0x800040e11040402c80d0400c01450481c4c0c0036030000c02411100e40366412a80048040c00d00c0040c4c0d030700e007001c000a8003441c00701078a8951450300500c501d4591011098681c029200c4450074540c00700c1c10021480c04036039140302c405002c44409620703100400003030141c2c0000707450070b4248009544a14022111688003155500e089218810300100904014144440e20a8413104202d506641c001501040700c00d50340c05c809940340100006850100c0c0c2c0350003400684900a000741c0c080044030481c0c0d80b51103906020380000914507402d66402120b414036844141a4440d60303420450800c411103420100340c4500310b8040ea80c40100380c1e101d15141d030041016000d15a881515103c1c0c500d14168004090300784000d082808020036230301c0701304100460280c45040346900c00c0c20031003030041241642040420412050300380780c00f1910780e079503901d1a400490008000a004c0320401041d59450300948000b40868201185809078000c019034940003030000c103901492002011603015442008410b02d074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 615762482 1250 615761232 615761249
    0x1090e0a120c150203070c060b0a0504050c0d2a030f0b030a0303050f071706040f14070518060405100f02120c010b090a110712120c02030a030c0f0507020603060604 72
    0x160010040042c00d103904400b015920703000c0d14102695030a1a0b40f007200e0080c1d1854550420004960b80d0fa000039000320100c864004801d00d4000515031224002c490085418500c01620344040764241d404959001406000c11050030715080010744103500004000070315072a0105007038008040781d001034038428507203e40621640c00381c0f506156056200314091154a41d000c0c031240c45428040b6144511082204c801e0b0340c1032004151240b915070b000301461102080b01007070300000307032003c0702801c0b2044810700e01250f80024a0080c120044500414560040301d80904080c10103001ca80c5a0700000304000078810358900740c003030745030003000f00300741348400142d86980d03410001c1101d60281191045090080344c0d20004030304001002c2c000d847c1c0404690143c0c60a200894031061581111900e80c0c10a10008202030035500100d0f004002c04541d5a4009540d141c0741400010115406042c00c44100304100c5104210164060122040c243e0115012030b1251500d00c0000d11610460348075448 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 615763732 1250 615762482 615762503
    0x40804030804090507090603050c0f0c0c060403080d0e0d1202130512071d07083702043611091801030b0c040e0106050304151a12011401090e0a 63
    0x120f59510383c01c124031800d40c90b039071102c0c00c40c0d0345c040940030b89205896000b0322117418040c080c031554001003e071100c880c9290407070303580c2179201010814a50140e002a105010000389001000704140a20400004d10f04014000100d580030014900e07000841c0e507041150300003803090f42581b6030030b6020010380f100034500941203483d11409a03403410340c0c0c071500b8880c000c1501800034206054409038031410791601c130f90f90b41c2c2ea100740b04015200c8504c02010b4082c1d106240e45a42b8950390b10007000c008441e17820040ea50384c14101c400d44c40304d402c0c4446620140d042c11020180d0106201d03202d0300030311001c81c08202c0000b5900d03c0005406000040c44d0401268144411031110640c00203040ba03004031041d08107511195800017403031081380101031123280d4080c01049460301c0f980c0215400342c01180341c3d40040b41020f80307034030503145000c40c010711a070b880c07401b82c00c3d0a03c3c0082c0f030b40c1d0920702c81030000c00131848440e1224500c034030144244080142d407150048140c09042c02007086035a4402d41005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 615764982 1250 615763732 615763739
    0x10020c19030f1e230115050307050f0a0e041a01140f060d0905060c0301140907170604091505040c050402090d170403080301060210060909050c2107082401030201080f040804030804 79
    0x620000f21040c0341303007007036003071504400c0e45103c0c0410303843c203940e00a03014254a03030618060100c0450440d84c941d41000308200700003100c801d0f500c2d920740280e102d190312808001510451848018040c0c03c00481c64825890040c80ca654031134a001c0c181c1800d48141e505c0c0c1c40c0040000d000ac150f00c4001a04034080c81081004905011000318140d50740740c1e8004041c2c8691409110402070200c44950100c0c110100307510240ca00344420540c0300c00000c202040941035580c0d91602100f801c90080040394940c0d05110410040c0d11504001e030405940031400c0ca1000000101e082c80101c070081d008004090200c500005000308881c013641d0031459050352540c3d1010020366616078469004201d524000e400310302d0070840d00880b04466007180080c11040b03881400c00c06207046a070718070304040d4070039610f8445854007844410000c0c034004025003c0410a15a214a95802c0441d4070191844039001400142e812858468010740002d10001003039a80303103452141d07403007150005041e1200214002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 615766232 1250 615764982 615765023
    0x503011a0306090c0108010317090d030e12010c05120a062d080c130c0e130e06060a080a08031b0d05091005071e020a0210020c19030f1e 60
    0x118249001542103030b15981d1058103494680302c2c903140e02800120540700410103c5d00911582c003290002c40d0465207031014820000b0245100c000b000c9004ca40c2e16000040b80380742c203891a07070003079610328000c0c0b0130251051002481ca10400c21103200b15a403101c085440c8402c10361080c030180841032600c480c08820401c01d00407084c14242c0c1e00c040301003440c0c404120f440c00811810140c2001a2521f10302e00d0421802c0b0024100a40094040000010718602030303944040900a00c801800e43c0000d40b92141d0b5403550808400824040c01000030305401c04c0032020000301c2106071a08511007d07242d44503601e8a401d144c4000012158612000c54900410b01e048e510160007030201a044030300410360340342840c05544040b01d4002c00f08002042c0c40049409070f8002040318032507441581e4139410759500007210300050305000070044c0e0000d021000603083c032118030072500e08001040c1c04800d00d1035580400c16840448000d104170094010313003402424040812080652004802040f0300ca4680325 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 615767482 1250 615766232 615766271
    0xf0f090e1f0807060206060d14060c0d0b0405040c15051b16061b02010f1115010501030606230a0306240201050a090c050d29010623030718050301 64
    0x1c011910618000540c040e40040d00e1002c451294000d4000d60382d68608000b02044405401d550122000d25600c0d140ba405105042c8503800d84d516031525011099142011940003408490081d403528040c800401c15500e0024101c0d007141d003071101683d4198508030785a014401c4460088409020a8110381b00045a03070542480b030850000100340c0d84e210111000d14603000456412826406c104000d54800d8074100d1061200b814050640c440d817542031850031030740d188281c80c040b14980060180350381c580180c00041c001d0346040d1101e2041840c9005608151001a00d542c020001c0c200c13003414041c0d000800181019049144060001c450172074892280410540065180400040c03803406148140485680c010381058103050516090058806400c0402d64100c2203541c1c48504040c010012109801d03a04140d1036043c2d403500340e01904403c5039050f520303401800181c200c1481c4100b5410f0303e9200c48140f90920001c03d1121854940c5000d136007140350954240000f01004000c0c0e03030300b07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 615768732 1250 615767482 615767521
    0x70804050d1415071205180a0501061401080c120603010906020d050a1d0c09060d0c081501050103060e1311040c05040e0a02161712010f0503060709060f0f090e 70
    0x2a280312040c45100c00904030411191131020642000d003141562140c3c0d444141e10112000036041d110540720b11291428402c0442118280c1d10741606201d0744131002e070b41010341282030820003018101004c7c1c0c0001802100e44240b011b64101000400985d025000003134029000a0115070703c0300d1901c40300303000d00703403c075100841682000414025148981d02003860140050b002e003a401485ca010003040600c050002035000c91341c090003034041491401a03800034a4500000d12001c1ca1036052181e2203a0143d002c00d040c9440c10030b08100c1031401c002100d601609010700c202d00c4450b41c0c60304483e403454008101c4d801901c0d14100342030702c4c2d4015000b0000c1e03801003040f000c40c1c2ea4424000f50b0682c8500320554410084900000700092000300c184516249084d40541c100708000080d0b82d030740f6034260f100020849031030a00700114102800401d0300a100d07480c2c00c012046c20302d4000340c0000e490044038410480d0341d0300c0307541c500c0340303d0f4404c140a00300c4101d05030f203207040c4155085032440a289 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 615769982 1250 615768732 615768773
    0x1d070c1b14010c151503140a0c09020f030403030513050609010506042f03061f031409030c1b03031308070f0b040303210e030309010c1d0604050402070804050d 70
    0x7001d44080e0341c06846001100d95000000c1041c0c5089000001c01a011461107808060310a540210019040c411482504031203d00180120400c230700384074038840710301d90040703400780c2c81000388400c000c0d11041140c2e0312982504010406446050200c10485c00d20440a0101c0c010a002d005540506400c003500030041102c05205003414440311801c00040500742016208400a4022006400e80302950744518003d046000b4450f4417a030103007605180d001480002a42c89000da442d1000d0a0084c03a04100e81400035030400880c0030b01c1d1555885014032880c110000c00c0401da15a17a010011a0014202d0300384041144d03986909082d80c40080307004283ca490341502010500c051880c00782c8045035010703500c0c500601c40090340111100c11401d0100b00158456045081545c401c200a42c0100740c28400060035600c2c0361001410310942c10140c044840080940650f00c3c2c1d224401c1d1015a03208450060343c400103403801c68514403540d03100540008042c500e010600c20464207480c0e1110050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 615771232 1250 615769982 615770009
    0x10608061b040311150a0c0b010f0509040f02040b030a050106030c05150a1803020904030e090a020a1d03010e25090507090303180e0a02071b1d070c1b 66
    0x1503030807603520080100c021007004001c1c841000411100a01282080d40103082219203110350088450298007100391680800e013032485090400056068560050901007540030b2102e05040000340d410f04068005001c04cc0400010030070b6545640c031171820007200800301c2d65045a00d103400d034060b003480d1100740c0d00302ca003144000816003403480c2e400072050f20701c2d28040e1515074524401c2e0750184a086130704031800c03e00c4401000680b2442d00d1140118002e4480b0345c101d00e554030402005400041250368418010702c4034000c400d400c90015180c075204464208006000341c40400d004040707240843c4680e12035038140d80540d004007019162251400d02c2c1440c4200d480768602021b5402c1507036581c0000300070303803c2000403d200304d649003032510044d203201c2c1003650756842808030301d0425101c0d00c210341e900190100400c458000754005424808010950303131071520a5a0390000c0c9080002051400c0141c0060001403103109100c1449a11000901c1c41c080342220385408078645010729440d0b071071003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 615772482 1250 615771232 615771241
    0x60909061103220c090c090503100e07060c081303230705091306150806150d050a0b1008030304030c0c06030b09161b111801060e10050c0303070201060806 68
    0x80341d04072441641e0a55440f41903607488078020444034025502030300c0e100000107011941d94800d0003441d420b041203076111242c0c0c40c1003508150400c608204490845458505160100e0070b01003242800c44000703044c00860000103007003200091144d840e180213104910350011080010100c0381404041420724080449482c0000e02e0303599060707501510361300c01c1c88840040c50407180d0702c1e41c1c100342c0c41c4104008941190362a10114042009800003400740c1c001d10100301c50308003001400001004200ea50454080040d1611038681c1c441d40d07406000c5010040000e408400c00d07004040042a050040300e0345c034507090400402c01c910074a0102c034101103550b03000401612a006004044000506031a61a25040200196802d10038218410320440c01320040020b2108840d1804450241c030045184507940010040360400d043d8413080302c0003010005014107503002e8a0f400104c10180c441c0d000c1000c42c00019a001c0c0280304103559684000420402c100c1d40c10b4006800f25600e0504489403502c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 615773732 1250 615772482 615772511
    0x418060e01030809090a14160f0c1e08070c0b0406140408060727030c05150c030423060d0f0f06050102030706020702040b0a03030c050c0102190201081906090906 71
    0x3001e1001801c0160203001c81c0c101481c00302c403e150011021000000da40d044215940d040340d10031120365045003040c00c40852016040200e190b001d80b0986022101035880d95101d410b10f00b00700200000b40501811400704011140f4116000d035500708a200ca00c0c01e560b41603210965206000303090009020318542c03254034242106460a0b2030203800a841076a580d060121101c0030500301c4414943c10070000c1000003401c0107107000c0910701503c0b501d0011030801050022105116070f4000b21003c040011100204c5c002c003c0ea400d0b0303401507165981e0507140071080030740f480300d000e03080340c0c0514002507402914900794020401741c2c0201d01c060141200080400c07040703031440d03c14980582c008200c1d100004c0e050364001c1c07228501c0203100040c58501d460100c0c000c4840c0f500102d0101d09603816440503c8410014024240024402001c02030303055100c0503134040c26034800a060000c0000400d004004c0420100c42c907401e44c0004005641c1d80f10280b601038100640250340341032070500e0351881140c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 615774982 1250 615773732 615773759
    0x6040314120f0301051311040803040e241011010c080a140105090606071a070315171509011407120b04024902070209010b0304030816050708041806 65
    0x30003125501d0700310385c605003e00070b4102d442d01c04d913885d1a980c0c0164003070418400003d0310103414010000c5403202e041c4205c0302d402c0c0c000901101c071103250389101d40c40e10388072891400c140c0110a585000541c0700d11380c425281c042c01010f0220307195003040c0190b100990b121885621510094106009261028185405614080c0281ca400c0940c940010f01da5060810007400c05a100f03030b64104815031996400394508105413250b200003625615186075488543c4c0281c000742c00c8500c1c01a420400103a951640d03081200d00c3c1c41c145401c241c001809000b001e52060000c041e400c46060742c2ca20300306600074100e9604a000089441c60141561a203090a109564500d40104071081c001e8280b101c82450307042440d15160a10407075150200b40400500794414020400207101585568040c4104403c20005800c04540d0303440506c1040040380c1d000b0b8600341c100340c801404e1440401c02000440c3c841c80740400107485450002000502101d5a5891880248661408200310358030ba012000022 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 615776232 1250 615774982 615774997
    0xd03090c0b0c0c060a05070501091b0b120a09110d14010f020a0e1905100e0f10080f0628030507270b010207260606040b0a0608060f0604031412 63
    0xd40c06801045821300745400200401e000c2d0303045c402c2c1480341e0340d034505094070800320044800c114192825021100d8082009028012004030b644c140301101c40c0d03240d107120340180085525a12044040240101c0300760301c590314030003e0b024001201c91781c1080d200300498111003142961900f541500a100948240d40900290b40c1d100401c40469200f00102d0107000002444200344111000903d6a21010420401d204a07112090aa501401000168407840c54500e00585072080d0119001d90b221212036813103400e40344c2c513103280d482d8417000c900c2c1c1c960160303014004041c02c044c603500b011881c1140075040300c0c42042101d1a003600c49040724408d0f400140c0c1404025180b8544a01c2001542c000c28042d42061040700d1800b50b94140800d0072100040040217401c1601601d0022003d0500019074410401c0d1f6052012850701c0300840c01d522102d228010400002c2c1001c141c4543e91424003540894000706200c0e201c54603400c1614040c62901c21003a030324840c408010030f04000b400241c4110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 615777482 1250 615776232 615776257
    0x609061014070503041d0103120206220c0306020307020a06201207050903060720070e1906030203030a02010507110c1005030702160902030105010f032a110d03090c0b 73
    0x1840405050398019045110b0490b194001448040f501c003440580424510452642c4034280b540755041401a905044201900b10340084c0304008195040d130050300d04500201a54941d10417075030810111114054100411041c000414030191541c0000da154044c3d018680c20010351124500c080104800d00a070390000314000e00c0700e01d510b101189507140d44200301d42042ea06d85402c40001900f0030701b088a680d0041020b00c1e01c1c450b5150544040b6030203074028800204800c0c2d040c21080c00c0b04141c014081d034440b400150000980443c0354100600941e8080c084985a50550301c010f4003800c41100c0550020f00e99100b101d2002100103451941d5000203010445200754040b8100d4143c0e10013000c4000790310400d0441e03031821302c4d0940900000c0804110040c1c603941050001800072010a1030501058207181044110120010b4084543c1500300b04043c0000e40040094070042d03140320403000715010750b5a90004858141e000454590311402e6241061a2913040d0b000660003151100c904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 615778732 1250 615777482 615777497
    0x150807150503041a0903031902031b0a020c1e0907050304030c0803060f090403030f0c0e01021504170f0304021005120a050705130b040810021c0209180c0306090610 72
    0x654038010402190424044c1d100d02c0c002031061500103403004400e84050300c1582c400010400f12040041122020080b60517007513244d4204104510818414565006000140001c850a6140c000c10440070f4040d000f412116a44854a0030504119140c50f0038500406180000030031b442d03c10741c00c80e4411030f4540c0b92740d882e0382c1c402e40703410485070030040c0290f410120300b00500340c4558404089034806e0303201c0d58010404800164003001940d202404031024080503001e504087ea0700130640007403e10540c070031030302580d0306d90501c80080f0708018140c150b07699001510144418011000350320850003079601c0405440130b00b03002c44680c410180022041454400818045c44081e04001d400c026030389003150501400f05068003c042d0b40e079200b0007251600040030045800140311003902c01e0700d20542107091504030704803100004169840600072550000d0301001c50f43c0c40403d042d020300c0d200099100586451800781c5281c0c3e00030303109a032040c05070f800020180d1a121301c034804061901d640307454 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 615779982 1250 615778732 615778769
    0x6042027060720040920100c03050c010b040507180b0a2f010f0b04150e04080a050c0106090b041a0a0b160602070606050114070308010b0a020a0b0406150807 69
    0x40c02c0a401a01d200007000f601e800d1480e01d66034501506807080d00800482e0800195001c400c00340481c0c01040740e01804002481080d1660844550b401e240e8042c203183e41d64085600d02503005010082080b03500500c4c00091045556000c60000d20b0300300341c109207005440c1ca9581c456050b010301440400001e885e01200d40b030a9030075070306a880b40c0c88141e040c484072410a00d481e45c203441030000d071003612a03501c1c4880111450030340100e8101072411744801c02e040e07050603800110114000e0002c2c1c45158001903844e0118442c10031920102000b01c000c1040701e0319100c9200c00b40c52550002d074800c42c1085041407902d841c00c0c40c240c00b80c0400410b654120f502c0d0101216403900300d0207603c42c0b81c01d0700800780c40220b0301d230780000c00d00540708443c0054400d04100c0091b205129941002c0c00501d0148000000641c10454040c159101c0401c01a203515841008074589009242e0040022030007000b03010400440c3d4000c49010140d605603100e82c00c0d100e07041665903440d107100e81006100d0602d2080d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 615781232 1250 615779982 615779993
    0x14060705030f040f020d2a0b090619090b0307212d0908070503030a05010e0c030a092102070504060b09060403060518032b0509060609060420270607 65
    0x5031a140e1003d00540450016510303031f03540220301100b60760000c030404082412070880d0700c00400c001c1d15100c2d0b9034600748211200420894003c07001000c107a940c50030b0b20f2103040e5006140400042008440980d40c910b00604024250040c400240103006882c038080b481008081c00345031140c4a08001d07511011644d010114102d03090b0000c0c2078801595000d144000c1140354004001060044004690f80c0c244104100200c038816400102070070550024003640d11000000c8039041a99031001148066803030134040d40e000d1850304070189003000d1030021118560040342c800c0403502c08a0f0104540340d990002000144504148079a1284040105000107885903011540200c1403001a03050103840050480c5541d020396410714503100201d40f114500d0810300c0c42400c0d442140e00c07042c0a036043c1f03811000d98655005c0d214034802e00d140c000250302c6449031303884452040c000c2e120b9100c00c0e1055001d4074420354850050300000c4807284500c2c0455942030003e510fa001805000145841c80c42c0e1500d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 615782482 1250 615781232 615781253
    0xa0f03050c0f1f032004080a020f0306010f090b1f0e090601080c040e09010f240f030b0711011e1413210e0a0608061c2d06050414060705030f04 63
    0x4c9140d2854152084460b403054170094005032010a0080c54100f04900400034138500b413a2040d8825400440103000094030074005c1c6044624591001c42d40340f40540c0018205a048600000c01007004100c603200150300144d00d00103440241d9212440351540c000440305c000313003100c6240d54540208410818008a940220b41c004d008800000f405415554080c06880c800d08501c20050302401d164070307074005103d1400d0028858080d006210900d1a9581e040318000200244248055040001c004000c290004088040f08101100003990008202002800100c2001184100c0503002076164007a120803404c40541044020034030086581800c20111406494041000009101c0030303499200d2002c171a024040a40302c0c4442d80c90f041c400d0141404481c0320351083d00040029880c0851a00c2080626080000d40115840040503050003440d50030600014422032800c801c120074040716503840c0d181c140303510060351456194240112590302040d40d0b446c0e15001104040b40000300000803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 615783732 1250 615782482 615782501
    0x806031c030e1c0f0305100b0901050d0f0f0b030a1e0302030c030301080303150d020108060108070c0f0606030201030507090614090d0b0a0501080d030e030d0207020a0f03050c0f1f03 80
    0x7004034012076140440c500309440b21000210601e100541c1e800210b410160100c840a107919040180f45003480d00385800f882c1074032901d285084009840c18250348214103c80401c459000d00380308683d8040c3c03040005200c2034a08404462408900020701e140210300c0c4101c050304401d8851030342c0758282c41d00707411040a64080b4194442008005400c40080c0040c1d070003020b03100095030312894001443c507200b00307102d48068813840860400300f0040c1c2c0c00c41021500001e0038604212543d40e00c03201541c2c8806a017070b016004100041d802410440300d500030300141da100707a806203e5600c2e044000d46210072280902000325190602c20320400c800750002d007000d420010004000f101203a25020414402501c2c0409441d440e1401400042001c00000450794280d1804210407003030f07510b40d141c80e0301800c03200d1010715400045400965890940d43c1e0081c2a813403552020031a034902d02159241d6180f80410b001d01c0e0300c0004204586450380400312101342c0c0d420340040720304050104030002c154212 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 615784982 1250 615783732 615783737
    0x3090109050610050306060d050d0806061e180a0b1606020909070216060f0e01030e0a05030f032e06030902030703241a1f0509030d0801090506010806031c 68
    0x1101000441c00c10868180101d0440301c11145843c00c04040c1400c10303000070821400b0b9069501c105001420000d64081015130504d41001d5903111400014001d00c24868608086042104110400c00c25040103202c11403000c1d90707031849040c00ea810302504940d14410810110800d1002d4840d085001030b00d030030184c1c81031200602c0c01864000061144c4410340b28480140d002d8444ca0310030032601304003900688014180422600f110301001403503812895451070400da242c11510382e000c041004803802c0ca650040030f0b03d480c0e8602030074038100350708212500380506408480c0b20580c2c0c10140c051200c18210b401c901007000d0301700341c42a400342c0b960000482c0c141c03265050010110f40c510640b000d141400c1c801c00e0034815403c603544000e440400b803001442d1400a01c00d140c01d941e803441078040d03099031079030307441c4012404e140240c540340030340348009425000d0b03035807191038850f84001d01c039060b5845510304101c245c07510001102d1026041ba245030b00356100c1c880c00b407a0585400064000c20000d032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 615786232 1250 615784982 615784991
    0x140913020909030702091305010e0a0503030a0b060705030409020a080a09020607060c0507150509010c1b23010c08061206041a15060c0313060f0516171b07050103110d02030901 77
    0x2035011a144510860343c3c0036031f66545d40e4001e03003000030a003c6c41030b0f10100c0d68010030040145889041d200c1c88081d0151040f1031751070350a56400e444160680c0d4550b5080015280c44030380c2c2d000c020003c1e500c11140000090b0759900040d851004510401c6000c2d90040c2038242044130300c0d900c2c00020702d1001030703cac2c00b801018443d02c07000a802091403500564044004169400c020010a003940c1c444080c0805011072710f000c1ca0580c21910603c0b584140d0440c91384050740b50b031a601e24410000d4414030a50381e5090a498500c01604403900038050034041e9000303803c0d400511301d40d507100e440c1528014580070410b14810884e141d600c0d008c1d604034a04032040d010300c614001c001903076503100e007007510b010f50030100d103d600b01080310804400414560510300c0c002d41107410001c1151023654150050180504071400078411101c100110207160305404641e2818240c0e00384c80e190b00b05600c003001501ca550004595548607000b07103602c0141050076141132002100c1000042d40000b07040d85e840f50342c0c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 615787482 1250 615786232 615786247
    0x11d060a03140703031d0618040e0303130308010b0a05090d080c03040603090b090d0801091802041805010f1109010c02310b01022802010c02150414091302090903 71
    0x6200c6002c2d00c1041220041810fa850b615000d8003444024451b60440c002560101c0c003103803200c001722281300a5406082c180d41380d04c900001c0081142814180d01840f020040000901010640070704039406500d032012141e0707079001d07800c0e480c1c0f10b000910750004105001d00e1405092101e8900841441130024500740030100000601e56002a80003130700083e114107152007400b003051441900414644c0282c07000541c58100588041c2061286024590b40c43d80981d50241c96222401c1c0c0959004100340448003c1807017241c06a05100f6044c2c5581d46441601c11001c4141d205143d440c3e4120400241010940d4005407908402d1003020798001920030a6940c4d2000510042203507409080040f160f240d0754030580d102102c42842c05c1c03a056500110482940d00106001c040c40b11941c50141e038010000e510040700c130303d07004000081d00710408258a102201c9a140a8000d03500e0310024100c00c5003c080800040b50001d66000700d4002c0c1c03400300030025091014019030301c40c4150381180e00c4e0405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 615788732 1250 615787482 615787493
    0xa1505071427100e10231b0706021b0a03061812050a020c041e0c0807030b0102011109040e1c030c080705070b0c0a03060305060c1b06011d060a03 64
    0x318049079801101da2800c284000224141c240b211401900c0c512495180c500000e0400020b01c2e080b0b0303210b00640f000511034144a004202d417074482e4030044400801b000350403455160419207005a40030303044192078a08130000500c0340304960603030b0700070144440f81c6401400760f805072800c4103030090701250000c0003081c100d0143c3d403240601c840c04c640550403682080890480a210041d08110013005003d850303e90001d061886650102e80019000203244403d1220b0820141540302e138508080c00d001e02c0702d40020300d6034820390032910280460303600ca00049080700d95101d0030600c100c0003480b0b04086400c180e40316120074007801046841120f200030103840e9215008040500103a100c1c00350460895002d510180c02002e181411414403500c1c0d510303000c0c5014000e11050746a1404240e075045584030f500000021600031080d600b81d82040b04460030780e0703030100000700d01071071240800711804c0e0800126035040303480a201d4400343c00002c00c40c861360144e002d001d8541c814032640c40400802c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 615789982 1250 615788732 615788737
    0x203070515060f0303040e0a02130e07030606030e2d16080f0d082203020102041208040f12030f0c06060f1e0801112b020c0604140a15050714 62
    0x81510521066601d00101040300d00f00c0300c404031a020340c0062004005400741c184041c0e0300b0600400001d41c96016207003000038030700c3e4594021000c4510306028804e5160709503100c60140c2d0140da40601008514007400c1d640c4880800b8441c0320000000c0505a400145600518001c000b01082e00c00c10300d940c4040b030b2035504503a0071000554010744641036070140100700c804a04403090a12000784d01c0c00308407e5681040c03004003030740c00b48603d5090004240c801c1d81142c003c0c0c954504000b402e80c0681c280110303603800c1030040d03c420592651020601c2c5a15020f2605c4d0036134103a9400c881c4d10f941c0303007084840b20800e10040f02d8580d2103240106000c840070340301901400c02c002c24521112040b000310358205c14958000411a4900f41c1c041914092140032225816103e5180890b048405c056000c40080c400e826032482ca480480c184002c1e100104109000724007441910701c2c02180e006110b900c07172200503c004c02040702c051b40d10340c11040f942c001c02d41c05040b50038011400c5030301e10b10540499 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 615791232 1250 615789982 615790003
    0x1803030a020d110c0108010b0d0608100c020106090510060507050a060f0c082a13090906231005040b060c010c0513080c0907030b060d0e0a0b0703150303030c02030705 73
    0x40e0800c0414000443e80b00c242010240b280c01d00401c0d0b40c82e0501c0001e0319440040c0100200b1050000d108005610540c00000c0103241c3c6c90104c401c2008182c010500401e00d4422050041d42080400034940740b481c09518000d56840300c11040c2070703160141c03d079402d03807040d00210307018000c103030381d03e0041200e034813440b0014800c03003802240c0020076510080c1a10710092841c1fa007012076440d45409003030107400078002c40e58050039095690000c000c50b0506c2c104a03501452500f414030413603004019003604035000b07083c002002e44034103581c10390b00c000480342c0807101050480f50554081069150a03000030b0704451025001510b80074900170f0b02800d480078101010048bd80005440324112443d41c440ca00a00c80f40c8080d0131000d20b1000000c1118101a040340304158655942d0522903440108990180c600c00c0400c001c10350442211544410005000342c941c1468240052800d07030107030080c0c07030a9412801942c0d144a00b166015802424850005030440c40244081030001c0c1c8100f1242e500d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 615792482 1250 615791232 615791237
    0x7080f06040213020309060109020a0c05010e0c180705161403070c05120f060a050402030c03071d0c09031c031e0501030606150c1709090406050901150f05061803030a 73
    0x5501d440c0c0148000040d407040281410b41c030400400800020109070035065940100c1d01581e02c52501c10111168901c1c000c01812a500e08040c0400460000900448100056519800188509510302007104c01250800d02059003003000c078030342e004141da121103064490804c40307240280d9a208189103400c0808101c89100c1301803400d010501c0d0254080045040c1d03072008043d02100540220b4840310050600c1218984480c00b050441d9424844042030b2440a0111902c1c0f03903444210000310b4440071880700404440502284164014a0445002410180082c0125001c080c064810f9070510b000000070943d0728080c034042003600b0340c0301c410b2000f028803010500b0350550800c0360071200749900c81c2200352600304041a155412030f850003c0d46070044210140782d007680030400302d0392241e1508680c0c04074600040000b0070a1aa22440c041e6544a00803c5035001070f03610206015000c3c094100d500b15000b030108520b181880007850308041a0311218a00c0100720701192031b603002001500301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 615793732 1250 615792482 615792493
    0x19030209010e04021305040518120720010c0305180a1502010513111516030302071b030201140906070c120209070302030103150b041506020706110708060c0c07080f 72
    0xd6682c041070440c90800b0449045203040703040c101c6145026464400c50b40501d840e10002140480781c4410035005450740e005030b4030180c8030460000c01d140d1002d0400c0700c102e5030014480982c00107070714003040781000684440426003001c0c0c03416680b80d00f19800751841c80c0f004101420391900c0703103010100100000daa60f454044070f5440041c1c00c1d1280100000d00300d0000003d2172003c500440c6078038403205029543c0c4d0081002c9682c40c80d805202d105c00410361150b4540000d0b041643c1680281102406070b400310308840345448031318884003910320000c0d000035000c942250400d4640e400500292a000b840d0074540841581c0380c00c21289690b0010111503000f83d145019401c16440c0103601000c5490118074540c110b582b110b1a102041d0154904140c2e150000d00d00f5442c0d0342c0c000124001d050224031906c1e9503030040290383d070030180103450015109003d9246641c900248003801c3d2070012001e0480340e0350b80d5490154581040002400d944074825000600c2c6400380440306486000e20058171 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 615794982 1250 615793732 615793747
    0x409060b10020c03210301140d050604080d0b1f0f0e0a090c030507050a0903081305190305120f120603150405070e070c1505060f0a090b040e010b0d0807030203190302 73
    0x50512003131004007403550000d060f078050352194100481f41940c041481d280c902c2002c01c0c0108a591031030b40e00080c1540704440c181f000b03118a034000380c100c20307401e000c0500100219005104141c2c7d01d04100301c40b1074541d1031500a401d40940d220b80c0e108d4895103400190110810001030384a0800d40c07101d010160341c0c6051210700c81e40750107001d5104080d0709000703240c02070b01c5500a04030301c5148409000720780e010441c6c540c2e50001c914100020031000341148120540010400754140943c03208484c6807054940d1000901e03400c0c0207854062034070a920a080002c04911300c1c00b00000141083d525000e036442c002900003d4800d224040c038042d00083c24594144503040004003030242c00c1405001c0007000c1840000c100940260405504a1010a5903240d44001c9007001c0c035072070312040d400b504034000407403400003c8d030144011040480f4240f0010710801d003403d00300ca0240281903008251a1007250100d80d1440013007403d01d12038411a446c240540d11005040c0c100464003c2c0000c0d00021603a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 615796232 1250 615794982 615794989
    0xc06071407141c1b0620010c12021b030c0f01060b03010e0a0f0b0a0b07030201050f22030c0204050a060611010c0e040b04140709030c0803070201020304050409060b10020c 75
    0x1002800c00d01807204a80101600000c4108a0140420101d50038801c5488208410202289001c1c603da42e16540c010780c031044060616501a1303a0a20301b07100300100000c09a00500070713034800003c00e485071150340b40010b424070040c5d8440fa046182c4459130680701680440100010818215490007034140c2c180070580c0c550039511a680300d4210341d18240014040c60201d551016007120540100160b0b40e400b12000c030000d4540b00c5105e0b5031010080358001190b880101c0246002c5100346c0c000c110070740d00c1e110180f040d00c0043d04c004140c1441c41c00f0882c3c6001918128008283c0281400c0007a41d180354009810354104a60156855854400411255800081241507003080000901000c041d0900c02084a8052228144500c0d20303019003807883d4039241e100a440300c142080c5941185400f94014003110554401110502c0e41104001740d004d002000780d42c14554168040d51030145040304002c080e01c0d034034005a40603603807411145081d41d50320150042542543c2c005e0480c3c2c0c007500042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 615797482 1250 615796232 615796243
    0xe01090b010e03121c0b010f0c02010c02120607030605041a010503101806140d020130060321021b040c0908031908070e03120705070e070507170f0a110c060714 70
    0x460984030b01b801c1c02d20700584e03004515032040564528202030014101c8c00129201c405100e0080d4102d00d061841205100c00410303241c1c80b4070580c1e1000d100c807964800c144821910281c449a00081c0040a8100b1f29807141000310780040c0c442400340069615040000441041c4005460040382d48034800c01c000c071020b80c0b03503030001c03042110405003040d00fa4001a010044403e004421100e03607031000a4088000b48940d02c58941c4d02c4001c200181c0c0746e01c0c00012845401480000080e12071010200d441d100003a094100c068180d00841303202c404070103000203003a02e6168601442090140800e03001e1040025280240d20b00404d041c4502000341c0103400488050820000c1000301c1c0d000800350f40300010140360b0f001f42c8000e0b00c1c1d42e450075401c110741001201d4110001164420042c898070a0340f01000c0d1044500550701d405008040700c0044a091180c03d038030b181055414030003c3c0e0301710b0180c040302f9058601007082e140c141c0820b10004016900c10401292005044e100080312104104031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 615798732 1250 615797482 615797527
    0x11509081e06100528090903110c0a0b0403060509120a1e05041508090a0503210702011505040903032d0b04020301030c030f1406070c0209100e01090b010e0312 70
    0xd405000c42c00c0202103030412010f002c5c04225502c690090100c1030070842d909000a1070418000c100c20f03000752500902c444030700382c030030042d030301c581310080ca0b00d80303040c5450104503a8840600e91800e491541d58802520f001016410b00b0b000b8000d9400c5503e058100408080c8250341e10940e604086a2001e00100c011580c01010450705000c14404503d503441d02d80503080380350074803203215945c4590340c0d40381245c200e00c0282240008204d4161551700484c0b5180300c083e02c06e04880c15561200360483c2201c0c60f416074504940c0e807400c0308001c542819404400c10900078500441e00410502c1c12000c405101c10b11003030020407504095040140c0c0380f2540300b0405d0221400d41ca19451a221104e2503080c0d0300016111410400520042041440e141c2c101410054283c0d1a24685039002404181050b00e007680207a41002c0020b2035442000019000d0300c00c4140c0c2420343c0d0b400d0030717903650003802c1c6565000d05001744c120410341680e07030410501480011043e009076a60481501c110b40307500c200c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 615799982 1250 615798732 615798751
    0xb1c0513080f180402121008060708150d020a060e0a0812040306180605090601061103090102120d020d11070203070602030a1b0f0602071a130b011509081e06 69
    0x4450400007054a411984501e0003481841e44461502e030100480000a000d074a82c444c2c0700041c030124411200c449244100741060001c0880b6984861003602c1c1d11045031001c00246071000003c149003020082d003e02c41101901c40000380565a0208003003232016000039000c260440320409103483d00e2044403001d42554005840340d40e1001102c42181d01490000421164403010f0b00c1996041002600c003c180c3c011000340018100348490944520003070043c2c20005031300c1c030704030110b4000020840e418000181e000700440701c50076007580d540d90060040f08403481d40030040c41c50030010501645541000071403401e5074403415072041500e002d002d6406081950801d100c0100196000040d2428103080b5510980004c0814980000c1c031441002c070050a59201040703850500210800d826505511100104030640714640001003481d03446800525281c043d80040c40034030301510802d941020a03080203c2c96684840c0c0355814840b640c0601d04141030008060509402c04222044d00002c604 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 615801232 1250 615799982 615800011
    0x170a020a0f030f08180307060804170708091318060515120615012001050406140105150d0906050405030703140a08010b0a1106100305060a060501020d0f02070b1c05 72
    0x40c0c0e9a1501d29041c2d082c0a08070000c00708480c401c0c041c810b50a11100d200042c155140d1fa42c0300d40014150f1601070707405482103002c1c001c000c50014132035012501c00a400c500322500781091401006141095070b010804c01035181c00d0a0042c4001040320034180622900000c610b515000c650940c01e850500162840350701440d52013113001001181991b0030100c01015074024441034001a280c0d000b40003014034030000c40b5500091440810740c4514052803003004148501041c4200b001d10101e420f0207131950085528000304808180c050082403260300030722000c1400f0300ea0b6210042150000c03581a03e1580000980e401059800b280105c149035540d90780c07030305000b0603401c0109078500501610003a50400108140c078203001e035034001c03403500d00d02040f03c0aa00d041c215040f1917084502c01205c1d680300e0074012600250290150b1020341d036040e40100b0025094201c1242c0c4c00c0e20700c1c1e800c1c0d03096000d1000007040a40320382e0000e040d003008171290483d12000b24291841150f070018080303030209114 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 615802482 1250 615801232 615801239
    0x50a0b0d051509011e050a0905090c0f1e0f0d030c02191d09030c01110d060806010b160c031202341502070f14010927090c170a020a0f 59
    0x343e02c1070b00d054403041a441c2ca514102c81c2c40c6146203100e990025035121034007460019000006030000d6219504a000341c900607480402840b01300c0d990b21092a910102069081d901010340d6260464000c4004050301168400c20003c512135840c20681600001c0301c0143c0103055040003184ea07000c035407091f1815620303d441c1224410542c0d90320303c902c1c44125040d40100d41011020016a5854140e9a0007040321040001001001d540514120248142008800950840040b0f015412108540c01c40b0b460290404201210800a868102d84103441070308040b0105801111140c0c1000711a00108401400110074492244030014125500e00c10103030364104101e04006c41c60110340c0d40308204000b210601c641a4244007854001000d548400c500001d4a40d00380c455880d003070719080e01d50b40315090300d407007240e0110140240301c15404c0d400b101440c42c01146a038041e01e8207a00030780030800103c0e210140240d502551103180350240d8404040d000c258075241008000a15000400d1402d8901c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 615803732 1250 615802482 615802489
    0x1306080115171b0103090206130503060117060a050c040312121a0d142a0a06050a140702150a0c023604060902090108030706050a0c1d0109050a0b0d0515 67
    0x71050b100e150f440d400085100090b4001d8021111440e8001c0c50300d80c50b00d000408901110109110b4a44a071080500004010002482c100b038440c0010000c3c1c01240c0d01c030b00e501d201401000d84103410280d020000000440c00c0c00e04001d0301e07001e080e038501c540c01c0d580e81c03510019030f40c85c9200c00b244400b50b0000b141c0140c3d201c02c9240d0701658042040e6640c131400b01c50f03190030440186450015900c0503d1401c50240201e844004011000c6800420b580d481e003404644c240249002c3d0400708441d0000f5100340c402e044003800c40184010b11700b0950803c03507001e40d2040e0b0403a2690b41c0c0802c0780030511740114a8000c62003658810050314800c7e4030b1071414503001a0b124034103a42d80e49400d5038008107061003455046a0009a0080d10105c00c0303503500c2011a98070745c040c0c0029104103180c00042582c2e00e0050183c0404001b156803500c10400c0d422600310200c0344180c43c0541803180c120310016880c0c4404911350020001c0c075001549540300031b070f24041601c0300103200a400180c45914100c4c20780c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 615804982 1250 615803732 615803743
    0x60315050901060f0e0a1508150c0301050a06080910020d0204080c1f0c020d08040b0715050106090b1c050403030e12040b16022106070914031b130608011517 69
    0x2906013000d503201e6240c2d0a6843c0050a081210a10b46940345401040c0e030708d80000c82c10f2030104201030002940d6549483c0840d5800300707000d41948944414403c204003441001d609402810718800c0d101100740a402000803640840f403d14034807074000c9010841d4040c2030000c214446401d1351503800040d4011f81e840c81c0900d9020395003051240f102c900c0da040d9210000b0114072650b100c50499580d40c1c031181c002c822900a00f00c2115403c1500802d01c1020b042070084504a481c25100c1c0d05040d410311407100050380080d41980501103007c01c2c5051510498000c0342d0180c0d0003034500103200407014a285042140c0d16200440702c00d0200300800c481e041d254211401c000780011210440246440000c204c040d455a24080b804884041c0544100000ca10745015107825142c80201c165140124908c0740c0e2407203082945500252404110300301d8910034120070030801006600b40444040b07021003201c0860b0032813041e6030356803609109581080b840c22006001e000709282200341002e0b0340d80d80d550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 615806232 1250 615804982 615804989
    0x63607090b070510110d060902090f030d0518040902180a060801020406080a150b03280b061b0c030708070306050f01050303070305130e041a0708070203091c020301060315050901060f 80
    0x100c3e40d80903181045442401a01c44406c4254002e02010b03949000060294201154192241020150812880c500061000c02050590320b56500b070080b40a900160603114005042d0031070b481c0c1d82c1480050340d0740301c4e06480102000c1b040902d9400c0202101c2c0445085801ca14802e0b1f10400050103910f40210006511890111021074589006000300c0c040c09051743c44a2f541100101c144241c0c00306420654000034200400c1c00e2502c00794910035020f0700c8a420000da040b00040048000880c00c0c8404816480e02560032203014a00076070120745440d15980c408441da42100e5000e10810001e4040d02c2d412461034411900076504010000b902d9200e04c150040034408000f1700c0f01e2030455515158001480700d003080210a1030b05042112207103444642010644800400141210340510b1415000e140e0300d0340294140303280c10042c000d00c1c00c142400c0208241c03a100104006940c2400f4800c0a14410a9240d00303040c20040000180c0b41e02402124a03641008401d200102e054000c0c041207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 615807482 1250 615806232 615806263
    0xa0903240f1a012c0619050a18050a0314120c032805040e07030f0c030204050102011b080c0c0f060406021b07030222090632010509063607090b0705 65
    0x74134080740060524452000c1600c80004011000078500350894081c025520090300e503180c02d038007144080c2e00e04480c90b020701c0f0703440403005405001141c108046031404001c0c0c04100c6130356110700c0e022000560480d5000100030ba02c0040c03139144c0752020010350356000c280849610f02c00701706e028001e03042d13014a014800100b8000d01c0040c803030b5071190308013040f4028948402c000d1038980c40c00c024060350140c0512400340d800d2007003000882c1001d81e00780c40500c0070b50307881d1400380c3c544011701451070303000307070076a00e0b89120341e010f090640b0106010550049108400060b902c04200300204ca00243c00b000150154120b55010005a11080c10101c054540c0704482c221041a80502c10014a000360300030701990310b488a0152490508407403481b0400401103a0311140710401e8400140311401d01845030480c19010110301981080b00b01c440030440400e00700c0c4400010184002540001c2078048403c10800006000b41c55421050b114054400031404601c0c00da01e9845982d42c414061000030301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 615808732 1250 615807482 615807557
    0x41b080402011206061e0e010e1201061d090c0a060c1101140a090810090c051207030f0b190e031806160b01051002030a0903240f1a01 59
    0x4582c441d1009070540000890100801e54030740790000c24076800780c4219400c0700c0c1030f41206e443c0c4501a400e0041d039100140c1d500c521400d42e190a101d10b0034010031440525649840000c00c0c1c1c418046222420b1440807104458186803c4c6007041c5040c0c29151003a002d08550081404640e40c800c03505210582c00105c22a240d6406c0c800403a001451030160141c0390b680407480e1844903038407100b034108070b031040011107140c90146201c41c402c50703080c910300920101c03401c40100911705001010041a684800513201d42690701e846405010700510012900020a502080001034454064004503261071204004c0311100c40406030360b81c0302d680c01505803c400140d005105030789030000c480c2c150505049150140b034083c03801660814080c000ca520402c02c01001c61a010710000c2a103102810a41d940250145192101c3e13144d80301c17035045106045800c009020094103a8040c000d05419034a800003074180e042d15111100f10042c407281410031072920702c1d044121407072030601e003001e20b01940c0222 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 615809982 1250 615808732 615808741
    0x4150e04060509040b0f04111c02010305010503060126010e0703150501080705130e07031704171903110106030f110102061e01062105011d0708011d0702010914100b041b08 75
    0x215142c090103410346c0a219840d150458030420400c2ca4481440ce880078000ca0b600c550403d61607180901500341030f11901c000c44048040d0429500444c485001c00005100a47d4200d42d03041080d5a00f060320341000a03840b0305205045886110b006103804005400a80c1c244000200d500381404004241d15440d4820313600611410312071107008582c00304884560403940c926000b202d800a20440c0280c80c04100c10400b000408510f150292218041445d1a122170f0354003134a804c013042c0341600a40d076030340f0804800036900c5106034121340c0c09aa20316540040c0c8000080c6020801400e0b01014850444584440914450300d6819106d860030f2150700380f140c60409580805a1506248c103050074000009081c403c1181c0075004003130546502002699604d006807070042081c421040184203c0001215445d440c04402e50444060310004ca0217a00984940c03c6000080e401030b0180e8000340c004841c1c49280d842940319042007070700c1c24030810b15058060a4000f40c03001b50311051207003540008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 615811232 1250 615809982 615809993
    0x3031605030d1415030c0d12180618080d020c0906010c1b05030118080301090518060711010612020616061e14070801080c1504150e04060509040b0f04 66
    0xd03044100081003c0104404101e00f5122202c000d8480c140102d035214070301043c4d420049074541c001c0d03001801440740b0362500d40d11680304480c0100740d2410444601050540b1041281c0000000c2006550784c07054510000c0402c22101c140c0d9000c080d103984040ca15005054004c500300a21000c2190101c8085c0d0b640d0700140c40b01003c0003002400c0c0350f90303146000d010300140c11812040e9982038008200c4880f003d07400c5c94080b1994400a440108140010401035490303410581d0300c0b50b4155000c3e280703000800306240c0b038400c0c25104400868200c8903d1041c0d40c07001d1003420000c01d9100a03c10020201c0e07008541d0f10f00c240e5418010441000045900307121190b040212002c0d020702c20010040d0302d99002000428161804042c3c0b002c2040200350024445d070f2080341610b4440340a4000354105604110062004194041219205100000d40da00c00c1d29210f00c41030036651140c0300504032680402c4100c600d103400c4584180c11190612001c00c0709100c15560004008801050796203860901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 615812482 1250 615811232 615811237
    0x1507020a06091403280e0a0b03060307150309051506151315020304030303050709050f0f0d080d0605010809012c030c0102131721091f020f0f0c0303160503 68
    0x54102a1100050420425010301010041840c14205d04280d449800341c003240c1e200c1503142c80541c04882c0c80700500108426600031030f0040720080c215803d00b0364a40007543c1203100d081804005c04d654407844414000c0c00d01400d00c0c844d074220005929860002c000800b04810b1401142d114a00480d907429140000e0400001400140d14481d982408d00e0700002c2d9650f00074013085000a0901010800c010f004980300f00540d18000c21440380c2c0c0607120180280c0100104d1250303482102c1c900b84a01041585004260b04001c207400072621604040c000b400d5410007a01e041c0e900c0e8903220f50503e4590580a419613403903640308a80001001082c10149140954084015203500c0041e591555014034080602141d00c05601c040880f0307122034055440f611840b507480038140c4d0882101544e94030000c02003520041c006c1003102c1422503000c04d0030304010045201c0c0007590204100d003490b00e108020204601260320f000f02042005140407030f40340d0048503c1050038510b560000010440103106 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 615813732 1250 615812482 615812513
    0xe041e240608062d041112031e04050f03060603030313020d1b05041d070501050d090501022d070c03021306030812011701090222020405030706020307051507020a0609 73
    0x115403141c10942250b41080a03c1140c4e0450391010041c140300a022076080b1a03c5981c20104d000c032044108400d1180511703001c2e45403031950104104603150b081c11200748184001c1d001c01c140c0c0d202c3c0e00702802c2c40060703511040303002e00c00c4c0d01c00c0d070801021b65000011030740d0060998640c080e210b080391001c9204525070880041003031100c244c9000c02c0b000180c0f006004c5078811907040c4140c0031342e0221000200740e00e1140541076007200c401404554041c800034542d200d40090001003021607030315142c4c2260000c2003e4210b010103288036104442c0d110f40150030940141464518107051a41c3d04c80741218103100080c010700c000c21083d070412030f0983c440c0004580054525940303002d041c41d90540303c0b04c00d0003400090808003207240319801051088481541d4080c013132044001400c40050081a50420307451407141d020080459a910140007407802494113800a54941a0038601036041c484694018803440c19803c08102440d0750010751511003e0b0414000282d00c01e00381040a50b103003403200e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 615814982 1250 615813732 615813749
    0x1021c110c0609150f0405030307080c130806060f04060e070e010309060509010b0307080615010509030a06090c140d200310050702030406081602062805010e041e2406 73
    0x1810050035034400701c0c042003910f041c01305069180d60703102075407070702c1c0c0038240e6024129500074000a45403a0040030015000380c0b0095019003090036031000c110280d10b8980002500360060b00601c505414031054803101c4100488041c424203040090b552901c007001002c4a040008098210f170090340a944a40082500040240520318001d403455028101e10909c0d180244203900c40040e1814020560501400c00b283c04003140e80340e44801103509400c801070682d4980201140700d03002600314803584115500c1001c200903244e18080fa1682400c456554140c015150050010700052010049c001d015404000f030107150745002e00440d01d0300350345107001035500c0d15050a0110198000015204070341c10390ba03072560551b84001c01010b07040342d0550044090f9100e8800314240c01c3c072030f01d44244190b8440b100e110081036000d4001059134020307804111240365190078042448090340d00e10f002006442c1c407141c40d911981ea0350307451040700d041405d03850448161800b48070700c60b02d40003d03005100d9203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 615816232 1250 615814982 615814993
    0x302010b0a05030a030516061d0618190206040e09060612011401031e02190513020711010f050f030c03060103060608090d140903030417192112090501060608070201021c110c 76
    0x1120180001c911030309c00c0c40c42c070340705d580300180c2401180907801408500d81c0c8040c2c440422800055511040b000e80c04990154040c000811640c03d03940c50f032440b45a00c10700030207607400c0800501482ca0444c6810000700c1e41011400301d0f0300f0080e10001411264070104e281c54a00d244200c110300311105c004020350145c10b82d84c1c3c0d104840700c84070340e4a0548408030361544901140190300c0c000c80c4a154801024102c240c4401a1158099954030701101d030541030462610307001c654040c000750b00403214121070200100a01495503818810700c0302809040c28083e10301d0400c0e03002130355920800702401303040090340006000c1c000c031030000b80c550301100a01200d071601c0c2c55040c0808406d200b406590b50b02d100303001d40c0c418441c607800001022150001c540440d41038401d0200400c20f030074109080140312065610320021500380c170030340000034081d000014035141800c030020144e61014001d0421603005004061400380480201d0000290321070001a940400c201d040b000c0d801002002402801039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 615817482 1250 615816232 615816251
    0xf110f12010903090621020a0c080703020d4d010606020303011a030118050601051b0616030e07060c0f0501020a0c060615050a080a20070302010b0a05030a03051606 72
    0x15040004010b11903112800c0981e26811704032a45009904080d00300e245405000120156503401032008c00b0740d40c42c0c2151a80050749030360059a210749800c4005030700400c4104400d50740003100800059080401e10340c1c1c0d101c1ea0101842c151660040c0d07142851101c08c4a8501540888e80c0c0e01c1d00c0e0b21018000d010807941c9440c082d440380c0092282003002100c5980344070a4041e0760301280c0c143c54008800c80301031541080040003e00d00144528140300c1c003008110940040780301600900204000201450b150002c9142025400307440f014040c0750401e4045400c00c040441d90a00361038480c90171040c80121410902103d10b4404c0c0094095440002d0031200030394005918031a42d40100c2051082581e1100a8000c0303995082d411000903006010f803a041c179216000d4203421400000001c2101d840360b00340600d048007102c6220010900000d43c0f2001c0540a01507400c0b00c490441d101c2c0e034080d18240c046900c40482c124002d0030080d00090000924444000f8014015049003003080407070030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 615818732 1250 615817482 615817519
    0x70c02032e091e080702090a053306130f09090309060212030c0309101d0d0c05210c0109050c49050609010606090e01030f110f 56
    0x842965118060001c0030205020810a01501c1000b41c1d01c501040d15140c80604180c0820000036011190001d00b08a00005a62a07802541c01a5203100d2300003118140035060390920f800e0a242502041c0c01041055130407414140e604090341c1041e82d007140d4400e034120821541440315004410f908020b02008504140c05901ca0381c01e5a02c0f075120050490380301c86069030f5901001801303101240007000040c404d810b184020f95001114482103801200400880d0400d860507030b0700c101004c412181140d504035404005080044081d405c1150f0861740030786030940c855803070a203082c4890815080464a0620000440b2003648800c6c008029003010351611945480708003504d984901d4580c1c5803401c1c0200030340f5990041020404041c0d00c000501d4554907000c0502d401140c02c100d4940e41600b0102e43d007800040d01c528102c10000902074200117014003842e60b1600311a02000110b03006000240c15000c4030304000d500b1040aa10484103a8000341040c0d203c3c1400d40e80002d05102c1c96040100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 615819982 1250 615818732 615818773
    0x1204050d232b0c020d2601090504032c0405010b030c220504020f0c06010e0415241d0609070f0c060f02040b0403031407020a050108070c0203 62
    0x51081da1a5280301c001198000c014124075140d8041d001402c102145010440c00c0c41052034000e1041030100e0325221070303501c80403210110165005a04030550200e64143e1100881400d100700640f010030944840300f40c801204814000c0354031181d40d0b840410245405082c02460b81c0c00c45144118104a6002c9a400c8108030740344103500036400d2400101c0e412103410300b520310074410900660700701240301c090300c0001c03c6041c8000d1401d80c40940040352680711400205900003002c0000303555100c204400d2840c140059000c844030200e85018080011860110340c0008a000c0102080ba040f4043c1d8032a8442c1c108941180b15070042d040c0042c03032610640302d8214034481030f070fa6010070790f0714032051003c400d1040b00d01c41d0000b071503d84982160350182150f0388155009500000e611558213140004a030320940003156298400b02e01001055406020340c00002c0c801c2511600349092580402e5171900f0300c1c06036a05005262001814140c41582015000c1c4e4004085642200680b0b001c0000310 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 615821232 1250 615819982 615820003
    0x5100906020d021902010f030608030a030b0f04020708041e080d0816020109030509060c01020919080706050f0304140f06150117060603010b0901090306020c060a240e0a02120405 78
    0x140120b1081644140c000f0502d00d00c2119056200ba0880c445030b401100d0340ca46005041d414580d170307a40c0c007140420040020700b109400c9a01c000030326012a42c2003190401200a45c02d00c21801040030100141020080d2421070310319034240c075103e54440020b109504865004501107105030001740950503030100d40703035004d60a80405001c91007440c6404030700340c450070b20014000c58402c00600e090390a01c0c0004020f144802d01c001800e20254074000381c00d42045160003440700034020301c01d1002c1c000900410b001042c040c108540b5164844400d201036010050000d49242400c011001041e0410b01c581161180410241c44c501e10f0003105800b4002e0701345c61702c1800a001d41e60514110143c3e140c1d02406400010091800c0d40c2ca44042941030f9402140150304002280c07100000049a90002e01040070407000688007a103800340001040312034000510ba0118140010312440f003542100c20801c2e242401e00c094140d903140e6050002a1180400f60b11a6403090070411003030280214054950 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 615822482 1250 615821232 615821237
    0x15270a0605060405060919020412210f0e060f0c010c0c150e0312090a1b091526211803060907061b0803070305060a050a060e061305100906 61
    0x842e200e640501080320300807140690000031500108504899031045a080b44c0d5080300094a401d495040b540c1e000c1c60019021940e0307034811594002403107108018141c0080e19841c24004000000100804003d41c10942da801014005a42c0b00c0200b0b8550455150503071080007807003052501440180f440c003114806036403c1c03480d0100d881c0d100c28980160160b181d40d41000b542491302034860303a924030201500c0528180f06260400e000110256521491042c519035620661450f01074000141d880c1011420100c40394101c0511404221014080c02001d4401c0b8201482c5d5000c0174284c54100c0d4035011400b907038016100b0008490005000b007040444d010700c203c40000c500f500741690f5400558425660350007102c020700103544a50000e911009004080701009801030301e4400790755100b5285800040c0c1c450081007400d0424050010040070140d802d405001e181207001000c041200c101c0500c2040e00241d51086145505620000f81c03100400c814210b001d8003070080d26022091103140c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 615823732 1250 615822482 615822491
    0x10210110310060f0c022e0c050c09010506120405120c0703030e03070506041502151003120c030503070f030615050c060a050103150c210e1e15270a06 66
    0x5410b8440c40c12800c1000131a150048903008550130030160b00d00000c401e0f407025103008407040780c424140c02120000491600d0342c43c01c00509090440c01c00140650b40360241c411080104481d454000848805060f020540412a00c852400909020303014480044020300400c2d0501a4100402c0c658202c82c8a074696800781c43d010028140c55881910440d0390003501407104100d0200c0000c0b05041c4405d582c41038940c03a00c2c0140c0c0b1120605000d03240c0100c0075042d02024801c02c8109210761200d0000390a0010804029550040842c0b1004054404028240d0300b01104540650040c102904002d85030103400d070dd0b074070401406a0050000d2880070b1194901143c1922081d03c0740c0ca0503244c00a209800180c031206180d4060b003164400d0100b00000b00342c03103244240b444d00380b01d400b03807555000100d01a41048035443c505018800000d40c54040d8040326400404000382c415030300000c80a45e41e0b51591811201610790341d0030410b6100901245004201c1c07540040303050354160388a00007c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 615824982 1250 615823732 615823739
    0x1050a0e0105031216050303072102032401090b0d02031f08070b13051206190b01021c0c02210706050a0804060906020f2107050324010210110310 64
    0x5060540a00c5241c2c3c068011511000031000c1441c000c2c41108580361098284d40415980d191859100300c0c2c4100005004003c8094000c0b0030420b0781c00484113400c001c2d8254206211200808141d2480c581c00c00d1901c00e141c800300d80d02507032030b05006000c074492040c1c65160002e9040b01951080314141d8004603540c500c600e4508042d019017054134424401070900380c3c10070300c45500940c4115282401084031442c0010f89d9910703d00c40e04003400740c0c40d0143c200788c103001840744414000c074440d80d410f95007402000c08859134000703006004c1c00f03a0b06a40d00c07501086103805a0300010781e42d00180d0000c00d0403c21420503046100003104007001c8404861445a503030380101c5490041d030384c5800c0000c4214020a0119020b50480a0b00c11300801c4010f00d070148008294807941d00403500012107403032001001034120089000c65501a0090414516500d001c1212590115410044002d40320024030742030381c00d91007042001c1e00e1421408003000142540c00c400141034000710f030304441071101c00e800032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 615826232 1250 615824982 615824999
    0x1005030d02061b1623010501180902040908130e0106080c04090e0f0706020a020411031308031308030f090c0409031d030307060f0506090a1808070305070204050403050301050a 77
    0x1240e0140181e40582096100d0702061009100d0350554110140828403c1d441000350b101101c0084d00e1090200340240e845d403951403024000d8558803102140d01d003400402500c0c1d5041d5403040d043c4005100040c4001d82072000400816404101404150f0040b8851680c2c6020000d0f5030240c400401c900e1103540e036240c9044500441c21034610030054400c0c8010046000786411000c001407100080c1c1d14005202d40c51503141110540c0700d240164007903842c80043d82000c0c03080d45544038403002c2592441c900f204580e54614071010303005180000010004401b1407814100e14005644044044d56a00345030450404a09003a6101a40c0b409990785642d91450584240485642d05407a9007503014400b1030301d40e030480f444d0161280c00d40000c008000c0090740c3c622a07400a03100e2160000350500f08030050120b410300003028104910728101444071134265251400d2011980030312040d5a41c03050780340407603040c007814400a42003418541030104141d0000007542c141d941c2030314007040055403803164 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 615827338 1106 615826232 615826243
    0xa05090a030c0221031b0106080703020d030909020d0209040b04020712140702031f150e150105070510060312050702010801140a150e01030605101b02150c0105100503 73
    0x210015003030205080c1b80c0f140e1728020081075080c40c0509682e0456800003a1042d00c090040e5800c0500c5102150701800007606c0542d16082c603e42c010010350002c0c2d924520540c1084d424a596003081e00c01da074103060b000903412030603040580055415130140d18403000700380000c02221016031000c203e1204221503181c000030500d40200e06240842d603a40408060f01c450417001003115500d142c8060360003040342010b1741c21400d440001030b5064402e4500c020494020300348441c81e040107540c0640c003160700660104c001c0d1003e40c10212458810403030003d0105031510018000740c1503960325a0007800c4042c04c0550070307941b00c43c100101804040390900000c6d10412548a4551385809220020318040d01d203000b00c1036500101411840d001e190090001e81c100b9003401c15035488560203420718404003051a91500a001c959001e05811140301c4000380420400240ca41400500c = true := by decide +kernel

theorem cover : BRFrame.Cov 615647482 615827338 := by
  have h0 := BRFrame.cov_init 615647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 615647482 ≤ n) (h2 : n < 615827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
