-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4813
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:49:08.045713+00:00
-- url     : https://prove2.me/submissions/4d22d727-5ffa-4a66-8845-f728af9b8c92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 865467625 ≤ n < 865647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 865468875 1250 865467625 865467649
    0xc041e020f0403141b01051602060c15160f0206040b01050402180409050d0909091a1b040902090109050114091002070b0d02070203070e010b0a030b0a03170901030c030614090402 78
    0x400c08040461189a6400213140004030200701000c5d80541842030041da194842c408840c502381d20801c0030207000d8a400400b5092a4140400380c51b00b00404049020048004540d003214203031090b0403403c0050360291400400c0c8140c0e0004210604040d268600b20300414890725106640001c3d03100c00c5610850345100c0020030182050254680318a009506e42411550311000500b10304400502440c00307000304140e45800124460b01004c007480d9010950000601d00242c3d80410303010850301c4000c43c0000c00007800740140c0140c0b14a07014000600f124481e90201e410402e0100310401c0041b0741d86c0840703608940880740154400005542a1709101a55000c001459008264090224059001099228070071001d40d0703130319501d4006200700e801c000e004509849e5018045c08070403a010b684103c01d0203000600609085a59603240c00e003021041e2480d14918802084080340c0e543c25000b1151442c1d00c90030306000d0103040c0a094900c0d0804854464810074000b0003040039500c0b00e8035030006c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 865470125 1250 865468875 865468883
    0x303120115030f110a17010f03080f161a0a1515020a05100608071706040f0c0e10081506010f0507021c05010615021504240504060b030c041e020f0403 66
    0x3003000554104c04594002c001150080780fa940d07281d940c420744010080b0b05a50540d25095899425501d400c00e19070442d02c1252901103041211802070f070000744001c00d40c00d228044103182c0c1045c81950740d0f40d0000240c03240000c4c80c140040038448100c0800106d09403180c0000c00d40b5500c48810b400c030320f03080c07014401400f240030b000c400c036800703500540041c0d040e20f0101044540940d0380c0e80b4000f40c0f42c00d0070b2140000700d820180203e000550502c000d90746403030060b5280c1441a4a0750589454500c0c141d400c08071140e130030301040140074011300c03d10b201d8035459035503181585445800a04a0410b406030710b010030000080c40740855540350524500c80410090031b446504161524500a0056000c7e4011541d041c0000080702c9100040300700342a4a40480c1c400c440e100c940e15004510b0300d001e01c40c0c80986200700b442c01904010b2040e203100d940a10000718038100720400381070410203096502c0d4080c5081a0810780c0c01603022254038074008000800590324484041a00c00c18090754000070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 865471375 1250 865470125 865470131
    0x80a120f0c020121050f181603021c05150717060310020d020d020c0a0507050910050613030f110a080309061222060c080705030603060a0f0e2a0303120115030f 70
    0x1107204008006000d21504042c4011b402074075400341f20664500204d01070791040080b107481030005040000020311003540380c05020362084030a40d219410b2201700d001d0400d10aa8020410180c2d903484800c40b03500c401c2c3d001c0b2060b06810400042034507011088403c0d220181c00040d020440c600750f9040300c0e004410380c0c01c115201c0380f641011035195880b4413000d403802e200311200852549060950180548071041950752035514000c10701200703400400e0041420301e0601c5c00000450703801da0803200d4a40c441c0b20ba15074043c00380020890901e1840e0402d031020703441400095035907140c2d041180c04808004150341340c40da89560410076604401c0c01080c09144c00e00d6800c1c4100955604034031038440c2d21b5103551032103944200d811161400200d545580c990b00c24004203045401b00d07131104c024411864000b013013a0500c282e02c5403a10003924014602510a0343e000310b0810143c40c20101d18a5045000d9803030b03c0220034040109240c180078010b40b0130314031403842e12460302a80c40012848200403040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 865472625 1250 865471375 865471381
    0x3030f0606180f1f0e270703270609060501211e0c08030301030b0a0b0d06090c050a0b0a081302030703230601141908060c090406090204080a120f0c02012105 69
    0x2400807141148042c00380c10090640c0d4074a00c2c0401b40c00685191424503101c45a495103012005400403030010b080d0007580d03e1010800203888408071030042e0040901103225001d038a82802241c50503407162904201d540310103000b84000b00042c0c010390350444420a041c0c000005001d110345d6400780000c00c0d0840d400c000081804000c00a0340c100c90281103000358981c0c5010750202500c5469500743e41c042034890002c40010307040d80c0310280450142d696281c03841d8540021501140c03032900100c10707400f000715500c9103c0f07a100e0361040e0700a2564582e100c0c1c44045071301181e600d1000f070000410011f02040041e80340018441c554a400c01a00111205565a2071000c02c3c0c0048100d049405200e003521440180442520018102e80a40c0c005003800ea542c141d00030f082d84c1040c82d0641c2d00075201c031070010b90a0b140b40060000f42c401980a01481c020a2070650a904424400c08081c00010700c001030f6190340160610b8952a0282000707100465688801d0355021070303e40214110354542024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 865473875 1250 865472625 865472627
    0x1140408072d03080d0c051204110307080111030c07051f060303030e06060307180908040e01060927021b060a15121104090c08060903030f0606180f1f 66
    0x2094880c8000c501c01403508180e00c881c02e40400c030180c040980520010082503c40189a41c01492060050310b481c50401e80f0f9016951000b03003007981c0a80c0d101d0800c3c0303020460382c5024400781c1e0013008200c000300705ca03030040c101d40d00c0b0901006104002188000c900c82c01442818851000003100d411846600440c4e80100140201028001900000c1c60110010842440010014024100100148080762030a8510203803820320040c52907030f59031914507040010310304c80c01402c05803401428540e4258103003003008110000c194030201c85400c1441380e000d41d500c10750b00010a141c070403c20240c0e54104200300c4110f6281c2141e08400184075002c1002040c05691384060012401c40500401c0385a80d60707406d484154400c0700207069015420400304180c540759005d24a0148185003a0b529159078035442400c00608942c0b105564000004200b001000314280f2644580111403450900303560340312802c00345080c581d080b030080483c580303528140c0c1e940401d54201c01070010780100c482e40340048 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 865475125 1250 865473875 865473899
    0x21c0501031e0f0b0403030e0a0303061a030403090303080411091f060203030c040504090f0210020304210317070c050d050c0609030403021f051e04150305010f050114040807 76
    0x100079036802c08154040c150b00890b000030894483e4004850107040103054640030b1103e400600114103040c0e4500f080812440706100c0149818080c1d100081d441d403604459200c802c80310440c4010402c1c2c208200310020350416503003020369030180780904080d540c618291f80c17a480e81c60307960f85d840000c407000c2140340d02944103203034034818080c20450a55655410140d1ba03a000560302108010310034030042c030041c2415482038400c10701401d51000000ca0036004030f00714080c0c0c03e1000740180c00c006402d02c90745020480c0703000720b0b030040e9101c4000c01c0300c6600c00426070341003081d400c0d003400084004914000d100e0941841c43d107412070180c4990307200c0d228000d052035000e441d40c031880380101000a2500f11000c0242c0e41229006404060808120038260000c03480344805003050003014441c40310002180744900c0c0440c400c072141169a00d040124100806403a0301c0d4644c200360801c40180a4210f02d401010304587c030a082889050b601840c0041140c00b0b030360000400c5106d200c40020f80f5040e601 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 865476375 1250 865475125 865475129
    0x204091131050d11090903120c0f0a121d0d031d120a02030c010609062111010302030c0417030306010e15121312020609060106020c030a080904021c0501 67
    0x10030000340a94a11003920404004031820759094071800c0400072800c0526261040c64803414001c2ca074000c409001070003c69040d194190f00e81c0c00404d4a4000e0415400c5580d08084615401030500c0c0e00560a60380d2880380b64001d100300071401e01e030240c0c11512031708035800c95041c54044080880105490f59504c9001115140009007407601e44030b400d40072030340c0000e20100a10041d2100c04040354500d145580701c6402c110442c8010403101c07607c52028401c050160254280100b00d917850203030110445c1c01e840805030100074000e080f030400190090b20701c3c1c510316028280544c0307a5523042940d4146010350340c810200314620113a40070301c4410100041d0721603202600d0302c10500180105020328903041d074141c00c00c881d204001d0410070802200d0351135400701c03a11742160701d03540c407070b980c0e45640544c80340c082c50140c0c0c00312090101d014070a2000c11301404580c402000f03010f6181c400240d5a41513194003400080c000610303101d040d2a160121174185031503000d0514101880700d0a034000b40030074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 865477625 1250 865476375 865476397
    0x1e0b1303030b060405130c210e070506031509061512010503060c070b0c0d0f0e0a061a10200d020d030b010e0105091c12030b120a0317090102040911 65
    0x3201e0000680b42603c29603060b1940a403006111030891102400208400703031140e0288201c5020001000c0310142140c021100507680100e6a485241c241c145410381c103800541c0700f410240200020590800150001c090046840c1c000e641c0b42c080101e07954060700198040d82c540002000300603001d001100a04984044d011603810b6a5481c52503100ca01031141d00034400c0800801040b005039540c4040c0140b10940303140003074070003107100650045035481c0ca20684c0c03507000300340c00758244a0244107000c1120341b06c2c40307150301c04522040041c5045044000000c01c2c04a003c07046001055800c1054003002d680c6070440307013849501103000e551400306c410020000390402e110380c2c080394030036156040901c0c010385405045c81620000c000130b0104408800d592440c1051103e0041050b0714ac4515a55803039840002d80c00d82036030140401341c1c11100c94004036500003800500003d40c0400d4a0107040b100e00d034155000d86807004a14060303c2507920403641241030400c1c41084098001c0108020300760 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 865478875 1250 865477625 865477631
    0x3030a0603110a03020a17030d020714012d0903020f03071b092007050a0b040b0a0b0405010302060d1805010606050d0e0f0d0f170103080306030c01110a1e0b130303 72
    0xb580c01000070020140c00000d401c148940c00411600103407100d844040005442620704000f00c40c00c1240490700b1800d0242c0e40c160482d48403100403c2d003840340d030602ca5075070301130301540141840c500c0042c0940003150a0380655941c04807801e0520030f2010984110315401940d9643c002424200c1020011201c10092003800d5040007030103211a11603030014030030118100100d562840b01c82200c641260f6411788460050745481c0700001c21008006104034840c420f0100c1c03d00344040d03200106c443d0603500502441c0f42400503c00343c3d80e01c0c0181d50b0403040540001c035a0019441c0000181d103901310b001400c07982002c4001c2419a0440040c10711051039482c1080000040501d955450340e060220405603000041c2e0411546d110717090004001942e810700c1447da880c808200c09419000342e00c1518071301c1021092050529060043c48041e503003d10b000100030080c0d541207a00e90060520041455250100300c250346400c2c0b0104200458201205a00e036291000c0607800410701ea210440c0000d00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 865480125 1250 865478875 865478903
    0x1e0f0a1d074407080901050c0403020901030b0406021902030406081e040201180f060503011508101224050a0b030f0c0108100f030f110103231803030a0603 68
    0x12049406800d0710050a0014882c0c1c003105600703100010041109140c00140340110151240090702d0081c054020390340d81080c00d20b403a1001d00d08403100580096505642000b0400150fa00c51400d01e040d40c0d0491031003005c40c0c40d41e180000081c0b041c5000030280180a09a0160850300803015008592064440c442d0301d079600b00003480550f00d102680e45c00071401c038000c10302651148080381400108041c15002081e00c47c01c00050300c0b00141d00103c00a00d000006110144c0c50390b401000582c0c0500381140641000d6a08a064030428060b051a00515415500138406c0148052403001701100c0703d07464031540c205410000d010f00300d445400e814200f424442c041e041c000349100d1003103100c801404180344203000440b01c581020700300980300f0003080d20108401c0240030743c0c40e001f94481c11001180b0746403840c4c00c80c0490542030405040c1823600b10302840c032001ca1402060032104000040c0d40d6a030340c00f146041038a5450000910920011082004001e195448507080c0d1707009100c5c80c44099 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 865481375 1250 865480125 865480127
    0x301080d03050c0712200109140a0b01062106090f0506031c0c020102280209010b090604031e0b04200301050105152b0906060605091e0f0a1d07 63
    0x2c1040c0d0b0003804440c0f082210070041640b4481e46006289a85403401160084c2c0b42d040402900910415559035921442d91040118160b64603a001890101515403915103444104034440148034070400e010721814851444c0340c800950f0300907803100c0c01c1d0800c02071b915940d02000070071004207a01c26107898440071424500c0c00103a815014407014140b50002400d5200c221400c41c6081012030540c400c600310f076a50810012510703503507862500443c0d00c1010041c010064503182c1039001080160741080070851540300c01085406503a0080c03040c3c035000400d2040303424480519103000c1d004071500400d11040004280d1600080d00402908402408403c010542219401e200f80d59029030748041c0103810050010181034041000207040700e0700348401c3c00032440e915040c1e04006c20507944001480400c030813840381e18003401540c03400700c0c1022070700000301c3c40303c0180502600c0441c0c04220280d40d039584450111514510203045d080c101a502e015a000d11074180340010260190100007910b1a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 865482625 1250 865481375 865481381
    0x303060f01020334050318190e040b0403090b0a02060603100c0206240d060e01051003050d0c060b220605010c0812061c1b0e010810022d0301080d03 65
    0x1280054544030241c180c2040f810a000d15034070791a540c051516131001c81c0c001d1000d4006034010840e8071028460100400003400f210352404130035285908014002c4680e4003410642c09540101c069010f5140c5050030746100c510703a8084444500d001541d142441d0380407035164000c41040d021138070f410700d11002d42e10503501154403200043c0e0009001032031050b40b40c140e46803020018040c42092400180108195110700e4409441340707501e03200c1d041d0340e08a091080e0340d449080840309012050640da0f61945030351078001c4d0681000622030088050080540c00444001001040380103030200d85a00e00c2001013032201c01d19003a500d80440010203500850100000b00e5000004928003c4076001e070781500d40c4045c2030f440d0400100412410102071449485030617502802c00e01000c803100140c541c1218245802490b0104062001000f00745030004d140526551011005a21480194202100b4000b100c020072001481507488902d2014950300a505031082d1005030f0380038031a420310075070039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 865483875 1250 865482625 865482637
    0x30e10081504110c010513150b0105120703060e15090903040f0b180303070c03060e0109080f22030605040312060b0703030504020d020d14010c1704140a080403050303060f010203 78
    0x1512240704920a018907056000700e040540081840e070501e042d00c01101c0c2140c400b292055101340504500b402840541e00b0f10482c0030418123803e1002070500c0c2d000824502130080805021040c0d2400700301a14000d4110501528540b00480214640044080b03101400c600d032041c000c00658007c1921541701100712001d0310510030100d0805481d00000d840c66500c0341044500300000e00d034aa01c0d881ea424002080c01074054155000d6660039401c00400711048000b40003130343d170f2500405000041410007521411b44014102c2e81d00d414070540c0c01c05403a4102c20483c0d225a000c2603001c0b04101031940801d000f5406039983c103420700c90003007000003207840500900407415000e0002400181c0310f81c2020360321600c003415076441c04549a001c03900303003190080d00320348440c022506010594424030407030310301080f20b2034100d100c940308040c000c01e941c1c40500054100081680480c940507010450380161641c005d4225540301d580782002c2d03440340c0060b03a040b4411529904804002d600c00170980f80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 865485125 1250 865483875 865483891
    0x110f0d12031a031207080c0f0a021002030a020c120c0909100b100509060706060b03071116050d11040e0607090918120e21010f0f1521020607030e1008 66
    0x150404c0b1481c0c0b02d4031113400111084514038420460b0320a480c3d03050050781c07506109007000342104001e910422070400c0e0000340c00821580b0501001510580c000b810700c0d0b21103810f0740c1c0340f000014400c040c1402c0c203440600007500441200240314032040c1c0014898cc4112203070600300030b0b059106003044450048142d030350b00003400038090302d50507150080081030384034811900003c04c6a03640c0d00825003900201d40c0300c00440d02c42a01c840251109009040c60000b441000005003403c0c0000900d0014580b0b4014001c500c902041c040d1689481e070000b10a41704183c00c541e003a01d450900107101e40014010110850304003850440307201e103e0125540310076800091210110385c001411a079040300b07641010b0740700e6011244903020001811020303501d10000b40001c2100072121003174500391074250300d110f034042e4074200b12004950140042e81c000e030340e01d260000b89405205021640c1e507000340300020350f100c0c4000a0b80030400d90005010500b600342074403180e544046140b8147c4611004840c1c0d90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 865486375 1250 865485125 865485133
    0x304030e030a0b01080307050609010606020304091503081314011d06130b0a050414060a0507081804020409020a1b0c17070e15010813050703110f0d12031a03 69
    0x100024054040500c030510080c08440440c41c1c80c3d00d80d0207420030217910410b0b05800c000f6041c1d0070b214041c80700c0741d88044408000d000342c600e009002952440f8a02c144100540c3e10842040c9608000340410300840e00804a6a16141140084421b1000e81d1091140030014103644504a500456001001d0380100c140c04520b43c0c82d090610849600140345070380711108090000c149007410038083c0025403c203a4403144ca42d070401401351108540300220034402c003801e02160040c181e121080b5214503901500d903c6d21501d0110089043c0c00d50b003941d841e4001c1c000306012601c0380f8103a025001688003580d4080d020620801d54000140880c0d078003a0110f407910405000d02e400d00d40c42c141610490a084820b019910305518040620598841e9021100344900c1061983d0103110303990482c43e6901c000e05d42c002d5543d5226614011813100a201c4004142c40c000e9030b95a604907150000310192074001010b58500e4001d400e11404400307080401d251141e01c810600d0003118820906201078014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 865487625 1250 865486375 865486381
    0x108030a0e0f10020f0d0311030136020702040605060325050c0f010c02060f091f110a030917040311040f02130807061e0203030a0e2e0b04060b03 64
    0x403a000d4688082941c0c000d1034400c0304090b03d0f00e50340000000542194007030080c0604280220b428400308516040030503003407050300b1300c88802810499046a5100740322a054001c55041c0c022581600881c108407603a4280e0011b8246050707800500403107100710b400304441916401003119074002031b12440140c0d4009603140c51024000722244407840d8040c1001410109441e010320300d400b00300d1240c055580d4440c085000c5042e01088101c0d001943d92480c42403520700740440b40c1d941c0079907030b0415020000700e0b20700c1c1c4c122041c158400900b20311600c8540b5a41c110802e000b502800790b44104844964241d54010b420b407084505072010b40341c0c001003a000e442581c00070800a00020000c181c0c0540e42001031100180c0c80b8007074113005021103806400014075150000d06400c691170010820411b00c15440c22003980d001c011260300c80c1c100500080c03050041c1c24058074192460040101c0140304404284032540411400702104023215030a01c00c0380542d00174030068848511a000c2d04150500c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 865488875 1250 865487625 865487627
    0x1e0308010b040e0a0c03330503030703050d150302060703170c0f0a05070c0f080d0e010503060603010302011b05060703021b2407051204060b0405090a0b06240408010e0709050108030a 80
    0x45000c80480d81d00d804900480c0440540b032490907c11003e00840110800100409060300e020740b0003040124003071070401c829030320007a00c68807030105c1c0c200982d99030301c00b0100d000b46120010005550081d0096071262420718000d05440f01d2039034104020f006031030002c0e820b00c01c0c410460300c444240500031400c004c008503003a0780a4010180c00c850b41041e124001c01c0408911002c00022301d603040042503c40b80d51180544185444012141089130800c1006442d48406045904490303080c60706020707803410072440020405084000611318043c44040c04061913058014080c8402d03080e040107c2444050702e0290740c0c1e0f0182d540780e5050404103d240c40402c03a03008016901c0081824007601d0180c1c02000014038140442d4200c46441d690781d40c0103401e0070a0b1061541c085034a50041c480078560307071607100ca4070744000d104920405803807030041910410118410750010345a44903540752501c44406a0282820785808001481003120025000160b4043e0306e0403118007202031454007160f508 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 865490125 1250 865488875 865488881
    0x1707061811120304050411040e13030c0b06041b0809010605031504030f0c080423180105061b07030614070c1208070306050324090102040803031801091e0308010b040e0a 74
    0x2422200f030009000004454a50b40134145c100e02c040c1e030440d42e4035810202c10070741e5007102070000303401c145507062500006500030140b14100d50300040c0c1e082e0b56035140400035010780603058890065000954a0300d0001c0d800070019401550800002c1c0100d0740c0f10030070300d544c3d02903505500141c8103107200460003003802502d0003410304045103000c0480b05d180f611000b1507580b00d079015000c49810084450801414495880c001c10400c580000c002200c42e5401c0c4480c5406006291144d100003521360aa0f0349104113903000b80c0c207244107648645507281003401c000c0c80000701152a5005410002d0b51452044084902c82a4070a200000403155000d0880300190001d042100f4103580791000b1425690420800300003012a40e2650803060000340c1c80c01101501405440700340c0e00600c414031106002100b96544128500140c130790004200c801070b800b51a00920250004484025001d0b2031000040f03a840f00c0e5010351692400b90740c0e200c0e0342d0701b014800c6201d100f409260b4103011492078481c9030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 865491375 1250 865490125 865490149
    0xd1e1b303e06070507060f02040602100b03071e091a100c1a0c03090c01020c01090311130606020307060e0613030e040f0510050103180807140304031707061811 70
    0x2404003050010481d0103203140c03441c260707002008141d0214003102040788038080e01c20340040d0b1039400c0d03040c249440800380d84d40d40c5030301482800c0d94542d03101c0280c0d6102000600014214149000301580e45a000e0003080403040c0140490f0608003610000c00c051140c0c210440e403040501b007070f0000800c8040c1292810040a8100e5042c107074000304414800c0b5002c441402409105a00c580e44d08000200c60f103003001303000d04641035411001000109a0b0401e400070b044940040c000c103600210f20000401340d0200c9005490580c2c50b211012958a0b8000f0103070002920481c4200b003122280d21849a079003804442c1c209003c680740350703d903000030b00c21520130100c030720f002d0f0011030150304400700042669800c1790010360019200310104007035a4035015101c002e1800b1a00143c100c00c0700e8942d1002071160700d1700074017024615210f14105000c10000c59004540081b101d041c0c2000c03034144254940e1088105075406c3e410a1820656400701a05912070075030301240c0880c0c510305010030f1210030b00d03600d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 865492625 1250 865491375 865491467
    0x90f0d24050610020c060418091211190503041229070f050f03060616080d060311041a13020d0e0303090d1e1b30 50
    0x5401003110000180c0080d400150000c9000310759840e000302881107038080c1501c41d800315401a030400d812038846100f104c0a072462039816071420051140310704082c00c620b01000f02001400003140b2900b9030f004400074071a000500688a1a00d42158031321110885080080c002d80c108200130080450210615400c40f4414007503095081007103007514510f02c0c11403019000c402a1002004181613211400d03501c00115820b095040c094000d0780001030b400000e052500450300055000d0341020314020906059034010002595903001520351009031290344001c8910200380f081e54007140c82e003805240d0103400c4d400e00d4140389a900804005019402e0341115403115401c00040d6181c0540340259150510b018000707640e00e0510340e00f15450b029a80c00020100300038020120407024000068126008461030850034600d400507800600ba10310b850b008110000c540d020103440b483c030508500c078404000e05812150640004141d0f0003050442026028803881848030040540a00d4004051411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 865493875 1250 865492625 865492643
    0x105090712020304031b1a06030a080315010207030f030e19080d0c0804152003070302150a02040e0f27030f0d06050604030b0405010b04060b190216090e0f03090f0d 72
    0x44060700240180022002e071504030747d40c54181c00b9032002219041c0c01c01d03401c0e00144406800d0351103107001c9000250120b5810b50ac400c4034540d480c2c4c0b003040803c001e07541040c544140400d040c500513101515041d003540c0100091506030a0404000482000710350321040a8280403140381700c00c449207030702881c00700c44e4414288070101ea40c1307090003500b034003420942c1c540b2400c40c180400d20050211a600021242e41c3c410010180000e0340855070150400320035601c00500e0700c1789007250700a40945d80214401114240c02c1010400c4980100390142107848030040603403103101c40d018850408600c0301e14043d4810440141100ca004008241c1c0f11071701c820000e405c64403500045c09645c0a0703841940c20700209000d00c0203108003031040a5058000b250104400c41c540101311031113008905100400d103061220390aa07140c024040d2802e4160300910344c55008d82c4800c0110001c3c1280c41203d516841015198403018100008403161042c005090307180551141c810861560207a9008890030f83e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 865495125 1250 865493875 865493897
    0x10f110109150e01050a050108150a090813031b081902030309130b2803020f010c021009081501080a12020f030703050909060306040b0606182205010509071202030403 73
    0x141840302e080121052003010981040c048501401d50310041c0c034040c4283e00c3d1000420031502e001802a04981130f1401c04502a039a450030759004011800f030281c1400300004107145d820200d6840c003800e4030b104140d010b02c20050f01c0009100501c4078000c0315010b40c0606600450814001800b1a40d14801000c40789803004240c0800c00490342800511101340d120310706111f107441c00050f004a0301420401884000746480002489501948000390161410490454503039114008010b105900600400b0014a510000600c02c43d628401c00c038590190354402c40380c545005140328101c0d41044000c09520303400b521000504c1c48980c03081400e51180451028101c007042c005456800d0007500c1d000d07111600c03d0280072440301c0007017949101e60020400c0100090510300d07015000784055034100d4440c080e4252a1043c1403280020035403204500c02803544843d50541d072103590001780c100c107005590f80c80301800f0207070b2801c1d40c034400803c100501d45418984c25501466101d4040c0c030744500080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 865496375 1250 865495125 865495133
    0xa02280501020726070503030f22031d030102090d1205040315020c010b06040503060708040507050a0b031906120b040302010b0d1101090b0a090b18060f120108030405010f110109 78
    0x1038480d035411680d8003030010080d590111813407a0800d00c01000a0a18075250300d5070b6403682c40e40300081540c0c040c08007520109a811741010301440c0030300180d600034410034905040140840c2035400e03100c0411521900d030030869041c10b00039248810030243c09024003049a681e01e16103c0c1d2080180c4081000602000011602e40603492070780e401c03030800050b510030001c254542980c4004940ba402080300304130412894400103507442e40800c040c645106c05458602d411401c1c1a01d590000f035104095140108201600d600114002c0861150040c802680305140005642c460322800124420500b038100102d101d42c00c00903801880f030710000450b26105400640e0b0212600700a0311030310040000d0360206e50300300001e600034140c81c0124608006400030010100e1189008914006402003a4400d41c1d08041c504034000744030051026490340d100c500c910720590494220610300c82c0c032220000a1981004c01140d060302c5040e91140389483c1003240682e001c04242c2d603c0185590381f030070100042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 865497625 1250 865496375 865496377
    0xe091812031312080f01080115060e01030b10090f050d0c120f0b040b04061419090f06050a05060907112805060901150806191e11120a020a0228050102 66
    0xc0309482c1c46004c44c904020803250b068040503048641113a2628041032180c648184050085070813a2030300c52020303052100100d000d010380b19000d50300b1446c0c0d6082166140c1e0020311b000142d030000e14a603d04582e80b041004180907041501a1008004a9003488407846080d03920320030342e001d09004c60616074242d81d554000201118141e036001c7e0040d082c0401c1100a01441e11429005441303c9414100006985000001a4007810203150743e01c400b8003c000f141c41c0203000d8150410030400562034070a242c00080d00044800d68440c1e8286400104c01d54020722218020828140080001c0c50000d0081c00700c032000402c108207441c80c0780320300b00c0c0041c40c1000020700c1640c940002054210500041c0c100781520364000516a4104c01c0411071210078918206501403004900414098581d100d000a0303a1100c20315001d1050900020200d07004100d03000b0f00440c40042c0e05c0c40c1c1070341c2e1441300030000c9029003821000140c00c4440403c1c0c40c040030004450403001c44d00d41848040070340d0380d03a10b822 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 865498875 1250 865497625 865497653
    0x6032706150e0a05070e03062401020f030d0f0e0f07050613030204053606040f1406040f05060f0f0f0402011e0314010b0316050307050405100e0918120313 68
    0xf5591140c0c00c104401d41c1c00282c6525201c400d400070005401c0003201046200e00d00c140102c0e5000040210903c41e07842000481009001a801d603569510202c0580001d0111085e500e07a06034100312041495000c005802d1038886c1506003c0c0400500380010004a540420442d04030174030111404405030b5154071403d4010b661501200300c0410410013030710135041800381d0650700110b1034040e048130041d011810991295000600d10400740251402d80246d185800700500c59200b4a000c1000f000081c49500f80d00501450840309250345000789212050340c11640c1c41104202d450200c0c148190000742c003a0800d10505001c1e03100501d8503154403582a507021820b0000c1d440309080c800a41220040902401c13208010078176508e8207102270441e80848044203010803600000040c40c1078400c0003514043c5c90f00074a1010428007015004100040c00b8020300c3c402c8580d400440c981c0d8140306811381030340a0348000b8041c0d03180000601106030300010044400d640d192a1143c001624003078020070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 865500125 1250 865498875 865498891
    0x310060b070b010504151208070b04080406030f0623040f2c010e060c070c0b071202100e210405091e0109050408190c1a0106032706150e 60
    0x5100d100a080c14090391106030304c5240114500840c18901803d175648490a45400b00380740800d1031401d02d06812680307e10b00004d0700f501c1108083c07000308042c04008208070703880c6903014402c5031000d00760710007103511a00c61603c0d10b1040c0d00c100e1104170000a0001c000c06801000003580446680c003241c00c1d15044400c0044002c03c40e545202040b01204400030350762081c20080140540d80f007552540c568002e4021100404046200000c000702641442c01400c07102055035190b40c4039103480d800103102554118094003541d45020301050492189900c4c03103016400900c18078501da2500801c0480207541c2c1d41e4000300030000480c140d10b4419006008072200c0c211a200060110042c4030100010f800401803030b810102400007068650041c0d6241140395005400a070b400d1240503030300180260740082600c002268900c1d00a040500d865040ba43d198030203110441806a6a03185c3c8010302d0410885807510444600c0401e8550384100441c1c90304d800c06121190711005040c412444c03c0320f10b40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 865501375 1250 865500125 865500127
    0xe0d02030c010e0606100e13021210290307091a0403060c090311100e030a03030b0301180b01140a03020a08061f0308120603030d020c0f07060f1704020310060b 70
    0x200c141c0003485064507101503c80501014100030001410813090380f042c1801304140c2c50403140d216650180c88544110014104641da50040c0300700c12513001d81150b1015000303120950001e107e00e0100300540740c14681c9034805907200035081c01c008043d04003910328810040d405c000421041c00103a00700d0024041c4e555003a442e24075503c4c1040695042c00c50207810460401c104200250100b004403115805c2200c2c0901000a50b41d400c07604001c07540d81d090380c54864007030b1600a041e0560301036103110070150000d004108841003040308110400c00000c04220181c0010030000b4100413602079040c41c010f2403810504d0f5250005100a103e0740c10443c07880e002201032141c0503c003890302d060310a0a00f07828482a42c42c5880c0d003241070103400a05004141c2e0071001035866034040c8100ea01005418204541b1b418001118560341c89288071741e11014400c041c008103120b030007400c1005040d51b8554032100d02c2204942603010040e000b400890701481010300c038400506070ba004100c0a001481d100d6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 865502625 1250 865501375 865501387
    0xd2a090908032e060323250e10110109080c1b010207120209090a1407140402090a1505040e04061e14070f050d0609050414060709060e01030e0d0203 65
    0x80c102104084078003441c1d0114140340d032003201c4003504070001260f5041c1000208508841526600301011403585841802e05001f0042c080d042c80b4400e1144a94030001044160704108094511107110b81d6025031081003484180d0459200d050401d0301500754500204113801243d50310411600b01d91407052854120b01c04803055554201c24800070301100f4402070005615003080504840c01300040030303000380a00380c001107421030104407908055602c1008000b040044080c0291550b041d07001d020b184003540200d2880f145480d00035500d10490050052008600d407091a22201c45038100c2c000921009000005202d0840c82a0902c2103019560110319048803060902208a506808000301e03450201100002d0902d4800e256028006040c10b1214072140c590642d464028030b103c64800354200b903c0030400d0407941e00424060f07440380303240c4540d40d031180181c00c0c0c40d0101100d0741c0c000262560301c200601c074400c2e2101165074030181000180c26008030001ca080c41000c0c84000302683c400511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 865503875 1250 865502625 865502641
    0x408060f04050f07050d02090403030e061008010605040504080906030615030705040608090a23010e010204140907090b0f0904180b040224092b03021b0d2a09090803 72
    0x42c00b8030383c46400c05000d042c1c2c1840000f40b0216075050b00a0702400424000504050081d032004024a4000044078109d00c4e145200d41440401400f40042d10b5090420014160900e030007a01c0c020b83d4400301803030034040a4024031500f900000d050a500c0301e01c0845030f49169200130010f502881c007955410380e496042600242c090003019040005aa01c040d0560000c51106000a813005102c00c4803c1d000742500ea00050240c1038014820350507510000d00000c410000c0d130003001d036440c42640c0d011684d907502e100c00e40d91010548035903420b0344402c0022000c045198801882502d20040001440601000d251081c0100c0101c0894031044241e081c0025441c0244080084084540300c5003c400c61500010015000b9841480c0c090104035905d4500078598441e40e10104602d00c0d1030414028550038025034403160740e1041403c03e14003003000d81c40b0381000c180c0c2c48002c6411188428000000710300d030f04046241d4a0026081e071101842c00709101d86140101102e0b203004040068881c20a048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 865505125 1250 865503875 865503883
    0xa031b05040803070b091e06040516150509130e0303090708011104050d02060702030307050d270302091f0605040302030f03031017011401090911030708210408060f0405 74
    0x4125824404140020400c1d200700004030380030140d20980c2c40702e140d1581d0000038540320552038054080d04180c0300741148418001107030392284d8090707000c0783d0003200451138808044620303006030100707680c44444da01d01c0c175402400100442600a400000402100c1c04505c0840c3e02140d540701440d0400030500008410400942c4050034107480204480d9070645003030710482c4118490f40780105401e1440105555032041a94110390300a000c0da41e4498191520545800354498038002181c7d140c1c00c0848000070740701824240403003045d00c1244082c115020462a41801007020320012006030a01c400003209000c1100202a10b898290b25142140304160605801c0000752708603a1040c801c0000d0b40d05548a560f0883e10009240382160003250529070240241002c8003a0748100c2000000d0b07560000ea00c940c0c901c60040c90303040002041c4008060b21200720b446000804d51065801101c10480404001c0308000d124499505d020b540d40103050070080102c07140440d0007182800c100034004144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 865506375 1250 865505125 865505171
    0x50f12041409190b1201090c0303080f060a0902091906030501142b030215150f0102150a0b0a05031902150a02030703180e090c0406090e0303060d02010509060a03 71
    0x21000202d600d4042c40328908800502c5186100c1e549528106200d611003003482d90700c204040000380b100065038182040040307018401100002c0c26480007e620030003425404d4010203000340747e00002890541864081c2d009a5003407135008080c500120510fa810034403540061401d81c40205e595850f0441c40e5441200e00c00d066402045a1a480e00c46140c041390741c54503006008240d114040c1c0c4a040c2289080c0c03185921b10020002481403150040f82c20b070101c84800d0084550750076200300013004a071180015030107921184268000b141e200c11154120703241c4840302401c824141079441001034549007100298081c0c01004164100a40c00c02ca81448000070104450307500c0c081d4003410003581c2e40300e2420301908116a00a0a403501007220801000400c6042d41c2d800240c1003402d0450b0700c5400c4071050a1084e46041d00004120b03126000c0e0591a14040d400745085036a000148917803004140340490410004010790440381c0e03070b65005484140003d44d400190424070401117000c0c20510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 865507625 1250 865506375 865506379
    0x6060b2110050f0415120f12032a0e0409150f020c070605090a050901140102010e0730081b01060602070e010915030c06020c04060e070504050607050f120414 69
    0x2100c410b111a80700e01410700406842075800182403c440c00c160300c50b4000700c1e00030681850441d9680c0f42807043c1515103003801e50140c605000140c1860800350304440c24901a4188030402c05c07410311000c11100c0041e1a40071250404010240e2010005030485101f10380443d08482865450f105000a0703118008240024040c1180340103840720340d055540f02c03184220f41c100540042d40307100c241c4490b0554402888050611600d07940c68891400b020078800240c140150300e82007040c81103040c0010b01c2030442c0c01220001460754a1001844c0c0c042000329480c1c030280241480460000f4039507001000c50040e00440d10b10030501c40d40850303003034802d80c0d4054011540b05607014845d082c10a80c801e411030b074004000048040f8580800b076000c8041d40d10291540d8082035000500a07004102d042006104503400c0000e551203c01000c5060030540d1618001001800b0030710039402c11800502d015405041100d0007000c1303120700a45410300b1000d89803040c25002c0b80c100445100e10f1251a405401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 865508875 1250 865507625 865507651
    0x90d0e0f01020618030720041812030f150608010812031605180d0804051201060b0d0c020f0a0c0312030203090d1d0a090203150102060c0a05030406060b21 68
    0x55000003540d8200c041c200b44d41403540480b00f420403180400888111581c4a0803060410545500c1d0b01031003640d9040c03042c080d6050500a00340368407a40300c00c0b500a03a00201c0c203406102e000174120002d140d0a000f0fa04616601e541140580d42d003031800c9402010030707584000ea00c6d030520030514141030400c42052132140c414001e0140c0f164907489c20051080072498815140c840c480118509598035011ba5900410200304010520a02e2030080c8183d0303000b580d14a075000c100a2009080b03070114070030030001d5401840b040340280c4040d0403503450004d880c8119203040070000d040e94140f40905108451035038000c0b0381041001201d046503044040039003030031810751070039115880d21002e80e505403808000c505440c040052540b00101a610040074013000155074545440310020740c07007a100800006da042d140c05220358400109280720b0846142001c0c104408118107482c190800343c001c50700281c07a41d03000b141c480549400760025205184040c20144a0402c88402001c030140c204842c80c84c1d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 865510125 1250 865508875 865508899
    0x30709050904230615010c02010c021c08030c12150d120203041703040f0503030702010504350d03050105010315050d17040602150708190b040b09090d0e 67
    0x1410184140031110305a0742400c460b0784518100d050199520500020081803107a01a46408001009071040c0504400180d101d884640156216480180020300084803105460018186400e000c1c028100c03007030362060303502c440d1b0b65548907640080750089810080410940120381e0aa8005d64100210964140c1e01140c43d00201d01c002c00c0305880540b2264071a241e09916603c00c1089030014480b81c5801e020746405aa410380e107a038441c0c865140d015040e480046200d1030044204c811269050312103c1c54075151107040d0304014098901d42011003500e0010b2002c0400455440000c0d400107400f4191403031561002600319038041c0c1013941014030346221005102c90f100c802100b80c803411601c525443d16285030245406032500005224580d010600254240d00010039084910f002080208160fa034a0412551000c0c12150781f03424034030f0105102c0e45070425a000240c85480a000441c1c48010b89001c00c0e40344030107440c54840b03a40134402040c44198441c40c04074082404540c14183c0e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 865511375 1250 865510125 865510127
    0x506070e06210402030c0a0801090b0a020c031b0a0506070903151b0507060f06030b09120f04090225080301051302030108250e04030f0305010e07170a150305070602010608030307 78
    0x2e014038880e000840601040540d9010082c2402d0400000d04582c0d2040d181c0302c025004e415107032021900c004401d03003c10031541c458000d403058856050700450421091500f40d00503820310468500d414040c03100140b000c0740d0306205151003590641c0320650340c03519524150105102c61070b5423170f2a140c03808000514020105408030050841c03413500a480380c3d8103081040082450300283d00780180340040010412080000c1d02c1d01c40d40c0003106460184c1d0b518a8016502c0c8100203ca00c40404108000c6c491031b05182d0107010f821100c40d4056034110214082c04603c1c041526055036401c2010004003c2840c0980c3e010103003466a05081d81103524000b4400e940310300c800c0c3c11001c0784602e4150500c8a11401c0d1710310009154070010703080d0724200343c00c028010303030301e032070380e0500000d0802001080c0b40a1306d80546014004540d40c101020039070f00ca500b02d000c8005450359030644d07101e240c006c1405a1594103580510b01078000780050302e00c2c040010742190495409032445800900c1002601 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 865512625 1250 865511375 865511407
    0x17090f032a06160c030b0c070f0828030902150a0c020906041401031a010531020912070e010503010b09010e0702280309081c0e060d090506070e06 64
    0x7580103014403040c5051980015400303001e505080400c0040e500810340500018500080469000d0b0940305016250705088160700d100340b12000d0300d0b8200b103400100002d64030b04001d054012403624203d161070a05126104130790a0354040c00002a01c030200c40c425450a4141603500900d03894100786007210306d040141000b80b00280181c85190450000707429600c0715080040881d415500c078030001d68580c0382000381e14043c4105002d05100100012515003444105130112000f16001100b04096268003e100f005c3d0341c484001c070494003070241d00003945a440012101480c0c11000d40007003401d00d1030314010018160310541c400ea040102d52145503c034146810b064500194450071142d1380c1403016441c00030800d481001c40c0750071590040920241c55004282d5038800da54031140581e0700d0152940c3c0d104481003044156041da075102032042c0c014151502c542c0c20140c411801c10240c9242c1c0d10449400c0001a1400d400040030400c04640c40b0764003914100c0112074080c00c0c80108044d0141c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 865513875 1250 865512625 865512673
    0xf0b030d1812080702061c0e01020909180f0f070e0907051c0512040b0304120c02010f0302090f09090303090d21050705070f080405100311030a09020a0317090f03 71
    0x800b441103101003051140400440760b040b50041e2490f0b54400c09a150100c4100d05001810803445c80c000341e510b0200c6060080311003240000b4551012611780c0741469100b80004040c40b0803e224a0110310309400081c050711001990803806810800d2606000c4084040003c0503004141c01003107051005a40d401c0619000c018040f810b2034401c1d641e4030f0101d02d001100800758003411f2000c940028400e1b50b03070006511031407007075040341810b4861690030f0b981040c2f11140280816030030340142c60340030300c268050801c1c400e0041a4901c038a640b5800b0402841f02a01c1c400b400e071b00004100304d000303441080200e161410a00d00391089900c12407841480c441e5420b04401140d848001151610b8030030015112003d81124044094290034604019203501620901d0b01031420554a803d845020b8410700140040001616140d80e5596083d08020040d00600f02e0740020205001b2000c07401070a82d201c216074042040c85e5440c0300b414100070541c103002410502c82d500088051000003401840421 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 865515125 1250 865513875 865513889
    0x16081003080a0203120a0603120206070c15020d05010312021c0804030807110613110a0608010e061203070303090501051012120201020c031804050c16120309060f0b030d18 75
    0x14030b45802400403821446205c00070014a100c000602c6000c0c04242d0200d4222441440880c5030440e107001c0690f04c1d07030411100c12020501401080010852380c5c07180302003010045100500d4070440002c814121542038100340e071760400640c45c2144d05074042180030b1040261361511040022248001402c0c540c008200504104040000c14240380c01008001514003030071041d180b0134640814281c1708602c0300e5005542c00e4501d4504405142003800300207095404650b101d4001e6820100401e40134000a400c83c5d401c600d640b08a071014100a00290507564803d64000c11403007443d081150035070b040035146092200d125102044030341032820740d88100640c480c50404501e078a410040e030080c000d03c2007030f105600002031290390a8082e5640f806469500b124200b080781c03105041c903583c80c02059000e0540300c00d0318111101080b4111a160700104807880d012690b10402c0c0da5000694005c81d518550780754030394000080d140740510101c1c0d911000c6181c4007c082d03100c2c00c0c6509204040c1d100b401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 865516375 1250 865515125 865515127
    0x3030409020c0304210204050a0b0102030d0e0a0f0309181a04050403020a02030313080f070f05090903040506040e0106170609070c050a0602040605090901150e3003031608100308 78
    0x2e8200d0a0510942d4020b0060b01980003607203c01c0648a0841e05001d03408030722440c07501c40012060001d911030000168810b078025400c100c640600007005103e807803080e80301423061007041700000e03841226040a051007a51001041440c1060010352294454009074043c0c0c1410051100e41c01e80821480d54030f41e08581c04901d030f454600b0243d0916094090203034050000107103644d004203907542d80004507299401140d84907140800010340369a500d00905012207135500c420001403030403484040c0c106020005032440c1ca96240700003840381d1311543c802036083c05850010828940c0000e0803c0d2864520fa00c401114a000c1e4002519801d00800d07100c00e002188210800f446410000026080d6000004541c0e0710b4803604040c01c179820416a040c0305d43c0d0001c00100d01c95010400000d08440c0e10388405815110325070030420080d01c05051089181c05034400d8040005d00200345c0301310400404061984c070304200c41825241859654944140010941800b020802003050780303003120340144440b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 865517625 1250 865516375 865516387
    0x60d0f150e07080606030312130210030c020c041134061a010305060901051c080304050f07060507030206070302162f010509061606020c0d1706010c1a0402010509060a03022101050303040902 83
    0x4201c10030505034080d40000c00504840e0098cd015800f20070301e40400d80886a800003045d0070042542e0241000d8404010140b101074079403070100341440d0008420000c0c017000500130040e0030302c441c5044202500c0f8541c440c0e4846e2041892102418240c0d102881c0a1040740703400400b2481580041c49214094890312002d818001406d2402401099000580c9580c9040c0341c00c109903541303c0c05230040464011900d0003d4030344d0043c1d0840d406958560003a1041e9510808260025086501c075518600303041d11000001401c55800c04021411041308050400c294510f0294404003c4000c00d040c84410000350a0f42e540344000c0d28045490340d88460000c01140c41c040c000b0b400b0366031403c1c5640c0701c1c000d0320841094006c0003030400401d0b00c403007808046d5100001114010200c1c171010380340d880102d031811501845c0e089801d6001c0e0060400501d800306c00c101186440c0c3c004103600380000e501242d03c5011486e800412907503661592461806941030900090b124030a9201c2d4200e01d81e40080c01c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 865518875 1250 865517625 865517641
    0x3110102040f090203041106070f0602071b0303030f0b0103020f1b070e090a060b0411192c09060a1a0714030a030e0114070206060d0f150e07080606030312 68
    0x4450180078440040080243c0d00d8100d00040d420176513040724046c80c0f0b94500803517803c02c4d109543e1080d40280074000200503e44400000b94450031041e600c00303888410711621040341c040c0000042d44a81e400003248040f0050910444c1d003203a40a0381014010800c00c0ca035045504283c44000d01806903d00419040b20401840d084841d400825030020180401100b1400455501c00d918004c4009124100c1088100310403540f0240c03168080c901c0c1808001c14400407d01107404405076030400071030011b040320526070640300d49010143d401540103400c400701e0400400e100e800090982e1204840f609144c43c0900c0c07541102c5000c00040d0002c2000000d02c44116031b003845298281c1d00b541d07075030700d001900103020300031000c000b03c3c00350700781445024200c41000700d0900c100d05d181c0c094103003510b07242c0801c04840741d4100c0540300035810128071030114071880450001204200ca0029103801202421b509004180d405240d06030828801c10ac100e0714003000b225840c05d414901c000c003035950502 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 865520125 1250 865518875 865518877
    0x1517040507090f1d011409070e04060f09050a11010207062c01141303020103180510020a03020708161707080f07140d02060604050610090513020c0a150f05070c03110102 74
    0x403825204d104030302511144e8000651000310141103500c20080c1c65076a103048a5a1140a407140c80e0b50b94441e50000350101e407081e4000801c941046030003040400b40c0741c03a05441c01c079006906598040040d503560046d50780420000008207441c5c141307107844108141d408140c4400700001d1a18072528012000c003540c1c410300d41140318130300004106488980400c0c1070013026000e800b089003c01e18000a00e1440d5a49004010700f0f940d120000b002d2100109148901a4009214120506409110341c0002482002c05442c0484601440300c22068150030240c0103244c240081500d603400400201c0d0225081900300d48940082e05406075441c2090f02d0310b200c0201c0408242c0c0c28a0041500380d490940d40821014040c01040740c0c1400292a0b4500b086400e40903413036840081086410b040009090050080003225a840c038010300b810b0088440c039082000030a011989200d0006079281401c2c2e492058603803100c0060010001c5141c0300c000a000301c41061005424000e02621111104001350 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 865521375 1250 865520125 865520141
    0x810290a081c2a11010306090e0f0714090a090312060e150411270d03050c120a1d030a0507080c0112090f03050c010b04061517040507090f 61
    0x28102e4074924010b680c1034200c0098181a800003800d80c1c8040b4089141120180c125250801c1c1c0340c0c0b8190050342e54003001307081c050760b0841c181619110009142c45840c0710300a000c40140c4041c151018211030a0b5080640395001000503c03404001030901e80c0311101c40b00d074031000c0713080e0000700981107040c10780700181520701c40c0000c20300381140400c1d22a071100c006030251058000301c0d0095803102c410002034800b40c110120509205002031010002c00d07106c0c070131110450030741035816066100003003400e0040d07007032055010450004810756250310802014948006141d2402d0802d850307901c00a0080300f1216a5240d040003515281030560340c14031008254035440401c5401e002e6580b140d41e0b490300088146031340810109030181100844038090325044943c00f60913490701442076901511150050020003101e13640c3c8400d21142070f11a131040e50068000e500b2a00c070648140c0100504012140d02140d40450241040c4000207800103040320513215102008641040f0b4404900010640c00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 865522625 1250 865521375 865521389
    0x80a0c02091302120d21060b0d0501051302041202060318070f1401021209091902181e01120507030e060f060a150f0c080405030d08010810290a 63
    0x30240440e0b01258450205001e10965070226522010584140c0b251100c18500022916211021550b0190341850401540f1080000182c40d80c441403c3c0607581c026445980b4100d0703490b0014002440c040041c181a5950003005601d000e0418071040e10840805400070300410b404000304060000c05150890015142da04a130724203951040c28030000076032840341d031390040c00c0304010044551000c548904010b0301840c0e001c1c83e24403d4001c0c00071210b00188251a10304900800c038000382d080340000d1031042d26111644500040c14010004407002136505a00082400e0f0310306d086e0740e40c1110440c0910221480c00203050360b102c0380240d001e8031000c9800a62801408104107a101044505030300900081d185a041c0c2502c1d030713002c28514922440fa507008500c600790112105072140b042d122015224040351802d0070341c0d90004c40d1600f000a0f0b0800c0110312124010f009401041103039501001070080103214000440715802c19001584408071105120000381d50003035202e03030103820000c000c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 865523875 1250 865522625 865522639
    0xe03030708090d0317090105010f051203120405030f13050306010f12030e041113030501050603071d070203070b1302040b03030a210b0603010e240f04150e180f06040f080a0c02 77
    0x403210b2011f000340024040e0100c80315031220080380c00c0c01c000308076416071003182005515060134080309003182c80b4014421503440c882080b12002c079403400d80180500711590040e28450b00c0c140010142000d40c16040341d200307400c01e104200050b02c0919040b40740c0a405040c0203141c502d044020030058440070039661075008000406070300700d120074100d50003168000c20080115031682401c06488500343e1040036212484c081c040c002a000789030440d50414402e00403a4a440d81315501c100355100119034109101d44900c4424095003024042c0e61303201c4030200c018518002030f0520280c403890842102216815104d01c0c600c440224981c0105d81c42040100626106d46e500c69880b84040c50890398241d2800c20300b80070a40d40107051808480c1e51070001d04800617048400140b00007819a07035036211000980000006000444403c0c8038000c182c128540c00586103d024090b02e0105601d0038104254880003c01011400040080312229030041c0415611200030204072150035051074041d511100e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 865525125 1250 865523875 865523881
    0xa030b0301020f0d050f010f0303050a020f152e2c0a021308010603030c02090a0f110c1b0f0607080706051504140405100f0e0f030a0e03030708090d0317 67
    0x4500c4050501045010700602046d500c642103507444030820301c5616410b00d108441030000a00a50191402c2841c500c11540c0341d0503074251407880d00047c040081401e0440d40d0520041d8001480402000a0110700c00030480020207561080c200c4107114844094240c07000302414000c01020041d50040c0c0b4034602009030809003074201c0258005031611840d86290348002800d18410b010740400c0307a81548590012100c030b5000d1010240004101441c55503844001190140c903900c104d40300300d0790302220241c68824441c035040c508540e0410480794a50030346103424403a540d845031a800e041c0f065800640b01c1d90300e807416880728081c80301d00514040c20101044a4025070550912611a0460701840805082408010040001c2c0c0d009410751308416000901004c81d90001c03c4001c100300c800280c0341c00484451824141cbc22a14698140c000066440080390f000030200e050402c1100618079180d4030303030307a408954401c002c00310780502d20f11800c40d0281401030130854052038405641042d03501d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 865526375 1250 865525125 865525147
    0x7050d0b0106020d0f090504090807050a0b040506330d0510020d061d0a05060613060c050c041103041b0b0f09031018080c10020a090303170c0f0a030b030102 69
    0xc5800d0191030018800c40f07034020031080c429120901007165036140c0720a6507050009100181007050313405d9401880401c95000000c00c200010000c2074040d10425072a402e003450700b90300b0428054003940c80301841c6540652220340c00c030021801007520210f2105040f0300d03400403502c4c458400c50054018003614210f00d4100b550f640050151010302403003044515240c0018151440308078444658441007040010420052940f0954210700020241800e0000c007240b080c107244507a410036400107203030310800c40400604020300050a18120713000e004454449030041900c3c08000d202600309401c0703c51004425068000c5000a00f80e2008407070754400f02c241c100c484036445a98214041d00c40c8802007105011a841001c040c0c41e10421a0009413415071642e0b03040b80c1109014003e14052074205001400c411320061403000d045071074442c606803450a024000b80c1c0029009446241400c04004400c0b840b84100c8103010b441518550311031802145c102d004290302e44420350150700c001340202d000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 865527625 1250 865526375 865526393
    0xf092c061203121006021c05090103090204050a1505090c070f0c0905040b0103050610051e010e09100333020307021c030e01060b090a050f030307150507090e0601020d1107050d 77
    0x1300c24585007440c2042c0d450350100e99803049900d000b494001504680c0701e0781d5110700000c22003140145804100c20403940c00290880d0307816501c0e40c0380c1c1c8e43d0380c20003000d500c4c1401c044400241021a07003c495490106039603401486550300041c181018000c3c020200070441140e00c01401c2251010041c600d4280b40c4043c03441400e001c02e90b0341e44180700000d10b40001d192007441c10388a001d41640340c106188510101c0321008110101d0520071185518030a5445140d03903944148521000001030130325500b448510f03441044900c84042e5104100c3c0483c0010010744920b000291020059881e550342404909000b28062600142030003914010402c903415004549103100700c50007000350540e144480180e034424500303000d4102590001c1003003071386030001e030940401c0b1001e01541d14004860351005200700856850022540d81c0d0402d00100e564060b1035000901018800000c503400c00e000080e43c0c65075400b03130078010000c1c201c08250140320180001e00050038060710400103603c40785081c80c16 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 865528875 1250 865527625 865527631
    0xa05040305070f180e0c0907050c120915030f041e050d030b09090f0a14010e031908060d24021c0b040b0a0f18060b04060f092c06120312 60
    0x600c0d003000d580c10b0b84c4910034461407140141c3c10000300b103400251400e0050a050003081d42c001c0c85001d00002d02000310910800b081490030605076030391550444200b04c54214064070045070200103004121507624420340d419042a00302900c6505031503910074000b008608014024524010b81070a00050307501900907541e0381d8030445851034a50b684540382ca47d00c0300566880752055001414503030202c0c10070000c114928088000119000804140051455004424000d40c41001001d000003060b8400101a0441c5e400c851441c0d0b110081d03291280e1211a80807004d192035142c0b001c41012070b08646c1142c00d580a07014030f00c1001002c10714190002d055061120b400756042400300c400f203140079641441651118402c03640410b05000c00411980324800340c4501d41c0b42d884001080081a4a000c0e0005240d650b0361840c130108421802041c05aa5a01c41c004508003900e03400842d4155012180e000e203c00a083d4155030b030b8242c001107814140b10041070b601d0000140c80215408048081c82c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 865530125 1250 865528875 865528889
    0x10e07050f1c09110a05030606060d09080d09050706030c08240d0203061005030106120f030804050a0f0b0117011b03110909040804031a070903061e0c020303061002030418020a05040305070f 83
    0x43ea40d1b50703041819107802c0121140c41d0b0099041242c41804c80469000c040320500401c980c9042031003110000003100c840c00760548690744502e008121465043c02030405400192811030624208804022001300c1266410fa200440407c9592440e803101151001c038150010104e4900741440c80e61399040c10355a029003801395081c0040400d01c28400820298000d074031900022201205d07440444034942c0c05442141c190290080d06008100078020285405000b101604040d514150039618107000300d00602c4040c1c0d040150090700744c0d41c4031600c5c00d070607040e41c100428450b801e00e400b204280314905500d43e005200d18140000c0c011000080d10a0720b10903a103054010101c50030722241c004048500c070002410b8400d0902c0040d0306030300700e016524100085150040443d1002c041520150b039070001c0164404001c100c02480c1c450000001002d40e40082c42c90581000461488042403c04220900d40c00240e0342d0316043c4078501305e4004507044800e0f50032103078551280001107256881031030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 865531375 1250 865530125 865530139
    0x51f02100c0e01200a03140f03010306050f0a1a150405090a0906140130061e0b010c080d0509031306021621030f030b060c15010e07050f1c0911 63
    0x644031503104c2c10b100c107403440c0d404014408080503a034112403940007030403840c1e004282404002020161071002e54080c500c6a071011410749041ca20198500100074a840100341c104583e800c1079a07161880000b451005035a03818100d15104640030243c802d40c0e003d150041104010030800021725800321a60314802c480602801140d42d4445102d24000e01a011000d007410310600418600f41c42403003000191a07225058202058965034215184406052400d0100c02540100a82d00e8402c0418545090a20102a4181d40c6880c2c0d024095003042d040180c0d0b5074008074462203410410394400154040c42c1d00300b8540ca9140003501d400461003d44216254441e010416040030100000c0c9642c160011040f00403403500c1c00c4a600b51040400c40625036601c00e45042900d0707900c000c2100005080040c1f80c144154002440e59510503400842c0070390101d01800720032984103040310000d46503603c0c8203032118510304841d550401040e4504c03220b01d1409030720200300100300441c0050007204031851 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 865532625 1250 865531375 865531397
    0x1517010602010c080c090a09020d0209190b0a0318080301030c030c060e01050703030519021306170c160c05300c03030301120609170306030f0106051f02100c0e01 71
    0x20382c240c905000701c010204500303d000884102556002d07000c1e00b00d0042400c01da0b250b660294400300d9220012030503040f600002c030f111460034a203c80280f201e4403124000c120718176040204103d40180f500e0a020541c88000904601d1003001311800302c0c44c0c01c5070f0b60036580d507903070316001000040911084031118a540d10001d25a03007d1803203034018071410f031100c40c176000d0196011401040f00410348488030b01c00d0310018142c00d00c0b91014001e00d110b0501031540d0541041409820520351103403c40082c1595420410080d4000007940e5440000300e021850040141c90544001c0b80300350041e40d08100320202800c10034108030b414940810704c590035150100c008401280c0c642c0315407204150958401c00041141315a103000401500340544800101d042c0d00e552483e10a2804001c9807400390004000e04c02e4a1509200b01c03940221400020001140f0308004280304410382394032510312541d241d804486180c000d00c07104200000d1504104000035044001030504915062440e0010f030200d019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 865533875 1250 865532625 865532627
    0x131a0333040c060c080c06040c06092c0c0c0d050414090403080103140f1009020922060f020c1e160b0d0207020f03061315020f091915170106 62
    0x541e0250381c214900203030903400d100341664000c0c6225022240e0700410410040c00000510806000340c2c861075081e85050724001008100c181aa0010300031841105440502907141302403101205c0400d0790a000540d0700d50760060300c0d0f030180415102d1580200c620103211194010010700a6800a0000c2005502d800c0c045c003121450895004001c240e007000140003140e0030b00c0c020f03942d4041c0d40c811111428001609142046280817812001c240c80348414021454092842030340308110207121584a8411060f00070a10080e60000c5c0400d0b9580c8800400314400e034040390003111420040711007844a81c1504a0041030461000105000e00c814011070364208841e480211040f51194504040008102d0002980650700c00c0f603000c403d00b46070350101d49042c46100e2203005003224804070b0941c0d90800f0103500814001041c040c81c41044031802c0601c0400c1540c114030010781c4e040000042c5070403a03201c030361090781048203d00d0700c02c1c4242200070340c050180d1800a1520040070b2150b6a03401c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 865535125 1250 865533875 865533973
    0x6070c141903050d08180f210307022109150a08150127150f090906150c030c05010e0a02030115050d0305070c0306021b011a131a03 58
    0x7001500920304c458030403441a50f030346800c0b480c180301301901c0303103411040b03540361926800c4079a104d604880e4522840c0000a0389860102048001403861071400800094507600c40440b0603400718044c190b00301c05c5a0b503550684080b030f480940701d01100c81c1c01c5290120240c00415000300016418000a010900d0b040052244100180c503680c10700c1c0300d07202d5200c0c50210b0110301030f036244541c1c2c000040c507180c2004d2014013070381d46074551030729140400300020403020704d980042502c02c0c14214100f100f01c0910020880c003d00700c1c030b0400c0300010545401c0355540c00d0154060038541c04d10320b40c141031110102c1d045042607c224000c21190703449800c0a000708881e40728840c1d00c0040300d80540080f9028400919060388a286803e507525100c0e82c8250882e00300c0d41c00e070550a001010940d0083c0000d10860700503104100306c0505180f44500000da07410110b40398000d42540742c0350000d41050502405000309035005059401000003101114180d4014903103160400d8401c032903402400c800d0074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 865536375 1250 865535125 865535129
    0x6050903190308011818060608060106020c0105040317160303020a090905011203080c1903092307140f0901080312010e010e04020603101d0601031d0304120206070c1419 74
    0x2496000f8940c1c80d1195081c89131040441d4070407240e03180d800c1442c0840004100c414a10300c5664000380031810480c8031484e094050b0000000e641c803442407010b0340e0303810900783c40403039030303c221429110345192800c2da00314000e458103190324041840314101090b030540c0141620300443d41d14180f699581d60b14171801d9810070703c5010482445140b80b2408603100300116507000d80742c101003c0c41c1074a000c2c401c0c0c030306c03529000660000a5880e0400002c0121305c0e0079400240d14400e2162002c003a01d908074503111015446a002500d90410940d01a074a03004141160064010442c0e0301c650381d64082c41c1e45030b0780074140350044000f12a0011074000c0d40c0e60011410398000c290441f6841e038031039091144030340c406000207803001d0380400e0001d175043c401c58084141c0321000720340d6121418018005401d0fa080440c00710b050070f54038180701c02da551000040c0c40c201c50300d00c0c40102022882d40041946441403110180c65108900c2b40860070150703440c10074069043c2030321344191407440d094642205003114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 865537625 1250 865536375 865536377
    0x9170d060e091621080c0606041404080a180b0a030b1311040e0402011806050904290f040f05090d02070803190522081e06010e1f080106060509031903 66
    0x240f01c0600c0800030501042d029120001c54000ba244003940300c1c180c16800c80d000c05485d5502010800980d41401d01444005a582108100301030900b69100c0031075024803103d25003041344400c0814512805210120014502000da1564a06c605000240904a080d0040703002e4003040884030031383d0f0858861607105e0b5107402c0196003002d0401c0d07984c2ca4140c5001d801641000300040b031040191300fa600f04a0700400d2586c41f4141d56042650912041d510045814601c0e1741e6030be6219010114811400558098102c803000300141c140300c0003400614941c0c0c01284824034010030000c22507000101170007510700c15000c0300c0f000b070350324510315581c1c3c0314250050b1000c0b106401d11003c03490103040a0114141500911a5a01150031550340980481d5112249540c8000305070003031507103400c03403c4c40c40c01c581030060303d00c2d913050800c40340c9400000340c1010044561042d0b5a410b406226070050050050b01d4020f02095a40c2d040003070641d00001840741c8031340030395001a0070b401c0c40c0303210000e401945 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 865538875 1250 865537625 865537663
    0x30e0609031f0b061204120e061902100903110708010c020c04090204200306150909060d0311060f0a1a0307090b0f1306090c050c0a020409170d060e09 66
    0x41e44403512070b80680c1002004158031079000100399070b14036014000d1002c0c01a2411050f180c503041ca01c140b00b0b050808082072000305201002607454103822148150b0140c1800c40b60111072060032071410b6070301c1910307020079454004041c0415500040c0344035415010811246419128068030f03003291200300c89180968002c06608250341010781050f00c039140010700002e860340d1041400391400768418410104444000108891f0345410036104a242d8601c6080c0303401c0250768000f203220404068052445403c0c0b480c020000c040c414030109009482e10300c01d950706421700750740c0c0c0199401c090b95a0f400e8a420700802c5c600046002040a2003200b00400600c240c134600362141000700b420000d03d075003002286444076034603210940307400d602c0c2246035000600d003450454010100e5407220320003010840e0411284070143c50025008607031540484000550306440d00c0c004058184c20390445d00240000710707908800746501e6102c03104884180c40c030020107035602000c90780c48800c00c613480200c02c06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 865540125 1250 865538875 865538893
    0x90e0d050405010f0e030604061b0212030c0d062c251110110304020a09050403020a030e0d0c080606100f140318010e1006060801121b0e090a030e060903 67
    0x221800c0180a1380c40a801d080107000808400309081c074000b280e0a542040e1034580c10344115152221585810400b4070141441140010000c2603510000c0c054800801022500050130309070340e84410001c00c086001810340d42420b0b19501c020400080c401007542000700009000342d0340c4100721108001c00c40d031000154909040d01a44d164040c03040c100c0c8144104801030001403014400e400303082d00b1b0960000e480e46130038410088203101039000a840e42d41400c0500c80042d40004040541c0e9605d800c0245140c800c240204050008908000c0c01c1d041c80c50000041043c0c0100c2c00500a58050315074080c558002c0c942035600ca03240407229030000b580c140c8201c41441c0920040e40c5c0021001e4540c88a84112107085425149020b030451140d070020307808240c50b00c403c1d21400008228130305042c03507158034281041c0980307016154054503440c5400d4200645412204075003000d0103902040c081507040007542240e0b80c0500f2041100856a8084d900c1c1c07880c60014280e40e2840c40041c02020724074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 865541375 1250 865540125 865540127
    0x40915081501050a091a0301050a0e0f010c050f160507060309020424050402070c0305011104060f09060e040b241e1c180503030106020d080c070f1b120c090e0d05040501 74
    0x30000e06106e4460b0f072115101040c907030b0300f0700038a0b02814a454012440f03400c09401030b8180310000314140b03841d03850812070f20304182d00b00e0140da61840003203401ea0f49032201140c41c0032425081c3c190090a0303000d03035a40450442d4156100707910f40c5000340d1f000c2088416109400c0d600c0b005d03000000d01d010344103800400043c42c05400910480d0300c1103c0c0104c043d03a481d40e40c1ca00b0340301c0c4032103075205052022805020f200d50125a03402d5800d040d141080145140c00c00c0541360304a12840035008a84840d240141a16003060721402a109904403108640501041c99082c3e00400d04a0010141040102e00050402000c0d03c07070402c9900c1d200ea4020400c009040c0081c0100c800e00c107065690600d139803006c01c0041c4003945c002e05542d0003905118008450007044c00c14001c1824006000c14004000441d4608a0018045a02c0400f94202c030078a03036401c01c0910081d501c090720116483c1e03510307010000c0850580045400e200824401108604416a190b0840305c0010000a03400e00040100d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 865542625 1250 865541375 865541381
    0x509031203060d170306010e0a0e220b070f1209020913050f0d020d0909050408120a0b2d030a021c020409290903040f0e0903040915081501050a09 64
    0x300744020720211507030401da5610030052402d134003603808904d0040304000c26960405581000d80c402240c454111909002d0300d8040b044004d014002c141c40c01c4485850001d0030b08440340c3d4029040340c05052245001c5c0002801070301660412400921390f9103c10308024284e002e0b504030680c4c010b119540369914480020b8050110403419203051041c40c150b14001401404103014812a640c0501051580d0040c068500b00550340141d050a207072000b044007081c041d00603114080c140d16481c00d2039490f12030501c00580b145501c419404003400241032a0300c5082c0c1d01100304044842d0110601420300801c06071118440e48010707421502c88ad80ca41c61100306200115800d51004000054903001034403440700b460035020f02d0400d80b04416940c9084210988070641c0d0008240009500e03003424070406a02c0700712640b144d10400383d04074002c10201c4509100352009400004410409038070082c5105662a04a00c01d0301c40718007622030720b80d902e01c500d078000350b041c0c45001d84810300c0186410075074801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 865543875 1250 865542625 865542631
    0x9040503040312050318060c04061808060711011415130212040308060321180103060b030703020304140a020109031712101802070506010501141606020301150509031203 74
    0x4203000811000c0001800c0c1880100b94075529914107440c1c2c90041d60b050360a07140e4910003005035000000f04814102c64004880542d0100d10b0311240740301800c0002d940c01c0e6100c0d0825030030350003850100107004e07521501c0c4191001459009002104600b00d00a41c1d800003074441c41108a031490590590b81494240f42c43c2e8024003200061401d038014800d01c440004c20303036013240005c412105000380d504c0d081155510844510052420383c41910811402070310406603584221010341150b40141d03030003648084020300d1207010440d640c0ca400b8000400a40c000c4608480115041d621650590400182104020fa060311030b100880d041d900c0c2c0306a4028100411044031104120a131185110032005a00421040c03034003030344c01030501c90001140300c54140f12412840c414000710703020500000ea1641104c1d000c0c00d0900c106101084802c40c2c91180402c0a83c2010840c8203947c01c004c902e0740114102c50700c040b99800da000314040c04954611485130150303415032018001d00c0c401a1484c4c01950 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 865545125 1250 865543875 865543883
    0x3020c07140a08011b03111603030b0f0a09090b0108070b030f040c05030d02010e07150806040902030c15091008010b0a1d03010608030705060f0118110906030f061f05090904 76
    0x220007680c50420600350f40e001130010384110034050301000303886e03098082c1104072400138980351304214070114218002c986220b4068105520352034642e58a45601400340d480a2015040703c4101da00d03800c0c100007410040b5000c980e0010550000034003040b000c16008190750344103618500e144ca40d4283c1201d008400b5100741e44d280200c020010f404d81e01088182c290081540003c66080c500c09039160501d0100c0d445007140b0100410f02d02c490b075038440c0d952980000704407000101c2ca0014008246420300451081c4d8004544105a81080201d08003411801c10b04607010b0880040c880000c03182c40c0820301c1400101352003440300900c41130042100030b515440303200007903000944401c0003909407407259001e0005500002804003c0c84402d1042039071201904040b03144a524202030003010000003048680c11660342d0885480480c2040f044071140107005004a89038201061403490001d02079410038800c580c0d4550002d41c410340c00b044559200e1060301da1604110101d014004888c2d00100100c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 865546375 1250 865545125 865545139
    0x201030f05090c0103140603030f130812120703020f070b18070b0d0f0c0e0105031b0304081c0525090302030105010b031815060105071b080f0d03020c0714 68
    0x34010081511605204000c00c070010040e880070320b40007400322160091424440b21050041007100e4800108658003840c0380d10102e41e031000d00f5200c511410800d131300035450901034000d590408495002c0500300034202d0100940403034440318000e0342203100b52117440013485414030107075011611241000d507001e200c00c0c18005c10403171a005038a0810010343c00494814902003012280c1140512030b02c0e14034144a6000c110301c1d6034000010340600c3c500300420f810810000001540403582c001c210000c7d10404e00304545908281c42d208600d60000800720505000202900c07031145250701030540151000d4003410480c0c12000d408010901c0b0082e5004140640d1010000058409100e02c60090183c0c007038081e201c3c248103c800310460248120008039601c0501c0b6507402a61103c48190050024240b03242d5480d00c80c50408411703101003080d03001c05071000c0c10010320103c02003988030458800f002500c2412040c0c02040c3c08074000e00307a0902c420b91086a04ac0280700b501c0c081101030400081c141c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 865547625 1250 865546375 865546391
    0x207050115080d02191a040309090e03070215070c0314030405150c0c091b031003121215140f011e09030c17060708071107080c130c02030f0304020103 66
    0x4070a0303200e00d5440030400c1e0b400340c082081215418000d01c0800c1420070344003001d0069548070329151504565070422590780340341c007180401d80600e104c000280898038050003818070801c0c0050b2640c000c2c240680c0190b0310048000180c0c0b131840c084840d541c1d8400801d14140b03065840c2c2c82e03616804100d01304000d01c0200000300d1555194042c07020f44001447e81d403076503842e45a0000f0b00b0440e0501601d40503000440a1015003010301c0004080c146000100d03a48a03550304000d062030086a600142144000340c9003250302d154005492074182c110004240541d00040c1050310361454244507040d49a072103e05c1c80310251804d0140300d00c0100e030500d0710003024610031a04c00019050019400041024502c0c204204038488142c00f0007099940610031011704811102070b16140000e100d0000c2180400c00204549d015021884101c05600200d0740090346842c0d030565102c15242c44030344613002c1012001c4081c802800b410083c0b03100d6a012714107158030340c03100718a6504080d0049040c59140d90076 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 865548875 1250 865547625 865547651
    0x1503030405210f010b0112050406090b040b0a1a0a0303030f0b042406170736051e0303121801090b01090b0901060e060a0311121609150302070501 64
    0x70341042c0d00150110b281d0308070502c401d020718061081c1440700c41a4100f05900c0d0a0340c1c2c1155440118440d043c202203066074907031900100070600490010010301082051005101210422034400d11030500d0030449800050544010044400c80b4190b004c050101b050000074402d40013a0b40031106140b01040c5c4201d00ca0000d4243d8040701e02c60303603101400d075440d400c60070a211102c4004040c0c43c185400301114a2581c103404600007440c4000340315000c01050442c3c0940c015020f0b0780f81d692410020785100b090000501410709101d064400c0c1e040e0083c418983c0d403070610914044100400070740ca0a00350030480d641c8038000a0185142040618112240b40700c20300070320340c500e0f00c50b1a040c03185604051410088500300c07201350b406020035400602040d03402007408200004104c56075a00d503895007100701c0150040b40709160170707524003007804400d4541103010390340600ca204041c0d60450201d00d4045820b66214030a0411100340c84030312307000c0c80e80258001c0030340f07a021340300115242c035050384 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 865550125 1250 865548875 865548889
    0x501060f060c0c0b090105070f110d0305090102010606181707210b0705070b0a36023109141504060e010209010215070302130f0603060b0c061503030405 67
    0x3100c01c011892180310032007000305080020f40a07010140100303003004011400201140140c0388014100c01c4500441c1c0140100c84c91010102500141040401100c4c5d18009010b41c0001c4500740c013660801c5400f068550103450b80c41100c0300c6282d50003143d41d20701003100d80d12030401403926415000d0340700007003018128032602c1080320118000c458003010035450581003451004000c00304002c8240508000a00304503409600401c0003680852650040b01d04440c044124a1441c00305890700e05440040184002c40300d5032081c02200c0c0d00d1105812074000d10005810844005c0e01c040d004624500d004080d5489044114001c0e0711198100c0100c0034600d151034112900800c000f0940300800042005a02501c1e5109204900039820051160000f0790b844580a40340b4401061a10004140300e03c81d074169940112408501e6113481c0d5588001003082d00300c1d0144000090420360080b80306600c1c80100c42490310100001c201d2551b9030498501810400c4802c585c1c14081000002606c0c0d0b2010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 865551375 1250 865550125 865550129
    0x4090c120302060f06010804050a140c0d1b081c0f0c080d0e0f0f03070201081e0709060314010e070836160b0a1808010911180103080d02070501060f 65
    0x180003801e8a0821404c003600303403a00105241d0410000004000c0040c20102d0390280203540810914803950030720b85242c1c20217402801442d00510f0070061a4240589901000984004c40c0c4411042684511030b558640b00d010243c804401848406c8401e190320404250b40d1600880c03074011245100c1d07560ba0300040e800940c07035034102d03500d51180c0141402d05100c4d03602d504002d080241680714040003650744a029041010b0b05028a49001a03410000e89508401d0541100002e0406140c00040508480240e0240c200064941a030750000000c10303400c014140c03400d540c2c402543ea038030f42d4421079840300010300c4043d8070b200e4840e03c0030016541d118a4681610745d43c00c03a100100c0d10b8500646003101190160441b0901814101b14060306081195180034080c5007410401e0360000244a446080358012030166207412066010f01c00051080c03481c08034101c03030307a82000e0f11a805658801c07400b800701400152042124494050741c0754028595140319000210704295a0501040c00c0e03120742e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 865552625 1250 865551375 865551377
    0xb04020a050324031203150a051e040905010f020a02070608010302090105040e0c1f1b0b070e1903110f040c021c0e030a050f0d1106010612110a11010e010902010e04090c1203 76
    0xc802d10208505000306490407d0082e0741103000c841c13401001440d00b480c486280703042038641e42e80c0030b02c4c181c40307682080c442160000024070101c800c01c0384041c000d500c000940401402142d40c04646d0522070129203040f04e800408420f6181d00b07200c1044000c064a5003091807a116051051000f80c032810301c2c015081507010880c0c001e0350003c1c0300c00b40606058140b00d034507200c114400e00000940c040304040c0c00043e00d2819500018110001c21a00d415281145131500d02c40c03400001005070105001c400c0c88c1342510308009a8034040e0912040d10b00c0600b450300076070081c80c101c03801690382c12200c200c4424146001d12401c0040b90100e4180a2460b4094409401000e000c8600380707010070588034010180c0c038000d408020f60103400742e1900018014070040200c0b1002e41c2103403000726088082c00070007403521950380385007000c406002d070940c0b034003000e0855003406401481c006041c49a200c819406854038940d0501c02400c0000918101000f10791401c108031740801c0e0424086d140701b610710705ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 865553875 1250 865552625 865552627
    0x3140106050112090b011205030403050601030615050d030f14090a060225080d0e01022b021b01050d0203130b0c2706090904060f020f0d0b04020a0503240312 69
    0x605000400c800b40b00d009500c101070401103000300140740780c0d640c1c3e0304449000722404c0c603154040c1740231030441c400c50788041d1103441400008001c0c01901d500c0741118401c4241d10702592992007003440815400c003400074010070807036a40d01501500a55011801d001400b076280e2804410000003403080129800210040c0c2c0980c0541106403c54000d0788071006404421040e0b251400c0e05480d5602c0914070300380104603160311070044590080000503020783c98a070f544000f05d040403010441807141d81ca5010014800c2ca00c41c1c0c0b5a0410403410018030007410394076145825603c007169000b0f9407010300144080300681c0c1445c0c0104001883d803034001c1107014809030707442c1280194030210050420520410180803000d5040a55420084070b003d80e800341c0c1c0401083d5114200400102103c074000b80485000281d01e07180a11034a00500c290404602c041003403c030103a052004902075100100c02103001080801c405822210f0381d01c3c90b24400d40c070001e04117014030002c2401e105803541a1518544 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 865555125 1250 865553875 865553879
    0x3050f0d1e020403150506242503021e0607050a05190207170303070c030c02030f0a030f0f02070b0403020d0c090f062103020c04020918130c062c01050403140106 71
    0x4484c4030780e045d40191500c0244007038103081c4006425138100e03980103001401c8000b146131013003a03081d050b5448040039a8404449501180d039104401d250f01c4401c900501803900b131191000720f0100c480c0c0b4064054802040c8503a02c1e80c5080e69107a10482042c010300c4818031840c0b0354000e40c80307030882c6d0125895018041c80351038120011021192003044c0300300782c1c00c02d004006241d075010039402c83c41c0750140740907411285070380003181c10080700d854601124014610108145500a00095065a040c0da00d600080e030038044200c1c0c441e4010b00410038070840400003040540340001c0741d803ca0602800801d4035148d554407801003203d204181801c440350701c52204001400580120078600700b4400120703400b01c001d60303a0080d15000c143c9110761241e503010840e40099221460f81d801e61044040010b10142440715070388103820012038044030428581200419403c0c492804115000040e21086800301d00d4495020407220b800080c11341001310a12000001c110510072140354078000c0000000e504e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 865556375 1250 865555125 865555133
    0xf0115061b051f060b210601090609031203020f0a08040c051503071d0d03080f010602120d0f020921070603050714030903040e072a03050f0d1e020403 66
    0x20016200340950980c0c400c500d408144003090500e0043c81000c450a8035000e2008100010b19668000b5404000080780b0b98040442c003011a28004082c07511381d25441e5580c0c0011240c040080c01481c0003d070604004100098070b0a400581c0d209a13810054144101100021041d4000c803404000052191043c48140b14480c6008009003030b042e201d080d5002413031036008046100c00381c400001c20699030b8544011490000d0501e162807401401c0c04c078a000142001000d14100360360052901032104000128580000b039104206600c000e00703241040f4910080340d0040c54a11101d08420ba001c0100140d142d5610150b0280001010784c0b54030440e22a0404a241a0301e58109100b814075140c01d2081c40f5402c103032030300100c10100512a5881d6200c40800b401c50060358040c1d8000d08802c0d0034007007180c0c6c02070041c0e03489800383c2ca1150040300c61855000c80da801c0c0d4410183c00710380c04200d448810302c00600104290040d1000100320700d80d480d58800e0000000d0358400440b83e80c0402c0c10b000304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 865557625 1250 865556375 865556387
    0xe061905180402160b0a0212070e01120c02030711040e060103020d050c0406171507020304051c060c05120a020a0e0907031503060e0c0105040807090c0c0c080d09080610090c020f011506 81
    0x11006c9410210300785083c3c2c80c41c1e8410500060011414090048803182c20303607114020075283c10382800814068480b145902035079a4120b41403c0f540c49102c034030440c441c0d040921413400361072540f00041406074650b4003401207081c1008026286809041c021042d00d4589000703180041004140d0b48521100f20071316103050078409442004080c1a820034072007015400400d60b0300b920021560740d002031100c03184031503002000607401803c060038001102c1d5940e401c0350281640c1c05a0f0442d0088a54411009400300d1060441d40c002050304101c803003040713050664802d41e1194241c00e00050054412100d0111807290b50310437220720761180c81b1002c628505004000d8a00400e00b0710b5030500f1300f080c3c080b5171290714501400034003a50b1404030300801c903c1143d00029051300030f4001c0b5070a036203880d03407140c40e03805010022001c074204003030005022100003020342c414482c101c098101581054400e601400300181043c00318411035010f800c070031b80d00303102d0556444441c141a002c0f0340c2c5060300103009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 865558875 1250 865557625 865557631
    0x601060f0503060d120207091506110d02100209211b030c0918011803050403171c050402060d0213090e0a081b0307210e061905180402160b 61
    0x10003505100344030180d115a11840e8090390b201712612905044200101d1401585d81d1003a541e15041c14003060713042c1070003404e81c8156803180d0389554485442c0b107400c039900c040e5a100c00c0c006a000001108134814a68013504030340100909d00051416400414210f040e10703a122142d454203d180601401c1005126021400900341c01a00291490400040703d0076001440c41038900c8540d031025000c04003e6103d480c00300c210b119003c0000c046800c3c01003c3d504240011189401c08440301c802c03482856007aa82148520302c038150651526502100c060000a001260018010300c035408032046180041c2c410f0801100001c01824a48400b02c800d031b6a119030b508000b40c021000e00d001040000e0204e6a0308a1206981d01803070f41d05030402440c1d840340b0007001d4200d9000300c1040542100d401013800c4000410355880c4c2030b80301000d041010900c11109040d10000c220627005d040036000380d0180100040d03d100914004442001050603079001c0480c12a8407010b60ba0340d0b100f00110350800f560 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 865560125 1250 865558875 865558877
    0x2114100b0306071b0609020d05060118020f030604150305120d0b0f09041b03052b0306050f010e060d23070809030301050108060d050d050d1d030d02030c1b0601060f 72
    0x9140d0401d440f01601c1401588510280400811558002c0c0107680d002140c003150702900c212110745003414a19181d000a028215545040d05404240c03a90b00c0c0c02641e007200c0358086214038584617103007000300921000340c07161031559103080c00202150b0b003440440000c4420320500395a60740e0300221042200d1030350601c030384034045002541103143c545240d01a4091f90040e105c408003040b0128805107038915520082c5a886442d09810392045a01d020f031214140d00c041c0c21043c101240740c16000c2d1502400741d250012038280c07804800f50303c1143d4500e6a008003506e110300d0f007444a0100c0081d86c60040b4040885609800c1e410460300c12107520300d5202d199494441040d0400c40d60343c40e101e02c018410356040141203000300e9110303640d0481b280b0b0040da01804442d18074070200005007580e0044007441c01c103203141c07040040807030074194000500c140d505000f440c54041007414070b000940000d000041020002d0001c440600204292010300a0750000100f00c25032400300002e00d03c842c01e101c130070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 865561375 1250 865560125 865560133
    0x9010509010b030f030d0e100e030a0f0c02011211042c010e010308090603070e031509120703091a1c14010902071e0203010e0102180a090e072114100b03 67
    0x8181004088203403010035500040100c3d80c091040481c2d0b00e4100d803c0740d4114a28030b001c603a00f1218270008020000380029484904e0103d400c0b1a00b80d41010405002a02141a0716860346050007103501038600d82003140040c0741025207910454034250551110200c074050710503c500c071080000030750340d8010701d501c06901149605640d82c00080d8026210b5042c010b031000310208600364050300391030ba40b00310090115840306885501c09005560b003951802070074080c24074480140d40c440401c6a03481501a207c0400d082c1ca070003009400740c0318100101e0181c000500420000381c1d00303907240d030100e82040c080204420202c003004039046141030303005011152040216000151420184c00001c05840403405200001c0d80003007400342641d41c503030041c00d5100252108138000c8085201d01d2200e4251340400f84152155446000c5800000000c601c55011031310030040642c944e04405080010b200321803581600a95079a8408110110a280e0f640c101080c0207210920500c100007074020120014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 865562625 1250 865561375 865561393
    0x207090c0c300507030c0f110a080f0c0904050708060709061d1005071b081005011706240d03050405191809030e06070b01030b0a05040b01260609010509010b03 70
    0x8028501148400340c424848085600ca0906021b9441180300b0381e0806100400e2000300d1a04d004414000e10703c00740304654a001c041013010300041e40039045030b8480c008103003846007581000348200000b8800c0301c542c8901d6402249003842400001d01a545c80c2d2205d08801d400c041c006856025200f0804180550002c0c1c800c903a541c95100303428a403000c40c00c04a40e030703040c1e60034a03051003055024028601041c6c817038002240d003000142d4628280192030304000c51b0762140d140f02c084414010a13980c0031351000c004511040c5107009002c42e48912804100f070104003800208014543c82001500451408101000b00b0b080100c604840c42c1581222814054100302800c201600c500114550f0207a0312a01d6008044c0610880c15a2200082280761910801e280c1203581c0e540c240002c0702c2034680b80c404102200c101380107060049600407030301c02c1d0680c02d040b0b5402142148000c0c804c010b44102615520780c1105000b03440c00381c0349100000c05c4c1840d090500609541741000001e02980c043e0360701e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 865563875 1250 865562625 865562693
    0xd060b091f0312050c0604050c03012306120708011406010906080405121c02070804060f110303011503091401091e150b03070315060501080f060d02010305070207090c0c 74
    0x1e00030940341d00c8280b803598440414003c85070790049a100e12424800c81003403005100d400601c1c9221035208400070300c900301c801002140c040c0705002c00055052050b8020446600d050322800704000c0e001c1040b03d007156900c00800d070941d000322015100741c0000b40b042c08038650b80511000f01500090030b040495050030303580d0954401e107012240002c02c50215030414030507403d801400c180c0f0410300b0190346032640c0342081c0c04a03506c14800d42010440e4103921181c124006e001c0030024a20788400f41d0700b540e00c0c04020242c0b15850b2856a42016520840840025100c0c0e040d041040080c0c0e0000400980ca40341c0116507076036841110440c215081800d0002403040e50601116a400003c0400c0c002c01200c0428503100d40c1d074000501c0c0c4041598006d58402155006000b211400d136104909921081040340c00b00d03071701303840268021b03035412519400355001390400b503082400c1c0d00c1100c034040c0d9184030410456030304403000c8002420503d50001070000308040681e41600c2e0f54150240260100301c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 865565125 1250 865563875 865563931
    0x60e0c0d11040b190305070801200a0c0804210b0705181909060e09060109091e020d171c0c211103070e040e0109031d030c0d060b09 58
    0x1510b101d6a1980d10000207030702c819500812610f0400603e41602d40c407032904a480d00880d024800042d0320f488480980840b05550144248813080b1540380340ca0346600040710400c00c1c00100b40c40b604402c05c000500084161020441d09904d5001d0000f07030b0015103401e105403403024024a00704101031046550340307120746c203030303420070070710031159001c810040a04e81d16014889230f0100c0c0340d0501e400000113280000150b00751041204405440c9141e80315220007048842c204805003812402c0d10243c80706d81000403c035100c0f5030006000c0040c45000e41d40d41c03105c04000c44e00d410041980416003a03008120081040c03428802c0c5030081c445030916020080044c5401900c85801420440000f0108007445c0d1042c0c9410030181282e5a4074074000c000641419540380b4102e005618014400c2000d25043c42001000ea506545260800607445014101c074201403281c41d03418003603501c10300307020758a2441004105111381c8010550500307403000c108840900a205010820846803e0680f1041c400c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 865566375 1250 865565125 865565153
    0x110102011401230916020d1103070b06062a0c04050910020313050319090605130e09031201260a0b012c0f0907090209061603020f0a060e0c0d 62
    0x100007442500760100e0f5003581c81c43c4404643c020b6002003d000c11041000c01c3d6444200c40f076004c440c043c00943c14100d6080030707002156501e540090201800050941039015086000140028100442d001c1e040b01d40d0b12042002032000e007410810394001c24424400001105400c131030401081c94814102900c8075191310010180d1640040000c600b0704c0e200300f02151103a009800c907529001c08a140019100254041002250321443c0000d4140c0c03080c0f0403903030410444402201d40394581840c410104c003001d04136081c9400300744042400d81d0200031000d8000c02e5503401440d1440c0010041280000c10302e4009649604000808008078060300d40c07072411110120b90102e0300107616801e0b00c101140c034040000c0048401c01c10310000c5c03401707180c1c130602560f031100650754000d03071312803d52041788114903a40341c01c0801404019550303800d84e540c1008140c042d00656188406203c266802c0c1280c0315400c844260362486210341c1072408118040d0044d0054a0015000c5c0140d20344074200c1042d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 865567625 1250 865566375 865566389
    0x80906030a1e02030f0a0506060d052215060911250f03021b030102040828210e030a030504091503060609020a0201140c09010f050f0a0c110102011401 66
    0x1000c10760260495009081c1000b0390000d5415a80c4000b41000203544140c40e08900e61170690049441000c4030301c40e0b20300401008003102c0c58008413107244800f4200c0140601c050031490244d00452580c81900b00000e140b1400c02c00303504985400d06038044417883d0300b14404180c0350041058100c01d0342c2d0200c6622441d50403000700d04011001c0b0502c000c1010000060a589000e1243c07010550000fa21f010000041c4202108030009001030600700d000d04d20910b051030b400b049070300c40354500d42c01441102c14038610b111a424902e07511002c41d10a42c0c24000c00072000317a54143c00120764408205180382c07030f04401a00c0c1002141d10020514000e80c0100845590750f0203480c07500c00c0103010f10368019544010b013803040d04d60700c0100c0d0303000b0b402c02c00f0341c1c1c0050350800d808081d10200070343c019403241c031001c1c407410704041c80c0d6001100c607521003030040010b11000f08200d514803855840640022052951070341d00401d4189003410780c01e500b02c807056042d6030500c0303a040d050400500616042d2010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 865568875 1250 865567625 865567627
    0x201140610230f071520090102030c011a09070224090c04050412120908040308220b09011e08040201210f09020a0f0b0304120309051f05090703080906 66
    0xb0038070042031444030400c41040c44035000072401002c9188402900c03401c0e001d1011480705a002000040070b072802501c1c1c503d11382491b000100c1c03541c010b42c005401e120906204607420460954500c40c00c4421030449412900a407120224152030080002a404a4148041e2050907041d0040c0b071640c940580c290105203036160005010110108820804500014030074007290810781000ba00d100d000703035011000503044800c05e850501c10350042c0c50310558002d403031501d13062a41c3c40d4490700b9004101640d100c624480c2508041e4900b440101001c5d00d55a120541e0b14004800050605440c0b0424000c8000b40d80d41c042d01002c2d001500158019028213203032011074645440c10801117443c814054646280802d404847c400f5540084049032095611140e103a44800400300900810310425000441c100001000150b01c911090800b080e40c0c00d01103540c190594400d404c101c11016021024906a4031000c000603c1d40901c507004060500640512403c54071204117901c242d02d8041e0003403030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 865570125 1250 865568875 865568897
    0x50c0d14070503120106020706050f07120c0203070602030901030b01090509041524031502030c040306090203030418051e0105060d1e060602030d0b010e0d150e01020a0e010201140610 80
    0x2403180100c41007580e104042c3c1e03030395901a855400a41c0b60a01a1100601c640030012805600840031600440c030702d1040030303052062903a9489411035604264100304140390341c03943c005031010800000681340d40d80255032541001c0000400303c456003c2d000d0304005d00581c3c10009610340c0c0e006d4a0300150401d901c84512059004107a0141c0820f05e02c0904000f1484078400c8404158030380081900c0c464a8005101c902c0380c55901d00b40d00040c0c60800d03880c04208020400140309038400110b0501c05029242483c2c1e4405802c07a4900160b0f80c80e141d1141c4900800440c500c6051f00f2000188500140341c1895040802280c941d0051204d07224440356910a0708031a40c000384082910060108002c1c00b0315521020000d4a030f40011601c99115401e0004a0072998044c20440707050304405002c0381c00c4cc800548441044480c0744100704d00f001e50344c0d03614072401340b020300040800703101603118010b4840014000a00316201017a4000d94005020144442a903030030449003005012407400322a684 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 865571375 1250 865570125 865570157
    0x4031e1223040f0f08010c02060c07031412060f0901080705281415090112020a0c17131d04060e070e040c0f0503010b0a090f0b120f010c050c0d 63
    0x5141e852103541038100c0460005011284814100d0540c1c0c0a1360540e035066a0314014207003602c12030030720800560850400501101305002c090b0624078001c0c40c000c000300c401006e440405a00806001040884240030403005041c4190b03400b1001900b90b403c013003150300d0902d0351612288140034180c0b149541b40b181158210080c03080980080310449840c181c90b6640502e0320000c64110300540c084ca881c00d8403400100314140681c2e02e44041038503550180701116607444002d41c400d1200c0c0c2e05000310030340034101165116032441d170320707203014203145544040800021100e111940e0040800400d01e84102103d40503140c640c98100342d002c0004904130401000d020b080c000e140d01b00400c901000410007081c000485001011070743e19525500078140c0f030f9401c3c94280c4404098140c1c2240902d1420011003015620020031010448000280640d0400024594014801c03860407075030300890f82d00b110b0840030f124103030481c2d0702d038140769281603034402c02c1c83d03101c1501c441544184003000c581d6801c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 865572625 1250 865571375 865571417
    0x307082a030c1e0705120403034803020f010207030203161a1914040f14010b04110d05010f06090b0f07080706020711010207080a060f020c070b04031e12 67
    0x101c42098540314103140e0b07080f44070010b600501c1c000c0d1114841c0d400c030f10f0200980a0216010340c0c0c0c00d566507400d035805480704001140c600040d2000c1d48508001003000d41c3d042c071001a0702000039640e81f540559124213000b4902000314075190000d034030412040780001d400000301e9120180201c8099201545401c104081c45c03040f000792040ca09242003000030940307065440100007d2032800030402140480340d040b42183d012a00181050000d02600d00459850700c000c0c05046810b50000c60750280c038002140c00e9071820102c2c2d130783d0311001003028198151f44d4006e040c05004810701d000c0d415458013000a0241c40c045c45092801800014000a151401000c0310000e0750000e66041e078a0300e4a24000009510144c004d80c3e5901d045003200ca0a1742c4041010740032608500c008009090881d29124010a10743c009410200d0717003041070741841501400030400804021501540380c520b5030a107440c0800307604103150015403480c404000016404800645441d03054901003a000300d07460b820180c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 865573875 1250 865572625 865572637
    0xf0b03030c150112030804060b0307080d0c1a09070b0a05070209010b040302031b09190608060109090b16050a03020706020d050f010807090e032d0f0307082a030c 71
    0x5020004500c6400348000a91005401d04a09081c0b41680c2c0d4146040803054030b444000c0c0098078000c003103008925a6000f4100e00c00000781559041c03a41c5130403403843e00201101c0140401e030b0104d02e802c1881035a10258620300c20303082c61400341c0e103440701c041510342c2054001cbc40380e074010224010352881d00c00d0f000c5c0c44809a01500042c02d035611503030010420380080c44100d00c01d1040304406c00c400c2420990002d03040402400e180050384031654640c03002808500061801d565030f10307001410030810171500d4020155658001900b00039802c0a440c590b10042c5001c4035400c8641c00d00c03c0d100e41c000f040b2021b0303c1c845e240058031803816141000c0a445040480b502c00b80c2088240500b085003901140d0484c1c9500d0100d48810f50b80d01c400304192803800c03085051941007485401d070b51026150000d48071904401004103401c8141d0640801c80d04010b075040c40c1c0c3e11012041201d0b00d034010030101c1e0800e004180100304048030b850301d84140d41018140284045000c4042440807404605940d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 865575125 1250 865573875 865573879
    0x20d050f07080303040c0501050c150c0f030a0b12070e190b121c0c0305090d0303060e13260324030312040b070c08072405041101090b03190f0b 63
    0x89400c2c2d0b2410026980c1c0c00c00d513000e403041060340d1000a91513004800b200d44181e54140034241e06424580c41a20503000100b0a00e1260030070071107480ba4850311001144290b4800300d00040042c02d0009125003101079440c4070b0f8440c3d04c555000e10811400c040015484000c1c0500c20803001c01104115000e0300d190b0101e65000507030440c8081c12504040b5034030610700c40300c00000c012078803148000c60740303442903032000340101d44108184042402c00741a15401e0305e0080c1030108c0c000784d481c400401c00c0c02c4c0880d00311641001c440c080c1420806041a60041d002c0621900c0c0110480c40c0c4079480300b0f21000c0d0074030140e000f0401d4801c120351103120f0b0bc203d501c00001c0603241c4880c01a0b600500800c004c6400304c03004400ca00000314940d0149140da00010f030400001030416000e90f68100460821030028018a501031420550f00c610f98020144124030580c03040000d580c0441c005441c4030840e81260309104018000c012512003240000341401100c8540420881c0892412030010601191003076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 865576375 1250 865575125 865575133
    0xb0f18040c0509100806010e0d0f0507030c180207081611190f08240916170d0c0803150604030b01150206070905010f210c030c0215040f020d050f 64
    0x20781000c0e000700142501c0401074840403495520944100c0d462002101c680303000c51aa800700039024104011034a0299100300802941611a0b85a1900e425050360046802c00200034007070040c1805a404140300c6030415005505040300c60351003860740d0240e00b015507140041045080f0501206115071054100c2c0039159001340c010746042c1803140e200b1030007544c0720704030400c0002804080c000317801d42c9121032000326100e074155005c82c1114901c40141c5680c585208800d1a680c4101c09200140300400301d1005507820700c000e07001240c1c14840e07000300040911014000c04808580180d08584c0c0c88105188102c01e140075490000c0d900f03020b142c00180540460000114118071900c8030003001200742e07001c40d80075a403156002c443c0f030800f038000c140c00038031040e5008040c5402040c9140b50030306007141d60714150030b407413080d802180c0304d00b2a44d60000f600d640701d00b081160103105030340301e1241c4540c11410a00d03254903411460881008024020b501c1c203103202d01440070501403103942c0c00c0700500b51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 865577625 1250 865576375 865576391
    0x1d04150915050901050d12120524030607080127020708070203070b0c121303080a020114100807030b09030c1b010e01030903080a270305130f0b0f1804 66
    0x11900600340c510440c00340c15941031001c94140f030b0403d0214120741c4000c105803c411555520500c0315034184084c00148a040304803556100090b009080c400c555407940740e10100144004000900e50340008140250401024020369541c1301d00e40b58103543c0b8807100c0c585200002c0c1101080d560441e840d00e5806031010a16804001d000070051000b580200c00f1600f8298985110b0040ca110f000315000d0740c1e61224640382c60707084003140907240c1d04410204203140035540392036112181d0301c4142d100c40180d660b4000000a64481c045103500b00103140084c1507111309001101d955a0b5a9020203130251054100188090300c04108440d00c01041074180c03038690061030840b40c42040400c104038046160f140034100d42d9440303403150f0342e60b16070150b80c0e85103542c9408158000404034885400c4504182400c070340c5014584e600791500081c0b00340d071030300c0c1e861003801c8604400c04940e800403440646128030030030822031458251102100c0358041c6d07594a0f098800726a032028444960790360890700f01050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 865578875 1250 865577625 865577639
    0xb04030308090609070513051003140a06140717060604090204081615270905070e03100b090c03130606030c03030f0305060319230c0a151d0415 63
    0x12190250380e80b070040314070689500080e00d4803080280250354000166500c2480034110302e80080740c0200304540440c6400fa00d9441d22140046146c00000d13295000020031801c0200c244200344416000b00058030450802e240000c0902c4048016828016826008505690340700c0c0102d0f401426407040440d900c1f961001c4042e100c0040200c0c4102803001d84000041c1043c0f100030702540c1010655a004070004912002c0d030200d411080b541c0e0001069000204400b01907220310703400303450346440d0715645d90000300c100b501d8501440c8400e054103090041286c0580c6510f01555041340f58007079544e4030b03565190064500c1c8090300d80040c1c20182450400024407005800502c00d0301d000c0d0b80ca8002d2220310210a03400c0d030342c040d82c40c982c00d40c2c03250700704200080c4074503100e10390503119545001c0380020f241342d504030b0000d515900c11a281c00510107200c02d8640103d008004040c0915080c4e41004035603005030a68030042c15044e402520807082c8001c5554950000c00401640844a8002d1791a506 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 865580125 1250 865578875 865578887
    0xc180603030f0206040c05040f180605011403150a020307020a080a0c020f06071101031814011b020a08090411070b044b0f02090103080909100b0a03150b040303 70
    0x1000381c000c0361a034000414214804261248516000440505560b192806210041c4502c1c413441c81c0380750760b0304020b41400740000902904140900c1c400b0800d541807440340503d80d0848018103100b684060101d11038050396010a6601000705000103803240d54850059080180741c0b04000c00d1200c001600f81c60703580d0040252000c0c0345c025104240455a000107101883c41001c2c4058000e0301b01d00d07e8480c0a6110383c00c080400c060f201c0b02000c48070701039901d07440c00341c4000d464078500d65105d001c5401c2c8003001401d2031007951000d10007040f10800c580c4580c0c14910511603003500031a15030025410010808080b16844c60707000d14001900d1419040903030714104040342e80c04d1080103e00b41c0440702c920000c00703e8140b54400815a100c21080b0700040b10000b02400101c42d102c0c0c482250001691314a000e1038001d501a0104030f5445039028200400b1800c01080101e180d40004014000d000e4800142c990b10300c41c5080000b0007050780b0500d046c04014a50046a031440001004800c1543c065 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 865581375 1250 865580125 865580129
    0x6270506030702060901060e01031e02010315080a0b0601030908030103031407140f061005182e0303030e031e0904060806160306090c051222060b1807020709090c1806 73
    0x880200900707030300d0700121235466000b07200142500d140000d640c0303400480400311895007881414000ba0300c082c0408005400007050744490501d81119100000340018008001e038094400d2800b006503181c29a01c0071482e00040c00090104001407810354412280c0d03408841c1d81941200081e0b0f900491942010b0b0b5801c0681180c008600813000410054203024035604c051300c10042000301c601b00880041d4481f00707001422240d14802d810300702c500010794036421031420580071650303882135815807e000d4191074141d050105c041c0d20401c0a01c0741d00100c000b44040046800d101a5560741140001801520075604030340e841c0e002d42c20501c101140180304030040564a42c50034030180e60b40c1d6640d442190060030b0b0100205404001944c159005e00550690205800d401c00d01c050041c0038004213200903072a0112201943c65101c80500c0c603100c3c0798941821004401407010746801a0000e440c1d0b012481034884e01d039211150b10017084001380081010b4032803a0440c0505800c0000c68202818082c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 865582625 1250 865581375 865581391
    0xe0a050103170d02041a37030209130603030837020904140a05090d0507051002130308070b0f010b03100e060a03051c090611120708090d030801030c0501020102040627050603070206 79
    0x80b080b181704004091165010010061004407610103060740150040d6006d1b80d41cad982c0c000158a61096400342520583c00612b020355210641032034400c415007020a80007070f5003501d0884449842c241801e603100c01014942d80b040d809611a2119004600580012402954601129000c10150b5801ca03804580f090034600219044008140001d03100d0781f08005c4044c002da04189010a03601400d0b030001d1841c2044403040c0300d0300740d6598079404c2440d040394404a4503c008141840051012000c0305805003419003400c0785075080c080c4d10020319003003902c580c3c8481a4444000341c2956500c2c04003500a5410405031400382028154018410000e0403001001c60044032011543c18441d07049000b05038451342c0107140e0060206000d01d00e50300208012100070204010a41c8561140e000c8044100d110b40c845a07025411840c080311051100e4001038116031040c44200031450b8840f680c8942a10400301803070400f0f100c110415903280d519002140c1043c3d000081c0811203500182e410300c58550b03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 865583875 1250 865582625 865582657
    0x90206210621031902150406020d1109030307060c0905060d0b1c020d080309030d02040b07060b09071d0604080a05250303350108070e0a050103170d02041a 68
    0x110140c4403031164a04004410b501c10f1180c00380c030942c203482030386078010540119074000a030000c05031b0070701608803421100981c0109002d52807214a01480e1076000080354001e0800b0348243c00f0036a81c0c0a40c28016105c903031078580c0c20340b4450080c200800544805008655144a00003000c0040d1003a0f5105601036413111680480100050700d00ca003149238014550410a00d0644034000c0580010300550124001040040f5180d901c1e41300902c01440d24a9000362218000d04040e4129a4071294880c0a110074504000c16198000e41c41c198510105065800111006020a14501503500400114414560040207110303000910481c1b581000341c0d0210b603052890460002d0f060759100060115041681003102d94116220b66040c040004218001c0d20b40540c1c101001e014082e405400c054010000c24441e0102c8241607541c8000700c00414080b0f54596034400c171581010a2009101c081d011400d45441d80194040310010581603246944400b500070612106034403201904e440d95071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 865585125 1250 865583875 865583899
    0x60513050d0206030c0a1103070b011d01150309030e0402030c1c060302011d040e010c0f03110909130507090c050301050a0e060f12011107050a030e03030c030d0902062106 75
    0x241601da98104903901405150942d116000348484035000100402c0901200520600100c00c04001404055000e00f03044a02c5525003070040301c545240300d85880c21168600010311040f080030858100c02005031500290140b0745080c04c0395840480e100141c0d005000105025a081041001c0c280050211401303c54010a248151049030030a21009004c0b4258003004034480290a0300010300700e01c05080420044200d02c529401c59520907038110114801c501c0c41d070300703071503062043c0c0b2441000203d9103890442d10170b0001c0c0507080028191410502c0c1d100c2e24004115003403040400401c00c00c1c1c410b014060602c4400f40c856042405075a00403580c600e0300080580c0714110440c05440007600704803ca058088c01e210135980f0984085034590340351000484051100c02c001c1441c280a40041d0460711410b00d0010540e0007041d503294401c0c0e0007404940c1c0310040c048101c0d04145c1c0103510000c0c6010f01403000c910b8034010f608a059880400300701c60f003c1e1105012000d44203843c11101c0454810b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 865586375 1250 865585125 865585129
    0x8040614040e01050904060b12010903030515090c030c041e03050c01141c020c0d08060307060e0907081510050a0206090d090e1e1905011d150f060406051305 69
    0x7008912504164a20780700040100f42084240075030003a00440000c2030b0307051071501285d025100724201078248c2e955211b030881856414410340d5082a070010309486004030190000d0101d05001c0c103c40382551000000c105042108000c960081200107180d102507060381c040c1d60306000c140d20003900c481c000c00c220a841584518541c0c86680e00c49031b599401d01201001013141e80350f001c1c40b50801c1da41d007080780781d811503000c00c8082c641692035600c1c1c0c40da51400d03005050601c086030303200d1410f0140030052107101c3c1c1c0e0b401038503517400002c9260080f0250303144900c3c3c1d4402e4602c440055081a04040340c9003040d64000e00400e200b41d015003c171201500d45840660381d510381854040002002d0020500020004e8000c4540118003600001d0b0504a044c5101c0c1901c0d101392003c140c880c0802e68241c1001c0131a0080e07900501c03544040b41d0f50004110400b100710400204800118541d40304107400640d6448240c0480e00000340c00c032520b07203448201c003900b2a4000044404900748011000a0038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 865587625 1250 865586375 865586377
    0x61b0309030d021609051603021b1f0b12031b16031104050907080d0c060e011a0a080304061205090a0f0c060212070c0e0402011b050a0c08030c1506030a020d08040614 73
    0x2e2002150808403504001f8822030080d004502d55a05203a07001400442940302000300300b802c50303400c141542845c07200c20720780c01c129800d0100c000e0243d4813844004c0048071020081e50500140f0392102c240b041c03001c00205083c00c10000c007004110004000100038032540c4060700139921000d1b01e0412030380d1540240315075600c000340704622290740300700e402c3c4042c14464100d14040341d1090501181024040c0304090070742d620070840310140036125840500030b2419060403030082c04030401440c40d00e403c00d800204103031400d00540c40c0725070f110b0000c144c0306003040100600e482d820400d0b61181c8091841c040d54041c025114070401032003103400e489a11500b060486090560005840e100d09140003503840d0a014014016410f00006042c0703400c501d501d0108c80d002d55403098015008800092038000ba5550160704140190b60090001c65810340b80003c40c8503118160581402c0b103540c480c0f001a10380003107001d000750002c14031590401082010301c0a007082d1000c64550203002a4061305502003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 865588875 1250 865587625 865587631
    0xa03020706230c0a05070507121106070b0718210507060314060904060605060c0d090603020a0e040b04021c020d0e0c0a03032d052106061b0309030d02160905 69
    0x100b100398070042a55001c5120041510001c0c81c108507061a569031921814640164003081405983e018408200080f0820300850b94204a030141c0c245402d948555444000040c0b0113424418540c502900d070750030b00c00b4100000c04100441c04160409100d644c00c46185c0c040e0100d5040c46840c0004c20028002d000f001420f9404c2380c08800b5503612803041010000c4068402c1d82c1b1a90307070b0f0750003248075107a10700100241040f110050442c82560b1400a01c00501a440041098414091401010340c00340341180d201c2c1d070465010074a0301503200014001e1240c031504540950f850031a603c1d0703c072517035005060030b240d907803100300300300940c3c4150192603000e08445c0a905c454901c0342171000a005e14000714103840000640b00981c0000e104921886880381d4016000c00c50204030381d031820301003490090980400906410340e608012020032a14083c411003002406405100d4001d50f810070419907241c2d51000382250320003c070304840603480da0354400c41c1c448003070961180400c0102e118065540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 865590125 1250 865588875 865588931
    0x40903031a04360611072108041b1806050301050c1908100308040f08060709081209060715050f010b0306060d110909010f170115150903080a03020706 66
    0x160480c040d075810803035206000f00b0302c41d8001c4810712510108849114207440303146040c2400703584102e641000c825040c0801c0d00c0c0b8005015012a174030045900412264006a200c081540c0c4459000c2c2d011113000291340200040844140c10340046100a82202d0b044980c290001c01c030b40d03100e4041c2c1d100340d07102e102c0da4001c2c0c480c3c481e81030810982c864062264400c403540c005840340b5450b1340c4e640e85694425030043c0c0841c0702c3c000c03041c05503c0c0c00384001900300c2c5030380c03e000b0f07901440c0110aa48410300c980a440062401040c0c43c0d01c140c80e080c00b00e400d42d03580b1001c0f540ea44c5840300c600100401044c1c03440001460b000c2c001092080300142141d00134070000301401e040180c4102408c0c003030309100310641a5010107111400700e981fa41c66010340038010b6210b00182c0320703062400c1c0c800c08001c072402011b8141e051540b15401949000c0106082d21003000c1c00d6500f0a000c0305055541c0201139100500054000822000c5158540c0c05055218406d150505c841c0301500920311465403150034440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 865591375 1250 865590125 865590161
    0x501050906090c13080307020f0405101a0c0f071d04030c080912011e270b060103020f040305060a05010b1809072f0c04050c030c0a0e040903031a04 65
    0x2542442d0045507160f00c200c2c04481189841c9007040e0a200300302059000b0a442e0b807010581000f103203440417000c002a00151410441803420318990300010404d441004d201420b040d8007a666150074200311049071414130704903103480703030f0214085964170300a104d20300c03840605c40c00d420600154140c0700c0f80615010740d07581c0e079001103d0f01c6480490b0300007280a41d01a10007225018041030a0003a1040044007003407400202401c0040081030742c01940d01048003c1041c1c50130450041c00e05000b090058018455005603a22407006030005d2154001210401102042c00410000300054042c42107103d14001e03c45660b842201c4092030242e103a1002c1c603a54240d41ea14110305000103002d030b0001e840d1070175034018a00111718a0071084500304c031481d50380c0e005548016182e4100480c80c14090150750400807860568a1403049000260a1780508900080c5020080744628417104034075800600800001c05c40e8130703000d030090807491410f201c000703d00105120f1514040c031800003400a510303510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 865592625 1250 865591375 865591381
    0xf0f03040b0f0a02071805040b070801180b04111b0d0e0f06070c0302040608070302151614030d050a0f0e0d050a20030d0204060813050a12020114101401020105010509 73
    0x34440b42e0064045401140300d0601c0006034816807062142c100115010005280d04090a0604031110028401802d000f071030401041000c03007041d22803111002290001414281060010f005804410382e80507201c103000c1000030042c2a941500c01503842c2101c121009118685000e540805505400560140c0c100483d00100e0030b104004000f264824036000540d951a64001400c440494110000070360100300b041c004c504020914034030a42c1c07411491030800309000181d42c038803c0c2000009202c0818000e90344c030f0840c002c0040d20340f40609942c1c180200d10b01180c070b580c01031030501b400c0042c01d400e01e1807100350038801152101840b441e80d69901c1c904005510291000d0600101440ba252200c041a0a001d0003c0c03001e4000c00040386c0c07000d030b65185000d20080030884094001075859200c07441c141c0004000090031300029074054225180300241c0c1205a00401103034448070700c805490800c00c6865525801d6890641d40d0301508d40722002416401242250024000e49400000d10808 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 865593875 1250 865592625 865592647
    0x8060109140607201f0f0c0b06040b010207030b04030806010815100809070911030105010e19050433180c080c07020a03080d09150e03030f09010213080f0f03040b 71
    0xa0302010203000700c24841001d03518804514481d1441510405d0f00e03c9507042c100e070f01584400c00c07846003401440c10001403006074940642280c03000c0e0001e442070340d580851100a900a0090000841d0004000c0d14145000c2c1406054084d08803140c80c002003103100080c0e81000400c2d0240784420000e48092030580c3c0c0a041602d820002074800100f510030b03000e000486060500445a0078402e085005890354545400580181040d540d581d00c10a008034440800708031415410040303410072030303012484443d003440340c004030508403031061100c010462000c1a0034500e190790700c4c100c40c00302c159407412648140b01e95084814a084140c002881c150201d061032005001130070b030050000707000100b8113a8036030b10029241d1260b040515000d80380d801020522940e4803000710a40381d099403d0044159552140ea00ca10000b41691840300090011804104095042e070b180e00100380c150f400219111480e00343e0760100300c21054003602c2680d03021160900e003c4203440488070301400c814100108450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 865595125 1250 865593875 865593893
    0x1080a03120e2a01090810180209091e03090a0303030b030c0306010303080906060f0a090f06090c0908250312230301230108220507030308060109140607 67
    0x2031480e4940d034640c400b10980781c005008600f1200c2e00341071075454102e06880c032007071080c040b2040700c0d0600121400070044040c000ca180919003180040020303a618040c22620310b15454540301a400501d03800421002600000d40390746000e6000880c000d081c03074058112071307591007020903464000c2d030000804c100207802500074040c440390044c15542110319144c00b00707142820990003640050340c000244240010705001c4a60800010f54800d0000600d940100d5642c0720b040c8101d2040c1941c1d58100190550b4691184002e401200700a1010b01c10031240202981c1e01400b4a41481c041d61813656903818011800102c250120604070003414950344030700030301e003549a01302801e0141a40103002c1c108001c501161001c460b031400280c0b254180880c0d084405141d03411829000c40f41040040305a8120035030651020003868486181103482c0103a484107082140c00501d14841e0754000710070582c000107540e100705006e9840ca214a036036112510050781082021a8020004200c0302c0d010030f00e018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 865596375 1250 865595125 865595147
    0x5010f090e03090d030302040f08070308040303082a0a020c0d050c0904021305071e050a08060411120c0d051e0411010c140a060e0d0e0d0507031707060f0501080a03 72
    0xa42603e0805500d4000f0540c613800d81801100000d40c00a41402044282e00c80d680181c03000364010648181182c0d01c140d000d109501001d400e0020860000704c08103202c03041c50420f001149620a03100d0780710502781e400b68001d08500005400307580146030140c1824080400c0e40c41d008401041800417110030311070144405081070303030171580049150703803603010301d00071030740a00c0180e40e86002250101501c010001d4a2440e050100b09040041012441c0d001c9070311038104004a42c0095000004521b00342c3c1e03880741b4102c10701049d17060b0040180301c490740000781c610854141014852503540903581d400c3c242200502c0300a040c04400403c01240311021600090f15041c100581100c1880e25907050b00c1c282e05207020320a0740294403071010013401d40128100320ba60400284490907220001a00081c00001030300e0265030300c906e45000b805001c0104c0002160040b9030a00b85283e080448070540d07006000550350141491500d010043d00352113554101ca84010181800c088c041e0340444505402c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 865597625 1250 865596375 865596401
    0xd050c04050a02070219031e02010f03050c040f14030c060c0a0609030e1503071d100813060c0206090d0207060914030a06020c0c121b060a03060e0a09021305010f09 72
    0x1d005440041c2c441240c00100a5550101040b0031803941c80c00854101800061092300300103000d00a0050f43c200e0040360250250341004180c640e6010500340351402168440e9140402c90100050f00c0d580c0d240d60414000320940c10380e201c01800405006952266070320141d12640580440000b0440c00d503c070001c0d50313200b464448400c04880d00094150206011101503c2070000180520240c115003000b100c42040a102d107e2201c1000004410351814240d40d000c1c8922400082c0d01003603030003900507103a42d00100c10003108440c480001e603240d404171110380310b40c800e9034400f1080500008450080340d0050341c80b01c0d000b0341040100c00d0740e0398049807410303054840c4080980000c3ca49001030458020401300030701b5003540c1c034005c12070b41c01c07000f0301683c07850f030000c07030b058040c0110b61042940b9185090b140c540d0340d40d100d240120020314440d032005140d9898041403102d0b14050341c01a03031607a4000c6500600324440118840e085510070310800c000074030030340c90410001403d41c2020003100c41c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 865598875 1250 865597625 865597627
    0x19031e080f13090c090e060109210305090409031707020703051027051614031c1e02070e070513090b03010204091a030f1f021803031902010b0d050c04050a02 69
    0x500c01c0b206090b101c4d20100030300405c0e05035200344140142c0d108002ea00170024a403034810b1500d08090b00e03034102622415038078054031081084007407601810480c0c1200401070020401a15103007030080c0008947d800500354441d608000c18496031000420105490308640034150220454040c08010000103000480308004c50021a40001c03c825062200d14080d1014119540f2a400c1c1403d22115076085401410800d0507000a0340c0ca000500c14508202c41070200350341890304c10240c6a41e02e08100c2030100038811013000c0e161940c0400e4a900b00d40c006d100c00d20742c6827200709040c0c1c0c2d2406022001d2042c540145010880081c1942000e070f209140680014036080d10340b50420300742d40f02d000706074100d510300308088262800c00b0405001400d03080006883e02034410941e01003030080300c0380264005030b00820351400000c0b098021418244009017182d9442c0011010200340c103172800550800355180488840160a118032a0f1412588c0b01014040c0b0510020807c030003428007034003c401c03042c0c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 865600125 1250 865598875 865598879
    0x30215100312020f010b01030e1009030513090c080c030124110706020f120c0a0803100504020406030509160503100e0102122406070b060d0204090219031e080f13 71
    0xe03201041440c0d80409502612041c04180c4c0e84078207440000204c2c82c100751800b20034012800000c0b5800700e1301107a840d00404c5241e0981001c0f2000c0c0102940108201c000c84000100d0000036408070000400e20346510b17a0310f60b1012142e84140c0024400d801030b8400490118803c0c0b0702903200407070903424500f4151581c05850450700c0c070f0180c85411680150348004c0c010094001e0070860b1022965100744840c1c0340c83c0701403101c0354440311b04210050050ba004404111100300001200c000f8080140086403035650b1180014003401d0f041e10002814002c0580c007a44564000c159141034440c007400900b240540c03001d441c0e006101004401940313560921508007051403406809014000300b840260226400580c46d02c5042c82594010f4441c030070411403c070000d280f08201e03a6000c40100c4044400c120380740003180280840101c001c1d4052008000100d640115030003290035030b03010301141c07605000e00f003050000d100145000609903503070a0004c2000241050b00600c4403809281035901c81903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 865601375 1250 865600125 865600133
    0x20405060712021213061808070501140c0604031709010506010f050901051b0c12011e020c241b0f0d02070c0e09101b1e0c140705030c030a0302151003 66
    0xd0408007030a0040220084101b190a03403049058400b00d000d19001c00c0380d1450721240640d95003040c4955814000045007600364001544240c1c0c41510408003601e01382d107001d2400900390305807204104921114403012650002c0140318440c41098180c58000b25030b00d103500169000d800080341c00c0c0c108101041400300d020a424040d00750440d54100808444000800300031040c44094040d1140e60303d02004041132320a45112070103164060100180ea400021004c6810210000e442c20a083d845044080a13220410241c2d07205090740355101b01000010440c00f0541d00c501c1c580380c1121074080c48006030b0310b54194024003045124181c415405a525802012054000c4401c100590005c091488a6441303600640540d01c40d0424840d885c19030030000500380d50301e00b4003184a41c9107841c03090390046c0d000d8458070b641c09400070460521401d070708880a6980b0054015503001e40560144102c3c94100007420026803a491340103041c05580e40700204003040030051600020207071045002000ca = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 865602625 1250 865601375 865601377
    0xa02040b0c01020a031415010c0606240906020c011713020909010c081b2d0403051c0203160602070c1d06090c161e050717010b040204050607120212 65
    0xc500d00701c000b503250001003001030200c07840c6803c41e16880c0112000c0044041c0080710740c0c04c0000c000d08180c4c5d444881c5003803042c000c0c045034201f0382c03110b0440d09000c41035045004114014400c56901d240d403260311828126241c4103e084800e000c1101c00588000222043e514198414142c0b0044d544400365500010000c0000b6131b00b0701c02c01e954440300c0550140d8070601150340040d41d00d5451a10100c56080300b0320600c5841c042c0d030310040040700c00702074003521032003414a02c05021030b000e900d0350740f242080c580303500b003d442e001c02e0741640c0514040c0450010007076681102e1000c00c2c0e40c50801706500c0c0d02c4080e50100d403084804010140e8045148500c1100d0300503102106029003119280450501c1200300002d00303180c000e02c00038064402c203200c4a412502200d07900036050032191031016800c44a05c0c1081c0303801403880c0501140803031134008811003d00d00c41895002440081003030000c0c0422882a402196080b80c4100f000c1c3d0b02103100990003100c091103030720441b0b0b120301d441c046907841 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 865603875 1250 865602625 865602637
    0x613090305040f0905010f05010309050a050607020c13060e06010f0311030f182a0f0d03230403050c1c0209090f070501021209100909051005090c07050c090a02040b 72
    0x30078000b140c240300800018030003c01030b00c840d500c1040709504100c1c2d603248004007072090340e0400d078451150b00c0c10403405000310341c4d450341d019080b16020305026101944400c11a204180519201000c0320383c001001c0c000d00d02103880d204c680400b2a243c1720011912a505200c0000a1540701c1003056402000bc03801140705899a08030901107090146800c0404141c107581c00c00103600801a00c980186448509a10f400d2090440700400e540c44010070400d1258030411070b400f003440801c05062641103c01c5030300d408006420540071300010700111220380154003000d84150b000078400540c41c20101b145401c400400d0380256002609640015803802d0221070110741e03a040b280c100926402c040221402810090024120201c00740160042078060301c0e0400d4428081610910720850140502001410010100380414905844a020701c64054443d0740c3c001e0441400052040082d40c0681c0e0301140d200e009490303040c0202d82004244140500340101803a4208030010b889030000000b131031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 865605125 1250 865603875 865603877
    0x212130b220902040302210d200111030403080106020703110607080c16030203010e12030a09060605120c03060708071d0316031103060703060f0308071718030f071d06130903 76
    0x44d8072411481880500541c4408148105000c3c0400c60707051080031030f030001642d6891600d841020b0329018210102008070203a00460352034400702d180c02c0100300e4011807150b40030751200b0310507986e200400c1303139101080e102c041e1502c81038000408682c5050780c010080907004500c6141000c8400004a042c0b15202040502d8000e50020810840c2002c0c0940d04501c1c0c000c00240c81d004e03401428152a600c0003d11038000c803991a60b0340002c02046500c80005008007901101078403501100311580d400700a90301f54070a104031030000d26500c0c41065054810380d8103075181b5005003400813142a42e0b4242d071210983c10300803481d1b0140b00031444074814009502444d110074440c200c03e0107150512102404902c2014142242403040c00a2030360b5440841b644103400c1039441a0701e0038032801d04400740407440fa120900140c6040603107803018411001c101d08405446840d0b074400740540d5616003520801c564104400e49500d00400004c1004fe480320700a0a10035503402194440400c5a6a01e50210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 865606375 1250 865605125 865605127
    0x303160306170f07060503011206020c010e060f0417160303181202030a0306050303090307051002010906290405060f010e0109080a1b08190b040f020307060801060212130b220902 78
    0x303900f0301c07040101000030400c07400c10601d07550400e030481d410312815020240c030894001401000c100c03001d5000c034031824442402e462032410450303010b00c1c1e0b0031820b49050340e51840340d001c8484824011011946483c102100b207d881094070b80d01a409040f0089a20005145040e03825021038159246800d9000d070716030145940300340b00354000d000c81d421034100741e010340c2c0180508240c545000400301c05645088401d03440d0403042000880c058402504002c00150806802c803241042003120000180d1049100c102032980050a00dc00c0b5841140c0890b0b206903030100350006035000360304d00c0d84500740616150420030b07220f085035854400242c42c1103130b4502c09140030705100c8a03e100d20348080c145110180c5903c1d0b180350380041d005800c500c00681003480d0200810200312300468206507a0b9400b03000d442440c0d03521000501100004d100ba08003502503116582d00000242c0126850007000019510140d0f0800032038108641084c02040460f00d62580d07940059201461580001c05800c1c0001d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 865607625 1250 865606375 865606393
    0x1e041a1807090b090a021b100b0108150112020d060e0c04031101080405030a05030601110d02060105040c26130818011715090402010e060406021b060c030316030617 72
    0x103034074010580e0301c2002c1103841c2c4a0a8100da0391041c143ca84c21600d0000056102c11840c1d000d51802d007008546d000c0e03d417113111602d8031002c08030f800c1029449400d80300c1c0201c603a200030b0141c1d02c2c03200031400c40780054907401d5205501da42c00e90281c0041d5a0321000000c0c07064036078a01003401a81580d801120301404101002040754082c05007034103120a19180c106400c1c5a602c00340d580c042d1148003000d110f40400040c04030303403240054000c1d003c090011031300c2c1550b4500e0081d44410080c0109405507040001c41180d090003103404074401d4600502203a9200303180014480c8450010f041c28480906441240000c00c4c0c906d0702814a840500450441d00400f0000140209488016080d4054100000c200300b0701c152141080c081c02040d03840c044259114401202c803c0310300c18101d5030118000c6404160568001006000c0c44c040440b04000c00d03040404020041c0124130340640f55a00810015900e03004004440849808a040100e141500c603042d84141502200001c0c42d035500c00002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 865608875 1250 865607625 865607671
    0x70b010e01120206070312181505010503030c0d140409110a020705030a0b04140f06090f0f030708030105010c11060403080a1b03081b07050601090b10020102031e041a 73
    0x1409005220180b8030506016071036000c50b080d40114200a4184001c26103c0c1448142c1600028540380c00031075451200a62458941d107118807a841904a203807811001007641e007000000c41c2c1c55091000024440286403000032200003143d00090709254406010004940003503014078005041c0c034002142c0c44210020009240c280c2c80e07445980700707512112228009ca02000c0f60b0782d0b00640c02449141010070114a030701c1c0707400d0740712013403180c1c1d40b003074000f0091900c80220b0410726208402e02500c0c082e0340b20201040d42ca00500710081c0296200300010041503000d803640010b55803107000b100c10103083e000001032403038204d640241c54103400007515511495000308682c1141301c1c04040c001032290591001024800d00900c0310040d1f1100980b480055500310043d01c5031300b0340c0312f812a0000e40c0c645190390702030309008030510f00070318091044040c15030040c026030748281c0001460916203800040b10211041d00600180e48545102c0f0801100c000380d4800f80b8441c3c0c0441008886807084902 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 865610125 1250 865608875 865608899
    0xd0f0f020a0906120209012019030207080d0903150b0a091103060906010507050a08162a05090705030a2c1509010e060c07020f10180e070516080f070b01 67
    0xc001302495104000741c401503038014642e08955a030444040c0306040341e041ca514601280001d02c0c04801009600e5441010b5001540701c0607290110151072113422040c4040c4c517803401d140401869008a0400003c02d001aa84180a507070401080c1105040c0d85110001c00c07561500d8440b01c920400008000d01c50520a11440d000507003864018580070342901c40b00d844009004004002d540c2c00100200a88181d4540c5880f080c2c22000030684400d0342d144c0404d80320745a031001c106141320544001030601d008004e240c0704a1594440c6423445c0d4417a0301d00c900500c5103800d5020b10100c0803903074400e44811140001c030704080b41c0000300f982208c04104400032200040c440c0e0b40503810300161000d408008290309400401754000c2d83d8641c000c51002406c43c2600d5200d80c0d400200d5024134101c0c50342c1c084c1d45281d400d4a50103a80342a5506d552224171800001c8400001180041103441101916517011001c1e0342e005103500e5042003802411180c10398841c140a031004507040d40140f004c10000d00d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 865611375 1250 865610125 865610147
    0x6030e0c0109031e050304050a0b1c020705060f10171f0b0a03170c0d0207140406060e010e040609020c07170604030c02090a09050a03050315030d02030d0f0f020a0906 73
    0x42020105240b40d9904c619019080e25040f0b0700d1600349003daa42000000c0080d81e0241800030710380307a00982c44520415098000d070b0040035090f80710140c001405541d81c4200c074103d54010b0042c00050303450040d05100513074007411090082d280c00000084044c2848503c08008940ea00a0300c1c2d071200404a940445501d2440c0c0c0e0300407468001d4445060741ca09a040d42140d600c000d000c19000c0001c2c404040c24050000284040d003d0081075503201980440c41d43e0a8480001c01440111510310600040f1110781c0204004540031b032258500c198080c20951240820081c00401c005440d02d0010050b070300300742042442075118010030300912a94400d409802c5541c8001051940b401e618010000c00c18a800607005408540200d00344c2c3c55130343c003d004110740000c00c03224152114500240036500403a0040b1030701c4000c41c1041c2082c90081003c50024586500442c140b842c9250004001c0408500c003802c2d00359111085020341006001900e40d9103903c0c0c8950315120701c2d02d0000345c2130700004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 865612625 1250 865611375 865611377
    0x70b060f01080a0c0903150c02060703020909061302070c0e15010809030906071403030c0d11070b0703050a14010e0a1b080c0d02090d0b090f0114130f0c06030e0c01 72
    0x400c880540e0341c0c04031000d54070107405800070072225440c41c41a2411500d941010740700081205030b42a02d2422a00701210003c11035003101e40d80e9a561030100e00320b001e240d0f412680a1845804036404c0e2500c1c03006081188000f5500614148c4c3ca0f40c0d454140403036a07442054208000300c2003101c150702011044503146002e00701100301e4645003042e00d4680c81018822807090070042460014050800400840412894100c940da810311f0b82e0790203402c0d00000c020709805424100d102942c0083d0701c01b503448440c0d010040d8000754440d07020507009460000c2c611040c0707039035503554a980c089081d1400350082044441208881c10059083c8040c0d5400f504050120802000c042800c183d000c80100d901001d5003002640364230005600402a125000c446540074540e56045424044144031243c0a40409411103501d565076011280c20b0310780740803690f8080010078000440d03100c0c221140040706131040380444168800e40c1e1321035098601c00d402500000341d0307400010036003031010031084400206c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 865613875 1250 865612625 865612639
    0x1c11030d02010b2404080d18060e24090a120203010b030601050d030c050709020c10140603030414040b03150f07030b220f11090301050c0906040519050d08070b06 71
    0xc0c04012070308075414604104e1909007408a80d1101156500507140a042e00c1720a80301a40308010005140c3c0183c80b0743c0780260380c810180000c015010310140d00340d18401521180c405a00c0c050b411140c4000308040c440042007c100e02000c95135030118072406003090410402440c1550b006150859900c0107030240264040390041c00666600707a880032840d0760520f82138020076142c1c60b00c1402c00101d6401214424000b06821585200106417480003260045082155104600c0c19030214070b0195032060309504108024000c0d11400000006131400240010800001640100340b80c940541c00030070014030350310144040085155600c60700186c0a103420300184400c03100040691106072003250001c04048000f078a254019000064042c44984080004034006a04103141c1e50000c50058030a510313103400141400c10100540c0c010310380203000d9900b010300740405d106c901050540300c1007408081c400b001500ea81c0c3e19483d411802c1c8200c2c201501e0719050f2030042810301001c0c080c80d100f060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 865615125 1250 865613875 865613891
    0xd060617090a0b04030507020d0c08061b0f1e13030213150608190c090f1d011e0f12020a060509030c060306010c080706021216050405010e1c11030d0201 67
    0x140020104007060f000702109040361950f140c142d81074843c0a1009401c0038051410134140042620440e080758481800e035051a912482c14000c161005030741e4441c24581404508031000090300a400107801c1b00b21100c0600c041800c80c62800c3d0081c020340601c89045490900840c101000340c3c0e24111445241804551080a4601059402d40c01072108200d10300000032000d4035503881c101e01244905ca01080041605500204032855601030040c00400034240000e8141c400032013440c0c1d082d030341042c2c03140716420f00042d130118202c0c160259204203a4094081501d15011440e07100802221984030220a42403061298500325a072101003404800e00150f00c9548001c030308180840c41c11104196a0b913500380041c0d80b442d00d40c4102921080011070000c08004065006081200e550a10307000160740315007042106c0e000694949000441c18030041000e03502035a0f0350500048000d000f804001c407860491160300f802d01038117031052031b400c004199442c00d05020003030240302644000c1c01308527 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 865616375 1250 865615125 865615141
    0x30611031501140a080406090b160f0e011b0203011b030903090603020f0307030522081b1f050c091302070303060506130323030a020d0318020117060d080d060617 71
    0x200030b00b1044024805c00c0320000d01008216030000301c039164044030304622810144002c9100e1100081010007042d0f035a840425514006c64803403406900c160344000f911807a2440a4121802e01501260190b484194850440c60030760010020f100450760002003200650500070a142e07141e07440311040c588100100400380d0200c00481e82e11070400c0c200072406072506070034548403800e450803080c0640d481c12040f2080007000303801031076049078a50405002e030503044070710f030b13210a042204924042c0d4a00c0350761351221050b030420395000c511b081145003400d07000800702c3c489405100300c041419900060315001c0641610440e0003030842561440e0420a80c014158001e488500010b029514a01540e0f07100d01807440c8a42d208089010940e40c59400078003000c0d58481c1440207013808213041000950860022200320540160165281901c0200780c410003400b890b005060641c21001c2c450440d0b0100d0401300081c520030300007040004581f0701c4d0002c000e100009128080884421589c180b107040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 865617625 1250 865616375 865616377
    0x10e0729071e210c440702040908030a1406030303070302070c210c0e070f030c18030b1e090a1202071a1b24070903061103150114 57
    0x164410008524025116042c000d108007262085404001030040d156500141c0c060908040c9602c900d103154401c8226580c1c0c4c0502484424108503802d103150324503170f6030260007002032541d003411030003603840d28500b80c0100b41900c034030180076554040c0000a02c01480c50398410f2603900c5004000c4141103003024030019407a0f10028045408058011541c507091007061a80ca03001480440d15040b4480b116400d20f07402003581680c10b40305520400c40010300c0c0080101c00070b200311140c3e0703500303015582d1904040d0f0040400c40402400c005c450541450070661200d0031502a40c0988810032452602d0690100c1c0c1e60142c0840280840c0541300740300070b4900c000f070712240a55000e1205c603002e101c0124201d01d84603842d171108031034010542c80390590b1031640d0010000c07030160700420180706030305d8070300982d5035010f41d46131aa10b00e0000c4042142c00e40b281c091190414498506181c0c80c542d2510340c0d009413080403410781103004001050204118551841ca550101c1c01c2c01d2000181d05205196002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 865618875 1250 865617625 865617653
    0x306060c030301060201050f2a0d060b040e0103061415210109030201050405060603190206180603150f0f0105070b0a180501020310061403070302030702070f080312010f050d1103010e072907 83
    0xc9e02007501c4100c46501c0d0424400707081c4003100503485030b1b03035000c0f2501c44220a210541d415442d00c1894071600c05000302d403d200d0030300140b00310007034448142482141100c03480929a1103a20500c130126a16080c058409160f029600104450502d414001c0c01d100c80548100d03c2948501d07100c8d0a0803010f489019001c94040b58041d842d00783d10816400480c80e4908001e5100700000200b160803000040010064581034400c4480502003030140f1000c140c00d00d9189012420900ca910005403c480559a2000441c1400b0603440c0c00b1080506d0b50600341201101c0a0350080100105217400c410a800244440e1030205503006103064074000c540b0018213001b041540000000d0001b82c002c2000b00c0c020034241c2d400c1d95007150303960100c5883c2d821403110912851410b6000103075021441e0490710540d00c00030045c12200c2a281d8030003140d003a0794108a03815540b180c054444202c410701c041801002c0f0401c100181c0c03402c202913a03260b003102c2039021910b000d0a10010740450072619581070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 865620125 1250 865618875 865618951
    0x405131502030118090c031b080d0e0d020f2d04151d0702151006111f0f091a09060714090d051c1e0c05120306060c030301060201050f 59
    0x5520351700760030000080c200540001c0c0202d0000d240d41000020841f114104a591210aa46130352021140403181c101e01518a135610484c64031000025240007286207046840003020900e280c040001508149400948071400c0c030241b44241200c107003800e0085030101c8026180c0780040f2400c2a0b10791000000d03100180492880401c00140c005008200707402d2640350040002c5510f2030011521144000700b401280005103044401921304007001a02109080c0303100c0c43c1c0314441e400b000d0314000601e0715408200301035445c0c182c51404034282070f80e1107004c240c4a2141a0803807030050303c0d00e4a003c00240c4114204180d00c0d415a110010740d406071840441c040700c0170800001075040141c076040c02031083e00b68000014090341d40e040d8101100b03204151010300403007184800300e1000e40745415050005401600903240d0111a00c21900065a100c0380090a4a0a00b050140400d180d03410036044040940e65400030b02c84000c4110341101d92000340da0115007210540305511528504943c2c0c403800c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 865621375 1250 865620125 865620131
    0x40f09110318030d09080310170706051c0504050a030201050f07050403021003060312030510060513170a2a141f0e181006022e0b0405131502030118 65
    0x4102c000c01d1048801c900b01c0b2280500c610510b500700400341e0383c4141c0e4021402d0341030b4080001e480d180514030f030101c0c4c04003001410100b413030040191050b6004038038001c41c48052014406281d815032280a021303d0081d0300501c0129180c0c940a421240c015105414a600d054208042a6844821101500d905a61642c0c9000c2c0405007540070b0185900001c03c80c042681e051841140d00da4481c1b4030402c50080781c0702c12640c0e51a42510540f0581c0396001024000b540c1c240300101000f141c1d0401c041c2d148048420800c41d40d10b81d2540c4594507851010101012051403030f0001500e40c4c85000340a02c2c400c90481c0c0801741e000140c2500c0030648055034485402249140640507100c0b0321008180074051380e405012280d40e80901344c0046520410f172004e96400802e2991000403c1110b03551150b00c00030f228580d01503004c1c80805407180300084192582c0034280f0342c0d1160702035980a00c2030300700098001f0000d8500140200700100b80d0280c0144180010021100594006182021149000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 865622625 1250 865621375 865621411
    0x8070e0402030114370903033c24060c120302160f051e1f0b091b07060c0509040f0b060301050f0d060603111f0c1202010212010902040f091103 63
    0xa00281704400400705800d480c0c05000014141c042d007116003041c05446d030884031142c81e1151130328841c0a20312401ca4250000903840752448160b482180100700071003e10304441220b40c100d03041074245400c443c002400381c42d404820031101e1010300800c0c8840c2d0805508081400206034581c4140d45c1001c0d095450090010080c0310007403210286c0e104101c10300b04031072410350540658426031000188502002e84108000ea04110b00c5003007000a4014040c1400740c589a0100c00d07a404440c881c035076110801c10164000403400d101d5101c1c0519076488280c2c0300c0364000100805c440144544410702810030b19503064079900c1808480c1075410031561110300030700f90004a4203240c03514200410151520b540407044c003141c0b100070740d5942c030100c8006a00310030380e0a107810010107000c110000b04070804140ea0004280403607812058006100043c284460000c2d00503020100381d02441d001c3c0d60001d42031010507020800540544505001403100304444014800288002402100c1a90a09504c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 865623875 1250 865622625 865622701
    0x615091401050702040c12060b1309092312070c05101716050d1d010507140d02030714180909011a24070b010f0e0105011d030708070e0402030114 64
    0x7055812400c84023005881c1d11041000e49980c80f1554107510002d800c10b001941102070301514001d1503008003045d201061018044080860a20b940c1c4454003c0840840790400c480d8040c2510324020702c04140c06501e44024001d2101041003000100300741e084440d40b20240311048203410131a01c1c49104500001d0b0a000c5603140134140c0210042070414001b401c82c80720006104150f80f4070300740200000e0319011015201c91000200260140d078041c02440580d040e00d50265502c40842c2c244440a1421401da6207040c2e40710a043c0d9902d80e4001508039801d0a000c03c00c1c5a01c026213800800c10580b20310071408103000080a16403259a01400c200542200c0940c540c643c0d6169154168403286680391040760301000b40515804443d94050004220100040f1541200d00603103c021258140120410349862002c0005070144190100000d29450822840c0e000706170f066140e01c0705050034810182942c60000750002005c2e140c20034001c101520701c1018103c81498820403039400a0014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 865625125 1250 865623875 865623887
    0x140d031d031603081312170a0504092a1103070f14011b0201050703021201140111060c0c010b241605072309040305030c1602040615091401050702040c 66
    0x454014242c41141c0c000042103c10400b0304000c00308520a86842030b01d8141c2540c00707801103100580358001c1441c815103043e50240040410348100c0c0307481d0745065142c2c41c008050702c0000d0030540c4890900082c140b60180d03680d807a810744015514000407141003180420f56240a40c00002e8074900e0700c0002e401c02c000101c040000b406100d0402441400b841c0b5005480340c2030500c0300b00d00954284400681d40521038800c40c3c20070341d000007070409584d00f440c1c0780b50244070448400794180304081d81c4062070080200802840303184840d250036034500b1000001400c0d61030181d442401a00b004003e140b01c2c0d0311820080790b00301003003c0301644a030b41c2c4203601c2c49486190320b805001c5000d013890104080715811801c8001520f031140c1106008000b0041c0300004404030745c05400a1010320100f21985124030007000d4080c0320350b03903290070030b9a56000101168040e030300849a2200500010032002c2d00010345400030402c03c0690f8029502600011382140f1645070024812584d590100c1c000d540584 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 865626375 1250 865625125 865625143
    0x30e061803120301170309090103060b0f15130b0418050c1303050703120503190203090705130203180a0c030305030c0d0c0806031c020a08130b0a0801140d031d03 71
    0x5049400360342c0b060050a0669100b03000f0b0862038411200034941070640042150490741001c0c0c154041030786035841c1c0000420504c40300907808480541042582d035a101c04000c8540c0240244607603a200101d4584d030000d8940d400030300903080c103200401008520345503e0112002401001c54590f40d0300980d010b5512512000d8040f0504d8044080300740280041d161082d2441125000d03c04641404240c03918001111022610324842c10031144290060b0095900a14114103ca45c0640c6840c00104d0b4015004200a860303540803003003041c102c4c20b050102002e80c0050300501203440c02030703d803900005110700003e07044c04400004980c03c204020100d412010180c0020000e107480858000c1100c0e600b910b44500c6803040071301101d1030028100600401c990075400501c0114086d51361801e40d44c11450241d004103c14000014004074150001c2000841a680d2580c01c0d40c14801000c040d0350002d00414001c0c000f00e101130001a4211204128655034030a48010880d0b0020000703281c42c41e81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 865627625 1250 865626375 865626379
    0x31504060b0a1401080a091101030b130c030e0c0f101b081611120a110a0f06050c0f03130b18060c0a03030e0f0a0212010204151d0d030e0618 62
    0x391400608500b02c503a0251060703e003680e801205880c1c0c07030800c0701999440c00001c0e00c81a20b0442900c0c041d0b000c1ea210406914001d002c0c3e162001240c000303041107c40921040d8007081d21044401403d010500044c80f10b1101268070000d01c55180d00802d081980a440440074060441944c0412214056078004040c1e4010221a9280440380500703000d402c01180480340b03250b201d5641802480c0c8200811042c1460500034040b11741d640e1600c5c13000700807402ea001d40200c0a04008180f80c181c80b140c1802520361a00c07929907400b01c2c1588245864030340c05032050076800c144007018600c036807000e00c5012030f5009074090b511024018900080081c4540c180c5510110000340c05078205408680c200030180070740c800b0441c00c000e9400356622200c0552240300a40c10581001e001803038503007034240c185021380e00014205521400705040400c50076a501c030205800c0c10760a070700c521300c0344800455071101383d4007524402681e540181c900c03c0070003203547c4101c0000c01d140e403040308416900e01b411000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 865628875 1250 865627625 865627639
    0x3020d12060f060f081b0906090409051009120314070507051509240408030f040f050106120b0702030a020601031104021606020c070e09030a0807110a05060a061202031504060b 77
    0x30700e0318003600b000c40f40c01d01302e000320380d003000010041e8066000c00400301451070b6101d49000340748001c1040b20703400352142ca54480e9a40141c0340100f0000c11a808481c5890000012541d03001e04040700b40c840c0c40101c410426041107090400365610200c050740042150070304585500d000c3c40c01900b460b4080ca034000c14550090304100b0111400207191842ca002c526070118800360141c234680d001c440c1241d01401050313041002ca8030040c6086100c3e90b000b402a898800046e40310b5540e17609540d150743c4054041c0c0c02441b2100c041c0320484401e55001a403a000035490500d6a0501a4490005200c054070b650710308004800541c4864044880044c0c0e041c030080344068842c83c05200941200e284c40c202c5105040001c9003060b41d440103280203100b00e40c025401e0a015803400c9039401001009042000911280c0c0a00300008100a640d114800d0011307013400d1412034403c50403a2025401040524400c048540258801040080c000304c180e13290340d0340305d13030307950410401406000740d1080d0007900c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 865630125 1250 865628875 865628879
    0x9030b07030506130207020d1b08160e070e0102060412050c010c020f0f070609360b101b030302071406090d0206100608060f0a23091303020d12060f 65
    0xe410b034030251140b0811034040310303414101c2c5071080c100d02680034002e41080031407126401042406011440b10402d660000f0034160f1035141080c1480440d00380342003545085101030242005491009920004a103040e0280844000c0000e5070f400b03020b04080c1460380409003042000e8030801c2141e00386141040240302c415062000256140e20901070064117020394010140c8441002c620281143e141d907682e04001410817400041780f141c080255802034194001c40da920f00c001120b504401c2074012030006105c90100103001d9000e9181001070100300750038603100202e0480307a10314045590913240041c0c0301c0c0d00e6131511044440d090380e80070340300d0300c11281080b142c1302001684903010715540d425030b061a116400c004414000b58011f980104102d10002a000d041031880c0142d001c2c0014942c01d84d00d591442040380c4040703814101800044032100e04000c0b403c10307a41103178120040c034052405456250710000c0d10b510005201100300065507801929400b0603801c02c1c0301525882400d0f41102d9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 865631375 1250 865630125 865630127
    0x2c090403270f1706071209021e1c050601060e0109030b0c03190b0a03150f0c11160312050a140c1c080601090618030b040606171204051009030b07 64
    0x100e42071241e254042c50442000c9a207484040d03000707004400040c0108090345076001c09445960740705180030180740d60390f40c8050160360380d0380b02c0e56000c0c00b00e00b1100703060f00f80c2c0c0c40038043c80d20060b090075424407140292000004800041c024116145480c00014100c00700004a0b01205a9070001c1d00c0c10003503805024403428208000d600810170803a103245040e051034001e4050300c8084c0e1981d644203a1100040010a00d5800503d4001c01d402d14001a5030b01c8180450303080303809203141a000141404c100f41020001088003001281d4444085511189595a080700c002ca100312003e04002e004550785141c607000fa050400c00f00030754840f050b02e41d88200d200a5464280d40144414003601d004910700a9004582032406808181c0d03d01000a0800c1c00999510303801c0d01d40b9018520340310a002010880001c0c00ea07005500c14400450b600c1d2a1103501e4a065a444c581c440082d00211201203c088002e400c03102241c600f1b03a61164a441501400e0f6004171080e40701410f46800d0108000040e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 865632625 1250 865631375 865631447
    0x100b0418060c1e020601210b0901050403020708150a090807020306040308040b01050117060d051e0705090a0c2a0b0702010b1216092007030507032c090403 68
    0xb000e483e541d415a010400340160b0300008030b143d0501c0960045001803241c0480c07450040d5801071200b1a00c4c01c152810740e281d40c0ca480d001c0f1011402a59140280b0081560500000d0300505600e0010035080700c02d10780000c00503502901d0102e21907a5221000d0400c11010b050390310482d0020107448e054a800e0502401800040710204c2d10f114200c00085525806098030116492180c000a10700d5078410003070000e80100c004083e10588219000c078074506031803001c0c403550450108003a186542c500024440c0c580c2d0050010846142040c19204403c0e60200351060480049582e1820000e040c0000e018200202c00d00a01228542c4040066850701500b05000303464042e56034001c59200071210030303151120b5150031880c80041e0481004508503541140c481c0c0c902d504c0792aa00c0c01110b0128a5943c1c0c00200200d0109402049240a06420454050042d84540211014101c0c84041a08288054000d19200d80c0840000c40d041c1031103511882e01e010000d01b01e40885036042e040b50b001e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 865633875 1250 865632625 865632641
    0xf030f060e0a08070b09160b0406090b0a021218061b0f0606031b030f0601030605041e0807150f0e07050f120a1218030b010504051305100b041806 64
    0x140c244101c881c481c04000900c0c1c0c1d5007941245540e4201200f41d03031410f115a070301400c0440030388140d40c1581e48203580080002d00501c10505686d81d03591400c20050220301442d40300030410041480408240754011895000007a0f079a5811580c80d00c00d4014010203102030703c10765030401c0001c18100d01d40b140c1b40900ba1101c1f40034204903012403482c1c000c41984c5200490705250560401d000b0090103001c0700c4038021030360750300a007034440109980000c14907243e400da005858050700c507001e00c020311594804641100c100140003542c2000d4a40301c20030b00f0310038105c0c000c044a04944540814240b00c2e44600368440701c00d00b040c40b410f5501002c0c165960094041c040c880c024844c0a07480d0327440d04031743d611500403100c4007412040303074140c403800c50310f040c032820706001e01c00c6d12070004400c84d009410080181d07124080a10042d414081030004407440140520561034600200501192002a40002e200034003200410303648249000304002d41040300e00c140007906140d1000c410040c15803c1119 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 865635125 1250 865633875 865633883
    0xa06090219050c01060305030c061e010b19050405030118060b030a0b04020d030509090c0c010c0e0102030d05270307050d0e180411090702150a0e07060c0c0f030f 71
    0x4101915014244100c0c0300741a55281003100c1c494000503003901030405040b01c0400302c1d00020310140d60b51035007429a807003111510066040394041210051f401d1130010f03403c0c0303551130740d2404035070420340843c1c5d00b0702c0b602c642c0a56a6080008440f0020f10034002c440290101400030b0108000810600b1000c117102d1a044810340e0424651265909000030240781d49a0045001d8038591907075000c0c4080f02941140070f0b420030200f04203084c1643c8030320310040c1c0222891100c0304e98034444146d03003d003152164200c00e801c11001140302e0700725030fa0000c01c1e0362249081c980b0009407900c0d60040c10003444001500a00c0d1514600d950840b100750220151410134007502c1070361130103992003d00b04c4000c7c0340c5420050344085114100c814890094244541c45485041040c5d90207084900044201100325069001079111165001c043d004075075045410100010040c040034000591003a103890190040c0ca00700251409440c007807040440a480050503c81040c020f003d4030781c02c141c82d040350801130a0b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 865636375 1250 865635125 865635131
    0x604030609150c18170313030c030506220308060a03150e06010504050403051605160905220b071d06030406050f010807050603070c02010e0a140f0a080a08130308040e0a 74
    0x14010307a010f01001000420441413142c110750400114102011121800034268403040c0b1907049020000102400518012603082c40d031907245d4074009282c01d0004000030000780c040082c861224100e10f880303841d0190726003042c5d034466480c0d0003c6840c908450740090418908004101003c8216034000c2c2c1c0603101c000d040d03814030703a240c0c014003054440548000780010800c0005000c550a28001c0101c42072042c0103440c0040448040802820195000200340c140e0303aa052080118101d64020300c0c00b801c2c00c85003607800b0481c0c1c40f0030307084102c000d08200c180711031520140c401007120300a01052680c0280410340340d0400e03003044002000d0485000d1b1444000b680041407500001079a40708880000304000e14560b501c04086440ca0b800c524200d0500101c4042c0e0700c603e035544541003015203464400d010381c0881910401c840410003008130782c000d4400b0b41051205001c00300703803580318540007042c42e079454251005100c2026083c0c0e2020b400c0c0000400c3c0801e0b502c911540b414041c03101c046040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 865637625 1250 865636375 865636391
    0x3080a12050f041716030e120610170f1e15010b0a12060b19141815070f0b06090f27031e1315050f0702060403060915 52
    0x58811503005442e0380c03280000510000700040c0c4031355800a070120380d10a42034100407031a00500d0021942c40300460110345e0810b2140003908144135845003421a01000340010b00f810b0203155a1015180500c00040b03120140d10729041d20300300300541030030f0740314030842c2c40314405440c09109080c84021498180e00911481c0f400160440f032509042e603542a90700f914080c0716490079180c01851414280c00a034036030b400040e4110a90b4040c00030010103441e4546c0b441d48121004000f403464050b6094145014088500c40c2c0d051481034101105003611920140c01c040c0003405528042d085005041e110100041d500f0850b980640d280a01c60035151800192101050401032080891b1205522101c1003802d0000b5102c0c5140540116414400c0c0e030300d401d808151202565032440c407101c001c0c3e40d0000340d4411000c1082d42e24801000440c0030040b800c40c01041c020100c1c45508100c0c28600300c086180070030740d0340308d20441e0010b41e84002c00704214500c03450043d0840c030b40c6103110300c0c7c00c0749440c5030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 865638875 1250 865637625 865637657
    0xb0607080702041406011d0a030c15030b0a1a0c01090c080f010501060c02060703180803031f0b12010b1309020d060608060117061207030816120908120d021303080a 72
    0xc4600904051f110b401481412602000d003405c0c448131071513400104440000045040c04000314081d005d8515920307480c0710605000307000d4429002103180526941d0104100192504603620750744036074020910354450205010a0141901e0540600358508442c03000901c0d210000d00d4400042140000340f01c2a03a84001c107803003142860340d020750000702c200413110000f84038900c10300e000500348030700c07090850f180c2201d58655001140d03601450014500d119445410004803c00206906e40503185030080c1ca60002d00000f10600c1440300180000c07070240e0b507507901c44503200c025010401d000c41d1502010b2010030b0203400a03118900114460a01141442d48204004040c00a012004800c3c90f186c0070288004250b122038000020b004204d40803000840500040000380c8000c0f010130741140329400d0403200b88a54404020501c14900c00030401c002000c140040a034a244030019100d004420800e40680f02c0d5854064924910b080c010003042014000752003205080c1c1c1c0d07210315000e04200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 865640125 1250 865638875 865638911
    0x9050a0603060b030105090c070611040602011505060d051b0d050114120a0210020109050a0f0210091802070609060c02061f0b070206090102030918090607080f18010b060708070204 79
    0x1e241c203c080130001400503051410500350001158504685005016102c1c1412207014414103106150001002c000340e60703090143d20b4003007230300d02c0440e0a0386140000144007441200300c4455001d44420000b01121200d590f104d020110400115540b00350b02c0c210900280000d005448020140c076010380c80c0e5003042104c1135002400030008000c680c586400700b02030184640c4c144811076407180342820001d101800403440c02445121565440002e0303104000658400035900340800000d01410011066210701000d180000e210005070380c4c49041c14000d001c0e041041c1c000e4515420010a11302d5154005070031841501c0010007401e40040029000040364014400c19142c004140080c00c00b61625600821181c00305004681c5001410b801142c170403054000e64184910114003040f4002c4028010254000d8043c542085246041d103d0301900000113407030362158040c7e4091080f0580000d600c010034035000108010b80715400c6192201c5035034044c0e08101e000e6800c0c400e46489982c0c01c18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 865641375 1250 865640125 865640129
    0x70905060d060e2104050405060405090a030e01090b030103032f100b0d1205040e0702010501061e090f0b040f0b0421060f09030309030e09060a0501050c0c1009050a060306 75
    0x408a1400c0452074594102425030594911680d000d0719004590803030303401302d8840d0400c05102c042512689810100003c6a000a101c4c038099405c10041004207040030410521007985030074041c812000c0c4c41c00490340c68030950072414043e000080040240350f0003184d060220501035a00c181001c0300c00ca103000801c09540c0e41002261301c42c0e0306000e50b9403a40d4001c034000c030700060211454401366132205c0da1407207001c10b60319011580001d020b00160030048504bd0b8402c0040c0024001945810001402444048041c0b164007410b02c0108508500c5a46480c000304010301c0317120b43c000e49610300a403d541c007a1042c0b580e050b10320900020710702810030a0b141150741c4c1d8019021821000d4003544481c40442c13104075012660703400300410b132030014494000030501030b90300000c000c034103072402818070b2114540261050700502d04000c0c1c2c0c0c3d5540f41c4600196102840c0c40b94480e40456100c52420b0b0061088a43c02841010540e10240c1d0200c50038003114000c94207441460b03030303070b4506404552643c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 865642625 1250 865641375 865641379
    0x702090f0109201903150b070512040e010b1b060f06030d0314070302160b3c0403200a1b150c080711060d24080a020d11150a0207090506 60
    0x4d125012103140300071441c0c01107281c10304000c00d216030f0040c0d901ea000344040c0c01190780160701258200030b2001c10020510000040c078841ca1900d0b04002011150359414070032003014810015007140084101880e02100f60440e4040b1075850401c40d0703114540000403180203000b88501144041c40074403900600c41c00009088001c0c00300e80724100304401951002d600ca000021542c242e84c40040e580b800100e114074040d4208610b004d522030002d20313801c54101a10000300862009011000d00c8550429030230641c14208084000d06101c020840012510704000541c05503051910a000c1d03450100482d0201c0340c040102d4903921854201801703100901c0c4200002d42c1c032400340c80050032010003031100500551500644651140c0002c0710f0743e014005803820962260030300a00b001d004110840d4040c040503407800301908140e2010f54419403404040c2c0324923111701c000d905020f4154942d0400d41000340c000d440d050002c004a4440d50f1001c6045001482815000100a205841040d00410300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 865643875 1250 865642625 865642627
    0x61e0e120702040506011806031b09060f0309110307060903120314150a09020309010e0c010207050609190f0803070c0603050c1c0b13060504060504060f030213020702090f010920 78
    0x640c1c083c80000d120082010f81804034080e800c07141c0324107a8907440e00600e482e07a804145151100c41440708426040190703414001101e5040c04000e41111000304218503a14000511505c94181071040324071030004144c05025209000c203c950f801300c2240140c9020300c2400703034425400b0804500701c03041c010755424031518140c08a400380c10096159841c110005110040003034481030002c04a900a540364491070f1f5507011050340c0c110013445003100001003400500f58117460709000c034041e8810100c90302d11031441000b1064040360f45010440160881000710030300d05451b0000150740c1d0f804204141c907562611070001908501c00c5c003600d44102c0710098160305104001404140c0064862004100f26486555009180d201c0c2c5480020240900c031010518925003810300c404c450464000c103006a0400e202808540343c42401d10b81140d0707050791040442c0c0c04424110000340600c1400035440f5000a050003200e680c2d50500d90705803048090200040c100140c2004040c684280c044100550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 865645125 1250 865643875 865643887
    0x9040c050d05120d0516030905030a0f03060308070813080d090b03040203010b0306091606030b060306010f0c061103040b012705061909090b06060c0a0f02040207061e0e12 75
    0x81294100503034502c58012150f00c007001400300e002c242c02c003103802819503036a1000c010481c15071105038603071251681000c100b00300081c1c80c0c40c1d8480c03042c51540000d100c07404008100c03040c42948004001c541291145886180700d15044441c2d500503d0a0340b1141d8050f00d0109081c02d01080300b10b2916402d40304c0810052914600c0c0509400041c0b00366415540e440014040d03032005d100e52403180d007590010708542e40f03e03ca4034110703041043c0c01104c109440c152580e2000d440350822070350000401d0134080f034040c111680031a1407858814004204905050709900031644c15400b550085108200303004450b03882d0b060715188074404a08052158298801030f95100404c4c0d40010341008010b84a590b0f030b036440000c083c59524003035000686403a520f10400c018400143ca02903004001207441e549407140c0f034003115503210722500c0003070106540b0710820800c6503115030480300b41d1648007a00340584030040d04010a0001c0c003030001040076051611026600c0070100780f01c000c1110140d90141405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 865646375 1250 865645125 865645129
    0x2040b1201052505090d020607020d0819031d100f060807030b06040b0307030201090e07031b0e0a080105061c080906031009110901050415090302060c0d020c09040c05 73
    0x5001201150480851030352604403650070700546110740e0011200410418104454100d0320403814002420050f040c06009980e5498a10044425030102c0303106444203581d000003011a800e60302c00a0904000181201004170307074100c0800010055203040143c4000d04804041c00340c2c800c100070101c0c0c2c0021100c1d883c00e082c90350200b03465503014030700050640c1d01c50700c0d40da18020850b0401d903071700c3c0c1d4600104000c500c0c0901808400c06c5051307015150191540c0d0010700001c089026004050780c1903800201d21a00c02c3c0c2c0511020001191440308003521003c0140040c410070340002e000d6045260301180c88a41400348078080c19010b09072000a003d407036446c60215100410031100c0c10310030000d04a4595940c0041e501034420441d1290300d045c980700318407040b5070b80d010799031181c200c09002600c0941e801405440440364110034003440129041790495026045030030080d80000042480e041c140c0001411040303803081d03a001c4030040180303c4100110402d0031034000b8500704110300140500c8c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 865647482 1107 865646375 865646381
    0x1b0e04060503151b07120809010c020d0e040207020a030f08040e0709120f0f0b2401020f0705011116080c10030c020a0201110a060608030d051f030204 66
    0x3c4692240c8040122801001000780c04040c4543e040d103403014204170303800590300007401c105103001080040c0c442c490a4503103c465600c0c0c0350800301c03200e00000380580c0b481210345421861009500401c0007a40c04418200d800400a100020001740c40070355210105100e9100b054440d81460310785007a041c4000d103c60700708107407001700304120311030000301d42e5440c2d400402c580300c40354007030412003511030036810b00030800752000d4108000040042c2850390781e4003c10320341c102d151095800490351580e086100901e5138001034410081341d80100d188403112502a0240c9610500150702c40b0741d0402c09910080721900070b07200386c001600c0d009040703031310311410390501b0003c920041200942d01c507004e44009052005100101030a0b030381c10494600300c0da60045c4140001a1640c104c0d540301d801c02c0e1507449c01c0301d0038200400d912440c420040141c402d01214909100c92641d000c100227 = true := by decide +kernel

theorem cover : BRFrame.Cov 865467625 865647482 := by
  have h0 := BRFrame.cov_init 865467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 865467625 ≤ n) (h2 : n < 865647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
