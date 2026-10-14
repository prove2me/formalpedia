-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1385
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:42:39.886914+00:00
-- url     : https://prove2.me/submissions/ce887a2b-9362-4d23-92e9-f95c43dbabbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 248920863 ≤ n < 249100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 248922113 1250 248920863 248920921
    0xa0e07080a05030306191d0712020d02070b220201110a0210090602060108010504030813050111030c0a11010203010614130305060f040311120a180b130e0a14 69
    0x21500945030120400c1d0646054000206100c0e01d032070240b11450081d012420028200c030714100e055401c001014401e00c00d8483d4081c00511894400c580c0c1d5002d010752608215100d00e0000303407940094200440403030702190b280000c210804019860800c030290300b424401c41c0844180d00440b2051a6480740540a21550581900503581c218031051581c3c0103565480e041890403500a28100d0181d12030746181c0d24000510000c03a138014049a40001510115045000c81d0300c0c20500400c10190403210380000841800303200c900752002041e00c2c0703110356038420302050281070240c01c0344828810361707001c1440c1c0c2d100d503841035038010054103030072440c4880c07514400e607a5103484d030032b0140854040c03c1c0b81c60b41e40304000400d03404c104800100700c4178034001d20285000120268982c030902d400c0034140418500e01c0b410000041d01607002410010410039100d412001d814200901c070382c0a0092a14900400541c4031081c0740300341020000e185008401c583c0b5441c00c00c0c558582d840051000100d01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 248923363 1250 248922113 248922119
    0x504080414060d140907060f0e090402180408030a06080c0928020409060e091515120106080a05070506070c0b1b0d02100c09060206040602030c1210050112090305030a0e07 75
    0x44c0c41103090904a410440710301d85401c149003800c10410b60048020f0180ca034401500302c036800b0302c05017000c800664858001c0e0300c6900004008603280071220351070310303185c03000c010400031020059400380e00035000c01d20160b91500203803500c4056061002d5004052070700011b80c010304400282a44850314000d40c140c80a0500286090b0303402504440403035621800100300710340301c42e00c07a50f92000c0d49501800741e005c507a050b140a584c41c05050001840e42d9424800720702e40c0c0f0341011041c405003801c0200003140c0d49100043c0c49034a082c10a07100341c090001300103440d003850000c950030140e000c41c03220201414560110800d422610f900700800001c803010304c1c40740008000302840328825400420320a5403400c0504144c4840f002d40c241000081c3d94100422600042d0f0941c005a000c4805600c0e585c8804c150503490180c00321352108100000148101041e500344c211007a0b0310300ba69424403980907100343c0002c1e500c0c0f0040c0200024001c000090000005a00541200000c00c0540e410350356 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 248924613 1250 248923363 248923387
    0x141e040b0a0905030c0619030506010201021b07140909031903020409182609011b0203162907030e0d06020f130e07321605010f050408041406 62
    0x22032001c07507010950041c0144210b281c10054441c1d5514100d541c40c1c03a06e184016102004500081d64200b41902c500100307030241e0007901904c00390202912401414010b50f01441c0c4e581010b40314120004032000000c5102c0d0600c680d4080c41200044010352a010041c0b075038411090070040c0200c101035081c8004600e400e0780d801002c80d090444444166004514180114880c40b01034040406071040c4402040404402098828001007420710304018285403a9202d410b05414030000e43c140244e03003c0607a40e40403072860000f41e0308220b4201d0380500d811000142c003411510049240584184100740029216554586102602030b108d0300c42ca030020f0362440c099030001d10400050080100d400036400102304c4000e001080b0208035610315080641000d00702d81010f030403c9401c0d12a109240d03881c01c2e0a1040703440d00c100c00300625035680d049130f1108220301201c00b40c01c031525400c0004a1007103090501070140515040b0589603d080d1506080d03070800307408504070720340025092120011140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 248925863 1250 248924613 248924617
    0x402060304020d0f0c0b0307020c030c151b07080d1b2402120702071a121f03050304080c010306080c0a06180801020f07030e0a0303050d0207020a0b031302040c141e040b 74
    0x446e034014890b48a00304060081e04180e0769640c124001d601090000b0200d1781d460ba5141c0011008000c2c01c2d541c7c11014400b05102d200340c0e005800c1d2480350460000d500c0f0000500403a40a4066494180b0340f140e20082d42c25030b4402c014017521100b0704034401103420388081c0d42c1c0300c420651360303400500d08000240c6411032004101c5003040540c00219082005600348030b60480440d05071500e01e40340c41d071020881c2056034005800040c0e54000d148146d01d2242c1da81d043d100c05541c104040b251915501c280310380d600c400301c0260074006800d0a01c001030492000403079140716000204290021410301d881103800c1c151840c01c1c0907148140c0e40e4000380d8501c0a100621141c5414598030f0794608503801c001d0141c40d1000781c0300d80611000842000401e5000e01900d000071a00e07a005691030361103000043c410a42904003d2341c00d01b000081c09a01c10290042c0c0423014070959041c0641c008400007078402460040c0600180c0c001000440d0030459800e00844425481060b0a4202519001e442d0403a03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 248927113 1250 248925863 248925869
    0x6050319020d0b031501030b01090e03030c0901020a020303040f03170403031b03030605100e03120c0a11060d050a05041b18020306030a05120403030e0607150507090306181103060402060304020d0f0c 87
    0x10101701d00041c8148141c42c07408501401c9802018407010581000b055904c3c84010403801d4610f602080c8001c00c3ea209120b640c0115800030b0447e900d90b42c452064080e55a042c4c44200d6281c401c00002c198001218000c0c1d8080780d8042c0c48440e40d840322900c5840562425060440030540c0d202030100781592408502805140640c1da1100f41441d900c3c10301d0b02e02080c402c1c0850a00a06010740b04c41c0311000034140314103644c0304400318180055034022540ca0b010b02e0a054500504000030010f40c40d06075400340d80320383d010b210074003880181d480c50003506401c24041c14101104240d1200c124400da60003c580268024007101e500d1001070f00c40301c2c1001d0084000042c1480005000c1051590102c034010f5a00d000f20707440e03031602009988108500809655620b20540c0fa0b10000d02103a000d448208010350b0040002c0c0100011040704400061081c45c089038034000c084041c46850600140d01886154050089807031138540d41c081141e4100c20f00e0080780d22420084141001070f540035400001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 248928363 1250 248927113 248927143
    0x6031308040609030314030f18030403120f020d080705030606070507030f0503031e060a06031a130f060906031109090f0a03080601030c05090a03060b0402130810050106050319020d0b03 81
    0x843c505600c0e00500c900d440ca0301003402d50310140f051009507182c0703001d8640c000110f4101940c074066098031035030440c0110351018040307a01c0354980c074171410380048610b142c0c140b8603800d0360060203015006517007c0300182c0704800024002e0002600c2d81c240103000703140150040c030848001903684e56a80b11103400c3e08500312069000441407022000b83c0c1c49403000503403241c21307012605243c00e0703001c5501e44002d4441c400c20503850790740c042d5100d250030b40810050311000d4201110500c010700c525018103c240b150840d10342c54680009041611032040206581d0701045450107095580204048550003400c0701684d8055031105183d140410440e8085030381c400e8855440b0b519041c0700260843d0200c401c01030601c00c082200c0d42d40c640d80d482e90f0605496010a00180060f40640071900a02444803501c00f8907242c01000b0491690009007a558521403800901a907a03d0fa00c3c216154042a00e0020300180c50010414040106402810742c4941441d400180d542640001070301c3c004003d510205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 248929613 1250 248928363 248928377
    0x100f020403060b0603070f1b0f050a150b0d080c0715031a0a0506090d0c08030d15050d05030f0d09020406261b09100302060301030b0901050702010b0609060313080406 73
    0x2001850700402c0101c92045684501754640740c20054040c10007a00208104103a48010301d200e44c43d50301c1340340310303280d0021409000092245840c1c2e940712804041078681d03081c210303c0380d000c040c02030040384180a405002e03110b00c420705584100b099049040c1500c424050b4102c00300c0c20364265074039280c0707001a0355808a440c030b500c88054850302120210301c1e4043c03544e040c0c0501054858400700c1e85800802d462520000503141007810340384500760400c11003400001000d10400c3d1081d017241c00b844801c042c44001160b501c02c00c05c8600c2071140f00003450b54100740540001a000c140143c0f80c100700b555008540780310107074009404c60724241c20140350141015610300456002c025170000314050f0000400760701000e07424080c05541c005840034490005640000c1e19421101561401154081d0210380c895071246090361080e001240c8031601d96213007000181c001132050081c003c80c145c010f044c140c5008420300030300080354401040e61a14154001c1c554000800c00c90042000301034a5590725 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 248930863 1250 248929613 248929619
    0xd031404090222090615050c0c060406030e0c180f041b06170a06140409020102030c011505091f090b04020903100f140f1810061e06050a020705060c100f0204 69
    0x114035843c20f81240011038039002c414450400c080b03042c1e01038079840b030410b103441d80401a101458100f4080441e500a0700c04140003c40301c0e096000401c10704c284178140c603d29890301d000c1c029103050280300d101c0f20741c20031000310b00c0c0350b80c041c4080303600716024020503140f001014007542401003196002d18001101c0b20034000c005040701900c65003100c440c100a01c04c441c50300220015020344540b040303100f1941d8200d1401168020801c803504882044000d00c102122a80038840d4002c1c0e030b100e80c074001c400c503030002241f6410100c5019034407540c039011217400c2c41c01d1803182802402141e4900d50003035401c10100e0401e640400c281d0349000c01011010030119226510070040d141c0340c1840700c8d0090094000e00548131440301056600c650b4003c00a00f100010f401c040380303000021a200c80c3e0040c42c20001003201480228000400c45c14030100310b100301c2e603070201214603200b00f0041034016041028103020320700c1c218004108588000f0111118042d01181440c01c0700c0c0d648044451440d0700260130 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 248932113 1250 248930863 248930917
    0xa0c06120c17220b01090b1002120f07060b030a0b0403031a1f02160b0a03060e06030303040609020f130608010f0209090f040c1503020c0f0304050d0314040902 70
    0x225110384640c1c5801039191080c1100001d802401401e142401d500381c1820811402800c4a04840542c2000081c9105e5a4801c0541c000b4407403d290240614011a0000d00c014000600111046010b9a002d80b42a519103600840b6070800d5004807003094a510040003699000c1204148041c0200a2003089041c2880c0140854940f840c0d0790803a070000f4007050615a452905045c19610560010f43c0003201c246401ca003420480c4420002141031a40042482200c01d009040e48a07201e44003005007503110301070031561610480d503d650562003040010005000d58000001c0148040c048030480c2410341c000611100117030b02d26101c0c090f0384e040c041007101c50900510800c507080704401c40c1b0b054080004120f01c8000103051001a030f035600302040400c8a001d00c0d400081640305440912404000c0d0010042d502c10b101e000d4441c810558400d8096102004407400c480c0010400c401c05411640d00741e03510003503440031a10a00050000180c034155a0008115042000e00c080b1940701551000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 248933363 1250 248932113 248932121
    0x131406060f01020d0212130e130308070311180301090638010212030c04030f031d0a080d0e0409020603070c051504030512060622051302070807020f030a0c0612 70
    0x3240c1103501481c071034041660003043c0200c0c001705001c81590b882040c07101c44442520103078070030080e1008c2c8808000c9403015944c90710800c14400c0c2d945c0d80c0309881b0244110f00b9a03200300c1c00a100d1000405c03030702201c1c500b628550300001e00c02030000f01d000003190301d0300c03021680114880040c0c2000c0107000e21454000100d8541240341040c09140c0003800c0900003036640500886140074980000045020b2401c0c100c20303500116440b942041c0c100b01c0c0ba180041110203101138a511618404240001c1440e01c4142d0b41c1c10380e1550b800601c0860800380e41100c01d00c900b214540c2e082651094007001507101c0b86c005510a14950300c841424103584c1c07401e24648012075541e8244da2009800b4480003a50103c1146e59240717845000d0042d40e25400c0000d00e461107a0540c502e080807030700d0114050016004a1542103031003c030f40f031201410480390088240c2c0f0540100600c28441040741c5001031030500405100d59801404a4410707081e10f03078451070070a0040c0c01c5607010610041c1c61884030106402 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 248934613 1250 248933363 248933389
    0x30306041d101d150402190b0a0f0305070e0112050601141306020c0324180a0b090c150403170f03090606100c02012f07090911040b01090303030513140606 68
    0xd04c441400b82c08521109000900001c1c030491640300b182c640c5107070384c5000e10050032410085a6a61141d06070144c10fa80038800342102090038040050340c05e5014007600c0d000041c0603101c400f209030741c0000c01ca009050080c100ca040c40412450394101460744806818001050a401c0d40f6103420f011010380390021307040312140b0a601c400f5040900c1482da1640014440040f841d031a8203884440401c0007010368501d042045101b40741124060010b00c070022402101e208081e80d8446580c0d4040c080d0b96010901204103d150801040000031285820350140e80105141c02d401c0903c202042442c55200756104009580715034107101d00e61601002c14040280d070b6041c03106400190381d0018213591102005030a80514090540825503601010041048403640c180c8600f00c2e12001e00300018031a19605442074100d40401c0c1d4403604251207001c038540d0058603006d01d11417855a048003d02401003120800d02c007101e0b405d4000640030038006a0250410018050030300e00f200030300c800d050307040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 248935863 1250 248934613 248934671
    0xc051e011403060102120f070201090e010605070b060607050708240f0c0304110a08070f05031b0d030302070209010902040306050604061809050307020901061718030306041d10 77
    0x2160a404581e0445007001e00403019046950300e0740d60f80030040c1e0910310845581460ba03100029414060b5803400000d04a05200341ca0700d044542d1600908181d0072801d00800c00801c00030006480403031000132009074040c00091007540b81801c240d07a03007401c164840d84980101e07070058040a03256042c10f00c44d401c61584d2280e4650483c27808200300c48000e1b002500d802602d1000102240074050001030004d003090002d0004026540c0c0c40c48559a10b60941c0300b412510020542c000c00c184c41c0118420401420404502440300800d42c00c000c0071745c10724a000c50a1640c00c101150068444004440c001c15100900503180e91039030911905560000b8035243c821454605c1c1445204164450564146082d450008922116241c2740b4034510071500081e40c0300501d6400014070503800080d818210b90044202d905507141c10407142c2c2000f1a150b24024940c00c14800611a41403503808000c20030403103c04541130041c0040a241490020019520300544030600b070010703440034201c02d4282d15421 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 248937113 1250 248935863 248935909
    0x705061812040902030a0f0e03030a1d030304020f36070c12050d1805280507050f210d1b0209130602070206030901020309160608190f02070c05 63
    0x1024001e0700c9a030041064595000c0f000ca000341009620100400000c503508001d481070301c58071a83d50b60401c503007841880c0d080200e604040b220098691490381c2d0541d0055085413219420400701c004541d1500c2c0d0800d101201120400c1c1d030010001030182c82c035640f50044001c80ac1034468811310000d0a9009200e43d0b20f072a040003404031070040c0d41c161032600c3c005032200300c045003036009003071000b85c80d00805a402c640c60040c0b010101b882c0a00266100b40311880010101701140d1035407a00038060700302c2c0c100400400c06420140001008010000d00302d5000b80119500707001181143c1025100d2680454580007485030080b0094441c0240f007002d802020b0429800200010801448061000d1014802d081085402d070140c610b0b881d03000703105a4691400c84a9907000707400171901e9901078802c607150041d51002d01c005e50030942d6850742e82c20510b50703180d80401c22803614901113054000d6480b021401101c0c030510180900030b11030001c41c20003d180404001208940c580c10041407066 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 248938363 1250 248937113 248937133
    0x10503031902071d01090506010c021f120c0f11070f06030e0f030301081f1e0e0c03010c05070605090303060a030215090a030b010518160c05010b0607050618 69
    0x8000156001d102030700011044050800030300720b08092255028a480c0640600308038004121071100a040e26040e10080040303580342801125042100388000e5005480d940c0e90f9900300c0403143c0514506070980c02d00307841a1401c0000101110f07401054440000c0310041405801684140c14844a0303900c017006108045c01c0a1070035841c0e46680c800c400034940e0f0380180045510042c00110040e65404003900c1c0c0361340c1d59004054984940b00c100300b2013800c0140c0c2c2503001c0c4509120346482040d031311142c403d920040084c54001072066a6100000384941034515149036024080e494213003001d5543c0302d44903034941ca0b0140c1520005800402150414410002280c45512441c4116501180d00e5054200e2410a039095441007101035a0091500038010041c0041074070b034241204d000ba107819505000d58090f40e03195280680b41d06a003500088250403c1c14071617680101164003030300001580c055507200281c029404000211540e41100040040500c400c4e8840c10075410b0220103032100d004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 248939613 1250 248938363 248938369
    0x60506041802090a1d060f0105090903070804050d02040906111b06090a12120c0c030e0102060610030518060906070e0d05060c07110d151107030815010521100605030105 74
    0x5001001c81004035507491751700c1c1000c82030380344001507190880291038481c01c2c0b070543c00d80912001d00410b0b0240b4400f00102d80c460000000f103808464011320798505050400d010094072010b02d500603680592255143c0011541c1d40c400c0c0c8035410012440155188000f9070303094882c01140b9101c0b00176811120401081a101080c8440007541c0041030355a40210a40195a051101c0302002e020500d401da00510084c0c002c0411001d083c080d44070220001741ba0001240e41c2c0600301c6040749c00107820795178411404e00036003005070089040c0e54203a1640d81003002880c541101115000d02503802001440003043d0413060b506c203000001c0d2180008140b490300d40e1980c89002170020110320000144050520940715800c10045500070000c08036851030b8140b2307202000400d583c034561503251940f00c149a00c4044126a01c0725450b865092240c2e446030b070104c480840d002c0400d814044100605010203007811103648584412034207440842c01c080d001003032950b405401900030b000b01080140103540d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 248940863 1250 248939613 248939629
    0x100912060c14040e0907230f0105090415030b0606070507150c0c08060603060a0b0112090807020a030804030b0601020d0c080903070b030c0406021605010f0516020d060506041802 78
    0x54020002181d01403120301e08849840d609030030b00c102e494000c2404540018000c04440c01404040e0890710030b070ba211040c0340c3d07040c00b282c882038150321f090a0415580e0f081c4100080880c94050500c41c0c2400001d1001c58140c13111048281d1713400003450018020041880042900000255009801c081c190350b2569690026405031540f002c2206802c811040d204600302c890303056204000c5405181d840c10101e036100e00640380c040c0302e4000c010008808030441c1c8500e07440d080c0140e450045504030b00081c0070081040301d0041c3c600001c200301c00c0c00540c0781d0940490080d881b03101d0099131289181003003880704a014000f24110b422048403809220f5010244902094200d80c44031303070780c00c0300100092a14019a0007142d017100044200409000480050000c448d180d4095440d44030400094940040d0755004850200d14124034440589110703402800c03104205c2d41d2040d41151507034001401d10308540d801220480c5d1540c04111080c10a8051010b00c3c480714400c4242e102026030002e1150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 248942113 1250 248940863 248940899
    0xb09130c0207180204081002030a2405011803170a09231c02040504050f01060602070506040303080916080709060905060f04151a070b0705070c0b0d2304021009 70
    0x1e409403e4000d94500340d046070010100442100d440203281200100a500221120500e00c0c0c0340200302403103400070f100756031403024209007422461401c200041d00e021003415204d01c160440343d08080001411400350000180c240c1c5286925290781d003800600b0305020f40c1040f4240f032907100550781038420900502d00002800c40e21007003804456a050003516184001c040e40c014104070502062200100b00c4014a801050080c03014a1300c40405a03980d0140c0d219036904414100800c1001c24401c403003180d00b04010300d00b550b00303030900c0c03139210010050207401081107070700480340412040c0c07424401d0800a00300c41406201d203180407000940c51000320742056016a840da01d07800351a8400080d0000a06031a912002d01526800140e9810b508518800c40344103d8a0011510382c50003902074400159100c1c005109040c14100069030540000c41400b450b1600d4003da44503903841d1440082c601c02c0224104072140c070b018010010701d0310002e0780d008144812240140011418011803da06d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 248943363 1250 248942113 248942129
    0x180506010812190c050d2706020c06070201052703010c03060b07030c020f13050f0a05010b07081809040609031706062b050907090e01020a05030a1d070b09130c0207 72
    0xc0f480c600000303a030301106104008045e401048550169141c014005400400146940e6105000c1103003961458001e24054100540e2100700752522500d000401040c000380b06150007414004170807002028030b2003025a12070b0051198189000e03d090920a15a102546240078818145807a80d400464410780101808100f80d40740300c801591105200f00d0040c0c40302412428100149040020081070140c4504001401a00c0414400d81860180c181030394010401a80340c00c4455413089903ea0124205805090f4482e0404c19580c2e40c1c6900a0721490003101e000c20502c20616000f0810600b038035001c010f0740e00c81010301400742c0703400c3c040e00c2d008400002d898003449191841e0b00c060000109040c40c0b82c5040008010801c00003050034012500d11840c1440581665605c07e820b07030240209540008100340001102054903410041c1214106a0a0288807840766003003420080113401c5a200741d04006900347d02403c2484461030740216070001041101603101c0020744580291040182c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 248944613 1250 248943363 248943397
    0x607020304120327081e0601080d081902040e0a0f05040b06040e010b030a0812010b0a1d061c020a1103090303070b2d0f060f0f060c0a0501180506010812 67
    0x10704d190700300036148410034010000400d2030b50301c4145030340d81c00b1204520711a004544410080416001035180c4c107803a50380300905a5580240c50440e025203000f000d0104a410f010706400300d4000c0d501c0200b02811b0111f641001515003001c0300f10070340c0c010140103540189003804100201d458080070075008001110003240380041c0750345143c09041d40c1214980d250186440c0041085200c030300804d05d580a4a0524540c0c1ea0780e98079903c2c3c3d0f401422401d001141103030303140461049404459602d0310300c000308042d080c42c01c280d00261105038809256801c142c0d000400c06070305a0401c02243c4a561060000c602c1d10885102107900c9010303983e001084100800c02088513803080440b800402024911b00c0071916880c0c40c40e40380d10a03404d4880c3c101120b40c600214030941000c002030002c01b08064002108543c0100034489190710460030704510340148004407001640a009980a0100307071809148041e8950a0040c01d204060744617401399405680d541c0c007203502d0482602c00c000d014002c449 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 248945863 1250 248944613 248944637
    0x11032211010f092411070803030402010302070804030510092f09180d1206050108281e020c010b0108090d1b12021b100203120406020409150806070203041203 69
    0x40c1d03603220305403c03090307258242200e4003042c2204900390842c4d5105a695041602e0185880d00e80c462400d4002c0b064030760030800c002001b6501940080008034450146c6520b413550701d841d02804c0c902d00c44640c0c42c006072a138428101380210310307a0a2120a41101c1a44002290305031405008144d030b81c0d00343e001d40c1c1000005031004c020a0003900c410740e002829990040d02d9202d004012440d2444c071100050310b40140420254401e0502c10b10034210803100c3c12003252960000000c00c800b14441420590b03d030340905502c2e01400c0c4810228040540001d40c650300700d08103035400e440203044205d0420844030100440d90030001035002c41e20603e401d1040895540b80d080c0c02006041c2c4c0c0c0b015013020141c1d841140d07081e40c00a01310305441e044820303034034120b6465010803a100030008845001a44180f00140c02c8411080400e60041d22510f070040c0340580da50b40c00c00c1595811081035181250005040190755020721040750b2000032840614500390600426401d0544401c0010303080050f03900b401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 248947113 1250 248945863 248945867
    0x1b0d020f2431030f030b06030c03040c09060803090a0504090b01050607082a06151e0118030302060601091403061b090406030b06100201020414091911032211010f 71
    0x1c40c003805141c0841d0581140b0446050380410007001c103c0020f4180c2c1441001c26101c0e124806034440003e007200c0c516143c40100b22040d4001030310942d01c4030b07070006c400100c1c00c44500c9100014030180340515101c203203080800103075510315031009014905004040d400902529000c80c156442150310b19280d44550034242e03078034000d51413284240c4448008200d44061351802c603551115401089840740d54445080c9445c82241d642da040d007080d00c801032205540f01042901201540600d841c12556030484519101c0042c039134010b8000d60002005d100c0c140d44d00c6800c0001a11121b9801c5c0340300000000426514000104101d0031140107046610211030f00304101d582d0390600030002d10203943c607405c02040f608000e032180d600c0f6401125003802e0050043c000e540031100ca00b2042550b143d441c81c10b0040b000d03c000c0104001e0300440c03128404200300303445604105510100c4494591500b081004180d560b00313160207503075400758046000040c00000c0b400060200c00c4c40c00300b504034151001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 248948363 1250 248947113 248947141
    0x306020f070b0411120307201903060c02060903190309020117040b011403010b011e020a150c030c09080a110105040f080a0605060103061a0705031b0d020f24 69
    0x100810403101c02d8148402e221a561040302c004000b280c2a42254004030a09070f80ca03c10403000034400807804464031610300582610100320400500000c41c10320104000c0e080d0300104d60000c9500558403000e9145480e41004481e5110300550000d500e400b84202c9c000d0940131520007030304105501d62540e03d0841e4410706064041c0d100d804204805402d20b86040c50140b070007405458442003540d4480005403405014a000200060719a0078801d040800c0c0704400c000700207034200c2584950300180c0002401c6501121001e424541c0000302d00711001c0008003a82c03040800d4030100b0854440030310180c000455250f601c164040c42d1404207070500030042e101c03130140d81d01c80350384042c0d00640080c00140c082120725580d8400c510820080d9920340040d402c440c0c0340d010703402440321350b03201c03640b01441c030710b002090381034007900c2224180703403a280180020030307800501c041d41a04046c403181e2445e034040101c212310035401d1005d084200400c06002d104104000203030103203e8184d4011a143d00300e1020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 248949613 1250 248948363 248948377
    0x30d0f060b04030503070201080714070209041e0f2006190c05030d1523010804030c0605070306060206060d1e02060706020c070e0901020408030304030c140601080c0a1e0306020f 78
    0x10100b921241d4074180759490360800401a40070401010014a4842c0700d5065141a080d0000140c2d042465680a0103480c0340004c02c202d81001c007242408003503200702d6000e05021480340c40c141016010603d407407292040c00042c00200b80c1086603404886d6900c2406854403007040340000c0e620414240030840b080703440c0120203852408001924800e01000707401c921260401300130300c0d8044035542c030100c0501d81410301044601448100c42e500d5190301c104015a0401e00a10704000c07020500c6e04d50384111881070341c0f0000400e079180c80c02c01000f50148190380d449642102c014051110399210589000003100c7c0100d4000044d40c407240c01c5503101810f03280344da50049021525443c091108a07035038001c501410039508521000100760314014003c0382e058900107000365085071070755607060301e0303c0074548421552000c1145500848071800c1103502d00030851000104112510704050000b600f0a03a0401640190403a490450820380d110003d801c890b4000e100581e00c9001460002007401116 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 248950863 1250 248949613 248949629
    0x50f090f0a0602010606090506040810020f040b0d14060f01020606040510030501090602030a200a03231513020901080f070c0b0901020a0306060804030c0f020604050d0b09190302030d0f06 82
    0x1001150250341548030703006031611034440c903003d90b0b00d40003040034500a40c0b055814339031044044000b0284941c01820043c210940d0890820392904110582504038403240a102590742660701d01000301010701c1d031341000b810b99451507029140d000007900c13884014095402103071a80041800d0303407101c004010085030010300030003900d0004d15204019600c140c6007240741a040070000090101d26200c41d610104600144504e042040071051b00a00003220f03441c1100070000c854404062a4500b040d80b2030b8030b07021440100e0600900800031481e01c60460680101c1c8180840c0030580d80003012160016000000844603a45420040b5200415640d0081240300514184640190150060424400c580d101406140d4036080c2c2106c40c40c1c81183c000e00018145200c041c08149501c607401540350015000901e8640c0724408140e0700c102d100e1045400c0c1021904009900320305021003c441c000145d11038000603142d4800960700d0050180442c98165541e2140619105550103000200140d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 248952113 1250 248950863 248950879
    0x7050906070c08060106021603060e0a0c0b0a030c111009233904020a0c080a020703110d0803180f01090b1e0709090c1106010b04080d0807050f090f 65
    0x10314190000d0000b038450624103104040000c50518008a8000c050391040c00c0840440ca1440c1c40f000003800401c0c2248070319000b02550000444d4110389440c2c003414030f40221590740ca1000c00c2c005e08441d0004080c1c0308020302220302071a060000310f220529a426090701244507801030414140410444001c50340c0455004007a16900901280500950900d10342a510980555486000d0051490100c0c440710070a1200c1440d589010342c040e0078038410703516044409021596a1110030b43c84401c1d5000581c0c80101c0c1002040700786d29103101d00302c000b0790709000b500300159601800340c0400346c100c5550640031141007441704000c0045070743c403114400c000e2140413210b0074444903d5900745c44200051142c190629524a4010202030003124140d07500300c240d80c41e04100c0360040600311903403001c01880901c0f2200c500300070401c09002e03040c00c804056840d0301d032081141c41e2001c1e0351401e2080c070603904200701e0520742100540311710700302c401005130b5104100f6002541c05a541641c60b07a0004113 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 248953363 1250 248952113 248952127
    0x110f03100f1d1f050408042d18060506090d0807031106010e040605090105090a0201360f050a120b0604060b0a020115050406180c1407060912030b0d0b07050906 70
    0x140020a4042c920303c2c4040050410103000107546040300d015140c010108010410000b01107a03110030009800d0241080700000c0100d28040c03e40303507000740041c150f0501c242544c007610f403203107000903e8100d446901c1e08c551040800c604c0380034620301600b410404100340040c90b0082d040040c202058074190b0701e00d0b686800c200441020245d405442052919000881d000030510138140569116401000054004d50045603c004040031500342c2d40d011150381c80c120710200112030001c040c3e82d00403501450500c8082d400080256100510413945c1380d208121000c0c60714030543c240e942205809070503035950f03400303c0d0140469a02c4090010000100d03640100c0e4198400c5001045140ca00c803030071a43c4404010a54505005c1c40744460b4002c1c11055201c40d11b175010369a100500e080000541001c4440304c8226001564161001510f40301c03500d04001085600800130075903400c04105c600703041c1000c10380d5450041e1006024851717542c0450303442c9000301c007540c8101c000104400d5440c55 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 248954613 1250 248953363 248953421
    0x90e03130b04090b0904050309090408160b090f010c17060301020403080c0c01180b16022b1203060605071b03050102041409010b0a020a0209040609150207110f03100f 73
    0x80903110f03c1940030724122842d0054640310035054060b030f420034011828900c103582085956980507204990500301000394000410300c41e050f01042c40d002e880303001c000e0300c5d1521005003070242121a601e0207074941800c000241e03030411035402d43c0d08040304101c5450750f0740b100400d009109542014040400c081203017102c0d0000098030090103002a81c82c0c00c81380c040000014100f038424041c3c180ca00c84d082c015075000b82c01d112580c43d14180010019201e0900204150f00c0d40c00c03010380f05156810540d05007200b444019000390808a19a2401700003091410b00010698018030100400151681850480d1900c0844100c1c01464002e8021544ca07aa00e0283c10241c071044d4588900035040900001240c80d403600a80702d203401e040e0043c10701640da41e0300f00050360b640204102c40c1300c1e50320010803001c9a203400c00003503200700b03003000144d4030500e60815281e010052000148100410320b41a4120307100444c041c425902e4240300800e1a2941a101d5406484c0c0b0001841406154140304002e0710 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 248955863 1250 248954613 248954617
    0x1406010b09010f030b0a14010c02060a03091208040209060105090409060c09090b01080603030403060b0a09110d050112050a030f030e011104140907140913020a0903020906030313090e03130b 83
    0x101c241c80d0a00c2420b65464103401365a28a07580540c8a00c00203000c112500d0454020b000c20700052410711181040c560000d90f85410811400c00000d03a9804aa03040146c0c04481c0ca680200b0b50520000500d0309030b0018484d0000280850b042020105034141241c0f01c9420200c03070540c1c402800c3c81281000080140004090721809440f00c1c206a0744448a500640001e402154003030083c500c0c00d030554a81102424008140caa045004103000094204580c85120b4440000c0428039503520418000da8082c1c51068200c024401c210744c002c0c1c1c0010310b0006000030700766070608000c00301a0590344c0503001040c03e1520310219509002609201d03c1044000340300782c1e040c8100c5514445401d82c18850684411034061003c00c149801040b50082c00c80060400000d0090403041e81001c44031300071003682c1048a104c400300e500110180110300d094840036034421020340042d030a0500c6800bc8800c1d017203480c494100410b50320207000e220203800788104c0340744403400d049000140307941d007120103196 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 248957113 1250 248955863 248955877
    0xf020607210c0326011203050714030a1808030a0f03020405040603080405030d030c0c031107211208060d02011803021002060f060603160e03070515040f0e040b040b041406010b 77
    0x101c1240304480401c0c910b00d1030410b501803056246456030700701401b1100c04110600168244130341440082c0014200064000c030000c00030010790740329213075241c02a0619900c3d4001e100240c885803028400c80c2030001c191a031004440c80c040744c03a4038101005400030302c107a030000e039003140c100303040170050019610080040381c2003541142e51581f607a10f821021a94080100c3c400a8440c858510110388a9280840305400f51030613140710541c0c840c2e0215906225682c07a100b0784c182e06040700c00707016100c0e01d0074840155030b0501001c0f514103071002603201006500700a042c0550f124404030101c0071483e2600146034003070050042548039020181d0b403800d044410150014603d070000d2000d00b000070507680103a01100e9107600102c54000c0980d5901b0f410010300c0d13014454050700007002c1d80d904d00b07040e0f40c801805250315a55400d00300e0070903028402d0380108100b084c0e0142804000b9260b901120707070094003e5403900c12925a072a12244005030001000a10701c100000443d039041c0c20b800600c0c0c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 248958363 1250 248957113 248957117
    0x9020a060c05280b07050c0105190e1519090c080102070c080a0b0c1b12040501021005060901090b0307170c1008072003070204090506060415030f020607210c03 70
    0xb440b480b0b00d90016030388030142081249003071444060010398004c0b070903604108182461828484520b0a5130300312082101d9103901000715100c20b201004c914030032250011481009030108100ca41c0a80b04d003030070050619484501c03030340c000e04485415035202c41101c0380e10038040d004855513884031034040d400c480b03416914244d00801c0080c880d40000740d5080c405a03c07143c2d580c40d980c1c076a200303034a0742d40101c940c905050000003148d404001c2c05000c0c0380340240541c201e03d9256402e00000900d02a00c0008107000fa82c60402800005c0d42c0304c0303443c641154101d20000c62107882c1c6d8004281040385903030010303141c0301004204000800c03010030000083c8000340e9080003100500e030402c94120500b5a440b0000c86d0007900000640d03405a80384490f011540c10407a40341c400554041021940125401e95441c0c00030303001e00420b49000d008000d0400144a980e079481401c60719186040200510300030310032080020b0300d408010b011400611245250320040441c03840011015180740c01400301100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 248959613 1250 248958363 248958373
    0x102010c2114091b1804062a09060f050a0207090902061317010b013608030a0305011707180b130f020a030e0f0a2301091506050609010c0201030f09020a060c05 70
    0x1400e4140030340044080001780e107090809882d542c5030301000780710106150100c81901100c1d02815002c0a9030580500f00965840d261245400c4004000400c0482d52b5000c02c4001c21145482541c0041c48405941d0540800101c1201d28400a246403040140310b4100d69007060300090003c60b164000d03201c64103030700028015105048011146c0004601c00504002c040d25905062071040c0c024090603100c0c541510540d5644400081d46582c00140000e000a5118001401803018030303000c0c10416030b0807800a04032241440070303000465110070170441070540d4a4045070f0055072464440202c1c3c520720941086882042d0320507501940c880522403000c00c2c10110b10030111103000507204040300c0f5440142c8842646540d44511085a07410807031050b807164a610560600c003841341c410014401d0341074040300d200c0400030109030b03007490b07011521442050042c00038690b0048018210183d091070001202080c0d06076200c0140510440690000c901c1880461281d41204110001d0342c0160101c072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 248960863 1250 248959613 248959663
    0xd0e0f010c0c02100806030106170a05011401030b01051003060b13032109090f060330020f060403030e03220614132913140102010c211409 61
    0x703980011041c80080d0007000f148100c1800310300c90203011b508540000c0000c41e01790381c0d03450041100c109a08054955400c100000c0381000390074400d8011910034003109504541c07441c0c0710224071074014401c40b80190725200805111074400e0b40908050100e4155890f200c8542e241100e50000c1d9600044402154180742e0466031381da001c01c201e280100700d54031215070b2414139040c0c3c130141c441c19048000c101e4846601000081c00b0084030902c0744240014030900c0100c1c2050550481341060790001550050344141d800204042030455205416040206e40400d9419000d8510303c6003820881d404607503d4001800b01d03c000d820f0b402150440d946110f4804c1e001011b4260b1751080003040701140c0d81505041016040d034000c2c0091000e8000451002c95081e40e0290049504c201d45c1c1c036080c9920044207210700c0300c03a0049d0b440b00c0030b07081c4020000c440001e8000742202481c81b9840745140381000510440400640101c4142d510032018104203041107118240e0310340103000c512411035424581c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 248962113 1250 248960863 248960867
    0x503130b0f011a1314120106030f020f0607110103020328050f07050a0215060406120606090c170a05180a0b010e061203070308040f020604060c05010507051305060903030d0e0f010c 79
    0x141c0e0046a1028448080750b1401c80c0003443d140c407545c0c006821034095120203480c03000a10649000314090340e450f00180a543c4104078082440c100307a544204428802000820181742c042600481c007804d005989454120507400c2c010408050240304d2032600ea0000c60210320b40c5c0185002e1000348902d0002500d40843c155801d01074a070800d40140c0c046410517408400b980b8a60340c202d0b10152002494a80340c01010010f01c802c0344042e280a40c40c1c01c401c104000709445180300b0808146428001a900c1810401c40700d000075003041926501c500220707111480700d5152074201d00f5141c00301c07441c1c02413910700642d008c4000d11500c03c4510705e0360006815030030007005a8005940c2e050241d460800295000d440107203015005941039101e021240c401a02c40400400180c040ea4540302885481f41c6407450a40f04000c10410070000c0c20700a450944450307002d0341003a00c0c81103610503201d00c284008a0701c1c50081200f001807650038404a0a440c074004500c80e400c0f204401d0091082c2c950764441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 248963363 1250 248962113 248962117
    0x7050c010605040605130f0612030512010608060f060a020c10200c0d080a0219030305060915100e010201020f03040605090708060403020705041e09080901090e0112030503130b0f011a 80
    0x40c00e42000c0d06d01d03100c0a441c0005d82c0f01840521014800146203078464240780b484140c1540d003200420030014454a6042003034001900400161810207968075043c0b002c40c40d0074055511481c040d0901142403050a402400092504c83d000b803c00c1001e0200031000030591207000c800580400382c41e15040f184480040f404442030040a010314603010301d20750b2104a02e622255a0004502941c050080c142d000123200c03540040c004e40d408203047c2007a40411071032010250240c0701c3e00c420040c4101094070303a00031702c01002529043c01504d441001c17005030301a00c01c1921516100100200b0441040019805140921001d208403034640391103151040d0740f400d044e5005800340e80204000c005a150a41003041007150014406203030120707088502040c0c403076243e001c030fa4280b008a00d01c1c1c41c40d644420040c0080010503170703108042d40340c402a21020f014901010f4200074000000500d6102801c0d64150070702e50000c05101c1e64900440500380d01e1034207006414003035030202d854030b840c1524102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 248964613 1250 248963363 248963369
    0xb0a05010503090c2103030f1b1314030c090f04060b030604030503011214030a030f0b0f06030105060d0204050603180c01030506010e09060111100f0606051204030c050a080307050c0106050406 84
    0x400d001880d0000b00705a501d424005da0361010014210b0152800e4140055405181d02c0018807002d82002d84040150350303011121045e07140b0060020b281114528480d480c01c541083d5204041c5000040200f8104181d00000e04c3e08464490140030b0700404000c107040c8100e02800c01004068644010562102810781c0d002c1c002603402e0005014019404501524052050505121441c02c034003000c0d003140c000c5410900030030f99031034070b842d80440e050140310480b034411206490041c086c880010024041801807501070704c0041400448030b0260344c100d50103480c00030401d584038603101398004480400349281900034054050200881e50081c0110303406010141c50f101c042028481c24480c0c0564000c040c0e40c1004005010318800392820300c20402c7c0d8034444d01020410004894580301600c0041d8071400030010204075500007001140105600154107190440441826042051500d50600b43c0500001800400c0c030402e550031030014150242c90348000c4c80413503911410041120340030b00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 248965863 1250 248964613 248964631
    0xf01030201200307021002060702070f0521030412051c03050103080d090f14011d12031909120f0305060d0203060a1d070e04021807050910020a060f0b0a05010503 71
    0xc00c2000041c1a1414504441d00520440c2c0c200804c42d0001341d180d07142406400c0260b001070081c000140d0f818058040680440070511005030b280c60040b80045815040d00294060f00210810081400f80200c400425003108011000075560900c241c40d169948915495850b03503a40c0780003a28001e018050407207800c07942c05803c00000600600107800354060495118084456020024100c180d40c900790440b48000081c0e46029078901141c01810204040c0403644451503110358a18680e084940c04002d504650030301406950402d0300cc3e005400b00100b44420b00c0302090f00340e90388000c100c0706014031075070284070581b956010f00001c1d80600d44080d4040d004a000560b000f411600401c081c5d0808036400300b4038000c20302401e0b0400c071041d0002d4500914100034801980f9080070002074440c0d0030034100745203042001c1d02400740d02c40c0140850203000540f2800c160380d802030000e03103200c903080481405001c90340c56604ac0148014451588180003400d4007040f5544903000f581c0c401c031098 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 248967113 1250 248965863 248965877
    0x60306030f080c0a060501181a10140d09030e040506040e0604080906040504020d02041d0f130201140c1606030c0c0204050a18110307120503120403030605100e090f01030201 76
    0x9031900e008582c04401c41110724813482d400c01000444610440f402080c0d08000400ca6108004201040d43d61a03401361515000d04207040b91103035208a1030300c1ca1581281410900a150201c0344c1d4618090b64900042180c83d0107620000e050300400342010004044a0130419a620002004201d81c40100d1001265000d0710010b00020380e40b070020b14015000402c1c040c202551000010160380c4082c031001262900418204500085542c064040c815a020800500c1c9030500c03d170000b2020082120000046600060082d6402186080c4030310107035401d10b5598040b1100079541e1142c3c1c07102c1d10ba190700c04d07001000640e584603110301c008413016941c4052004100e0f80811000d484041d1440c280035942d82c4840076007480e008500c48102c1e00c0f9504031844500458101410000303594070940301c070415080c1e0000022000300844240e240360300e01e01c1c0065100c1e070404900502940d04190317004241031b030060031401d4011a40380b5032048200c4404078255141c250710401c2040030f10000340480e46d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 248968363 1250 248967113 248967143
    0x902032803080c130305010b0301050c07082d03040302060f0108280606050a15030608060c0405041805060c090301060f05011b1505190b090702030315010e0a0b120106030603 76
    0xb080e0b104a400c902140595030810743d02180150705540701d41c1c02100c6a07076640d5403404483c1000e0241d56032100c1c646406074105446611036440c1031103829019003881e520424040403418104100b1111004641c0c0302c2030301d902c2c003850080d640c4c01c3c0c25261304140402c154000502c02e0400905100c2d030500c00c800940c2094401003d8051254900c4011503c1c40e4440314081030903200c00d51260010a00300d0340700b110282180c400681110200e40140069070010340410614842c01c10464040358425903000500300f0521103101ca8071001c640e802001400350b04140f01090030210050816008100c008006d49a0b40c0c101c1c0c41c0d1000e00a00c1041e011130300310000b200301c1808104903407014a0082e01c6110040e80342e041076400301d4008803010b034181403401c002d0580000aa204040b5103020580e03260500341009440a5540d01006101003610b4403280401d0081ea4407e1125141064001d02101840b9444000d204141d40040b601025001034601c000526184280100411641c121500c583e065403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 248969613 1250 248968363 248968367
    0x52b0309020f090403090510051204030e12060910112a030f0a050d0605010c0c03080c070f0801020712080c120a0204120507030204110a080f07210902032803 69
    0x4a650020307a4000168448642c0c1600c1e00390990740300720b03c01e07560909568249400c00454141003510002040000e200c18100364104940c90f5821940509092880005080018000ea0705807101003a02e8000e00c0306000901ca00000c001c2c800c00c05a8800341302c0d1051881002c01d542c09005403914090400020b043c9140c2c6081c280044e0800310740d0700341c03440c00404180301720f0340d5409440d1040020702d0006a400d00c0441d240315043c040c05003440c240f28944440d450340301400d0024003000d02012000101c000b00203104008100050012181d8044d2050b80c40490b24000c1d0013070f110907201e080c011003544180d18400c1003614864640e181d569130824503070400b00902c950005214491080c0d00304008202c9481404840324001d11074002401c1c030b2421031043c00155901d15800001100e020b001d0810040d400064076540640c0c2c2e204481c3c0e0a80d10400201c440c40c21806185074903030303003d1191388104603144d04402ca0a0b8001c0d03044650400307100910261100890102138040050117550303000081c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 248970863 1250 248969613 248969621
    0x2030a060207030c0b0108070e1b090111030c070902030109051503070e0a0245030d03020d0b0901030c030606050a180902030a140d0e0306040314030406091b03052b03 73
    0x64080d11340038030000d00c66918410101400e030400d61550340040020413201002206683d80031480d0307140c1c040c00c0011041c6000b4035018000410b4140648841c01403441d00c0b0400130703100340d4400502120301c02c0d5512a210b80007917000307008119a00d03045c8000100700c0786050720010141d020150080510300c0c50190801c08058016000380d100da50204004030480710001c0b00380420404402035203101c0e03807400080040300e4808540300d649641c840200c203001580d020070303200c104580314103005da030320114030714220010704141403095030182e14500080305000c82d8842000944c0d106074420860701d80c81e202040710100355071140300c240300c10060020003020b005400c0606150301c080c0894034065400e541c4e0f412080000d4812064561003442d013407552541c0059103170b1400200f50080c002c42d080644008001501300091107100c0b00001001c03500300021076020001c820340009030200407007030000a02c0740305561840241d9441c82040283d41c2c2d084540551042e44061032150170100d085460000d501030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 248972113 1250 248970863 248970877
    0x219050304061b05030a0f0e0a4e121106040201050c10050f0901181109100806070c0209160c060c03110c0c1206010f06180914070807030902030a0602 66
    0x240f1020390340100140040000d070950342c2840d1100308845158100080c048510048014410f90302104104400a00c100312015244880230103050740508851327a600c880301107402c034100858850b010516680720301c00015000507124490810360407181d81812174960030341c1c1400350380c1a00000085001503000c0c60043c000d03191001c023960341c3c014841c0c512400301c58046030751044542c0c2400400a10310300030b10030b0b50102c10341c0c10701409180e2141e84503105002070440106001c1c860780c60200f0001405010381c0c6000b001f039081110b19520740454020050806888201e015100000120306000c42d18095090310170607982d146010307040d080d10380310058030740c8050003001d26a40e11b5482203102c1c1c14100605104110900900031848681c09100c1000381c08001e11149401200062007030b036003851107000480d038941c505013000c40c00b40c2c50f4580d58043c4684c0a011031500d051500344000100e0701c02544a050207403940041c0d81c0c1c55010503010385000400c02580350708901d55090000d003080c0d003c5c10385 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 248973363 1250 248972113 248972147
    0x140d2a0203031201031707080708072102071e050d0201030c050c070609180605091f0b04081f05011d130f050303160f0e010305060d06050a0c021905030406 68
    0x5008164000c80e00b5580240b5014110300d072403500510501098510840d0079461010f441450b014a03038071603610300c0c0110f075001451140c0015142d41800407003c481a00c540d51001c0181c000207912401035902c50b06807048281c51708094058911501707441030b4a404545000c6d000341d01d502c4181d801180105069003482c000d00c541404074030319414080042001618290b101d09030241d040140340c074001c0141110340001c20781410030030300641c0c803000a80c07504480244d0410080c190820f02c000e001749419000812000c601280c0058041c90005140103550030501c0b62442e025205148042990b03c00d00504030010369001c407000508081010043d030110981c20308550345a510343e80d0034529000386a0555441c2d001000780464010a448085440c0145082c2810391a000102c00340c54440c40941040c145991340b00003e110340c55809540341d030194401c03400c014510704082d80000400d5214100e40c0144607500480841164011450a4940e00200110f04191800c2022541c100700b00c1d501d01c00d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 248974613 1250 248973363 248973437
    0xe0d05070b0a181514070f06090809090708040c050d0c0b1612020c0a090902030a020d0602031503060f0103060519060303020a031706130b0d020a0909140d 68
    0x4403200e1040190200d11440d550f146400c03401100c0c1c2c00f1009a840c1c000308038000c40700304010001908890f42607a0782100134442d540352401407e0000c00014030410151007282404005000c01000200511408000300c4400d45642c0f10b11508484144040350010700300c1d10840000d0040c1e00d410030054007214030440f015050180c44100754a9650083c110002c1841100380310042080540c1280300c0419100303200800b16070740018000b802c1140184038102c0011b40c0c824103a000c2d1740b02071002001c52900507205449821041c0703400c1c4000c0d88200c60102068420303c1d125003552601140c5a8001c02c1040303810215a421501c5e118020030380a000c040701c040098131032440c20300c11401820000d5000c3d40182c070306094030b0709014054001040f80c0103240d85000c0108202d90b951308402c0e0400c0c60b80070707200003016002980400c00e601c8602c41c010f0352110803000000f51810103a0040e004a900c1002d000800021050045507034095210a101c08100c041e9002283d609442c0502c07112014145085030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 248975863 1250 248974613 248974619
    0x1a040201093014010e0d0203030a1d01051302030601090e0a0623040b0103050c04020c03120601120212091b0315090a06090809010806100507110a09140405010b040207030e0d0507 78
    0x1204419072442115a40000030360203084203028407841e40305503078a0300a007a0781b00b101c0b40029124440101558130084ea181044000988507032241100c410691008000301d0610720340c0036408084c8043c040b07100303208142c0003084082e214056440c00102841c000d000c44081943d604029000040c070070f428011070b04948580c0c0c070042a04040c000c5001d80d000c0f40007541907090903424015840d08080c0140c0c010489100c90841c0082141d00c440610f041c2080c1588070f05004903011903003450400d1040e4008203090044007a5107607903900982c000c10031a071105218204085101044005456064000d05090000192000c000a03440200388043e00c201104554485c0c0c102c3e11104d900303840c01480814001d55a503007002c50241c024104482031200002503100003002c1d4828008001c0410b5841905038805403940300780e541c05000307145000d00040716003404800d46510308075000d560540c20211514011f09081c400c0310320454050b81c0b074803000d50504081c05030084640c01c046405105441c400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 248977113 1250 248975863 248975939
    0x1c0804050309100f0e1504030204020a02010e1c03060906060c0f05010f050a02040e060102160b0901020c04020d0b031b131113060207050112050f070804020a030c0905041a04020109 79
    0x500f608090039100e0318020443c0444c000c0c510406002018000c0d130b0040091103448404009a030100c82c0d04581c05030740d4000300d50b002c0b03000d42076180198245109201800f030b003260202c03070401c110310b00c6075030304009040e9290012402c5d52020b00c1800041601030f000100400c44404c50210b0150040b8008950000d6426084045502c21160008080c1c0d020905010415880041c50b4008001344003d000003940d107039003910240040d1003485011030000070002003590092000c04c0401c0703001401152501c1c0144150b00142c440c11000910901485426040031a5100c46400a842c000350444010390784010017000289940790003600782081c11300080c4841c0c0845403071300b00500340ca81e000d0106103240030f00141120810104151040e410301d410082915981200e444e4000207514040d0125200c50001c641066240d8102416000074a03a0100f103040312a080103000d9442100950021041c40480803111441030314020b0004440e0300701042080744801d400c410420107e406402d04c090b691000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 248978363 1250 248977113 248977129
    0xd14060712060605070b0c031806010e0912071e02060912011407050708031b04030b0109051b09030a0209060a09021b010e010b1f0203070804090b0406081c0804050309 73
    0x10040001e101e01040014001c100d020300d0005242c42c1c02c0c4a401d0650542e40c6012503140103202e0508003101200248500c030415410804c0c0303900681c2510030b01d585403040010782010496100749903101e402100fa8408460707004840304544c1081140b40010f0652480070200c0505c258180e078000341c1400500c030280e4031484000b0102003a0400020301001d030701001040800300515800c00d010061000401142c80030003200c0d030091080d009001240e040c101070349058020391300081c007103480440011078040e00b02c2d031005008014a0000d203007101c250001a0029100b041007258054000c42d81400041c1090030840350071200092949242c107454000c0a012070300140070007908600701410382c510b00c2000f0702c91820807600c550700a00ca24011203010031030200500e031b41000c4043c007844811f041c1a04c2442a5a20103511441403603032581d0b2001044e01034880c4c0200703584194941900001c91170740000304406100110195090002c0c031000c0c0c10780310b4039002041551a4041080007980e40e50314011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 248979613 1250 248978363 248978371
    0x309090c120f0c090b0706060b0f03010e0c0a090905183c07050607290103020306060108090d030b0d050a0321060b03151201062903150d1406 62
    0x1c1c460035140c103500614010b41d4090041c0030348180c40e001d46082d4243c1d004000c40d040e2803010350100d940b01350904c0c0500050409502504040c84007268000c041794040000314100c1b400ca50b0b46617000d031111902001c50380f0940302c202c0302207140c3c003104001d80c8066812040e4070981c4800c070700c95079920724517446040688806003070113628146891190030141ca02c1541c10300680521014000ea00302d5101c40740e071020f0768003503036216090104540d01007001802c03500912240088103100c00004402c800d4034410020302040b846409180300103400b41d48501480c0c0d100c2c60280c0b0081000702c4000500381c000304000128142c002029410000109008000260301503200c1c0d0740700c1e907007014240b00c105100807038180b940041c5810484204441d04035402620b807c00c4550344990180703050761001506089903620740312080c0d4248040082c2aa000c90010800c4208982110022446551290b615484111070340d14100600b0800443c607030525003000c1c1c1009100e0541ca018545031550b1132454010111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 248980863 1250 248979613 248979617
    0x1c061b11010e0c101404030804030b160201022a0a020307030b0a0c050703090506030a140403080610180b0d0207080c10110301060503070309050709090b0a0c09210309090c 75
    0x3595044098009200d15440c0c00754407005462a58122400140030500030504581046403004c0d009001010400484008507885100c465550b5624901800b0480c030488001d1800c8034076505401599006008403400b107a000340394003860201201d100801c01b10444400101e0388200384600f801610104120790155005110b8110146000408a0240c0703004051007003c10105021000c0001d401c5014071090f00c40460f400c2e0b440385c0d161303d02030000300300044c0100341900d5010144000e25422402c1e05018801c10740ba140108200b008050302c0540030121100a18101624108403086200015201594055201519100031a261680150030400111003c2e412001162809a0040c4a04129000b0318084641035614000014050b4007006002609064449111030300f001814880040900450b030303420080d407000e80c188a100e02200311040e180f5a4945000100c6079401188090b04032070383d50640d0103004207401d122001820290108505100ba80800410b2607136090140001c5a00d00d6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 248982113 1250 248980863 248980877
    0xb0c010b040501050303040602060c030a0b130c02011a1c0809030106030c0e010509150607020d06110711092205030c1221090616020a0803040f051002091c061b 70
    0x14080000320b0304180d1005109034400c00003042070382d0300850030980c09510f00d8043e07910b9a03a2542c140001c1c203403c040c3c89901070080301e00664000400e6105691900c0e06600070002040c100c0d40962810410103003542d400f11400350384070030030007040c0c800448052080307040354100f00c030200209094503c0341c0c008940901207000140420ba21501910340104000c84081c00941011604a001c842c11400010b014060000d0060301f9521606c4c800c0c4156540104100304e0301002c14092112600324190403650640903640c80c15003454285102c501500c6c00300050082e00d03030584255443c0e162005e20449540c0006d0000e620200b0003402103c4254075840c6100b952402514140b4640030700600400180460130030900c00d40300d2000640c00e07807183c20a0041e925444d80d2043c16840c01d052150020440e440010410040100d10074500c4886442101103c1d1400807a4030b010042e030007940580381d0015101c4003844407010700d00c3c24242d181406140002111501d1030000740303814000b400a0741c003191003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 248983363 1250 248982113 248982131
    0x20f0306151804050403020a0c0608090c03010b090a05060a0e0403050a0e040c020a1e0b0c0406110f0c0f0f0405090c030d0e0604051908032d0708031306060b0c01 71
    0x410340007810100840e03410103241c812441400c550000030800018021540c90002404050082003500030045e00002164074207a40c1c1ca000030041a02141c0342e8089008400440100b4201402440c0d813121006202040607928860840001c14004200541c014146d0000203031074410380729810b000700d01030b0f640c40e030341e4091080340580014840c0590070b001d5841c00549130081039011800d00c06250f400410018040c2140300d05e21004843c0480281c44c0f44202e8080c044c3c0340d042000244103c605640302c5810340700310001c240361240d44160b50903180d5000340c00c1d225140d140501c0d03042400c040c0188032001d0507550502007411250200c50842c00d60344052041880d500e010862842c010529180c50450480c06101140d120b00803803043c940100d50751841079924030000d41e601409001c0b4801141d0300e84548505030160030b4100042031070000412070766000c01d1005081100c0e0b86941003000c5628503241d150a01c036100404101c01d65040d661098040b07030301040d010041100c402c4590000c555041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 248984613 1250 248983363 248983369
    0x1f0305010806100806180f0d020f0f010204060f0503070c12120b0301051005011d0907082e0611120307030605031501240c05060a0e010b0f151606020f0306 68
    0x4000d80405070f8000c09080400048000040b4154810020ba404101c1400701c1c0d98490300e807041c1c411008503036005013441d070010103500096440c0822507110403210710030b40c00c40c016400c0384a540141000038000d0300c0b036410414007440003950084070516040800d030184c2c0e11950070444003440c1510004088440006490505015465448204038000c11441c1002c891400d11a880c921030141800041c01001240e01c51a4a03402440c1c1000703007a060041c039040c0001000804111842c0c01ca111803d0f201541c0c10000c003040446444c1108500d0449a06100d015940c01032403103640c1426100e07000c94102041020009940035017180c0c1c401103503150520081500341001451807403808000c6800400c0484d171680c0702d0804110103040d45420b4280d00400844030088401c00c060040d2150a003480501021030344140725040f031040081056100790400c00c65100c0520013450b5000b440c01041d11040c001d1040200040507048902c6041211030369030b528107a030440030b140301200c3c03004020010241 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 248985863 1250 248984613 248984623
    0x20071502061b04060f030e030d0e0d0c05150619080f0c030a020907030905030c0a0302030a0f0309030f12060e01080d082a07020d0b090601030516031a061f03050108 72
    0xd64092600d0326003903840d82c4124014040c80c401d039020000407030032200395a4002e912140071281c0305000d0b40d5442c1c03444003181002d071841140e00416840b0380d4050100681c0720b1035144003420740c0840a02042005030001c2c9101c410040c0502c3c0e4404614100203c0f014a00e4060740004c11980018003140c030400180300d410074000d43c002c0ba01941180d114580140d071a000550350144450600151084c0d290400600d58040d5000301680c2d8400e4158000516800001400c000c00c901d42c1c07202201c0d400f03a40103d0590368010750040110323124450100100c0c2c05400c01c14034030790600000040c010303070315007890070104000e070f2207411141c01190360b18480e03e50041040b940000c26200c10700780b19152040380c0110180440c0b001015000101d0507004640c2c84030030b40c1120941041d00300760542401d01a00b070300e44c002888111481e1040c0ea02d0a000781c980d003c0c01c0c03004c41c1d82108040000d85680c201700c0d400b80c01d000b010300780c0c00161046500b002c1e000c22100f11120b501c899500144560511041034981 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 248987113 1250 248985863 248985871
    0xc0c03070f06120504081e09190305060f070e0d03171b0403060b0301021303080306041a03030f22030c08060708010f03080c010609021c0b060f03072007150206 70
    0xa5100744800b8070046400c10050340351429041000110303951703207040a17910f41c0901440510005001d407450101414214094040301c01e00710303040f4031441071225064030580414031005020b03400800001e9080c110300d00c0c805a0003d0a41440c0da64480d04500040d0304000d8440b084002c12411428815003020405416500c4864040340ca00004e002c62142d01c0c0ca40660700c0000c0880da21035940c80e560307490079010344c3c13002d5001d4001c44134901d40b24909015190001c6550764060741c90200032620a1080421103046a1006000f8514040d0960500c0186a00001c507000b501c1e14a2540150b4007181001c03614001d50003a0184d00d51142084c04150400c4405010700d020814240010320003040c00e071001201301c1e9840b060a55441e05402600c7d409007038698400214948040f81c090028040c19500742c1c1c0b111385c00a81041616452010080f090181d0301c010300d800c1d2024000240c403640181c0400c1e001d4110b000d05e0350700b00c40303000c101d10780f401007540c1000400f10a045500b00342280c0402000707400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 248988363 1250 248987113 248987129
    0x1060306050a09020d0b0c0705101e05060a060509060c07030812090616030c02010b0a03050c010e090f0c0307121505040501060807121d011503051207050601090c140c0c0307 76
    0x10012490300060b0902005582c0a4100541b2002248040103000c00b04c44500e54403000341d8010400c2a600300c4000d1030028060b08090605a0007021303441110f00c80c161103004000c0180041c54106038044842d80c000458183c0c102d5420041c070071008a041201c0d200540c45024101d41d59518120318040510010300010400d41c0300105000e038285600758180650091850001580c00e45004120f024022a0502607001441480c001c400d000b000720b40e00c510020280c03281e0b4941c492000922510f06800c5550907800000103000c280b060314000001e48d00610180340c094000c0c0103450a020458000c1d03100b1020110545004000718189806454010f10031814100b01d24541048080c000c510901c4000070b2003565a10b03128040380ca900e504807004200007008000112150001c031506400600050f00d8030300c26800107004c410000b8085442240e800f0025206d5a4a000702410241c40d104a03e41d080c010700200b0800100d20070301c003815040f00c0200040c482030600500745403c000340d503044045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 248989613 1250 248988363 248988371
    0xd05040f170a02070608060a0e18071a04051c0b0a15060504030f0f14030d05100801270302031b0606090708060105090d020303040e010b0d060602070621060e0901060306050a 76
    0x48029008130382d28003118141d080284076582d800000841c407040c0c5411940c1807007140d20511401c60f00b03030104000100f81c0581122441910340c0e81c24402c07100140b2485088160800c410700c07841c208500310030303c00c0c90081c4100c110590180c0d10b02c0003406c000c4601c00c00d07407942c4204280342281a1428140181840d0409034540350940d1508d48080b4000e079008dc2c9200c04d450800c004100000414801e1056000152500c4051000010015100c240c40310301302e43e00280d030040f40140d01031189042c80480d00c60180c5c041080f1240030074511030080d10035025800240000d680300d000900c0c500c0700d46030460340030f0b208524114041043c0780402415540c01c01a40104000c0281d03001000c95404045c103c3e45500000035900c0068694815034202c5071040c0444000025090700c0c1e003000e06004003074540c09229013600c0d44412a80e0780854030031600000d02044081c040c00c060b50920704001c403102d41001c98078548030b0f16034485002d0161004030b460b030b64400003041408100c3c4161900305a5030385040c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 248990863 1250 248989613 248989627
    0xb09010e0103140f07060e01020c091003170405031c0f08040c1a090d03020105010e07020610030b19060e01060e0a030803010b1c090303090c0504140a050702030d05040f17 75
    0x96112041400000c220600c40d808908030f00d0010800c0e000b4aa050340102c44105072610f800800d540c1a03094414054400c4900258a40c80d100304458410b0804c0040c10700c2881c590744500950302002c4041c410940401c00c00410300b900c1c2444030040c0d83e0f03410740342d4802c4440b21200c002c0014805500c80820000c008042c0300020340c40c456408100e540c403862441c504842040c0c8804e2034441e40b94030a0713104094800c0c900405806401490403610011a11101c3e9a80c903041a82c8900e42182c01c89806500b1a0051002904d02211030340c000348100302c2061a4102040d801045807596002074034490b8014004106155001c1d0202d020000140e03214a001491640c900440780010b003e48001900042414291015401368130701162003025810320001d092400d01400400c0701c200d0070340d240f1105000101c1c0700c0c00e00f80211a01c0c0c106007000f0703084070364403180011b0051070040d00301e40031030104001106410445001d1140524003070880c0388500714041c91b140c1100c0170090754024414506101c21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 248992113 1250 248990863 248990879
    0x302090c18040c03140a050f0c0c060f0a061d04060e010608030f1822050601030e0d0c0302030f0a120606020f19081c020d050c03010f030201120608060c07060b0901 72
    0x703080010400d40740070801c0c4101c610254003403c0c204e1058a14940d40c00708009064600c2e802c43c50250950080408142d00d4204078650640700700c03030741c0c1103169010b0303008180c00b0035022444a0340241006000549652640055140b100c0c002c1d21b50f030300c0c212100c424030061184a03c1181c0f60000c0c550b0082090350700c2c1400050b00d9020709014550481c0740403415000c080e64035a9240c05a020041090640b030030320360502882c400c980340300305014514060001e6580e501a106900c0f8a20403400140401000440212001715604408508600040c800494540d050a028200310307000e42e15001030b5400019030301811a040c640c810310440d40400da68840e011404510207042200703541d41061540c40f1400d202c0c1c1544904120010b0b103c2d1403100c00380a10a040e8083c1c0b45449005c2001c0c44942ca4045250415000030b00034907550f4810910308000541c01130503454204140c90f01c010580c1d03513440880f01d080480840e0000c40d543c1000803220304001140c42600c11a4a04403451403842d4145240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 248993363 1250 248992113 248992147
    0x6020d120e0a1401140403091806030809120c060a020c04050c091f18060c020102061311060a03180c05010f0c08090d032c0f0a0b1e041e0302090c 64
    0x14190380401c0a40c0c050320f1101303400c8240600b03d010390010480c00c003444c00400c903c00d680710300004450521307040d60412001d80a0f030004c0303940090700070342002203c40800c181411190401c00281c86a006207020395100c0340050040c0c2d60300e68000d41011203c110a21058a000402c2352010440410002072560b80702ca80450726400c08814128104045036025506142011000742e04082c1c10b02e0700088d40759019440c507040c2131003030342030f41d100751a041121030b400d2340f00707441c02481746c00e2000095805003080701c05401103415a00d008500805054030f901c4251600c1201500d5241a540c810302c41540c1000109810403c0b5280079001301810341c0324141c0074081e1500c0c043c130500425541400340b40c8620b03012455115480602480e00b800c48003080108400459000d01950803141c40c0c0c045441d00c0102982200c001407100c5140801d0ba2100080058915440900ca07100c14000850240d0651451440600c40340c40c60703807100c0d4254010403690400042c080d0241e498208240c58250b07420b281 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 248994613 1250 248993363 248993383
    0x20d03080915010b0a0f18030c030c080f0c0423011202010329011817100501060c0b0a0207020a0305060f070206061c0311030d020f031909030507150908030106020d120e 74
    0x940118060100001240d141f9502152000c0e550f42006001c01807255071080c0d40101ca11586108441e656100017558494164250441054114403020601420103400081c071448681441c10040c0105424402e2075100c20381005510f481e502c4400780855070544144640c5000113050340c0e50030070705120800f0300345890401181c10088204486600b508500b040c080145c0750345407016a42e47e0b0840c0d130155071003541e4041c040710981414000280c0754000c0e901030381c1c01504221900c48903619640070b0f0010303610500c1e0403070b0010f15095001001c6001400014051340c0c601c2103004090914010003450008003038115440f8008444500348000600e5203200c000715803504000c0c0a00450105641c20340c09250030b9041c02c0341c0000b4256155403030950003180720b011780459003a1038845c0b1a10f0780c411070f8140381c001000b0417010002900450325204101c8610152200041421310903551f40d100309420070307400301c3c001d40d00c01412601083c0e009081003c0c410b9035035004020051140702480d54441d0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 248995863 1250 248994613 248994617
    0x10506090607110103090602180a050a05030706031a18040501110f070609030210230901020309070e0405030c030406090501030525050d060806040b061f0207150507020d03080915010b0a 81
    0x81c0c030303007083c99000b5040f0788409a0068021911103440c40160200c400f841c50609101d06807018001c9060f01d8450b800c08141e8401a004003540740c108142500203004010200400300c1c4c1c40904040d46a0301c058944100c06c50054020030306003040c0c0750441c00c0d1056107800c1d0148410500004105031180070070346400b9134000d00040344403440c50400340d0400819045070301d052420b2586201c0300103100c0c0c44059502d440500e1100040d59034405d414201d01064554440d540c001203400c00090644591080d00140520244c1b8505088018440c2c5903501940c0508007142219104000c65a014070900394022080084c0817000c800ea51101100b0303411290308c2000b449008a401030320f086496019902a0400008480b00390400e130511308044e0900f1a84103200b48880000340200c002502c107092343d00e041c41c0d0003c100e0541401c2c1d040040b0761080146004001040c4881c102580d81c02c04400c80c1a8081d84030b4045604040f00e0180c200784461040c2d0030300001c030b00d00411418201400b1546424168 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 248997113 1250 248995863 248995883
    0x50c10031409061e1e0601050415120b0d02010e0402181e03190302060c09010309080a08040c090b06090f0402070807051c0306050310110d020a0c0b010506090607 71
    0x958164000c0c000000c0807110241040100042070100085140c0034845140e024950006400d80c0010700f03c404450515110417040000b01000308610072142e0003e40504045080588544414800c0c03000b02c00b00c100000c0c4c1d20004030501110521500a041206982e00d280310780041d00080d05116129440714000ea5000034400d4410880d00844548004003c00410318801050505100b01c18180c0d01c051003030003400900c1c0c002076186031504825682c9500600001e40d03a154041905400005613241856116585c0a0000e04c80c20014800c00c580c0303495010140c1014102000b9051294001044642c42c1960105665894405542680b10121070041c0c980e041040454068080c24a006140007004074000b01000f0f00032403051442ca074011000c849942584008805440c814411550950400e1807840c0c5400d0098010f4403858182c2110355181000004280c8100d80c000f4100c070700056080b81440040009000c1c0b01401000100e82040c01c094101001442c00c1c171840500400a40071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 248998363 1250 248997113 248997139
    0x70f0c110103110406030203090d0c052e022110060905040f020910081509160f092105070803030906070c1104050106030608010e010e06060d0f020d03030c110307050c 73
    0x110b41c001084841c030380300c0c0d5503413201e45c1e070000900650400c1d51034102034010203607184c4085205078519100b02d03400a0080105624124400c41a100c03400340718000845141d0300780303a24800b1400148a4151004000842d4055441d203401c405600a400e105120b00005420440c003640819000191001201d0004008110345010700082c40344c018141d80207183c0c90f524600071070b00002c1441c803404148142240181c510010041d82e004102d07010380c000000c003900c0341200b904c15200c011031100d42d400c0440503287c55000100200310b42071001902c42500f80e03908402c00c50309020901c01400c0c80d2000718110304282d140940c8810b001064001080304600a4100b40012000c8003050014041c20030440d07541c682e00d00a01411003401420902d40c02c000700045056014400e9041d5440000060f191984804040083c2409620000d0347d011001c988140e0250389ca10041e10781d258032035200010744600780c60b03014000f00d54662007c11141c00c24005e2401003039000c68100b06d1150121240701c00a12 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 248999613 1250 248998363 248998367
    0x203012c10052b03081b0a0822051506040b0105161e1b061103070c05040e0709020d020a0e03060118021b01020c0d030f060513090201110d02060f070f0c1101 69
    0x10f041210030203200f42d034640300024103420903541d50054070408600c02802801804440c902d20812103040005075020340024040800d030144441d001481406640c40c070025626114035103c001000352000b02d02c03540600c41c80f0300d020f22a100600e4070a081080c00e107030b115001303160700e42185c0d45c0103882d6100001c20200b140103a2004040c040e54018084541e08403603400107079021582d1700403036000c00d00a0389000665180003080d00e00d0661320240008946007441c0c1400080c0144170784100f6644980d20010a003616a800070b4402e001c20788600607122900e40d000100f0741400300c107007107020303810000050000c3c0701001e0208036420a4041c001d0782d00c04c00d02003121010664070140035100d52010a420015450108800c088443c45035030601180d941c4c7c4104a04944461180d2130b40007280c550b6515802c20320f40c00c05886039005040550002031441d82d000d00b01906091542c0058000804000f10710034541e926682000c0b40d40303444203101000d0400074000248040015243c408003501c4099681c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 249000863 1250 248999613 248999659
    0xe0a030f061e1a040e100b150403030305060910030803010e060f0406080a061a1003180501020318060c1801110a0213020a270b03070509040203012c1005 67
    0x95450b09404142020309082c00d0092078066904000e80c070240250003414a05401a080002801d2000d00140045c9050700001441c50b901555049030a80320700054a2540300d0203403006600070346002c14a464800c0411189075001800d01e5018000c4010030f00100b10200c0a40f815031381d40d1381d89d220254803030308001583d141c400c501c119030080c24104081080c01c004070f0401078840c032501003801b05684403d42204100c0c40f4815035034100e9541400c10315454032a0f04094001c1d009103050b0201e003d926280d83d42aa40101ea080c4243d001c10240321003140001c10502f94405140340d080c0d4180388100d0f0b00e070324103206e0070b1000034100000ea00e6941d144040500c000c90300640c1c001c100071485041a0301e0a80a5000145400041880180162141c803041d80345116001144d1142c0801582001c01240440e00054403200030030009208000d41ca8485200442c040c040d91000b0715080c240c2042010150010450452040c1011400703001064103140c13404019950119420710f035000d4510214041c2d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 249002113 1250 249000863 249000881
    0x623340b040c05101706010507030507060507030b1302040f03060b04020c0723010801030b04060203090312010b040f05040207020a0311032802040c1803061116061406010e0a030f06 79
    0x1604102050004110b50b00c80800c04440e0305a5407a894100c0065060ba4088194000009000701a00000e0580d40c4240000d100c5c4130300c6820690b0500201d27480d05411581c04503a100c010036582d042c5c4581510300f101c1e2458404160650940c6041e0901c0d031401114040d51100400c0581c8641510905a1f9150141c0c0d0500c101c80007118840e65551840c010941c800d50000322031101000b1074207806522560b14181a240c00c90a882c0362901c8650380c43c1d0003540000d028000070300050220700d00c51800e0008540c001c12940940e2519582404040c0c0c00152050b0300440c4147e1041028100503200d0000420803a41c012808018000300540860708000c544e005c54400d100e0301102e040480c00100703400603a01c90007074038100002c0f908400155075010509221f03186131044c420f810400141c0c50340200003c20300000d0010f0408500055080560b588a502160b46a4488803c0780c3d52a0350f01c0b03c241c1d4004030900c2e02000c00c50b0904003160407004c40b404060181d598000e8490188844e5030000190 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 249003363 1250 249002113 249002123
    0x902190b0414041d0604060e0703020105030f040f05070303090509010e01050108180c0a0b04090b040605010c06020a020c06030f1902030601210b09040f110402030610080718062334 79
    0x7400750f40000c0c040d12484111b608a0b0a180781c050400040440000c0074020b0740d80c12385406240d078844290031030003c80020310407a0900018101080020303018414680254031030b032914800e007410305040069100f01604910706518a200c0100f259a902c03220042d000414030140120303140c10f000c001c500f00040009503540081551700009081420440103100700c8000040c100210080b100070170041d20310301d1003950b0000355200c080401284050b4000c00d0320401c5401190051a01d440c0450016007080b0307134407810000000c0030486d507000c0842c0403224404c001282140f540c40c000740060401045e5045800f03194840c100d554000060503030012010700802807264480b807821b460220a121250001254410417070f0b00c0002c894141802501e001c0c040040040000300d0310b605c8100d5403200010a21402c0100301c00406d02c070060000208405040c4075520080c1e408d44039451000051018000b40c81c045100700080c0c500c14204031000d100c2801e0031010f800c1090741c58148040340451036a07010344 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 249004613 1250 249003363 249003401
    0xb071206060c110d0507051c020406090905060a0b03031918150f0906120209010e040507021011040320011107060807030621081c0f0902190b041404 65
    0x30301c258001016810051081542d000e9020080c0306021000d402000014000d90110301e0a102a107000300056100484840c00b26520030500e800007002e4845550000c4402680c4400000c2070100502c80d042e0300c0081c2c1d070340900c0036520702404283d0b01c0c82400401541c101c04015200352080c0b1a00c408028104002e01a4016a1b00d50b20000c0c1c0320140c090880c008a081c4204201e0010700522a500842d192030b2a02c02800040c0e0300e01d00080e42c0402c1a6604000044030408416540d51264038001c2d031040c0d0081c0300c030800c804000e404a41140a200e201150144000c10000d101c031121030003021025a8900c101000f41001a156880154030400c5503004100002c00c0c0380760710080140c8180780669050003c1303580d5030a40d20300144207403100300d02e0038442c14614011076541002401100d1301e14030702d4072800b0080340e941c2048070a1f600001c00050b4581d60b0600c2903207490700c1d4116005070003490030321640c1d103051101801841103100b001501451540d0b00b03111542d695102a040100c03012150b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 249005863 1250 249004613 249004619
    0xc01050f040e1504050f0c03010303030207110d0605010323120c07050303030103030f02010606030b030a03030e03160f14060907030f0314030403030b01022a04090606080102040b0d0c0f0c0b071206 86
    0x115601c503e40308041e0042e0702c0e03d00001d080d41180b554007401002d0a094036495a42140c41c210041d61006005440310001d21001ca10700b80c880e260300c0110540a03403000503155045291076500c1d408043c8000801000c92881c4040190700850b541e041c80640202c43d9503600c0c802882c081c1002c0c2c1d1680180c1d071602011000209162b00b050510665090700cad03000f08019034441100f9070484000d071038065019400300d500c89001900a612080c40030006004590a00c45e1a410f0710f0340d00080c00303104a0f004840000310104106a003d0716040718002040a00014030340b5001603a17855030356100143c5440744400e040010305000e161111211402803400ba40c2d42d2074035040240281c8050304602d4010b11911001400201c000d1004030074400c20418141d071050341c0312003000301810311004143d50745640c0304000142c003602440244010311407480c2c0c03252a05d0880c00004111000c620411062111281a200c00c0c1c560144d80748400550000c0010080d440b1100200c3c0c08016243c0003c100c1031910f4404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 249007113 1250 249005863 249005881
    0x30a080705061f061704211214010509160504051c030e03060603030d1e1410140307061d0a08010501290301050d051009081c0209030c01050f040e 64
    0x18400d41c009440f6800f0120110001d100000e036522400000031001340480401c02c400166541e0040c1c06101c0030420031190492003940d8901c0380e4040008541000212590b03070b000350050300d031415071500807410f1039898131011515040740180251255030340d40100e00105070040c401e0310080e041c0680340841c040b15548114001113110078041e001302d80981c21086e00ca04e030024140d4443d0f0f202401035410301ca00c0c050000701800c1c007081c2104109080c810f58092040d070520900c81c00131404d2503c801582810341e8445200041074011041e201c800c01e40c49407071074400242030340403141d85d0700d08908240440c000310062503ca4070040744e813103180c01900080e15601500843e041c0d810580c1030510214040e415284540d40b2800e09102914090004115a26042c1c0d8003071051400b42d004c1c1e490f1b151100401c50116600d0b40c00480c0c1842000c46e003a00ba10b05029800704c6010a41d08086240c07680c01030000b0395450b0409071342d03030411400081240c00e104103401030340c00500802c81ca44650b414030a41b1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 249008363 1250 249007113 249007123
    0x1c0f02100c05040f0b03131b0806100e07050406050a0804020d02040207050a03090b09030a1707050303010b0310050a06020307020d02150d0603050c04050f04080304020114030705030a0c03020f040e0402030a080705 93
    0x1089a0300c0310f914804100040071400702c0f8040c1f10b090880c4060450b4a0366808003882070380880c00d214005c6030400140c1d04c20240800e500c5202081e150f1305040307003044404000024007618003410400c05100c10310090350840c08640c0c45242070708201103140c1e520710001d400501403c030025001400803030904e04000300090320343c26081c400d807600300301380352150440f42046c01581e1020740d140d0f01c204084004a900201ea85040d03410800c1403a00c5c10b40641c45840c5581d200b0b0740001461030f0000b080000e09150319840001401040720741d2003610380741840003541c0740a42c401c040d118101081c00f110441d0b5072802e002c403106180e00040398490711411414001415144810b56041c0501d2a0f401005c1c41c05100d400d10130611000035040c5a112910b40210a400041040303050007510081c886a80e4002e8020314032899103a99840d640b0703d041d020490640345c040301c00006040c010320100e040e1103443c4d01928140d0f03002c06c00c103000640d540c3c00004d10740218036001810741c840008d1044280040450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 249009613 1250 249008363 249008369
    0xf09030806042c070302041b090b120a1d1902090f0615030702010e030403060c0e03010603051002130504050702060718030201080408160b01080f0f1c0f02100c0504 72
    0x4400a4903541c001c180015034028810540b848109207100c810070115010a12041c08000800c640115480b40c4c042400c5481c0000e030801d0650501030b0950745136512a0003c005003880311005030809800310b8212618000c0581011001e646441d242084107002d48020709590144404480b80c00029215020742100901d205a0285d06408001003038008000c080794040c46010300303000b20030f0b21071f0140c0c3c061175040a00880110754a07443e2000200c030b800c00240000d1030080c1400200400d00942c09000c003403791403294004e034140795081005c55000710780340c084c600c00c0c55030142c0d4506c010029005420050741105610610704402e1000281e800241140300f244035850384402e41c40909500340b03219101d03100090008040800040014408101420b004c030010b031401a005034803640d843c3c0e4140b200346c000440940c80801c1c202c01c0c40d40d0402c0721508501d4508080d04000c0b441e0514207901c074a044407814140110484446060f510812900c820420310701d03000c2002d20300c0040c0007080307980a84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 249010863 1250 249009613 249009617
    0x180b07090e0402180601211a030a050a0222090c05040b060c0607030f090f05151044030414061c0902060408010e15010608010b1e09040f0903 62
    0x103400850700e815015405802190001d0102c4400003d0f222413101d036100040c186410017103441c100c4200320407182030024800202c940081101a05410460807080c40001e0b0741c0d101e0b40c403070035105001c1203002c60000c504130740607181520800241801c4241c51400003a080c50600d16251540d004c1c0f02a401c1c1c444141d41c800c46041c03106090b11400c0001074000c00b0940c054a4003d04040b4501d02e0180e0307c0b460221500c0d000c003055800c03940e226a00410b418440590b050740000314400d80d803041c1c42c0c0205070721020f4030000f446581e0070102481c11204044411000000890840540310340050040c3e01c0040581a01c1e0120b9030100c032001e944a0700603101d0700740d441d00744200410340f41c98404180d940b04e4105076000c64162902400401c060100c502d010b82e0008020480452255000c2c003840c4000070a500c0102003100107038208501a040c142c0c8500c00300700d40f01006010a591070021a80070f8058040400501e0100c1c22664209126251920b030b409403825198108510251300240712041c02a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 249012113 1250 249010863 249010877
    0xe15090d050601090e070e0703051b0a18051c031b020301062705070503150f06031f0b160206030a14010f05010f030e0309040c02010603080a0503010e0112030807030f180b07 76
    0x800082903840301c640c041e07078200d83c1c8811f0001c1c003403a11a5115581c0140c00707424079a406550005280016840740e6400d0001804a0300351502e007054070540700004010664411442c1e918a940c3c03001d0001040d00020304000e0640c10203a0034840b00c1e110a040707190014020020660707102200300c1200c02c0e28404108002c0102c5481c03001000603c6120304c2950291a00707855641c550f40410407128080300d800d640300c00c101182224684820002d50302c00c1540c0c94584071400241c1909400820b1039038003a40080b8403c0050000048060000203446a4192099516500c500d8802c02c00b90600c900c540340c004940f0000068091b0948419000f00e9500f030300c980c8900010380c00d0407010344042100c2000140d00c1042543e000b4202544a010f6000d0188000201940c0f42d940c1d0002c0340e804603c0301400203001000502043d0207110301280145040a0300480300700c07990303030080c20145000303040609241d80e0b11605800c080c0c00e0f4004d03030103e51040a410300031006a14204403440320503500b40d4002080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 249013363 1250 249012113 249012131
    0x1a040305100c08040b0402120a0b0a0f0608120703050c06040c03020906010201151802040b0408060121200a0306020a120f1109060a090503030409060503010b010503070e15090d05060109 81
    0x80c0b8071070241d10040d19039903400303140e545031118140b650340608126048182031240400650702442644c00c010702c034050341c410a080261090095400151800303d80f546010703020808110000380040d11080c04489003034a582080c20b09032554040d54040004a004070803c000801149240c84002d907442160310f0034943d00e0b43c400490880381c48000202c0000131003035041c00740c0d4a040d644420300d540d84c0e0740092300e0982c50f0301070204c60303821603805000d4580c880b000507c0402400007040304003041c0c400c11a0303810344440c3c4a100e41401c80340380d4158002d004501c16540d40c1c4801007030f90090b40c0c21101c2550340e5004100000c24248e070900da0694000e01e000c2c00ac42620040c2d008590380361016804503800d0045100c01c109096000791084002e0020001c00080c06131800d0002d48002d09186000051170781c906400e16003911303a4002160f0410070100200301c52039400c400f8850600c0c2c0241c928610200800305117401a12410400690011405054808105d00040c1841c160380c4680d4040c448221 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 249014613 1250 249013363 249013393
    0x1050103051608030306010e0609190e01060513060503190507020d0306080f25030c03081902030f19090801180203070902030606090d0c030c030812090d0e060706061a040305 76
    0x1100c0d000702c01c0e0540017007000c0b6510398419500c80b0002080240554030304042c1c1382c0047c0303000c82c83c1001040c0340e980908007041002540c0300894018010350030300500e031140420818000f0300040c000da5080c0000800441c502003220110717522070b4205007400300094207182c48007070359600000c03c041d4002818014085000384010820825030b90165008003a806541441d6081e00042d4600351112904e14950000100311107d102000540c01020401e40c0e540c190301501ea28810900d8032a0f040d03500400c81c0b0340300c00510300e01300d6140c46034000500384c8807080703c20100e4251505070301003070566080015581d88501c0780352040442d180308404554005d6038981c101002e0380011990190701003020701c0012114103044400780d4119105008101c0019102d40da0b281a800c0c09030410b903141c0d4000301c3d1b5031045008032a0b15642282c0d84400502080b03040b408003c2c40d075600155410f01801012a62900300301d03031604004040e0101c0000d1071951a88270300032114a410602c01510140b080c01c60125100c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 249015863 1250 249014613 249014653
    0x30d0f02040816150f0e0307032f1c290601030605040603050a020108041a040305120f040b0117010f060305010c080c13090b0a030f03031a01020705010203072003030c0105010305 78
    0x80015190324803144e14000e066500402c0200301d5001d1003190180c00c90340f0780d406e0007580040c62042841144010001d8820304d40542e50a41c0086000841242249581e540c07080c03104c10324020083d01540c92800d8078000012100b404681c450092640205440058106031214410402a6410031985584d4000c11040e50101d10010384550400e440903805544240e8903964050701502c8681d4aa0401d6000740c50500d004907130540004201080103841e60300245500c0d6001006600706800c2d908180e281c103110000188186103044401c80d04420159000f90400c100c442c0c4840e0003040388a582e0704101d40680280c1c61b2040010300302c1400034a000700803006541d0080c8041000141f0386007407070f160800a00000c200d280d0300c141c03c02d0b40000091040c07402030150a200741c0c1c01042e9100da09696905600e8081d0400f0b041d9007014030705000603640001606e10381a040341e811034010b00030310104089440b9140c40a601400000341e070342c200d02015040141202d111341c00301c036071014000c2e024103548 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 249017113 1250 249015863 249015869
    0x90f07141309090507051309030314190f0605150c211608040302060a1706060a0507080702180112170304021503060f040f0905010e0a0f0b0702030d0f02040816 70
    0x71000032101032044031020703803140e00854801c03812100202c0d1580005440b03d428290241e00050703c0d903400e502055850f009a405100d000c070940996424110088410304224800c0c0003a41a40d400e840402c80704141c0040006000290009443d04584100c060040e4441190030321248103850081c0883c0300d80445080020628005e06814007074940d05c40702c206174101d0410b0324600000d11021015030b881000418003490140c03203644a550107294442e5000c14028091803003405d0500551160540040031100c0c0c142e8440e500c00c1d95001184000785586419011560b610705800d000842d8001407031400d0351940b07000d4001c190603814181c210701010311049030001d400c00c80b513100e81560140460091908603500505200b40408203070f0124048401000d0b2540a4079202c0316010280002071040380346100074407019041d0416940c17152001b0301242107008010200392800030710501c0c402d0091300c0c120012a14180b010004a8801c3e4001e50814020400280503561254003521070fa0840c01c021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 249018363 1250 249017113 249017137
    0x3090d08180d050a11010203012c01060801050d060204080601170709091208090f060405031305060702090c090a09020f0a0f0203030603150907030203010e03040608070801140d02040b090f0714 84
    0x481d140900b42100e1a130002c0b000d09060060341c59040842e0707082030019602030001544009080e00741070b0f6407604091f5030070b62624020404070005100d0701c0d0b404000241034600c196004402c41d6420314108000303118507031001085004140021604020603003440d01d4501504c01258840c0c6e8941d0440c5c405c562071502c009000c040640c925011050180709000d900c03150341800e54001308070002c01142490700841e41102c0c05d400c0001d2840001d84d032000d400000e0310055418900f4032031030f80e0124082e818041c3c01852602404901004030381c0c1c4000030380003e040003003c10340d20ba00025110342ea10b0742101c1040e0011400b0b200381603071030f188008107480c406c4400030002d01400a141c024007500c00ca001c0e16600392401014008005a01d0074000c54072600002c40046503250318040d401000c0001c064502d00c02c100c1054010058003900084000040c00112148900666580f000038020010300c1e010341e400040e01e808001d030a10705090761a1013084140c440b91f0f15144528165205c6115003500541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 249019613 1250 249018363 249018373
    0x1305040309051203191205041401060b09030604230304030b0a1406010e040e010e0a03050d0605010c0515100f14040c03051009110f070818043c0203090d0818 69
    0x603698078a25180801d2200c02d061a034424006c21504105950049409072102c2103412071241000100344964802428244a41e9081410110010341c0382e00010f00082d2a03080001e207403408031041d40000d400000041001c43c0d564950301d01c0d2040c006401103e5199a01d071501e00b400a0040c0c1d044c01980c8119416541d180c00340f0284800c1200600402030041e42d50340d0383c1e0701c103200000340400144603000d000e074440c1c075180c00485102c14292092a00054100112901014005040060b10b0500c40022072480501e81d03a0700055050030003100d500080016056540019201410901c0c040c0d52403400d1b42c0500040303807000820340c260707017040c0c80b04609482e80e44070801ca1021180e0084d00d42201ea000003503c0c2540d0480760204a8221410984082900080d04001826140c962101c034004c20365040c010810390b916140804010b000101c002c90010400342d829417140102e03291030028020204540382c0c00c2c0b4003c5959a4041c80b6002c00206032900c0c00b007031000c07900a440720800048000280 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 249020863 1250 249019613 249019627
    0x2010b0d17030a06080105010909020a150c03050705100203010f0303030b15190207030803070e09090609030d020a050d06180f02040e0411120303130c2301080c07021305040309051203 80
    0x41d15030b00003080c07040120707600c0d0300203c0c5500080c0100d9008144030000031510403181c0c010003962501940c0308003000c7c17140e8200c4078040394100e400c20640300e030103081003502d440d19410000d091000c4c0c40240c584486c4000004169101c1c81030f0b4042c03c1c0d030b00a543c100110000002401400114001880c00d80c04080c080d42c0d100c610a0716080b032110b2800c0c815281c0706540c96603406035035041a2940342c00b15016400e82201c03030030220381c0c0342d90084c12540103141604000b5904c1d6200d00c902c0d0070580109800007195181d0a0107501103415204c29400c04001d010764030f02090703500720101f801ca65085400e1007071071740c2d0380d003c94001d07a4140c620001c0700c0080c64465035158000c601d113200400740c03c500c00c001200b840e020240701071880740c0303524120561a450b11786001442401135801404e00d0170100342c0c1c0029600c0310501c4070012140d0a0a122810341c0b80e941c14402d030703030245000095014000001c088400304c61078010034003952007521041c24150b1108100706410122050700c40c0b080d40144650 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 249022113 1250 249020863 249020903
    0x270e160315031203060e0f01050f0307030816321b010e0405090a02090408091302030705030420150d0f060605030a05040809040f0b120d0207060c170a020a0302010b0d 73
    0x40403031035403c2d080008040d40d81300176990b1040c10490740741c0da243d08000010446824203030300f501c88200707084000d0900c8c0c0d801c1d941c540d0490b010301c02551101c00c051003032140070400c09101d03004100301803004000382c41c02e803140110a00218500220701a00a503148030b00c00003040c40707010741402c005031102001c1d001410180b20041074001e1210a942c45110810805600c80c1281c0f10b0081d4011130040369110300c41c5052014100c02680760800c4580f0410400a901d641320080d02d030042c0c0c7c800040355404410100c4440143e030b40c0c185d16a030110407040c040b951031000d007004044502c54120305000461024284000310703401d034410742e00420010000210100c10a80c4180d62003485a24282c4c00d0000f074401040444e800a00c017940000e03a0b582c41c40815240030340b05120600038000041c18607031f4844500a4942e01e2502c99041071040901c12502040754401c2200d0101c51310014803920b64991020003969140528425005075180008004031800e09894040703070280c00003081042110300c8045 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 249023363 1250 249022113 249022133
    0x302130e2b0809011b050c0d020a0809040f0f0e03090901080f0a08031801020f0306030c0d0c060e01140d0b120a03020c27090318030a020907270e16031503 68
    0x484001395a00c4408000b29040c0843d0f15030312104990392a43c07150444100e071850b10818240b032030290340c4880d0341c16001401010490360100016100402c02d0341c1e640480101030b1262880904a0a0501d403c403035810340b0001c05480303510003c9901482c01e1341d070745a8060315400041d5450540350482c91100c1c0c0481d00200007150080070040b80014240c10300d50005003242c20444540384a030340c0c008180700c1e0b2881c0c10005186180c0c3c04850b0368690092590b40e04129203882c0c030030b81d4140038440c2c6e01504507a015002c50031a1243c41c9840719a2220070f030304100008c00754006041e00c50750101081a215480000d4240741d0f030f80c4d040c0c000300611250b072170130000032002c0c0180d8882100b100e00520400302c843d118556004106a03c02982c60361305003001c0c1c013713510400c1c62039400380d0300000b00361001d80c1d00c9076142e0340c001406092900c200c4641c0c600000748441c0c0c4045003000a0100c01d000944842080805846070238908480006401140d004070180d03a452084546a000b41070001d0002c1281021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 249024613 1250 249023363 249023371
    0x9020310020c0a0b040c031103012a03020708033402250321030f0b030606040f060b190305070507110f03010e07061112160f020a0302130e2b08 63
    0xc80700f00012030f0f550086001003c9a00f15000e4808400c2081000f06224a1300a841b40441c002d0001c1c04500103059441c01c90038444416000c1e20b40314030780d410f5010f5230403103007034a4011028503584d240c0032000c564003800d100c0d400ca0350200000c0d01100c43303804464450074030110f540e02515004104141d034400c142c4071000302c000e001516070000000900d103a41c6c1c459254201342d4500241c018404405000c480345222501d602a0801030413a0280ea00400e06980c490411240001c0c2c03103480302c401100a08664000042e41507001400020103408481000035001c540c2da801d100503a01c11204948900a11100608000b010f08890340d0b02d1400a400c07000b20ba070040e0001a01a5959410701d103441c0c02c6621070f1000c1140102c0c0ca0841003003e02440c12413003080241149005840c0c006c41e500c00075400c0001e0081d040c1c5070f10580131540c03810310103c01983c00600d03024403010081026402461144c1c01000280310703001d501040d144184403615035808e10740e00140e19080012209a9180c2c00c000c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 249025863 1250 249024613 249024637
    0x203040609092a0e03070602070b0409020c030c010608250e0c0c100606091802030103050c1002030c010906050604050a0b060a120b030d08060109080f0304050d1511030a0b01030902031002 82
    0x40030311540446a100404200545582c80d400701440513410705041031300a130010710454004490900c010a080300840e000c5980c503a00041e5039050700309209056000300000008594202500041d5100c8009a56070b0b0201a015000030f04d45855005224404007601c101d85610110600040260216202401c401c084035016101c4c0c00301c200076032108640540d00040c001c6070821405000c84204004040708412605108524650643c0c40b5182e030b030494841c089104440e240140705a0910910595190740103c0e0f00030b01082a851520b04050f200c103c4441d0301480c035005c0007400c0364009005189501c413000d04003a00d80094840c00b100e04400ca82400c50303445484076165240340e2400c1001d250011010b0b80d0f908a10309065000620300a0b003540120496485000400c4095401004540844a0481c4c2400b249006864540c7c10713002000e09481c4454503021030301800b016800015445292121810441c106040005400300d0318800e801035050b41c04541c6d02142d440c0240c1c024070000c9024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 249027113 1250 249025863 249025901
    0xf030b0402031912020f2407140406030501061d01090e0c1c02040509090f30120105030c0612060d11030d0513170d0305151915020304060909 62
    0x2008480421040103102110314a136101d03074075800203905000d070207220b145210160002c8041454104100d0030520440d800c10148070f40412903482c052603032150701d24964104d0035141c1e81e80c0c410185c0209824492080410b188031000e91074000b002d64070380e14401050710b55222942c00c08000850042c0004c10301c00415008101c2020940d002c0422648030b07203003000d0050391f11820501480b4440001414581d803d9010031a203100305203010850030841080f00080700c40c45800000c010400410385450f03121070403000640c02100000c0c2c2e8a41e0342c146c1d40705400701d403001010901807202a105034554400002c00000109080b85005603200b1440d03801380036102d903840c0312100000d050010060101010030740002e650401401c8440e2903000400c42905055405c01e020800c1640b200240d14085003055500c0700080e144000c030300d4400c642118054119640091f0801100a510034280282101c503a00e01b02c001c038519100004540940740c00e65600ea0201c4d01c1e080d400c501170040394000d0072a040030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 249028363 1250 249027113 249027133
    0x130515090f2e080c0a05010809030f0a0e040606020a020108091f021b161a0703140702031e03041a04060c0201120f020a050d050a0608030f0901110d170906010f030b040203 75
    0x181210340e0024201c40e101414444001000700917200d80c3c95441141440203d0082101c3c0001c00f0003070740d8002c50030320b40007503607680700344d80448641e1140d103101c6500c60310b400300100380b0276800119034040030b100ba00c40c080075843c0c0c4109143d980e58902d0510480c41c0281c803011300d078140070343c010f80510340e1a00c0802320350708040c10000307041041c0480000140302205108124071041d0907003012072103403180b40403031900c8101d440051404507075030441004000c00080b06411522f01f044507941d0720850070089181c1d00201e800c0c4d5034883c0d002c1c0c42039108503003106241100032031000307080724100d42441e21a140c0d02ea41d43d0780190790300341c800036407882d10996a02d00d02544080e540006d0500c50881d669107035841600030f241c0d008545c00a0000d01115203001014007080c02c0020844040554030f05890392908520340040391018583d030143d00d890300807410304041c000d40080181e902498102d10b8504c0c26a105646103a5401d800d204c3c000d040303650700302d04001195202081c0b58010340094203403a59002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 249029613 1250 249028363 249028441
    0xc0905090901020306100905030601030303051e10140402040f140105130807030210030b010206010504150b04090b040605220207060b100207050a0801180209090705130515090f 77
    0x8003112589180c0c0d40000400c200b5260480c110b15030000301b03047c0740040030300f02800700b1343d1002d050100409040e51030021030b0100c0311303141a080c400c0c581e8950714035141c68a00c12002000c0014403030075104a948060380c2c0c069103418000c6e102a5500028213480c482e140c88002d80c0201010001d075411310104001100c3c40700041003c040240040720000d02000345184107011451b911140b22101b0546090403450840c1e9003c1803107030440d44101d801003074501c034264a421151300c0542c059030070b4410002d000246c50b04290880d5081c1c203400c440c03c000b03007035581050040310b0039845a0304181030340f591a101a1410640d0140440701e00504001502c81d8861001c80e00f0515000c0020b0050307408500101b08a00e450210b160140c54060300902c82c1075080d4003441c202d4100020001c1c070620080e40001c0f0a503104009840c028400180000d02c0c4031020046080103000545403100049e0b008526409603041040c00d0740d00030360750700e142810365035540c1c1c1002590081e02d14a46c03500c404505403030f515040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 249030863 1250 249029613 249029629
    0x71e171b070b04060f08040206040f0608010905011a0301121e0813090e2e050f040c0e061509010c0b010815060301060501050f13030204061d07140d0c0905 68
    0x88146000c40d004400390518951a040c49039100008030101044203000944d440030b1510300703182c01400c007000c9688842c400960540120f4200750044041400000303076056025143c039048a0646001304201e9032690124820060411280c1505041c108010070980c1c1140c0845a500c40c0207252058614144090451070f541a58030142c44401001c20700e2410324640c0481c0740005c0840410400c281e940040600b80c0307032580051640701c26a400508002d40541300d4098045203d03000800b04071030700d4800c1c1c084070301210647c1c003510064152100869841c4407071440c0c500414000700300409108c080d50542c0c0c1c03075504c100340d02ca04002d00c00d400703507001441100945000c0d20b00d40c009040b4040c5910008800340070010001840384c0e043c11410480c5980000031107000c5001141d440e030343d403d05c1d074041c880f02d041d480c0d20007508145010300002c0c14030403400409040d40b02e03c408a02c525100e002c2d044070b5120000c00b4094800c42c0800160400e0401ca034005a845001e60070100c03801d03903680c000a0910 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 249032113 1250 249030863 249030877
    0x60b030a0504060b04050108061b040801050117190201080c030901090f08030a230f1008060901020d050a0504240e120c0601120804260f010c14071e17 66
    0x3203034903001404108100c03801640f2916606a070700308955850000c24035a2810040c10607400c2e111100a03098980500108407000351041e08000d001e1540d40382600d900610070842e03452494082d8402d429803104030754450004558050391031400907220396080b0001c541c005400c902c480e65a03000140d000508251611030a44d005140142d220b00d494110001940c40c0e4402410650702a10205061400c944105c1600140b031440d00702540e5444006179042c60708141c01040152080394200401941c0540041003040d025260a010680303401c509034080c0c650a890040c1584410f030b60461412188403203d21411100050200305105070580841c1800c01d80d00ca840358a0100044d0544040c508125250050000500c0112189020b840d02c0300035010f2030150a1041da44500c2072a440c00da0103003a00c80c230300c0c01c00d0250358044940c00c1c6c4460003072103207000c0e0001065500401d41000d05442d4207035601d5642080c03904a244000f8140c005542104250441e0140041003003d8181c0e05072101504007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 249033363 1250 249032113 249032131
    0x2030c0903101a030d0c11061b1c05250c0f061d010905030a0b060301090c060804030801050a080a0b130b0c0403170a0c030e010903120210050108030405060418060b03 73
    0x1c80190340a03503024000020b00c3d40070307034060210b01c105194850044900541c004a203d0103403402440058070074410344541e40090303681104070262255012400c400c40498102e440c0e0b081071604801900e040c021405910701d031021003803296144071034161724207239424803466582c0ca03aa6181c1120001d582d03401d40003100006d0a0003002940689201c809031003005003420b00030350361460100040d9480700340380c10047c0100d10010200d100c0352000d40009a90503442524058240d890300e000400356a411181a00003e884a000062900304100100700b03942403403000d40810165611031620703210010700701e401c0d0720708502e11101c00b09001c500c1e80d50251000302e00342e6a41d80e10390308020075511160380190071031000c1009080a2590482c0030784a0a079803600304a44900042001618804920b920141c680d00c2000f072311040080d40419402c4e0501212241040f031a603e800c410340ea00d002c0c501905401880801090140702c0d80740c10380712040e030f401c681c2c0400c600b515403850407099001a106402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 249034613 1250 249033363 249033371
    0x20c010614030a11010c06020405030613050d0f0909020a051315090e07051204020301140c04050418051b210d0e1f03020a03090501091a091f02030c090310 68
    0x1120315010341c1c003107501c0388045004010285654940003114803c5064160504c602c040c600c00800c20b10fa010b17079009040003000e072100d40c0343c43c500c0c1c01c0501d420928220742ca809510030030141e182c01000c80d100d4800c02035850011440c24048008001d500c400c070701c0003e01c14284082404d1031400307241c4101400c41113800c01c8003036a03004405001105160400381803581540d040000d40780d0300000b85c4031640d00d20500306c00d944d103540c000300b8010140c43c0c40d00c4500c25035080402460172251030050007101d81c15242004000c0c029881c0c03420a600381d01c0c000380250006001c042000180080c161200b080040905960b00c00082c0c0010200542146a00042e00550380c5c07029a26040034441600301741c00c5d10a90440700e804900c6a0005070030300e0100041c16408580c24049d94803d600490003180e200340200100c51907401d24140c12600382410301c10b42c2c40c1c101c0000f188e18002041100c10405514045808c40f031600cdc1e80d46003e5000241164000d48052001c080700755010040d20010b6589504001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 249035863 1250 249034613 249034619
    0x50c16050d1e0503060d1718030c040e03070f060b030d0f0f14090d1509110a06020118060506031009060b04050a060f0b130f0605031e2215020c0106 65
    0x50720041802c051160700602c501e0081054641000840342d020004031142c10303141c5138034600004441d04c560b58585840d003020420300000400d05d005a281d81c00120201e904c50301e00360302000159451034100c0280e0360010301c42080001c0390301c0304036807205100e00030124001d004080481c0c80d043c0c8001e0381034001030b004407a03208948e420134441c00303907201c29280456401242b4049851203124602d650790040004402072424040211080c40a030200c1d03100901103106c25003030001c081010600d015200700a500360000b034141c01403052a02c50941c01d2084c0d80070240913106d0400515005007020703010300650701d4152001020b40314480c09244200c10000b4810402d505100c01c940d0300410000c01149032080911154103c0a000300844000c020f100b541c9062700b00700c00500d01d600303500540c1e02044640020507029000740280d0f01c5400d4410020104003480004102d00c0d40f8245e903815510300103d403c000d0403e18040d801d5040e680100980c014104106440c001260300803440e03945180d40d91071080c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 249037113 1250 249035863 249035867
    0x3070f050318190b03090705100203180301060f122603070314060102060a180f0c051516080c1c020f07060908030a030c020708010c020a0611070c030303050c16050d 72
    0x5403004058501104650300101040010f045600460354032000120004d5503020703003001540d01914015081103c202c0d09038001a6483d003110b518001c0c261080c0c10046030f90b00341403017880c0481d03a00300c1b2005203052501050303160964510805840c2c010740146076150381101d18100100c20f141101c0556601d24081344000c04440010403240b0542e9980d130300744941a83c1c0003a080e90003c58000c00040c3c034040d40c4034038981c0721391403000041c150002e5507496030902054041000c120303501034a00c4100c0b1034841854141d42e101d514403243d5040c41421040e00800c0d00c05001c0c16141c6043c0045402c4442d200707140a4010072120001c100680c84001c901910050510001000b040503003005101a414484a01c1c0c03a80141c022400c10159505001c8400034820440c1000078500c5000800289600f071000a444124241040c0d0f001814200e50303484100361441215501500006d030341c03262604543c3c088001c2c000c040c1c109c03001c4000c24080c0080101e4807481e5500301c28440c100424804c0c022600c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 249038363 1250 249037113 249037147
    0x18091e06060c02090403080a230f070c1208040c0302040207060e07050f0102060a0c0203120a0f110f0702010311090604060801050f0901060903030e0a0f08011d0c01020c1203070f0503 80
    0x450070401040076030202c0181c407100304054102c0e07818107000030070742c0d10800c42c20000c1034004003006503403c030364003081340b02c0303620504590141c100d125071a00070342d83d001d00582e0850003c0000a015201e0300800d040001d11569040380c00c240b0801f10140c12a5403a00003509070f03001210280d80865403007203109407590702003154400401044d40e0145c0703072072083c000203520780e04001c00101119031a020302029541c828003c640c018000b00030000b2280c20121641e00050610182c05c60200789409a44c1c24220200401e40c0d0713600081401007490140141d00440150488400700100c00b8010700c881c11040d558140074001600499070340c1c0000758501010013807240b212800b1b15001d20018070052102d5544840c0b203038107a0ba050309100b11611030710030104074134540c0c0c2d138007800d005c060200020440f0b040640005185070701401d0290032100f8080d031a5919403200310341c11405030788aa038000580e410201041134510030100c0a407403c010454880001800d90310030100d03503541000031250794180113910 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 249039613 1250 249038363 249038369
    0x5041802130b210105130510030f0506090106060e100e1219050c0406030203031204030507050a0b06211e030d02030106050702090a02160b091e100e011b18091e06 71
    0xf0b81d04154900400304448401a000b0181c00715201d00000b024480701c1d0aa210045a100d00c0d074628906190419544402007a10340b80135079401c242d800140d05214400c0c403440e1000003032030050420302c0c01400343d40c44007010103a1900561036500d011045642030050f010f9140c1038a800b400391444620703005050506803046280718600c0c0c03500a0015807400000d4443e03070414550710035416192420295090702403244021b181d81f00f07690441c403c014840c000c0c01c3c0950300c2038881a00886c0412740c041c204103558a048881c030342c044400c0303800d052032182858080702c9010080e6440d2042c10802c64003642e01c01d81002020407000140360f400c41c1440c00015500c644000021030910020461454000017040800b030510000840810404c020034032000100c2e00460322440b6044042c40842c40d10364194020708080c440c9441c602005405d4180103510301d00410204401034020b4800c001e503441c2200040c5d01085580c10040400c4003141441044484206200000480580503030000d06490b4150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 249040863 1250 249039613 249039667
    0x509042c03190c050d030504022101020405120d080f060a030c0801050f060109030305030105010513080607080109050c0a0c08030c0f160203011808070201030b1311130e01050105041802130b 83
    0x1000710808284c01043e00310001c1214580411507031520300014040e05a5900190039010221490882d2504154014402c4640a50b40300c180702c1d24035840541c81e6800303211040d000ca0504c0e00021400b48903904400e034040c8004052064081e1291641071803069103420401382690744a0a0140080ca2402c0b40c130340c010703001d00e0036460040c2966001815400f040c0310305418000701041c205818441550340401401e11241240d01620f001d41c001800c1d14020f1182c0f0409a20f0480800c107200e540c40b00700e8505081d5a203c2c80c185569a645020881d40000d185603003056061100070039240c0444001c0002c21849101c0145003420790042500b117651301310344644c00b82103600a03480002e00d1501903c4119809080015801910801080c0c0805546104144082ca010751030320711501b403c1c002c0c020010b050500b103000b56464513039520382c1c800c081c007aa50100350140008c01252000482c402d150b650070050150031f0460aa60b910208021504210000400070a400c1c2940209103a2640c1601b244 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 249042113 1250 249040863 249040877
    0x1406010525080c0a03140906091509092406041d0405010b0301020a020304030b01092d060e280b131d030301030b040c08010b010509042c0319 62
    0x1110010304507101d00800c19070604001c00c0c51072040d8200c00c00d1185400d4200b42000c1c0c1e1011201411625021181d13400c8006c1048080603101010b0950180c0c3d00402c0043c0c0824030b010203020412070444140052070003210f0301008000c01941314030756258001c030205003842c5410010805a11002040041d0701809004240400c100e42d480c40046505070207003c1b07803090b0171a2200d050480c0900481e40106415600008404403a964000010b1007183e02404500849980303821002081e1070054005072001c4265500c2c01d105046100f440342d100740c11540000504e00e5892001a004250803240818800c04030041111104289080320644074504134081002c07aa50381d0019943c0b190b154102e41040d540c0f400402502e841780305400b03403001d84e0201280e46940c0e580c5030a080c40c1e031003100c00725030203083d0300c900007000e100c14042d0b161a400f058580a0031302010b48240b10003040740510150910062859012100d0f05c2c1180141800303441d14040e650301c4610300c2e000c04454003e0306100c410003a40c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 249043363 1250 249042113 249042121
    0x60219080909090f0a03080a0c0c0b01032a0b1215010f050c0a1703070306050303070b010902071104020a030c021b011b05010e030307020f101107020d0c0b0c01090614 73
    0x802030803215010001c0310981503a03140c1020301c616050309098000b4840c405c2407110828581c022003500d2040c056003800780907031181110b00315044400700d0402441301084000500c0025401c0760003003140b0441c07407092104401800000b50b0ba001003540001c5400600240c09000c00072000c480b03a5114020124402c85181e1490008005007011142502088004522044d080e0b40c02c0c80b2002480740c03c501ca01458110400c518840c42d401a1840e9010034906140003e85040200c250341441e42c000049512984c40d040303114000c0c0d48440d504a845110022581c0f116a0320b91000e0440c40d51643d6001450071614240a0718100c80340c003040c002e0480090f844075041c4e1340030010b40c040703007950000305405000f189070541c05409800c8040e06240404410800c82550010715006e030110814100c4040c9001606204112600000c0c5082400f4042103a4000340c2001030310403907940d10502c0e044803c2903451645104a80241d52038001c140d440301045014803040303005101e0f080b035010010200c5414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 249044613 1250 249043363 249043373
    0x504030b070c02130504020102031603020c0306130b07050705190803060a0b041404270b04030f03020a080a180c0b07060b1203070f1110090611070506090f0d06110301060219 76
    0x350b604c0a0082985078000101103920900540d458600b00c840b007100300d4101441c0207034071040d0032182607000303100d02000a510030000341068010103402949100d0a80c1705c200040f10306910400064545200740e4201c45081c0c0d0603503e000781624007442d13000d502c0e806c05004000204d1083e070320a005805040c001441050403102e608410308030300b120300040c2d4041c600703040d940708400c040e0f00070749030744500050805010710400ca40d0b103d20b200b0740c1c4003010b0325400d80b0b0030b0b0100d005601c400c0c400241c020000901c4808550303c000c900300040281010500d40c82d40e14058100507940010800c0000072500d00c00301b201c14040d2034400b039001c98149412507060020141d490142c06005096280c004029800f405504980c0030030070b500103004806126549480030340048034a2103082c000420b00c41c51b03a10000380103d21f02040e14001009030703141902d0700042101100b8000e00c4030390b02800800441d0700088180c03041c0c6802074034044810792690726090001c0e041c440301c0c0c80c00f00d04465861400e0000a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 249045863 1250 249044613 249044629
    0xb09130920040b0d060506090901020301061b030201021209070f090203013b090309130b03060115110703050c040608151f0e0702010501050a060c0c0b0315100504030b070c02 76
    0x800c41040311010340c0001c00004000d4801c0c81c82c000c0c0c104040c4490f54044c41040d400552250f8000c2d248105c5070740312900444d080f44024800c050011b26080b0181c0d2400c52003008d8818502c1c007171310002d4200100d49042c80124641a50300003120b9021460411444011a41c2600100300e00103085086607d000b103140c61a9020111744001d4084c856504011444001c5e9030344141c0b0440d07e6581d0084c94600c003030955070b60158080c980304aa0002026844154900450341080c0d000707005400307943d1030301060022700e0404011341010f100154140c2c5104d0001003002c0c0000310301840042561120300000d01048504503041404c0940003c001105110b900000340e0744c100b01d161241c03458029039490075540204a941111601250180c01d0102c1964150403283c140d03001101c1000c1d81594030802500c143c045032a0041c03a0200000c002c00c4000e40c0780c4051980070b04802c01d48000001040000f81c204501205220007040700450f091081c42034058096510038994280b121089005400051700b107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 249047113 1250 249045863 249045893
    0xe040236030109030e24040303020c090a2304020103180804032d03110703021003021b0105090c12010b121501080109020d060902011202030a0902040f0c0503011511070b091309 77
    0x903102949003400d03c2c80078003444101c810001401c42c0d11f403901e0b454000c1d103507106034444c0d42c4180c1d9800c1c0413654000750b9104080c0c2e45070102c0105096459000c21401c2003080040041c0c1c14543e03101c4c40c242020107004103c1a1a034801c003070302a074843c21450301e62240401c0a40e46255849140c10980000c1001c00e440343c42a5014102401165400c4804c1c603d803912a400c001d4109007582240c8060700d805802402c8071000d07100d00151100b040b041380500302e440403107100e04030b980568180c1e540c0c1e040010030592804040c0c070000c500101100701064441e4ac8080450055500c046050050306100035491409480c6040083c0071034801c41c0c00040b0882c541130000f40c03400c1c1d1b40b02c440f0340441e80541c10010705290400810340d224a090358101e0300070608554164012410b00c00340c0f00314840188500b0b60425101e8450b54150303404d103409601101026101d00040c8a44921804004107040000c0c0008021003c503582e655500340043c403010a128031502c1195906001000303000400c0700c0daa440078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 249048363 1250 249047113 249047119
    0x1110c0a020607050304090c1d1e01050906040815090f0c030a060203071701090204080c0612010306090c030611040617190c020a020d06050609100e070e040236030109030e 75
    0xc0d115107007455030440c4687d074400c1600c00d2030400c140b03103215085120b0075010b00da030b04103001d11000c08070244082c110040c1c003a5071130300304007882c0c60910350700a0019003110500034010504064840d4011480c1402d5811400c0b90003030504200309030000104801104038181e0384c06000b41e01e03030b1000440d644020114000749441c0c0c001c80082c0515109640c03002a15440127003e2404d943d541c5c046400940c0180202c45c0940105101c101c058100b5400b1111460120b0358180c003161700e56141d010050000c100b003120b040b01e256200101041c46409000c0c0703003a1401c403c0c1996140761000180030202c6c8159407010303e003002700070805549404e51846422900072000030030030b2a5418070807418041880c0c0000e5001d0714040c20744c4103204103036010a20070b103001d03030340b5074141e4071380e6440c01c41e000c0c1140c03140a0901c0c0d441000501828464880410a100d000d4805070400c1c0d08030101001203c640042c8a8208100c2c0e40c0c1400b032011089041009540709400030403402410381c80003400f0306440c09101380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 249049613 1250 249048363 249048367
    0xf0518030711100e10080403020f010b030604110303040320090709030308041104110a020a06110309071719110901060302160201030e10020a050c010501052e0c0c150201110c0a0206 79
    0x50b20342c021404c40b50074420061000310400d005107400b400c0c4200030342d41500144581880f2204c016014440c034808200002d0007401147d40d15034500040d0429070b4a030913050b000a1000000140711703006d0031005641d074084400c400d0030160080c4050f44030300400c0c1d1030400c41003807820400f103900401c0054002e030304035641e1034500200d000480c000c1c0007454180540d1420024039200010741c08600c1c0c4189074800c62050160304c080d6082200c0a0109562100032600070301c1c0100941e40100700706602250240040d00c1061310990440e41400700380741000d49071243e00900c8200c991070101c5069001d072160b401d046060007504c0900000301000800006e042c50b6540c5c410005840003080210070030412640103641e100c006600051482c1c0008524090035802c00002040c40c1c5000036440150611074040341010314030010b0740c03681e44c103182c1e640c01060100409040011582801041020b000780d00c585a6505108070002400c540d02c6640074910000c0a10041200c90004503016000300d8046403066 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 249050863 1250 249049613 249049639
    0x3020405090a021c02010207120206041e0e0c0a020f2a030c0301090f120c0201050a1d0301090303020306100305060a05210102161202030c060c030a020408010f0518030711 75
    0x1e881e00c0e8004201a60194400c000326900380b1041058034030952003a030a96640341d554613503072030031407200410007907100c0c44c107010522154007950071124202c000001da00030100d94a1440c505031820079240140150b030005146818550100003205105000e403004100890070340d00c000420301e140514258801c0308c800b5101c102580c0401002c480c8040c010001c00410505151180f83c0c01c1000c101210540000110401d0a070f0084032412070306601a19801d26140002c0421201c0c145501e60084034000319202c1e8a4058a092199140c602c2c4aa100142d0b00e0900004000074458584082d4080504160070401c040d11102000c2d002c4410581c1c00002d04110242001c01040c0d0030123010545601c0860342e40507030200922070340d1f1500e0103180030040c2c80c540703040105d0b10303071045444084c40c550020001c070790110078075401540e004842c01801400c00ba12000c0060a495002c1750365038040749c883d07061040c0d60300d0380b9680c15207c610000c025854100700d0383c0c4458280031414031107032240b0403c01b110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 249052113 1250 249050863 249050881
    0x15090c031c020a0c0f090b01050307020c0402160b070305011a2d090618010f05090306070f111609060f060c060203061306151205010f051909062405090a03020405 71
    0x141460311340c0841e906035607070b0b2a0154a40980210701c5a4514681880d1300040c0c02d5014800316401440658054000b910b10311051101075806881e00c030414508001d500c40101d0502d9440c103026800c1650041000c0d4508030b00008a0044850f080c440e0010411900043e0340d2410f03084469401b8019142000001c4600c0203a8107000b1611043c0d000400001d9180c0907040c1000180701001098807614101c415001e8111600d014021101e5015031118021a80207401441c07018042c3c1d40703520f407890f00740301c075084201d041c40a0b0140001903900e034043c5c14000c40ad198090341d00904100300041000903d445001000032102c4034024011550000118880303803109481c0740c01c1703403001400904c42c8076913802d12190000c50361989040002c10641c000358404015004990490f1081c0010903a6075062404100e417880300004000d05504151000088080040c0589000ae1540e4003080d00c00368459644001340002803a41300d806c01c801001485125074488114000f9203405031000a0195182d00d07607 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 249053363 1250 249052113 249052123
    0x1140a051e03030304050708120a0503270d050a0e120d0f020705060f181f030c0309050106080604140106030b13060209181b0f03070807180815090c031c02 68
    0x70341d03416000c0007080005026002940d08201c48a2074112010700c3d0030140081514065281c07907400140d800c00201c0d500704502054902005da140100400c8600c150148030b203003034540090207001c12008900c400343c16030080c00c90f03100400d0680b13030b48100e417544561290300c8691300f5071040140518075806081d030a100300010300103070030041c0802d035890035450f5007900356800c0000c0342920441e082540c60001e09203016844030aa8901c540103540d0a107841094000d051a00040820161344103c0000400c200b405202c004020910203800d41e820b243c2000e040d0010010410589681000420000102c140c00c00caa40114a18901e24130300002e490020040e1241e54180369103d250284001d8420303181e40703030080c0034050b4030029104452940900e0f8510340035640421129020a000183c1c40d24016101d0990000282c509081d180320341c2c410141d000b1829800c1000d00342c0c000030241d60814040c2c09015004005e0100500c42d9101c2000000d075100d06071244940540350044500b81102d0003005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 249054613 1250 249053363 249053419
    0x1103010c032703170405030403110d2411030f10080a030c03030b010c120f09090c020a061112040c08100614131d0f0d0503070c1103071a0702030601140a05 68
    0x244c2c0d400e05040c2086030303407074015000a0f1443c504241d4071100c58070b00001403034100313944411144030f00c0f02034200c0c07a0840b0150081a50341319031140b40b10078000b01a400158410044045079103041e04201290b90301c111090340203070142c2c1d400b074107200000c0b0b504561401c20559051801054941c0000012140e156980b039006084280d500101d503210b98021a03501c0f012111036a900c9125941c40c0a51402d44070711204074005030300144080c101040d05504200380202510646030314240380340b004a41d4010302110309031544512803e0602009000388003070b000303190f409001800783d10300b0b00756889001652648001c0c400c5102c100c00019940064018000e030110616810a01140e213448860310b0b01d0050b541c070101805040700c0302908034010015a8007a4150390b0700d070700c0980f00d1569803c400040520b0090b038184643c100024510250b00c030403802c81144020229151a05807040c140f5000c01030700b1007600e642c00c00e41e4034159030301c400201004982003115034550200181880701035a000c012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 249055863 1250 249054613 249054647
    0x90309090c0d050603030a0507031b05031b150f01090209040b031015050a060f200102030106050406030b09070e0607060f1a0112021204080d0b0d1103010c032703 71
    0x54108000e281c0040040c00703041001c0c0c0401e121941e500010151284206200400031440500c81c84000c24400c911400402041d00b0880340201c1e0640c0f607180c5142c200c443c03030310b101440d004080450701c02c081c010344c91440d01d5217520039564240b00f190071001c0705050141c04112640851640b44a50352500071070722074a400390035120b1003004004024081c1402003060306024205900006990508030b100c0e0080b00d8503951200a00481c01508481c000b880303421501c0c100c3c416000683d2400002e100460081c243c6880c0c245e0b03698604603002c3d0954000007001481140284204100d50f90082c0c603113038070110215a00e0b40d40300d04a00c0d0020043c01845803540c0920703d403600da9180e4000c0361254000c80102600c0305800034842d144904142c0c4523907210313204689068004900050050400b40c4401035280001050403410390b8003060b00d102c1460015100050003c20311400c5003020311425014108500d420302280c10140b000c05003045084d900c0c0950480180491400e042c401c01c94002c1d06131401d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 249057113 1250 249055863 249055879
    0x12020c090c0a0e0105090a030b070917010c12090c0605030703020f0c0303180a170a05040e0a060306060504090b060609030708060705030901051005032e0e0f0607020304050a030b090309 81
    0x203081c103038a5a0400010318002c03880c01000948150301440c242d0303846140040801513460704583d40d4808078580641501f0501158410108602004007401941c0344034176400001c42c1803c40000520b26090042c0042416146c001c002c0c0202d900710f0200000c0c2d6540e030800d20355a80300e6541c100e0084c85503402ca171101000100c0c80d0b500000340880194000c01c60340090708012900ea18540d0346a60360f2010003440500c50032103d0340146002d01c003600050b070482c1070441c01c29650307a040804841c8200c40c4045416039070031085c4100555841004098001a602080104101d684d1800343c41c2e0040d000324481d131000b1441c808a075504000340c0000c0d1405000380e4607142841240504550420b489107000f41d428100040c00200031000d002040b25001001041e100180c072140603540c0e4060400f221405040e1060710042550a0040d030001c551020002c0c101c90f0880d01d0060b090400c060075110031500100402c11056545076000b00c02d481e0014607000c03940d11012140c928503c102c6180075008005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 249058363 1250 249057113 249057121
    0xf02120706020c0105070302031003061a0904030206182109040207021c0b0105030a030914040609111b0d05033904050f04050603030a3e0706030903090312020c09 71
    0x705801600307041415038001e000548480f4020350582c0401c65190b11310b10000f4a04201040c026080702c2c60b920311a13110840c106c40e0180100f291003904450139000340e0b02900501003203801245d990a503141444000d4000b008079569440401489500003080c000404240010160b94035811610942d40c014a02040345004503141c507016195800196029120080001114100030411825480c2e01d83c0e1b45207081800d1440d00e20500c840d402915420540c0d4900215100d2018425080540340360100c1079290030034007480240c1c003a65072100c9a1280c02c445c2e185240c1c15041800d40703411070782075150304507503010040120580b0a000036031074150b01c00e6007420040f20401000140180c410682c0c03484d5030600c0c08810320003079a50030b0f52200c3d095401000540c542a22a80d0000d14406452580c5084410b51034090340083c560401910030464404581c889034407802c0054100508140c1410701c0704606980b0060490061484081c0001e20381c070103205050b40c802d20591203030b40e42c02031000c1443c3c24 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 249059613 1250 249058363 249058373
    0x60120010f1506170601050a0e120c10181a22090b0102060415051f03081801020706090e04141b03060c13030609030c02060a0206060301051e04030f021207 68
    0xb1245802c002580b01d081012840304c0c85100081d2141580503c08801a150301e8011076840d8088014a020400710720216070040d03685072200202c4200c0200207140d0341c0710403001c020b1543c1c07466a46005000782d6458100420340c60013400d80480d0750031b40c2c140345101003c0c50f9100b51480707032000e02d090100d08204507484081d0810301d510156640b00d01c0802100c0007610059030340303078025580900241400e150940b0303100c5d05a0016684003c940423501140304000c06020f000581c10740080b0744858001c42d42d1040d0081107482940c448030b003407000b040307524a012009408910540109001440620000741c280700185c0803042003c200e88040754000c0401141c600400c0b0302420105209004070b5001c2404204030b401551000710600712108021403030750b5208402040380d14012020320207203155801c05a03a801d0041c0030542826000780c0401d141681c01c0608444008041040d089480d064000303c070000c005107140d2203035041c200094040038200003603143c1440754210110355500003030b80c001084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 249060863 1250 249059613 249059621
    0x1053006071206030b0621070b121e19141305120f0a0518090112050f071202010809010e0304080718091101120209040f050f13030503060120010f 64
    0x1d41e60781d5980c44011502d916540c1600d8451002802c1080d641001c1541e51030004a0b84d074400361954261007215203410103041c18618141c0c04182400381c0403d20701242411075950981c0f000312a0205c03848000001490320310b1603000390820070360560007020a050900d441d4003081c904c00c0622029840741c81c220140c1d004d0004400c0040356680a140d4000308404980010b9546000401681c5030411607002802c0b41c540c1c0162450303260703001210141240507200c41c080107029000013200906414454240070349030084044402c3e045901180c0c0401c60b07610300d0105252100d509191407000c1e41c584900310703405000102901042400005030000c0c04032800a451002c81e0400d24600c40d00c070341d42c1c203001d108407042d08502070b00c0072003841d146c80e072198032881d46500204070034a0014203141c2524013040495007240a205074a5543d1014444500d5040c010542d01402d040c002a0ba18107403650010903600003c0c102506002240d100d00381101300959040429070007a1008019070b0000c407010001030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 249062113 1250 249060863 249060871
    0x80f130c090903320a0302130803040302101d280e070f020715080405070b03130215071a060a0e0901020921071a07060f051b0c0601053006 61
    0x10860694404014404501991502c1c0c2c3c4186070139040f601e1806259070880d440848000c2c201a82000240301d0402c2d80030f11080604081c0c030045884500758030500c01030340c80315140e140600110b04a40b02c2005036115180241c440195440240048010b411807054880048102003d058990380841c8160b20000060302c1841e107650780703903005401c10701c0c183d80b074200ba40a1002940502403600032900d000d48001508a48075a04561a01e030b611380002006070030a4400c0908480d5101b0004258038104071104101e01d94240c0d024540142c0d590362804511180c5949030304048031400140980d80c0e10480c09000b4031756600c0901c024508003032410300070b43c040c03503205100d00c204400d0103001d820201040307070300e020703a02d0f004200480c24414003801c01c11520700507107412103040000c10001035840c0654160b2209004001c2200e0502e220007001150201c0c0a0322841802130001c0b0307080382ca00140e50707070441d403064401c44a19030f020750284d044804c07040c0030340c0c00380c0704003580d01c5000c20b000194042c46 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 249063363 1250 249062113 249062117
    0x20703110d17010902070203031917040f060614060316020102090604032901080d030207020a05060403060e060702030a020717070306051f0e060105040302101809021b030a080f130c090903 82
    0x100384e0f21200400d00301d01600078040d40541c4140603e100040c000c0c0403064002e1068103100442400711481711400721402c40c0c1c01c4404208007410301c0100005801007101030b01462640150072803c00c000700300c80c0c0c00014810422130800380100c1000c14003c1d8111b800c00c4c680030b000c240e912a103a050213501036518908113951060000b41201d90700141510f40c50596a40c0c00103402c807003407002012400f9411480043e40c1c05980c0741400240c56950100500046116142c0420600c50f10801c8030308000004080e0019074208000109403c1d60101d01e03d4144e40203440410b0f403214440d08610700e0224690802000c07540381c0703001d00036152103401259580c2030b00c03003400c0b4194584460050140060a5071083e0101c0c10900c028001031034580840d9101d0b8481d40303040480c50201d001d80401030040da6200611050740050492202c0580850b040d4107144844003c2d840c100220174001c10714200202640e011901d0b51010565603080c4256072450190031260550080d52559000b200905c3daa10080300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 249064613 1250 249063363 249063407
    0x1406130e012d06050603040b0a1b030e0d0f0206070c0c090906140703020f0702060306120109060e0c030705060a0f02030d0207080a030b0d050a03110a020d12140c070603020703110d 79
    0x840000602640013682c01c082c080c1c90560702c55654065603007102500c076242841d2101d0302000c0070001d40c01b0702600c0341c10694012034203510300c811181c00d00706032026500402500314103c14800d82c000030000d41003105450402c94200c018140010311100c2e1381c000210060400c94120b0900096030030240120a034014508030355140d01c08140c08034800d003030221900c1c0c04144040400740c0b9003e0042c59001d140030b13044000700d480c1400340c0d500712548101c2c11203825540392807003c540001000102d02c400400d40041842c54186000039010b0300401c0564001c0209044980071200d01c20710584105042c8004199103400ca20302d03190225070003440a601c0000e181c2039281c2c0d440d1600300340c5064007540082c00340c50210710302c0d2001c4405803208052083d00348030b02c1c1900c000684500743d45c0080d850242005001c1080b2030800140b913007010f900070a200107000d0010303400425010540c1002c0311100d003070059880e2500d00e0142c0705032002618070a85809424019000d098000b00e22031220003082641003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 249065863 1250 249064613 249064691
    0x3040308011d06010c0201030e060a0e120901050f0307110703030906020c04090f030e030309150705010c020d12200a0806040e0706022116030903050d031406130e01 72
    0x1100800402d40802c010508070804200326500078441c0c07444040c018980800e5245400c410b003442d04500303a5030403100c01d1f43e80c42901c1d003500061200001e840303000d51b01c3c0c51502030700030002821401107152020207580e00102044005007d400e078078843c1c5240c0019104010f6490901501c40f89440c0315440140c050a41e2400d403620b0148111401c080e07014000000c682e040f0340f0b00700d88020545011981521080011000941d01c03940940a200c07600c201056441026180a9003501d4042c039016055501c003910408056420480200041d4101c07000007420f00d028040e003031417201b00c0c4c021442a507a07001540c0010346134011001446003909071800d1006144809069595581510803403005070001e45480c0c20342c0324810142031111085031001c42c1850102e000c030a80161a000301100410469101081000014804010356680364141044600c04c8440480010b5000400440c41001524543d4a5400c040c1e4030000c11070464800030440301c0780b8001d18042000780d07420001c0f0b810503414501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 249067113 1250 249065863 249065879
    0xb070b0601030915020c07090f020a030e01060608040f0501060b07080301031a01081209030a060609091a240111070806011403010515060f0c0307061e090f200301110304030801 77
    0x401c00244c0d002000391200388030700010b28020341054400f0b46090083c0c660010310082140220807240c2c0180d103005030b6405030f80c0c902408885807921074040590522500704002c85c1c02100c180d81c4aa0042111400d0f6486803400600410315030700400207190020130340c0810300070a1005141607130b1092141002e203140c2c042c02200c215209101e450f505038040820b0307105291001d0b001c0c1050782d4001c0e01319050118a69961382c251807054000c804183c3d501c00c058424070211a182440d50200a80c400c0307843d041c1942c01c0328108440c1e21880f1030343c4c000c165429406910800c04400c612018000b540c001c0d41e03c0d540b000d45c45031800e2194507451072010303482e42003c0c541071240902070481c005d1800c0c6802c13000024030501e0342020000b11030f04031003440700240c00e076020310081003500d04c12400001c1801c44941800b209550462000385002d142c144410000351f0507a420413201e0b6000390300c0040c0c1031454918050300d09910780c0710580650800c0100f8400081c1c09000c0c50245201e6201c08445a80390004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 249068363 1250 249067113 249067121
    0xd03050a120207030e130536031216180b0f0405040207060605040e24041e0302033f061c0302071d060102060c03040f06050f04050d0801150302091206010b070b060103 73
    0x100e140402440078808d40d100e60340d10001c481c0b480040114140f2141c2c0050b07618250b07004506408820a028000c21000880b41510120a14024144600240c2650030703543c82502c1d4501a0701075810380068203c50010500003920000c0100600541d41c072440b902d0180b0180407584200350156052240c0111082c5003c2450603a50f01021580b168881002d1981c100340382003e48203a403080a91047c030301003000c0064048410724029001141c3e41d0513804104a2002094244101c0300500342e01a103054041c9a000c00d0740d00b5190b40c1c40c585194850304001381140044011300710380d01d158031040500301a008116042114071451803034500d003c0091010180c07147c01c80d00c981c0183c05c04800501000d210304003440d04180075960711b12111005988903022100c1c00c0d00c0c1807a8000f0f40350108801c00104002301c402903541032500c60110351420743c5540c0c1800000640000f49031300440c0180003512034200d81591300b041242222002c0d65100c000180c0c035072001e081030f01c8030062200010010b500a005d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 249069613 1250 249068363 249068371
    0xa03060602010c0e060711180f0f040c06080a0b060d14010f0b0301052e030515010c030905061803071d0901020405090402060325020c0406090b0d03050a120207030e1305 74
    0x48052020020314208240740e0f00c10700e000c031f403050526012400309468022140324509a82c003850040380c1000540201d943d0401809840005080e0041000140b90000350703a04446090400b090030391101c030941c3d00601805500c154000c0000f14002c006040c564100685070000c02d8040211640c030385103d24501e003918014030a5059003040100054186042c00000c0110091600e0040074200c0304040e0b240d219542480001944030400d01504620010406822020900b0090040c09083e0303005003a40c04c2c82d2045500c1203a000c110b2000500a240c43c0328100c00c0010700303494010343c5810244040c2d5140a00fa03003145504000080d5203610140f007210700703442004240e440d072540c42c0e5082004a03400103084004c003800352981d81b0060800c0c150f84034125100c80c0c0262042c1d644410901c000c44081e5800400b041d407c10103a101da40d00d401c0344031020ae5401d0300d44141c1c0c6010301c0e04151a0303d0200c0c03c1d0003450901c001200e005040c2d000d418400760100c01c0b20310003a5000906015000d661041d2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 249070863 1250 249069613 249069617
    0x40203010305120306060d0f060302040506010e010816020f030309010f060807060206010510031416080a090b04020f0103090c060c0236040c0f031a0901090b1305030d0f020a03060602010c 82
    0x400101c3c1020192030107190310440c001d240a01c1c00c1c410f85041000d0701c42e00c0d10013010b8961906010710441c80c0c24000c55610490a29140540005210008045c41000780c4000020f0100c0345444038032900c00d1047c025985101d0381185d55030f0620155080c001c10403040e1080c03a05242200101c0c50f02008195001150000e81c000c0245908040400807103101210400c07060640e10790701d01d0701c501c00000019120f5849040d1110300420446405000c00700300403c0240c40340c3c603100c8050001070b0401d65544d0001e4042d17680c20450224180160b00038550b00d100038120f10303c50b007800180c440e8480700035a031441c03090b1661a050a1007048006541a6007140404e90103184c0a00e0090607043c900210740c024019841451100d645082450020480740c1041c0c40514401d010004c0c4100180c00e12900414140c008211251440c0c880c1c0d190000c0141241002c10080045030042c840b0800940b4031001a03a0b404000100b00d0600a070700a620503c0003401003806c02c44001003c5006100310030820001e6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 249072113 1250 249070863 249070873
    0x3040602070915151707090b04030b0a1d06101a0d02070303140c0d0e06070c0305030a061d0f0a1118120307080405190506090d11030a03120b040203010305 68
    0x2002c0040070b480c41d00711809005000c00000510310305055010b0604000035102e10b28064211102c241d00c00f80010070910500c21040d00400080c81c06000700d0b011660060b00c0b044440e01c0308501d441c042c3c10450030000c1d0b60800d054000755000c10101d280c1c3d000365211080c0d0b40515940746410b42c91307c0f17015068080a8403007402841d45421880c0c009044480c400e150000c1c034070704c078840820010300c025148208040d80120300c1003018513240c17051145012002000304850f01c0c000e0070041c552801c04038002c0400c18044040798141d0741c0c0c2c1d0010f8010b48a020001d05500110b07402e001a0100700300d54a4a6440220000c2080000d15201c0c0d00b50040c00751038107900c0c00c25401014080070940c905504c1d0402210119007c00020901c090a441440f070107010740d03102d151030100101d8070503100f8800740c1c1c4640940d00b084955200d000321081303a10141c605c218401c0060038521080c000c000c003c02c0d0107001d0b0380d02005c1011f0f0f00c8004030a68103041c0304204035002c00f40003840101c0c0130900008000e039200c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 249073363 1250 249072113 249072119
    0x2091801060f140a0e12010c120c03152903010b0a0813020307171e030309241506280318030806190f090c1403070c1410090f060e0304060207 62
    0x17240c034126040e018003520b4100c0052049a01500311824640300000144c1030f20f140703841441c0d8034040d528070a0f1841c0f4050042c1112515040d4910140e445050044500942c1c1080384101c01550000c0b4401140809c0da16503a5500180b041030f401050700c18001811500003c1c501ea900151303600d42d0030b801500404240c0e080c001d500d640710020b07032610700480c4502c01c42450f0103075001d071440c01e14041c50800703103880f410903190040c501141e40e4003c003462a20006120995051100b265030300a01501c00c042e000520580851060300c24100c6c0d800032150260b07801c280500100b400901c076181c541c1d40800407200d003c00c2c080100701c0038400080029642e10045081c40c40cac52035a6080c12030a118000316925940c40c3c142c41c2c41e10895101c5481c4a1b1a501d0721650f1640005031403076041500c041d0180b4600e0220030091034840c101030000c214034440d030380c2244013103c108080400041c890034100980e04041c1086007540d9409542101c001c1c2c00c140308c512010348040203403000c449490300148602e9003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 249074613 1250 249073363 249073367
    0xf03050c03070809030d0903110709090b0a0f0f0204080607110303070f0c020f0301061508092b0e06132c0609070215040305120a060b0a030b0402091801060f140a 71
    0x75019044ca46a4807040c461401c01e00464801d0b84592446526100031202d031355003840b030401c03060768400f0f04000d1420a00e0000f05441c0c010aa910080030343d000120881d20708405001072007803e5004036028804103021442c02c00000e1101d0040404d03841d0000782d400b101d80031381d64038802100c0440002c1c0c5101903200c0c215000e074030303d40b10151005008045064452000c41e003100d5a0394080c0f64246210071400b01000d40128003642c00441640292058007050081d81c03181e83c060703052440340d0391482204690440d01c50b2040ca680c030000100301039640c40031641d09159034801ca0040844100c18000c0101d0104c0705041440c0807007159503038500c510350f5400104401c00c1001401c0c0400c0d4040d000800da00c610072081180c3c1718600c03e8039443d0300c0d20121440c90003a110010400fa0000c0d00e0320005000c01b1415078142c0e40625168078011620b54501c502060180c01031003c40ba4010b40502e50081170060040e9516058480796070754074041c0e0344802022a6016a1102045907802c400c12502003554 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 249075863 1250 249074613 249074627
    0x61003050d05070804030602032e05090601080901020d15140a050d02010c170d0f0606080f0402040c0203040e091c02060f01180608031206030f0a02090109150b0f04060f03050c0307 79
    0x600034140141171550f251900b00680e40b00701c0d80041c1d4885166444d0352212581406016861403c0b0b41040203981814003260345848054141030500580300300240800300250103d0741c485940490600640394032510f10010390303550303000303251088038201c045a046040a000100c202c1d040207116004900c52900103540440b10080c040d0340d604140120300948603021801880000c05011001880c030500c10f40c1d83e401c50700b00303400420401181e00140302c5400741c5800b500750003640480d0000b41340300064100703a10b91310985d400300700100503203000c003c1c0709a804103030b40c6418090301c0282c0d03441541c0020102e0301d86c8821120b024003410030074014004c00c02d00c4005100c0e80307420114005110303500c880e121495900156031054408031440d04014042c10203012641c8812402d000030081c6c001d2650000301c501805004000007c1d54601301100f0100351807000380020000c10703600075545d680d006111180d5a016014040208064480364148103110784211849504610962401c0d40c44001c001c031450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 249077113 1250 249075863 249075877
    0x1081b180d0503030103030806040b040e0c0405070e031e010606081b07110a12060605121e0c090c0406020606060f070b04020a0512010608011404050717032a061003050d05 75
    0x64001014000140c0b00308021030195000e07482c0d108591800c0340c02c00007526414010140203e00b400700151440a0004000c003481104440206640c0c0c0d40840c11074403200300700e08155061080c0c0610003401c0601003164108181513070f00a0041301c2d2204d60645a5000507103442c441204588000b55084060801402100744074400d413003078100f400000150340c4210307500142d0620b0840c0480e03404000c058130545c1c00900042d80c2001403c003142c82110b0311403030f20f090036002d00383c2519400404c030307a004d020741c1140e8840181004814140b000d40c41815400a00400740503108142c04900d4034944401500e0988001c4104c035481c01c9a07a0762002c4800401801c1241c00c0780c200040428903544520300d1824000da48000050300504d400400c50a44a44d59992541c400c40c2d9000d000214402080803001c1d05e982d0f0181d10300310b2500b01c40303c0b1f241d03200e11003844150500c061240c0440e0085103404080400f10300c4110380154507004450a080d000b6403200910f10380c00710180c1c80310300b0300400280c00c00d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 249078363 1250 249077113 249077119
    0x40204240302210108010c030902030c130905030313030f03140711010b03010603052107020603060f0a08100c48050313050a060503130b0402150a030b01081b18 70
    0x1001200c9520000c0d001141c0310600f4100040f80050006610911440c0d11900e19071800303104038501600402e4032440c03909071890041281000c2103024044d2508940d8400707074484116135803441c0030b0224283c07220003d841100059100c40564404920a004015a03540e600c0381c0c03e20b941d02d03905000d8804820b004118240707035480e100c03802e00340d9400307104100040d4000c00203828442e12055500414001c0c0040f07055602c002030201d000036841d400141c990000081c0c80101d0900d04a00000d89803249561040c0b100e881001d1400c0d1259038560840350260f61181c80c2c07641c1e9407a800c0c00340b44040204a403036004125070b628101500c1f403030b44203520403852150510340d105201513855490441e4406024114200c895000030800c078103042e2088801000309181c02030541c00d00c500101540c40c0400000740c49610a440481c0c15540c0e058001c0c0c2d14444d0380d01030143d42e0104814081c0103443d00229082c04540300000244482100ca041001481c84101046242c03c0d5060300020400c800c8140b0550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 249079613 1250 249078363 249078367
    0x80606040605042c1602012f090f130e06130b040201030c090807030317090a0201021207020a2c0601260c1201060512010801200a1e05090f040204240302 67
    0x13442007240b0400b50300825204c2d0b1900311000003000c010f401d590031044010082e03084191190314880c0d250800520400140c03080b642d880c00d8050000d0039003908015002d50000380380c4c5c218061604154059611210707114155401070740c5e2080c45000940543c000903040c0c0a49000140c01584658009091b4a00354204008241d4860f40030514000003600101c0200c1c6403401d8035400d411088450f5584852603600030300402c40d940d80000e448a042d1100c80d212180f000c1440c404660302d00344100060410f18540e9071a60380c1e080d420068001d8005010800794030280702140e080d511034081107103004410f11081038910ba551942134082ca00003400424041d80c00d100135191962196141402041d55649a03503d90f810065007400e0360320b040e4010021a80b5100586040c05121234090302c114007800d03d07654813a00c1000d0103560681c1c00801c258840c0900300d80314402d07182c05c0b00240c00507070300948440c0a640910014442280b055001d03d83c940b0b0020304c400d0031800404a40f003c2c2000a81c50054 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 249080863 1250 249079613 249079679
    0x6070e0a05090723041401020606120a03180806101d0403051615020721050a0f05180312220f03170c0f06012d1806170d08060604060504 60
    0xb411600f01b0b810400724510102440c05407580c1c10014031360444000c980b240660a41020a5652070140781001000e2017030301c944584440d943c4041480042c800b00007541c0440c500310f81e800740769050a020341044e800c0040a0201e1903203448d01d0f0280b050b68992145c9140198400384940c00ca10b440b070007140c81c1e201710b10604815050034005424030364410348280703001001c58102804401c40600c95030301000b00c2800300c40c0c80b5541c04480d28140528604041e13907288500f5042002481003007680c6501403107042e89201803454448020020120101d640e504c5480300c1c2c15800840302140e200d8102282c103508414030204550246418455100c2040c0e281341c80180300b602414414000b8000b01190000303001041001104515103c001c07043c1c601c40d409840809140030800e01c620300401301c1020030000d40e5140280b03179a0200703010301001e045c10641c0e280661a156035892540c401c4800040e284404500a401c0000554003034032501e80302c0070700b8142042101c1390b1030522038205c40c512038140c0d030643e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 249082113 1250 249080863 249080927
    0x80a0f1a01060807111603080d0e010914010c05070305180d02180a06050a0602030409050a090b0115020601060c030507030c08040f0906051311040b0f07020405090d02060601020601050f090405010f05070206070e0a050907 96
    0x701500742d1003155100a00d0dc450081642101d0390a0001410700508200c5640000e41c040c04603400302c10b659000d0401102c2d00c5012a4000500760700007074008050000140b440210000307110709ca10b0103400c0503c0003903214428021081103038420b0f00d0150780280030600c401e80858100303e601c018030700700010340b121564031517190320b44080e4841c1c940b00000004010700641e05100c5103014004a08000c1314520480e0b030010502e1180401c0038007040180300700341701001100d0301118010702c408800d42114a45079510500189214400c09104d100c0e04000059001007038000c0707014026030f140b856030070315180c400c8010340b0340e000c52018244408200312a1005980381d01c10346003e540d5820003040b48440b24a8041c1c40d0000140c500e0b070540d40000c004000030342c0d5001091010303090588900e1000d45581c6009400740110b00f0055080600f0001084403007640058021b20401090752849180c1e000c110074011080124091641c01c01039041c0000d40c024040d218218890140403c0075449106090207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 249083363 1250 249082113 249082121
    0x71106070812100308030a090311060c090405130b0f09010603080d1a0a080c04020f070803010603150f08061b3c0301080a0f1a01060807111603080d0e01 67
    0x2007128650000b1030100d002c03080c041800381d8458540010f241c403050a41d00c4071007035400004c01030040551104a5001054495241c200c2d40e030b17103550100c46542c1000300c100340154000c506818019458030300003542601100c00b000003803a80003280c007801c07500d03003d0f80b03800074203402050360006640710000040015500c10080140300381550b40000c6a02d44e1101d4038103900b1003a413450f481107549000a110312a4085200960b11004581c01691100c11100346101030061140c003a00300c400c003100004415405400c2600b03510340b4501c00a070a581c030ba4000e155081c541d0f0003100300d0ba078003000009050300c0300c00b0184521407545031625400d01510103600c0c100303035403160520003226170707020805120200d030f400701500307800050340e0340504560525501541c0c50580e01d10103002d03003000200400c1442003c1c40c409011020a01c09500c03e580c496001411070401681c107280041c1c03218400d55000f41307001c180d40381741011f600700c45d09510385545c03150011508003076a442505036680008404121003486 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 249084613 1250 249083363 249083377
    0x807140c06010e060f030c01050901170103050c01020d48050c09090109030c060f060f091b0305040f02090a0e0f1b01020d1b110d0308091b0a060302071106 68
    0xc080760360500003119580b0902a001c0340c081c480c0144845059980854511701086007031074030300d48904801c80101e4003909901080b400d500c802e10004418440003288a14000e4020780840346800d091110448008038000d800b1407038110b458003602420803c40809035005002c026a400748280b880c00340700b0309016042021256580305449890490506070310344c61348141c605008005c1c0c680780c0d403005050742c80303100002020180c1e01d101e00d010040a80d40100f0241c582d500c5147ca0300760b260b84040004080f94031030140000003484894070141d10902406100e01e82c0711440e40b10048840d400d000000c0e0b8041c00c1d100540e6184c24440c40d8044082000b81314024a00d0b00500c00189180092070654441c00b042c0d5045402080226642c5a0469080c92802440c42c2000c00c102da001c0c240116030300780100c2929484017081074044141544036148a001c3c1c03171010161000454000d00c12850791a1480e4a03a80280003440c2c10005039029501074070806001e0306a12402c0b8812800041e01607101c0e071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 249085863 1250 249084613 249084637
    0x912030a030507140406110109050109050f0c0f0a140f09100f0503010e06060111010e0303010f03020f0a061d0f0301060807030b0a0b030303010909110a09020301082b080714 76
    0x4503001440c55494042e1030303004480c1303040201100c21199a010400e200700c2c0207000610640c0c440410200c14254081e08000b500200200101c410500d8404d4903454582c1c0c503040c15201c1c860308401c0700d18200e0040e1029004c02050101d00750b1801040a4850304980300c020780c0440655408189520b421550345e10501101101440280c00c001c0089100002c130740000740260324000c04041c50741400926280c000c402402c2400d610011041e01901400b480c07a0001401c1c003000c00002015180d03181e00d14162407007141d1200001146a040c0720b000f0496129540005029007a00070710411001030a00b14814090800b94984076000046420342c4e503154070080003544a100200140062026005d03044003603a0001d01900402c3c5000a940b0301041c064941140d540e951500200305600d010400089001b611080c2120782e86d150110094000b4401e88406005150344d0300a040110141c401c00c00c0f607480f60f02c82c000c2c3c50404044448100042010301803221500740c0c507802c2c024200180034400307103030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 249087113 1250 249085863 249085867
    0xc10030f1b022e05060a0b070308060a0501020d020c04020a23070501050c03100b0f071b031103120403060f18062304030e09042d02040c0c0209010e0402010203091203 73
    0x34024a490038941d40c07841c0c104034030010500750034040395001003d01e0320f804000c41c0f1600e40b0b40010b403428002c0c0c2d000203010000042c00b9402c040d003040010303200d83c108a8400c1a01a82d420069895038406046000141c100c1042c0344001d14041d80a04003101301031421003c6060151340071001a0340c81104101e2066020611104201007401941d41c0000030941c940d013181090045290341c94501c0c01000103500022585c5200d40590300d050340d1036190001d01000d0024403080b2080300c1028203020941d014180841d054000741030001d03400400e40c2000d60542c0c03606203561600c400801d80107200740c11298440d51050b40c1d4154040440d40003d014000000306001c959070b5003407108400c0100481003007959420030002c01d0b004001c100445c00300ba0b070400d50a40d183d20b007000000070701010180c904050200c2400f85100307007845c9148854801d460801603d09030241c16502840c0303030b5000a5002507044c00500401c02d8041000f600244107004580c10304128400041001c05024040d81480d800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 249088363 1250 249087113 249087161
    0xf060b07060b1206150d02040c110c0303190e0406080105090d031a060a0509030c0a08072c04030c0302010f0203130203010b040605100c0507050306040804060f050a020c10030f 77
    0xc54410306042003070450b0b12940c4050407454403504d5000041c11200d000e1005441403c8a4444410040145a00400c1001184400c0d1030103023001008124141e41440703a01241079139410000103c03100d5407a07080c85507082103503a0000303e44032481c0405031600581c441307000080d00007007405032900070f003002070180031000e1101a000f01150360464454207441100b4007000380a40b985405c6840342070a40c80c0003655030480c000800c0c41d085203485a590040004180010142404901c10b0b00b070b00c0c040c95585982c0411540300c81003040220001c19507200b1f1b00740201d8002400b907069040a10310900001c58903e00600294049800440b6071040c034a488546480c11454280b1961500c0c840803101004240d0078000801c0c03200601d034160a060240c200c10040c1805020041500184002401c0703035454945840c010007580c00c94811840850844241082047d000d1410349000303035501d50080a02c042260304202c02d8201d045040c105050f546c40d412400f5801c94020b8401000d100110314100c540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 249089613 1250 249088363 249088373
    0x30a1406150109030602030718080304170304081905070305070801150803030f06150c0105090a03110708100c052205011803210215090703030e1f0f030f060b07 70
    0x44000e2580100e04070524080c1d1103030381c00901007015660007000050301d07079480d0b030b10607035464008004030100382c1c3c0c02900003e100900040104166000c01c005500c0d1031000d03c6100e582c4c0e0045014482d00ca42150440311a82c880821900016500400454000c0e40d56611590b0030680c0c503801881d90380c0d4440924001d2441d6145030366008144150003076141d40307010138012910b000c010305000d1140e000c9a21040f00003008905032806e000c24003008201d0b50401ea547e0680c1c0700d1075030f00d0482c0030400304808040c00c03480108141d021905400098025412030400310802000c00c0070104003071100511000a00541a40212041c102180100406030b8100b50024018841003100d003006008040d40910000e19019215101188c5d19251054140180c0b0700c00d81c1011100300503400508a45410440d88460015091048034003e44070000d01e8060303c01406041c884102c903416050a13000d0030404c2c03482c0b040488141440c003500c2d0004025456502000035100d0540c0700c000407030350100b01e003000e100e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 249090863 1250 249089613 249089623
    0x91c0201150e01140f0112140604060b041802070201180e040303050c0c0c01030b060910090e0c0702010804020603040c0302060c03130906030c0302220203010b030106110a11100e030a14 81
    0x500302c0000e000e2989802c4060130003001c3c01c0890350241c008482601c92a900500d90003208a00b401e90510100005403c40c0f400d03050100c6030503202d18100200007030194000c0d4112404c1c0c03042000b5210f0404184443c10b00a5400301c8812030400c240c0f070394902e00d1030100c0021034015100300c490100c80da00703180c04c00504bc0c0b00c028000080d0400100991521841d0000305110300c0202800d000c944a20200009600e6000304034034a0340011036551401c10f419480f840030400d4403440b06400c14162501c5c41c40d0801401014030081c0450420004036000d072402c0d1015540c0301c0c0c828400c4200c1141c030703a80840c0954101459100580d8004200b01e51b00d2049901000f0180203d802d04020041c81e585854844082a1002901a078040b490720030380d80182d8990103107846c507820015540c80d40e40d46528007165000344035400005191025203400320300046400c14029800040407010f8004040801c20b005100e00d1845082c070644406040c4940c07410300c0711a030054001c09100d4900381e41014464200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 249092113 1250 249090863 249090869
    0x40f140105090c10030204080d08180a0b0601120f090602030a0e1b0603100f080304050109050306060109170a0f0b0a050606070c0b030604020708160204110f070b091c020115 76
    0x59062100b00610b0400c0010032203002e03901112001200c0d40824015002449543c01c502e080340140c00b8250081a0891b01c000d0140c04401c3e00d07110307104c8143c1441525242031801c000c00f4045040046181c940c4900a49666201c010800007958200410708000b2a011100c00b00c415a80110810030ba10b40ea44c46411440c540080c05880ca00056151414960640304040d0388150030101c04181c1d5080290103a001400144003200d44882d101c40c3c4450f076039003281c8130b19400030f081c050001c1038134100030a80500406060b1199580141049614141c2c180040d04101451148186000105001c0c1164244e62030080544500e0f50900ca9000d20503614010325040c002c4a080014500044014405a0459440d0f035225a16a2607480009019105600d000362030742c8800706411422a1000c0c507010605032084504001c3c50342c800150046130b000310b00d000c81d14454140001c41c04103600742103255000c8809810713251900111600b001c0c00e600c00303420b02c40041c0e44d91090000c498414102030300207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 249093363 1250 249092113 249092153
    0x40303092901091d07140910080d0e130f050a06060504060206130c12030807020607090807090b151201030c06030516110a08030928080a0507080d0203040f 68
    0x8814454844502466040c0703d4528510368402c5414121518180600c10a0100f9030a9941e00c40c0d4541c101000f880710720315900d12402410001c80d82c10100d200d50002121503400180c140050184016a11484140880ca40007100e8115031800d01c1690302c1990300006900c48000b07854180801e0950468007140c20210501c98200024020281c001400c19440f60f4000856082c0c03070210329107404038010030761003a4014500046140101a084180e241c411100d0354211450b60381d03140e204845141c0c552003480c05980003001c041c002041146c005001c14030019048280c0c0311a42010701301e60f0350005484d80007207484c010041c0100006401420010700d813070314060002d070608450411092407511001c60521613007440510303280b80e05006201000d030b04040500c0c5c076860a8400c15443d985110228030001244004019001c4040413a1910050300444424184581000242c486503c40d401c02e4500010a0006410195207400158860f034411344030390308458020720f45400f0901d114901608 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 249094613 1250 249093363 249093413
    0x60609090302030426010204140102060609101a120a02040e0a2703030e10150803040e07080606070606150311120c030a0f090f030e06040308090402030709090504030309 74
    0x1180c0d0000c192400d90f0928aa0385c00009400b590750700c0d458a0500f610401075001040002d040980c6034540c40070014207070203842150356400200403500c08200e03403003403030750701e0700101840560044000020340ca880c1c101c40ca4030b410410402070180c44422182100107030340001e010701c24400c10030742a64100b0100c02e418003117101c10324020540b0011700081904401c200b039219105144c42074121881416110042d030751961923a03143c003c00340101c0e080700b030004000d4200c0020360000000c01c4078112030701100d0605554940300001c03151000041e0005500c80011700911000c82c84034810352009200704081da1103502d442d20800740503074082c0c03404440602400c0c00000804a002d046d515806008030b036407140c2d41d58400c0606802800d0302c10100440c240f0b02904442040100803001040500940380e0074a054449000c00465201e1400300409c0d10500f03105890030381c1800c1e0040c503003011490406003041030312491104216501190140c0000c2c0d11a4655401d001e2814002c2002185641500c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 249095863 1250 249094613 249094631
    0x5010e01033018050607151508120a090305060106030501140f0d0209190908040e13050d080c37090803040e06191d07020309090f0618010603020403060609 68
    0x2c4055104000300000740846045000c000d88104100d03900030f00401032800c0d803992101c2c1020f50031091240032030100d243c9860000790b068040360118a04403040d64008000c0454903032481100c0f60094007011091008030b40010000810502000307020b0321395507400151941c9001304005130071070001c04203405048250f5400d040340e00d680704240f21007074040d280502a615850804101c01d1100c02c44039a0a903d400c4481c020449038100800446070003425610381d58854a0040d104003051481c010110351010f00c3c6484810300a000c241d60249006400d94104807176540c00080452951210103c4110108103184c00707055041c0291651035683d01c0c0c407010700ea060030502681c87c81035000708600e01c480c000006009968800103150042d01c04021240780c0b5540785090440804401c00e03640f4034100303080014035a51310001c151590040000c2080ca655105c401640d81e40c0b45000c1d05c050382104440111501741c000d1020450300078525135500696591440c1400802c40303500f90002560142005d405d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 249097113 1250 249095863 249095933
    0x101710050604030b091f06030b091203060915030a030801150c050d12020405150a120504020d03080a1401140f030105040c050f010c0b010902070213050402030d11010209030105010e0103 81
    0x203a0192940404451500d0300c0d005c41d054a4010043e92815010711018081d40701e000b5507802041c112441064002076940317401e040662070368802e4480b480d40700c0d000c1c00081c090b03260071030310700d500440304001c1c0344503c0e02090042410404c1d01078040d000b0030751080041120020204002c2a034401e00c6c80c01d404604030580c2c1c0d5548800100c1036000800018503e48150b04c01c40341e04403002401d000700108490240200c403603a89400a54414012907500d18a01c503d48280340100e41c4680c1e402441170f44500d990755010749041801404520400d690354000980110544032168040d216440b500705e8210100410000d48145410314140a41d040c20144000104410000c0068030400c40384070340407003100c80040b1441503103141c002e8180c886220001903d14815401003100c507009881046800079400c400a056a10070341c4c000750154800501c1c2003049100b40c0c0300780403d015460015182403c4000041c1c2036550030303041000d07014240d60040080004442c1d649004480d010240d5900129500c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 249098363 1250 249097113 249097117
    0xc0901020a1203060b0301122a030204020a05090603041b0602030c0a020f03030702060301031209120818061603020606100f0801060f050d050108010b01021b0a140f1017100506 77
    0x8000703854401c040c903485030184c0c100c60040d0100c0307003400303841c0e680d01c0e84a005001c9420320f0988500c6800034901410b0305a500d001042c0000c0031114111003442c6900f4007000750f001c40c0048040080500a4a0155499400550081d4014071000321b248079003a0409466568580c094810b55000304000d9291590214140e80e4003034040700c24003683c0140c80b010a045220b0714000a510400002c000300400c0b01050346040d001150b41e42d90f01c1121384a04281c0f034020a040400b070980c203c00d01060100361108a401e010303519010300505d00780071500324115052084190300310b0150700070104021103420725a4080041e000586084400b0450024001d09082d006004242c1002100c60900c0c0c201c5005804440b802a8117000400482d0303903420307213580240507602d8024014010801c00c001d60001c0301c104043c0d500d41c000d2007500d044d0318002c803450540001a0355290059003103402040503075500c2c6426003001586071a5011000203601c0900700d11280241001a1300c3d80800c0140b016441c1c41d42 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 249099613 1250 249098363 249098383
    0xc0f0318060d06120312061a030a02030601022109151615020f04150206070306031e020a1d0714160b040303020706050411043914160b0c090102 63
    0x100381d6501e034600010b40e005007000e40c205600d88400c0608007010503a010500d107142c03a40300d400030414641c03101182060441d40140c0566030200500100d180341c1240d0b8000d640108050040340c00e148400100d041a4000440503018200404140c20000d0f080403c4a01400501100300502c2d111300342d5000c104402c0ca40001820901d0410004c0124031501e5040b1280281c3d003617401a1165994016003420b5046c4098071801130140c0e00200344110301030300814094980c0312a9a030141c082c15549400c003603c000d80e040c2d070b00c82d407481c00014001e0028054402c224141d04800042481c01e000060501201a00e031035a18501c2080b0b920750b01f02c00b40019800c22580304662140544660400703c001e03005200019040510341014402045504c902e040038805040d181400741d038410444401682c090421a505440b00c4200c030600c0c0c481c07140d041c072107118503030f81851a040c80d03a01d13400725a190801c0062504040c490082c0c20300344005100240e0b80215401940307441c01180701c2c0000c0d12000101c2c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 249100719 1106 249099613 249099619
    0x307030c02150609060a1a0901090f0608070f0e12010f0c0906020c061315020304090f0204030221010b12060414010c02031606060905010305030c0f0318 67
    0x4100025201c1211034241080d50b203c1e020b20001841c001c1500b607221415840228585c40601103012080300b000880340d444604d6400050310b40c0e64280c1005800d0f888958081014a0744030903a60350012840c5001000d408203050181d0b02c4020308110310b50b1283c1170001000c3c4c3c0300e405500011101146402c280180d07691002c00b5a0440d400c0d008090040e0082c0d006901d05080801c000e2030024a41c05160b4010369a071058021409800300c09030005800c0010304000a141c140104460181421000c501e024910f80c00600d00500025007000c8540d801600466584405e601c08400190080c0c5403400140380e0304c0107292940c40c1114200c0d1421441c0c1d00c48105403105116822120400c3d40056140c4010b0300c1d24400b500c03030a040225082030712204c02042e000810302665000b03501c540d00854a03110001d01550400d60607480c0640d0590041c000da1144006005012100c03200c26 = true := by decide +kernel

theorem cover : BRFrame.Cov 248920863 249100719 := by
  have h0 := BRFrame.cov_init 248920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 248920863 ≤ n) (h2 : n < 249100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
