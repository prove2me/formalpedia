-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4326
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:15:38.058727+00:00
-- url     : https://prove2.me/submissions/11320eda-d87f-452f-8651-ccc48fa62810

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 777877697 ≤ n < 778057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 777878947 1250 777877697 777877703
    0x1080a08121f061106060405100b0a050706181e05370b07030b0a05030607051e0403061b210b0307030501020c0a0215030c0307050a1e090504060f080c0607 68
    0x22520980e00720741021a070b20050142681c0d0f038060069100c44003868480081d25151081d4030304414422080950350b102d800b12803042615a882d200c4809080c2c8444c010214050807103800c01d07100322580c0c03504140d5030003807a100e5000012905028541101980507802d00203280e03920000000207001c2c08101c003210a540c0220305142c61070fa2001c044090108040002c4505002c50b03801d01c0601c0350035018100f28000190b509441d40c4d4030f0200002e42d94113000d0a50000e007c00040e246410401ca400824542074040502c196550303075a1034500c00a08007000c0040d1100e54189820001a11814103141c61600c5c00440c1e214629031200004020a00c2e140f03d240c1c584680d10380000050002e0020f00303120a00c1a0282210380030f680103026507101c002e0540c48600d4020401c02942001e440e003607a03041400740c038142d07442c3c1610000c02d56120216643e0325911651031b0f200303200303c90b902c4002003054030029075007030000b1a85d56610201084540c029040da1740c000508800a60034540e0240a01c240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 777880197 1250 777878947 777878971
    0xe011d1522020411071a09030c0c040b1503010f051e0d03080c0919090513080d02220b1908060d170d0606080115020a0201080402010e03010b04020a050a0801080a0812 73
    0x4108246409281d0084d03070100c51500600d10001d81c1b0201852913a079000d031000024602c0c1004011580e91074104003604039100e6640d481c4400d841d500c544c41d145c000c1100c0c100d059996961541d100000505051241e03900c02c0581c2c0d132010340707107a03050f44e08000c880d0f0b4040d05020300840039135402c0d2420000200384c000044401d026a4942e9940c0207104007060082c07001e00c2d410542000803c9040e91001011800002004181d49000501000480761005490180103803034080395141e4104550104100c03d56901300c010011035980344440091140b00c0c00000c602135641c0304d074141500e481c001214110350001c07245030200b0102d40752440040302d16078403000462500ca001c4c000481115816000b103c0081c80780c0c030041c040705080030f01f1550051458001000c0101050380001e24440c00180700a0410071106640641518250000119070400038025910f41c140010004c0032074008240410004450800009149501050301c120f501d030808500340c03800d1071542c04140301c00340c0a042401c00710 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 777881447 1250 777880197 777880211
    0xa03140a12050417070501141c020403060e24011512050106030e0d0c1502210f060a1202060306010c0c2114030c0c12010e011d15220204 60
    0x34001c0d0040d2070030a0259200c95880f81d00f000c1140848a20360302d159503c95101d04070520480e83c200e0702c1c0110070000201d5295881044014001181d0499210410154004540441044000c2e0080f0713112016000880d00d040c08100e5440e1480484d82400040b40032044005020b0506d01000503e915150703401e000c1001001c10315280c041350000da0080e800a56286011034005c942030041c0c08040030949401040c030304198440109030384010081c4420568001503001c41811036050581d11000c10100c144003e00e0300c02c0210500b41e0085841e0ba200b80d50420020034404440600044043e0f0050501815503940b503006484030b40c201c03c0260b0342441000000906600b2500c02c140c103480b01510510528520741c68072070203e0581e121402c01c250814044c602c40510700190307000440f0400c44000848240b488001801010004285080740d400c0ca01d4045e8084022000d040400d0410740c00c64891a03030003200e008401c50b00f0b84000c04412007080a0540848600e100f902250b400100005001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 777882697 1250 777881447 777881453
    0x20d0b09062128110303070c0e100510081b0a0c1e0f030302090f0915190b0a0306030c150f140f07030c0c0515070b0405010b04380a03140a 61
    0x5000c80c560040d20b8500b0380f54081c020028040407003e2041e0050b4011400c0941c107a03070f054900c1025000c0c40e03804c100901c2c0068001300c0201c0c004c00051902900300d621120381800d005044040031a4080c006840d00081510610321300002c0782c85404841d03a5044101e1601d907140606160281240c108168410140340302068200c078850503018400c0c1c5005940d0407d83d428844100c510184252003908014100140d0360355550800180c002e080391503084c68545030501c502240300c0307500440700005000c6001e0715141d170580c0c0084103a90040240c16906503583c24001c3c0440340d420641000980e4116518075414000d0340001141c0c030305545850b08021f40346040e01c5140d04001e2043c0c0010781039420724010f00014515072000380c8000e40c1c0b1840310104011113481c041c480c03940f000b05658010381c00030741449420f501040007440d0041041c4840c00d118002014880303841030310003030a00625012040240d07810316a24880301c0b806001e40342d00f02e1440e00c1d0700300c000001a416030080c2c0200320a0b0000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 777883947 1250 777882697 777882733
    0xa0507140a0c0605043b07140a031401051e090405030f0f040303030e0601050306150a0e010602070e24040209130c051305121213080709020d0b090621 66
    0x1030f140e01e90350b0544943c5403800030300d0780214040040407500c444821000c00f003469040c4d801c00c0380a2036511245a0349540f841201c41c100d590040002d40400402d2040049506801210010212145031940c0da40c8030420019a10007c0503080c0c1c020f029110344c0c03241403c010740500d0340980140d080c1d0342402c0302c0301e245581d19032102001101c8107000190510415815200e000d2092100c131005000d1581400302090343c4003405007900c6940c01d0800ba003602d40da640c0c440f9500c0540001c1c081501e1035656508083e5840b01c00340a641c110301c0303002002883c10f0300c400c00d03e040b555004544080c40030795030f6003d020003035000c486c185070400070440807035003002c0850085802c05032a942d00d0a6841c203814481d02d0188000c0d0300001d01ca00001c440040d0500300010f064503140c0440c1d00c205585000303076142e418140907650b0141c9660f0140b04030000e40c0f8401c6da4060400b100451a05100c2d440021041140e00071003103800c107030b005100314031010040306040004080c0100c030344101e4035000009008040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 777885197 1250 777883947 777883949
    0x5010203090637110c07151e1d010909051305010c030e0c13061703190c02030d031104050a1806050609090a021e03041b05060a0507140a0c 61
    0x48540c05141400410070841284140007882000c0705408030b9030a4426581c0300c4440390f440046103455640032016400900100c5210030042e008454045076501c0c0180a13042d01400d68202042c00d1541c600d400d080c2032a8408800d044540d07480c180d003035030403140804207022010980e040111070207000c17074241941e1003482d0280543c2030903c02008a5440c1140c29202d40c1541241090b081a03038855403204006115a00320400702d1300e860003101b1040a14001b402d00341e02c1300d00e40c5900140340300080840803000b480c04020006151443c8000d0040030345042d40f01c01002905944005006902030340719612140390b40421781c2c000f900d4030342d54900041944155402000b400b034003001400090035210709c41c0b6002404265640c500b00f1420344005020360f400140b50140090b0001001d5403081c101342d40b503c820024040d81c0f0b82c0c41e410a420401000c0d05802004031441c006003502040c0352821005179007410480740e03a00d52610209589603150b8400801102c0500d01c1040e030300400003041c1c0c9010350 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 777886447 1250 777885197 777885211
    0xc0b0c1e1c020f070b070204090614041106031005010e210c031507080402010f11163609020406030c030305030f01060e150c1009060c20030d0b0102030705010203 71
    0x41149281400d4801e0010058420882994000c8070000007101001c6461001c0f500b03688402c503140e5000d800442c024001002d0024201840c0c107800303425550f5090101405603000341e03d041c189140f4641800060f120640e580098880b24141c1000f080d88a103806203a0400c01178442401d99410140340c0c40010b0310300c03aa69020781c000100315a16800c00b0803210b84816841c1d4108585800d103007601500030803002e40083d0421800c02071114259014100000003000c1394000c4440700c00d9140c0e80d03e000172441d4058005101014002407d419010103040c0083e850300c13210054108004914100007419030309012a005622440004089071180f050fa070015406521240d60ba03103050005487c00b090160000414410300034030174101511303200c2180e06c402034011401680c0f40c60420340285041843c0c8142c4038100e040200450800015130442440f484941d20703480c40c035840b5100000d54002e01401e00c032007560300034080509020307c16001f003084800180150707494120207858282c00c1e40e0084402c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 777887697 1250 777886447 777886453
    0x90a0807062601290f030a0b031f0b150c0102090301230f1b0a0c0302060604200d0902100306051c030f0e0303090a0f0302100c0c0b0c1e 60
    0x822140307030404100c4a112400c4451007218210b6509000003509060080d25814104010184c01e408030502c40381900750360844450b900d41408a8200e8040c2c0d00484190700110304000002c00d003410700249034000d084010340d44108203445100791100900201903556401600122680180030001d4001c1102022420025030fa850705002858291501189072181401446404039a41c4080885845e0040c855240d0094543c072100c00780b0802c0035030003800c0c1007028000070303103441030301e4001804000040c0f20342c00391555603681c40d04200444030000c0d021078034174550402d4084072100b0200146098010308100003084006600480e000086036480355010030350304c03001070045241c0712600d219440c240e004d10034940c11180d40d00800c0300c09a01c50150070721400c820543c0f02039406000b41c801640300940100d43c0b01d60b0f80c0a244101c90003078442a0301624a40c42121000d03445040e03502d003da600071145840c02c600d030001c203c41680c00344c0c2241c002d500441d00c0794101003d05811000c1240c030f502c001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 777888947 1250 777887697 777887699
    0x7210606090e090d021506060415110d0302040b041a07081201080120120901090210020d0e0d0f02100e040501090902130c080105041104080102030103050f060a0603020306060f0402090a0807 83
    0x20103102d500c0007034100362865100140441d90385900007442d40d41d590056a1200080c0c4980010900328000c1c0d4000040c6001e842500c000215408a006078140803503d00b1500150000b01c000d50482c0700c1d80c003942c3c0c0645405c00040c4510029542e40035100c003008203925183c50f000d074860780a00e8008020b901c18100400d40104802d1009004104125003070130344800c0140c204130024450f500c00c0e0122041040090000200680029403021b00300c0b80e0081c005107520919204020344030221800403801013080d00c0c4c660461030516550190704d45901c02c03034255072040301350200100c003410610040200f051398100c001c1b82d07032524002c0078000c0080002c0443c80d80c22a10402410410540441804620341450382c00000d034041c2c2001e0458100380c600081c0c21102d10040c503810300c9a41c0003040d0a40c00000000108480016005000c140c4102654060785030b5152603403e6401a1102a51540c0900c0107e03080d03141001600c1d6404400070070040c030f00001100451042001907208511540000380 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 777890197 1250 777888947 777888959
    0x7080402030d020c010c021e130b0a0e04050d03050c220311030a0c0b09010309052d0a0506040303150801090b0a0c03020906040306050606070803010e06010905060c060721060609 78
    0x40c00b40089140080c0c14595018030009048042201000c0c1c451b62441c82c403807881c0c01e03862a1080d01440080c01c0311140f04010140c5c10b016000103440240900c2c40c1a00c0054482c400035441401154414050b10348400e03030fa40220003504000d008405a9041000702c1c480c06c945c504481c03130b040003610002054072031850070000d110710715244000e8020713005900d81c0e03c0061460a03182e801c1c0c7c0d01800300e0340d0322039107801c0040300213000708440105a84600120004103220b4626540e490107400161880c2503030a0002e5103482e040c800d00300900740d0b8444804500000d000350050708140c009503030840c0d0704950740c160b21406c2d11111a0f0503903007860181c1c24800307840d415004491055045080640c40c0c400c01001280441c419840060040c5070f0301d0020650b155514400c403009270360040320494482d41c542e0030855040d0001d4551601060903000001014209402a5080c000b0010081c09150b5640e031401ea81c0c480300030340c0c054203180b074000750b180c2e44000d6445440d0191a444d600c010400d41000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 777891447 1250 777890197 777890203
    0x180406050c0306061912020409060302042304150b060a0f020f01020f160f060518010e120712170a0b03102d0204080703060911090405120a0c0b0708040203 68
    0x54074024024400304100715554807104200c0e000c05502400700c00c1d540d00021401c0342d15209414022039410300000d400282d0001d0b83e0411010389008403801c014401c8618410b821007203650400c00601c10040d00081c01082814031100021200d0b0311001c80c8914042000940a80c82a450798001c80c502d22009911385a040003800c1d095402e5600841c80c040340c0c0149110b05010344604068010581400c00013046680c40301000800d0b07102d0018402406c0050b1340701d40034078510700001220343c030741210b02e0740c5400005510050311a1000155140982035200c03000c2000c06451b211080c03010121032802e4603020001d030300c0d00c28045110300252160074241018144580c0c4000d1214440c02c0500c7c04000c0c54a4400c00b0782081035140ca5003000082500a0307201070300a5520800b00d80c000e044000060103201d8125081c034500c66010780c110341c00c4000400030402c0c401c6c0c502903c1c5520001c85013004c0d001388002054030003030318103001d0f89542103a0b84240307401c04120348100c0060112000d2100f141420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 777892697 1250 777891447 777891451
    0x210418052202011425081c060302010509100e032b0503060604060e010c060e060f010603180b060d050102040311030606010801081b0d020405130c140612090c18040605 73
    0x10701c00c60302100c590002880102000a03c0e41800400a545106041c5d86040700c0712081084001700d0b224007150502d40015002034041d10400c08114105a45080306403003004160380c0d05841b40c60070200b01d1800c0c80454800d04440348240710b0701d850582c420b40e50070020703150020084844990302861004060000a55031951001031140a2048c00004e55403241a601030b03400b18581800b07414809001214009080c40010f400c8510784030804140041c0070510602c100ea025100c003046990b00d0f5400c408550310b425074100090202d003043d40001c8d540401d40f94200300000d0030129100c409803030350360890f40f140e401100d800d42c506804200c1401d0522140b60b10900034201182c1d25890310024a03100e00381d10101d0041c0e4214a60a103600d03546400c103842d42c1c00d801500401c00351521f40490501e00f80100000c0c0c401052401d000100c40c41d5030400d00103115405000715080401c03114010910140280c40c1502c54014030512201c15224550032040e01c0001e04400d4155050a09141c4121000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 777893947 1250 777892697 777892741
    0x1060816030b1822080706020a1b030c0b0c070203030904050601020c27010b0a0804060504021f0e041b0903080f040503010e0a1e0f0f02031f0b01020c030a0521041805 73
    0x20000f5442c0400c8402c1c5c01e4880e01508400090b0b80c440701903000f03c0c1c3d0072007100850f0649191007014107081c0b5a2040840840910901c8014400c3c0c0302c24050000301d000740d02d00203604d64803c0204a083c0e0404d900320641100042c012207001c28070030000500c0c0d02603140d00c2000d1103100c907062658044003c05100d4014a1040300140c600009428014810300d402800505095102c0c0042821501c4456040007920450140d2a14007919058010411042007805512036410204241d03c056006200c100d071081d10b548801801031b186a4403140c00384c010092640f40310100f4000001d5940702806944007107540b00004e4100c1d20050316108a4443d520f200c2c0b038403601c0c000041400025030a81d000b441c0c840c0c000501c1c030182e20142c40000c1c0b0740b44140d08501681101c0a40f09450200143c2150fa4000826025211408008014035542d54008800a402a40292200d11541451402840900841c1d0300e08901e400d1719224001e1b0150700044040e502690f4400c2001100500009905a41e0b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 777895197 1250 777893947 777894001
    0x90f05090c0a02071a120907080319030914070f06050403080d0b0d060f0606020d0518120304091b14090d02040218090c0c0f030301060816030b18 64
    0x2062902103003000c00000c0022000c040300045004001e4001c0205500801c8000020b0a615100e030322503810982020f0a001c3c007181c00721012800b031107008103840b4140d0f000e100045081482010031801c0420041c16441c00781540c8240100100d403030448030f8004020b40c1c0d0010205940b4009034082140c015901c0001044010b11092000030a10800c84180b801c100341c02040c4102000c001a00824070500d0080211b8074210280034080c845400803000c130784158003902c2c514030b50108142c1d200d119504003c40000c4240c10811004c1c031340841441c11800301c0c002120304160301c0d21020301c02c44d04040da9a45690401108103140300398006409145c0600c05800142004144c6010507845501c1040c000d205030740114201080d03060b030303103289000040700800d49201030034450284c40341e03540007103901c140c2d60240001c0c0c100348200000440b8101c1c0c40580d01c1c1c070035580d915074510709211007212640c810075031100701502d030035a90744c2d00c8101c09a800f41200c1c040c9040a55103075203840c0b502d24114503642 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 777896447 1250 777895197 777895199
    0xd1b1e1205040f050d1e0b0405070503030f1e0c0703061515120506040e010f0f0b040b09040b06150c1e07350d0c12180902070c0801020c0d090f 63
    0x9181da003205045a01c10785110045511521b09501e401c0d0110208002035009207585905000a10044900035030207102654a429100d80505d0b840340700f20f072200b100031030741046180400d0b518055207a80c0d0840c1418005d040c101000d88040c2440e01c26801503a9031921045000503030918041841c00500c204800c005030200501c3c2c02a01c52000784484000c83c50b039980c00104035481e6034100c8017440c20003030000c0290710401012000142401c02d002100640307440107030a4a07003051f03c1003085180c8003c240b1115981d6507954000744072030081500e40c0040032100075078103011840024040c810304c02c101611080c141140380c01c0e02940b000103070204903800010104460b40c500305156241c1881d47d00702040309140440440100d0480b1001041d4030f22424103040360103544019004180d52180200441041d80000201c840c0003800360000001e582c0501c00b0002000c20340d00628034248110a10598180d60b00011800ca800c41150b0b01200d411500740070b641c0f02d034009004005841d0802c2420541 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 777897697 1250 777896447 777896459
    0xd02070816030801060f080c031005060d060e06040506091b091e01020c09010315090305130b03041a0402150702040b1f111b21030a05070c0b0703020d1b1e120504 71
    0x20000a00074102010b8004041140c4062b00d035280b00203840301400d0256030b9800000c0450041c44180b0079090014032003000304020345024000c0501031440282050001d03143c0307000781001c5003141b845d082c1186104000041550301c40011810942554a402040444d0403a00290070000141000791060b4545d00042c40040c101d01c80b8800a2889100c0c0000e540c503680c40c058600d07104441c100161015014000103000d59000300541c481c520401c0e00c104078180329800140244d0701614000d6201954004404081c0d2003c4003034145140010700c003080910b60900450611085501c0400031201c0c05112076642c01c3c0c2000b10b000c00401c1020081a00c41201000d05103802c0c0036407460b83c070907002103030b03048104441d06204400d418140800e503035441c8900c000c09403407a413000d9021103602801c41381c0041c6100c5400c4c29642155015000343c42001400401182d810390061040c0051401d08080c15003c035a103102c1099042c0c0d1400c900321070301041c60a2824100c10716424071010010200414001d0f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 777898947 1250 777897697 777897707
    0x1c02060405150606040b18040606090b0901120b0d0b150a05011d0103021e041401050304020d02010e04020c032a1f0e0c04180201121505060d02070816030801060f 71
    0x4a040b001c12000c9207844201c00a1010703c925880a481683c010418249490401041504607c0100c1701004031350791368202a50000603510070350900d1201800110146d50040b00001c0c80703400e06200018100320041c000658210300d031041540e000e940281003001200a1038452406600c00700c0750702440d1841c00000901482c45031060203040000f00401c4002c0b41d00940545d01c052087e00c15584c25420f0340c4444090b50342052041040c030030b07503152120806500400881e801140c01802c0800c1150580d0015122014007002c01d0b03030003583c00c0145e511340640500140504222040c00c8c500503240c0d2094094120511100c104040c2e00075049281c010301e4850850a03101c5941d042c0803545080b90862581050031501c08c8503001030400500301000c0d44240c81c0c0b070512a100362101581030591511540c00c40301040c0010f01c1c21004104280110300e011405040444810180580790814641c1c0d1119541c210642c0a5031600503801c00d142016040890240541b500b440c0c913807a00000e12400030b103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 777900197 1250 777898947 777898963
    0x210f09120c0a092c1c17060604230d0c091e0218010f1e08010608090c130e010e12090307092306310c0311070209070216081c02060405 59
    0x2100c2080c000144c581003418085031500002e03114000d03110003d0302002408011000401590b0090020009602407038003070103542c2601d000861054141c030410f503480c0796104040901c25440329285986074005114403403101c010f80743c10240425031440901001d03c40b0003c249601010318018001380420310200000340b03070b900509181882c0ca109245900b070315000c400786811b03194200c0e4040d038600c001b60010400f604075100c956461100d60b40701000c40392600e60900d070b40c03a0300c4494895040d071020b0070782e00400c8034800702100008008030b04000251a006a200303514001c100f01040e0031101f03140511000b80100035a29080c84410010940d80c40c2c00602c2e89a84132090040a0105070540c40b0f0104840740143d81c1d000400d002c0705111095841c461880c61a40303c41d03810014104071042c42070050b074a2169215440c1030503c01b81c2c0c1c0c00c220007100300a0810085105c3c00191004441c0d01d85000030044c50b1580150005111040340c0b01482003103804d00030159840502400700050f00091182 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 777901447 1250 777900197 777900251
    0x200f1002030601050412030c23121e120108010b0315040f0606050303030a09150b0607023f1b1807020c0612060a08210f09120c0a09 58
    0x1680d82d554400140c0707190180fa0801000342013482c80340000c064200840885080c05942070f000420081380c024403258081c02080080d94000782c0c0180d1144030540054111118200300d400b62011040c507003003034650008d0303c035201d000325000300400c103415082c0304590540c6c0c070980c05060000c2d400c400e401e1107540058401010021200c08650510030658480781c082c0000030140c0c3c0d52801c0c1f044c0680c001e4880010b06941d400a41d9540b80c40a090742c1c03194064412010f000c00d400e2409640800882e16440010780c0d01502c6031169050072030340d41c122101c0a008004d0f121071305000c4821038503490145a5052102a407415049001c55a5a10039029070600601c00200a541d07640c018121309000501e5a52030b08640c0204000d50010a104103007803040d241a68135207005540c2d05006a03940002c000c5000b440304902d8410580c1d001090300601124400040e4a442c180f40300707012528400701451125441c2c0c20920710001d40b450404100c400070040c00c582409402e0f101c0503c10752454014090b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 777902697 1250 777901447 777901451
    0xf010603050405071809150c030b0a060c1b0e01031202070b1c0e0c041a031005010614030405070b0d1e0905070b07020118080d021018110f030d200f10 66
    0x50788017940081c4941544803500030180c1c0031000200014141c204032540110b410a520b0580c3c505104888130f045540d03a42d602c022400c0c4603142d840701a258200c000c3c0600121010208004c40441e0701d00e40210320402c1126080141400000d05040d1140c200070344102e820003400d0036000020400c030b0688013039884001a145904600a46016081134115030058140b0000205c45045c107000b1010fa04000d07000d40e038a8662048081c402c441d4240035200c0880c04240318050500741400140d50710912807011103480c152241708a0946400c810603403425039496110348440c06020040039031540c0700c0030009000340c00203565015100d15440c0205c254440c4045154025a80310700c061550030150b0001441034903032100e9040d40c8604a614684d8054070403048041c4415070300b407158a442840070708041c1c0c0da0344001c0d5030340e0900f1002c0810099103d00c05000c0e0301031079502030144046082d0a52140c02c1e0220b00190795000d030315886409103400c2e81007503026008522010030740c03d402001d12200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 777903947 1250 777902697 777902729
    0x612020108250f02010c02240c12040602090103140412030203091203010f0608070504030b0f3111010905090406050c0412110315090c0f03010e0a05060f01060305040507 74
    0x5120290380c124484a100040c2c040690602a60400181d10254005500a120303c0640303040c243d03034070a1120800030f8500114000300084103540c00b1095040001c00c40a980b403c41810046c10603911f0564003030320b00f1035001600160325a014421190301012000390030000b071030301d6154401e0010f00030041c48103258001001410340c01c018802c400e0040310041d011522075031a601880d401c01c0c0680642808204d0358004038403030a005800707035811264800403255091e968a940b4204170358016281041550743c081c024a01405e800718401101410021aa103c40e0600c0c01c025000b15000310025050012014080c4044e0711007003201507002d60030002c0440c25858035507081035984a140d104144d04010031411404010080031011108001201141c414070b400392804600701c1d40036100c03194240d01c01c40c00c4041d40e080485d100c2c02061300c024000615003140c40081c90070700f001100b080f5203035005001000300740a1105606d502400e001e14042225190170360310b05030b3f218110700a03c107401c401180c6c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 777905197 1250 777903947 777903961
    0xa03090305041211040e01050105060703051e1c0518030a030216020604030f0308090d091e030b0c070201030f09050c19050a09050708070c0308131415190612020108 72
    0xb100c00411003810703d092214040d0030b0850200c0304c41c0c01828400c80c20041640c0041e84140200c0f8162640280000e1500c1032a83d070070b4442c0c1d032200d02005034140140c201406000146009091b0000c42c00750394000b0390005010f610120b640003400782100002c952460918404004103035045100d0310b0600680e03444040301500c42241c92010025444840080c020003080081c103640300c105403090301c401300140c8824020b07603143c2e1254005600014894102040202ca00c11010310302c0c00da465500100309601c030f880e06400c0d408110782113092810700190300021564544522842c0240f41d140805c4007208039564141c0340d29008a42a100382d0030703076150280400d0000085002408018190001e6690700d00c2401c001e0700c03080f2000000300d1111400a0b260701d00a446103440d00342e140c1c3c0d4421090750788800e00402820000c0341914204070140c1c0e002400304017003100400702400c0411501c424541880025202c40da1041d4104410703007000401c2264802c0541c00021080d42401c1c84103c96540b00303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 777906447 1250 777905197 777905207
    0xf040503010e010c022406101e02030913060b07080304020a09020309010f0b122805011e050606040b030a0c261005100e040b0607080a09180e030a030903 67
    0xa0402a8994030340354000100c103605520188180180b0703000d554140035403018141c0c80d800100c4005405c6002070000480c0c92411103110307074840d0b402d03041040072661140300a0441d002071040c8980980d1000502554624201c0d1400003040e034bd484080c05090b080c981e81000d24050100002c0000c2000720124045544202c1c3d00c2c405041c401504544901d441d40c182d501904071030303085962881ca801c46500890506108a03101081c0d00f10040c0318a00d2000e8040b40d181416502c615014800e0342280d900045081c0074251031060400e100070f1100c90840240c10480f6009801240300b9001004100030384c044030070a6075841012104006150050044146c400e4520400707078203004003a521501424449102030b0a0103009240380701100d007501c40c400e001500000c0440f8101144480110010358601b80c0c0101900c00000f816440c03d21002c0d0790b03a400c46401214405000c60110744080c4800c1158500c2080c500440709000c0c0300d4181c0301c101d40e079203d1181d016603c1c01c050b03c42080000b03144c003075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 777907697 1250 777906447 777906449
    0x120c0512070305010e0105090106171f030f050c03070f03060509150c180306070512040507030210020f0d02161503060b03100e0603070f06050a0207090c1d01030905120f04 75
    0x308005001514101030010000c1100740121080c2c806170400105540c200900d1550503102551904804030323544290029100d04020212026229a14440446c000110048400646c46042220072880080c5011801d1a8207500194002d40c4441c0040201604001d60102101e0f04500c001426881d40a8524204250079080465488840c818030440c080680c0003480d907241c2801000b00c035038072520308040e2901e10a0b0b5060b80021300030302c030307503000c0600710500242c0142c41441140c0c0566900c0c0d003c900c5c4003401108640241e082808006a840000e101d1050110154409803802d8080c0c0b00c407000f0f000346940502100944100e944842c030034002c0d170201c4054490820015101e181c5481d502120074a207001d15400180c07140c0201d00e00d410000740060950307c2c4200d24424860601004480d1500801200303411031044003030004061225104001c20404030341d540102842c40d01d14121002e41e00e045080381018503152080f0089107001c24840d00d5108800011552030f11840102c865a00803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 777908947 1250 777907697 777907717
    0xa0506071406180c1806040b04090f111e060d0c020f011e0605060c030d020306030312040f020913030e120309030303010906030b060a0605070303111b0c0102010e0d120c05 75
    0x1030901800b1100d08600c02c8081404560411100c0e001804400d220603805c41080b080e800c034682c2400300d0607a241c180c1004105400c05040018402e10f40e407200f0b124410558070650308001c20b49003c400318107004401204800341040e500c580c08540201280f9980b01e0078160303038070a0741c1d500c407045107e920034420410304400c020300900c03c01302c880719204901802101080d40c154036051000a680c140f0800380c0b00c1200b40c1a01031401c0c1031030111004081d41c4024105949804100240000039204c0c56211380030307a024050308401e2100d144103000c42950043c110440f005110011880001c1e40417030003d24040d4240c0d03a84804103002d0200c0d070302c2c0d806002c030310310f81c580008400490400969441242228003c90001c1510b480745000e020107801d07240034000010b0010070500b00031900907000840c01589015001e45885c0103902c004070703441078441c802d103800d80161885200c01e607424000c841c01c1e060100c010348114150307110701500d400320b45003400400f1a00c80c4c007001f0f11030340200203650403030340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 777910197 1250 777908947 777908953
    0x1150c060e0609060907050406080307021c080d2306030a02121002070302030c0607050906160804050618151801080405031e0309160e070c0c180f05150a05060714 71
    0x10f01207001e58451800f280d1420b5284111900000c2910b410b0250038100c410110107980340c0f10040d020311260f156002d810541314014030403c0000245144010f0107408408a000241ca000f10038150712018040348850300c2c05185001031020a070750110b170721070301f141e8100c50841800b030046c03158504101895003011034240c4041069414076030040010310400500740c089e20b00517030703403c02c1c1603c032406800c0450f0b81011040c003074000520700c01e049020215018580d114186a6250f0025401e603100321200c02c82d0045804081e281c80c20400220140d480c81414000c2c1445980d044d1a1010902405030078104038a90002c02c0c1408014411200250082c00240d400000c20020b10a0b1a500c284e80603821440b5403a00034610744d5030880b00e0750030b4911000c03200001e9110360808441f6024220b40c02d45042085000001c2c103000c0520802c61002c1c800000450300d0110b20445100300ca40c01005950105407005125042d81e031500e40600503918103c44494075070b0b0050400c0c0e04c880740c540b14801c00c20301c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 777911447 1250 777910197 777910201
    0x515070507050c0904330f06050102010f0902130b010507020d061409060c0307082d011409010b0a1407061419020c1f0e030d050115020601150c060e06 66
    0x551100090440728029011152008607803010300c00104011640130703007201c041d0000c01c0000360b00c80c10b172205001000313203980b0f04641040c02d44008071070400b266442d00c259103078001c0182d56020700840110810443c401c0100c0c078900d030042202c540d900801c0c0d44010741d450b41030882507070281094818842d0003a085c1e060f903200e1454040020248050340101d10711602c000506210340005202c1d20030300602c0c948038110707141c03188140e0f881c50000d03090680c8015200e200d0035501049020090366079201b055004459450186c01ca048210945202800b4180f040018800041810101d412401075071420b0411444850401c0710503008400f4010107560a0008501800c0001405140200084076014048019000c2054201d01c501c1d00f0646082d00600b0441c404591110411a140c0107d4080421102071241d151425940181c803400b4180c1d84d94001882a0001100b18615882c0140010509941403a041d008230b22a407644090801000d00303468000c2001da0f40110400c00340420481e8518 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 777912697 1250 777911447 777911461
    0x50a09090f06061b08070f0c08030c1f020a05030f040305042303280b09030c070b04031124070c2c4f080706050606180d0515 55
    0x24100c41e03c1032400144a803030301410812546007265450315030183c0794030301c0c1088503510b0300240e59841d8001c0d1000624200002407203042800140104040b034009840d101070801c19070483ca1090300209a0102d1051290000c086e80000c112504207408084900d031507580ca1904030b07920300c40e0b50008000c6001103402c1f20f1045100240d4143c01800882c143d0b9a4106140c4034890648172120700c0d0400d4602d02c00c3c04c04d0100b140e08140b0303600084030380c0a803840c0000324031401c0c7c44c01d4038941c8100c0d0200c80000c0e040091090102d042c0e0003034001119183c0300103800c014050b1090440e200c441d80d81800c0000c1800c10000600c024400400d50f01c10000e40081d0f0001036131a02031002c04400000c42180c100080312a501c51005031b058450b2102c45040e19090044140c580108103a1100444003070b103a10540d45c80405e0b0040c0c482c035031081040503541e03111803a001058601c091302050041c00d00f4000d03080314001001d040c104a0005440607107002c807541c2040c81c43c0400f50401d0600c1000c1c44820f02c600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 777913947 1250 777912697 777912701
    0x120c010c06051305030705071d130201080402031c020a020f0a030803010b0a030605040c2f07140301061d09150106022a2d090f0703022206120f0219050a09090f 70
    0x3211271182005a9030140820b00000d00703c021034001d00d00098100c0a40010760060002c203811900180031211080c100a80c3c01890101d007032140c07005030b800308504104502d0004101119400180c41e41d00d41103103140da41d0301f80340c0418007401038082804100f0b981202e02ca41d014100030f14000f801800740b405800009030256800408007540c19003520355095422500001c079142001c2000d00410749285031040d00940d5030300c940403155065480d2640010140c4407584845660305004958640ca03052102c14a03250004000090403601403241c010800340d5000324500142d0342d00e100c0300080310790111031040810381007214043d51021194182422040b40c403142c0764207000f010031489882090003401c103c1b441004803a00d01099410302c000400340780c0709801400840307203003445803a400346c2d41206200940d030340c903040329000a800070380240032803040e030080e03070b02114206034114130741500e05000002240c2c480a285091000000e40c01d02c50621865005008050710007080040707020006030900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 777915197 1250 777913947 777913949
    0xc03030a020d0c030b0d02040c1202030c122d0402040207060f0605034e0c060f060a0e060103361202072909130b120c010c0605130503070507 62
    0x40b41d0351402c10708440c0315000707200341d0a041c84010608410480c0a07800c11000c3d00c41004010100400d500310300341da14403e0300103103001c0c001c0690402d0700d4001e40701e001c0c1307150350000b00007001210042c4080c5100400442181e081800502e02c17460141da0740b400407502030701c60b885005192070701d03220002040203013542c000b07400c0c0e4a08900355241000b5036400500e641c900304a0341082071265110a00300321a520b454555411072551110510788928090100550845c00c5144a190048010000b00d500b01004d0907610040072900320b130760681001c0c4c1c1c1a0001800804040c14107a5907507001120364004007a14050500c0b1001c0015170700007005030760444540303505c01190403490119102160380d001140f1a0140c0d08001010800c2d42c540301e10031141642c0081d504030b08007a0070000c0f107042c3d44807820f5040e001ca00700c60010030615110400c4c442d031104903481074503c2c1e420948140340a6039010741d40c108150340014001c5040d8841c0400605801a2520700607e03a120000d503000803c42c0c0807072480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 777916447 1250 777915197 777915217
    0x3050708041d0106020f0c0112060e01030b0415060303050f0c100c0c2906150405060a0306150c05060a2d060e01080303130b0c2205030c0d0c05010806060c03030a02 72
    0x28a642d980c0000c1e40d1b40c0b0f50b00341100c6000d0700311007900e5484c3c0d4400c02c021715412044183c08038030150b480f81d14010403003003078000343c9910344004100001e01c02d4000c05a89600500c12041203407030300d1902d00030440c5c00340d44001201105d000130305801401040120f543c05200c07003501000516468a8041e00ca422084c1c0210762040e810000d2a8242040c00c02030031414060301d203a140140c3c1d5484c2040f003007403800e600140403000103000108240d01d911021700f8400c1460786001642d00c0c1002130250440280c1e103001002c1148940c10b190014102061041e044103503000045541c0d440e07010201910007215164a94810a9040032640d0302440c0c1c200c0c0c3c04681102000d06a01c3e41c883c0340c00c45d00d80c0310441c0e84c22201010002500001441c1c42d55031030340500304035040c5084c5020f5002c445903800c04c42c14120181c68200d031041c406807a080c8841042104120340100c99140d40b80d5511440102620907507043c0100701c4009071240d110682180c0121304590260717075803441c120412100a4100c50144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 777917697 1250 777916447 777916499
    0x90c080c01121505060913020c07180b01170604020f1819030f08030c0f070302010b0415062c03061f05091905070e04020706050912090a0605070305070804 68
    0x3100c1d1040b014072036080d42190322261080c4040c00c01c004e0204550044150a8103c0e0921004144a520a2000d080e079030134904080d102845c580303281c8910f025918240540d8251815001c00f91aa80000294000c41142e94001105556020001d0020b0050010b10301c0c86400c0018001404000884600c40141080f500b010410a29592a5900356028040140310594010f6480c001c10307602c0024690041d80911884c0c036000b042d070345d400f2543d00400c030110007507910342c000c40c1c420b441d06000c0c400a8940701d40f050101640b6140d0001d12030b01a035040c03110400816000075442c5c5220360017090800b4070141c12036a00d400c03c00450908040c0c00c00c1203006114000c01d02003014030300000d443c1d0266180000041d209402e000030b12008000c090a6581071105010184289880340d0000d454514061540081c440c034040c2c200a003041c10705030088100c080200105807c981da4040100182c803d07514203e5121507091609542d41c0c86842400341c000400071030006403541102a90301920b865030004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 777918947 1250 777917697 777917717
    0x7110405010b07080a05091c1142300f16200609030a0e1009180605040204090902010f030507020c0f180c09031603020102060402060d090c080c01 64
    0x101240d43c000c40000511402041110032601407256000c3c08500000a100030b401400e100d02e070b00807c018198040784d080b0348a03000000c05140020022050304e00340d41c840c6000c2c02100c0402c4803640f01c0c80902408260041888041c1c0703424280070303181611409241100c480300c4e80800d014000030200e450101d102c8140c80001c600641070b050090003032221401181341c89000c10b20503601040700190001e000b416900200b913064a080100c24040c0c04550301071681c1d1004560010100046941280c0c01a2055101140c6180d4059689812200301150314981088201007503009086150300c5154824008600410074000d01e034005c02103d40300740c0f1812080140c2040030740580310100c1c1c0f1100503802c8050990498206903080c0c2c2d10315400201140f40c1a00c41c09a404101002035071140030f000e6011440700380c00d08081000f007009031000c002151482e4956170000350745610060000380120004915100000720542041c40c403285e0244c1c000c0200e5072603207001c41c1c0e604098424140003c0413010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 777920197 1250 777918947 777918959
    0x150e0109170a0905040f0905060421020a020603040836010801140f100509090c030a0510180f0e030705010f0b040e030906090114160317092505060711040501 69
    0x460320b1401540c1c581c050120f15000400c001400e41c01441640b0325140c1003403100060080c040c0c50300c90786c0701380310a40444a4040031340c0c0c00741294030101c5055601603880c030400b594962098a0780543e2080840e5519070740300001000f00050781402c0c441d203000e40c143d10800700750a21400c560101007a80c48008580c1c1c0c62000100304003912245640103040d25036031102c0350a010201c040381c00d2960509a02c1c2a11141c04269401300880d01041003000110502c244020701e4050550451100c98800c25510705154403e2142c0a43c01600603050399a00d041c07101101042e00020300c00409001500d46a0959040460280102c10041c0107858501504107003c0d1038103128090000c11210000e5013008074640074440c0991000c05090305011492040d070400c00200801091000068030740d052007401603103405071142c84410f01e0f50440c1c1d0401000c20028043c0040d40d401610340743c3c9484070a0b00c2582d038002d400c612071500002d4102030002210703024000204200c0c1c0e0001c0c01640e081100d41c0e0780704 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 777921447 1250 777920197 777920243
    0x13c0504150e06130e04020901080309060a05131d0915090705040905070b131a0703080a05060112060b04063c090f090519091e150e0109 60
    0x2001d0070340c50400815003036040714420030a40d00b541001801040c90b1048500b0503440c0d2a5090307021684140000c402c00003141004090307180101289001541005000d00010b5202d0003900c04603002c000010591a07102c03204810298000c241444038500206800e013106c088200c812901014144140d081c00790381c081c1c07000580c0b44500705000240150500b48002c03c0081c001511050f42e46114002001c030744008030300c0041898050030400241e4041c9840d520f0f002116117a520b61101100500800c000729400c04940d603403240008100181943d55003006903220441c00c1c904014036841d18a001c10701d0f40e10400100152445030b11a0390005030b0000d40d15202c2d00d02c00c0c0d410805070152010707110b9601200300d521142480c0700d06060740d25170b80790307202e1050912555104084d2162201c0074040c103040010603032040540c4e420300a00000c3e465403160312014a5200c101c20809000000d43c134140300d01e40031070401020300814144004485188801d000c0c2101231010356000340307002c003142c0d0510416 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 777922697 1250 777921447 777921449
    0x30616050a1101022709070302031009050402180f011d0105100315080d08070f11070311040e010905010b010e0a0608061036051e0906013c0504 63
    0x659505140c61181a002c0b5400c4071180e040e0342c031940d000d100b4001954100c80b40c0402112900b003807505c011030340d142041010360001d0000b100385841007003031103203a42c90119240103840740060301054645440c0302241c4a40036007091110008000003e200b40c0d4200090a13504031074440f1038030459102002a018014402842195403210100c0b0710025014020741000e410050030000d6126065070320324403981020080d45c18400026a41010030035005d0f000102d0540c155500e2505c4a200301e200c40100303a903540d40b03000107040e941800c1560203059941e50040c2428100b0718009004103070b481d00c0c105010b8142041040c3c0403d916075001c4895061006007641224101e685107030054443e402849504c4107030314120340c1040219110201412148880c4400c0e180380c15a80c40040d500040001007141c8654004034818078248a8170a587d0303c54480003942c60134102c50521160f160705005940d811170760f01c0b50400c03440c3d00da14060b00c41254460600e440002e080f01ca40522070100000303c83c64400c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 777923947 1250 777922697 777922741
    0x7081b0a050327100606140307120905031605030315220e070e0c1c0b151305092401021c12110c070302040b0a1a0c010209090106030b0306 61
    0x10b00020702500c1140701c908040070b40b44002c0b104400640c5982605222100081d0040191201000c001540d4021200008000c03080921400d506107428000d241d4817001c1c80c4808005d49a104020a01c442441114400c54103180c43c40101321103450034035181c8e04210b440441104402040d16510305103141094005020380603000f2508280c101c080c030043c008034400c10100c1c8500c0c42c1c0460005c03a0181505d004000c030b564401d84600030f5100d07103940f1120440d01030b40d0740e074107140d0401d00c036465601d0440b0b64081483c0950751a071400e800c1d444a06103980d84002d0344000002d0a00c514060351070413a00b5070800d01c4c00300502c110402e000586e070341c48540d40d2400fa10306002404003c01441a09a080d914003c09804038654200b0740c0821107940041000c054180c0054000b00110311f8640f10303d4014240c103641150354146003110005004c807080912441014001a444001c2e040c298110b54990b000101018483c0d42c44140060050120304140340c040e201d000041201c0c8020050080a8002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 777925197 1250 777923947 777923957
    0x5070801030b13120e12150c09280510030207050601030611070b0f01050117010f06080c0d020d1401171b180f07140423010e030607081b0a 61
    0x110715a90310200e003000821500106003501500400a039510800c042c2d1040c580e540d29624001d90710400202e002d40010000850740404103180e148043e8400da00e038009a00100581c4800200300400c82200080c440a101000c3c00000300e51002411011541699015100c20f908180008000e40c124810300401a1040d4068001080002c1941d04910343c0c06191184040c24103000d0342d140420a4010b0310b07241c0340402440010b000279640145400c2a403d0050625201c42d4500f03050011200458060034040040c4000068032480384c45048840e0058460340c110f50340d41034428990f00428640c030044110030816400040c00340e044c803407810700f01d40900e000f8005454400c0c1082448101c050a0380350000c022014292045031103000031841603040c00c1900c050307444c003204028810310307a0442c2c151070030805020611010a46c4802420b482d01c60004205102c0386400c0141c85043c1010f4007140e142c41500300304003030540e0110200340221413100b810114070071802e0410141c1c0c0200c14040c40050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 777926447 1250 777925197 777925199
    0x806070801140409060605060c1005070f0c060c020f0307120201061a030a0914100506040b0d0302070303080406060b1c110c0a08030a0f090318050301051b0304050c060a030b0f030105070801 83
    0xf1070141d00016405101d90000504d042c0d4800200e000e9800403200707011070381c020345014661b2034024041c0359030110b450701d01156088030714103010781509120346e005090103035180841c4c0360700c030b008200c50011441c8541c00c50b9154a8140fa09240400742024254015401e014000a194000d078210103203410b8120540b900f1135446401c0030b001000410380a440031398500030764802442040c008070203020303454440440c0c10f1804405010940d01d454516600406081032143c002c05d60200f00c140540b9414a464501c685550070070102070582d41c2c201540388600014401100c00c80a00443c104415650003071210140d9923040c01d0941c000c0d200c45032400e030402c0c0e5140c0000b07801c0030010350340b061100d1070000d40c10049450307080c1102c288920480101d00c5043d00a40066007403441640146000c138020300a81c94090ba0a6030384418480160224a0002c404130f000c0110610048034104009080300d502e480c110361000700a0700c0d01e91102400b51500c0e070140442d6080c1806240c0c030801258640d5213840e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 777927697 1250 777926447 777926449
    0x702090414120f071e1e1410051906030b0a020c01060f0b09011e0219030201094106040201050c070902040603090b010b07030c060b010c020316080607080114 69
    0x401c10465448901d0007a41480c84948140601801d09141d524a180d070b200d000604d8000300310304452640360035402104001d1800104041483d0794464140034a042c1c3c60280e0f031400500d8032003d0b0403004654011040c0c602a030707110380d074025486400060303050b4a040c02d0341c4075003400303c40c0340d070001900c90715000000818182c07890300240403281e20307031300001520356480c103001041041c10342008650310f00015001c0200d6900c032002040004a890040300070074038504d8069581e942440b45050030601d01410320782498000c0d40900d0140d80c011341400751300e4058603a00c2c880d0180c1c00440300081c68001005500742012010008520341598000300310545454005480319040b44d03030b1400c0c1c14403031014041105012400a0001040107440220f1810782c1c46c9068034440005800601c14490144258804039610003184903859400443c00941c4204080c012a01043c01803006500340c4540e2400030090281440c006c0f04981120054404176100e154044802e94020b01c85c128843c94208508185 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 777928947 1250 777927697 777927713
    0x20304020a050f030c030703050d0818030a030c050702030105040c0302120a0203060114060720030c0103021c0b06041a120702060408120703020d0e0f07050108270a0b04052107020904 80
    0x40e80c0c200070111101751080100092a0654035002145c568100b410a0602c140c0c2000015401003140c101c40d40c50803900b00151540c9004040180c4101500e0740000c980c0140600112a80a41c000e03000707103c0361601d414184890011488201c1c003d90001940100414020603000f101ca90b0080142140ba480d00c500040c10f002240301c1e09a1084c0100040c20002c3d582a900e00504a4080382d0b1040e202010307002c01d4100f0300b0004440307040c980104141800c040241402d00700740c60916000095424103500492020701454000e8034a0b21869403000c41070244000140810450b60300b0034240360743d01c03800d0407600c5000558005148080900032201d0307000b070074501030740c0c0211146001410540070186020a65014008030780d50b0390480ba0f01d4603540442800041c01a01080c2010490f40c02c0001c6560343c0081600324031560003040b02200d010226007407150160054100c0700c03100d01c0f414a401c00c03d0303e85968040c007000403070090025802c7d034030000781581c8000e50004e1605400e46d0300ea0b110f1542c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 777930197 1250 777928947 777928969
    0x1d0a0e10050105191d10091d0c1b0a140312010b04080d05070f0506130b07020d02071401090308071b090b030a030507140703061a0d3c0501090213020304020a05 70
    0x103501c2c2580b1a640d203a949070725202445030075040d030303400949500c0c02d0101e106400380d5000c480c0d4080b4200d401c0010300072700c10701101d0883c05a04452401c03a08003142c11820300d440040c000b490503001d01451884000000058203140601030b00100c4144d9030303039456002c248201d1103515403581098640c61300e01c2d40594060b00c41c40c0c0c0510308481e112003495075603a0824404444020300040000b040e00c00340202d0314402a842000ca0004000030280300c0000703503450030707035204004180407102010000e40e44181030310f078003d550100200c0c0d01c5203030924042031640d0701b80e0400c4402040f41e480001d4101c09a006072814004094003615001c10b0356181190207030702255044d00da808071254200040304041000700d00450184000107112070030304000c1c2e0072001001140602c6507441d44c00324000724103844001c40a01840308003510140142d250301d0511b0714000703036051000b101510454400e01c00c041d045450f6407403080f85d8800010a480c20003904a000946000e034100d128032074180b01034148044008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 777931447 1250 777930197 777930227
    0x1f0609020705100c111203011701051510020109050304090b01030b01022a06070f030206041101020a0804050909190503040801051003030c020f040f0f1b0504060f1d0a0e1005010519 79
    0x10b1039045c00d40f503103076162216002da060213100000004102d481400070199405891200081c0054241410298807511202c41d07c1e607c900c1e11200d00030b048600075030040910075405400d0725183d680d203002c507100405540c1d00c12404030342040c54001c055880802c2818002b5400f06108c42c1c20700d0032074407000c5002011407106130066020002072021841580c104034602d0700c6075004011601c1e05162402000b1540c1e112141594031036089080051442410380d002d503001a15500d04683d034500f480e0b450328801080303c03900800e0f4119500140320380030005006071840c00000380b02d10b403207101803005590040c1c40094000b9000b040c0320401031403c4c407134015007001e0091010506c2102c1c2d407441812689103500d6081c43c2c542d10f10002c04003ea00d48002580745030b00d03041c02e9040918104003e002c21440307400e100c0403c07003104d40303442e102c00b1b00d201036206050000d00100086911000c446440c5e4005880a4404842112001070990310072001c42da9500c00b20322400605005490003070700c0106082c030f011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 777932697 1250 777931447 777931457
    0xb0a0e1f02060108190b0f040215040810061a040b0904020d1b181505090d02030106090209040e07061b05190606030b0604091502090627121218060c1f0609020705100c 73
    0x4ae80c0c800d00d4101c0600007070010440540300c0d030484122942d08880381030b80000b802142038401c0066440124003620100c7e00c06804003555150703403000007002440745105074290503182c215030140403a403820500b2510152038507179140c000b10b104180010120380380710302c035020807001849804980c403640203410721b11b9020704480481846540001d0a540c1d458000c1c1011a81c04a61b0060a03e414002e241018070240058903295082c12801031044504492410008554501c040100075003044807503600d8503500c6031100001ca6a25044001d40301e613100a44140a42801050320352801d4408e180c401d941c070050642079022a408010f01079000041034581c001000d005480650079404c1d9141380f000070010707002000100020130804954030124209102d6031003502d00078800f090b008221140802c1c01c7c5008500c1d040d070000002c00c940300b041c0c0700e0b190342e0040d80710010208086500c41e504a03202d880b400e02400c2e0721065603008a00820201500c50343c01015058483d581561101d80490903514103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 777933947 1250 777932697 777932719
    0xc07020d0b0a0e070b09030a0314210609011e05090a0b04021809090d08010306050a020415090e0c0a020703060c091208040305060f010b0a0e1f02060108190b0f0402 72
    0x1585094070070848152001c40d4a60b1a030690000f02030004002031314080714100d09184103540426600c1512070002818040d400414107000450101503c01303021110200c05804442400344208106040e00e40360300a070440c50001c01c143d001e40c0d012011140400c803840180900d00340810005e94009461525510f86d903104104458803940001d0080c00c0c0307029a0150403410a00520044c240014110300d841d81160164108456001c07a8250440c0d41090001c515515643c480e407000b0711559000c1429503000ca10000070054100004070304aa0104a509103242d54044160041c0c1c418240307144016040b80201b8070000301c0300d501c064800a603e14001c80f400d034580b04d440c5082d80000c1c400390707480b4101190800806c0f40410003280c4c00302c0d20b1804000503500d4900050154040c00e9145ea050042420408842d03449003a111000d0340c90581c1400030103080709070060346400080c00b401c40c05000d0603000e2890506500c842803102070380007244400a0361030300140800a203026008980c85172503000c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 777935197 1250 777933947 777933953
    0x9090209060d210903020916021902130507030e0715050f0c19050a060612020a050603060f040612030320041e030b07050c011a0907050a0c050303130201120b03060c07020d 75
    0x210035042d2680c0b84d116000001c2c01c500400641d408010b100c92049022080c0000c40ca41d03000c0b8044020120b6441040041481440041d0412110440d40340425290408200c1c6159040e000740c03c20210b40400e070781d0b01e20344403c0c2101c034514441d481c0402040040201e40705003034580d4014030b0310030395905c01c1e1100411800f0100c80d4151318000c1c150745075400840b02c0400d01c1702500c070b82c5004144598441c1500700780750b4003050690311244140c178819030001c400554151a031201c100a03c0c20014410010507460382c00d20003413101401e01c16130009203031a85004002e003c00e400c840082c1900240305040c640b40070060300d000b05c05003050b49061074000c0c000100040c1c0300360340300b8001e42c0e16807101a2901d41d0307901c00a085503d111000145540c0b16011800c1540700e180c00103410280900c4e005a030340d50246806d40d00e4484400c1c2c0184140300c0001044190b000301e082d80c542c0035100740c0c0c610303070950f041e40d802e1000c0d518001181c81c1c3c550480d0020039424102e201c01050440d1010f401c2c1c1c4080c071000d407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 777936447 1250 777935197 777935243
    0x2028050a15020d020d02070b0a02030904050a0c180f03020f010915030507111507080c042c1b0406120b040207030c031206030803160203160f0c09090209060d 69
    0x19010845060718540040c81c41501800001e0300c8414a200420031044884002540c605842c850031560200c0080c1c458803043c070078000c4509180028005010342d0405010f250001c01c3c3c403019040004070b454100800003564200c0c01c000301c6601c00b06c1b4203d181d003982c0800060301c075034010645c1070021490000550013595040301b445191551800203452a040c64090804e120201080942d0307001841030503140e5100b410700d107030040218908400c4a6840ba810945a44030307a4000541c222980751818680c000001610b1240d00c0281041c00d14540707880c0750040d02100c1c6044080340f00c0c2800d000c1481250700c1114500540d0340401b401151804144001c41e0491340411802d8000a42c04d04481041c19000100b050044c001d140b000c1040f20300d962103040c61404081c0080070380e23460841d641070005200b0400e0398032a2843c2ca0102c01000705510700101201440002111480303061032001403402c00610641c100c40d5000350510240e942d0384010840100428003003110102180303182000801c64203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 777937697 1250 777936447 777936449
    0x20f060118050c1c1d0f011b02030a0221040905040b0a0c0e03030412080417031b19030c1b12060e19020118031703042028050a 56
    0xc60001c02007184198a90310940d4002400b1003145001006441100036484012400f28950710030300040980111928002d80d8103851a402d50750f204000b0303a1224148190700c40c481d88000590000450f100100c0c0990f1030713019906958025801500a1001003c19541001b2000c28a800c0d040d04c1c0640f901c03c2c4e607080f15404d580503254041d0344400c101101d81d242c030500007403901c00d040c015460008440081d40d05d2040d030188081c0d41684241490412400c102580c018094407c2c50201d0b0340015101e030b035541d4001d01040c0c11014000e6080d201c03003000201e81c0590560300e503d0082004c0406403410340e002d54109904803900d50011205072000800c2c01c01070005000240204821205642003080503580903d0041c50b040d001103d0200d0320600c1c10000006440d07082c00d00c80c1205d002800d284c24502e031980d00c0a40703040380842c1c0c3c00c041041c2c001c0003503115903c2003110708540c10500700000040d01e001244650880f880c41007030096030655903a0f03015182650708001c5419502c810115400d2429 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 777938947 1250 777937697 777937709
    0xd0f0606030e061308090607030909020d05040b01060f120b01110706032f160f0804080115080604052503050f07032102070509070e03060708010321120c020f0601 71
    0x14482c0750250426081c8242070b0003012499030440088940c2d1a000c440d4411205280d10940002480404060041c90050001c010840046403540590380f20100908000c49044031301900e11030010480070302506000e05420515500ca1012244550f0340308010694140024140050100b90701c2c80c21130100440d47c042c0c07507150307400719a124403020135408500c61502d05400c1440b0b11142c42e421070f6100d00039959126a800e15090a48949041401056000c014090507011000071f012a48200c1508168401d05410000015480d81c174000582c4031102503400a001d40c10040301101100b0410b403200b403840c0151001c0001c0c1c079603695515803815108101045181c1c005040030402d02045800d0050140090200d408031007903e10002500d440c0e00d07000780e40c4070308499008922079510689060743d0600d009411200c8a00b09568041c4c02d5050902c400c0b0b528000c00c03864010007443e52206034249640c07903204d01039441d000008120241000c00c40060440c4200c0d620070074080000c021182c020f00e8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 777940197 1250 777938947 777938951
    0x21c03090b041a100b07060207031b05010207051203040203060609091903090e09010207030804150b12030702040f021e0c15250201050f0f04050705100e120f0607050d0f060603 77
    0x100300d0440d0302000001441e131642c44a801100b0402c0d10220000c030751a0a511040042c4e0740c2d15a45003d5a803400074100c08501c5800141041d010841e05600900000b40204100d46190703a407484030b1101440100c800a4041d0469801b0544d5400d1a0f4103803074000d00f07a6002e48290a025031030510450002c01c02c150002603040f88100451200042e840382c1005024000350314050f11601c1c0a498610054401400c407980100c0d440e0344840f8a80c01182c8920b03001344a4801c4036400c80c822580e80e08401400d138426032820b9007814156035640f00701c0f5200c0001400d082c2c2e44403c003440740b14054000302d0510b002406000004a2080110044a80304d842000d120103052401c00c00b4040800060707104080a40e0314000c02e0003002b030751a80c61190301c0f558070f86d6105100e036250318002e82005510351049800c0703130302a01008110f40d0407600050070742c0d80030b41c1c0c1082c0001d1183e01c52903880807600c000140b035400000c0810140c0d44210001c0101094240000c9403a54408440b078080f00c21607071180000035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 777941447 1250 777940197 777940223
    0x9100309120905010806030312180a021e040f06080723030f0d1b03120b030c0405040c06030b040b130203131704061706131d0304030f0507050d03021c03090b04 70
    0xd82c0101c10550446c4040c0c00544c10a10008100d907044000a012140828000300010441c5d83c001c0040000c1c20390b024203144009810801c00511119603010240c0c480e07411326070410100d0341d051103400300b1107507a0b20003421482e18242c1c4143c3d940c60002c0707503001e40200000c504e82d6551001c1005640f540d030140000c04105241440092200c13605122494080c5040c103800d1300865030001c014440e50742d006000003084204840004e140203030700300b03d40e50014240340400c0140325100c040501100c941d07071420f100d100340300010071045603840c01c50241d01085100c00300000001950155901100071482c11420000d01c0d1140c03040c040304540b90f0090030400040500c0306d1035001c0707090440c4c482903c0103c3c05604140300025203030310002c0d02c000d68040c3e8401da2040030203445241c04d6200718499058943ea2616400c0c2039110906211090f51036118452000a440c00c0900206a903541c0682c007500f602002141d1040750740c6502200f0004042e196401c401c0072a80540c0d28900645c401c0141e10500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 777942697 1250 777941447 777941449
    0x30803060f0607030906030c0c14010b091305070909080408030301290901020a0b040215042d060503010b0d11120702010b010e0f130e0106180b0f0609100309120905 72
    0x7a0000411240a960280044400660440d0780303001a82d43c3d070304001c50a2818550101d9003410aa08042c220304a645000003001c0c106502c24541e490040c0c401600ca90b8440d0308000c1c0c50190120001d0140e403041c1d00c10400e01103a54001c91038a0310600300c0c6842c1c5a83c61790902e02c1c41e00203812240103031107800303041d0000ca00d01c5144d100555183c060101d06010311036001070744400300341c00050302103450840010210354951801c1440c80d40d0700707072805450f103803519864001088008101c1c080386c41d9442015140b080b070881c100d02151040e5480c83d1842e802e2203c0b0902d1900081ca04200040c3c840c80580c042240c00300c081c00302d2000c0e2b809003d40d50715001c170000f429105540403180c18011040c45100721703a102c484130040303000d1060780c0c00b66003800101e58000041061000c411070319443c0800105002071300713081715090744810880912050b070a481c10131206481c43c1c02440d921100030031500c5090704151880d820080094100050007001d5501c82c020502e07804070303582d80002c0c5144403d00ca1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 777943947 1250 777942697 777942709
    0x6090c40180504081206120607030606020709090804050d031101050c030a14061309110d030804050708070506040303110307060c0305090114010e06040510031b090f0213031401020403060603080306 86
    0x4907541000107005a04064449903503d206250111a4010701500043c40300c0d02c17040138005042001c24220b51140c07a2490009008003c82d018050050281c1e141c00a00704202e80200c8505a801c0220742d842c241c80c00c005c200d500360700d04400310203115881e01000c91f01502880381900c0f480481030201d03941e04c0c0090200c0c04a846005c4811002c408010500c401c41e01e4800440c5c46103100f090740003031000d94034180100e00740111040d40d40e02040e0120080101540595580e0003544104112080152101d1300981c4a030158001c880d000242440104040b2703105001a026801241090300d10f06078040e1540740030f0f90b405240c0d00000c00d40302c03001d100d03c0480920036103c00210501a01019505081246103900405081c00344540d03101c0c0040b945032201060384000459000140d1185e0301000b0b0b07840c1442003014841d01d110289045070000d40e41042d4000c5030703181140c542c2c41d8403070719042d41c0c1c882c40711007554100080c00f590300340700c007100103400e5200300c10240d4080c28a0940301e00e040d03c10000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 777945197 1250 777943947 777943979
    0x1f0312090608370c030f1b2c04110702040b10020a030e0126040c05060f0409020702360709080c040f0b0319060b0d081204032c01020606090c40 63
    0x340840441d4004c40c43e541c0130ba48c1039850300f1007586240030043d14803040c6151040c0c49440680c040c1c81c012980c02c90304114001480700500c00e0b9001d0005521400810181201010352680560868928100068131400c040e900b180306c14100082c040d8001d030a0410030003818404a82c1c0410083d06210501c0181000d142c010b04045501d1494007a00050052003070146111b003030354098020622404555905501e4081c07101c100700c41c42141d4030181c0c541e02989004070440c0500f040e8100220303000310310400c1c10100b40c0d1058401444400e03070381403c1c04003c0c40e400310100703020359990001f06010758041c494140041600e82554102c0701d5030b81003140460344503000f454410001c1c0194400040c54000c00d4800c15820000c98584a40d26800c00340c07066100d080181c640f0000c4424241800300600c0955140e03e00300b0788c219482541d5010610102030401c0e41c0041c2480030600009050313090304400401007021084260140c8440a1100103034080d62504400e0701c03800032102440000d5544070011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 777946447 1250 777945197 777945221
    0xf160323160206061905060325050304030e10051903091205131508041203091e0506060405060121060b0f030708070207060504030206031f0312090608370c030f 70
    0xd20300090f03080210040309052046c1ca004800c00301c0041c1142c0d0110480000d8540c1508504074190b12a5170010850390048034214081640b000340791407542403182c2242081101a20398a14001e62100d207503445140001014041544990359080091680354076280c0e44062600c0b416207441c41c42403482605c1220350003800900d10491510b082c0c1640c08180150041c0e080105842c0010000404401030103211402802d25898020a52212002c01d0010410035004006943c003607151a0204000c0d20800da41650000300c503106031000110501a0103002c0c50028500016565981c00c0c854820303070460a00c110701113002204000c80260000e14866004e05140701800b403403410014090f2543c007613400082d00a01001c400126001d20354a030140d1a80c0700c1110b007200e65940d034500300012010300c034a41c80c002807604400042d80390042c0482401106100c1801c1460034080e40400460403030811080349888000300c0551080c0d4030b41c030941c10030005599000ca442c4262190b00c0301561540c0c40e070302c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 777947697 1250 777946447 777946459
    0x17010b040b03191716060c020105060d060e0705030604060509010e162913050301180b041412160c120b041704050a0803030f0f16032316020606 63
    0x826060741d0007161600c2c20040784070b51003e014400c0c0c20007103a20015000394a0034520000f030010009582000d4501030075100f6130301480b480300000d404900b0f071941551500e81245241c440b220003d100c9400c40c0c42c044854604585d1281e80ea000064075005064805941090f0740d0030503c10110001c1c01840c55600d04c2c0e0004188a40141a40112a007040e104840d840c0c202c03441e00400d240035204042100d814407490a17511680344a14180d0341080a01c5403900ca5071901403800141c40882680c1d940003504028407030300c00d584032b803038004c540e00c440410807000d40170700040b10103040c0621018015400e1104040c1c002c441803441c1c07030041c0441d03d800070400b40c03130f00e0740c5e09000107030203c0d1285a2190303002001100048071050003100703070b00a03a04620381c012141900070071a204000302079840b50740100201d40c259143c0d0000f080400c642a1800c0900465015555070a54081e03041088140082c2510b41c240c0a03514540310300554098424140138500c25003030f409010350401801d44c11400072905 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 777948947 1250 777947697 777947711
    0x15060406030f110a0903110604091416140a120f05040f05010c020102280207030c120b0a0204050f1c1502030403020c011403070309020a030b0f010812040810180203010617010b04 78
    0x640303070b01046d10001b0304049640303500c100251902400c0e02d0040c405400103124400480c004405800401c660403140101d20f1a61207094071f1003080030102d588107014980e450301d40038400c02c540c1c0080c4804803407845a2103e181c10f2851119104031842a802540c2c039000e120400e00e801401d4844074000581103a00510264954131641c001040d070656048807209003071284918142d090188552028140901c1d01d80001303850420002240c510034410000e048540e81c1d1541c10308200d00890040300c0c0c02c030003420b01181240c00c01c801c4428802103401d83ca402c14910700c1d035800418403540d07a0242c58087d004800e0000305074040041515034002400c0120385940d0384a402d0307840f400024161003c250b03c42903c101591100c1d00000051900031700c400c0e20703a203003060070900e80c0300d028464080d06111348020440c00040d01819107003034518141c00380103010340b0004520701030700ca8003103d82d03840040c0d2219500187c2d002d00c0307044001c040100d046403054a00050017400c660742a078044d0b00036402c20603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 777950197 1250 777948947 777948967
    0x602030301030b01090b1c0303021804140f04210909060603200a0306091503030e010c0f2612060f06070c122a05030d030e031215060406030f11 63
    0x140c3d5505642c005d501c001414201d280024154070450306800000c8082c140442082c140d040d0005c0c04140070380018820000c10440600040310240d42d42c03000c10009070004034103401c1840c403425030401c0c018404081c0d0745081043e108411345501200201140c00080c00b0408020a80201001801d407814104030300b10055160048000450410580301040065100d05050003940218041c02c024201084220444241c20b00c041020340800d0300462810b03d002005903100703007404034440e0382c4654407111511060340c600b544a01d1072894404104811403940d0050b62400c000703025030070030f140c9408590307040074014044040e050400450050800b0420b081c00705810064440454114003240d00e4012400d00b03245828a5090786c0f0601c0221080400f0154003100500c00c0c0d0568200700c00ba1403d51030a803038240c088600440c62074021381c0050000da0032070451043c400381d102408101e03d004038600307040080c680d03511640040c400700b9034030f07070360640c6a4103503100d0b400d080340620101c686001e007001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 777951447 1250 777950197 777950213
    0xf0e12073c0b01210f0311030406030218060405061207020a0b0a140106080903071104140c0c0d03091a060a0b0301060926071a0d230f010609060f05130609030309060203030103 77
    0xc0405456442c489000c85d04161003400c0da11400707142d150540e601c50740c452400030080e504c565031a0a4481910109413a9441c00704100d804440303005110328580344180100d4040340390700418a45c158040e3b441c400002c12030001c01180726001d01c1c0400150f000c200007001180c0f20068101c0c0c0c0410200d50200021900000100c51985401284143c2c0f40e08038040024017400c5855031301031014002d1010f001c4035180c0d8130080c203804d4844d98240c484001162208400321071080d0b20281148010727012400c001c10401c0041500001d01a0610000b9912000411038680c001c0e402030340080c0d0b034044200315411180500b03140891449100502400209401e00d41c0c400302400b405510446442048030402c5451080f070340908000e01091100c04e07100140c00f5440e03500243d00d44c000200e010005903840100c00e210f64180d45040d110016000d040c800200e4005003580428800c0c0301042291104c0d000b980070741400101865070311442554194074000301582103a41c00b890540d4801e00060000812038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 777952697 1250 777951447 777951509
    0x71a1608191106070c1e031e0206101802070b0408090301061406030a020307021903050a0e0d120e06120f011a0f0301120606180f0e12073c0b01 63
    0x107840c0c5410401c151b4107041b00030120f10403501400a4a06d026001007540040300c40300c03c0b442c400d6041c1039198400e60243d898000071102c0f11071524502c4c0041c0302000c1d109440002c0e0641c0701c90014100440c40d80ca01d98074107015242985c64890109248106183c2405000c01804035290080385604042c804a1420f0002030722070345042e0f4001c0006070b08688200100200d4201180d01c4110035043c5003005001a40004c0c1c0313940014407060096011828064403190015901454244140e54000300446949210000c5d8541c400400c05c02d030044034070700001d010b015800032021007005500d4410010240a206001c5201054061001000d41c941c00010380b4111200800c00780c10760005454090300411454104281c030300103420035680c0b075061940c4034544074076000d0000c02c9400a200a226595030340c40080c9180400c080003da40010f50000130b00b20f5005d200b00880c0314908903450500058905250f02c0c4000c000c9a8035003400f40404a4581401042059280c8240890302d4001364111070b29 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 777953947 1250 777952697 777952711
    0x1050f0702010c0f06050702010b220504051e03031806040308130503040f080303060109061e0e0a080102070803150405251205010b090a0e0603071a1608191106 70
    0x201146010540e4041d09412403941d40c0704030400b4800d01d06140400052500b550038400540c6044110400da042450310440968159055a5a80c06a1266803405000c0c010030840d414002c0410442a40500070400146c10880c0d1018544038901950b00000005864550204591129013404080380d04400c0c26600700207600e410b01000c07560340c10018a140700e2948440c0100450b448000340b4601e010015600440c0242d8401401c0d954990f01142c40c00319080b2010b080210101400716800d02402505060071400381020030810f90310700354282203800600c800d031034201001040040c8a1034200100946074000c0b641040541040039001ca500e80b29504036410080d08910f403881c0e15800b50418504061303440b28240119a1190142c070840d40140344600e0040102e44008281410f0405401c1d22403440940200040c80c40e100d24001c60b102d81c4041e0308a180002c0024001019948215400380d50089581550b01d079214000882c000601024a10800c00e04501da0786008101042d51038101c50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 777955197 1250 777953947 777953977
    0x2040e0f0403050418050103110306011802091507050a0b1b04030b0c0c07090e0f2113080706031d01050403020703110109170f071e091e1401080c0f0105 67
    0xd180c1c40e055038180715541065030140e098a500700e060380855000141238920030750300990000b0050052560310321742130041461040400d643c41a12940301d9012f0040d13084001d02c043d1480608040c20b24090748800f10981e903a4100d4421001804510001c280d0480300d0604208015101080d03684214000c50000400150006010070f5402c1007007015940d5461102060b61445a503a0170300e0001400b1008000401c3d01420129418602010074680540f1800c40300c2e02e02c0213001c01f01d40c0840e0780e01c080080e8140e0800000c000c9240700b0b08105c640041c0c4050b4a0016038600080031500d044c0d08202c4419405a0400341048002a0302060003030407203500c00904c08004050500507129001c10ba00304d91a49009051510f80000f00029440c10381d07000501611f1941d41c030341d04040f44182d0200e0022021a100380801c01c03545505a0010307601028072201085401c80c400403500070740d4035900011404650020043c04a13050500030030398200d008032040080805180c1c006011405100e8040340e03240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 777956447 1250 777955197 777955201
    0x2d03040c03020d020607061e0f0b0a052107030605091b0d0b0403030e01020a1d010c0308010b0c070b18040c050901200a14060f0604060614180901081e0102040e0f 71
    0x5105d040a64403020f40c840c0c418412040081d00340ba0030714825400551240f810302c845a243e1040d41d104038504000044d2a44c041c45042c0303000e0181c0d00c2da1040980000112034160803007000d006200c0000914401e000c085005d0802c404203e252007801c192900c001f8400701c000394111790700c0c62000344540341d0140d9032007030564480c20b041c1c0041103000581c1140b1350002903140b08080e0710810344201c1406840c03200c0510300f1b242e8011070700400140c8005003c6040c81c1c0060100c22007520203409251450400c03a0704a03604c945090006400441d0b0709105003c02440000c038506c2d1600481d8402c006502d0281d003041550302c0000d05404000c40d808003025440a100c500c064018080c940c92290003004000d000c0c081d00c50076030b035100320441d07003160600b9014001c035000d441c003802502d044a0250751080340141a40a00d00e03803039070108001e00e189508075210249183c541100550090400d04080c04640520048a10800540344d02850551344100000d0290b20208800719401804004000c0407607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 777957697 1250 777956447 777956449
    0xa1404200702090f0609061302090607140c0409030f0e03070302030105040f17070c06030218091009230106030c090f0902031909031e0309082d03040c03020d02 70
    0x610002038610300100d5002a000d5591918200901c50a0702c2510308000c01e41c0d80340280c4006502c283c400c1d0b0751000142c0f021806910f03040f01c049040d801d45600051604840d540019255441204100d8822051034030071801002c00b403006800c81d5105440c1400013084980d0010012400e045c22401804000c40d44813004d034074104001805181e001d00204114202804c0c034400946003540d0803110005015040e20300c2081d24003c1d40d1344954440c0f00303515104e042c0f2500740c020750040125110741003078405100101d6500e41c0e2400d40540c5180c60108011820840c0c83d0094800211003004070311071420b00340404028001240c0d044035958640090104001101141c0000055012544040c0c40e480c2c00304007401550300660207001e0403629020105241e00301c20003a20b010482c050042040d554001146000400c6480304240c628a800941e00800f96a001041d42058141c401001d8100e4200c03600c460b841c8040e00d100071840c054041c00c602d40380d40d401884441e075020007809000401e00860131 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 777958947 1250 777957697 777957701
    0x5160221070602030f01090b0a030c060f141303050c040e0c19080601091b0e060a08060f060a0305180f030d0903051c090c141c020a1a130e060a1404 65
    0x4140d8804400d44d941c1c10508180d60180f0001c1c0100c03c980c40c6403d03072000c5949841c00000081302c0d482009084403520701441070301ea040f104c4c1049400d2214406002c011192910020710000c040007113103100c03035030039170411a00c2c0503102010799014a1420250401042c00001d00321101c94080390340121122050711565100e205e0341c0e218101c4c43c03203510f00200319442680c101b10400c1e004010394929020005004654040c503d09022380c1081003004140031183c441d0703010b280e0122000e007021490550150114401d603100c01c81880009a544080c4038540d2040c1d100511b8270080380c00280340c04008060310350b4681c426043d410600d07540d207100e50f400f054012000d4413609200c2c4007001c503c50b0f49140b1484050312205008403020060040d001c0f8480415006883c441800581884002034000107140340040b468a400d81c1d12040d0000300051410310750015042c8212207948040e1a902540c41480b42d0320320640040041403c1354082049a0315600007640031640070010005c810074060002c980 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 777960197 1250 777958947 777958957
    0x121e0c030711222a0c1208041203020d0b03030a180e06010203160501140c0702041d062205160f08010908030a0f18080c1509030a180b03010801060905160221 69
    0x2080001210044c0e112603081120300e071109000780f081403c000c20b0715108440403401218010200c010890f00101500c0c0320b0b5000d4001311000c004001811822078000030b1454104801e03080001e24004118003404089042d0180100f802c1c8400800c14184900040d48134041c03c03411095842401080300e040c048250410440c9030401c04455140b411b0080b41026a60720450701a40180e082520f440b048111601d4442250f1200074064822074070b9258a5401d180c1446905030481c0320070b040b86c400030480c14814003c40c40c0c0120340ca00042803402c200e00c501c0c0b2100d136001c01702e1a458100c40c213000c04c0c91002280d62000c82c00c080050401154084040107020b4440300b202c0c0d85d500000038008100103e0f000341954010302c0100d030380300b1103203000544c1040c00864101a441e001400403014560140041107921001c80701c0100c3e00a450b06894041074000364050a82a91140e60804c82242284131743d82c1c00c2501003072040c59082e0b854901941d208003142c804c980e02050214082803601d68079082e95 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 777961447 1250 777960197 777960251
    0x311210408041701022106180702162d032027092107060c090513020901030f0504110d0c05040f0501050415030203121e0c03071122 58
    0x303d800440900c850003500007403402c1a01c09004204519000c06480700070b84aa040244080a40141e02c51260046030f006080e40047d40b0600088035041c4824881e040050091101101ca11b101c0d0700380750901410000391404184850703104180041000b03141206150141c0745e502d40030f00d400c5c21010880d800102d1103507442d11402002811489207400901c2800303a80d0007001c65014801c60380c0300c02d072514035620454024a608210400c0003030f00310341010108065600300441e4490303030ba001259402c441a1042c0104981c005030341101136800d81704e82c101c002c0c00304030104018606a9907040240c1c0c0c1c0400010700c20039001000500b00080160241d000e400054003c0c04440c14005054000e01b10a02840d485181444115007610366401510011250000c4c01000070007000342d404d901690244c0141d0494040a44981400c01034507001003491903d0100210b40d42c01c203a04080d0301d0260910582031055140d089554200c03105180740071059140300d1400580c500c4070215003003455507049400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 777962697 1250 777961447 777961469
    0x20406020f15070839070b090f030720040507021c030b0904061a2205090a1a090a080a0f111c050c0a020909010510301e0b07031121040804 61
    0x1200001755403c003c0c0174024414031035044140c40f80c01d40c0e280c503114442200981603006100340e1020814941212000c0e841c080b40740c1c021a207014012a05982007210b0801c0540e11440c00e1034a01002c002da8902c01d000a440c08102e40311b503020003c1c014010190001d8181a1180711481030306d1456444408842d9005011040300c4810300c80c208061780c01c5540880340c05113401c0c0014168040030941403c0d0381e0f442158007000e080d884d0440368405802500720641d91081c49440c500050b024001000e0b80c034480d46407071200a00d4031200504008940380c1240841d00f010380a5250320326008144521103819092560719000781c80c0ca21842c180c00032902030b41c42210a030074004d0408041d0300031402015003581c02d83c6407645400c0010070903016801904460001b0b503280d2441d6244c03800380148440e00c078003410011000e0f02c1d80c54107042d1a034554240d071000051003d00c555642c1500c80d8202c28000018000d0170111023010742d00e0540c1e0303101c5110412101040002e07040110780c2003280c2c0030709021581 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 777963947 1250 777962697 777962791
    0x1502160b07201614030a0f15020403030e0a120f02100e0301021911070e040b100803120906010602070b04090b04060503030a0306091518090312020406020f150708 71
    0x506039520280f03900b1003804010b8081c0415030103001c1d00845020400500144a10380d2079035140c0354444c1d94420f040c0c801c081c2c80d90304894600c186000800045000780e640ea491448810100f12242100e5400500400280b058050009000040039400e09404440005401c00301000a030744010302d07110350300e41c15440050305981d0403203254182d00c070713811b41c0b56100c10007070322286225952840d981c05142000c1c551140001d0000e62446445a840081f16000c0281e55503200c0c5940d155801c000d880e240340c0c0c941074040050000e010815035006080e184010701c003e42c9000c91045a0748a5070082d40140c9850b02164101a1281e403c000024400a800c481c0d45990b40c0000500801075800390241503402d01c04028404000008243c00f6110700d0402000ba001050595a00800011100303c0034040304010018001c100c0384094002000150007070310704444501c88090904040642d10b034400b000403c180b000c41341d40103085941c0700011914180e40c10700701c0351407803110314449210580300102e0822 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 777965197 1250 777963947 777964007
    0x70e13021c290108010e070609090e0304050919050c0a0c02062107050409050c0a0e04200c010b0a1502032b06090b010806040615120f060e041502160b07 67
    0x405504890220001b00095254510074540f41c40c01c80c810300e000102010720500c030b80701a50340300407d00300c0c002046a1500d41c0eaa004603040300811140581142400c41404039500140d01400741e00140f022403443c034103004600003800f580c682c00c1c4041e01451000c2a5205103400c3d01c01c03002c6686000f039000c00d0381ca01d000300c0010940d91050180300b503003a00304004940c40d61031950aa403c035252540301d10302d21305c601c8000c2c00010124411908075a100c0d0481d000801d1481c0c1c40108904019940007003210301c0c001051001c5507503a5807000290000c22400321640301e50102c01d4644002c91881100e2050b41300c403174a4208410b0010160b035030a07152201c00207114129501c403440c928800e03200e03d03c85507240d608000c2151b00f5403040d41000440c8801149110b48109000400c08050020004d8017100358203c0100300c0300d480d002240380403104014031040c0b022040e00f80c1e210040d48581549003402604d07040c0401ca081c200006c20560180e400704204c540115009038402519a203100381000d0050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 777966447 1250 777965197 777965273
    0xd020415020d0305130303050703021c0204061404120206070c0308131418070f1b050a031b1101031d0a0321060803030c0a050c0a05070e13021c 63
    0xc18444050700c03460110050942c064000c282c400c098410f0803500743c0d900d584003074000d440e004111a0400d9801c000100b0701c00c240c8016500380c01c004200c0181c0751030074044040c02c0e00e1031591340402180000e001c10004103506414070b9801950582d541074071049207140c0010050003d420080c80d800e00400e403029035841150602003250884450300500560440504c01c0c1280381c03000b0804003000000000c1c0045020319103140c0400c60901c1e2100844640c03010742110600540382c110742c213030042c0380c0d08001e03d544480085880050942458a00d24050380c1e05926131241071a603e05241d100c261401d00c035155500020a8400050180d448541031071400914101342195210b081c1d200420030010b00c9005c520030f21301a180800300451440d203480c988006180c10a115480410200308a48285100e09204448019206000900c001420210718010b4402e00170075050980b1401d4900e030016a441c03035031050311503128145d06910003800341040a070b00307400700c0340d025114400d010314075820120304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 777967697 1250 777966447 777966479
    0x20d03030f0c050c0c010f18090203040b010608060a0911040e0103060f050117070302041805070e1614030f0a06090509030705010b030a030e090c0c061003021008010602031b030d0204 80
    0x10542040304800c442d0b401d40d100e00550003014015840621340c404103501684441e100f440242c00c1c460744070385902e0a010408000c6410090050340c004c8107020070488000c0c412405030880d400d08014901c0c09402040ca2800140718108015860740c2507407000a1200044030080c0c07860f42c90403449583c41e41081c034040d01c0c05200d23a41882e440c0000005070502c049125441910740c0790090600249580c0170407010704900c0c3c80348001028030140103000640f04025132401407100b141946194580045d482c021105003e0760707881407008402d105914018814101c0e81d0100d0940c203c0011078551a504000030075140d000024120728080510404410000240404a1042c002480b4141c8648141a00c1e561100e40007070100b080513000b00b901c0c0ca004030a031640b203002d0804990030800800d54082c41c1c22400e441d05c001c02303c81a0404d00650034078151120049415007084442c035454000001e5803881400800304c101110441c154240101c280101d803c1601148021740d1660f8545001303114001030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 777968947 1250 777967697 777967721
    0xf0c07031d090709180b2214100317071a0c16030e1509030c010e01051303060603140d0f030e0f011103070905100e09060a050306180f0106081002070609020d0303 71
    0x101601e00e2179001c105000300e03050804080d1000c41940c0d00c18140403111000009944400d98645018804204851220910402414078082e01283ca94281000b82c44042c0c10b29501c100c10800420340801c41c0c0782055050060504250784a560329003c4041d560301451035491017025195441000381548542c6c4c1040c0c401007224541c03490b04440d03581000754440c010300160103400c5034404214540c003da40d680c4003c501070400d01c1c03414421080d1030410140c550001c440d41d9a40c0c0748140107110000010a840340001c0c002040a00c980350380140600403102800000c164980c1d10444a4240a1201a00001d5084024081b5000100c4611101c0d0401c460010010305442400a4189000e4110010f00149620780100102c3c9040c103001140d40010103c03600210700f207a001500752810002d41d482031490b00c22400c002c045001c400d03401c100210b8804200e60707041c103800340190f00d0301203081e126804900100580c0c840b000e02c0c0c00001b501041c94003a600004502e40c120900d50150428100200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 777970197 1250 777968947 777968969
    0x1403071d010e010e091e0108071503050c09040518010f02040e0705070209010918080c030703030c0e010207050906042406030b0904150e1f0e060f0c07031d090709 71
    0x900c800111024180341c810303140010702411410b0058141184066007016001800007408050075000701359909003a4003001c2c03142c3c0886000c0200342c00e0b13104100201c0d0100d02d020f220a050001c5a02710f28000c161940e482190b40d180491301080e14516040510b08280e0000e1005104100a00d4000e420606c0303806204075080740003585441c172580c122415150700074035000099081c45414001081803807100c3c3c03035405034100442c01051914002d4494144280c0066954100515000b8143c0b6400b0880d40144821010000c03502c1e03802090380026030b5030640d01071515a070341d40001406841c860003517241c03078001032541400c01d040b51139502c02550096201030080c00000303402c0c041c2d0424101c81c050031082e01110a1880d0300d2407504151000600042201d203400da2440d5180000c103100d9800403d040d81d01c03065003107a01c00c144800741d80842a600010240d1900704040c0905105040c0002e04101d400c4d01c0030400088100411000c4682c0501221114a4040c101401005c00d40c011805020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 777971447 1250 777970197 777970247
    0x306040b0d060c171605042306120103110a3606080c011e021e0a020a0b1e0c060412023409181b0302041a041401080a12140307 56
    0x4803c51017140203801556a0b03240b40c01d107000030f0980352801c08040740000440400d03600045607103000c05040340064499203a6840c0d4950320b000039010b2092240c603800380300c0040c401c008070380d24141c4d100b6807200c014080300800e659091015440c468503621800c0041d01d0840c006c60398038400201e42010301000e8a4003d102100002d00807a510101c654110044c1c3c490342100c428000e0b0070602660420705401140c541589950018075080d5035904035020981c408169103800c02c034140500b250341c0e111031005501c0c10a24415040e180c1c03200400c090301c1c96131980740380040300d4401c100510394600b404441060b021407468046c100120b4440001403ca26944d80110701d4602e00e02c584800c030300080c80907820303a203203d582c3e01c90031801070580b0036501d450300c81002000d40c4907802a40c82c00c800300e4502a648154100401c0111603640c6210403200400310014005210300181c07119216400c45010303004081c50000443c0e03101c1d502c0c0c040504201000c0180801c9581100003c103001c080d4458101c0c40b6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 777972697 1250 777971447 777971461
    0x9010f0602010e1501031220010c09090e030f03041106071202100605100c0501060f060206240a1403030702060f030708090105060105070f06020c030703050703030b040c050306040b0d060c17 83
    0x506180310f104000c2c040c040c001000000d50711031b05140c0c55503640c00d0100c400200d143c0c5920394208c00340c51809680e5180d00618100c3c0754801c81c64405000342800801005000e0421190b503030251260242e000900000401e091001042d040100143c00500460b82c80c8040c2c6484500481024440d178090310035110641c1150a443c0902c2050f01c50141c92105402c070040c000b182c51120f43c032820f0f1620b56a032080410b2801c62480808090b10307040d0010082170400e240c3c00e400203441511400404801e24070000c205a4070451584100c33a0714030701d80b0f440600f1450009046124605001b94043c200040406200c1303003540245106140a48900d00542d40702c0e0320050903a80116501030000c0c208200380f00c00544000e0f800304400b405014010f040001d50303641286158449075044d8041080030400c80101903160150314450f82085c0d4092000d42c26000c0042e195000251070148500c2d140c502107030715903d50320200c071040c80e0085810700c4000904a409401d40003203080490348049034100041403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 777973947 1250 777972697 777972703
    0xc060c03020f07060b210c1c03020303010e09010f020301060c03030f0509120a0201020903252306090d170c0d140a110a0f1b0503011a0f0a0509010f0602010e 69
    0x100851080aa510b003901c51350f6000014040c412100740d00104c0d0000d65101d5864080740600c00c204a1402410401d035a00200500e608442e840d6a1810b10b04882d0300380000c4d40441528110343c030ba43c8031140d590b105d00c4c854601510728404c400540380e101000004002d40e004500102c4c071030180d1810003c511b010704044d01074a1044403c1d100702c2e403050b04240301c440b01000c0100213407021032000609108440000a0500d561008960b00030801d550034444c1e4030f080d0700811002850408040c5458004a00444032001041c00000d8820000132955a6041d180c0e03050b20340826030b2001020418541c0d1070000c0c1c07516000080d403110b0b1441400c0d8540160f40c003441c51203181c918252030b450300b050300000f0100c89440c90170400d02594001c82141a00040a41c44030400c05881443c55420702140c0024082840007541e120341d01c40d0b810200001c6113415040e40080c4c10100070356000c6d61140c03043c00400c032140900da002c40d4102250100000d001e0100d00d200800740c4100d64001c0c004240c500350b09079030b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 777975197 1250 777973947 777973957
    0x7020a20040b12121303020916080906090d08040206120a060312020703050a0b060d0b0108031c050601050913152d030b010b1c020a0f02060f010b07030e031c0c060c0302 74
    0x46504c5846401451a03104014042500c500310038204015141e40c041110034900303440c01b81c00000c041d0340814806030000340131a80b100700c080c0186000c0c94800161652240b800101d403090081c0c81000c1130549d00d440d4102c1e00716841d200c83c41500c60818450880c001e11a511098440e80750150074020001e00c04280d94085a8008e0001c101413003164031000c1407808054040f030360050158000e04002080100317514001c01d80140510788a1080c0c1c00d020b000d8440202e0b1100d0214078100030040e0750313038100c0182c6400c1901900e42c00c036072040c29010500200700c2c14095041420b404207002429034101a800b1280390030141100004242d040345c0307104003c000f4000109644c49090050050400c9040501060350a01e124040d003404284854012039118401c0b807800034914003ca44040d0b0740400500390040041d94800e0300030343c907105100600c3d01507500700a0802c507200780c0298142c0d404011010a80d4510380c0074010107800d040c0044c1c00c0841124080380c4550900344c2c60710405010303200b1342c0d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 777976447 1250 777975197 777975229
    0x2508221a0a030b04020c060c072a150e030f0a0c080d082a040e01031a01060e041505300a110907021f05061c020a05040507020a20040b 59
    0xa4107000c0d111405030702800c80c1401d0144c1140d42444102907540040190b18040c0c4865225156103004a04248241c503d000c4200b803548101c5030016180036440c038648a0485150a00304c88920000c040b0031154800040c01660785840360b50004201140040340328525075219020411350156100469502c4850804009000c00e92001c0026a82040342c0b400355920340f140d035010900d004482110720020f40164100b1251162000d005008012102e99916141155440040000c0d8909140200101003c0c00d10a005a40316401d8030580305d82d0003488405082c0c005d201a00303207200744005020383c043c0c803040700041000100f41c0700380c100ca020801da00c1d143d42141c400b9a5118462043c4684144090041c0b4118499201d014030107006940d000400c4a50801012070142826010010384041e02d410b409005140211803c0040ea1038090700d104480d03003968085881c0d40d075000c1c1030b0f0902d965044c000c1c01d81c03240d50000700401e07841302c14018520703941220b0411025004405001400595800c05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 777977697 1250 777976447 777976499
    0x80627060316051005031801020307020a03090b03152808010c0905240a090819060506010306230d0f050a061802030d110106150309060c050c03250822 66
    0x104e54500e01ca240250340c4107058200e404000c42e034040202e0308a0713100716090310068001d48884002c05600642150040246c00d4441c0d0840c03d102c000e145012103004c6d0174078403a40b1060340d00410a2030110b204105400400b03640c1803d02c1e030742c0001601824481d8100307800656201404652440c0418040da1200c500001c200203101103280d00d0841640300c0004d4001303010104800048109040202c15400200300d4602c5071010881c0c40e00809540c000740046040c9807d144050194104101c1d17641004255101c551002e00100030104260a502540150140d011801c000090000000b51048203900c036400c104500800c080310700403000c3c60940c0007035042d0403001d080c4031a544100c1c4101b42c0c4000002c0001210f60b51140007019025080f0328070008203480d40c0380c44050081511581c00041e40d2820400d2070519070320303a11038403031244000140c141001800b40e10700110241030b103003210950141c0e41c10b550310003030705401c0540c05c0000c0310b000100e800024080754801d80c085034030b440500b960400b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 777978947 1250 777977697 777977719
    0xd030b240304080304150911030d050c1b0d1e1101020d0f0e0a05130c030e0106030201091703040b0721020a030f03091109150a14030d08062706031605 66
    0x9078940704c2e84040c200380c1c0c135014581c2800704a10381030b2254035102440741c0100d01440307500b0014581020b030010303510006c1c0700e000d000c01407000310701190a851580450300349468041d038520014041d0400300f030b00505000e40082c4940002030466024681040c05043d4840014461b10b00484e90761340c404041a00141810142e050751390300800200449a5004110ba003030251600302040740346821080e44400d0320f403a05c1044104e80d406104001a0f422500e0003480458210b0300007801d105198820b0006010400703148000814091080c0c80107815254031040c0c2e16401800c2c03034010000350400506e41520100311488a1500002c3c4a0f00341503030580300e9042c00000241c098004204c0c444060711100300c1c182c2002e070142d844c0e4110324410000b51003009562143d160501c80300042503000079518403141900c041d061794000610020401c0c2034606000303260750701c6001c2030b0321b0300803528112036021000210a1090710f40580071482103030180c044813003489000000020480f0310703200345170704a0700d5504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 777980197 1250 777978947 777978953
    0x16020f03040b161109070201050601090e010b0a110f03030907170303060a1a2a01050717190b03150411061c020a0e1201050f010609080c040c030e0d030b240304 70
    0x30303d1243c114050340c040a0018110004200745820407159880140d54500820480b9a00b0440e141c000d0320040c13240307112560600d0500349651062081003014011072081294125030b08011402e1001c40d850b01752500ca080c403501041d07940b070041c010741c240c0140d980d10650840c3c80c0082964401da000030a012511454120f03100780c010b03420141030f2241c220801c00c2e001c032981d0140c01c1184506032840e000b21180002202c050071502c0141100b0204881c003070403212100d21032401c164000c0700c0444c0d54098000d003089054010010079440b180c0500038250010600080b400c8014822801030700c003e00500070213010407410344241d540c040740e5841844480f051b40645a40604140c00b80360400429100c103130800103c42d84000b56090b15a0707034403042006010140c642d803890041c0018100103107036604003055540c41d490040709240c041c0c7d6403103541000162007a0803246000c41c1c80000d031078501c0b44d072a00c01800f07422410603860181c6070302400c09074044c840c3c401f00c060344524014040c5c150380b1555 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 777981447 1250 777980197 777980227
    0x206010911180d02060d022811120a0e09011701050702060603030d20030c07030905030307020a050d050705090709060201050934180b130501081216080316020f03040b 73
    0xa070f41603812010901030702107100d666200402c01d10494070032440d072840180020700350f9070248001a4040048800260111840004a88a414080b08600b0391150707440358084440e9504070009d6a0b00a004000019a80c15115003041c260306590000b44410355881c107051741d4402084d21500d81541c0100701c40000344905d51301410701c4110725108800501d55480c102d0065810540d804102d150340000c00804154000741808010b02098002d1402c084e800d400140d101c0840344a16400b51520907121000c1010900c6141e000e0302008141d03480c1400d00c0400100700903018000e1401540ca0903012803d0b072400003c2c86144444003030000007000000e401c0103070700c01c007020007400c80b0001d07410400b045280c01e1144614143d0552000000e08440100402440b0030398080503590203490040140320702c4a0100b0115400b03036064080b595966516074028071a404030741c04c09401402c01105224035028006042c0c460051035a08444407155403c4a641e1240324a10448603061420041c40c49000341c90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 777982697 1250 777981447 777981469
    0xa2d12050f0f1b0c060109060e010f06090512010b040c020601080c060f0315010c24050c090306061e190510050a050901031509022b0e1207051606020601091118 70
    0x8600b0440c01d212102402c5454000c01f03800c078911440e1100c200340b1602454240281c010001241c003819600c2c50201c2c0500a501140500c1d400b68160310b00c1c42201131401d412a901035200a0001c0001080450000392500001c0c010410b41e401411241d500ea03113408401d4601458041c48000e2641d22424900c000914a51440390b0621260183c08008201c4100342985503c0c24112080522441e48038981c04959004061000828091204440e241c8000400039400081500e10800481034100c44070050200410300581c0071440f6038251112101e15460700080b2101902c44068480030001f084d1001e0003000c040000191007845426a290300c81c2d00110300d80d5940c0d02000016603100ca1026003640e0204110000c190034162403040240d51801101520008401040002c0d2024518240d01ca41c1411504a01c103000428040107104080c00303541e003207800c1c1c03003040340f0b071b00340c1d5401c0294843d0f4007480381030042d501d044100440814200100d6410040400716190400181d03c01c2010080b45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 777983947 1250 777982697 777982741
    0x1020708160c080f0303010e0a0c0e13020421020306010e0402030615011206081b0a060c0f0c05030d080f070e0f0d050f19061b050a2d12050f0f 63
    0x2d22400007078002d000f44880702407041540e0145541c0c0d8144a80e01020707241c0900a09511403810811240c41c0e607105520320416081203800501043c0c002c00120080e01460b000042511540006a92904001240701600510035400d4804581e40e6488020180d04101e8003e501900024005090721014190203440704005040012100c5107906010381244d0031608a2042c0b94464040c0054096580044900442e41240c00e001140e081607c001c0c00710f614440004c1107204001c00c03400401644103074800c040e0070041d084452060078600000c2072140c0c281e4001050519040116140c0d52150b070080c62488000b40411070000492814000d8100e44040c0075111400380c58400c1500301d80503c808a030000002c0c43c04411004a820840221980310035003003d1581001c05003621180c1041c241c0c0d100038164200075560803c401d20358120b0002000c0a40d80b003030b0b000703014019690f4118bc5100c00d044180c0c942040307240d440c0600707110b103034600b03413200040c4c0c085100000e0003c4580419009403648 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 777985197 1250 777983947 777983963
    0x9010509070c0602030c030105040b0d030f0e060f0712080112020604030f05100f0b01120510050409020a0906060f142b0204081906230714310501020102070816 70
    0x80b54880404a800c140c1d48000c0208000004200615260182c021200000c403545540150703503a602600070440401e0030003d0042542c0f20304041d59a41082d95280484c040702c0c29552070240c60a0740b00600c2250383c00c004605a08008112003031081d1352507031900c0d0f001d0813003480c0c1802c580b50340903d00d010440884d02032189004107a01004140100c0810f81518017010410121200015081c419a813031150720310382ca8071041006501c810111502154030549000030800700c2d90000c2840620160803554284d801d00038005820b5900c03507590b0103c442e07982d842d1010f2a4400344407a00d01c2c421420b82c8425482400302090343c20100081e0322240c0150040010301d05580d03020024100100c4100c0c0e0704036100036440e0503062003a6030292865003043c081300c2941c2000080080c0c0c5000001a10100c01c2001c0c000d6400551206a0200c03680d070820340160721942040031420300e00394604034001d0a8200392803c80010311f540140269181503038042e03052030400c1045001c8402c0d241e481401511046 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 777986447 1250 777985197 777985217
    0x11706041a06041d1506030a11100519020f010b10050d05220f02100203030f0f040201121d012f2503110610050a0510092303060a0b0901050907 63
    0x13030000e200e048044901d5501808001c080840084c0c1c80b0036005000f42c0c06034000c00590800a15004084002d0072421a01c043c1c40c00481701c403c52706030080c8101d4032209081e03403103100e00340703500040c0d102c0350200280000e000520444041c450880c4c81101000b01140c000e000201c105140c0b03030420303a0301a08955007034600034005100d0b201d040110320010342e41243c01c05030f01c0041d403c00d02a12481c4070300a0009600d9810505c036003005584c001410304500d120190f0104045a11407514400058884101400001c500300100c043c87d042071034441d0900e41c0391001e11102c554100c4003440009461074070131b40701128640d0349031006034861501c58410400c45961503040d800207042c80c408150107070b95081400c48007040f001d450044082c03c0036140301f40452040041d40d84d03261495081d0f0300c0c04d071060020982c1a00040e502e6203003642026140c50312502aa00c11400b41c0b0595280b8088110304541c103c0d201d05103d00304880c1b800340d10640002900c40140314600f0308510380c036045070891604280314 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 777987697 1250 777986447 777986471
    0x1231060e0c040f091704050916140a1d0a0b09150405060d0c180e0a09050a050d0e01031a030d18030f110907020f060712060e0f011706041a0604 63
    0x3d4100c403c00c0303101d066440070302200f4018608480c0c4402145821007620b0b040c1001e0000311800b40041c040c102e20b10750946000d90b59403103803001010007031303007116401d80340c01040301c014000702e103021100c9201015040c1b108800e80341241c80002100c12040781c0601d000110014001c0b01d208155150340003c404100020b0b168a803000206102c214003c40018600c2454000401d020040403980400b5a040319044c400d00c0c50180d1070540000300707210009030700403070340c80e044c1d0510304807000c0076010703001c0d0000c0004810740024030540c1c002000d0b40c0411190058085410f20a80c66844454250303102669218116000d03a0171040c2c1010620001402d42d55645e4408100420050f000c0380d00100000c910300444c140380f00200d4004504e400070300203112a440d541650346ea40140030703008008008440c03110800a41e80b100c0b018003038a4000e05654a8010710184000c1701c28821014402c1050810065064000ca0200c0c0981e6000700307000c1801040c050301c590364a1018001c02c4e407066552030b1403400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 777988947 1250 777987697 777987701
    0x601021905010e06090721060e030706050f06040e06060d031e020d1d0609010c15060b0903100c080a1112040609020406140a1e030204021231060e0c04 66
    0x2a4881c0001041c1c0000b80c070001d0b410001c1c0541649001d0340090410b01c044000341360800e84400c1d40103441220303c1c040b0300303103840940f04010000c15640000581c450902000e41c0041e407141182503501c0800741c4501050008481d903210301041c05800a802050113494650b81e0f0000c498000d01d00905152000c050240243c04002400c1b400b6900680c005980750350440b6408540c144d888030706a40300c440c240701094041c45040095410031040c50882d500300880400b03a1402c10000c500104031094452010333600c03591007242558420b2044240070240c1d1840c45c000d0681204295645044540ba100781c817802034111244c46850b4028144210305410b4a80c006c0184618061040807954108034018481122034a8000380d038110079851140760b480d1110804902219118895001c43e0080042e107031140003000d0700b00031b5100d0b00001e21a0301a0350b0040145000b0340c03c03009001840401555444480788840c01940c0880c0148000c65010440c00da0245600d0480c860a07660a0500300d0b00041c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 777990197 1250 777988947 777988993
    0x130e01020f131401020718050402130501060c0606050a050a15110a0c091b0e060705010908181306030f060506240d1113090b060706111b011b0305060102 67
    0x1400341d03440004000f0400707002c95615200748280094080d940c107000c203121244a04240b1b04500c1038442020400f103482c0c009038115050000e0104005a5844030b00c000d0000f10582e106881d41405c2040c045141d1920310003450031680001c202607945490a0304082d1440b5058000c02c061109960051010f40814400040c8031031240c10b40001c0c0c07030b05010f546001c95050440c007405880344814209800e54000c80d1600a18200b1031b0101d031203154502d40607014101300d040041c200740010445c103000280c0280300c40745001084440b1103541510801c00401c868203480042e182e0488900c06001261180e4005500880050f160000c0d018a007041d0141d491110781c8642d282040004102c0c408503018030860b000d580d0404606484d220396501c4282e00d5244074003488408640e0340e90940305654604048401c21035001400f0b101c03000c9050b92aa016130441892581c00018551741099032003010f20507100c0d00b030788405041a004182580440091030014001c40c194844c09001c6004a12414501c003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 777991447 1250 777990197 777990217
    0x302040b040522181e0209041713080102090a230607020d05030a0f0e01111e01180606030203060a02030c070f02030f030d020c30030603120703020604060b010806130e01020f 76
    0xd004c0000b9292100300c2812081c403481083c5400c1d8a2080103907684a45250007640000c0503240c1180f0905000200348500301542c9240c070104500020f0110064000d08000c00341112810b01d00340c2d491101021030303501048445a00298080880d007946040d50141c40d00c07500103041d4a4a66040e80d603642d241d54003014140b8049112000710305a400e070300c4045ca00f028002841c046c6002059442c400360361760817000d1100c17181c1d864000ac0702111070007544034a003040d920b0102045080d41c0e078240f02c5d00030207450106038000c0c082c0c0b0000555045540c02241c1c0074090115440c0c0c6402c0b080d45510310010919070041b40d06015820f2102080042080030b441c2c0e6910644005a5034010000064a0a4441d1060001c8507410300345500c46d61581490081000d11821100c0f562543d0f0200004d06000761402416001100072610368141603002031558800ea05c543d604002c0e10030298015290107008603a083c0c1d02c00c49101d18214150000d1300000d9040c1c0c00a00058201105c8040303912241c0c00a0040d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 777992697 1250 777991447 777991481
    0x50405070804151817130f080f07050d03031a2d150a0503070207030f120305090105250c08030103080705070b34020306010303020102190302040b040522 67
    0x301c000d0014803c45005080d0200e28100b0101151505804018896090191914001c03021600310480c40b007048404040d081d11000d140261120764542c02e68015000c0c5840b20301c540c407106c03d02c600002807101c00f901d50091212500039201d0f034044015100319101c140d621602201a100c0d00d07100c6802c2e0b000d1040e0032440c225201c4508140c00020205000c0045204e01d00b000c001d001e0b0300c031150080750324001c041c0c40c109650340c1c2c43c1c8a050b07191502580c402000080e842d0340b050140108640308482da11605d03a07040c4a40c0e242c0f2015a07098800030b076410101c070000d40f00480080c5030301850f003e101c1c05881c1002071014105032200c00e825002640b00341d9803008009500002c004051140001030308080c2041030501e9070343c10611401300e119030701540f9906001515112240d62106500c0c00080e801011500c003036840b441d000f4040e4016811030203003070045081c007140c0c1500038020f40c0d0680c0e4480c2003050425145c01c0802508803d41010080e55800c205000401c10b07209000f0488410800680c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 777993947 1250 777992697 777992701
    0x3020a14011d0c090114031f090c0608071e1205010305030705010501080d09090203070309060f0c02010b0d021e0d080a0504060215040b0a0903050d1805060a02130b0f040504050708 79
    0x11960b003148550b244a250b400c840c032801010368569514038151054a56000780380307003202c0c000c00d00e840d1030182e4042c2101005440e442250358290083c00c800d40c441e115045100d551138000703403031004081d98810046140c5140c04588916032034403107204a012407070b11440d0307881142c1807901150400c8e04140da01d03400c001194014000c09001d91801022031900034041c81600c8100180b050610b40101d00035142c0020108003018402c0e0084060176401035400c021300402980b02c10b008100000c010000365003001341141b010b1504041c40c2c1c000340c0c1c0241120803010f419044460443c60742c504c00b05c1c2c0c8110100e040c100441c8911000c2e06101d01d00b40c485990321414010081d14154060561100c041d110004100000717002200c0140c11440c10000812407810618060300c1c1401400c0381c0102885c45c4c9007010801c44108440e1801040c0903d0075506261102c850f0a42640700d00040584050300d01d500811042c20280008c1c00c00c1611011a14209515040000c090b120243c0e4170400140c0034000f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 777995197 1250 777993947 777993971
    0x160803091b060a03023f0105120307020909011815050a0204060e010c050106030b130b0901051509090a150b03060901060f060e040b040207080403120e091303020a1401 73
    0x10090030a80350710460018012540005106842004021010181c020482100d074003202e0981c410025204402c0012850080d2a0a020300b210072004040101d920400012581410b00c0d2000344500410042d5140801e2902440301c4004042c007041c140750741c2e900f4000c0100c044290821141031040c0e8080d1030080d0401580026600064901c4091600c104401c000490308071100000d217001c00c3c01c00800605407420800d0042032103a0028000003e060100808801d588030003482e03140c89922074107080c0e00c8032002c40c1c0c00c840080310b0242c3c11884920f2030321098504002a958090540780c1160312a4505907554880e04000303018555040f500c80c0c0900c1e04601d002d100d8603a00500305402040101d01d40514100d28048611481c401d22081420b0b8503d251115000f06000e440c0262081d5a41c7e041482c00c1b0032164064801514420742c40010700486074840d004401d04083c00800100460321410110a65520081c408609520806020500054031b1038a1100010302040000030070300038900c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 777996447 1250 777995197 777995203
    0x80604020915010206040f1112011b0315170f0a08090f09042303041707030507120b04151803030b09070306030515040609050604050c21060f0c16080309 67
    0x341c0302c5058101a8400341d21682da00140481c0d02c1500000c101c011480e940c00d006604482c00414641c05c851100302007220082c05400c940c40072400326600490541d5402003c9084641c151103249007022111002c010b1840036203c200802ea408a060702d0b05880d0400d9902c0c40c01c00e500204452500c00400c401143e450085055041d4038802d840f00f0502d494180d8641c030300003045c00d2100440c01070600c40041c061030204203440c0079105901115422480c600385882d500c410500c8220741da880b4444012510002e046964491582c0c0001310614603195aa6500540c81d202d020360458940d446045440403000c1558880c0098000d490000780c0c019000d003407201e02d07800140010103040c101001000000d00020b0200703d041d5071030340e048041d9210380c900003019050020003d042071190805010030b001c008200c210f681c2d441202c040c035410850035405402c00315140d02010642c6c12001c006018503000910166008403800c6021740381c40c504202075100c00c001c100e401d4130007550110400111038810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 777997697 1250 777996447 777996451
    0x30210050f030f0429040606060e03030f0703121a01021c0c0f0512031009051e040602160501060605040509060414010302010c03050d1415120c061b06010806040209 72
    0x985452071404800ca2201c200500c0041d00948044040c41d000906100c3c01d02c212412040300e40502c040d00d4550401c0310b282c03501e030070795050340d10600d00705d00010100e00030074102000c600f02802841c104054003500c0c50f0240c108220503401d1000d5130000109002c810f100d84480c00c1c2c50480d80d40c040502c0403000a01e000b89800030354403890860034031500c0c0a5005014190541c0c2d03c6204d190390501e440c47c10034102140304000042404012007482110010344061609641181c1070410442d904d1615003c842807440c3c285020045200f0045000304007a0340003410a54078005a86000384403583d5078608445403035200200050300840e0a2102d440c0c00c480854005104607414003410000c018550407404043c032000703041c0300b000c03000001014001d03c01d85100700c440c0306040040c500980580114010101c2d8000c000024140401c14586020402d0610a880000007044400444000d20103603a01c241c1922000110104e9450070780d81042004a020b022050003038103240c20f1030707c10300c4051a40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 777998947 1250 777997697 777997729
    0x60b040c200a08030a0c050d0c050406020f060106140c0f0d09090612080d05091504050a12031401140a1707060e1e0f0402090d0c05010210020f1b010b030a03090302 72
    0x8001c1000000c0f07050f00d800d4075082540310000040c008a80c0c81d0540301380c80f5802629042904113900644a1500314000d807045076026001ea400248807040440d031107980902410002c12403800e9a50444c50218001d0401000d0700403c84460b15248580946010903440340e000000716101e0081c0072441c82402403400402d8001d03000320380851159143c000341d015a0a50500c4070b9035910000f040000100107002415108403101c04c81802d1500f4100d80304c0f0307469a81030b2102d8040d02e600000342c42c4030348260851442e030342c0b1030b10740c2c2c2b0f908140c1502c66031000c85031b03c903600c10b40070840450004128180041c580c4821700082c80c085180c0440074020307101045641c0e03c603001c00240410f07201000340703a54050b80030446022004007521000600240100c0611540054400d52030703100300248e00c83c2d0641520400d1b0200e0755400e9882014009901c5040c1c2c464a80180c00e0108940c080d03c440c2c2d00500e105401070000c03a0106031580840c0c508401020306800203050b0490410960404100504240b00c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 778000197 1250 777998947 777998953
    0x10203040303020c1203091203120f040f0b1009021b0d02030a0507170d110c0c030105101205031e13120f14150901020901080a0b09040f060b040c20 65
    0xc555100039407508072982d650350081404c0d40100040c8501401201e807d0344004080d030009110040701c041d82d0f5080070000307801d0301007118041112207000107002441240e02c404002210000c075a9800385082000e1310100b450040c075000031a000c0654009000006070301844004e004128480403840e294100440d2029900100580a6620751100031901013640000c65005c4c2c40c0502c081c2c2d40c00c00d210b92415118400c1c0791680c0f000c00401104002d0020b070240c48121601d9400c03142c201401c0301c6c0c0c20f403804010301900601c04c10001f9003d10201e00307072a02450603607090120780d59206806850303010201c82d01d180005181586003804120010240ca8540041c074000d40c034568441103441200c1c07001800c0c0d521824103c200e41002048502e45c6c140c0142020511810110b0100b4081d4004803e141d010513150310000740f45c45000c0c42408034259008080304107544803500c40c0920300c46914820ba90031902d8208208198459002d0440000000e0340e030032808580800d540c1280d000f1403882c160082d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 778001447 1250 778000197 778000199
    0x1031401410103052e0609062d090b010309050712050609010504050d05030c0c12031915091e050f0f071e050a1107090f0612080d0902040618150501020304 68
    0x514001114404049000c5c0c0003604401c200c582200c1108007031018100280c1020404964000d04c2d42001c4101d0f18540d0203511420301c0144020304c0c2058040500d03983c80c9a0071030400c09500c4a400c04030030440181000200005541c0310182800c1c4590403211900301011200c03410040e04100107603008401400800090a181e43d68940300c158101a8604000e000b1000c03900c1c1100b07981c215040780c41064111510b14040716000130300743e0400c544010000610440b440702c84000d6018420321515200c0d0810079103800c00c80c0c82c1c40242403050f0130118184181184180c40d080500c906802028000d11401c200e1901076040040c600b801412402004228040b00c800d2041200b084400d401c0305080152f110b0b0040d020494030303600700d82c800256a11801364001a80c200d980d110128480044405008081d100c6415044c03054550100400d03840c0c042103d00140946035010400702c510007040032540a40d20722400700191b81c206c900c1c0c0700382541c2d031040c60048094004010010a02800030358100313 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 778002697 1250 778001447 778001453
    0x6010215041101080601111509060901110d0c0903050a151b0818030f040f090608070506030c0c01090c15030606030e0d0c320c06070b01031401410103 66
    0x490b802001d05818809084040b6605a0084400c00100240342044a81245140151009401c000d030741d410414059480405c1c3c40c0c00c8180504070940c1c1d00d03640410700d040000d100c080c00400f0f20340d01080c1000034140020000440031301228414900032200c0e003041d60990b02c4c60800320340446210421016080f0088000c0d036400c69410382d80000544003852074442402c00150951290142d02401c203080014041854000d8228050981e80301650410105484040356955a5020300480342d10034401e100081d0702155110060034803035002e20022900c0005642d13200030010311600000a051414001642d04642c18858280185a240750a02070500f0310505030f034583c1e04407070b422004c000841e40f00703000f40900800d0301070311804904148500d01c01b17002c041d503040003c5c01850b25294000c1e910b03200e025250074001d0392120742d00020310868a034030715a52210001a20350508030030b03548500c5460180b2001d02c028900b5007884001c1c0ea807a018000101c450705841c43c80300c0b500c002d19614018804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 778003947 1250 778002697 778002713
    0x718030b07120933020705120c0a021f081b0901030b0d021806090c09090105010f110a0c0f06030504050303040b131209030b0708130b060d060609050601021504 70
    0x1118060414040c84511030901d9800761026038006418800e01d0540890504c400040160070100d1869074048081441c40f00d08040c0c1c41030035006005984124407040e88255400001c0110b00d41042c200d0750014155400f1600350100d132400d0505443c42e50150800e20b54200b859181e016030403034040d48640b25041d0b2103100c02d0080d6011141090368800c004071003903e541c1c1e012007100760001c1002d14410292100388030100c00458015020780084000f150000401e1001d4403a202ca0080610080344c0c00e0000460300e01c48005c15140c00c100510f260317420015000d00103000864020000b250030a81415140811580c8503800901050718080800000c1103010084e070b6041503105e084204140c40b09150110741100824001e070002d200d28074030103c0c00b0340010110b000c43e8440c1a590900da51268810340712010200d407075002c0035441e49003030800182203440542d400080101a144038074455160201250700c00d40001c0d840c40d0f076031018406190f030108122111406166010b1046142503504c24003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 778005197 1250 778003947 778003951
    0x121d010e01020a0b06060d111e04030507030f2a050a0506040e0c0c070b1207020615031c1407030903020a0f030206120402010302160605040c170d1b0204090305030718030b 75
    0x4013002141d004206190fa4103001c88500440142e0309110181083c0e0090480364046107aa51b4056003001e42e41c2800c0e5560010340342283e4105019010303162940c1c41c2c1100d45580000101c58034003810410035416100000840c0f803488804002e20030b41404c140501946002c0b50b009140301b0f22082c081004201081101d142d0f0100c0c8041c80c0649030350311140f00be0f1602c05160044201c146004c10001004078102d40d002c5c0c80f0f403905500702c44039034a5000304108001c3c5103540705501038025002c460500401086442c0303031614549081505104550021581600041c0c0d08800003801103508000354a80944d060303010342100c18926107241e203942c0c0041c40e10310640851190380342d81640040c080d6070281e03041d583ca446000006404400d0a071400b000240811a01161601c52050307001c00c40c0c3d01e05480b421042c07030494005101000d0700c000c058403901c101c03801104034041403003001401138032240a03640003144251980c94907800c2c04500601100ca601101c1100381d54045002c1000c03c11400c0115 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 778006447 1250 778005197 778005203
    0xf0504050d090b1806131d2508040c0305070602161403061f08010507030509010c0f08060105071103030a02061608070e040209032103100909020f1507121d010e01020a 73
    0x4184c04903807401140d018000ca0408a9070003401d5203000a10070100c0001c44d000c20610500700314103590b00306520100405050b100340c142440c0c0e80c440040740b400750400640081c041d01c0e1160a0300c0c1c1c0c82d40c50306d1500642d9000300d00180c105c4440d03402000c0707252031407101402070200c10050b40320166002c2555284018103e035109000c3c807511646140e060302002c005858607000030b0090b031034040702c0070b0007803c400d54080d48590b01e0a000c80c050315118001000c060072003039842c14150384804004540720f070001d640a403200b100ba20400c0d407070341e0b50410080c4440c5001d5005021503241102c0301a81c1010313403094240c2032003030840800017000e5000b14821208201154010380300d1450714007291400c0c0341c20050300188030203180280f5100b2803503000745120b04001910302d030916888071440c005640304c41200a41040c0940f01d140043c1c50550700401035000d1680506081140c903844a69440703840601440100d00e141c6189103450a40014032000b5140a0030032152500580700002d698082e180380203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 778007697 1250 778006447 778006477
    0x10b120303160516211d0108060919090b040c0f0b0d020f0405130603052e0b041b030603050d1e0e01030204091a0f1503010314010b040f0504050d090b 66
    0x10110080010280050554101d03518a07080030031074012a13603040345c881914011032910034126118891446940343c240b10183e5175130209444020502c0719070603020b88900d06c1c2507010745110103526814461704480ca406245604000e0070a82058a140329003900440680800010240a4004174004a034a2107080500c01a5115a01c1c0012811b5000e15005180c0c403401d410189044042c0d1034101e8403e0b280114141c074070150341640d02181c1d01c894891760038003801c0d200c00c41104016484c0e10802c8a100050030211395066040e0f40b140001007034045503c042999407101f401400310800001e04225100d08180c080162444c0e44042d041d012000300300304220340341c9401d900b82d92082e0180c800402d0450001d2140b114074080c40300820115420311130007004540c800004500c1c0141c5c4a400401d040c00c0389501d547d00315220401a45030b640504041503403550140ca1454465120350100781701c000d00d002650742010300c0e045040c141c0c0001c52104103c40250103004264005045039440300b444080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 778008947 1250 778007697 778007707
    0x30303070e060706060e07030f0515120c0303030c070605010909110f01031409010f0e01050c0a14041d0402010f0c0302071203020c0a260d05090d11040608010b1203031605 75
    0x2001c6120f082002000e081c104000003403020017144016009006603107041c002c2810000ca88007c84c2d4044480c411080004802e840203402c1282034907481c180150161604a6004004a032a584c01500c400b100d540000a5070301c14000715110b03403409040141d00c1405060010f4440700a082d80c0310341803901c91844283c8940a9030b00070782c0320b401155890b008001c001c0c80d114800c18000c24035840105139250030b0203806a01600103100b401d100700c0a01c98410700380780e07603100201c81c5180d041a010224003002c100214410a8032401139540f1401c4154030324151a0910004041400404201003801035400ca1400000c5d0041442d400352990900209040d03032141c03c0c120314160810640d00d40060726040041072214003c920780c008112000202240c46003040c2d111030396091102001d2002840c20b1082c003070300386040400740c2169401444d021903500460800201268829401100182e56950340b20106d8206104101000c0c1003900c040c40c02d5103030440d8000306101580012100304100058 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 778010197 1250 778008947 778008949
    0x206010512370c030311010b0f0607030f050f0304150f0b0904020609030a061a09010b071a0a020c010c020601080d03142205030a1115280e01090807060e0c030303070e 73
    0x51154071994101910041c8a513490501a00d0312044c0c034034000e141d508020030180182420003811551000181c040c91901d9100e4508031f404440d002100020401e007001000000c0621401460040d800744c013000b210b00340390090303040848890303240e041452070400c0c442d41895179560100740d50041c1c0555035165a081e50030000f0782030040d000f400416807803400710100150203404400c090f02d040207898240480e40c8030790440e0254003841c2c500410000c10161501c02c0388035501c1c070182d08540e503c1400750a20f82c092400030b00351882c0c000341400590003440100418402080244019034881c28204402c1e0540501101c141500800c00007c2a0748010030180c00410081c0c003103d01608542035a4899403080c8008155420b20050751100d44109080100189003c0e445c5600907080f41210f2840100700030125001e000c14206500308480d079580703104140750828040d204021344550250b40c0e031200d00386004412a045000c201540f907200c03018400b05620004216504091141442207a1070041c1e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 778011447 1250 778010197 778010293
    0x1d0a03030c051314150705120c0115081f06050a050118031b29070b06031608010c0201110408210409150513090c050111070e070206010512 61
    0x3d008a1102c0d07660840000e003a22002d1381400c0c207620b00310b4842070440b1079940006118050540058100d0300240100100c1e075004000500e032954104002060320fa845206940c681280c0c0d5110028607088101c1d50039248441280c1218451107d4a003046884e0078a00840c0b4035064a00030103050080800340050a611145450b200866021018610b4040f400c07210501d140854484c603e6000c100854608001e1940400d2008503011800c00c1c60912116459500302c802021300050342601034001107130044455a0110005445c98600225041301c0c0c03c0b60083c04c4a640c0d00ea10144848280014441c940000c034200b040c035965a500c007002c2d02102151041d89100b55440041840d00d040301d0500c0407003c03004000102e4204480810140e042d01889d0f10594ae0403c50041401b9180b0384144403030360084d20b41c181c00140c643d00301d9060a80303c60048200400c16543c810260340250010031070751600340300040f101800d90000c1c2299880d556400001c08108042e4890b444810070442440c020b110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 778012697 1250 778011447 778011457
    0x180c0705010e030d1d060c070f0809090903221805100902070b01090f0e0606010305090a151b091a030601110303040b060f03010c090b0912120d1d0a03030c05 69
    0x950183c07075403850880c3c4032100400e03e0210841080010164005010030045803083c8201c2c1c54040c40c0b841e006680c0d0b81c1700040d9010b6402110011814041050107444410f030701c0340704204080c000d5a6410241b40244c03903a1400e04605040d601d8100000e011040c1320388100540540403840c0410b4075211160000c079500000e800c186605840804d0440600c20705480f814101c545100081007480c2031601c0580c1550310b0491001016486400440c0440d4401e600c034a070300240d0380081d100e0101550b621007100110078281e0220558940da03482c09140d06039103089800c8030060828101491900c03129114100c001100e04444501c00b000090203a40a4041000c0841500c03040c2d942c0c900c3c2614000100c000251a558050300b0550102641410144601c840b8540223488a000c043c2c5400918990303613001c040219002402810381d942001c82c10443d01c0c40c00848040c00e04e85448400b00d2907000c42d018400030605240301507600540d07070340c004601031062580501d804602440580b2040d5114403039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 778013947 1250 778012697 778012721
    0x30501080111160227090307030f1b0b07140c100f021201060c020d0b01260f030429190e0108040b0f060d05070902070303060b0406020d08090703020904031d180c070501 74
    0x78107001c105500c0804401060112721945420140030050402103403614400944141d1303294445004001048080c1401075000242d481d02c00e008070080d08100741c482d00990320b0041a580038030038120b010906030040e8106200004804c5007040c100745400e4840070300610030002030107001e04182c0d095450741704040c0c600715003000d1070201130b59498110002c54000c100c1c24040700704d4051614444210085481440c03480d803078000318205400c152602d06039549060055040e074039900c445403241c407503c002400004850100481e6480c00089020f0801e01c032802c0803904221028041000266010341402d170050b00c0d02d500300300d95998840c0420f040485100c0050154460b1400000351400150010a1040d2081d5010b00c0719980d41c90000000e40154001c1801682007010f008100c0d906c0384544903440329000d0201c41c0902d6030780c0c0208440700000d55040d00041c1481005443c0070001c03445c0e4021128041e1402407280110740e4800703114100280c40d800d03a40900140790010f10400750003030a01110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 778015197 1250 778013947 778014019
    0x61e04030504030b15041a0a091a041409150105030a06051306060905060f0405010f05060306010530060907020705060c0a140604120206010608011208070807030305010801111602 78
    0x141411764014001c480d40040c1e2250f400c06820500c00384500280110750312000d04806030480c24000042c2c00350000f0707445030f6040264009550b0b100e039903c1c017034074203681d4010f42a44450300f0305500c000e041804050900181d1108100100a5074800040d203003040740c0c105000041036103507001c8140c40700803090000b40c0040c1c02d001d4081403000040e408240944001c070340c030310b8414107403000344000d0321000d1048181c0102e00041c01c019130305110000f1a4040c0052400501d8400c0645401e80601c034040c12620100140313a080c1469900b5106085804c240201d031210024a080c40d0000d5445180c0d014050148101046a149101c01003001d90701140d8000000700b10f000d40120004d503a008211401ea602c640030042800102c3e0010031801c2c1680c001d075032100c1c0c20340e01b4083c0c42d540240c50369a080ba4040010811800400d40c024050001e503403117130b03601042d0303540f408030f00c1401e440007040880d40c0307681e00300503903000f2841540c28070060580c1698000040820b540403000ca107075000c113400e18445 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 778016447 1250 778015197 778015201
    0x90309050414011809020618030a0b090309041505060a0f1806021c1701060e0d060c05030403023c0c030715080912070b251808061e04030504030b 64
    0x41e10000c4003d050301e110b800407040d0511211000400c1d1581183d010f07400843c200303d12100001d50b8441c00c1d07940c10028044a81c420b00e103941d00c0240303d100b2181c841c0103401c0070a0403c410303e0580590b450b1241c000140180395818900020b407d80b080c11180c07014400140c20307200c0c545014045401420389159408090a90340c1c0501039112869485400485c3d05046030601069001d007110105088420498005581c00e1002c00d03243c6e03205003030149030b00c081d0398181500000d805024400d800034150b5030b05a228181490064035000070480c00c403000fa022440072201030034040700e00249d41c46c07080300309051400d42c0d154820b08080701c00c0d03030a51f098000c5100c08075810034603811401c0c1c0f0071203660b507060311903842004054031400e01480009200f203080040e1004a51428900d07a0400003c3c140007045909180c0603000d4165280140f1000c105038032881d1101e184a9618440280640d40180c403041c68450b10909031105d00e03683c414201c001000209080c1031007082a50040e40c4e01c58038805941c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 778017697 1250 778016447 778016471
    0xe10180b09010b040312050c010f05070c1e0323090d03090518070c02090613140601031103011203050a0903060c1d040e1b01030e030f1305010c05030a030903090504 72
    0x58841a0189401141c0200001402800c80d10803a000c482d0040508619142040740c2101d56610002075402203649a000b000c180364024030845014101d00d85a41d06452858608035808568556525042036000340700c1c4030100b40c001d580242480d400c03444030483c11000d10b00b03d00c031500422041c25000000459071404254015058500340c1c0d01c12070707230722282d0856400003280640c01111032400107100a0314240040c03e15042c19508804002c0009045107003003003103c01100c82c405540c844040303480042c8249942c06116050f1512a1111071a25540c1444044c1519161540c0001d04100c40040e903241414800d0701c0405c0516072003d020300580b005400000c05043e8510407080c000c203066107444605281074481c2e03500b4001c5c028050b1547d001811142c001c2d81103400c0705c0303905160711520b83d2101140d0620003440895000c845264442c940b4025040e031100312908001c0c144852600e12902003800041030b030f0075120b954500840c0d20001c0303240444040c20641d200c0b0307800070b041021b49104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 778018947 1250 778017697 778017701
    0x801090516261f12030e06030709031b0302131515021507020f1506130506060c01090f05160e010e0a0f0603141c050f07082a0d02070f0e1018 62
    0x10001e9401102024151a6401c1c440d402608241c01004108070707450720708aa05200008d1a4060b0080c14901c4203035a4913122008851030208100d504001144400c1c000c616101200040221048808014540c1124403204a401c00f074056494403031900420038090a108000740032401c50805124102400c02e00e0000e90369000d503005002c4640112042400c1d801c0c60014103d03c01d2100802418240f880b40310036100514001e00b5039500841d0400800401c40e1003402042041480b603040a1400065824120700304100030035030002c000c0d070711102040420007022805054401082103480e03991200c01340c010083c108900c18070700d4203060840010610060821f1000c0303014100042c0c4408021440342001e28410704001c240c0030403424400c040d503440c0003070050104a4401d4625510303107000b4400ca9801100460488a944c000c0009410040d000a2001082c0e09100340014045c050030407188071143c0d0007a00a030704205160b0000a02402c4540c1081c100601004142e681d60000c80003550300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 778020197 1250 778018947 778018981
    0x307031407080a03140d0b04110a110102090f090a020c1212150307060c02040f110c100504050c1c0213021e0304050307080a0c0c15080109051626 64
    0xe1a030180e424005001e80d0042610240395038580e51709811201d4524001c01300707400524441c907845d90341e41200300c15621244202466901c0340044a40c4030341107d80d00402103030344410707111103a9005120a00f600c2d200e003850420301c0380044480444a98449941d14005e024501800c500c622412100d005030501d000010700e003040c01028203001c29591a440b8030a8146000b12081e010781c481401042040d20840c002109a4401071003c6541c0012800007400e6424081001452220010f25108400b0082040c84914101c106060145150a440e10340c1c46510104100b0300906810703000b01c0d0712202600840300307400d500a01c0e424220013400c50070700c025013080d01c03500f060200030300381400d10161007026039200f154050000d51410a0903a075080d869084440b28505010200c04204001041904184041e10185160140c200d0501c04024916401a40304211051034402400b42d00f03440e68101060b10410360501070160551a2250070801c0d8019404c0c00801030440d0a10603007007081e4081e80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 778021447 1250 778020197 778020233
    0x607022803110306100302090c0403060e0d02160609180e01020307030c1107050a151107080307020405010e0c070609020a08030705030d0c05090d2406090b010906180b07080702030703 80
    0xc00c24005050030306903580001d45da00c010040c403283d4100010b03d040581d6551042007081c80f0750030155a960f61800743d4103510b910001d981c0003800c0c50026180e04020240307005c1800485140030905c0c01102070311418140c01a8095111016291104405240c0090b185640070700000c40d528130300603000900030411098808002003c0030490035603038400250580985600901071406280b4103e002c10141599400710b4040c04500c0d0121041c121080c007202008000c0c2c0000307107503500c20758410081101c070160845001a10320b8400d0001c21581842903959440d0f00000020358101d0030f00000e61015841e07400900c003840002100d0701000340210240012585409050040c0c904024090310207005500e001600070321084c00c03c8002c81d9589032800742c00754403030f490355202c00c081080d0740083e070351250021000c090f240c07010021507503482034400000b8000e1b0f2418450106050b5500d009840300c42c07080581d0490b0200d0f4820502c502a01101c2d481c6600508a41c8003135506c3c5420b203e05942106d41c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 778022697 1250 778021447 778021463
    0x10e0f16030b0708040512270909070e06041503141005100513090b01060e090609060f01121808070b100f180212332b0203010e030414061303020607022803 68
    0x41c0c1040c200700f02701d11301806501300030f018801d04261280554600041880754030544880d180d0340d9000321286404003650003002040c24604412010902e41b003928140c990005203010100000d40390504a080262402100c05402d84c458000c0c05402a0207049005408030415400000300550859100c0e12803441c26903456000c1c1e40e85904000d00b2000480722250001b0007540c40004c0780d8403a072206d46658080e503000080c0c440312800568007a040741c54088851071000601603051105401c1190381c081080c04400300e0041c10119940c40358111407168003c03c8000440d40e2a0b00410354058030040d20b240340c004907141c0b07020001c2200c900b5a81c00900c1d41c9000080c21407030440f0a6019440300c0c03090181001c1c10400c00b4411404c5146140305144502d00758081c04800140d50030f0040e0f1700c0b0071070000e000355251303800c1c0502e403840c0c50300d04100c45100340c0701004080342580031100351804682d011682d0640b1380c4054004a00086200300f144d5008a0480184003245021500040c003600e0148003d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 778023947 1250 778022697 778022767
    0x1b0206061507150207080d020d0504020117040c06080a14040507050103060f0b0909040201030209120106030308060604030b0c0a050f040602030c070e09031614010e0f16030b0708040512 81
    0x4074151240c19005009018042d58580c0c50103442d4000300002c0c0e101d010490300d42800740380c28400320b8100c190003200c5a91114140003c0d0741e4402c02c3e500c9001c010034000042c1e810507070703a5030000c090188030303c1c41401403100001c1c0c1c00101d941e000e908681c00300d11078030310140b4151034030584811050180601080c80c224000c502c800d9407040405c1664003010f031003032609400604100c001d01c8000e10482c1016000c01081c4d640d900c901d00400d4402040c400080784e002e055240161270900002d0070903000303501c00c0c001080800c025040c8290050b9151030402d0391088010000c95941c4100410052190b1000800160a65001004200140c1d14038150b440060b165880580055010b560440140d0700500003100e01d0313030b00c0c20b40600340d4030320405c54413500c1000c031207809080d1040c0c0034550280350040c90071382078604000d000c15151009501500300c0118116600c00c482804080d01100810440d0750018080210030803010200050075803003281c0311071040d40c143d500070445e001d9048440c4d245d404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 778025197 1250 778023947 778023979
    0x40e010609080d0c150903081501020c01050d0b0d0c030b0901052a0a02071e030212010903051213020607060b1903022b0206030c03061905221b020606 66
    0xa010001e80720701d40d0103443c040f11200d408a130309604400095038404240301d02509418814491901810b01ca901d031644180b9185440150320070144c0d4a43d410754010142c1d07034000381e0348030702110310746d801041c400106440340d0b0000c5007020f60603800c02480011324190100c18030491141541c45548441d0081c441c66030b40c0c40c03070faa074281008000050044100c01c00d203011140702038040d140c41182841180e4107196150080112048080c00030b01810188980910a50a0580c180041034410400a102801480e90001c09038402c00c0e01541e80318126802088480c0702c5140880c00b103d030000c121a03101c1900341030210080c0f0b2210364141c4504400030102120340d40201d10034044030f8008012400000c40d8070044154035412220a511038030110100b0001607403500091341c012000f22100e41c1e2a440c000040c005103101c1c0f2f4424501c0460b80f103504101f50b41d0390f10f030818101c0c1c01d10010680a8051090b10304040c003081e80300300381c07407090945140c07140c5940002c620f84100b50480d031413008400180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 778026447 1250 778025197 778025207
    0xa0207140c032109100f020f061b0f0712030623010c0b0903040305190201020d1e030c111005070f110709020906070b091b04060e0412090911040e0106 66
    0x104125007503000200c0c0d101c0e40000a29451140510f0342ca20185401010000107600c201e4407401a000700b2208010b03891003690400c00c11203140b80400041c800d0b8202080030801280305481c00f00c401b030100080c81c46c07801c02c1c18804e81c0c56903030b80096280851500c0400c080e02903c01401500001303401c000040710240d0709084101284141a1580b00701081c244d20f42d09190100140120b18510007040008005001005030250100500b0003512048509200082c241001080c1340c01c104142841c644c410490014194880182ca5040004485440030001c4c0c42d200710781000a07105020b10500070f03840000a800082c03262502d640c0c0c2000c0444840710603118176820118408107940410014888075034113900504c02101c00130803940c10581c09507210340f020703d8112203800300c541051100e800300740d074120b90088a03d441160144645424840c829948003070040015101185c28144804120b00400800d4043c06099a083c410f00c185020803c01036030007403240b44641c00703282d800062407038424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 778027697 1250 778026447 778026463
    0x512180102160c08060c0703050711030c06040b130b030903161a04051608032a030c120a0e031903050304030905040203090106140d02101101061d160f020706140c060a020714 76
    0x161245d03400c003043c54690402f0614108200c2d03425205004500310030750b903514040c00c001d03c01c4075107441d56801c080344102207038480342d400f80208580c01d00502001d00c4000c002c0e28400100d02da0202d590140c54289a1160031b80f2540d0388160582c00401e0009102e0040341101041e4603030b071466010b540e0f4440c2c01c2c51b941c1c8140c4103203004102e40c00181020098000500300707103130107400040305c1c10303c41c0c403503406030420b0203004030341d2100080002da0700004e541210504040200803005130000350302c03e040e00381401181c1c030002000c0100010000341014050646400a0a4042d10454581c901150403038000c180d18003942c3c80032500358602a01c640f4207100318100c107a501405060030880c070041c050750100c10b8424480d14654880902141d101c5004d008114107a011030034211590510000c00e8a032010800d606c2003c00015a003002d42154001617400100d80341850441c80c400c040f452032078810b014110303680b80f10b0300440c41485007800e5250041c2c100e60b4022001c200b250b07003504040580d242d0740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 778028947 1250 778027697 778027703
    0x40b0909060f062b11041d04051c050d1a010e0906060703050f30070203120f13060204080105010e13110d020402090d0b0a06060512180102160c08060c07 67
    0x10030008901000c00b06002004c12010182c40c0c0580441014510415200c007480aa6403044c00410104a10310a220003645c010503200b0098807142025268291907103101803114420b000b8101101101512039001c0352165030500d101002001c615030400304401c0c82030601e503030000b01c04075202000307498240112800f404006086620b40300c001e0394282e031130760001001510126000d01c419024100c503001c0449000d80c100700140c0d5444400503941c040380b08082d00300c804650080c840b45000110310489550405282d400609041d41c5900e11444402c0701c05d1030042c5150300101d030024007a0170540205058944400d104510703a90b44200514a4603165103014042014030210941141041488040424000790000d0314101003500070846900c0c0e4030004a4080d601e0b842000403110a0384101d00241c012454018900140c8800c0e1180710180905901d50340c10401880821510096049800c8000940c41c00700c0c0e030b0b001500701562205000c0c86050f10300d0040c1000103035018501402c6450a03a8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 778030197 1250 778028947 778028959
    0x1b0f070816120f0206040e0c0304060c1d010806030f0318040e0d08010e0403031103070e030d0302090307061b0c0f03050c030303130605100906080f011a0117040611040b0909060f 78
    0x80c3d4445154040c3c040105a801260401012a0341c64001081c0c0b44204044060246c2c1da080c5441d10b00e040315040084441000081482c18440d8502c1a4202c50760b00c1c002d291002594961000103802c0035036009010313003c3c1c400081d001403100003c4000c04c4a49508440c02c02c4000e0101d5805919030f01001351303c000141416006224440e88003448a801c90702a00c1d0000c0d01101010111b03001d40d10565600e408255075a41040040c80d040001000c0ca28251074158100009400400d42c1c8422500441092203400358429555000000310896059004140c440d10340b907460781c0303144500302940000c1d100360060f82d086541c1e6040008c100c03170084103810711640144006407925801440d0242404908a25000000410300100e0166a02400340d98010301110b00000408a086131884451601c20300b05015148409a8011462081c1511548542d0b1859074661428000030010380c10040f011800101d03000c40d0301e11040c030190490f90001d030340f21540368480c18100280d0f403140e0140c040d4851 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 778031447 1250 778030197 778030229
    0x1214060916020c03150f07031505010c06090507090507080a05040c0506030402061b06060112061a1c0e1501170c010e0a0503010207060207021504060c03051b0f070816 73
    0x8000301d5442406490140b0503148442da000c80002d017841c00c498030311075502c40c08009210001c0c00b80c0200d1604140641000c00014050341e1240c0c45618607071241d1741c14011205c0b118401e12040390000c40c40c85a0207000d48816688807094040107000a40b080e0000a007420006010601d4500c03c4500658100c0d140705565490001000156480208200c0e0803010034043d45641c40c2c4005681e0620704201e8000c2e00c61403622800051a081c019455404201d003022800c001514040016041081070005c001d951150360340e1480c4104e0207081d003034401803868809e0400620202280b05441060310f00c540040e00d980e10307018101b84403120b007001c825a40245900c105258001c59507501c4080b00942400e1038584c6c0e6800090890700600800d40300c01d9000101030b011860405000c0c4104007140031024246401c1c100700030460512000e0080a222000070824070840102c0a040300d1a003180048a6440c180d1041d0300b0740740c4406220311b500e070740706070600d045c00d0001d040b002d00c040c0ca407900310003c640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 778032697 1250 778031447 778031461
    0xb1201050d020609040c030b1203120c0d1d0102070201030c2f0f010f0902040c030615030b0f0a080307060f0605010507170d020c030703020708061009020306180712140609 75
    0x1c01d4440804982c021810800a5241e4a8500034200100381c10744000480600c40c00a00204d0000243d031031480d0380041040b1240907840024050f00111804009078848000000d240020a0406115441c0c0802511001703c6441c0540050000d81d10030380c3c0512801440030f500759020142003100380c05800100901201c1c440848200c107420503800c0c0102c80442d0540301000d42110760354039840d00300c1500d0750114415402d00d40580748024034107180802000d03242803034115010104240c4402010340300c00c880e18042d0749140001c9100c0c2801024901625540c0084503a2030388085421a15241000c83c1100107410300c0c8907100031264103842d12464080196100e240d5240d02009100b000e810030310245801414a20143c40d18600a0000319514005410064a8111035520071499a8050010401c0f4407006001c0001140d66030800513881c1e4840f1030000302402c0c1d4528908601c04513481c20452000d41c009070041036064100002c1001c0b0f0140515903850010031907a8030b4110a80901003080e0f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 778033947 1250 778032697 778032709
    0x2006040e01030602070501090602041e08030f0a080426180420090109080f250f0b090103023601111504050f1036030e0f0d080d060b120105 61
    0x51180b1940002a24901f0349d500c1c58101c1c0c2080c3c0064090014240320b560100c071320356081c01c000c0e141c158004e5040c2001e080c81005248540007070302c2d0801c9000305c042410030181302d00c0000d084180202c1d0740d140d2200c10003542c2c10b40d000041c1c1003054228007920304001e030805100754281c89000002d19000d04070301d4408800c4990102000604200c0a004001043e03501805004250341c0f405c0c01a040c80a6005082c90724140112010380e413121400108202a0b03086c517580320700715105232148648402031500140c0c02801504884d4501c40c80071381c148400200c4400c81401d04488a514146500c40300b00011034161844200b21802c0b5070200040c0e640c260f4000c940d20303a109200300c0484080c0140c0c8010541000004c50700d50b01c96545034140e5119060450920100030107003410740b580300707448640800302001403e99000e8107201144982004546928404446104000d0040d18140e030310341c44d1107042c552128080c44002850110f010801040038021110880d04079091303200303542d00301410420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 778035197 1250 778033947 778033957
    0xc1b020a030602180d0804050f060c061612051009060807050d0b0405191104050610020303042010180911040b0c0a1e120203030c0a030203090307020d2006040e01030602 74
    0x1300c0030154000503503940020079061688a50069030301c4600e09010700015500c00c203d0a44030b002c042c061800010310000305182d0014280c13443c14140740d0140d10540d0903803e900b00c0500014100f00400c48180b0840e0f05a104407240b40c5000c12049555050503900c440c402c0c0141540100305c50b13038143c00b00d000303031080d1a00503009800340e9003d030084208031600d0440129040300d80c1000200c942049142603c02e09500090940c2d01104000307e90200a44030310004200a081c400c1c501010344042c00711440300301410b00050030841c01c4c4100381c080a0f080c64001c401101e460342d003140c07020640c10454094441c0c1000c03050300c41c3e8209400c00014401a0300154021042440b5180c0c50402150300704510300b0381d51000100c40520000ba034100310380040d040c41e81490545d4810070031b21020113840b0701100d1925190b40350058907504d400600d07605520500c00b010350b0014601000009116900c0c03400295003600300744000c011250310050101c44d0045101e19040e034a2141700400201c0c026800502c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 778036447 1250 778035197 778035217
    0xd09060905061f051314072a0b0601030218190e160f1101090c060e0306090601060e010f170a0e100903090501030506041418010b01030207080301151103030108010c1b020a030602 78
    0x4108900b0f1b15000c106504411201c410000340e5900c2465042250139070f807558003208459903900c0400c02620713200f2400c070000d403803503040640c0022405070002c0212894000490010840c0f00c00359981c00e0b69400c980001d000c0c0c5000d00c1a000003203a032800d20b10b029034600c440d80d0349489251490802d001e990320300c0d100f800806075540710001c0d8070008030001c1d94940a00b0312a2100c01c0b0105c3c05a040c1403070452300800070f845ca640030900600c032440e00801c83c82100c98003480e1042110030441c2049900c80254003407142e00c680c1e16018000e070603407a43c005003400d01c942e8040b140300d021950b5402c419a40e9100019000c1240c4040a002e994420f402c00c0d80e00c1800500041403039601c503140c000d91082d0494055846040c65000d4140d044000c0c0500c1c1300350402441e0079400d000182d02c40408a22040c400c1505640f19080300070321150041e00080f108040754815681c03a9a96546880d018024411001c1c000650207040300340000741d40080100d1194018204201c894255600c3c81d0003944410495 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 778037697 1250 778036447 778036451
    0x110604031110110717070b061203040f12030f0c0308040b1b1305030f0304051e0307081603030807090b030f100512010e0c0d051b060d09060905061f0513 67
    0x20440407012070040c40d201c8007201d031003c3e070345018070308003000d110b00420300c40540114100090404542e0312441142c01940441e004403001507071a400c186544a07590040c0e03c0541c0c0c1060020b606450f61210f4042079004e6150100c1c0200352880440b144400060f0041c0071500210109020545c41503009a2103840c6420052420100c140c03100034640120b02c09003020b50208000348100e0406101000003908690b004604140c1818005854400910140311600211800c20011550200107842c01041d00c20181d6100081000c20b0000c051894001500490042d00102d10f0f030602c42d004075401c64446441d46411a125513546022191000c3c007071903a143e02c062008200d50341c509022702402800000006034880403c00c51600341848410303564441d20780f5000300c20105a01080c55201440c056a03400b881805030030001d0500d020b0031040800c401c0c0b0f041c48200401020350700203440d13140220101c1d4201da807200541031101d461412105a030f0b0301d48a0741000141490b0341684c0d41c1440c0c8800c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 778038947 1250 778037697 778037713
    0x3010603022412090610080c030d030b06070606060c06060e0c030c030601030605132307200a1514060904020109051903080307230702060f0d150608161106040311 71
    0x8a28043c0105407148a0103810980500c101c012214062034020944c41020300a61100030380003d0703c0d0300ba000b42030814075445101d4640c1c10343e40c01049844490340a602000f10a84940004040226100c01299440e240c04000b01d8040b0f030701c40245d803042280b1400c030392440d51844c3c0100c4c0340ba00081c5c18681410740360380c8086025a80c102c17825404848040d800270b500e4042c240101401030311010b070300d60400010000d021480e03601025480400e03008080e00b889625114589501d000707500d0002038106d400000d00310368030096a81040034400902ca11480d01a1503040c01c1040c240350558000b4046a41003900300240d044c004c0b8114807844035a41000780050352030300e49c82c04681c01242c0d0400007031818a00c0d101e403142c541041d452031041280c034850401c1c5240d40840c1c000c0c41411078401e004079010031400b401d001260070180c0f0080030b030804c1c81070781541c84601a00c00c490945904407980781210406221301e100714400ba015202c3c040c014415a00c6070f840c15102c411000344100d200e4050200307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 778040197 1250 778038947 778038967
    0x9091a040b16090503070e0903120901090605060f1806010c0b04080307090e0103150b2e030b04020c030412030203070b0709060f050c21090d080414030106030224 71
    0x5029200354041c02015049180c044030844003081c480803458240542c0190510180c0c400103100f00c01e95001014000711070715001c50140c51405103e41c101c0c03800b0b42c100c003044660310041d000f10300c06511403e010b100c640c4500d4100f008241c0c2c00d16200d900b0070b0030500902d01400703440007103e030481c1c07060504100b4090a900c540d01c030080e080794103860041c00003050000c565881605200201000c40008e0901c0d4110b542d1920012021108502e50301d44482403000303a65500021310360a40005940103450005a8071040d0b5850649007440c00803c0c42d00c0310026140c1401d00840c2c60610b02800514603240c10000c201c450147c8104040d81140710a00c0081d0004902040240c0180348a84985103914601140203181441e040a08001c0250130700c50788581000006034244140c403804159080000b078208421210301440c03250650024a2480038418040045d00500c255204c0c2040780304009002008d01d1f081e00c409210007904002411080d0038840700c0241e44c02109440500310324a0540019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 778041447 1250 778040197 778040243
    0x40f0e0304030b0402090a02070308040b1f032003010219120f1404060b03010b1804020d080a210b1507031202040902040602010b04050603120a030e063d0909 69
    0x42c01c102e40020900d42408203503e480f1050642c401c55601c0154501002d036500244046400307000200b1902020010540d10010780a10412100e455070300c4643c841d640341040ca555403c000d044c0e0410390380b8401c01c80814113041c000c480400c4008040c416440304502c1046810701142e0320b014501950780c41d103c9032254074900425800083c0d6445428050400c1c3c20309004603041c82d02a284203030704d40409500a0f4035100ca08100008040c0004062581c1e54000b0418200620310010880c00000031078060a50704407018400440c54443c5007026001c00005803022640b1100a40703503c11440466100d035588400020300320f0900c03910340300340a003492464a1013070360055003200a40030340100b41400450360910884404480072203050100c0d040c682c011a03101e2108025207100c2000024114091a01940056a0200c024003c89045240c003408600c14021164480e540b141c02c811200c49e2000c0300e00744001d0880284042c40c14019151000c1600144aa200110f525402090341500070030010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 778042697 1250 778041447 778041449
    0xf090103082704150807120c03021002150c04080c030601230a0305101a060712031d070806010e0f0403020304050d060912020c040b0a060507060f2a09090203070509040f0e0304 77
    0x344440605110010b814a13040360400001c840c4041f500d100410142e140c8201100e40550720944c801e20351441c12400d0001d512103030590703c0c0700d41c000d1104e4203c1a6004004403004141551048030700c010405840d89000e100301c856078801040030140d03001250868440d031150007045031035501c3d929590b00e4140301441480d00382266450701248400c0b0b00740c501f4030360754480480303c00349891038542e281c10510400f14688030800d6520050001850094801200d440600c0c4003140c0c10701d592900115600c24090040102d40751030385021400e801403040c012070040d43c0c15005581017a0429041c0141100141d0054428548410702880400c130b452030300d5158012240d0241c2420300c840c03020700047d206621801c42c05602c1300b40e001c002d4560f1140941d400c256125102142c0240c03008001301c0601103a070864a100b00903015442c440644140c040c0810340110703107804080c0d69450302c0c5c0004a002c200c03101c0011400c100070304055854664440211a101d100b400148180040c4d01c0600e50342003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 778043947 1250 778042697 778042721
    0x130e0a1a091903120b030712060603020a050d05101505060a0e090601020705012c030105090717010903210e03130305120712050c0c03010c030b0f090103082704 70
    0x3103441030290340e2209210b080c807058801c200d1003504a91075500200003800035a02c11101960712810301155540c1440040002c0144540b4105094460300b0158002d011501c4200e1140c0c8a045d000942c07070502e1840100a5a001000703441421040e500d001c020b03018820302044c0c40c1c41c2038000410705964030320203401200d81c26641c0c140320303444080601400203801b40c0504c3c150740c001307181009940e0344041c1c219a9940020206800207808411010f580c0826034612541542448208100d600b070025034042218803808014040348900c0071118221060501c0c00350010309a40e1030406140c81d00030f44071001d210300100019100107202042c0b411034014a03031a0406015611040041c49800c00c0103089500f82620102d1400c0303055501e95401030101e012000034042c0201d21040403c909100381102e10360301074024402e00200c80001402030040b01586441070b00892100382c01e0b818070301d58aa050300e0341300a0192800607001244071002d000d03c0101c144001c84030041c040c481c2c440d401038000d2070074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 778045197 1250 778043947 778043993
    0x21210503060111210d0b0d11100e1c08130905100f080705010c02010207080d020d0909090203100f0204081204030309060512040f03030f1a0405060609130e0a 69
    0x1020000100f400300c041d001e09000d03910880295070415141102020152402d03441c440d6220340d040381400142c800c6030800ca50007070402813031324103000300c0d00c00c11003100303008680f00364425030000401c4d02d905042c070300c54541000c0d4000028550a26020302e0b12202400b80c0b80860034814003520b91281407055030410310016403581c0c02c4c401c030031078800081c2d00030300070000000082c10b0502d2946a40c840040c401da40c1001040c3c01d0030010359000f8800400034158020a45154592010002e503031000104002c000060b8509000203044070640302d0f85440c95030041c00f522100e0801c040f03070380141c415400b0505442d6402c10001613622010009052041c00c500310107902d517860f5081c081c0030340e0019403103a001d000d001c101e10360180000e403d0343c0307030f00c254850214158040c00e030804030b00421844000d03e0900f4138004446655032204008200850400c807420b11a90b9174103801d112003401340b441c041c2e40210020310003246010b81c5030804141640c0110840784039080e41d0321180d4101da041400c00983c12 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 778046447 1250 778045197 778045201
    0xb010806090a1709040e0705100509060d05100e01062309010206070f12020706050f070c0203061612020a112505040f0e0d120c030c0503040209040317070e12060121210503 75
    0x41441d2271442c80300300c0c0f9410b100b410151002e0206855100e48200305150070358840009181c2c0404010086c00342252215030101503840300b10160172071102c45100400d1580840341107201a03480740403500c4180040c5d024001c941c58040d030a469106401c018201440303803a00c0a0b02544a4034400380c60098000c4901050909000a10340d8055001401900800001603025401b60320005540364100380f03243c507410124114400d089074890310070801603604c41e00020301c000340d056001c00030042020031882560071402c202d0b202003c040d164031414000e20b10004a0070003140c80c1540c8100350b000c0280c14046003548500b02114140032201c0c0d1404040340d400c01001c2c0c0150b2070303031094800c401800d080402c0340306c0c86980090711f00d020043c8000d01c140080c00005081511030008604104856000300c0d80e9400c004802920000080e1003440c02a10001042c884020001032030b0350403542441002814800e5101d400e42003141845025200124a60a4014030400c0c0c0ca01380110707950380b80c0d40c00d030302c1e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 778047697 1250 778046447 778046449
    0x18040e0109021504050303041a070507141c0c06030c02011509051902040f050618030a05060702160e2d0a060906080d0e0f0f0612040b010806090a1709040e0705 70
    0x201d80b443c1080810054240018446601c00004881c2035448050903022402c5003555504854460040020a14001c010f00003408100500c00100c0450040f01c109510f81c540c0c0188003041d203501c0001420404006104014082c000d6201140c01c15040c03001151181c0319044000e444045a03000a0117030741d0300c50411480c0310341d501c220071480707480c50010740c80d01d0328210000c40e11003000d00480b4840c0700000351030340c00820351440407208440050252603400002c0d04001e506c0d20412031b18070001d4066000f082c0342caa001c00800609035055660340301301d00d48890410401c40150700300d400f030695421000c0b5465068009105a200c1d0710100404144103042c640014241c4100c3c1d484181c8aa1200e00340920300750304400d075812452070583c1c0000d0003c14000001d001090301901d142c1d0441c00001c0c02d07503072410700d0000d5140b0650241c00b0709000303641d030b032501103a0b6501c01302c40300a46900510a2900050080c00c56100124a0f2004550910318400006800c40d00340201d085030350790055a0400c91 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 778048947 1250 778047697 778047709
    0x3041103070b0a0503040b060a09290a0303090b0a110708030403060b1203160219030615060801030302120a05090405190c0302040f1a07120c0b010e100b18040e010902 73
    0x140841c0758040742400003c00000c4c041c0d0202510080c02c0d1444480020b80d070f6120800008010050b003481030040900150599201d042c82035040d81142145030900300b02030610050103c00c4a506545a4012610341a1410043c1d0051700785041040403003101c480013030200f0880350000d0000c10000d55901c42c558074155040f911540070070350148a666540e024a258080156681028200d12170328041c0310b0343c0300103605195180220300c18102c2c030940100030701016500c04030011240c1201d8842d03154440e40c0954a600091000400607482448010440d8809001820070f06030745051250a0041c460f0005040d154112007500554400016000c5103070154019100000c540d400c0851410f0700345006601000180c1c003a0030412300340101c44205260400741120003141e0401000b00b81c140c01240000c3c103072555160180c1d4585404000030581c0006000c1c1c042c003070040d1540006a0300d2518004c4000c0360070400b000c02c00d170b0700f280c0d018107000d4a0740c0c081c101c00344442c0d2000282c04280c078410002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 778050197 1250 778048947 778048949
    0x6030a09081201060e01031512020307030b0702031b0304050609060f1201030b0601020d0f0f0e0d06090821090c090703241d19050415020f04051302070b010e0907050301020304110307 80
    0x104150074440c00100321210000080d050362683d40004127582400d001080c900451680010100341c29102040300442d0b010018107003943c01d0400c1c3c0d018001102a184d40c1d240100d000741580914104440405da207000c03001044881900340d841810030a941d4807148451409170300546825075044c0401400d0341e81880740941c450054105108811465a4028048100c2030304190611096a19009546d5200107000c0320307482e4440802e0019204a14040c49140c101d0b00035000c07600c6200c3c921446000b4802c50031032103141050014090740e020801042070030070019080f4014075079900704100d03c50741000c00b01c01c004020700384a100043d05d407402005506455081c00c2d66000b400c10103100180005008091500c01454400300311a00c441c18512000c0c1049080800442e00c00921100700406060140c800c45104440c00007121206862880c20380c030036404018a204011001132180c0c250b05210300381c10088050071580e04545400101e07003280e10940d402d8030b402c1303030f040102d0919203400c0104c24 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 778051447 1250 778050197 778050199
    0x901020403060f2f0724230406150803070b1005030f15040501020919050306011a09041e140f090f071a09180402030c09060d0206030a09081201060e 65
    0x602004a0a403041e00d4030940702c400010003403820350f540010134042c0e80366290400850180f1085600140c41c008004d4020341c4074941c204012940011100c2c9690040e90381d245540d8101503030b07655509001003099101049100000c60004911501c00304081c0280a01c12010135401d030800d101c03859880101c5610240c402d034805580d4840c8a8404030b02891680d241544800d01510b841c5030140c0a402010041030300001c014000e00b001034400d4800a04503901902580c2036640c176455a14000c03d03440000c5503d100081100079120f041c10f52042c0c04214450309a80780c1000a001c102040c3c0b00c03480c48850001202d241400074820f16030700100d410444d0040100710062244400e1500c1b41504e100f10342041002143d9140001c201c0411a4020940142404100408085040303407a05059030268041d104154110303105041c409010b41c0604802800d1010a00c00f6900304241c542c0005c0c001c0000503102c060007000100498040c1405003d004003a651543c113013103000b45400c000790062 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 778052697 1250 778051447 778051451
    0xf07171210080c1905100203130b030c04031e0606060c0c1202010e06300403080a06230a0e01030b043e0105120a0615170a150b030901020403060f 64
    0x42010540000340711000000690f80c0c5018020b0101500b22400d603254417440e046903459101d85882070b4080300a1280f6100390010308175a82d20f5074920b0495000c201c8200402540400081c00842c0d0303600385d81d0406040c01a9543d689403000e583c1c3c40c05950f07141c0c0c8000c0c042603249205004019148040c0405800e01d000b0640101806030002850b83e8102d06505000740400120031310b0505110308410404000000c001d40034400c059086050884116001d038006500e000100c0c04500060040c0c2d422248001903c0708540b1421014141d6020400070729540000c40500018590201074041402103001e00405003031841d0a0410070b05020301c0142c20340b2600040b540804240b00420740b03c0061825907548050307201c03081d0700143d813140310f82c0703c128140301c0ca01d4003000440d034501e4010005440c2040da1b000d5468209000645900388290070f00e0422000060000e04022220760104001c4401a00d50710011555044410000d510070344141c82965000030f002c0c024490113008008a43d0702038002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 778053947 1250 778052697 778052699
    0x30604020d0b0c0d0e2d060c1c0e0304140d0305030118060905040506090c030c1e03070b07061a120a0201030506030313270c0203030c0f07171210 64
    0x49403107031000d078000c0c00c014000c00803030158410082034070000d55215004020100e109080d15940d10021010f06003500181003d211032208240c20081c41000703038000030326190b00c55860818954000e80725107003040d00c1000305400c2960481c06043e00066880d40903645d151b040c004506401a034060740a40104c1ca2610f50a000070b86c007030122411214050b0b00594402d0956055034050442a40315445090078101404144440401c41a014099050480b048150b020040c55195980d11020035030000c0c010074010316081030141000454000101903442113912215051a141c0000c0743c1550301c141d892052410441c0c4128081105a000b01c0c0c0201d0758281c03d81c41d05940c0c0c13084000003810141c407040415903544082040d501c00c0b0982e811010040c541310040441a9a145140349040c44d0440700c003804180081d118040c00c008159010b5803465880e01034481d46139014032850100038100b0050304d030104407005020303103004807009110790741c1e03200d00288156261f50287c1200121001040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 778055197 1250 778053947 778053949
    0x120626030406081b2a06010609080a0618080f040609050906100c050a0c1509051f0f0c05061e480406020c2e0507081911010b03060402 59
    0x1ca100e03401130f03d0b244803400c00c501c0c0403200c0c8924001d0501c9107500d4041101108019140c859200c400e5601342030880d002a1303661501103468074030b00e10070420707542c1112200c800810495001031110800c1c1c0c02d0100c14030420f55071074051651110703010001d00700003c41c051201c00da101501d04005c00e0112151042ca05190b0000307a0300070302e005525014016015101d200b00311041c480d680d070305030b0095626031055075100b1100d4007214009803020005103035994042050b02d440030300c203001c0d19580700b0580c0240141410588039100803210003c1880032071001d450000708200300c52403048030803000e00e460141502542c06003c0c180a00985100d80248a42e0480f00f004a041d030480304407041c4a075080d002d55078003685118000518140c50070a4006000b00e07415030001840310a210b01074621305203201d5141090486e40e000649a19411401000b80440c410b202e100038026003401034940742d1030001440784416075041c0003191600440c0200c00300090b03004081c4600003100000781d01a103400d15180e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 778056447 1250 778055197 778055207
    0x406021201121101051c0e03040906061416020a08030309010f1d1c09211205041809031b0c030201021e03030a11090910330f120626030406 61
    0x50f10324100100440c2500b00c41013080ca200c3d0008812810030048072422041c0d4039200e03480340c000d24201e18180500028890320640000b09240810310010b030030481d60b05505560281c1c01a000d0b40e00026481c0c02282d038020600c0114000c08010b00009000904000d0100995031984208405221020140e1a1781c844c086500061266400e0070b2441942c5054000c3d55081a02d400c418201108030007072803600040442d981c1c07031050003045c00b0760100f0f1419004036000e100d80d010340d500c80c40074030f082c84070300102c540c001c0c0e00c010b8401e0074131414007010703400b0040700c080c000c0e0002e480c04008100e04009650701840b0641d24070b200228a221aa5030044010741c1e64480a0400d0403050fa403601c0d0300354802c10716000c4d500c1034a00242284400d08003003003000494105401401d0195000800030380f003002e100c0420b00000c4101d19100201035409c01d41c03d403845240304031010188007080b101030311169001d12480015004200050000488100580c240390000c0002d04030182e004210500c2480d4000f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 778057553 1106 778056447 778056473
    0x1908040305210a080910020c0a1208071b1b030305041a040302010804020402030402040615030e100c02060115021018051c080c0f12040602120112 64
    0x1041c240aa00c0c0005a002e5108079420012072030305034028240380f980400110207907012225190642d0081c0d0340003808404581c0c106a1400d810014000900c05500510385070004e507038600b5400240110001170075242014041d1f010038010007000c132039902c0407840e50b0020300e00810750320719003d000c94100d409585040f01a0818124005001c0e01c10340c1e0449405940d1140706455903000c2c40300030350010700f061b82c00c29141d66001c50072082c4000300000c121f0117981c1c00204002d40020007801c0502820281003160f0910b01012140d590004036141981c0c0402030707511201c204008160300c1e02c0044e100b00c0c0c040c2c1c0e007080d0804103250485844800d9030f03070244040d80c205c440385641395480f451490361400042014000801c50b842c400c400a420002c04050009280c08003220f0180e84041d02260102c0d080d60700001e003030110300d042814050042c0700314a21400c40120340c0d03507200c804a00c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 777877697 778057553 := by
  have h0 := BRFrame.cov_init 777877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 777877697 ≤ n) (h2 : n < 778057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
