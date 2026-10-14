-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2287
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:14:41.528735+00:00
-- url     : https://prove2.me/submissions/2eaf703b-5a0f-4cd1-8e01-9323387e6eef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 411151079 ≤ n < 411330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 411152329 1250 411151079 411151099
    0x4050403081b0c01110304021906021011090a17070b13092307080106080702060f0c030a021b011a0a0602190f050a030f02070b09060d0908090d0803010e1003022d 71
    0x1109080001b980164001c0d100e4006174007071000080c41c0c5c80070b1840f8210069104800311521448503178007203401d20b0300d505403407844c2500344400031b0b00442d91500040820034075100c0705000e032035003044040014040514120b00b4600d19080d4040a60184d04c140402d8a4550001c48198103e54000f00c141c82032501c000c1c241030404a0740200305417003d0103100c0201c2c01d00e90100c0c008600001d01c40c2d204140c1420444a240e5410303180e2501034101408401c0a80c0d020310078000b064030074a03000d4800e02c01200000512249400e9450388501c2d0a546090069028040620400d03601151482c103407480d610846002c2c08440c0b8208640ca00c0f50b1b6000b0f0300d203002d80a83d02d801c156000f00c0102100000e982114580b58940e00e0100282c403034a00c440b54003401c10000f203040c02c1096048000c0c0103020f040d00e9820010302c4400318051283d045c02c12a903151002005100804410b600a90080b8246000320320740f505603800b080d030320700105651001c0c9500c0c1c641c0e0080f03c030301070405c14400ca02000e04107000c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 411153579 1250 411152329 411152351
    0x9240702070e0f0103030206061e1509100e030d0513090915020c03030a0c08060a03030e0a080f030307091a040b0711030304180b030d0e060304080408120c010b04050403081b0c01 78
    0x4140f5003800b00b02c0040c096503012903443d01e0030f086245151a823806658882c50010700400009010302e00e0710320489103003130020078003c5d51110407801c4c000100341c50305007208050004150810810804d244241305043c00410a004490841030007a9400342e0030000d078220150808016403142c04503c40c2806000160b501e1344440007201650050310002c0c0103105a4010000aa81d840d004940950308101d01050810100b440340f03d00b10030f010340c084c00d403180f0940c03192403482c109004105111195031000043c4207509600c5002c040080c01c010400f450184032120440949102d2441410300d5103c000c5412402e00c1144034010b124034100600326565603546500c048041400103945980c0d040c540883c00d071a5050104141c1c50411b855900c0c003402022034000c01000b41c00c007400c207940c1e4203c2404081094101009104514460764015a03100d2150b441e5079401d554a04000502071410311050000103a007100f0950b0300711259402544280d082100050000c0c003509014070403d40c2495401780c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 411154829 1250 411153579 411153601
    0x3030f04150e0a110915100f05121602070b0310060507030302090306010f0f050a03021008040c1d06040f0c0c08090609130e16120305130e100602010509240702070e 72
    0x4004e400036540722850395581030002040c2d14120110039005055203604081c0280305810007a03050141d424518140448002602c454101c00c49032501585170f99401402c2c840e4040104400138400e026100d031552500c18502410900b0074400c4e00300344500803c0c07900c100740c0260141d1b9403180f0090110707549903035a8035201060084a20903c466a4021880400c10b410000c002d02d06882d00a48040b00f00964640122004100103000f0795804108940108094018031014a1052031501055019092400401003220140050084514602403000c40202d41007100300c264aa000865261101c0501001c9009481010000c81d80124000075000c105a03da40c0440d1040342403c0444209030881c0021300c1000c1110f010b811102c51045d910075000900c558018454400d0f511041304540d40e40320304a0300081026500000f00c20080c04003070001a6092081c83e0b8040103a000412aa024803860091841c00d0f1641c400c941000100000701b0541c001c0100030002c107000480760000349003034040c40c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 411156079 1250 411154829 411154853
    0x1a19020c0906040e0a08030408070803011202150a1b03030f150305070501020a082b0c080403080a110418060506030103030f110c13090507050907030603031103030f04150e0a 76
    0xe00c2010001c1c040707040b83c2000c2c4203056440492100400445003a80c0f80d0780e45541004100302c5142000700709100c00039105002447c002c0959202c1000030314010b104008421f0824501010b4501e418003400c00070035400703007280d03490300103a290302000680b4a00742103015102076190034031414103054003100c00c640024140c6040700d015000380d4041c25101c0d001242c6602450f1f10150070349000303005003000c00503003007001001c14140050b40c11712079000e0b05529095176141281c4c0c0002c01c50050130041819005041c0952000c014101000181d800f20500086801039003e004060402072130000c000b0150350b8010380103490010036080d01ca6940f4600281400c0c0b42040c0031000506e98000389280c2e0780c000480a101610003050f0352440d584080c02c80d0010b014148040d40c061191080020361500c40c641a20300510b09070350b010031090300f5428050946520b824403200241d1040003003206242c035040800342c00c6903000d0384003212444004071240180190781c3c2201180e0255840035000c00203060500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 411157329 1250 411156079 411156103
    0x120a060203160212040f15020a061a0910050102030a05090303041d04120e0616050307020409031e0521060121050a0612020a0e101806050307050d0c1a1902 68
    0x11608040c0d6013001e22101d002d10302c509510088000700c1440322000d00007440c15003600d14030407949a081140c5078202138851810f03c240c6005800c0d04100401d0425035200d6600c0700041203040109482d0400003986c91282c0b20900c820000d02107102c28103958248126401401041e441700c0c402000c1e1101c000b0000010340e8222840c205c88400b02c0141d5018030504160a1030043c0700130304141c00c00202c06811207540c00c04543c1404100708038030040c0e40d144a43e005180c000d940300034203142e420b200701100300400090982801801d00c400c0321490341c0c1d03d49e800b10440000c1803100141d01c8040c0140e49502c3d0300c0420680b462403801c60300b0503608060340712900c1400c58510910055036102043c020f4801c01c8000a50460f43d200018005007454050303840e0060803d4407101d100c96a580c440003806c000d0009200701e102c0c0c640700200300070329042040002606080360f00003a9051640e4444070360450030b201d00540948205201840d0101c0201500c000e80038441118691a50219009488000021030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 411158579 1250 411157329 411157333
    0xf030b0a090f0b2d0d050115080106050a140f04060e040318051807270303090e090105070504140609132a0f0e211b190302120a0602031602 61
    0x1039032059143c441400e559034509a2503d104075000d45048981300040f50b00c2c5107401040c1442c107000060002d2144040c01e0f034004c00c82280c07480c1042c070402d0a44810f42c0c0400d1003142c401c41e0034800061742c40c0915410400c100d03514800720903440c0104000c1c1480c0d82c441c6040a5503201004103250308501e41c00b5010202c100c9010005880b0320070031102001b034007004054804030100240b42c183c0280c910130701240082e41c00001101e00e1144803c509803003500308034002465560200702c03c02d910b58620784c01c480c8000003031000303241801c00149240614421350050958080c54100d03941c0301c8004a036407050000d03110100d010a071811820180c40c01c01c44030f0314540d40601402c7e0000c00200c42007100c0c01410b036070741a01003a461808031003e800800039194402200700201e07044100c2250202655a00c49001d030820b010b030b298084050546011541d2300400340003141e8413201140c0554481a41e070b044828540c80301d21000c00038a4429501ca000b041d81d0700c00820b1044070401c900c00e43e203078000c0b2642 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 411159829 1250 411158579 411158591
    0x3050a110604080d02031e0c040801050117060c0a0e181602010b0f010c0c050306070c050d0801030305090409050c09040510060605090a05010c0206070819030f020c06070f030b0a090f 80
    0x5400d507981d40100d4000d4241c480a00104001d10159001160040704002c0842c6546031080d26110918000392105007008030005800c10003e00d080c061b050040050341320010060448440464450000401da00840440062544a094003032b05800140c000040c0c0301000051030302e0030490548000741c6001c6408a0081c492075109441401003806504001d400da130b0034900300300019141d040e900710044441c5010f1000105680d10300700441440b075045581d41d00080032890410718104003020880d0b004100d5444014401309411004a4074454000d44001a07036140f14201107040c080c0f041043ca900030301a000b401305100001890001c0701803100310410400b566000262114854002c845410003004141000701e90b00030030300344510a002402c402c1c5802100c3d42d9904696000e412030b50300e455410103480103071a40c1841410301c400c0c001d4004514080a4a810503592440184240c040205501c3d24400b900c1c070a4008085511000d003c1e1410aa11290544050601c60403c4a1001d192030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 411161079 1250 411159829 411159857
    0xf11011a13020702030a080d0609090f12020a080702060f16050f0f0a0c051002030f070305040311010c1a0603031b060a110f030114011407030206040c08010c0509040b0d020a0303050a 80
    0x1100f1252016401802443e18290b0f90740d40296a400000e00b031a211030f91400009000c898038010301c1e034501d118807043d0a844a4902d8038601c54030070101030404560020804100143c41003081740c090340d404075499a112a20b80e00d1420751031055025207901d1503100107100c0704003c00041c01d010039410f6042500d54100a00105550701c480d0604040c12000b11107000700320380c0c01c20004056003401c1d14415a85081e0380c0800c12545540300c0c000c00c1b400103500046c100b082c081d00c441c042822502c2440e00c18031411180d110015113074802d644000a11110101044466804000320391500014030740035030070300781304040d1180c45000881e501c1440c6030402c116544105060011210303407880304a80d49045900708000c00d20402c810a40c024140006c9800208420b000000900301c500d00c40d44c01010140740c58600494400700503407000069030704142c4501034654200003074962006094400041901040c400588100e1510300080d4001003031050200916074040000d105020154039803012044001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 411162329 1250 411161079 411161081
    0x1908031b0f0a060905030405060a09090c0203070809060d270b060a15050307050d0f0504141501150e10050307081b07060506012c030c01030515010f11011a13 69
    0x30200c1034100c2c0d000201d940001031125406255124041c0d01280e08150311640270401591145523228041000c0304410840c1c07580c44c2c05680340108061020b50b08089856403807004501581822a01c201c07008100481e00c0d1219610450000307403000001150f114904440390201103200c201940c1141001d80020343c5400c21070040c50440d258684500140203848078110307203541018000404002c01009018000542401004c1c09080c41020005003810107103440c54000c80704903d80b81468000d000071099101c01452218110780401c9030301c110003181c03e2004c0742d0b55442074903013940c4210380b4110418070720360002c059849612251250003885d2504101d1610210120490a035000c80400010002400913000203401400c107042000f0082070a403500030784801c40380520700300006c1c1c4800c01c00c524034041044402c4107130b083c2020041418582c0300700840055440e021414840051111709040388074680302d84140e0aa00e000300406c10b50040c0d402d01d0300702d684908030700c2243c1030b903001c14241c03902d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 411163579 1250 411162329 411162343
    0xd0306140915031f06090624170a0b010e10090b161719091203180503240604060e0a11070c0e01030b07110c04090c05030a050703020a0807080a08091908031b 69
    0x80410302d170844590f001e0103280b2008024078041c10003182240d50052401c00d4407449e8050720109602141840500b8001482c0b070440c1c000d043c0c81002034071070804000f07400900440669030242030407039895004900d0301088441b1948010f1642200d401c400e001380a05c40090401030441d0400b03416000759016044a2110703d600445000c662189030400009008503a0a02a03021031100307001c4255907000001d040c90a550030044004400244820081840400c031640c4008211801c010850403c640300400010003040c0c40321195840440e0101e01e0940c03000e9810499000f01c4015480c1d8641440b404032a101784000c80d120f02c000004180403600400300349141e84003050003420711145617020080900b01e480416204911210720100c5c80c1e440901c94056070500941c010304440d0319602c113000c02140c040d40030241c2034104c11000d008008022403200c100c560860300d61626107064400203a0743c04103104113002098412000002c041002101810782d043c0852103032005420030701e140b140c5540e9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 411164829 1250 411163579 411163589
    0xd080c03060d030e0321030a0501120b16300f020a0e010c06060902040b070311030703080a050717010605220302031207061103010e0f0a0507021c110115080d0306140915031f060906 79
    0x1031b442d0001200c0c500845c0580c0d000f62586c4c50305101198041c09803403e1103b065444228903004030b1403102c200520b9008d9148000e50700d00c002c5150624010005141c10080e00d045410400d0003c880001e00c80d09400440241100802c110b5076150399122070345141d4400c8104401080c1c5082c14502200004019500c0f400d415403202001540c50120000040400030b101c7c600307108181e2140181020323000c1090b8060a01916a181d0316240b0304610b20209070011404003010010140510050b14007041c0c11144c89218006203440c0e004619141018289080300c0401074900840001040b07031400003801e0081100c880c0d049081d8a0b07075008035054070406c50b0716401590061740031000c104d08c54802120b01c100300d45040d20103149114049400d6500154004018180030541440700e02c000340301c4900350828030300f02040030354070b010780002d0280c0c48042903d2082034aa000205c1049244402800300b0100800b0780d60a110205103510060240102d0002c01520b00315000c80c80c01c00c148224400d0320 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 411166079 1250 411164829 411164843
    0xe071a1c05100b0a1707030204300605060a0b07050a03030b040e0a151509141f0b0d0e01021c0b120a020f120a050d080c03060d030e0321030a050112 65
    0x2803c24150380140d074080b910903c02c0104548203a56014860300c2158066030f120350300907a54510b4003d4001074001408890358107261244040522150409004002164040d4010079581d4a61f00041c400944560084421440c000394000401030045869084903119440070008241190b05100494800c0d00d5070700030f1540049800b20200e4100381c002c200c1d040d8001d001050880200c00c84405400d071580c00070780c040d0349880c4044803605028074450b501c8260045101940d0f82101745040da500e040d42305071801404009001e10524030141c0207203640f0421100299502c58803da0340d9004080001c50714082c0703a00c3c0441c1600c451414545804184403100010401014181c080004980c0701000d007507400b8403d00a08844070b5000e009000341c641c01103000c0e00d03004050b58405803a0600041070442c44100400030003510307603612062001542d805180c41c0c0f00c001d0030381c40407034501806481c8406031180e21505c0c0414800c0a100110720444101d002408a641d846504007071135242031800074109d0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 411167329 1250 411166079 411166111
    0xe07120501061b2618031203130f0b070e0103060b09030d12090b040804030605091518011508030a030b090108120c03090907171008100e071a1c05 64
    0x811603003681200260003081280c0d02c01a2805411020904e422003501c0c480e03401040044103045200e1456240150070b4015210320f01c452803120220b40b1005050410400c201e108541c01d000b80c0e40c1291513501d900104030020303802d2800c405801244807242403400031741051b10101d00d01310f01c08207845103a04081e008191103140b2100c20b803441d080c1903001d1039032241e80701e06480200b409400d4943c000c50081c5401ea59071400d50500030142d45004201100c3c80d8456060040190706220651340d002da6014680001d034408a00e20a025045070407500544901004d00032a0550300400140300c041c681d510104140e64100b414061540801d01c54000d0b180c211031000c0380020741007001403401c0e540359801e41e0f03e081d03403450009120b404250307100e40014034403c0b0350601c04d0400c0d21a00b40c219065030905c01409140c050025540c030007242c0301034142529200c400298007000c0202001400b0700d00702d11034021500d05848480303508841c1280c0f800c1d28070078000f00d90603a6580700b15030085901d0700d07109a030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 411168579 1250 411167329 411167357
    0x9050610090b09031c1806030509060c090d06051815010b0301060c05030d0507020a0b1807060311120c03071e020303060402180301051e1006170901090c0e0712050106 73
    0x89030000c071000b503014017604140090840852a4492602196896440c03c100f000c00560400810303d420042c00e0500e0102841640b400004003181c0c050510301d0115a214511004500e000c40c2c0021b0042005042600f84111005681003010248a008007180e14918a03440c09801040d070030302c0f808240200800c010301500d8482d140c0e100a490241c0200c901e000ea54440789002c0364021198980160022080c038010404c40100640d04007481c031084480c080d00020300191505814410202810f603a4503031140029190710544080d08840e11110b4518a800700780ba1030315a000320b80700780015005c010030380700d1074400c2d0810800001c080d40c0110b040d561500e06001c022b500290803100500d0480d0403c0d2401d5401b401014405c081c5c003121108900746141e40c00e0b070300c1c0e0005031004e041d04003c07920520445521a03072200c0f64808807106c00e8442d864400c4958010585881c02400180c01c0707034800320f100b915040110b40101310b250794106802c219120f042c401c441c801e0248030b001070341c2c1c03440e0514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 411169829 1250 411168579 411168599
    0x1140a0207150c0519030f18080306041a03070602011b0f1709070b04080109050d08090d0e0a080a08030915191d0106060207061b021f020f0d03060905061009 69
    0x8500b5440c00c029103800c2a003540702c1076980c0042940b600017910340d400401f10801c0743c0a03140c40a070301030b50341142c4410346030b94503d40c50000901e810302a1b580c1d544800c1c84800c0c1000212403200016007560f05040d11610000e0181009140d205808146419020141c510070f015881c03104543d55600c99021070381240b000c603c1c1c03c0c05000d581c040d110321140450741016080052004183c4070340001360100a0385002400e2030083c4c0d0206060001030344c00c000e952071000c40ca442c04442d03685441c0341c0304048000040c48e5044e03690800446e901c1170710202020450442c00441c011103440e01221524400c0c1c00903440d10000c112020210b011054241c06851803054000300e00210050508000da42c501d14035560843c0d005500c883c006038003003c807c000c402d80162001e42503007038444d100300b404459500825008180c2600e000c098098140c40922800e00c20301207200c8091042080e90051128074800074080e05190180900c403625080104009103400000900c11b05800d07111900c520746000070b206 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 411171079 1250 411169829 411169841
    0x50c060f0705010c0f180b041701090807050102030f0a051003021c0b091c0305010807151101020406050301051c0b0609100b030405031e0a0212090a09020c01140a020715 74
    0x40c000c400340490000100213008034044070920355070716031a14000e200c005144d06000b8075001240c08440009010140a18085805494840040c40055441860f01c640101560b0b88060710b40d40340414000100b002c1034000718098011504205040c0d100c004032031041360403c0d19000c4403544801d20810040c10300b08402d00203007a403180080e01007400307620740b86414401140c100c2c2c055005203000d03c043d004a400074004032a01c52404011035810f2405d250717919406400781da0040700d04a44203003d034134030910a460310490031307000030b54586588502c0a08039402c28000d4500c60b51074100c0c808042880401f03840602130b08800300310480d441d0035081c059914805044000d64643e500004180850008011170185110b20000c603501c2c02c4000c1c1010035020401c0c1c486026600c100300b04401d40c2d6001072001070755542038808e01c1d40c5031b00840004482e40c0741548204203407400881d4054411206520103c0c04030300342c0c2e83c40405540c0702040340040f441009030040581c10f80640c03580501074958084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 411172329 1250 411171079 411171097
    0x80f04022101050103020103180308060d08040b0d02030a0f020c03070f2f090702120a110705041a031b24040e0f100f03030503160329150403050c06 65
    0x6400311184000038030440c0790408001da41e440e9100c0b4010021940d0600c945245540c005a5030300c501c402039030703004000a1010700018483c4c4d4503101d211051050450841d801442c0b41d084541d5945d03c0e8a41d44000303500200c91140d2224505055995250442d000702c4011078050300103940740816039640c1401092a5540c01e4030f402002d030040c003408112288141e10601110700e160820380740030324108034900c04014a040e0464224240d0340c5000e0384940c080e24119000303030409118111000c2c003030a02e840a140d1240b0750050900201380c820360b009886811103040140d0540341007001c00104414402c01214407035400a00010800c0742502500110b00c205015501a0a103025070764a40b02800e904181d03a200c410607424402d10807004c103400001001450014480304030310f860358401a00c64080103180410100190f84000141031003035024810304130b01030014501c05101e00e0f400c505442c03180d04c98640030f0384040c42c0e0284c10400b02d9060f101141c1c0e102d40180000391084c014401a40c00220300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 411173579 1250 411172329 411172339
    0xa0903021e030414060a1715040c0509030f011a0103020a020a0803150307170d0c0f0b04031e020c0a031416090b0901060e030706030e0c041406090c0a080f0402 70
    0x2080711514540a0300e64810200700c0215203460130003003640215690545440d100d00d60404c03200c6a840e03000610308900d00680c01c00c0ca060f0741c0d94034801100004030387c400780354810710308581c488965400901030005841c042d0304940c43c1c0d802c41c4607998205d5804419032640c007002030080c0a240c0d80300350003c141c80812881500d02d42e18540e51090040d4009455a80c0c1c03807400c501e0595100d00701000310800914081c80044001880b10070784c1615080b0b00d044400401021030b84000070b001703102c1020356400e40d0020554080c4d00e86410010100c24204000070115601200100141440001c1c411400240240300712030052550741c8408150150058240b441c0c05a0b242c0804541500100c0000605c2d0b108c20214100141108218268905800030340503c20756841c0c1d40d590780c600090040682d115401d0020361000b400c0030f0301c0d2800803e080000d82c0301d8148510b08100c20503102ca42801103d0540d48103c2540302d04081e40a6405800180000201090000b42883e120b000a00d038010303001801c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 411174829 1250 411173579 411173593
    0x1b0906010c05030d0b040b09071223041112011a0d050c120d09060c0b0604050403050f0c0102090a0807061e1206030308090610140f1c0b041a01030305030a090302 71
    0x982c55080da04074690300ca100581c1c8400030790f654106401120414001115542400d01e80382c01c0140c400e80466080034803441d85d510a81c944140f003121703941841c8130380b403644480e546064a0844c000403c0342c1021801082c10f501b40300c0c1016414000c00461405c540c3c000622095001c090149040f1070540c2512544101f08400c80c072612a048180038080208000d0400e9041e005405000f6065661080040001c1401c4000100350f00900d0759803c00001c803404981c0384c45504040341d4500900b542690741d06c0c8001500030240c0015401802d258400740d91a42c0c450780e0342c1d90f0040e122109031042101194072084444010034014000e000749031031504200c40c03002d89551201c0100c990741d80040300864400d6041c0306480d042085110780c000e03041244408100d040c850b0790581e450101c10694011280142c04400e6a030f181c090100421260103140705141d41281444401c0d61411b07907060340d21462940461032914150f80c45d00703045e030340c0503122940307583c5507880050020704001c00d094046000300c031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 411176079 1250 411174829 411174833
    0x91502130501051c090302030a02010501060e010f0c0f02030304141e0d030c17040b0406110703030906050f0d09060912020312040b1906090219020304030c05090c0c01020c01090b091b0906010c 84
    0x88602c0900351b00a03401961103c440301130180c2110b4040e00490f00317015000c1c4800b41c080c1c4e07000c048843c08010754940901c581c0c5040c500720340c812034100350084d8140008139020440b20303001c0290f80860001281c072138101c196100d4036400e0010761400659042841200c0040100303006002c01c00e00075101e144100300e041c24048440c41c0e0350300709030807501c0d240308005020003245500602141c20f8405d50406082617528565000d44011050306c654401e110020a48d1000c601c0808141c0d01005d582000a00c8081041c1c644130000700310480302112100303000780009601d00e10000944042c159100c800301e0160302c1e40d885a001640e001012201c07080581810b4103400c110a008031002080000b60150700c40c500704200514220740300f00c0d40821544207105c1000840c0101a5140c22200d041d940b10885844000b0703c04110701c0750035105107156000081005583c401580281c00b000d01400002d90070340c4070341490310345404980e041c0c110080c180406209651400e20402ea4100f141418001c103420714607 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 411177329 1250 411176079 411176081
    0x18030c060103060203070f032c1519060e010b030a050a020706021209120c031e0903070305071d1e0901150e0f061206070f020a0204020d091502130501051c 68
    0x90b041102c1a60700403050000c103541000c08090300300e103141818030501c80300705054000c4008074030004143e0501c0c91008a9214030030700281480c548840a504024644005040030340c0d0310886079505403a00d00080014401c004d2551681030320881c2040e589541c4500d0810340103800e016100020155081110a0000d0403a01c014524450300140c0703441c0303d240500c01c0e81d00300018021021041442042503484225003c801c031380c0943c2600d00341414564110f503900446000f0b91400c1c80d01481101d0000c01030201c001000e4088134400205050a10281e0031084003100040c2c411101c0c50181c0400c08504c0f84a000605600107000b4000249180c0c40c0072417640004800c1d480380117001004000e01180310303900600036a10101c107407218418100e1047c6502da0354032008011138100810140744401161090181c02207041d0010001d5448003000c82a8030018903911200300c0b2182e400c90044840300503140203580583c0e940e90480400d00d450440191016405001d0004007030700b240f11038525600403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 411178579 1250 411177329 411177331
    0xa0e01060e0a0515011e0c0c0f080601030b10060e0409020310110c0f01151203090e070302090306070216090c0306030c0e09160f06051b0d02030c0c01090503030318030c06 75
    0x205900200d03113401c1002000b0480002150128100144004207510440c1400200d800b10f034a01d1821140d007840398241a84c5040070340e0002c81905969820026618000003030050582e401030315000020b1f140c480c188101c5140901c22980882c08990007052f06107881d0384001c03c414005820b03a01420f8414080c8000c640103401410008400403c54911024080081e0000c140080000b00246441c4e40d18420540171944075445060100d91054020541704400d00d0006010060512990703043c401300190180d0040417107140a44104000103c4692000404080041050710196012810080840068640d00c403181d014140c035203400000082c20043c50000a101900d155981424012200c500700416061034201105001d1000e02594242080300c42c01c4a0440c01c141d80d440ca861895111042000400040301e0300403611824540342d000b2008060540740355081c1c91005a0000040d5590410b500907a50564001d00c000360750700c80040341c2c80302c2440c4880200ca04180703c079001e01d460620 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 411179829 1250 411178579 411178591
    0x9030703030f03141e070917101a010f080a0b0d0f03090e0c03071d0402070318060906050412050a0b15150301050310110d0911120f060a0e01060e 64
    0x141eaa001002c80d40e00d80300700b0001c0210092240321a0801e4075040080b1406140180d12001c0341c0c6001c211102e0144901000800c0d402c01d0329400403803100000c40e181c0d5840c4854000d81403c210b1540c0301d545015412212010050316100d80c40c04100fa4100c581240061002c05402d42d1080a861071741d5070310b105007011501c200550340130410f031403800a105440a62001400b0701c025018004106003542c1070326489115450540d04c1f24090704001d400c800e080000f401c0e04603100003030060a01d0b900c81c89444545403114000c1030120b503294021100082c4610500000610a100500c4190012a40c56138440c1c003c5003200c0c1200e5090b01c601a0100e001e40b01d90301000341000a500c00f07401d1410040258007d02c1010506661400f404a0741341c4880d0541e2950440e52492082c2c6401000c071f0035504ca4511051040140241520b01081d101c0c410f6a00035208076103002404217810f00004080f94209814000ba0500740c440002e0b98000c0c0031500f11140c0603540f02c0700d003c070b4000c58180d41d15225034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 411181079 1250 411179829 411179837
    0xe03100f0b180a0b09010308180a1a0d06050306060616080714070906080102040e0112020103060e0a06050102060603070f0b0a0c080315040e0606010f0509121023040b040210050903070303 82
    0x10901c031048100310781076280f130700e40034114070801000070400b16002c1e80d41080d0006494500c3d0304283c03000070302c0c544a58004204178051841c1c041c04000d804070107403598001d100c02c2040550f868400b05035507601c080b2011a4040d40402800744901c00ba96003654069110301440da0800940e6907490b9000c070400590b04042e6800002d00700a19101402271800401c0346400031843c2c20308102c104001c201050041c0710050b41b0801c040021a4480d600240c001e098843c030000d0282001510540501000e11490b23005100b0b02c00801c41614000c42e9082c12654817200010704c1501e0301b1080c41c0740c0e81000750203000740088200703507901141c030600c01580700b903140f01002c42c03050b001c070010030042300d0640003410101d6000303404100301c2d070360801184400c00449040c52500c03454488000388545003412650075240c09000005130b041e4071590058034500303a419004007180c003450094507880000c11900503014240500114025003030051020035001d904c1e1410301d06d400110408240307818401d82c000c41c001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 411182329 1250 411181079 411181081
    0x191706091506160623011a0d020a02032a16290708030112480302120105061507080f1b19030801060203040509011802090d0b0402040b010e03100f0b18 66
    0x2007074004141c17a000d044440c5191411b0390005c42c843e66580a481e11204003c1e50001c1e42a01c1e542c000c006503009009103c40a80030014028040600c0700700c1c0021070301080c443c1410125401ca1400500400c1e11803260f080c01c640311035030080c0c400c1c200405070100d03a0321074100403d2020505c00001540a08800f4464220720811351038140c22466206030f001c1d0303403e48040c10903044080048001104403207002c545401c00724240c1030341c24101c045584025030051028022014401d81034104511454040350313070141550019903030000f240300c0c1820080c61100308000080b2490701c010090807500001e0500390700c81010016105281000f00030b025640001070001c0c8c0000c25512009250243c0618406181090700d0308012905a110600039108100c0c14007044030050340480d030503070700d4000c030040684080c607840d41003900d0042c100351000d90150741080c4140120354010308a881e40134101070700a00040c40c209203090010b002040f4000e10f00c2e40c8543d00084641e80c1c50f0790102c21081000c8105000e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 411183579 1250 411182329 411182381
    0x3090b1806070c0b0a050c160b06100203070201090b030a060f090203042a0605030603030705030310170d120b36090f0d141917060915061606 62
    0x2070024010024001c20040e020b5900000342401009600304101004c081107503252000c020342c1c0341c0075411001110038100200d010504c110f0b011401d02948080e90090100050204201c1e180d124003030019021800940d810400e5140340d40040d980100d861000091454031040c1e4807031914003c1d400201d18940203c28001805a040d0b1901100100480b06a00150b81d600d0069000f03540c601c0354209100300400041e0460b2410f10441e1207403a401010b690fa28036040c1c5400715641c100c0d0003005c0e15014001d8000c0140503001a483c420200c003903da07400512241c20440b8007078810060001c1d001201800f901100344441060342001060203059000050320f9203e0620103824024490340340d9034040c1d606000c00c7d440c003145c2c0802e0a54103103820480804e801c0c07000f402505c41c1c00005108a01d040740ac1a1115034883d800c0310b03406400102460154480b0300810441c400b046c0c8a00078040444a03a1540500d4050000d0107041c8141507000d0a09a00e030f11154102c030500d24201109280206542c20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 411184829 1250 411183579 411183583
    0x41b0b07080304110a050a170c060714060901020717091c390603090201020a0c120c09052503180803090f1b010810030f230c061903090b18 61
    0x760040b016603140d40c205d40780200013001d021070b600c00c4070340d00d484004405250b50428005200800f9024044590f90401c6280c020031895260201303080d14000c1b41d000c85c9402806000311101580c01101c411242c6e904010410003543c440c1c070450307502254400350340e45030106c0143d2924010b4060410020305100d0340070382003c003400d04031400d00e849008036006101c40340244404000c0e5502494001105c034400c2c40180d242502103500540f41d0103200c200000c140b84012101040302d17208003220466142c1d50b909041c00e4601c2a2000c0030f111034011040c010701c0d42d01c480201c1d07810120f842d000c1810b41030607103407006a041c40351050f94000f40010400c007440c00d0030811000449409002000e0003016542c0300803480c000452000c0c100411240031400b10001e40c6030107005160040041080150145044c003007400b905840103252140341c44c8800e140650101c1c520f1070081c006008030381382181701c0d100f4410a000d4590b600d414036603030340910004500c1904d41a441004596010f0980084243c003241c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 411186079 1250 411184829 411184853
    0x150b030c0a0803070f020402253807031e05090c03070501090b0f0904050c190e0f0d0c090507090f1a12040609060e0a061401030b041b0b07080304 64
    0x15006507214a01002082c400200311424160452100311401425100050103032042d020303071149a105840700a500103010003041d001c214480c170110384001c1e5241503030411204140d04550425004019007003240250ba006059102c0078500c0d00140319015488035407588059407540c0c1009641c1d40080054100040241d4010828124000c0145520700400240241254064030050702d402050b0000c50311054020b48600c0f0b0001001401540341c01c5066091135008483d041c800506440070304400c05000380051008010050002c54140c000f45e82440000d1030010411502c6c2c0c44901000100c0319064403a0728003581c000c2d5a200c01d1140313031821459183c0740c15080b00d030311050a0030180303106800320301c200d981d590b1942031130080f40d030366509091004007401d02000c4c0495041840140248002080d440d4101d8400e0004015400100003201d6603a8004d000c02040891400041000704007d0b105a41a090b120090411519201c400300281a041101c02700c030180008000c0c0420013019072400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 411187329 1250 411186079 411186103
    0xf0b0306060405270c130c080f040506180c0312040302010207270e031207030510060219020103021b030c060711010b150d020d02040f0303020123060f060403150b03 72
    0xf400700c0c0c1010700200d42c458081c08100004a4415403032504030b5002071120400c660b10090840c0c4a00c68000810b00240c00d0804005002608480000b40064003034201f847c065504480180400c1d0b480c1032000c03c1d0b01000786004081442669029243c0e6039082090103a240420700a05843e50310318400a450500940c00104424204d0b03c221002c010311106502540e802980c00400d40c1400044102e00b54402d03070441e031211400a02c00c100301290550030060140380081d1000e00d0b2541c0d2031200320384603a0303001030700d00800c985d900d4400007641c440c1d0003074040603c5082007540e00004c0da0f0162441c0d5805110400c9807608400104a1b06030740040c2d114201d112854004c2c000345007100c0014921a1001c80018002d10340428030120401048e41a1080704040c0c80c1c00719a42c0f43c4844c8985d1149440b031104a00560820700020b015550102840a8100b078150405c0129200c80c410840c0000d4034000e8140c02c50410300000011804050450480554900001940c00c00304000d15080020b82000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 411188579 1250 411187329 411187331
    0x80c07030206040f02060706050f041101090501120e07080a050a02031504030e01141c14070c1e03030b04020a050c160f090506040e0f0d0f03060b030105040e100f0b03060604 76
    0x2400020980100e0416401640003044111801d42031000400d03d01580d030b400340560785068108031720340417518089030080707003d8441070807000c0054004642c111118001c8900040000c40b41d150140c006410a039403156410083d69002915800300510f8540d00d0001980d60707501842c00c6d1419130600b407001481001c4013500401103032030651005400704030b00070703400c0f4104011040c07030206403142c8100303491070000b0040300b0940c40303040042c60304041d02d001e092507210f0070784200200304400d00404600b5107a0b81c2c0100c0010094400303851036012050f03005400d034181515800c05500c1d81d0354510042c81b03040b181c3d031079894403001c48048040c0362030741c2c3c981e170003030300e200c46032010b10808041000c6441110084200482c0355590400824040d1042c00050a0944991506a100e9400200b900e00c5001102c0e0746051104005c1501103050318020b1081c03072202142040107000c00e0030907410500451000c0000c1b1800020f00860078021a01032400b504d48841c3e0780c626141d040d2805105403608500704440c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 411189829 1250 411188579 411188587
    0x18060103080405120705092d070905010c170a0306170705060f22030b09161409040302011808030118050c0d0903140408060711030a1403060103061a0a080c 68
    0x5038031140e611070b0b80600b900c910a02105001610402c00080c1c0c05410040d120302c941c1d04004406240048a0503102d00901c203007145000283c1811004280c411906a5659902d40385447d005450030a4000d03415925034031091441d00c4000c180c07000600d1903480c2541c000a450745486110407016004031100d40c01a0410001042a5661801583c1011502c0d43c8120341e62080b2040d02103403034a40f01e2a800134040c040c00c0000a2001180d0814030450106c03007900c840f4078442c03c400140c00a54012540b1807508074002c500141495813410f41d000e882800000f81341c05240340d8006c0000034039001122550f01c0000180a88061941c250200c0300c052001840a82400c5044122074040c000f54102d07020b42d550b4107442450301c250300c01c4280c0c0206800c40c555a0783c42d6400c240c0c0350760003143d000002c1007200035008100d450000403034039007451079503c00d1800740301c59908072240d80c0081c0900d0304060311018040b850708080743c0d880b81181c00c0803070000c1d91114500d0740a007881300000c00403500070340140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 411191079 1250 411189829 411189833
    0x2010f0302071a0c070b090a030905030706020604030807110624010c0209011a090918072103030b0111070902030603011406151c020703030c090f0b0901052a030318060103 75
    0x82c040c0c43e94031110007407082595803080240c95160191040141405029105101040001040c1c500c580c80c000c0d50341d14880307074a40c1c1c10315654010718403a15005a000c0000100440d1250300d105821012503d410720b2002051007041e8584a07051f03901e0300c6d40425000900d1300001e514038581d40d440b4001e00380741d442c99407160005030180105200341e04203072540c1031ba1400c038040750034111490900000d200e09510300b0000c0b48110301d5861801485079074403036000007061700062411340441101420807505240c4600d9503044020300040c1e001d0764180580a0208481c089085c030031400031b400952030058892400d24101425640481c0c80c11103803e44160038008030391a110b00907401581e42c81c0714a80c0c3d813400030500d81900c5200c0d1980c0c0401c244049602000c05500d500aa640b010700c940c0c404058a80300c1c030503900000c685103e2900780c04c9c410010401154065000350503c0038800c4100b21100848039980b04a5100300d0381409141d4200004007d1350394101d01100c1101d10003040208072541c110b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 411192329 1250 411191079 411191093
    0x50103082d04031b0503061914060913020a0b0c01020d0b1f050f160b07030f0516030e030c01141b0901050906071b09050702151e0405030d02031302010f030207 70
    0x41d02014042d20341281e2801c500800000152000f01000380843c2c5140c41c0c2001c40190806905234a0380d0003908044800035410209500c032400b94a005080c000035444000d01500a41950f0104036002156000d00080cd16003650281c00d140d9084400560b445170b04811540c01c0799024151240300c0c503807246c00170b0300da0b0030143d2500d000361110b0300b00a40c1c0c1740802c200c607408901071014840c01d003070703850307a0040c1c100601c07541114019442d07918180b00c201300282c4240e041d120b0444070103070140c00c44106c1500c6680f10750020310002c51000d01362031500309800c01890954460b00d80c40410381030070101303200300003441014a80204d108070380700c5800c01507810002046840742800c02441000d0229019080c824466083d6002c0801503040840c05641c410b0041e014010495004015000c1c1000151610100d030640620900101245505596080c03c00315446840540700303480d03510042c401c5440000e11407000714018809900440c4104800c3d100044c024010912070b2820140144008000140c074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 411193579 1250 411192329 411192337
    0x80d122a11010c020d0e01021b061305030a050304052701092a2c030307061d150603070f14130e0d030b041b090e06060706050103082d 59
    0x400e14080e80d0050504540800c040c1207104000d51038030a0040c1e0007600056071104058907600d40b032202c02c0d5240300580e100c03104a803010104c614088113802c4031380351440c020302c0c0e030a0a04058506180d00d54003c05e18001404004a50303039400018103002c1440d24201e54000640150900300a09513050b121222030601840b50000e455101d800802c2c5007000e1015048813140415602c2c010f0070360504c2c00600604001e0301c01d0210302441000c411410308040031800ca0301501500441c81c02c007407540c526000b00340c40700c2d1040100040d03030320011103c0030522103040a0855020051110b0501d9402c140c104130711903000d014080960101001074018925410714201812140845c0345d01d54020041c7c0940704000c604405030040707034074a510131501039020715101041a03404221421412206000b0803690044d084c010a0075080108035800c2c1034905a42d000c60702924090401c201581e03820705948007078000b110141000b084542c009001150010090018a540340100c90f2003501021b1076445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 411194829 1250 411193579 411193631
    0x604090c0c141906050402030a02180f1b1c0b090c040e0a15090b0f090a1406030c0603040b04030507060f0501030b0603010501030c060e061c090c0b0403030e010305060316080d12 78
    0x2417110002029540e060040031070f451b4028040c082211141c0840741d074525011900c01c0c030301900e42404a038131405260b52641421207503150452802154003c02003012984944040c0036603220343d0408070b15120b00800c0343c062900700121688490170400c0d10081004c00802c115801403600120805c03101940d1020012903c070b07010001080074060300800e540511a40d0680c0e000191181800300c0180d4a0703203c014404400300420f00e0700d4a07100100744c1c941c072114032510790100382800420042030001100c280c0240c4641003403442e055030350b40c80e5019110405002107046903282d0040040c090300000140e40180c048008000d80d60444d500d00341510301600400c0200643c40c800c0182c02e441e444111400380b9140a081c0f84035001240c1c2d0328002d045207030703001c031000c000d0f00c400040c1c0014004140c90681c0d030306450f100b10904091004400414001709aa0350601c28824400b8004010141641c09011746502600c9807034141880544000c0500340d000c2c058030300c0c4c0340c980340341403000d92106500f0507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 411196079 1250 411194829 411194831
    0x315090212060d050f06100501021e07030b070c050f010c081503060f1308072604060806060d020904090f20130b06040f08030a08070f020604020f0604090c0c141906 72
    0x3c5564103000b45021451407000d1042c0c410764080c4001e1224152407441110b0090b1300b03c4440c00000f40544100700c1b5100d0210b0115840920240002441991065400030441c0b5290a1502060300c440349050341031a407000f50390b5540c18402660076804a05940d014218a080884410041001c282c0d00c0e074000700020700001108000ca001580d08901e15410207070403180581e1038400b0703424046405102000c17034403500800c40c0104d042910306401031ba400c681031921094aa40da0b000c06000c60b5a00c83c00f400043c06600300070943d4503a0b51407180348290340c040c0300200641c111034585199141441e0041348404001d207028a162981d030400101012411550086141a041ca02241c8140269044680c00d0f80c000b031404207600714000701502c0c00c00c41030359901040e600c40d0041601d1b1440c0c41d0880700c005801150004000d4101b050231480402c01c0071740481e01c1c040e82d03100400122400070030f414000801c46d82c3e030700051020a440a40f50841c9040160100b400611951614246802c0c8018651 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 411197329 1250 411196079 411196099
    0x1205060f01020d2a0c090f1806090c150f12023f04030512060429030a0804060203180f030601031b0308070f120207260f01020a031509021206 62
    0x11022030507085113003144112001c15610701d24180d001c985141c01296000c0d481c1007440c4015003258081c0c288012541c0006040705040390312510041c1003070030b4085c0c0702c2c94140080025002c0280c20501d07050f410303d0340d800d40c001041a80041c2000d80d84001940d1450061200c07440d03400782e5024030160910085900c0e40380c010303400303080140307802c0880c03214560303801352000c200601da00300004208518000c000190b16503103010400085401c4009001a0100001640704421101c00c220b411030f010014207e6446d11159500c4242542c440c3d0441d10041e040401c11103260801c2d00255102c070101290200352120007840803c0c0d43d8681407001810000c00280024203509000010802440c1c120b01100d1f51812076003042001021401d0003100d60715405031543c08002e201207048019602d01c602c615034602d01a4003140d0b0704038030050101185010b00c100d172920070704091004044401032a10041036209034444001d180190b1130b400b420080740100203500419041542d02948000c080303441141c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 411198579 1250 411197329 411197357
    0xf02100c03110a030e070b031006080c0903010e0d1b05060a0908040f0602030702010905040e0703030f05091206060907211505031009050f190b04060e030403031205060f01020d 77
    0x15120340c82d48000c50700302c00504001da0b10703855005104990303c0c6400b1240250342d21000c410f0648000c0b560984c00004ca00c0782401200c5c842c2003465003124114000c582050036a80c0001d00b150082c92444085901810072804243c4e0403403614250410600c5803021048019250b680e01c2c3c0e14002c000ca040195242c0c803c03410421701a003560040c14180752328003e11a01c03440065680e42c40340500b80d0124410210005862400780100c072500050030300030b40200c03451590103407101c3c1d500f1200e040920100b40440c003c141c54480c0c20034280303100e1500071f020a060450074851103030307800b41c0b0f48002c2144c011a60100382d481c160701700384c0032401018000342c5c1d525244075064645210b6040240d050003100241100b442c0e46070003058410380030314159440c03200c444e110039039108001a481168100350f544a000400d8504107242e03070290140328045840d010380d00c03800b811a030207034004a0200d60034464803080d030411446074951100301a1824160540d1040010355100d401000f40400c00c444541203080c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 411199829 1250 411198579 411198581
    0x110d14060c0408160b070f032003091011150403031d01050405010b0f0a03020609040b030a0305071a0f0604020d0f0e070509130807142a0f010f02100c03 67
    0x4400040a8103403015410021005503a0794031512a05a15104522648040b64580071000d030480c0c40c0503c10614200301c075a00c081d581c03e600c1700160180b00000580145d041c2d21304214401d280c0b0400055540c40ca9208204182c401000111004001c282a503c900c804e40c0041c031480f5088044000c840c407941d031340ca0128041c214600700c80d219481d00400341003882ca03054000a00940c843d1000b03100c04101a8144079052004030080c0d5441500b264080025042c00c030001c04030300402070000700da04240360000c01d03d0425601003c5000680c0000d5410a02c44004e1a02c0f01c0411400b800341e0f01403d2a141605120308080c00385481250700041c454a000c8140e488940080c0b4407100500c002042c00c280300361941d1451144034001c01e0070b10001903001c908404e1203441075600010b40d5003484403d48400c20383d40c011819046a900c6900c5a12005212140050380000c1b241800321250074042410b10040c442001c500c1414040d1741910b000703100341c010038042c2c0310442e2031388001001007021100310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 411201079 1250 411199829 411199853
    0x9030d120b060a1e11060c0d020c010507090f121524180e010501231c0b04020f030d0c110d0b0c030a0b06072001051c0903080a09110d 59
    0x1a0300c060b00140310b410460308000380420783c014082c81c1e85903000301a14260748000461921100030303044007000070708480a40c0040d18642002c01c20060a01000b418140d085440a0f00c0100200d20720700c204005440c0302d072030b86101502481130f0030749008080381c0d00c001042d008104480c503203a803034018108030511780d001c1e280c400a044041c8145a00c0d074070100341d105440c182c2ca02c650300700e00300202c420800105003d014101d43c20181c04042d1028800b003200203801d201c40b141c0d070b4000c0307042101d000c0c0641c810f000292428040ca0034200a420148100181c4104250010b8000e0b080150142c0e80701d500024000d88054002c0d0050b81c0411040c00029445400490000c2c00708002009100f42c401100e40954404c0c4200f00c4100b0000b20000c0c01c11130113019040d0001c1c144621022251200e0484c111100150301c410304000b410000f01500048103107444c0345144600d02c2d0348603600d500749540030301c1094020681da08200004000340d19404040224810803502600040d0001e000304281d40300c0c60 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 411202329 1250 411201079 411201101
    0x17031305011401030204050a0e1c05040b030a020c010b090115080901020f0c10060602010501030c290a0e040c090513110405030307030c0302010606020c1f12110a120209030d12 77
    0x708004003440b03210a905000038082640141d160034002403031110b440c4505440300350460010141004080307130145440c148413003140200002448009000f281c1e4070065401aa1407990140c0c4602c0c8007000607003198042035125200382010740040040b82506006104200640d10b050b002903501c000c00305000e4440e400036801181000203a8605818011a000802c807804100511102d80d80d004100d098640c203010103007041c21406410000b01030740071514030901c020031001c00c0082005400c2004035030488001172011400002da4860381c1d10f001d00c2116070425490070030703114850500010410005c0f00307081680003280e40f00c03482524058404140c8004003c02001c4030b980d000c440ca0b00526a1800520840c050340c2010340110f0340341d002280781e80d503034100a0314007907640c0e02c1000844200f40c080c0051070103110141c010b811403921a406804c200d80504441155191409a001060b69044200640d0304900c1440013a500355808904285410600d20b003000041c0101003514004059240ca0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 411203579 1250 411202329 411202331
    0x120f04210f030216080310031b03030f0809010b040504030c120914040f090203060103032001060608070815090405030a1b020607121205040501050103030e040209030622050303012301020a1703130501 87
    0x80140d0740b01c91f4482041a42e218801080c0140046052000f00da1071900000700800ca40000990000b8070982c0860351081c0c041c5c0020403800e002c0c001050850f030042d1002c0d00050100f50b8140d00b0b114910300842000000f0b4900421081c4c90403580250a21120741e407103201790341390710f44800076403c1034200d1184103070000c0c1940ea40f56928075001c0c0c81d80c20413600000c119410110704900714403062050b00201c0c0e0958859201c00d94407070104449121005000ca00840b200401041040c0c4400c480c0c00d00c914490001159204040c00c4003a00c0351004e030b61104015503d461300c28006844030b200341e8071410740c421001d5000740348250081c0d58400c0302e9104803120382d1400040000340441504001c0c122402512241c1003288450184010b81c0710303041410350954044004583c0d19000707000700200110344903030300e1a49d2814507955142150300030782c0480758a081071102550b0f0640000f0245084003400d0006052424050b501c0c00c51554201884001010001c0300250001216088007070100d60300c140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 411204829 1250 411203579 411203581
    0x20409050c07020a050306090304050409080f070302010c1b021809010b0d0305070213020306090f180d020102071106031303210608100b04050613090602120f04210f0302160803 77
    0x9007034207080c0c1103018240c1c86161012000551402c004c82c03030758080c2d580d42000d140782600785404e210140070442000c8401e804100050b0510021500c0079107425442540045400d49a86400505100760600c4040c04086203070061001a0b175408802d01040101064811850b0340d0014106d0042c40b01c1206940c01c142c0202d40b00041560000003452514403c071144c618040d07000c0700f048201e010446c2d0044c8c010b50700801049040070300c0300c1060b900c600041824a07944000e81c41c001e0600f10201015405070f90082044010442c2c0c2243e48401141c0c251016415840d000386020418020030700091300740700e59410000c01003038001c00001c03c06109142c0c1404000ea56010316907807407005021854089141c0b040da041e162070103001c1c00d40604002003183c0f80e81c030990704c841e01c010501180102c0341941c2c200101d4174130710032501d08180f0074408800c14810318506410701a00e5481c4490405440080c079901010000d908040002c0c1c0038038442c6001601c41c2416500d51710200c100e110050800070000c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 411206079 1250 411204829 411204841
    0x2040e010806161d011803020a0f0f080c06070210020705090f2203050406181e0303090e0606031303110f010b0a05031203070c02010c3f0c030e0402040905 68
    0x10780c0340c002c3c0c00f9a000b034002090442012556400c400b0000040808031041c801e0b82580b213003910000508841a901c800309a03298001184140d5650080c440c0c1e809000c07040090f04407002400000344070180140091b054210002a103501c5540c00007441400550a80740c00075200300100c0001c0c01024110207021705090316000c800c0c6000f00c0c2c903d0b80b03040c800d00c10140e24140d100706900b84207030b05480701d40c1030500301030060380e9032034101c0341000007042003650004080e00a9001194009003c080700c107003c500f941401004041c007500301c40b0030340b01040f051024a4480108070780e4440d10001905e5507518043c40c084a9091010110351032500c5400703500c0303440348019801212b840303030304441c004005a44e607800c1c51307103a0408100c50085a941400084c4846004901000356984149030041c1d426099555401c03c00c0b00c10041c40740500001601c2001c00b02a4a5444000c191084071100345081c03c0038000b01003101c0613500608014907040d03207001a44460301900c0c05081004414403443c5868 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 411207329 1250 411206079 411206083
    0x708070f1506050d0b0106052b020a020610030b040f0206070b090c040605010f02060f0c1c06090606050702030307260c0f06130b0a0b06090405090307030e03010c0215090102040e0108 80
    0x1c04801081500e45800094140f41980200800d0760b0311200c640641d0303180010544140d006680c04142c000500809500c846000b02180300f01080e00c940010703103801d10003000a203080e0008202d4403c8030000801400820504c060085c0e01c164000454095601c5030b01c0466018040d070705006020400b26010700c880740e0004140d158039410161010081946d548004482500c000400003016030031802c041030a074501003818a6000d40d0700550940381000c45050071003aa80781401c051000b5a9074103051020150314058603004001070b24215052000e1600000c2e2644200d00d002400f84051b00a96402d591030047c2c880700500e031440d0f03041d0701c0d8090001050380315580700040020b10b014080000d02d0f68040302c490551049d4208010365070541e1840d0780d00c40102048910380341e2000c01071100301c0c0c49950764051079200f0b842d600c02030350320307448185005000034002581c010b1199040002010001e079001464154060020079445899200c0c001c8150091140c0d801000702d101880c000401c0d28040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 411208579 1250 411207329 411207353
    0x40b1b010e030a0c150e0a0c03030207060306180902010e060409020901020c062503050d020d06080c030c010e060f0705160e070306080601141207080106080c030a0506010b0708070f 79
    0xd010244084424a840b8403d0302c4031a40031440c0da0300c201000c6800b07044520700030035001e140025103618840445250490200c02240d005885075000c0c020107034103101e1071000b40b4246c02c007400a10f0505502844604407890b141d14242c0d95500c645096a120382c8502c03030b003554040d03d1aa51607443d5620f4201030341c044c0000318058401c18071300e0507090a00104607241031450900c1c002d0207040107800d149281041d05425001c00038140580c1d141c14003540700a2100e410510300000303039245441d0106061407800f2041c0c82c42600402c2c0160342590708a012504142012507880350340d6610490540e0541c06440c01c090864820120704020a0310400896000d9a02043c041942036903041e004030300340c0780140100002500710100400c8080d5102403181c0607203074003c1401c0c001b0040c0c403070158900304066010482507911060200700280041c0025920a07000740c0c06130824008a880f101d9a500040c41600d0400c2c100007000e0003840032202c19161050380c8000c22400c402aa41080f10030031031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 411209829 1250 411208579 411208627
    0x10151b030e041a063f061005070201080708091e010603030315180c140c061f081c1106160801090b0f010e0102030d060b19020c0901090e03040b 63
    0xca0090a1550b00c2625600d0540e070a10003002545400580c3c51301d003c45c80c0b00781620a0310307115020070640e00104501a21002d0002c0002514507034500712041110300f01000300e101d03003400020040400947d903c000c90a40c46801030601800c0368413504c140600d4202c1d040500c4481510503c14001201d0701034005d042100e0080c0d40a201035140070044035940b0440740f0800300b0040018500b00c9031261103810002004140b0f040c03000410150b095012810362020880907450340000e010009000000d1808c0203150001444504600b400c211115a4030b10070000d4141c03100041099240c0240d22848130348004141d07500690358070381042115210414150882c000c0855002000403500500e14822074050620007400070110203031400042d00c0101131a840c00307045010400066014402601801c030041c1072251030b183d0340d01c0f800000c0104059992080d503085410103044081d40382c5c1e80c0e11046042d01c2050f0780c0042c000b80100c4d1464074601c2107901c002d800c050007041c0c09840d03001d815296a4008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 411211079 1250 411209829 411209831
    0x8060f191a040f0e04020d0b010b0904050109020a09060324031b0503011803082509083f0d0c030605030f120a05070f0b1501090e10151b030e04 63
    0x507000040049142c002c0b40141c964841d4081030412031041d60420f00d41c0c1281c0082c00403030003c4010388441040b2802600011800c0600282549050070644559801400c03400c0381107080c00c2280500170030382040b030f2051700e0405444014442803166421030007502e840714400d840c01040d66034035211074000700782c4e10a95400c0e0018400080c00b401e06000b1110003940c0000d4040300c40440b95021740c3d6404028181c00424600201c02c444019201070344280466020346911541520349900300b807070300c0c8555140903e41c140c40402e1303601c550b207100c80002c8075007039604202c041c03903140342421880e500541e400381040c10b060030112401150035911920948106405688824991118550b52441c54500901c2c02e810200015401d8078881d0000e401d00070312031001e90345454a183c03900b02c0031144c165080702c9100f400083c014420b680207204907008081281b6420700d6454603001404908000703100e108029030700311813000400c0d486400f040c4540c01408a0b0781d9100b00c110f0070000c1410f10f040c0240740c010f03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 411212329 1250 411211079 411211109
    0x60603031e021507020313030b010513090f020d021302030112030833010314090d031b020a02060702010c061508070803040506181f050304061103040b060108060f19 72
    0x200c42140160800d101c907400414000c0c0d603407410890441401054502180018861640100802d01410000314001d1107000340550420040000c10165000ca403001507142c03141500c00200c003e00222000b40e0100d4181c4041c140030b0000c41d200c071210300e124020040c4000008205440d241d800f46d60303800e020356905801e50366422455012230407072100002d00e05001c0c0b200b000d09842c0c80d400c400c0000c141850085500d64880300280907503039003959680b1841e0003a0b0b0075014100e03070500c40e84492000c2448111038101c004e00c000780d1a540713405006805108c0003d404801e6900402c45403010903888002001800101c004131000e5800c030f0f00500d0124007408000060b00c00f0000140d0f019030300010502d52504604200c003008400c2000450b540101c000212040805e4524420380364a11540e20b0b09641d03441c1c6803a019048405000c001d11050324103000b40b0010820a06031141c1c000002c2c20400070503268000000c42c00c403140c0c071955510492841100450700190101901200c402a03020100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 411213579 1250 411212329 411212357
    0x6030f20010c110f0a33020307080d0c050f0c03030a0b0303031b070609061404062306010302160507152307020910050409060204080c090103020f0d0602041206060303 73
    0x18241080c0040c00030f00b00d45061038014070301000c65030008600141480b190b142d135424031001052803002c2d81440f2a0650f0340540042c05c000b25542c072034009910103940741420741c2c0d680246500401c10349500840c0d0341c102c0d10149070b000d07130200c4243c2c504006000d41c0340c0307280000c11683da500440e0079010303403030030204114030908001050301c2c021405001c10321132204207011400401c2d0441c0f44251030b080e80700e2003180042025842541241428022070201d1132600e818000152490f100c121100c0007500b2001000998860740d003d41c01942c00d28002d81c0e07410f40514010381c14221500c000d1306a00411070001034000e440c2c801083e012180341c0f14034050f891405612400030b0001520102405402c01c5501d005181c2003012944c03054031040020798282c1c4560209088a0003500100d031016400103013807000100030000384880141c11610700301d070313903044d1360100f550394468100e4540100c40001420f420010140c0550f0702070021002384210409045c180130001c0c2076180b205801254400c07444180c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 411214829 1250 411213579 411213587
    0x40f121104090b13020f0a1415120c160b071d0f060901051b010c080105091612021c0f14100e06060306040b061309051005011d030106030f2001 63
    0x72003e070442c490140c0f6503503c0440e035148107528807003268440c80030106685181c2c0c405040d01d0160416095040348a1680c505000640e199081003d031550000d015110a806541208a52141034021110b488170020300c0d030080e040310080c038014115682081002080d070791003502070443c90281c001244c1200c40100912124540180400d83c00039401c1100320b5044d40200000c0c03400c100030114000c1c051101214107800c58100001d4030300081e850800410035031038200190313038002c1c80c0d110144411040c5150043e140032400c4800e00160743c0c01141d0900540c2a241c58881d00c0c124901060108001c00342c1c22000130070300c01c034118885850001c041190300c50030000031303400c1d80da003200c3c4060141c42d42810004650001804c1d103034440d80310003100381c898031000c0c0500600b84104580307401c41401d2508510580d80002c1a02c0119103101404220a80c3c1c071201c0c081e000003043c00030443e008494004280502003503040030701101c0c4440403038400c02c031003001020f0302c61045002c106810000c00b00112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 411216079 1250 411214829 411214841
    0x7050604080a06150b070606091a09041104021909050a060212040b070501090204020d0c02070618061404051002030c0f150604020a0c05100e07080a02010807080903040f121104 77
    0x7405940100b00e4000014500c0d40150f1020300c00c0314555444a544228100c0d99602070704085800b552600e0041059081500415070300c060990641100c490402d00420704188004002800c808044121007a00c0c0d00d07658100e420014108101e9030710601540700140c20090f07107110f420300505901e403000810a10105104110b4000014400d207003910700388401c10385800810081e0707515540c4024140c0140d540d48010b103120014404041981c600c0b103031000e410500f1039801441840300c0702011042c012030840d0303001c054440b21b060021684131000c40004a90043da0040c940110641800000d07290300040030b4214028014100c500452040c0c031199110b02d42d10495a107510784071030211b00c06103401d801400e42003155183c550070280729034640e01d103040707026503148004503a20f58900c0d4003c0d10174030040d409024070300010205500a98002000041c000300b911003004000c03000b240105e1010f204403002480a0891181346a881700d190801042142c4412103910348503411105241c10680102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 411217329 1250 411216079 411216089
    0x70807030302060601180e0a09062316090801330609060c06020705120903010f020403050c0402031f0e010f05030d021c05070b010b03011703070507060c0212100b0307050604 76
    0x30f02a04c0c0c90b0340c030054443d0080c5907144542911004404030349a07141820716407041442000100701700010341001e07011100511021881140a035185030b01d001422404c142d00800603503501000000c070790308110360b810901d03080309a29508144d40000c58088401d00601c00d4101a0070000780c2d400c03080e10701d4007410b08a21418010411f0001c0030481e00d0b00881c5807034081c0b4043e403000f40c0342011a0f6503590800403030101810b4000350100e00071101d81001d00c0340c1808049503038400c500e06400e50321803d40d1000c0c2030301c2c0c41d441a40c001000034200710f004541026100e601b071f201c81420b80d8441c2d0044c1d0103c0c100f4020341e0f161000c2480000303800d18000502d01c0135230450390060440030034880e0510400c01145400c41003407140801c00d002c0000c1800c103800f802004421500c646039414201d9200c441542442c10f03c8a650080c80401c001c140c1c003089020841c0e0035410500d1400d900c600c0410940c1c0c0701c40d000c42e8034501034001c01e0044800c41c2d4200110741c040450903201c140d074542007084520f000d140a1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 411218579 1250 411217329 411217333
    0x140d020703080f1501121b0201060807051228050601060507020f0406260309060d0207020a120b01141c060e150c0a030b1f1d04060312050a030902040606020d02070807030302 76
    0x5400305d500031030500c80090864040840c0c401d80b00c0320024880720680c020301e00180e541d040d040040f09024444c40c0054141205d40c83d80da03600d940311142d924030540c09180c408000704400710240026006103402c520b507200c0e090b0341c219039461601414540181d50240e01441800e280c2d180d507844c01e4850881500c42c03500041140c6040390706c0c075006c085180c4208144a100400c0920625501c2c00e01a2411080904016941c0e1005105010800c9001e1b44100c844038690f0140000103840d1300443c50550308030b000c414003e1203040000410052542c58400b1a000e0851350400c140207103600079088010ba407400300e03045450700345050440c4041c00c03a03010309000410300044000c1442900500f400503002081d149408102e100078442c21040c0d50030403404117090400050304250600b4074400c5410045404020b501e196841d0903402c043c400321810100500024480714140c020340c01600d1550f00640200a503079224140079680d003540c0358804000d88600040012505000a86141521740c5a80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 411219829 1250 411218579 411218611
    0x1080a03050d18061d0106080105061507050307020603100905070f14071406010806160309020f060a1803240203090a1b0b0f04090c020c031c140d020703080f 69
    0x258030002091142203110b60f05419040202c08a44140a410131403400c2c0b01c0c91080c9075280d0000700b0b0840386030307074400e07075880c3d0510f81000650744da5401089a0036070b502100c166a01040d1501c14110300c90403900030340c007280200601c500c0d0841c07004540165014020108126150b1038801c2d01e00c0b143c840c030300000152407840d00e190201c802c0005016503038414480407160b14400c01aaa007091000d8011412340c1d44060100940200229030044442180b0f040402c100100c035008a041c290f4070303143d96401803500094624016120300c0030780c4c0c601000c6492031205540c41c0c0c90803414410585c41080f98031b40d0384c0260611404514821240105000c1d802048601d14a98683c10500200c120a500c110b403486000502082c640000340003948651000665403030402100c08215601c06421504545c0416680401f940380002c1687e10408419035088491480c11012142e00029103070b0049503070408101d0180c83d040350b4001d0942184640c41e41041950394034610400b5003000c031007810f990800b5075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 411221079 1250 411219829 411219847
    0x90c0a090e07060e040603080c0c1c08073c030e03030909060906011110060603230703050a110f03010815060312030606070204050f04030806040501060e0f0604050a06020a030801080a0305 82
    0x220f8030a242540580089200c0e0360303a883c0c02000740c10271110700300181c009820310481881c00c40c11511161100042000007031f4240c4e01c40c0d80aa000b000001060f90b01d004404d40380d880d0120001402c1103070203010442c600038010a04008038521503a0803404204280c040c41400e00d4088281e1b01c915402900c03039501541c1e4841008140c11000d005941404080333030040c0070760082030090185144000fa40810030f03030300c0c0010040c00c4a88484000003902c41084c880c582d803400c0340145c503400c11641d20b008100c1d078891030300c00f00040155214038105481c0015502402080e041c0103541250302080544050ba0301e42050078a0f024000c881c240c5d03044c1c10044201e507502020700090751704488090807170307820070300103074049400c548044e40c01c1c0108845a4040104240c0d01c208459444041598140b1072545080300181c106021408420b12a54000c40000f046458200658000b89402400440c10b1659210b020b074941d0310b108403c0d03000500300f80000c00d98410018a03848295071540c0c440d03141c4039480c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 411222329 1250 411221079 411221087
    0x1b050a17060d0609021f091418070c02210f070803070302191509061407110d0e1807080f0a060b03070302220b181806010c08070b090c0a090e0706 64
    0x40e08017207030b1218040300303020140000308050801c0c902a0352241402503041c244c000110035003800045120f11500c21100c0c00c1c0c1a180aa50f0340c01003154107042e4036030011407002841804901075035642501c04500c210281007000a08058019000b100340c07010b650300ca4400d951244500200a0090b0748561a880420b403000d82c1c01c501428010b000042c880035100030f100059484d00f0a0569002da1191000380024013107403441500031000f42000b00c01a03881d001038903100c0d0f18054800c0140801084585641d1f01c44032015222021005280300f103038a092400030f4507015095840010520180000441c030002c544035050039111f8202c00c450859907035410450107940940000c40d009161358020802042c140303044070700900100c0a129840b83d050300e50005c0381506102c0150301c503580345110702c10039034032036071159421000030301c1c080381c2c1c03003044d400c00f00702c2803158190060009034220301b044207140e030205507a00040d10031111801010354400782201030f1102d14080354074076000b40c081041b0080c0a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 411223579 1250 411222329 411222341
    0x403020120060c04170c0915011704150507021603080a0306050418030806010302120f060d0506040c080c01030e1e010f0c0315050d0807080307031b050a17060d06 71
    0x40d1150041c5075202500c1c03060b050240a550b90840c8040200702444040c544480c42404600714100410544002c0000036080d050b010700b16041c0300802501c124400d900c6159040c0c00307014040e041c00450309003840c01303480342c241d428503009400345410301250f0782d248003160380700f10000c003007901403011811a201d551565208183d5041815a2400c00203020f8482d4041d40d050103813100514105107515080180c82c42c040108014101441040502c07a8003180244964010121024420166442d400811004000c01d00003401e9441000c00300401c1042244480c030564a107041910f900640b00030043d4144e03517844001c1c8526400142004110986038040c410a0142c2c01001007271924030250740c80100c030003805804001a07103400c3c41505030714011848a004290550b1076500c071000c55120a4450701911000030a03001c0000042440715120740c000111100b611940e260002c4601400604564010110100070417980e04070802928031410100703202d650054100100302d009a6605002048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 411224829 1250 411223579 411223607
    0x213150c02030319030615020f0d0908101a04110a02010608010903080402100905101d0d030801030b1e2e2106020c010606020304050a14010f030209042d0c080c04030201 74
    0xe86c0e00c50005107202c810580d0f2130034050a03006445960b50701d1029604107492003c02c03509000d0110010005401c0006a003004201c0001001134007c0c0303520248140b090492180e107500c0383c10051528803070711507880100071100e01ca400030001d4558641d010340c2a551108005000704801c203001038003504104441043c203407101c0c0780c800e400b00d4649001420300010002c0f8480000d8602010b000c442400021400780400c1c1155000030a02480e64000e0007036005003c000c100501d40c101240904030b115400034155941050009544d260088200c2500b9199191801d48554084161424542020081d4080d10800100c031900700103414a010700d000205541140c10550810208808601c01e00c00c090207003203141e025580e102e05e4034040003845c070059004899100c440e0341600d12030f41e030081ca907812803544a05001d40c07244040e0f00040c00030058a42100b0840c07501c030300c015003a907203011b040c1c036201e84c010350081001301c084c44002c6882e50343c100e580c0c503040c410401082c070156014070b42c02d161001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 411226079 1250 411224829 411224831
    0x1b0f0f12040302060106090e480904060504090c0b0a020c0a1202010e01211d0f0607081602070b070203030405100504030204060b1602040b130213150c0203031903 71
    0x25580903140c440c0440c04403825401a000400140300c625480340b08600105555400d0728983d0901d41146601024084840040045820023840f200d03080c05080c40c0490700c1000c003005400c00c0302800820180d200441d094840c030310b80303400410b21386010321030500d000e500070b0600558103082400803a40c582c00700a00200f540300e00c19880520350b0341c1d01c40c02c8000e0311030440e07543d0301d00c480d44c8000f62068500c1088103040c00b20b40200c60418900074440303c10b5113102d6880200381c444510750004001e20000002031300500400f201c01d41c50300747c00038415005030038990724050103940d102075a01142600350074210058000c84000c00c001d0440c81c01074019940001d05907840c00b030b62640015410b036030807011140440c00104042056290920640d4000e1150241003440c15010190004061007038000007445566201d00b01805915070b500102034504040c0713000c5542c0c0d5510601c114045905200310418207405100e5600b42074411ba14190704294082c00540c24a1060f500c15410031851141c40d400301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 411227329 1250 411226079 411226087
    0x90d0203070f120b0108010c230403020a0b0a0e01030e0309010804020a05091608060904021c03110d020703020a091103270304060e040e0a0c050402070305040f0902040501081b0f0f 79
    0x25401c820040801020780c0110f80454080900e05041e8030441640b00c0c95080e45005401d50110740c0145200100e0700d201550100010407400409a89000b07a0704047d410030301e44100443ca070008000108500002a1201142041c100d4011403e58104001181c1a90400e020303072070b159402038151a80091009212400946e141d90106600c00401c6488102d0a1108501c100340c40da04250520313085001071703d01d1041c0345025004035a640c5056040041d1030f02c03601300204181071082903080301d2826010300f550a20360345600025601d1806000c140d210707101034000022101d02070710a800b0b9076201301c2a01421542c0d144003210300040309000c0120546100c0003480d24080092000344090911903c1c0c84032052220401e000c00c880680403a078960754440e0500202080c00b01c00c0190445000f1030b801340c3c0c0d5454900c1c041f500385c00381c2da024002801540d240890700420039000b0b0b00075500f083e640c0f200165a01c00c544071540d4505103c8041446040085000700070101d0001e0241c0030b50313107003070340c1c60 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 411228579 1250 411227329 411227339
    0x619240903080a0206060a0e091e100609061503060305120703020703050a0c06140c0c120c1c050d170c07061e09051b09060d06060e010305060921090d020307 69
    0x942e400f803e005401038004404015171845d00015420244c001c400001410b0700e03002610a50b5800c00155150300721b461005d107070824100c200900c485135113864038148440b50755044014040d1620340107007290300c0e10441982c814580309100b9501101e400070001c25107890f201d1156140b5502011041c0c04500030700d100400801d01c02c21036116054401d002d0500201c1ca4580e00410f46110074249c3c105040041144417132000700020a08441c5e2000c8581848210601101c03e2402c0352000c9116046410800000005000522891790b0306010f2019900c00f41000707041110b92034641201e15152858107404102c400d207600c000740108034410917000a4004442c0d070710f44ca90450100100002c9a1620504420020113100208a175180c103050480c151a0f040d0005150304c60042c203d41c05075142141140512595030046001000782004001040d40c40c2e040072500e40c030007151680130078865101203001c00b14105007407100e21840f2a12490a0580c60780421400104800007a40c4c5841a030001150b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 411229829 1250 411228579 411228593
    0x3030c0714030f240601110c010e010e0a06090302040c0203030f01031412030f2a07060b040207020a15030b01140415110d02010209040f020301050a0b0715140619240903 74
    0x120901e1481c01030001c42c1c013030303a810041d00540140200d0400074480462411902c0019a440140409007070458141c3c0c07500004841c18070303c00c4040c41e400a004c02c0005022a00b0908900a5a00030b8406019015408905a070f8a2000b5034001441031260b00040001c40e406010f03203955052800151843d003448034451054540082c5c0e01e00403090b4005090002ea00ca140c1040c40c909120320313400010718145031001300c1c5540641540502181d07140e00c5000c5842d60750754111598140d0042001c10300b0303501c50b0324160380d9090f80e40700003000c2443c091085005602034030743d10590041c03c47c660791400e82080c0210042581d899050010b100b1610340c200c5a41c14144048040c5e202c180d400182c2360074505c0100825900076030255101c2501c10801400180c64150304513040d10b203a29840c50f680c0740f962414468010700c05941100c0d00c0c2c03800020160001100d9000c60007602c04650a844256000c03642c0000e948441c465298003484a60840080320a600d1481c12071501d20f08100b11159a01d841d500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 411231079 1250 411229829 411229843
    0xb130302010921020c09090303070e0301020d0504050d110703050606010c110a0b0d0c050f041502030f0d0603020a0b090d020f04060302090a0c03060e07021005061c0b0f0603030c0714030f 82
    0x10385005004030030f4a1070142e04000760081018101d03030f11662401e0218a40e03480340310240c1400c00b0800800300340502a00c3c02d40444518401c5035500300081c1c6014200b00b92100301d04550800018080c140d00048080000348030740a0380e03000750145c50315442d800019668035242a600701d880007c80300308880d080c0e880c000751000404454491940c3c4c0c120000c0d012089035030102a400610106000d9018500400d40540301a2410341524070072403030356a501645540101180c48101c2040000e07000c0a604064202c0c0007102d1082d00e80c0c51032103440f040081002e0040900a03904540a003001001600c1c02c0c4005d48c401e140c014000144c40764994020071003400d02107031038500f400e40710400700421590600c1230b8402800c2d001051611800c10120094aa0342d191070008416600d81000ca00c00c0c2d0303035901912055012419260132410120b04d005841c0c04021120b0642e4000b4050005500e810003200311072100f44141d02400b070690810720f0401131145120940c2d900741c40b4032900740c40b10035030400281c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 411232329 1250 411231079 411231113
    0x80f211804022b150b130f0828050604030c06020408030d051005190e0a0624031a0f30032701080c180a0b0d0f0203040b1303020109 58
    0x510403910107021000303c14140d46550310040c03440c1c0520200c9482c07500c40c2044c00c2d2507009008079074403000c01145648070207640d0020300d212480760200184030003000421402c24150445110046120054810810030380707280e020b0442e130004c80000f0b0020340315982d207031001d038481e00b401420280c0755100185150850001c0201c150350700d4080c002c902041d81c00d000001c145c1140c0e8007452804c00002e410314145d03144140c0c0f070503210000110750300603040d401810151024904400c1c1c150910f4541c1d6504001c0c2d01030700800301c0e207071001302c401a400701e1000c0d034054100034100307103002c02c141c0080c001e4540d8108c0a0811f118016528107030000c510442c6002e02e0741e440310045072600d01e0360f90b1b8100c030b048080340c0d54180b44000c240e0030718060742c019a80350340c000c0040300190f85412288108001c02d460405959520000545000c40d01012a401a03c1a81c000ca2400c02c16030500000320b03c100c0c8000d640103024003943c0c0000a684200305130801a00030f11a200128200b8026610180b24207600e40c11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 411233579 1250 411232329 411232357
    0x20918060c0f1b0f191103010203150907030b0904030f08070e01020319020102040e0a0501080f03030105090403030e0a0b0703020d061a07122c130203100e06060c1501080f21180402 79
    0x3101e000e00c00746481b40c1e08900400c9008602d54108052003105c144880407019019030f4140c000220b03801d01a61008a40c02c2014140300942d1420b441c0051003483d0015400700416004404140000d11507038409041c040d040c0c00961500780395084180003400c14481403421503408000104101e80c181000b9801100552404500340d4105407403942851001740d901e00c03a0b9031051004101c3c0d0b950300ca0041d074000c2e81600f000039118903020300c01800c0044110001e804030180c00140002550f043c0d000744048008010200021612083d1111210920914850000006200d403401080c1e80d408a00346465813810058064040c0c000040d010644c902d0b03044100c020404001c44850800c91580c00100c12107040441c80d515000520f00c852020a00510810308170900005025888030800c841c1e02034015011030700b041030080f515079541c0f2024010401799003e80b0000c005a9000060030f10640f000111078246c0c298900650142c40341c00581c0c400d04100c00344c0e003e81c24a41c44500c0240800a02924 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 411234829 1250 411233579 411233623
    0x15052107080d030e060f010e13140c090112050a060507090e010923012102040b1c0c1508040303051b0c011505011d0f040207020918060c0f1b0f 63
    0x1000d800c840c07980d20404c3d0141c0082080140251581e1459410744410f20038000054640b44c90700d24043e00c4001004284e0f0300c41d440d20500403500000c40c41070003101100d82407216a200c0081141d00d051003c070040003a032080580b100001d8164008503480355003450242d09403590754042003101e03070003a444140241d644800d10002e0004051000300400380c601840001c95152001e100c640c0b100d200030010340ca003c0f01c0c007014119a140d400c4074626150041150500885101d91006030141c0740d401100d02071045000050903180b074460403200442140c40d20582a5030303603202900a820f000b03045010600d504605100d607200c00718042c2480134061400054000c00c041c0401d004074100703410481c180700d081e005a4064020ac04800c507006d40c0d050310003140c003440c1800428040e000d5100f0003540040c0e044104aa190a003c00450b001a0764000302e50440c2ca0f8410801c4041c03051000d04002204c08001c0c500c00c0c4000000d203105840c01000031a06011201011103060030788105c114065401464 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 411236079 1250 411234829 411234853
    0x1520060c0d2405040b130204060306050a1703120703111603081003020303090609030703020d050a02150a051e07050d0e010f0e09060f0111060403170a1505210708 71
    0x300c1030b003003003607800030484114030203003a019030503822140314581c03050351581001c60325516245000781c040411982c0541d03c03240c4900e006000b525250140303500401c03499800040001c400050f41c4e40c402e0091018526100c0302c258500030200c07008000030700741a10340041d5008100490020844040002803004005c000d030306e0020007520024050b107039001c503403d5040c8050b94010049920004080320420707900c1c06500042410f00101b070380065440083e600c500000e0242c042140c1447d94400ca480c03e01d40d0124550038422070040b000343c40009281131000c0d051034001c045480039100150300d002800d16030b8a40c0c0c0c1516001c5000c9884c030008200009000e03d5582064510540303c46078180303129030707000c0e010100d040c1e11401000d03248a1010031a1505150340107101c1e1007c110060f81c103858044c641802c01800304804421b040c10700f03e04030300c0005e01e28019031188141a82c00c0450020743c0c90303e40300401800c818507003d0981c0300308040d17094100e80242013089000608282c40070300305005481c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 411237329 1250 411236079 411236081
    0x1e030a080105091018060e09010911060a0815150703031b0e010c170f130305121804200c1506040603150908041d06191520060c0d 57
    0x1a40024014114501800043d0040c503d44d28150703845003055001c5550b0032401d0401402c17041d440114040c038100144a184001904003944035400f900311600981c100e40240b000743d105038a541000030b100079001caa00000411412446c0810081c03040740880b140754a00030701c5501041c000c4003c60341d2104032440068200c00000c00b250b0349800c0c212074108001c0300180001c3c00504000304120102441641969518030548012110760b20b40b03070340c41c0c030601503040b10003059a0000b40c0302446840d43c030040c1c941d14207040780d0328210a602400a41c1100400f40000703420001d00f50078410004084070250583c21074040d21165a12100030151071681485046c1c07003000160540e809941001c9040c80461828074056500b0740341c4103c00601500682002160b034012508042c0d0804440c141112444c0c9150040c40d00a910440c2c1d01f0340b4190340c00c040305505800074440d2109449158840207862800356203005a0203102074103401e080e40405076000e0500c501200c1120014201083e2807141000f5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 411238579 1250 411237329 411237331
    0x6090504120302090310020d0e030406020601061106060612131b05010801080613030c08040302090f150103060303080601050a0915050c1207051b0402120f01080c09190209031e030a08 80
    0x2450804504d0425044003203501c40c100550b1001c50540c000640c1c43d40e030303407007a030054800d507001c1c4064a0f11030303840740f03c02034031507c0a1040360000354805a04052003900842d105005400040c0702c1071a10480b802d4801c03130315230700422034140c1075111020400410400c008207441c400f00d07017071568001f90414001402001041e04058076541c002c8081013620994840c40e2004030350141064441340b855894400f990388540e4000030b410a440c0000e00083e05002c2c02c6407801500240f24580288041000440c00c4030325030720020b4000f40c0d0f0280400e440394000c07001040c0d021860310745550b4041c0c0300c1e104050313081c0320302a0040002c0c000089059003d03200740620b036411a03002c40c0191400703034203446180d5544903000e5004030038100c0300ca444080342d0380e42e41110114070803510007513036910380085c2a507001d01091140c1a07a6025104250a151030a40403051003202c03a010a0a00201c207040c0000080d0000e518158252064040c83d003000000946a198207440c0d0380000c503a02c51010100802c2484 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 411239829 1250 411238579 411238613
    0x10b0a142b0c0206100e180f0109061a0907120b0a080a1205070b0a05070c1a0f07020a1a090a08030406022107080406050423030c010e070b042706090504 67
    0x124a0612041e4045c0782e445400f19280c14101900d0f0b0b407650404100c00d01704d00704054215104040c880d0390001c6042d08440385070f50041c0d80030000c03580d120210302e003d1040b40710b82a601c01107803000228610300400140600105a5100181d541c0100020801c442c42e00d42180d00a40d100021004c104204640026500c1c580d030320300f041c00d00100d541d5400c44160003508180f001d5880300002514103214009046c01e090300b0030204500040d178a03511161842c0250341c0c0e05020101c041c0081c00e294000140f61040ca588031319481c0001ca06444404410031b40900380800c80e00690612a000c690b4203c06980918010240103981d0903c0d01600c0c0d00d821880d19410b01c41101c58420004a26000240540c0c465040b001c040307100c0c2d80c1c502d09002007031500c1c80c880240c02041d210120b840900000540b00900c0c50400030000004044102a919080342c0710b0603002c580104818804a50040d9014043c1d031402a00c182c08100751a5649041e91031a4102c003200941d0340d010882488200c02480d02d60300c4c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 411241079 1250 411239829 411239833
    0xc230a05030c0c011e03020c010b0d060903020c0405070f03090c03080a0809100b090103061802040c05040825060f0908061303020114010302090a090f0c080d09080105010b0a142b0c02 80
    0x1788030711554042061081e0341e410185036002c04c4c81341d44000203410014a81300002d0284101c00040d1a1590040c112560203500600c621207048031941814442c0a0140101d52030b003042070740c0940000c501800061134100e45014000e0400400a03d070b00f40541080710307403911410028078007011240d02d0f100104030703014012401e0140181703403038450751451415240c00c0400400d4400b6042c644907040c84030104003e40061400e101440003d6020300a0419149850141c1c1e003030242400d60308040d40d41c2d006280322618010101044428091404030001c002142000100b86680340301c003500b071440c00c80703455401c0c0040d00840404c056080c81440750448240f030500001c1d50464002c42c1107403d00400c0e000e004c80d9101c68000034020f003108090051380c4d000d08046280c0da01c030f03d011510350545207880e074041221803c000c10029018011031b81681d295000950a185040200316003100d005600b00030380c002c0400054120342c00d0540741c200b0741a543c01e021030041c07a403606200e040300c2071504c00703000319 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 411242329 1250 411241079 411241097
    0x71707060f0e1e1914040b09060303030a0506150a0f090b031b030a0605061606060f03030c02090c07021e10050a1407050721050c0108010302010c230a05030c0c01 71
    0x5076862180f030360041d040c407440e0745407030191440c04180c10002c1042070307541c070000c146800108204020300c0d4803040407064034140705604121040c00243c2800352081941908180002410701140e50f00180c0d10000003051105000704814008511350700042d03558000440403001030380c0c3d42da009000f060040895010151462804591562042172021502c80a00c24000046912a12143c02c54400341c500100304954504d8031500071141e20300e070004125442401c0003000a0298820f000000403a50103444420f40100c441c0e007004080c0c81d0090402203800f50030b003c0940961203a1510340300301d4500584210107207200404000317044205020036020000c0c10010369050302d0748032004200d600000c0381c04585075115460490705042c000e81280c81190a0b4140030303160344080707181c542d0b03043d030003802a0b9801007020401100d00920900002c2e000c81d0006840000103040700d20110711403056080d442138a12080f60f5654102050500282c98580c40800c10b41c4807241b050001d208204000d00303000c0d00b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 411243579 1250 411242329 411242357
    0xa0b03070206160c0209040309090218190b03010e040804030609030f0201050606031b0906040e0f15030a080f03060a030821010e06010903020d03030f0216150c0e040e071707060f 78
    0x1c0c5062400028020341942c40070608143c000d005600c090242c001096494040140360105245008640543700384020013150045c04a2141e04a0643e015a02903624580c24082d0741c2d1018076002d0812502d02c402040000007148040c41100c40e028487e40d100d10042810b02e41c002e007501c00261945104140400500a41003413104000e0082101044070644940340c0c8000600107024642c0580900e4001e0300410011504a0300014419048252100303038000d10407040c19580c0005c2d90300140740707880401c165090349992401940c0c1c070041c01050f0f4003802e6140d40d41c0c000213070480180f1000ba0424400c0088126850b07040050141c81c502c14007101c01d181a4000a05503551884007901a030f1800c07038640c050500c00e0304000300b4903c40790000d55980540c10a4843c1fa8401a0801e0702e404000c04500c0f400c0c000c007801080aa481150b0741d200b110311610040000401070074080350078501c6051400100c08125104d0f6010003e6008046c2c9001c074074104000d041900d0800006013004011065140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 411244829 1250 411243579 411243587
    0x7083d080c1f030c1709060612030304080d020306130905030a090e10120c2c0c0309210405030604060506040509060106121a130f0b01020d020705060d0207020a0b0307020616 76
    0xa924518a40484c40c080c802e0410b60306002d410440381d0101502e10100b01c0d54000001c1c055010781804c0d139941d000c08081c1c0c04226240d00094400501e215001c2060202180403600616040390000b8221603440300b021075858111000140e0480c1c2a03000462040236454100c80c140e0000d250301c249600c807030f19003074055407403507131540c0100c0c080d441201c1042402d0003003205401004c1c0190080c1901c05c6180264503000411320348990964501e2100002542c0ca441941642d0142002c00011b200c146100307225a103400044110b051220b1f401400001030607a002c004150140340546000540e608110342071000341e1b10f00900781d038941c1d03210200400806c6e9200200e540300d000b14500c0055940140d07100d6600c000701c40c1c281e00c4d520201584c048000340c24151301000d19580d138072108200910307c6000580c0c8603d001401000960401c82d410000d0382007140c020400543d41e100014a05070260340054030302c900e2038114002c42d02003c410411403540400441d03822007404984001078400c4003c0c020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 411246079 1250 411244829 411244879
    0x1090e03032a0c0c10051602211209180c07061505060301270b0a0611030d02070c090c09030807020f01020f10020703090e07083d080c 59
    0xc1003014084092050050102c102c0e0000c00b031005050641c2e4111040b451640c904040d5944c0e4030994005644081050103a011101d0541102c0e00051525400e0303000c0001d60034486804458280c0d2000a840c0201020701080040c821750003109910b42c082a802d0100f00b15140c845000050050414080401c40000c182c50346103602003808512900c80840c4441860b0560f442150400008000424509440400e84440c0e42e01c05124102048180b8802c4054614003007040740c120300000300610403c1d01c03507003011240b145040700b2030780b41c160241180000c0303a01c0603a0130b80703150030000f40500c01a0310a000f00001c0b510326280084003d420343d104c00d04c0521881900074407404c2605195015a4002e2084250583c03c0500742c0300d284d0090316001e00a0340c0010b808400082c641d04001c190012808150380c09640d284d0340f000040c0c0e903400d4500e010101e80c4c80000103110704041d802c0540041d41006400020441c0525403981403404400c2c0b0316211050704100d00c0740c20f000d02e40d101c45800091800c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 411247329 1250 411246079 411246091
    0x1020c0a0314132d0303030207030806030615011101060f03080306100906050904020726040503010e0a0b220c03030201060905060301020711060a210203010623070f02060c010c090503010501090e0303 87
    0xc07514612130500102c1c2102003000700c01001441d0144000306040d090f40c050302c03099020392520180c5503651b100b050340f1840b0031034011003401c0306941460b401d0b5114000400001045131b0002441d90346502c070180d02083c1c03035401260710410000070001242004041c1e1003543c142030401e22840b5041110240c000d000301003403507000704da0206420342480b80030046005001d070300450841c07450032030400e0202c03107a109028507806036003080c021000074280081e051034a40e40002c559901511440030903501c000004407881c05042c061f01a1001240c1c6000064008500c00d400000340c45141002c51029690b006026034460392040c030909010a515904251400381c040341e40719074032443c1e40303030680c0e81f0314031a2040e022000e030310000c6240e8801194003c5069600e0f0f41c89070507402d00250203802c0f451745000342c03000060700d05110044c000340050349014503e61004000d18100540c103410700d402c40301400c1c0300d070703000400b1080100054202880703094090800b5880038004880f40b510035540e030b88409880 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 411248579 1250 411247329 411247349
    0x1b030d091401030609020c0706020706020321090705090c090907090323030d0608070f1a0d02090109170c010807050306060406081f031b0605071a1801020c0a031413 72
    0x10581e40d68400da00810203807400e900110748807449468010f540310950300400740544180200840d0540c0000142c1d103840c1d4001c40d100c0b52161000c070403080c26142c00360245860340f141c90400701d840c2e0f6030728440d90b108142002500d40c88035075080800c5060b1001909032020311001800034008a0602c41d402901050f00310080b05403448641c01c2d8078610b1240d21a402c610384d01e000c4000c902604c01003810030440b100c50340215001c0d500d42c0c661500d0303081311701510ac91000d0304004011400ca495000b60a1495050501d011007655818800f21850544120007000e900124032003000c039a00140c00b6508801140340040c210f16082022508900c070354050b00c0d00348416440007401d03850050840741491016202407005007030303584c80d00c0c1240d00c1c620740028568601d6100d022a0540c402c0c0d0a071108681c10522015100285004895003d1400380107144100c41c4010802100c1d40e0900041c02c0e12020480280344400103814001c140ac6805045541881c03010010070041d111030225650640c0c0b01600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 411249829 1250 411248579 411248609
    0xc0809030705030106081006090c021e030d0603140d080402011d03160803130e040c150e0d0506090c0402030606030601032a090501032a03110c0f1b030d09 68
    0x80024039050190b80865455070902c1c070702044038600846c0d058404a50880c05101003602c500001c4151840c402c02c010040c0c0c0030558070030b03e01d84240455900041c6100599180200c45c513148400c1e11001c0d00b00b035440005240c130308120f021041003410200451407400c01000d0605500081005680003c103101d881101c450004080c0d82c03c0c00301103ca05081c085040720f1540d505000b03a2a82c0207404c0320b5021001c080000039203400c0c1c0c1d06241c1e01c0750740d100015030052400c0005101048000325000c1040004000400ca9036445074804102c1c1c25000b240201606c0c03030448580d0f031400440f15800b1b80174600510600015031103060580760041c0090031f0118a1125000740d41c40b0708045c2c00e62041000d40d03032000c054030094001d9580803d8541c2039030107102c04844050f140815042c2201442001d00c210541c045a4501c00d03413140603244141c103801c0385800b01c0051071501d44283c41e01c07c4c40702600202980c01c1c04003502c05401c00101400c6c1c01074803c410b410240649482103d02c00ca0303d149040f00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 411251079 1250 411249829 411249847
    0x3090b0903120c010902030715080403120f090303140a020f072010090e0601090803191e0e040b090907030b060f090a0c0e010306081e07030b090d17070c08 68
    0x8400081d019000180310758480211000c03080c084d00d05c1d01010780c0640142e090102e28004810b6030320043e0141074a0b440303241c2d151640c007103600c01188405442c100b642d50003000a0407446004070300d2030328000d55000c40c1d0b24131803008000500e180a041c100da4103204224900b45a02d800081d552100e8100210b0301d2452803501c038100c80030342c40c140303159807100030340540c50200d13600040d05105444158118070010382d121401591415990302828456600511991414035040074501414001524011049a905207005024029041000780208181e84501c6010b420035110352103846c901260511250f05102034184d80320b0796540005000c0c4090307040060102e8558000c2503404420143c4021140e2410500f40c80040c80129103003000552012a01c1c0781c55803003400b656042da00e0303c5002d031660404000c4030682400c0001da40d4203182c01089000408544865240e07441141070202504100c07428a1004010032108080d0f00b5200b00d00c1c0c024080244d40c8450300e02807a41d0300540b165940c030ec0304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 411252329 1250 411251079 411251083
    0x601020a1103030f1c0506010e010507080a09050a090204030b060a0308270d1a150609010309020d050a23010e0a0b06011704240e190312050c0702010e04020703090b0903 74
    0x2d0b82d504c000c0d0030f0009460142d1341440c81030440784800c4801d04212a8562100466808041d2000c140c001030003480b18101140c682401420b10070a2800c0c840c045550f0fa0b0045011019503500010100c0c1d40880e00b001400325010480b944a24125041110740d030640d507440c1d00b45e00800b15480c60305054403204800c907000c21440c140d180080284414040d02d01071614040c0b46c01014038940240c02c80001040010000c5543d03560094001445142008072810044004002a030811384e80990461001c0c1c0c0880c4c014094a0340c803502840700d41c0002c0d241c0e0108403401040d414420085685001c036050a094000f02d05460240d61141030000261950001202d4840070880103098001480b0300303001c1040a0810101040c40814140c01980d620340c0f102d1204649407a5003402e5944c00071800c2207400c01c5000c02c00a40544241448030b0302071200d20a2000b10746040b01c0e001208600002c0a03810741d82c003d2110f00134181c040310305518000059038014403c032080d00c02c24410490100c3e0100d410343e01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 411253579 1250 411252329 411252337
    0x1a0a05040e1014190312020118080d150b030a02090f03010e0f01060605180d03171305060609010602100506061b060a0b0603060303030f0702032703010c03050601020a110303 76
    0x5080e140d01c000b81003400c0c0b480c40401c041c0c825400100c03049a03a448a509021072580141402d841c100c0c040c02d442d5841d041d062501e101d10706001c5568852120070b01207003483d035124000b1700820100343c44030203021502c0b049a8900d58030545086c8410f1081124220000449501c154441e10150702c800044001c034845140089034260325500300990600311a80024260758142e00320002481010369031134040d45c84e44126140c00700742d1200000000b03168140b944c00210300740d1003450700c036011200e6004101d00c80002038600041001c0d41400d0082844020002c0a400c100c00703d42400365035150803806540c035040c48905054264481d000140c0580e542d4003542c410301c00540c5404400c4040d0302c0901d459013011941e90b408c6618100088002d400c110b02070300c2c0704d0080500154510744450a1400b00800c0041174442140310030041c840d40582018003100200012b1341d048018030424404040c01e641c0d003100d860041528050402401c3d07a800124428000d070012030078041032600c00040303400c41c42 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 411254829 1250 411253579 411253589
    0x6052b0627030507170a050406030902060f03010e010609350c0303040603020408010e0307080307180b27011716020a06060f1d07090e1302090c030603010e071a0a0504 73
    0x75640c00c180d41850381160003410454441d11178401c1035101c00c03174443c420340506c042c2100016030a01043c06000d0280d0b0100c26180d00080170b90381044d01e001e80c4006c40343e04c00d8101c0c03030400c081d8800402215401401d40406801c41e0321060a8808444442100c603415203d0b0340c40045003100d4a00410703001c18440c241400310040c040d03d507100e44801000e4040c0d442403268405661804880418004d804001e451031164015001840c42d01c400340300711002120031105800312582c19400195102c4c00f00d00404030b00000e03c03031080c07846900c540c0d146941070342082013505200c0c20301403c00b44e403060b603400668020307880d00e01445075141561080b403900055103001006289410f4012a005120352841c42c121aa0580e0601c15a5a01c02c4c0703548480c4405d5425101081e402c03001489400001c0240343d03400030194205c0200200550005184070000361003040b12200c4c0001480b40d107080038003c40714550181c00040c075a6518000b1125074080041440031100e01011801d903210034816400c49001b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 411256079 1250 411254829 411254891
    0x706020a031b14120301081209030318130207051501090e0a2a0e090d051207141606060e0a0207051203130b01060e010f03050f0a0e03190306052b06 65
    0x213088035045100039402801102118030400e6610580304503c5012503824101c046d020714100361031054403010400440d0310a6074446030383c08110f0f1885002d440600002c0f40118001d1090444280d030700100c041060704085040d500b0060ba40103003181c001541a0304907440780032414507081c4101094804400d400389075912200e02c106c005100003d100c0041c3c01003c00e03105840060320ba0004c203607074500c5542e03401c080100000000441c411700605600100ba0034010800e407404d0400040380d082030200d10411117a1654947d82405100b003069030a550100300908d00710b290101e2911910340d204500001034180b05c02c000300261590782c50204030048154040010921543c442d440907108208204019001840001620140c5442030107840e00070610101300c003405441e08603009020300012064180ea920081041429603a0b0350407841c202e00c003e03642c000609074185130411100004102000034176119940304000450318150180f41002c2d8085000943d101e81146000d84090301da0440700501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 411257329 1250 411256079 411256093
    0x9090c1908190b0109110d0504060e0f0c0307090b1201090507080c010315030803040516060918091a09071206020901120608121e0a030209030706020a031b14 69
    0x10342280340c0361815200c4001c26115404612101e040d0008034502c80a48000c60b582d00402034032500b41e001c0007000da0079400d25460220004d0900c000d4680c25503040b91065582d80303601e403500ea014409030344030400c0100036210402040000075502c0e10980203904115a03503210010669079207510306c0310b40c1281c03c0c00034040380105040ca40e03220300b500e01c1a500c1d64000d080001084d584603104084080384100941c0b1201c034190345a90800350001407040300e152055410750b5515409641521008040315558aa1010304140d00c0e05022450020318003446810030b20420300040001038200c8040c2401414110141e5403140202c3c6011400c1c0d0202c00600f1807513a801c03003442074035001011460f001f07880e041c21407007240d8426000c0302d4451007000c4c0e03907030444003001d0316501070740004000060314002d50600205218581d007203c1e601003844400400e40c0007400702c00505083c0409001800b0500191540100c5910040c045407580450540b8400c118070740c0000f048101c0ca443d520240c401c5049584d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 411258579 1250 411257329 411257359
    0x19050601060f030506060406051b07090606090806090705060c1203150a053102220e0c03010b0313060216030309150207051c0e090702011b0504050f09090c 68
    0x11028207004180c0041c4403403020000441c001e001e114010781024110b2841c00380f52510449040d04603006699a06009001c4960b0320581000280090700c078000c40019424a40f060142c403685465000f600160041820801102c03000b0a1000c100c900984403079680703003609003c060900b030389200407201600002c1f00307000140340b0510042840ca82c0654012440c2c3d9214410803804041100781d401104501007100403050500064100080d000c15201604103440308891134400c400181c46078107020000b40e010089080d61291054010780003040c40303880d550410901d4001d500c001403802c91940107001d921010406641d0480d1089a00c00d80f549001000901d07004019042c62501510a6203a1803941000c0c04500e02c01c81d6031060f40300c001030810041c0e17024201c01c461010305041c0b040c02000c2040341002c0c1c9516458174426101e9600028000c1103152001250b007050071211010804280710078001ca499030701404001f003004584040f4155a143d40207403a0149840485d0340000c0c4c0d03003000c00700d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 411259829 1250 411258579 411258583
    0x3030708090406050d05100f020c01060605120c09090f13060f0209040605030d0e010c1104050c2106060307080a113f010b030408041e08010b090c030106111905 70
    0x141c0400101c80510010f035880c1d007000481c0a2440c80940180c105440029060712554000007183c00700c114050305190180c000c2508642d405c0d0311140200d01d00050388020075003201a6960310040d440d01d1141898412400314501a01c000d2a0103a4441745401040091842d00540d02c4582d41c41a001d10003071203481140000b80d0040181c41c0d004a052a0380400c0a140200b003c155070581aa54101a50641c0700111811808141d095030026140420b50020740c992b409681c1c400d40c0440c41060313551080e9500b004c4404c03603c46840c143e0b52854000e1000607600d001c2100d4100e0854504540c554039000b01a90040100e02e80c0350080d0304001034281d410850b00301003500b0300000304200f110100c5034240c4504040a140902c600403807007000040c0302c0c0103405000385070401d000d20301c92820113880345421000614000c1101c102d9030501841000320800c24095a884440140d41c0b9030141e081a0384c099106010601912007808a054030b070400300d01d005c024a00304a40c0b204503920800f1210b0618036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 411261079 1250 411259829 411259837
    0xc080c01150314010e060a0b1302130e0a02040b07030e01170103050f07270c090b040b030a1109030a020402030a1517070e070f0804020a0504050a0e010627110903030708 74
    0x150300c503060f07040d601c04400043c420341400c010140050404c50741d4403a526002001d109035580d41c06584403203c038a55002c0c0c0d20103000c900030341c5607400c110a410300309240104c15000740b40043d15801004203014104200d016030700d945a05040030000894071070f0050f01d8007071801c4992605003100704000401c0c40000903c00720075186050a0f03d11460b01c4440043c0e02200d240c1d0f016581d00060400484e44808560080c071511960341b0389040c01e2912984080d040f580158041e820711031001c000d214003159548503890040c80c2041600385000003207408a9105c08445001900c5540d001c07001a00c8a9080d40006c40c00d0800c010030303a959071391a540c0b21003140302400140621440350704004100340f400300f622140200c00586510702e85d000c00890803500365000401c12032300130698a00004045d00ca41c012a0301400300204040780034000f6000c0d07182110f00300d600c40f07006001d079038810345408080c11010980750f90300001c001c07036454900e80f05e01c1403a2086820098041c0300000f429424004514050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 411262329 1250 411261079 411261083
    0xf03040c081b0907030b0a0b160b150f0d05060612072111040509300307021c0905011709010e03030702100e121801021e07290a0c080c011503 62
    0x326813a1100ca10442c01c89a07812016034020f041c012061003d007244038042c08100c02100516200000c840da1032000510007900e109002d00300350b017243c64a5250501d4622480d00c81640d0309aa190b0164955030b81d10b0701e0141200b40520184526141407820a001f0700010706101100414001e2420396800c1912181c02c1d4180c5500c8a0302440140b40c2c0340c14001e007406050303084020101804405d01421405040c021120942c800b02c1e002d0315444840440507520940d515005490100d806402a2407211052881b85003005041c4109010076a04840496030340c4449117810707502641c5d02c001050060004d0102c01200d480044104504143c0c0010000000150030506006406558482a5540b0b07840c1c010488050000c1c404620340c4442c0540131800800140b04070344142c20061101e50801c2c416028161140d0410f180600100c401d0441c40c2c0900700040110802c08204c440c180c0646001c0c0c591a02c0410007503880010601540c28203981c6035460040080150f0248030351130382112090741c842 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 411263579 1250 411262329 411262339
    0x1109130212010203040b0609191a1306060210020c010e191506060e06071b081b06031303030902060d06080d0e0102010b0d06051305030309030307140f0f03040c081b 72
    0x407030207601e418003e407405651300c580e5506a50325102c040001100b402400c3c10b40d4096410041d00d90b150315030064416800b56402d42a07400c000003410700c18100c82d19081c0c140850304081c400c000580c0c0c0000c440d102d0461207100140c0742c0d96040390140c01b40c584070300f01300303060301c6003094980c0a2030b445100850b01c0780c03250040070480d019440d402025038269214000c0810340010168015060560080c4100c52190900100142c03038040c0c200c440d003005800c800b800f1741c020002c5409800d00071080001a1404543c1c1a0443c903202101001c0c1091110000b0105030300d4240140c115111030f0269442012011700c248119901c0d940042c1e41d85404100e09000a606460300c154554018413aa400005014040010400d051349a1501500c800703000044800c000075001e5021407000c0c0083c2d40214103070b40145589041600c030042111042e841c41640c85c101c20800d01007118409012602c0070b80b040e08144d512581c4038100100c42d10540d074011a01170098002c3d10311510000c001d5040301c0401110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 411264829 1250 411263579 411263599
    0x6020f090307120b01061808010c020a060e150a09110a0612050a0623031002070807020a0503070f030b091204090b090a020c0703020f121e0715140711091302 69
    0x508440c00703040e420050004803800c0c005001b56445020014480e070004600301c08200c1da0359420364211f4401401c1d07200180c10030003041040010b140070342c0e007401040a00403d5500380840c032608040304050000c0c080380d6640c09080c01000000c8407141d94115000344621310403691030801a0a5600c6030071001c01107440c10001400300d007400d1003100280c403070000141c0342404150860800104540c0d0407641d040c07080510140e81c0c003060b40000c1c070034648602c4041d61695540e1051104000f0b5903000188690010704080c49400c1c00301d0000811203402c18545916915414104da00b002441c1c40808a400c00004010034481d00b01c0e0000d07001070b001522080754a0756440714050481c09a2086412140c03c140230400261070f20300805050042e0042c5100f024250114036035107400403140c4050782c0000185c84800c1c40d20b0061040300002d0141c408040100c07800100024200014038041980990340840d01d4028041541d5902d000084007608241184c2010031580c10f2076488650100d12815028dd = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 411266079 1250 411264829 411264839
    0x30409050a271b1a0702010909050c0c010b090c03070f0309050d09170f030f0d1e0903020f03070c030b0c0d2a05190804170a030c110c011d0a0306020f090307 69
    0x1580c1e03008603138000c07610580e1038600600101456000142c1681003120400c80451121841c0c8640e82c01007400079034080d80e800080e04030b40e080d03580d04481c0910803594902040380c0800c0300001c80e988180e19250034a10155506025001080d4082c0060400c0c858407007a510820f80005448040d50301d07006a81d08805801c652103507441410135841c9080c0d4105004107a07034440c21001800d041e01602802007110741c11001c0e244204801c0000c0c03a080d0a850321003a00516406000d07514107030010070055440e00070b483d0ac034107000d540b02d0b10005055102a00001c1c2000c400c500070394000f44900d150130301c102c4c2d16500300200c3c00b80c105800c0d042c0d800d01c032100d6048064000c40c1110307035109041e6000020341503480c90568074410014000d0392000c1d078000c221410400d0001c002e182c041003c0d01c1c001850610540014150740702840c504140f40c0c8045004205680c0004040140001010f0500d4510740c621b00030562111240c1c0c0000c0c0000d001042c04200c14100314080c011000040e008c03103004550b01c0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 411267329 1250 411266079 411266123
    0x20d021c090512031905160908070b040302130f0e0c0a06050901090e0c16050a0b0c0903100b03010b0a0306090212010c0503070c030203040f0e07030f050108030409050a27 75
    0x51031009042e6400350001225001e04a405990721000c01c91030001e052000001141c1500e0007240c148002e60304060300d00c4d011a0704602c1d103002a2103544001c0c00c28a05000c010062482680000380c230561803805403078040c14954009a48055200105210f0070100407142c0360b441082c03550681c825054044041400792003030065580c0c1c424140e40e20a800e514043c1c594030320100c09017036841c503131004000c0b07105a690640291268948104003c0100ca0050304242c645420090101c0b040802c0410158a1319500003907030009a40003c08005a84910200005c1c01400e14001e03403500001c480c40000300f031007860780c00469030900a45100e000600c0300c50001e400c0304d03548403590020504c1880480c8c100c500c0782c1c0c40c00c03050604c0780c0100c0e49005d45490350008080c29961111410426200c02c10128540c54000c903007491305034100c20302555041c20000fa4582c05a4082c001c04559030301d002862840e61500010780041c5440c13008004c450f040302d47c2c9144800d04400c1551020346800f42142d417501c030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 411268579 1250 411267329 411267341
    0x1505061c0b06040b0607050d08060a031203020a0e130b121507260a021c062d0e040305030105011707021906020c0609010f111305010809030409020d021c 67
    0x1622010412040300d070303a91000e98510240107039800c1a503400d09104d07151500c1c4014444035008200401415013420001401550010211400303081031a2040000a0f132070040194000401d06015072140144d81044031801420300c400d42e401040054056003030707840d0750f10210000c0c0c02903031805210042040916641c28114085013650003d250000701d8451050485222820003043d441e0080a01441e403401c52207070945d4440000c43d400508a01150340e010950814803200f040144006860407021050f80c0405440380c1c0207105200540b000107400301e602d5000503024036846540c103418039042c01443d9030400d000715404a24040c2641d6811903001425911881440e402003280e111401510303032040840c948200c80700c41c0c01b40040b00711080284091442068500000070300390241a40d1036082d506a02c030f240303d1403c0d08000021581e415540340f04261142800c080140ba1030340c60b200ca00e90306c9103a100301a510700c0816140780c00d6929400409004041d007030041e51354610a203808040b0740c1c0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 411269829 1250 411268579 411268609
    0x50d0606031b05042916030915082707030623060603010b0f07020409350c0c0d0f02030d12110307050a08062803050105011e0b0d18150506 61
    0x4000a00851034032005c1c802c1002c0c070052600301410400d440c1c43c500840c1380841012000700300f20420900840f20301000710071004030b041c540038405040c031000f1f0304c907a203401114002c405460440400002780f0300700f10b0f510081d0f510020030004a08007005d081c000100003040100104024070105019180100590381070724021109186025070946c00128a50710011007260003d455909040120700c5241001c05080d4004000c400014540d0b042d0f42c014868400c4103112550007400000c17116400090b101c4602c1400381e0300e6244000c02c03800c000c403140021201c0254144648114400481c0e80404101a5280c03090414041b6060900d0000c02c6800102d03003102c00030b04140881d00105114088140c2c0252015107220103407070480d81c402050f618010290589880c0190040007044401d22905004040e0300e2891100031140481e00e031141c4001c1d1107140c54000c0d011501100081155111242d20034504800040394001840c054100c146551520b4005501e0400000c0302e03402d00c40305d001c15401c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 411271079 1250 411269829 411269849
    0x5010605062701090906030623090c0f0a0b0304030f0306050a03080d0f0906061412010b15031b0a0e01020c0904050607050c0c091e07020c01050702060a050d0606031b0504 75
    0x3010440d92032407078180602c42c541c1040b08001c1d0000e4450322900c50300c80135502602d00480d800060400010b003421080403110340040340344c2c0030808541008600f001a000301101c0005070303440c00c440003a000034120f41282081010000c140700815811080107030400490707407001d20a0650310010000018810300c006401d8000030051200840560341c400c01c2032040a581c00200030859407500d030211005604903e00f03074044502d02202a140c46806140c181d60310b40000d00003008407001241540030701d02011424107078007101050f020011002d6500001c84000d051546a528580c0001c240c02100b15145015000780d0202034a10b04061200500c641e400000400d1030741c98245040380c0c29404801580c45a0061514580d500d030b648001e203a0140b001c9110a040400509001d00d54006000d0a000199484000c6c41c0d8240c0e40c2007020f580d1096011108181c8034002c0080035502c92181c1c0c2150301d15a80790983c0420200d0705540141b11000f80d58581d81c1c1180580001521a03102e6806030880321 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 411272329 1250 411271079 411271117
    0x903031b1b01141b07061d220902030f0f0a0b01080102030f0114030c040608010506090f1905040f060c0c0c0b0a05041412070b030906070c150504140703050105040501060506 76
    0x3c0c2c2034001000448110100d240300c4041c02500340c0d092600c1c40c1c020200040c0c8403511240070240760302192098400c1151900514000f040844c900700b408103090980d540d89484100d425560288050390502c6060000e64038400c003e468565140c840e00314040702e0008194001041014051003620303c43ea148a0000702c46900b0080740280070900b641045500d8480c4a6030070031680c0b11801010020708000e400802d40303003400360802a400d50014100307400301e10100f08001d0b802c1a1814441d52107450701d080003c5540704d504101480400014020744040e042000ca541410791081d40c1c0b0025600506159081c2610380c90b07a0340305840740074801000a4010700c0241b02444001c140e80650007002051428044554180070742032040e19402071141400100802011400902a25520100518001080e14120b03502c418420140c03c5503010340d644d50b0000103003004510410801130100c608101c5e030a640d034901c1c100e4040d20301100e040b2035550030710b40001000d06040d420f0b2034100750594200001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 411273579 1250 411272329 411272357
    0x1150c02062a0f07090f0209060a0e0a030b09030315030601230a0f0b0a0207060905060403030c240902010306150207050127030c06021902240903031b1b01 68
    0x11000803911198110820840e02c182e20b10310800c581c0031030704000800751141a150901d07800031501c40342201a00240100a0081c6568400c001c40307980c41042d080c01c0d2a2241c5101c041103404901d80c2009060402e1802400110200080510300c524010f00e03007200048009400d15440b0301c000c0c03058105242c001e840c181d1032080e41484100d0740810180c011078103180e80d56040900110582c1c07203215030b03000000349050103940c148282c00241102d814205c03000c1d403400c008031340c1c103215500c006020050002c004c00c04101890300c2d0040c0398598083e40d100c11b5018880102d0043c444080120f0119281440014034813031070b41040380c404030170394000d41105440d0400640c3c60700550030182903243d44000ca044000b1041000c100044c50084040210b118101200a441e155901d6540c0c08c00407140c1004500594034542d100182801c0718105026003804031420400c3c80c02a40502a454003010a1004007420800000d24420400c038040340c8698440054042013803401070665030000d072100000000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 411274829 1250 411273579 411273607
    0xc0905090a0b03100b04020c10060f060f0509090901090215220b030115110a030210060902090f100302070803150f0108160305040c05100206010305060615120709030f06020301150c0206 81
    0x105d400c1e40504090700d8510307007000791030900042502140280e5070300c44052151401224299024020a0424145248401310003a009008002d08984141c03140000515016401c0d04a0100b20354084c10100301e1050340d007440c00c69600718640149403101d0384d0041644030742090110b8030803200301c0b0042500d140d00b4092441414800a400074042c44640504201e02e00701c10003540c401a4025405011018440884d10066610139402020007500600c107084941e6144503c0c0045080100c2d0344585015411200b03074080d010b8580007512001010041200000307000240c240070034021518074215a04003001983e030600203a4480c1c0c03070000c4448084030558020340c4401c0d085030080b02a1143c1c6950350700001d4000c0c600242c1c440040e0070031700040081107402c000320b41d048903007101c80e12017444072210803c50a0082c03105d0482c0f0040038101203020103014001c1c080245800220030001c03204641030101c0070390b00070320810003140c40c07404640044a109100da040600c1e8010602032030003802c1c1c02d40b02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 411276079 1250 411274829 411274841
    0x302010c080f040f15201f15090e0705090f01060518150a03060603061a070c0f030503040305060601090e0609100e13030e0a0b070b1003060c0905090a0b0310 69
    0xb000c001c00020070951803028224009003640201c09403000d006000040c5103459520342d8802240040d9101d1001c0200032071365000f100000e54000d1402c00b4912280c1000d0076178507800355003400c0d0440d40403540200d01d40108908928500440714210355400c02c0c000c1900e01103c4190304908900014404144140018a6040102000340d1040d20303880780002d42c165501c0c010344058050014801014039094000e0310000c01843c10b0822040b49441d08403606520140c820360000780001682400f000040700b16000034046182c420000c041e101d18205a4039401030000340c45610035035001078000c0d0311600480090b15852101c3e00c0d4a61910400d0101512f000340000040506907100030070058103c007007051060440b00c5d50381a550b00282070280c40407000040d01070040440c07140c1032100042e9001280e04941e440b203405c221503a01c034032008408580c5030b0001000103082403401c10b11242d114050005464080b180c030762498981e0220744048a181d500c405400d0b400c10040c1d403040d00c4a940c030032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 411277329 1250 411276079 411276097
    0x415050d1d0703030212041d191107030e0d08030705070303020d0e06070908030c071823010f0603060b220b0a020a060507020309212409060906130623070806030c0103060302010c08 79
    0x10350180d2011060f00004e62b4440261441c04a402094006c181a4040403144000034155107000690b04a6100c06d500c510000f007142080c0030700012000100b5120f6411200805950b107010801c4081032400b141c2c984500344d50b61b80003e045844081030341d40001c411611800c00220043c8005450181d0004400840400c140000b50b030320320100c0d0300058404184001241c1219501020f5810203540c41120012604a130040610f01401400303100c0e40c0030115800451079102d104840010344c1449020400301d500302000c80d80380482e80f00c00c0d5640010b0790114192041c0c409000690704d022080380d49008008402e540001c0b03000608401d105a1244081a020150143e030310742050180da1041c0b100280612090400548042080d01c072800c0c0060703078008901c079024003d03509288014403070b80700244202400c0980e64000c0501c022217010768545030402c001071142d000d85030800001e080800d003220581d00a01030a0404c40d0742d90700c01e102d0a81aa81c0c140c5400c43c1d100f0705501d0726001e58102e0500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 411278579 1250 411277329 411277351
    0x1504120507050d0c0c060306060909050406061a030a0506011b0b090c06040b0903070602060c12102303062d130203030f040305120415050d1d0703030212041d 69
    0xc00c2002c180305008102c050f039040d4a510050310f580d480c11110790340c025800304040614201d0144030066008182c2170840e0704101000c905500c40e400d006000b0318081c1c3c007280b001d4400d074402249000c2c0f84400340d40b040c0c81d4564100a40d985000040d240700c400d00003070300b070300c0700030a100100020044100d1640140d4141c0840f000300301c102000c9501684075400c0034084100205034081107140800410000c0d1807280301a000600701340641c0041406810b00640c0359401440000d000c20185414000c002c01c06200b8074424007103c083c0d68000c10404006041c042c0c01150000f4840520b800c1d400300521090007000c403103016185503450480c600160841d91046411100c1002603076040018000104901164982d102c1c43c6107000d61424006032030b40210742600b07110410055081c40e21400f500e00440c00d14541d15161400e2030402050041d000411300c0401d81041086c00c00c00040c1c02c030650388a6021a00807404104881005005a106d402c1c030512400c4045001500c0d2801016005072079000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 411279829 1250 411278579 411278587
    0x402070501060e0c0d0f1503081e03041416030519020f060d0203101a19020109020a0b190819090311060a290a030308060f0406030503040503010c0215041205 69
    0x3d400f02c1403900668039420380c8540803a280c8940b140e180315220070002107034010090301000404030b0024100611002d001d001012404052440c0400c040b180401b0a075034200ea5070b4034142c6800044800c1500354829507104803000144460700240c0d10300240ea40040003040d6945240302d100e0910a48010700b01d030410002a0520300035298040a07125003c0080b00150701c038603150312200b5603000d00d5800180b410f000562007507030320140b036011a40414032181d4180c0500d03491260076405001d14680c0290840c152820000c3d14130504005010042d64050304110141c00b000012251040143d90b8620440703c004440d5603860541d07403042d03650502c2410121481741ba411140e43c10588212040f5050365104d509480c0303060701c3c2001303e01881601c4440031800192540124120048601005080c001c0d1400440c4032640d600c8031103180110f000344140322440d281e162040e02c0303400c9442402e0096007459044c440250011543c034010703003114002c150007588c99448090325603070710016030b0341400403c02c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 411281079 1250 411279829 411279839
    0x30c04110d020414040c08010608040602130e0a090312060b04050f030a12090e010501080702060a1508030703030e010b01050c12090d150c0807091a1e0408060703050606090f040207050106 82
    0xb0000d00000c08103e001c148043d040030080c8001e4401451464041001c0100103000e041c0d0071811007500103411640058481110040d04240200d5a801c503c1038100c0c40303020001e40481a03080090528443e65840e0810203100034400c040ea0700e2809048000c0070180003d101600744080d10510f00d81c0001e0807038810840d075403141c00110904803050000034248e0441072103040700210b0410b006240a207000f001c28646480001e490318000303484605155201e118000d028205580000060803411003607030741c3c2d0442d03440c024004100d03400304046954201001020b10750f01820035038103080b40300c0010b8910f07c15101310703d1a031680105680341d400418464442d020622a403540d4458620601d80040c0f1410020b40241000d10024018070801000740014802100000621400540000c4015881c0c0c801c0c00d807942400101d41d40148068000810001050400041c03820301403141a00c04200a13140e150500a00d84211001d451700044480c211a0050410b41d004181441c001c2000248042c0c5032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 411282329 1250 411281079 411281081
    0x30b0408040e090a0b040206090a0b0a020d0801080a030c02061c0203010306050108060604090507060f14180909030f07230a150b012604031103040e0403030c0c02030c04110d 76
    0x25902994508008502840040220169660000e168100130149000d150b0380d00034000c800280000d02071040468a4030084d1104102c0c007019200c00034000740c8421582c98001d6403a84d40000680c00101210000a00030b00007103181d0303049541556030140d403440d09809002043e8447c0180280070074a5035070816081c0900e1018601075889040040707115450f220b0000d00e0100042d116030b00c5180303402d24000c0040d1000130180119002d504080c400100c04d500140c80c201100801d82001420000390fa031340800013900009010901141c107243d203522418810350381d9000b52204405191410001c80c404201c00d8545000c5ea20641d50021400c2184100030b00d040c1900380c08101d036000d1078a007980448500e14003810401e90703c20300e840402010a6503074030300c0c0c0b8142d4905010800c01e418010a090510840d00d1000703a20403001203d640f143c1d5061400310030b9a044a054000910b0003001d050194800c200080340c5540080c0245085c0c2007040400000b007600b01c140b402c015108020051003080070b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 411283579 1250 411282329 411282331
    0x1011120702010902100e0901030204051003060906020a112109060405030a0b090d3011030405071811220f06030605131112060316081c021606110304030b 67
    0x30036800800c4140e0148180300c0e609090b90b040c030046c01980071910546403540841c050442c0c0d0100c1340454141c171401c100070311049a03904090202412314940e101801340c4c6800611212242e642c0c2c6107501c0c00d1011125445a24024282c074403042c0d110304040d150b103152000b078214610000c003264542030780c800010b4a40320070140304a07200e20383d01c010451000c106120f120080c1041d42491103803603001000c600507403100101040489a05203480c1b0403110038903400301d20340710040084603540e41402c1c1019503440c0b000b40325008490b4070340c422640903640c06000e0003220750051069030b42050341001010f088e6119904000884601411001800880b800d0702c110040100c0d840c0026468208028060800c20003100c1251042c02d00c082c000300304520b02d00b118240540b0388100300a0b9204d500c0042c3c240318003072400d80d601c410036000c00310b00c04401048032203404000512061107100184000c2c5c0c1c50300c00810209030180f440c0a403c002160280b1400f0b41c034204400144e91400d600ea5a50009282c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 411284829 1250 411283579 411283591
    0x3090e090105041112120d0908070c08060604020708071103100632030a02010c060b0301020f22150f11030c01021e030112020f030f1c020c12101112 65
    0x244650070301081c48155503181000440589134045403001001480d80d03903841c55002e1000c581d000040c061032840c8198401c00c0c8542d4403040550f6140c02b2400c140302208100d01407040030b402803c0200700300b840e081c0300712040291301c9100e041c100021070b203170b203610340c9040d02c0d015400d40a1010140c59805241c0304160240032010a40c904102c2c0001c5c40340b00c481420341c00203030310103480007200c526540c00058141c0c2c6143c3c2441d2000c085d4940c1e10f000005400d03a00301240c0c156002040c6100c80044200140007401200d0b1881045003a800e0003a048031040c03407103258101040340044000c840d00c1484030f0609024142801d018100f031000510b403840d40302c00948507050b540861194148101114292000c0036403240140c110b50500d41200c10441c1c1d4004004c1c0306601283c80810240c900b0f115161820110400f660782160b08a00709400310b1184030002d070010f0180f00b5095000b0f10307045056240301c84005005080071411444030500503d140c2000e41c0c10200103000b980c481c040c0604000741b2540c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 411286079 1250 411284829 411284831
    0xc050c0f0d181d06030a060204060804030e0d0b060f010c0507030f120c11040c110303071d06040e0a05040204021204050f0616051c06050307240e01140703090e0901 72
    0x1941004200349401c000c03000325241146003c00c83c08501c45004284070191a14070002502c4140009113010000c100080442d4008a00000d045420110f0380e4880c034000e03164141414032100c10460004400c0c1001404481c1000214003141003c0030000041c1c40c044c10032150f2000d5980b1402d10342840c0e030744116911902c01516604000f0b02c1c110001240c101401c20091000c8160b580003d584100540c041c0034654400700c0702c503041d109401855219038060183e90b0b480c01d05940040c1210103040610155040c03141e1070762040d040410441e4112450708080710b05580f503201c0c5441c09000e001e0004d9902580a010f500a12120041058000e500c51301c010b11800e42c00b1500a400e1843c020302c561070201c1c2c903100c0c2c001c0e01a0403004441d00d5080601c035000a100c98059000010400f68020365094441c020003c02e5141ca01c0307507031000d00c00344a641c9044424150034106c1e03840010f43d103081e00081000c0b0021511a0312032700a8803203584a81010205103890301d0104090010407541c004284e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 411287329 1250 411286079 411286093
    0x40308071203020f04140316060e0f19090203040f02150414040501050d020609040615030f060b030103020a17190602121509010b07060e070b0403030f020a11040c050c0f 74
    0x1108482001c0c05004040c02c1c250b04201d6681d2150209014611450801e400030b1041d8100031340d401d015204486503000e00184200751150001804000b0000c803807800b030740076040c21441501e0100c210f43c0e04041410001000303a404e205e0700c4006500090421a4019549d100c2c6a00594880442543c46c6000000040d1124a0100003841c0781e580b04202074019882c01d00103122545038548bc031090240c060302c503160358054443c0400c4c001c1c40b40382c3c4845100d41c0000340704094240e064204030700f60305012009101e00c94540700c14007041d00c401c0c400298000e0180500b040343d2082c11060028200c0100d0075621081c9011030002081500440c00329041c2c0e90009462100680094a0a030000010a519041c0402c0040803407040c107011302450340c400d000031660030300f08801a00001042d1288200782d401d440d03581c10640c4481c0c2c100303000480100303490f03504071440d2a01c0016402030454204a17600300f000102c0091000074000400c0e0481002010041e0720340440c1c0410a94034000041c200420708 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 411288579 1250 411287329 411287333
    0x16140c0303091005011212110d020c19151809060608040c081504110a0801060b040524070201031e0213180209031005071704080705100203011d060a0b04030807 70
    0x14000540d98107500f5a1600005100803140084486010f1380e010b4402c41c80b00303000c80740640310090043c51110171440703000c450085007039000c2205c4c0d5000c0300940d051101c0c4240c6208580b2030b46001e00401c1e15051102e02c85804003846034010701c1038940c0001e0103c2c0d01c2c68866103403070180c070140c1e000200800e1b080402c1c80104074640d9001001061080d000c0c096a88004d00d00ca40042c0f009040a001e101c042c44011500b551101e001e03400400014008200195480b006a42540c1041c41090701c104074050445c1c0506807081c040c55031b145400445940382545030b0b070055001f48408001403880903592810740c0c0b501c00c440e00c000c01c041c98440c5502229603241c88070610781e80d489000510441401403241403030a407000680daa0300c1030008103001c075850f500c402040350001000101c00ca00100e0040a11081c00000002048050f0140050f1030a04280c0d1840000b41d01c028402c10f425010059000c001701c8141d140c0c03090300220020031036203105565485090043e0826041a140c202d0006041e0301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 411289829 1250 411288579 411288583
    0x6050417040801020405150703050702010c030909090f060f020702010f051e040e150a08100f200309061b040302060a0201140a0204091505210a24140402030616140c030309 75
    0x2188447d4031100e20f1030408070342e40c001e10034040c219000341404001804001018000c01c1c0c400047c0488a1040102d81c5036410030050480c075000b4140c40c054600806441d420344140201c83c460754060311408152400842c0c115550ba010804098600810070f90f4494a80e0090340207100078404003062000c54180a10720080200b40d2520051003080007500030850007034080b03140e0310010303034140000900d58000105c0d180980300d000c0d644001030746c6000264014611800c041e43c06000010b003102d0710b55507020380400100a12070203010b00450184000c00040c85c01d5001451140080d100100b1144818600c00c0a080c2c01074414040042e00400d041c00404280c0c45000184105103005500c0140f0302070210301001c42400f0401fa014180404461a150041101c800c0050744000c444800342038411041406004038021407030401c0c2400103d001020104952a015540040c0170386820388030300b031028045e076454009030024460003030029400320300440042d01d4119150f04c0511707074030303d01103103424 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 411291079 1250 411289829 411289849
    0x30224061201061401050f0c0a0507030b01152a0f050f2803030e0f06040803010510020c0102120318030417060f01081002030c0904020c070303111906050417040801020405 75
    0x8071103030314140042010760a00c0750b20b81d007035071310a003002c903a160a4840500d2071071280d005208420310491f4401810880000790443c01c690055250b0700481e600c41c50304003844040c035460000010504e000e4400740b2100071140c4440e0192207502c141805030380344d403061184081800242e40790741101e900300030103030801c0c00b02002091121051524101c1035034451601c0415640d805020950340b844e0744080d035802041545d04200054080300c1d0707580703840c0c600b1700c3e06617000340901400313012401445000c1c540002100c031422401600900442d0003403103603102d5103402c010b000200703d0f00800f040782408001030008001505c010b07180300c180d003980c180c403161030244040c0000c0d0782c110310000100308807013001c6a0082c1c0301903101d03000740c0d07281c40341c1001c90407030300a000309030383d00a20000b1401d80700240011960101d030310a80b5111402003c48229646075603100c211a81e008200e43c1ca4200001c001e03510071a40300b48541100790458445100c0c0c2100e0742c101da0041d951580d80001c2c01c0c04185801d9a00b6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 411292329 1250 411291079 411291109
    0x138041d0c011407020307150c0c0b030702010f022d041214010b090405120c031306020f06010e1e100b03130308010e040206040612090512042108040e0403022406 71
    0x581d190004c81e601084d07642d4601e00c0f80e42805030003a49214100351180301c1407a40d41782c02c1100110400d0700c90302444000e41c02520400099803030f010000300003c047e402518007400580000782c06000652609607061210004071101480c801c22022031024004581d104042d8050380980c001d03da4400516800c40d41e101017a140b00710b03a03140402c400104005500204140100310307403a16a010306103554035500440c0a5031121881e0b20201058a5070b0001e00800e0a113006011100e4603641d61100c1c0b1000700e004c0d80c480307081700e5041e4481002940801c040582240c03010940b03044007580ea46400c3c41503003041d0741e10300704001d45a006d0000e042c0e0002e441809800040100c043c6420300c0c1e40040c8040c4540d2241005111100403030500e000d074142d0061150030381100540c0c4043c81c00824003034140d4031a0180c115082e90703d080407886010344031520710300242d002c000f4030f01e043d00b0304242e80700c1c0304401001141144102800629128420714100d003202807424520507041c1030000030028680c0034aa5a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 411293579 1250 411292329 411292367
    0xe09010503071a0f0408010c0c0b16020c01180906031416051c050c09040b0a1109030717120d0504021c1208060303160b0105030138041d0c01 62
    0x10030302c42d00c841c0c0d00340005018a00e00e5456607900030411050501c5c0103541c403624180d403900380c00305001c80d001100b1040151040d40c00644507a0b61442e0f04840300500c68103640141d1101408420b203502411101c1c505180341000c800d800740e503a021031020b5a085030401c40d0018100c1c0401918010200810f1202d61003801110750810305000100b514100014540c22007282c802020205201c0e0070f226094072140003401902d0329180a0800c01201d50080d1140844c507898222069800720720340b0250384030104000e000d4030401d0314040100c001d82d8600d18042200b80102003400c04480b12900c02010100300038400803580d445c00d4010482c80c1900307000c3e802084015655103a001841058061607004002e091030826a120800030a1a41c0141c9a00c510074a4070402050103004000c2280c1d070407100704500a0288149551404001181800540000060711240300b403546103c0c3c0300501500e000900002030503100715000b00c50300e201c0c10b607010031181c022182161841d40e20018407100c03420b400318 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 411294829 1250 411293579 411293593
    0x9150503030f03190609021801020601050312120403050f0d090c0603020406211805160506071203020d020d06060804050106140d08030405100903200a03091203031b0e09010503 77
    0x55101c2e203500c001001c1103c140d141e07100314044c5811550100000d080007500854035540004200c00c8000004c190f000d02500c2580000117080c600062022403400012000c241402211400031a40340d1016004409011080c003118040503810005000101100c54001c03451a589040c48941e60071070750807840030540100300c14000a43c02041c08403180c00c0031042482180d12205c0c4410052446002200d02c070052410503009201c0c000501c05442c0403d031001d02070715a5920200043d51003890030040031500f0003203e1901950196014040c158cc880a016207132125034002d00d812540e0640100021980400074402070290910a88001d030400c421044004403040d0006100111891001000c950001000508015041c031402d0a0700c4440c4105005007100c0d4500070b0300c00f4030810a0701c49802000d100c031954400c0001184800c440d055240d07000c1e014180410400c40d020344034010703030500d500c498121038086228020f80450010540e503038661240c07076504205402d001a07101600c260301111f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 411296079 1250 411294829 411294847
    0xd0521070c11030f010f020c060a0203070e060c1c0302190804021e04021c0902011707090e07020a020a03050304060207060e0616020d05010504060209010e03150103150e06010915050303 81
    0x241090003507680100da69840003011000081c5010110a41d5503003a5003406460468002e4036000341c034100f5503441c1956501c0c0e80389030100c0100d010860b0783d000020844490903100c0e04010f4000c01c3c1a10354017013520202000a0703103e0000c48206450000020b0340010982404841c01d07000980c058414500101c190416800060b446500405c3c405d405640c0c1500b680000c0d501c9034115040c40441907264117030030300c4000e41e0400418010a060b4081070000302e6003880d009820450502c200a10303100c040c00303a41002d001503013040300140824103500c6007007035410140e515010741c2001903220740d00541e5990b061420007400e01c0550b51181c41884240210140c5c1582d03550140caa41d07241c0c0a202e51440c190900015041842c200c03400f0b4004d52801e0240418440030384c0042000080a032034040b0402c074040c00f41540c600400b80d102c001041a000103000150030014854401c0a448101242e0700c0030805001d1308003042a132060b41c1c40d542ea404400c19503114480040000c00c0220003440c1400054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 411297329 1250 411296079 411296087
    0x806010c0803090309090405161a2205030102132402060c03090a120804060b09150d05011b0206010f060c0506150415060e0a0e011202010c020a080d052107 68
    0x40ca000401001000c0700240701c10804009842c241c405c0100400168185402c0090b11201517946400c4a440820700c0440c030507212040499901b030341c140d909403624250454a41c4034604c5003111107600c80c0b44040015566500740007030042c044000e640fa809807454500300303101d4204855004e10f4201401510480340b69004654264000c070f00f0501c41c1e540340c0da2480f04a0078912601d01c020302038254a00000e411a81c0452041c0c410b6100f02c42c01c1010700030f05e50422024100c00c07aa00d19011100c003c8420300d41c1401008400e203280b103800081860581040c603080500c40c81e851110040c1c0c0316100400c11440030003c894010640fa00701050300c01120f8403040d480391001043e003d0601100b50444625448503840440000f0a0031000e81601703440c0d060080032800c40301d0f00548030b0a180340c400b060b40d6841c0c0081c08d0407210059503011800c811a8015039000b049928266481500102c0000d8495405c2c0704030009656141ea900e41c1c1d07051130703842e01c540200031183c0c807000c1340e031811042005041d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 411298579 1250 411297329 411297347
    0x71e20090610120b0303120103060509070321090317120105090c04030b07020c0a0902190207151409100201090201020d020f1203042108010807140f041e020408060412080601 76
    0x81480c0000111680308909006414000070a45d014400054140180d00000b48102d0580f4070425080c004d40d103400c0a8595903883c14003001d0540042e14800202c842d160021032030520060b07041c402c0d822030341c035150607000c26905410030b10452740005101c1e4980d0302c1442414090b040840303504041b4148040148240d001e6400020005a10000890030305402000040b10600300208101c03145034858500302d000c0d401405e0300d0840d24051040d061205030010070345409072002c1035215280e0521070482150100752190003042c00380740800c020310752a00c032444203903102c03032142e00041101000780c80028030f04004081c0d100c04641049a00d10841000801e00c403d0b03d410098441c0c0d26a20703141001c2c0c943c0004500c01000c00c00360018203000f080d800c41780c41c0b4102d03030b008001d951015507101980e11910380038505c4a0f40c0803d5000c1048020319051703100f4074100705407403066114044a80d081c501241c0c050b400580301913000713000300420028440d010140b5100585008003290800c44006482d08030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 411299829 1250 411298579 411298609
    0xe04060e060613090908040e0f070c03050a050903070906151b032f060f0618160908101a060405180405100c0915020102030108030a05071e200906 64
    0xb001440c4031050200b118032074050070f40d1500800021489140100050380700780b15152411540e403002070070312001c012007140705000680701c80308100e0701c607903048440382e000681c2107040c450280401d50040e24200b0480000e0805800005002070074490100080c10711b91020302c080000d04041c24001c51010140e02c05801e61601304261004e55240d01d0020501400e10450407500d08404481414100081c049002d01c425041244044e123034082400180c0055000700745420440b0004108c00740c096406002620440303180403908551100c0041d401e2840484070305072166180d00003002944015442001c0c1e50104654940c9030074078210114881840140141a06038103030700019003402400d0054441d9a01c50582c10007070300b41d0105001d00f140096000325030001c4c864450342c50405005100701c1c4d050750400c800960511409500c11151988100401c40d840e501c400e00f00c03250290118001c041d49841400608800c56a00d20188002e11907201110300c20a042c2c4140200d546030810001001c3d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 411301079 1250 411299829 411299839
    0x3060c030b06031320100804050a060c090602060c1303080a0306260f0a0521071203050601030c0f08070e0f060304060903020d0c030519110703030306060e04060e06 72
    0x25809001a00101000c911881d00b1100010030400300555030300407138090500c04c00e0703003d4480b203044180c11201007411001c590411a4030341c08549441c010520540c0c0b19204104460314240a5035482c004d84500c003456201281d9880000e101960701801000e91001c0240526400c0c080784182d00301d84075a5500c4060601e5a00141d540003107882034014102900f441f4040c00800040c2c4140c9071540d121005007010b0034041c858580f81741100101c0c408503090341040003885107450a42010318031144040503c80258010400600019445000c0c814075034800e07140002d5500e800d400140584070020140020041c0b60f10148040d540c1144000782c20810a190100c0014244000706489044800c1d01c0350b4429000f0040108200c0d064104a0b080b0748640c1c00e507a004904141e007500e98180002006010910074006010711425000080c1d0a00040f403910700c0710552181a8241045095041500020b441301005c2c410740d500071080c3c5c0d8500400352420480c00b490030940c410880b03000390200d4410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 411302329 1250 411301079 411301091
    0x20d05030417090a08030901030b090408030103031115011d0603010e0615011209050703031710030305090409021c060e0c1f1103030708090c060a0203070b04171c06051203040306 78
    0x104681c2c1c15510282805003900d580d031038850b07865503900e40180c00440d000a0524440101506110400502841d40702c103c285c2941d0841d03030259194040c805407c0071520510880c00742c28038600d01464000c04112a00307000ca4450410941c84540000345a40d00030307030520280ea50211000128250720034141e41c14032811040100048036010800036000d40380d40e041034402e10078090301168000407a4840e072200b01c017000c2503048841222800711220800401524020408640510004c002d455001000000c103030006a0009003401c42c402c1d20980440a00795154042141e030b840ae1203405d400000040040652600c001102900781c0072010550402401080700c010380503103c182d00300c000c1c1c40143ca031a454000f10040410303404035405502e901c034107000351413181800011144158102ea01452915526441c0c1d490304500280080391541512080c1003a03070110007014048002c1052000144519482d0a0340c0541d101900294440e4210200410300003100204940c100da0f0300c48004911 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 411303579 1250 411302329 411302363
    0x1415090f060f040602030c0609071a030a020d090b0a0515031b0a0e011707060503061c14010c0c05060901063b0a0905160f17011d030910020d050304 65
    0x442c080d8a05140a58002090203d40540c02002602031090804202d42c00d90742c2c1d11603540d50741c514510030a02c40b042d000c6070144550f0b801c1e80c01198081000c6c003001d40703040c50482400007103d01114058031304c00c1082041c4601c01a441c00303083c0d0080080040983c0f99036000740002d0312080402010b40782c01d078038044214800c1d110b041c0000020301c02840f00c00c4966a41d01068000c2c034200c21400c0351140103001001c100706001d0350980f800b0740c1c805021070807071840010305000142c4402c40c05586000c40702d211220b10100034001c68588407840d9035403003041602032030494a41000500302c03041a9061200c1071014588004079104200190581c88448925445101412249000f032141d4210011403c200c844001500714055a511450031695030099181e00032a0f500000c4c016413005010070034041050340d41076040140303002003803800040d4100740c401d0700d02c014040c80d407410051f0b0307040400d001c003451812140d840520016800604082e030141c3c00010240c4c0b00c0100000c0400304401c0400c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 411304829 1250 411303579 411303589
    0xc06141501121e090b0a0507050a0c06020c0d0e011403040f060b01120e0c0a0e061f030b03010212010905010e010b030f070c0b181612081806040f1415090f 68
    0x100424503200c40d083e180041c61010040d101400c03007900c42c840d00c1c0d00440c550721858440d051003441242e840e07e041c1076a804c03007102d41140448058501e40e40900012f2003051061208000001c86601c45000c0114280300142050540e103103280b601a205008020108000e113000d02503490780090b000a84c9011032005840c48080b5420304404245025a0180c0c82440094000040c034002c803580b414a50740d5110300011200100c0e811078205070f403941035600c46106044401000c580300e041c00f080e12110840402d0890b0040c9070769030900e869030700c0100a001c0c0103100b81d60241445640d07400c240e6044c085003007110310010340907aa640c40300400081c02c081c8150340890f14554001001da10508191810030840d4414071041c10090203580c8242001c1031481034058100c0b4910170b0140780b446a0390b00e483c03040b50004028005100c1c2a094200141c0e034541d0010006400042d0104040c142040318408031601c1088000d4000c520b4450100850149802911010082150000300140600d03000c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 411306079 1250 411304829 411304841
    0x4020313050615040b0906030c12120c0303150301020301060807120605040e0a05011506090302040e07320d020913050109080307020706030b030c10121503030c0614150112 75
    0x14100c2c0c001c0740d00b03110340014201c9800c2c80d8004111000c0c0300c942c1921080100d0008140c0b841c039031641c0942641060380c03d2100c100d103c215a03050654170384a0b00030f101c200d4150300c580c1066815401c00010403c1002e13484407040380c40d210a8001f103003550306280300900007800c042c0814061055a280104508410760401405410054028000c04410140417a0303101c24001d422216542060b0f5000141111186948112403550b40c030103800a265070280300080c10b1105e410f04081c0600600032510b504a075038081000c0880d626100a1086031004220098012081c0c5c98451002005940056600c5d85462038000d00240c04000050f0840d1410500514400d07000812418000c4200401c050300415400c046402c152414480190030408160311041c0031000a640000300c00e0803401250301c9580d0340218000c0104000940703004c03203100b001c00e6900b181e00490014800403401c030700b08075960007401c1951080350401c6001d410300c6100c5404881d02c001505040104018644002910030380000b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 411307329 1250 411306079 411306083
    0x608181f0207020d060902010318021e1903050a03090806010501080402100e130b1509090a020c07080307210203070309061b06090501090201030b120601050904082b06080703080904020313 82
    0x4900c000444d17207030a501030000f1b41c0040c0e010a240c00820b507909004c0d501a80e52455000780302c6070340349201c00000307094507030358410352038000005e504103180c42c064814101000c1d601030402404001424507005007114002d402903130791904803400410103170b40c22940c1680c2040d8115201204091940301c200d030861112400316034040c500c04000d8184015a50203a403580109075003501244100a582c82e00900c83c0407042c54102c10350400050b01c00110f58050640609504280d42086070341d00d030300038a540c005041c107540620460f0340c6090036441c0c54281024040c101e00203181400055100a48880c0f0b95100301000d0007070500344a4001c040100410701090b50114040102d003c0900b0028024040f46904070b0100c0d00c2c082c540f82607854090510b0100c00d200800034172080e800c0100788064247d01400480c1d0580307044c4407030b801c811f0740482c03249401900c040292035050f107a140c1c40000e4414035400107506402c044028000710b050201100e240c800c05881c0540c0daa01d80d624254840b1280d0400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 411308579 1250 411307329 411307339
    0x42d090b2d0726090c040207050c041119051908070e09150d110901060e2b2f09070c231c03051f0608040f1b0608181f020702 55
    0x2040380c40c01a0580c00e038051381600d4216051002c0340c0040c40102d224a400c0500707558051110701031607250036003000300c004600d0003038582010010401881645550542040030480120f0101c5207003191007035003010403517540350035403403410100c41c040e141c0c80303000481c14003034101000040e0200c001007104000126020308a001e0354a410706142240082c80d5140c14451602140001141842010700240c2d086000f040c07406a4407001d2503e144480107000e065452107204072080002c1806040106019441e4010041020a00999000d40c0d0b512143e000f92040364564240140b00c3e903c0311070b0300780350765014005d0341845421a4580c805041480d8482d040c1e8419158524502080b1041c0403c0720000b070b860611468495842429049507030780415003400315243e03010020103100c1c03040280c01c81e0044242000182d05911800d0715140030380030700a807105544204014959000410b1030b03100751420606140503800304141a02c0b060302d501001115042c0e14201c5503e50041c0d41206c0c07640b40d0080c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 411309829 1250 411308579 411308627
    0x207020d0221101103070c06060b0f0910030903050a050a020a0b131b0311040b041e020a090806040b070c0203030408100b0a0506120402042d090b2d07 66
    0x4900c0390103003550050b08080d004503404a8000542800f803111440f200e0071401c0e0075640c1b149021580c12100450640d0340c0c81d2034110005181c9400c0c0000d01c000444040f100303036134070410014042c042c0369039a02d0f0f03c2058541074801c40465030080a50300551f420340f808079513940760700c01c0482c0b500f420140040c102d0f0140e0401d00444c0f81f05000c01c40c05840c899940f44401d1302c10745910b994111118400a00190030b049603010040c034042d44217000742c800040c070000e12a00f0481050030b009801070160806a507000076907032045600910200028003501004043d88c0c5050b5813000050f101c0500030800344405001002c04540d024030580707020b054203a044503040c8041190020180880c000110b0240c41000300109543c10101d040b10f0001c21015a42c070b0141c1c58543c01e100040010b51040780c0e51085a000b4440f00c006090200c0198406104d00801c00d00d95134104803803898406440c04160000d805c000c2d0a54240d068100c55004054a41c1d1100590f80e040301982d5100c100c0e60140800080c1300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 411311079 1250 411309829 411309859
    0x9010801020910090303090504020f12150a051909020d0e06070201020405010921030807051308030403021305010807090509030708281418040f020406051c0b060702040207020d02 78
    0x580035194035201140e0f0860700d03064154094030807070040d020140004006030740600260506400a2180319001c1c060f103854503907513081440c8014004c1d590091505180700300b03800d052a06582030809004126100c00c00302003e00341604402225110307000b091500031440524003981a80b01c0300038402d61a0039540700b8a40840024000c0d070290044134003062041801240b6038600b170300f8000c104103000d100400c03c0d282d41c0d1030079030f0b480e04001d081c0420003004000d0300112410b203912100003418040e00440d25641144104201c06c8402225002600c2c546001003190001c002803076400c40700c1c902000542c50b01c403229100c4c04c622a220340540b2160001864803030b601914a8001c005004908a1541020300700c1001c89210510030310910b03542000f40050000144020211f41d02040000c01c0010100c403035904040990700b00d03a0102000c034202143c5001c04285230040d4001101c8056000c2140c2044800000c04a000e1440064001c6071301007020002c5469010745055110380041c41410310801038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 411312329 1250 411311079 411311081
    0x605060703200607271509030501060b070512032d0103060e0c0a090c02071d0106110c031203060402070b0406021b0a0c03030c0305042409060f09090b0d0209010801 72
    0x182d401d41c00c2210089554000309401003021401140b0035a0782084030342001030141d40414001d4044c0031104090200026a69078080103c5255091500c0e845500361440c24241e0840d099035001900c24078041000f0800550302060b050010940745590075260707100c80c00c00000131111000f4401614090350f640003071800400350410704a038030803c1c0070b005005043c00c05a4680d00303490005034121010304000d00c80100c40750001100d9102078411280029a03402188000c00d18103055494a40d100740d00620050340e1059400500c015420003e00c2a018001c0210f5a1130b0710084c1010000b100110104e5403907502c9804a540d01c9400c40141852801c190030200c0c003c2d0310a215462886101ca04803030b901c0038010485a0a444d0400000c0d5215880c40e00c068400480d80e410440400404020216007186074001302e854401c1100c16a09070301c641490050190001a00010144880e8060100100307a000c050b0009a840b00540400d013100d8080203c1c4910b40c1c1c00070000c0d4410002c1c400401c1d83c0c001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 411313579 1250 411312329 411312347
    0x305190908042c071707020313030209060409080d09110d03080106050307031803020d180b030f040302010b0d050a1104060e0604090c091e1a01050a0f020a060e0f0609010614040902040605060703 85
    0x8002c00c911817944800c1401d0303949208101d03e510701d003c0040b1042015107422002c1503800440038101103851005682e50803071700d0b030148c130707264000785d40da401c08e0340901c480c01c49507040f20501a00d003004421a2900c025200340814810f034800c103c4000001180d10f8402c0e00100e8101003601c0400107200700601d40a900e80e844401600000340440c0708200c1c82c01c41141c154012504140d00040c45c40e101c1094010206d0b100820131b45c10b43d92241190a02d035100c0e1022a0b000078042e401500d1804402e1400491100c100e80c4414840c608244007800041d07a47d07040550040d0341202c00044941c0145400404400b1580c0006451441d142d5000c0c60606080022203000c00f02003410481c1501a078190009000b0a508840c000303607007030050507401401041120302c19103142c01210310203001a604c2c00140d40d007885860250360805a855606084100f00c03042c0c00070707a228000d1102c2d43c10110111198052011080d10450711b1345c80c0382080d503c40c0c2c1d0103030b0080c140140800744d480f101401d0140c44201c0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 411314829 1250 411313579 411313607
    0xb1c0302210f07141e07080c0105031005010e1f030f0e01020c030304081b0613020f01090e1b0d06080a0c0909030e011d040501060305190908042c07 65
    0xa241c00003000e0840c0a4121101d402d40d0208150920703080d600c881910002900c01560a40308412200744198180f810040c20071a544004005d454141280141045240303910300c0d050080900511070240301c0c01c00c20b54281c40080c0f8211840d16201ca000400c041c1150b10050b001c0c0010728504007080c0d5041d000702031480010203052280e03603464a5400c0c04c0b44201c00184119810620100e000103250348014190018504104203001e2402460203042100503030340c001103034100260007811170800801c02c0302420000d0030f101418a103400317214000e141c4d005009284000c02a180078840000c0d1780b05450300003c00d484100000e98580c06110750382c0c00000c000303456015101c4400a00c44100340682e0f450346901d40e440c043c180c000507005580300080411030b0358161000704074099483d111842024000c00c50399401040701e046c00040c51040c9525140340c100014200118840032581031f00444040390621000710484504010110440901c01003a5520013075080041c03043d0b0b598852482a4100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 411316079 1250 411314829 411314863
    0x30501060905030303061305090f0d02070608010519060f0302120901060e1b120601030605031b0109120309050d1a0c0405190e13140106030602030901110901120b1c0302 74
    0x6480b5401c0640ea80030881d0510f81c0102910691a004046a081170360822180011a40c3ca80b00e030710881d1303052010740751020b030040e40f01c42410404079a1002585005241c107840700085501c580c01007644905032402510107001c0c1d001d01c1c003100c03c1d20030760454642000c803e000d100241021503516020300f0491081c4a10707400c0000100302c0e1401c1c08144007204d800324801039440c00245d5100c00c5150800104003038141640d81c40006000c1d103050042c80882401b00310703c0b61074101c6010001d4645d405035000641400c080792050740000f60030032505c5085d18801c5032000203c040514241800c655402d0168680b0003803d410f2001c40300d1014041e00079100c00710784800100e000c0c0700300104806c11a1003101200c1c8103400c0410090010604c2c15411940220400d10524a07213802ca1401d50301242e208a400b282d00104215001c00284200140c0e91100e0808900c0c08855400090011281c1101d007840640d450a9070070007031381c440429006681404c841c80c1084003841c00e002e5254a481d14804200e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 411317329 1250 411316079 411316097
    0x9140a0b060a18120302030d05070509060d0b0609041b1e080c07060e0d0c150218011103070519060506010311190306050301021902120703080f13020d0303050106 71
    0x1210600909840c0d03600507081c0350800e95000c004903198600c07943d582c194905141d2000c62195100000d00c01e00500940085030f0701c40c007000e00101250001032035101000818096040c2580e10a0111100315a60f40404606099044000784807481414089640540f504895101a0b112014003041030131194480c80c00840040d03c0740c0d04000b81c0041c4443c0042c9454000454500003031024004003030180c20000368502003400103d15001819140f44d0103d42d1020124007004100e030030f20003200e00440425410b141240164060960b00c1004040c103002803d4000011000200103540700c5980010844000d0410100c0610b41c003094000305a980f9810140018215402802040c1c801307601489414540310740182d28001100c04401c0a4003019207803c00010107641c02d001508527002c05113092345034aa00090040d10303051001e4643c001001c400c0c000b41c1c0100341c00c44c0c000e603800403207040300998543e43c189144010500111009510034580e03492681455071540c00309040e10103030744410140d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 411318579 1250 411317329 411317341
    0x20316030b01030b0403110109050106150c050d08070512010f14030c131112100602060907080a03050a1b030305090f0106240207120302030309160503150c130914 71
    0x2141024000501180d2406004000080c02c1800301d66000c0d0081ca08405001c1d80c200c2694252000d81a007075a040e91610310903c200b51105a954030304039142c2c10308541054895031f507151035180c032030510f00c10301c161500000e0081d40074404032010800785810180b00c542c0c5807441a03204101c10b0048000e22103440301c0128442c01e0006140c80000c0d4000d0500c10b44115015a2070040e11241242c4280d090050180c01312680c24500c1c101e0060001031303001504c0d40c0c1070031300003440c0c08001005203003a5880716004110411002c5000301410340c0503c0e01e15038038052042d069030100c56054018100c442d22903c0401071603072680c041801048201c058881e104101441a400d0751801c0c05081c940705c01c100c28050008402c002c1400044100d4019110107643d200303100100e9000f040400e4000d84c200000f001400d240038088481c0d05000c9180c1c0d07508035801c010101c1e0381c840080c40d01c40c440b44485004246d500603010140d030710b00c08100d0b125102e00d688450202c005030540c2e41821462000e13980c00700f14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 411319829 1250 411318579 411318613
    0x50a081b0a06080a0b040e0a0501062102100f0504180b0301140601050a050d140f150411040b03041115180a050d080a110a0303050106080f1023040e0a0203 68
    0xc66000b992124010303101d01c0d139403074002e004004035a6886503403108200703000309081c00201d07541401400001462450407105414503079000c69001220030050183c1c60042e5600c40d40030b420039030140740c042c2d2031012501c01036525100343c0c0c10031340402e9054004030210030200e42240410380c000354003e00c111028005c900031103a4050318070720f0109a080c443d0000c03075881280a400d40d50003403031000c0342e541c40c003c10400607900309448004032640c43c5010003035240510080210004025030313003006114207000240703c2d06c0c010b602031039500c0017001020409008101030008400e6a000300008a00040040310303410981c001105024000352141082d0300610301040b901e8200c070750203461a10110039581d60074060b40e21400000c014042d04186288550404020180c14144203480c001032650500a0103001110010212040f038001807003003018100c2d002032200d044511040001d4001c100200e03205600030a1031b01c449810a2038550300000c0074100040d45c1c40028026019241d100d40e07980c1c0006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 411321079 1250 411319829 411319849
    0x20a0f0c081c0219050a080d2f03010b0703110d050903010f060f150504030501140406060803210702010917040603050105120d05032d0f0903161b050a081b 68
    0x400942c0040c401281d4840c8130440d4002c503144210151a200c01c0780e95100c1d01b00d500458410003805986402898080c0c1c1c40150350340c0000b02c40ca2008401e10152104d01d1100d100502031000c2105010404000301805407000044003210102564509026440024140d40100d03220a10a41c00c16000b108505001d10540003a0303072450384210101c505181d8082d0511800351180c0081010400c000030101d0001c1c4900048044511200031890407d810081d050340c0003504020065003040000d40d42c0c041129400010384100701040642c6070f42c0d01d00d8180d0040c02110400303014902030307440301102e540d06c1c1d800030000e43d00310b510104840e0362980c081c031403078074048143e04a03568041400c209040b8026405560301c02c07074410340c0520000030140e0715108101c101c1050b000302d01c4150300340303e44a071000e0fa0f8640d00c21780b05c1c0000d60510500940c0d2440c4c4190449020300030100b408041550310032056032040281c80301070724030180700d5900c6a1640d6a800d800c42d1602c03a580795401006c00038a4240511 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 411322329 1250 411321079 411321133
    0x2609150c0711122406030c041b030e030903010204140a08010c05030f150a06110c060a0507020d0618050601090507051603030209130f140f0603030415020a0f0c08 71
    0x600d0b07800110b141840203240b048403126600c0d1054000c8400c1c14240d14076481d2420190303014840503410414241403818840007002d42c0308500f041c5000c02281c0f031071881c0300d01002e864035001c10f03460b009044081c00c6100c1c1440442c0c15500006012481440c0120f42c07501c60001500c00e03005841c1d94003051030803511002d80d40400900f0800104903141008040f46401c078034088010007134420305000007000b2610946c051000b00d04119aa101191418088011020f004be42c055103070803407100000784a80304480000340f042038200703949024040c80760b1080700c2c80500c451521544181d6420710350380d900e409220700b00d9114140000107030560f1142084d2041c0100701118400f00041507035082d4003942001c5540381c0c101769103215140000320350b4040c1440e5076400381030002d24005801217007449018010081d243c1508580d050124a0303d0000868003290128440781d0780000a074041281042e155100242090141401c44805d001207014001c1c1103441c240122210041010a6041002c0f0301600d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 411323579 1250 411322329 411322343
    0x140a08011401030201360303080f010501121a090a02090a081c030203090f06160e012102070c030807050723010e0f030327010212070f032609150c07 65
    0x400055001b502d4001d201d00284036501441c410059a8500300c0d403c4800e250302e410081c1d1005c00506410030752180c4c21010301660381c01c0a60401300081d2164031040110076115641d003a58611300020045500002e81c8014500010340c03c0ca41c8001000c3c1d002150360f035201d510218000035140700c00090310924600da0000d190401c06110030300350000d406c000d2a80005020f41c607903210400d48140000c074402c6c8460140465828000c0341d0081215910416440c10310800c0924440c040612200c050540300310108090781c1c0d59510b00e88600344030829803000306a254042070303044c20088003003090341c05e83c1e000c13001034080036141010368001113005186140c003003004841c960060b801c0030311200040c804045d00b00ca1030542500d00e0103001030324800f48100e81305a02554180150f0341845802c0008800d580802d00f0f0103c246c0385d0452910291100800b400104040e010610608500d24212034107054203040480c5000c0781541c0c0c580c3d0f00b040b2016100c00035280010030840e06074040d10001904907071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 411324829 1250 411323579 411323581
    0xc0a14040f0f0c0201050906100302030c06031f141f1b020a05031014070504030b0115140f0c07090501180203040503090a060906080f07050a0c02040e0106140a080114 73
    0x1440001c1c0200d11100407926180c02ca840c20400d030034029511200e000798000603480c60494145410201c0281450b101e01507500783c20005aa400902d503074808408a40280d560303125603181c2495100e460200c0d40c02d2290210000505a10012070030f012a5000d030307000100080c01c10881500204442005004602c484480c03181d070b10105403880388000e20241c41003201c6a110400285403016503040f136181c641d25601241032151072600705c590082200c0c1041c50800707003980e0304d4031401081401030785002c021500d0f5820b0958030420000102d92028462203a50342503171886030005034060b05c002981446881c200061040342485014120390105035400000c0052140700701c0070b03600c050310a0340c15200902400341d49682e46810100103081d80e803078080687c1d2034000080d00880004100c00c1e03203030072080c08002c803454200341110050600c0c0c2c541030180382d0942c40010028220007940801c42d42c6005008221601c20400e10320a400341210341071003955070b84070300600b80c4010b40714a80380c04a00c44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 411326079 1250 411324829 411324869
    0x709180b040b03100b190e160c080a050c01050619050d080d02182103070311150403020c130e070515070f0303091419020108070c0b010b0c0c0a 63
    0x361203003080010050020400348580e0000078034000c0c0c80401105060380d54800b003401d40c5003440c4e402d540386420350364540c07119240c1844940c00d480000c0c0082e400c14141c0c5041101a8825602010300710350001e210360f01c031440b00c40010440d0b000200d815410351300c0d01d00414454075290341000003400c02102c00d061428140710070720042140032082206d40d070500f8800c4a0709102240080e000c9012800ba0000c0074060010170812500d2212000050250108010703602d00000401110281505810300610729030306101d4052500003410140140b000350391062004155012400304800f440c102c0c0c40081d0300350358541103001c5420002c0c900320b8660042e2002c01c21303414400bc44201c51074940f250141440c242e81c845031542c1c4003403581280040d46c4c900790034003000354400c603030740c48026240001e00045040b201d840321144494076010703042c0422400003e45813440b805841c0c2c60940e10100444065a540184491542007503029034410f0059000805442c1081c40b101c804072203080894480340b00e400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 411327329 1250 411326079 411326081
    0x309050d03020a03060f03050d23090f010e03061303020f03160b0601140c0a0203060c0708072303041d0109020c0312130b01080a020405090d0c080c07030b0f040b070918 74
    0xb8146100501d81c07505c400140c10074060980c940150301030300c05000200301c907400c0109519203213005200b038401000d400c03130000c9080d00300f960100c4905450300381244440c2401030750f8132880ca41501c1e0b07052203100200701100480c1c41c0f401000902c070b03400f1920128003e45440f40c5030f01a144403161004074010804000c87c0421380c0d07480d000f11040c1403c03400d600c0c605002c28070b01d034040400c01840d80c0c8a21001d00443c02c04000840d0f11035001d681c1641003840b195180c211070b104883c00603109618000b40c020501140c044c030341c1c0710380100c00102e0780e480b039450803030004000d405510312103203080d100300000d07854415000300e40d10305601d040a14a805000102c50420060103015001d108495130107000000f81c044100c24040c04281c001080c800e4001c1c810442510b00051107a082034100011009a09030083c0310707112580c0d480040076480d20980c141071403512030154030182c581202e4205004036001d0290307195000e5070050f03000d8501030b920364000380d482d048580b10312000382e80088100d611003221 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 411328579 1250 411327329 411327337
    0xd0210050706150b12450706050904021e041404050c030906060108130204061d0907080706200304062a11130f0f0501080706020109020609060f04090c0c0209070309050d0302 76
    0x101c94820b8401e40e40140d20642c903412451b5080300000d81201600880f622110700c0300c500031402c1005110b800e0030716000034a03e0051029450080d034001c1051251030304804100c2c03481009100c0d60310380307030b9945a5100c0404407a029003c0d0260703252001081e00707070292a007102c1c41403400e1801407405486000c011103614034000c1c0f03070300098202d582c008001a50340303019100051406402c2d0341c60120188004054900024250720007c0d4815241080160390106d01d0342d045a00c5410018898000016031914400315004150740074000002d0208440741c100e0110002220490080303800b00381c1c00c18440074242e0b0950005031001c3c250b029200c0c0980b421624000151400841c0400c1052080003c00c6c142d411a484064240762a071005110101b0b0402c000d0008280307910080c005034001d44c012400501c81c03e400f00d4090940001c1d1000c0040c500c500719001003c190740104980b0007101c1d00109280190001244144900300c0400c541610030b0103842d000341d8000700034004903a65444264000d41c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 411329829 1250 411328579 411328591
    0xe011d150403060219030b010f140c010e10093302090d0605040501141003081b0718060311060c0303070c020f041a030d020706020a03030b0d0210050706150b12 70
    0x80c0400000c0300241c40b038006400303400701016800005803001e61014040e20701c0c8000b691304121940c10303581c02e2940e0140407050800c0316195800c0da02c0d201e26003c1805800ba45130158410711462000c00c8900d49550b003d0704a41e03003d010481e0751120007c40f100b413860550752000d0800c100300314440300004450742c000d044110380107212924010065030f403041a103c0446056807a03940d2014034243c0203460068641d80032041381100240c40f410342c0d82e2940940035240300350144624421584050310030400440e400b6040c07440515151507510001c82029100c640401c81d4020191400041682004403d46204448440141d030035582c40a400b02d40100c100342c030a2f680b0106080d104071154a8922405e482c03071410004201034558200203061a008503100c4036000c5601c00340042003031a03404030b0f5118010390b1626000c1014411a400209203810001006c0e60120b038802010407000c1c0c200004012451040406006540207a04880b81ca03100c18440e940c89800300b000f80700320705001040895230200c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 411330935 1106 411329829 411329869
    0x912120a140706060305030a0e06070c05010507020a0506030106020109230d0809030d0507081611061906080a0f031119030804050319030c0e011d 64
    0x21085200300800c0140503804044003511501c00c480c81e090300300005000700c5480e03040440d1a0307032000c454240424882e040c030809506040c0144e8011580002c2c00911b01843c090064585d6808440c040382d008038020300119450340c0e00c0010b14042c108540c00020402c1303071443c050b00946c440da45800d8403e2040100d241c03002c1b000003111031008503103240c1052035032100c00250349107018034218440c40c282410108054103500c401c1040c441c030561404007101c0d02c2140f0b02500c1c403c0f104151003a49820560004103180355000d41034010500300a000035285503100806400d00400100413201482031044442c00c1c15445818219007804400282c0944581d001918100c115494801400e0080c80e80014007803000030b10988031844c0f66a00b9020300d00b905031f100100140042542c00012602c0b04159544951145c812141d01d0f1480e0100640c1031103400d0100301c1d0300003000c00529021 = true := by decide +kernel

theorem cover : BRFrame.Cov 411151079 411330935 := by
  have h0 := BRFrame.cov_init 411151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 411151079 ≤ n) (h2 : n < 411330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
