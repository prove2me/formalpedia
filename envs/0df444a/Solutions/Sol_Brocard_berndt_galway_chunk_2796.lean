-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2796
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:08.875294+00:00
-- url     : https://prove2.me/submissions/1439e9e4-7d49-4028-ba9e-98d7ad7360c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 502697841 ≤ n < 502877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 502699091 1250 502697841 502697849
    0x9150e06131d0f130812060a0b030c071106070f170d0609020d0513080301030b070c06021207030e03090d0618021906110102041a0a02012a110601060c0305070503090604 74
    0x1062914034054400640c00f080c050942c0340180000c003107000000d07000b0b1040721142802e100192807950350300c000045104055400c21004d001000c014005101e08480103480c0080c1302e0b2540001456504050011500494802070218080e10398203101042090f00503000358810000d4291401c500c0707030306001c290741c82c5038020170100b5030000302750b0307d842042d12400c0e801180c41d0070013000703054803a01c0d22045408180400740c07a0300103000108513110f004050380c0708499400346065481e02010740a030517106100310703810300100f41000c082c0d00310f424022040f11043c06008180d00c0204803281c4600c00240a5a814142c4001101d180c05000d661140800d2441080000f61180d42904168006040c14040c260361003150780140000e12514080000d0010880120002e0340e4441e940e1940c00c03409001c1200c1d207903030040c542020a40c043c0a01c181000900320180c0c6551105001d42d405195442c0401d225140000c0c1d07004501c0000244142c00520342e03d401481101d040a034001c0024002d91b0050340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 502700341 1250 502699091 502699139
    0x807270918030e03060106091806050312030f07212007060c09140a060f030b130c170f01050f06190203040e0c09030a060510090e0303010609150e0613 66
    0x41c0d4008159000c89554114801500684020752600902821800c00e0b4002c0c05075006000c00030f001664071a62126005260017800c544015603880740604a44d407003034030b00c0c08043c04003600080019001d4040807800c1c40d00300b4000e00740c140b4500c2041004001c6201d078120824420340c50004000178010150521341e00a034400204100780c0c15010701858400e90203961980216080351900e80e50300d4148100311409401c041900703104119003100204004072a8075400056440ca8000131095980421100340c069102c03031000b1a903456007080040b50449101c034203002664014480c60420303510188072841c0160542e42802d403284d580c0350180020b44680c4006174804242002100500d0100701d4001171840c1032645801008000700b91600c543c00005003c035030700e03200072807441481141e20400502141000b00186100f1070042a2254400e11404000a00d80400410b0800d2846a21085550140c540300050040c02c2d0910240d9004030501540c10006844000b03120a4821584998002045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 502701591 1250 502700341 502700381
    0x303090f1e0d08121819030e090a0501050a050607050a02150708040803130605122a0c0a0b0f010e15011806020a060c08071d0d02121c08072709 63
    0x1180300306400710001c02c0340c0d4100d02c8445c500854118003240f054505410400f92410b840e149040944958244020054011040204110716120340741e0002d41030700d8007140c0421010365540c04001c1940030300f800113841034001071b0304d4500610341411001003000202050b103062804903200c24a49800581c00b0300242c0d00002200d00d017020022841078060000c90424a0500e03610105816922a008106a00c66900c4e940103031192214110010f0b01c102c203002c0102d039900d060301e003050780300ea401642c03c65005403584046080200c80c080000e040c1c0e4100c8810503060754504003d00e51201b200049281031069130030720104500c00111a11003c3d2880d0380007403008590601d070940c11107220500c0345013002281818042981c2c1c2c454844000d9160341040c00042250b40030008811a00001c0300030340c00341c1c0401c40d00514000116240450010240d441c44090112000c2912011808c441120002d98034003070224000c0c4003401c10000b8040808405c42440351140001d00458217400440100b0303200712 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 502702841 1250 502701591 502701607
    0x504020c0f121c0b12030f0c061302030325050102030103060b03060f070e040c0905130c121a062d0d1112010506071505040b060f0303090f1e0d08 64
    0x100b00032041c0110004005141c480d4040c10780d42d692114071840781d40d16407104a00c24984c0c3d200700c02e18100d100618140ca82c2c407050b403081851640d03c0000034001a008190004828095031200003c403584c000c1d018500c3c0c42c1c060b0003103d046141c3c800b0a08240104000c4810114109101441c080c40c410713440052541c0d6a44100f600d4414001e0032812030380741a8080040c995800305500448032002d031004a029251140190390241d100e4002c99003012401c800d51000c07800c0c0c0e030002c00c25100b0b10b441c0c00c07003216410340100c4182d40750184603010780680e000e031006031030403c240209582d01d5030140314034168818103200d01407020014a0b4009040010034039540c402183c2c0b24840031449802051460300c03110305800d00900d10140b181d02d205e0b80010411400f4400c0c0008455643c002080c000c0041d1b1070300d0f1030f2180081205603205401426528070843d801d0500008541c20410020804028105441c04006101c01d82c40a0502c82544007031a01c02d1907150119210101d038401d0408980f00c1000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 502704091 1250 502702841 502702843
    0xa0f050622110108070509060d0c140c12071401020d06061e0e090c120106020a0c0b120a1e0609020913060f090c05090904031e0e011d0a0504020c0f 65
    0x41c910341c0c09a40340604508400084220410038039564007828519466a40d0031016141d40c000c80001540044000800d2150051258009600303100c19440e280c1081441d000940028000c00c0c03281106584a450039120150400000d000761510800110031800c06184140f400d9800100f003510b14143c460720244541343d044081d01c491034a40140016503a00030400050002c001d101425014683c007202280720301c82c4081c2162803004440000d08200c4d41d45800007076079a110441c7c10f07500e9400520307011890f50021030403910005018034840786580c48040c03520b40146102c4444550700040d0780311890340403040d806440000c109403000162100703c903c061000035003194465a000c64500300d401d001c14501c01034408180e40104a0001c0c810490b824251a588030700c4240d01e41c441500030405c8209a07100c0044168081040c21040f0714514003001903c801495540103804203548010111318200c4110b2680c1410384000c01c184030580e1b40d100401c0c02c0380d01c215507040c055008624000350742c0c54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 502705341 1250 502704091 502704121
    0xc0303030b0a0e061008041103060f0403090501031b0318061e050108060603060705070305120f0412020d050315011b0c1e0b0a08070e0a060306080d030e100b030a0f0506 74
    0x10200c000081c0d83e01c1d15000044091040084000501051001050500480c440e048c1085c0e000a0304980641c204600e0300324000320125401c8000039580c00c6c1c04a0749500c2030140740e064240340700d2004000b04c42441d06802400d4040d0604000380280701403003002c1780403409856100c84d40001c01c0b0312500c1c4168140c078242d900c142c104207050760101c1d040c00820b880006620742d00040e50306d00386403103c0007807900700c500348144c100e604511111007082c070000b00d1042c2400c500070f0f40720b45910742c1c20100507070040ea1503d203117010035400308800340001400041440006120034005240507041d031108002100c001800705901515070403140501030100d800324403050000c1164400c401e9144600d884442c081503c90300c0360030403c02054a021402e0755008190009d81076000174051031382140c5610000700144028405c58000d44140540316454a019200d036019085550307015092070981d0b0225540034144100503560148200000c1d03001043c80c0340c0100d000c0f144254041e01060802c01040c1846c1f030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 502706591 1250 502705341 502705349
    0x7060e010e0103151a040f1409150a03080a0504170303090c0d0b0705070c09050f150a0e0408070c0b03041101080f010518091908130b030426070c0303030b0a 69
    0x500d07115040d4052207800244c01c0403030fa100602070f480f40b61011881e01080c01554045126080d862002182958a100c81050181c005691010301d070381d61001030382c01096500108540180c1170742410f2020905180c01007070814207500b040e500c0c0ca030b960040e400381490180034001c690303080407081c0298000207001e045008202194a03d01291158036440000750014050009100700068a0410803c18064040040106030010003040c9020295000440030880f00040e1401e1880c0e0f0390507280c6010005401560070b80031403819244d0302d03136444030040e611030130043d54031885100000841e00c07080801144103620800d4204940078012001600d48070000e00100a1011b1000041c401d688840c1c5100c250b010380384000b00407a49480810908114070b10702804e0884050403102c0060000c0d0000410b60602da10702c02299855541d036010500b40010f89008020014542c0c503110070728808031604040700707404068140b5000301c91f030350f5052041250380103e005c207845410844940c50a40d071000000c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 502707841 1250 502706591 502706597
    0x31d03070602100207050c27010b0c0703020105030a0e071203020105010803030c16020f0301150f0f030b0c0304031818050a0b10030e0a0204090602040e090d080106030b01020f07060e010e01 83
    0x25030411602a4940f0304100100c030110360f001c0381c5c2d1024030104004006581d00060600150203041110301f920001c0c55091220314031800000000e4031480040c2220443ca040d20041d145660543c3d00449480e4406061040ea140c2c071143c1c00c10b0224820700946004007803e1552401c950b016140180c2501d07016031161485410900410204140d42e20032504400780c0c07402241a01c641900c00100241c801868240e055842c04041142e200f11035000700e03060b911149404502d581d6074008684003000c90b804002d1094407203401089190400d00c0c0138580191090402d030035501d0011280956102403603000b0300700b0101c582d0483d0080c1c0e1640c0300d12500028000c00500400c8084000304000070304194502d42095600d14030f603103210209101004140303600401c11711100085040807c06074000d4044d40d5040c4007400701060420078000b504405511540d107400202e0b03071030503801350000c001040010b4150302800024824010007441044042c01c595150308900c01c485000040c15903407a081c425041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 502709091 1250 502707841 502707853
    0x30501030b010e07030e1203010609090509031b032701090501020118020603070306181406031b100314091b03030a210905030f070605070905060711120a031d03 70
    0x42584204294103641c1111084985601c0d0401c0c221700500e04120000401d0180c0401940740c040d0842c0258101e448644e5074102040c2c40d00e01120480308143d50740d600c9039000304100080c1c0c1c51044002254408184280e90400c6100c2c00c2106250040a80040004510070030244075984c00c4141c00d00900420303c000c000c8803c0d00b0003003452041410740301912030300300440029500761082e0400800792550f042a802c0701100843c4540c050006105e030810008140800146c8034280000c061315640b000f07820703c18484680006100c001c0c054841c5113810540c8030300005084426659920780544c03443c4004003211000340c0200010204031405c500e00c26001041180240c5030f012040e094191052070154031400c6030341c2d40400051541c0c01004041d8000400e0304d02580700728401800c1e03650f0060f40700780480d6481103c2201c1000880c02850b82c80101070208402241d0595030301d0080f01c0c005040d1721900c06200d040d04c0e00c0c06a410308110700054462501e43c4031186440350380002103409030000c0107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 502710341 1250 502709091 502709093
    0x20309040f0e031204080408120403021e1014090d110f030106061706030f0703050708100b06040909020d1401090c09020316140d02070602040e071e05070f020306070807020d03050103 80
    0x346a01c80c41141180c1150079130045414000c0081c00c850042607000210341202d4080014509030b50443d10099108607010070700b44054448000091301048401030040c80c68140c80c4100740d030781c200320582d50b59064006100503513031510f445003000052402040340000c0c4540351000c202c1e4104800300d1241c0a030741000820403a40340c100c04d14030401d40341c000c88000f0340c0e03903900046031a203030780750041004e44d01c6040400020b0004c003060309402d45061342c090b00d400002c403030b100c141075a00c2c580d496a00414204001c120410455000300c0182e4030081c24001c3d6684680c450804c2484048682c2c1c0c11f0303941d101d50500400c405400404000c1c901070f1019421450940d04c941002d4941903011010f102480d0380d80034004203120700300c60802da1810740464072046c040c10414025041130084007001031070032005c100140c1c0142290b030f100401d01c42002c1142e40b0860030403103454102c014129071a40714660800c0069609000703452052501d40e0310040c9514140e00024500b4000149640605181c500140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 502711591 1250 502710341 502710343
    0x7050c12070b0c0f0a0f0309090e03030c0304050f0d030e070617150d12030209040621030f0207050a0902091c05191a10030302071a0306040f02040510020309040f0e 72
    0x7408079684040712075152000400d0322820510300a580c0b80007070040c805100c2c200400ca650440722a4041da0b90a0902c584424044044034590515542c140e403040c4005181500d05030010342e4490310503000e42d0b240c082d94415187c80c04100240c5500443c0e181c0d140f0b4020000100300070030082c000d40c504201c0205a00c00d8800140d040034000f600c45c10021514014152110002c00030750641c001000c805203920004020025004080024480c605010700080c009030320a10300c01402443c8000300d5203101483d07038140c9145140316002c400b58061082d002030f6641e1003100d00001010813403400b41c0c0d07407094078040160f010403041c03051002c50745280e00703032001c0750001605003100c8007100d0321036030b07030603654109400310180ca41104040c9403070050411654646180c080d104507403290b002c40c1d008a450b10080101e252901035009200f620500002da403618060300a4090012540b4006180035126004614107d40f4105101d026a0001519041d1800e161140c0f042c03101c0801d50400c541c0548500301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 502712841 1250 502711591 502711603
    0x50306160c0807020d0b0406020702031501241e030609060b070812070309060915051503030a1d0910140102070b07060c0905060d0e0c09090a0f03030f0f0207050c12 72
    0x34180c900b012864104540b42c924180b15160f410066040780d0745081d29000e0065030015404074081d000d03041601c42510311032078885041c0c489803812170040700d14024190900101103510301d41009032040f070807480d1000d16026600207500d940d5000c1143d500346843c03201a40c919910000c0e40307000030800507000c5585001580c843c01c5041c14000c020fa1680c40e0101d0103000d803c5805013000e0325080c03a040421078080f0280743c4102d4002c7d001c3c0030650f00c945a026051600320707182078140e0000c000d1520514030075805580303100c0c144104102c0088281c0007050400c08101c580180c4058002000d008003140307003015840e02c06092000300500c9007022007160315405481c400500300780c4c580114a00f124000c907501805071401400ca1902c40700d001c01c00401810a102d0f440b04a402103201d0446d41d401c0141155210b070f141030000b4040307245280e43e02d00d402c018250099040540d614900c5d0a40d00240c002c03511140c0c1103010160305c0c1c40c1c6a061090410102080480c403c0301e0000744c00000d05001703da0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 502714091 1250 502712841 502712843
    0x150b0306091503070909030f0c080306061b1606110613110301090615150908060720070f0512010c1202030a0608030301081005010b0f07020d080c060907050306160c 72
    0x11000e40e80d00c42c500740d8185611080700155040c010310002040e40e01c001e03401078036628001d6440c0411031070701c10b10039035140d030a1440151212038200000382e03442c00c020008140c07240c40c0001c0035071140002d8090740c2c10900700d117548010141594100304103407136000c0b4000001185400140419007010072818a100d100c003074008004240e014009500d40d82c0a500004c82c41c0d4011106000d80b6115071002042c2c0c09143c05240c4005002c1c95001c192a88121884415250070038024079081e2a00740003a1400010143c0c0c2641034240c110345040d441c3c0080c4110030040c40c4840750385c3c44a074101810044ca1552007544034599a24003103814007420b5000700c41c04940320040c1001a5203071540b03101c2e40c0141410340c00a0040b44800400099412000603803040031089c2e10700100101d0b600c2c0c1081d03104078400c1461841025405111071000b40c41d06e0044602000d10482440e4a00500c088016051040c01c6601c21050b4120300c400300841d040901050381e00010303014241e42d405c01007100140c042649100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 502715341 1250 502714091 502714099
    0x3091218040902040b2206090902030703060b0301090c09060f240e0a2c06060a05030406021c05042907170415020c03030405070f03030e01120b150a03150b0306 70
    0x82d10300564445a00c480e81d6608060034601c1103004403241c2d000c903680450100c035600c03450300d58000358900300e900c1821007050f4014042e1010324a51346071800508000070303c00381d141d541c501102001442d81090400209405200411030901c1c00010504004690b40071007070703070302d409443ca00c81409a103215030720f540400d013008510300d410b03c1c0215482c00f40542105041450040e0280c11014907007030b801c029182d08ea00000c01954030101070066a0227507214600c00710703d043c4045400a01550044c0030050b00c003c0d006400600b074001c032401581c00654044e00c0c40402400203206200201c1000c0d0081800c06014800c9400e240b940200700030080104103d20020300320110b4100320a070a44c0d03034007803918510150f440d0000000c1158490f4800e5804854920882e640022283d0541d80c3c02c1045980585a2100402040c0c0040d221002c1e130105481c1e0305c598900107452982c1e43e200340031101c41080c08043e925082c1c02200a001c0782c504c811606141c080098013000095184800c86c0c0d4000c07402d032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 502716591 1250 502715341 502715351
    0x6090314010f0c020f0616050a0813080a08160305010b090f040e030706270503030720010618110c060a0b030a061406090703051b0c03040b0f0309121804 67
    0x903206401008a140110002c2e401c01c000d21000c2a40041c04c1c1d66601005820340743e640d25100902e1181c4214041c0c144045481401101e6649006200141d803001564854149564081d600d8180641c46200c25601090146050001d10702a250701034071081c0042c1420803655050225803581d600403644014030070000d940011880742c440d42c200d00c555054180860382c44060350716003000a8103001d011203100e8444205610380d85541207101800e85c0fa0001c001e107256461345241102c4060000d01c00c45030035860100c0d05442103609121b0880204086400e1580c1c000d031503a0010191035205174525041d40051240545400021800c65000180903200150314004c4a01280c1803105203107000d80218036010411541c0c04a00d00c0c00c030311075001211140803d5445c078209904035075080ea9807035620000c284180320350303217182c00003000c039103070b000c000c40381807503540e00340000154400300340d07001c0304400031052042840d000c000d8600c1c22112956100d040c000c10780ca81641c2001440030f82841140c0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 502717841 1250 502716591 502716623
    0xf0e0f0d0b07122c03160605040807050d11010b100516030c120f030507091401080408131404060807150503100f0e060f0901050319080d061e05040501060903 69
    0x30143c034640100e403c60140f06902c1c3c50a40148090100c0040310203502d01e03456403111441011080303d542800007540da1404050039100c2c42c00811000b0320807188210704002c1000403c0341001444141281507803441084464485094203503002d003061203020700c01c2c8451075108590407000392031218041d5034094224a21609048440021803080945080f401c207055125a44e0b0000004500029545080c132450301c8481085466580300d00c1a003c16110f01e2111030a958410400181c00c00d001e102c506003040500150704505504035030222100d080306561a070601c0c2040d005850003003024901070b040712403500d1020713443304c0f014030380030010480000009a8a000101440405801550380080c4044c1c3c50b20000d800d000c034107468040c4150b030700007c185107505d0a014201d040c0c0c1c4020f4050648204840b400d01155071900400300d40301e006c14040c000c903552061060400505083c901c08140e10f9880e080340001c803880750420b9004904100061191396000300b500b4045a038030088408840041e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 502719091 1250 502717841 502717847
    0x910050430020a0f06020c0117040308151c1109010f06050a03020d060f031406061309020d02030d0905010f11210c101d0a020315070207080601060f0e0f0d0b07 70
    0x50707a90000c1d800034142001140002490000b13009568042c0c080750f19600022005440040c1c40c1c3d001d01c0543d2000d42c00090001740705100050b0400860307010f030412007103594000b4036018003940c4e4542c001050f03202c20a00780540c2d066440314851041d100d86400d54140ba07034401e9200000d020b1f00d4203100780051030007240c610a50449900f20280c4c0c508110942d12940005001c901901c8141c2e40342e440e241c2d0b170f01044d6001156103401200300030200000d00e060b0706000d001401c0181c01c01c0c1d0b800034070620103c0258605000c804003c036003030395954817118204070026150241e12051030080045015030301300c4100d80000c14242000f0f100d6030320526802100b40b41c1c035051241c4248403003103016194451440184d0307034000c040b1401c00a80d5198640707071740340d8000395120400603000c0d40c90362042074003000b820f82d0700c000d541e00110148140c65440f6107400d443c91900f10281d008c003001450008403800304540c001403080507400c0031a092111540d0150006881400440001d41030a0625010580d00c40c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 502720341 1250 502719091 502719179
    0xa031b03050105040b190c0c03080709050603011d09030406020d0c170c0c031c0909091106030c0c1c170903270406080109080f0304050a14010209100504 67
    0x25124000f40301d42d2920b4904100d030000140d0b00c071848007100d0041200c40f10114001c42c80c0b00d8143d40e803248850741140d18219105d440181c206002d0113801c0b14003040c60380703800d00210f002c0c00000b26141c040301c0318004041041c0340024803040503038200b40b205010503640031903d0100440b581c03802183c1480d8504000000042c01c10701d000307070580005405104400046007442c0c0d1624114143d980d45500784000c1403403050002c02040000303008000071f011060070742c0c0c00040c546008802482c0742c60004004204d15910607104c640410001050088a049040000f42c1c16a0403202d000084400b03a0000904180e0380200700c070004181c070754002444144100140e42c514400e0020554404a0207030212030000c216403651b0380203a003400804900c1c80414000c26000c2a80403074024501040401d9034401130300080c000b21801d000d0041624042441d040011802e8075429000580d1900208108660091051071501c18000c06000c1040f040c0b1103040722904208461048540074402d000e81003400390 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 502721591 1250 502720341 502720343
    0xf0a03030e0f040e0d171909061506080f2202041a1f140c0c1c020a090203060405070e0609010318080f04080d02031602010e030a0f0b060a0909020a031b03 68
    0x81d183c2080b0b407600000c0011140f110085d1030301c5a0f00c2d00300120416841400003140c041c1101204038140003882c40141d40f0210300307a80110800201810100c0141c51f05c03001c45c0e405800003500d11801d0042d500c28100c10f254228410070b0545843c110340c840088800160560040d224580d220342d400c4103034138039070b10120b1030110041c01c240c400040040e00344007400243c1d980e000018900c014820f00d40040a04540041100d10002c1130640c25480c1040210f028208214101d902000c10200040e100e2101c2e04001d044030340d00260710303880d081d000d010851f00700410b51810004640c04001044d00d46004403404e07d103081c60042128514015102c0071148101c9005094030710010f2503909400302c4901a00545506c401580c0c000c1c01030007002c82e9603018030b1a2907000e0010810001c00103601500c03080c08507139006015148410282e803510f001c0002c2031181a130b1054810010803a1620340400440060300354840b0411950307145030007240c07490606001c001c22042ca0359014040c0d582418456400131 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 502722841 1250 502721591 502721599
    0x1090f29090d14030f010308070203032104060c211505030312040309120803070309110603100905060118120c030f060903230a081b07060212060f0a03030e0f 69
    0x142044814141d40c2c0510100d0b6a001546800300905400182c00441e80245005d0414602990070768488080340e90050008aa0520041010341403001c003402d4040600f0704198980801c5180a091410a81704450084030030081c1d03000d0300b4604d440103510b02901c000d50310440020000003c000f500c5000c03032160803841c2c1c144800f040c2032070b480c404104501d22482c4281e40707850982e50b07101e244107030f40540008020010f010a00000d03c8540c4664040100b01d07016907001b0040000c010701160310350b0b005035640801c0e10210201840088424002d1039001a82803a2444000e00000c049400000c1540104401c50036240b141506125070320074800050b680001080e60100d00c0b9261803001000448802c030b011845441b51580c15264602c109841c51030712284180c5051003004040b80c1000c0e008012440d0240601d0300701303507200710040107055881c0c032034040143c1e641e1114551100048004003031500c2104014510300d55a00e68403106001c81e40c2c14104007502c449031034001401c05e404c90f2011508 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 502724091 1250 502722841 502722923
    0x519030f1211121f050d03080402031606050c1608191401020f040f0f03080a0e0102010603230609121e04091b170621070509010605120901090f 63
    0x2202c060f06400c0c0c0940701c0618100002007020041480d030340041d1085640c003008175035103140031901500241e5807140c0300400f66074070740c190700700d86508860141c4c025034002040801c00c00c200010810035160103100903021380c0c003102d02d01058580c1c2c4412008480c03004000c00c04580c1c0404c20400402691890304c20000d40d1903030b4807070b201080d041d0050300c00c0c005a5481c942d03000844d07000f800fa103070b4280c0e6000f200c1103140540d600b5040c0c0c0c0403416540500d045658501000012410b030300d40303284107074a254280b602080c0f203100c0094540703040030b081009660020401c42009442e0700b821038000d80624100780d85800070904000060f07000da0ba210426040c2804200c003100206076124015078806525076801d810303100604500d443c0c000300e40080e041094101305a818a840e01082e4070740c4541242219201a2a4000f00340d4140c000e0b0b20020103d00c3c08900c000c2600790304020180e01070030b40d0707008102001c01c0342c442c1c10400f00e00e03000c05030010040c50036464000740c40c003100300e00d00540d00000c0e440c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 502725341 1250 502724091 502724107
    0x90e161202120d1e030c090504091a0a1a0316030605040302100f14092a040605040f02030103030305130503030f180f060a0f060b0403060b03012301030519030f1211 72
    0x1303d001e601d80740e00d00c1d540c18868240b1004030300912580040d03040f50340c0c4800c04582850180402040003038002e594420144900031018000e21300b00e036206030700b000d02c0811b02c0010b052a500160a800c940b2901c01d030020a0401d21002d450a00765007100d801110204058031a401d05a05200040e441d07564514100001080007528a4200d82c000da014050318441640d5a82c2a1030b0310758100013141c10000280e5051800c4a41c444000a52956001800050301e1a0b07108009812241e058416400c0c050700800100107240c0c06101e61980064100c000d43e00310b12141e55602e8481c032000341503841030008800480c41903101130071126140640d45c41110741d803c52200046607992411905500c20b00d0405040042580c002d01031078046402601e1300310b0070301d403d50b0744480c00740c10720300d050a81541d85c5190b2600b08118080340d4020085081000840303a50540c00c129080c004441802d282d042400f00c01d810001c4d46c4000844100b440310710300b090b1400c100740242c002a15404010990031000403401384 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 502726591 1250 502725341 502725347
    0x504080d0c05060c18040f061d0604050a0209030d03020c1618060503010b03030d110d1e0501060c11190812130f080607081b040906090e161202120d 65
    0x400c81e401507045032103070703a0b801601078820f100d118a03030798411803440303010740403070809800c00d501e03d1920000101e80c2e2502c0d010340513400308500c0c010040c2503222030180480780c01c040c41200d801003603d07403040d4030f000141000300780d64582400805040543c0041d1680c840b94051284401840100e80087c1c0300d6a07543c10040d040c0e04848003068215403603d03100003260310381481065108200500558101801800c0303000042030442a0244010000c012158144076035210300f00d070303281440b5803440903503110610100407580142c014100b44800c04041801017000d4481d0b1910440c0116888160540400d061000c851a20391103011a881101000c041074116200076209050f00001540d503401e03521a49004130000b5071050301d2541d040400070504041c85244041d500094010460400306407000c10707810940e015510410b8030b0703541c5501c00d0004c10040c0c042c0789a0040030f06e00030704c08941e056040105415440c81000030400010858408546600700300800f0030f040c00e420f032a44400104000b07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 502727841 1250 502726591 502726607
    0x30f0602030a0b10080106030f0e060c0a1d090114030a2f01140403060b010c0510020409050f0f180c030a121e080c160605040c1403010204051c030504080d 68
    0x11100b19420800c001510742046490300700501c1842c4c4d91003a107a460401c0540060103141d01d003400003034440603840000c0700c042008602075a60b8140b0f4030b584100c0c0b01401003c8900003822450302041d03282c02d850329985c40126960664001c0d00102060540e0000028a07042c00c00000902c1c0b2148014048200c03084e80e61421031040346080a08229072031680112081141c00c0d41c0c0380c40c1c5040c288010300205d451640b12a07040c6206040c04411401161a00c528001d00d030348100ca819a00050148402c10b00c502a09800002610300c0101034205402d00710504640100040000602114990b05000042110003207140d80030f803c1c0c4807000250705120408211129004010466500c3d034071100350725079034014a00019599a6810b0360b01c5903103401d401c03944159108203980d003510036060013242c1a0f205640c09103201d0180060340500d0010117500da2406124191710a0344140800c0003aa15040358208000c1805100e44510b24924038080c1c034036014582105210380701d03036070380158626009008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 502729091 1250 502727841 502727851
    0x3241008040203070512150402120303010f030c06030c0507020d050c150408060708041a0402061c0b0307090606050d20070f03080a020313300306031e02010905010810030f060203 78
    0x83c0e03004640c03541300380401c140d070902242c0c1d01c6c1c5e8801c020039a0400303079000e441c1e038019100600e191600031007040e449265030800e03001802408c0c0d103080c040040010190001d0020580b070305042c0300d0240d198002a00b40e000b0100041d01a00d0780e54124010000c040c065a0701c2e0326002401c0c2c10b0b4000090490700100c3d0058062590700707100e0b50300824900d901071000d00d441281d02a0b0101142c4501d00c44215071800d019100302c0c0c100c2400c0c043c56455090720200c461904000c4400001c0c810411400c2500d020590752045950518290702805141d501c10b0845a81450f851004551b4240755230300011441042f0254210342030002c07410404004400300d50341c0d905406642c513075010b80caa46145904900c0152001e4001284044003180041c01021540d102408451003c030300d00d1084403900c104400c1d11240e8900000e41d61041441004100c041e03100e80600e000e11020410700c0f40350700190110f46207011381d0707050107d8a00000c80c00101442c081001c1c41e8483d00340b401e16042458414040e4006442e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 502730341 1250 502729091 502729093
    0x30040b031e131a0103020f100c1a04050115081b0607061107150209060405010f030b040e070f0b040312030e030d09060b01110a051e0f010e150702030f03241008040203 73
    0xd0580d0f803034802480c0c0c181a02c2d0024001425140d4010130001c40010403013a07101840220400a800b1800c1c0340450b240302c000180b0108414a010b14006084170100d151800069081510170b101c80c110018024000c11864401c22200a400c00005070035400b0390700004140c141803007009401c4031584d0010b004840e109618107a00706038400b100700164016040c80c250850414042006158032606403c15038031820700740014001507110214003a181003846441070b83d880000300700528980c00d8690304c02010040c0c0c0d018107082c110303030347c41c1e0344512410130030801c1544401c20503030440c0040c400c540e00310480c998100a00105483d0443c0540704030340c8804c0c041140c0c54210b8035002c0303010a0b203403d0075034004050010361051000c070710f240d0011290242d54910458402024600092040c3c070700095a103001071940310345007041c00c0c1341014020116011500300b4001010030b4029070069940004030380b0312003c95410807083da000c0601c102c00c0500e900482e0340304807962842d04044c4803405180264 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 502731591 1250 502730341 502730363
    0x7020c0402391603080a030209040f1a0108061005030103021513090e060a060503060601030c11011a0f0f0312030606071a070210020306030703080705070e0930040b031e13 75
    0x1400f420304070411884040c124280c200a1700c80d1051184d4001d104004000b40001f6a610703400e0030301c80c02c890105c0008440400d268021100c1580c011408a602540c1110f14031400925803000818501042c480280124203c4803d550403088180540b010004218203600c18a07541c0c1000c038020f000340c42d00b0900035014500108100700c142e40502d41c2600c102800805107602c40000460044c4518007d520400000382c806000440080c042c001c0d200001d1401a03000c2d0110300d04214010900562803440341d08480f1141000d0303280410090612108901803640700e030345a10103d1070b140308201e401098491074150307104080c168200705c03038013070f040300c1c1c3c215003491520b034111030201e2005030740075541584200b4080002079031a000030081c1e20300ca03200b5030b59078aa0300c030780d00c01c2200404e48242c16250840304110074100c01001c0ca590040b480f9003800e10350b13117034508000c100074030a600450310081000400180042c0003c004980711085081c8145100d140040c3ea80030010703281803003120310300120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 502732841 1250 502731591 502731613
    0x60904020c0f0313060e030d05252a050603130803130501061d070903150b0f060d060e100f060e030109120809210d0b01090312030218010807020c040239 67
    0x16141e12000c600c9e1141454107100300003c00c004100001c8403028171444402d1480000c50200e00301b003800e0451226500702244841d40381150000d40d0700054081c41c018402c10032010068440e088072550002ca4a5039039448410001007006a00d40340501250300b00b5400207007160460f0044202038070f01144410803500c1c1d00804540400052002074250807440d103010641c440198007119004a0007440d40150b16030b05008100c85030030428100707040340d035159000c1001d046c8214109501007540d103011810141040e504001c404e4a900aa41c01c00049911500440c3c07001d50048404c41e030803942c90440401100001000ca6104807511819030280003520300305000540c110421800c0c0807100242404001e03028a0300402107000501c2c10007200307600000c08101d810540c030400b04290754015940d603841c013506122154070384c0c02040c1001850b0080001c040e50100745012101c4044402698132601030419001a540a4101d40000201500540c2540c403c0b5440c01d1101c1c84000309030b032303000d100f5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 502734091 1250 502732841 502732843
    0xc100501050f01020c0411090409060b040608030f0f0a05070515010501020d0318140304170d09060e0d11030c030f03070b0906090a141203090d0e0301020405060904020c0f0313060e03 80
    0x380401e258051780c0302030480304040c500398104685203000c200855007000c04010024042d1502650103039500c50340d46a40ca5401e0610380100300c0648180b0004624140b1071400c540f0030b5214040c00d881035168081540b55105100c0e80450764030a40100803515403040807007900c40c10580a20030503025200e8042d82c01c2d1011701902a14881814020b0303002410070395915241e007980c1041c007650011740410000070403002d00034403160351070240310b030000c010b0622110b40280001c802c0350443c01c10300111000c60030455641c070003407080355540880810740303180c9800c01003032405c2e48641405078103003c0c60b443e040d5549000000382c0b10050003000c4150403522200652070325220b0a030391004e195041b401010001c20310a0001c2c984000c042d1040f2070101031185201c164a40054405170740a4100f07400790040b090384030048001e4030400301c000310310303241c43e2000143c070901c83d660f00c031b9000360b4010441640f08901401008d081c03142c0c02d0241c9075145041c04400490355143e02905001c1602c51510b803615080c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 502735341 1250 502734091 502734109
    0x30a0f030513142d12250f0602180a05060c0a080313050a030c03020615030714030c03060406290d060f180c090606030203040807080702150c10050105 66
    0x640d003007254a91100d5884181810b0185002400c00d131107130412259405928503074680c85902002000c415403070071103002ea800d048894104869244052040800e00b5540c0101c3c0b4101c4d5894400c4402c2c101b6040c42d2484401c14a12005400184042000c0e8000305107110140108442203c001090380c1c2c4500400c4064040d0045088950348003038100c5000402900080d034015081c0c0c5040d81e0094620740d102d52903c41c4941040300016003248155081640401109400000594180b8507032103840f03004c6652016988100d4040f41c400e440c038006291024400082851800f40940c1c401e481d00d03090040c0942940700021001315030f5070000611540d803d4142100c1e8a800510300703c8100300a40b03c0b8400b8007951040f1417581641c0e10010120220080e540180440c0714240c60301166152401c10011100d41b5072041080c03600410402002902c0074044926065214920a465116600104049042c4140c41214145001030b940070400400a60f100403400718a60512480c0e0b282d07400c0c402c00c0304c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 502736591 1250 502735341 502735351
    0xd030204081b0109030b100311010e22240611060c09150f160302060702070b0d0509010b09010305010b10050412020d0203010e030708030604050c040513020309030f0408030a0f0305 79
    0x20b000071200d509001192188403040c400149880404152079032180d4511500588500d42810100c903010001c000150000b10b0071203070242000f4465031940da020400300002d0106120180f120b51001622260656019400c0010300742c40c0d00c0c10171588100d003554003175602d000c6c490100340498555401d07182d0029210307110341a00381d000381c10142c08605003c1a2822050360314845a000e01c0b011010004003c06403c0311140603411141c08001070801900b00b04e4054600340031504049018801a1506800c80301c1a07801c0d454005020366405440c84e004200d00008903500203000d40000040c80415040040a030b242110a114a45500202030700c4c0c274400e61003405c10402c50103907800c000d407a100a40504040c005400450011110b12500c1c1c20f56000d01c400315001a00442403203428241752180507401410215124901418580000c180b940c118000d2000250000002805902c062007561090840e0310301554980c0d8440d141151241c01c44401040000c0c0d4071f480300c450f0743e4880c1c0102800780e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 502737841 1250 502736591 502736593
    0x71e08070308180a120503032509030803060619020a0501060902030f19090c0609030c1401170a060302031203010603050601030510050d080f1603090e06130e0c1302030601020d03020408 81
    0x814820a450802800b0aa5a2a5204d0755115000030f1030400000c0d4501c1c51840391010355500d282100e4000c0c0d400100280c180b06210000d6003040e00d00340c100c0e4800c0203403608840e009841303070794140c0090820710510b46903c98a1203111141003205030005540c8194511904c0280807039610344860800300d0008444400000e81500003003101d42580e04010105001034041c04101d02d281910780308141003543e07001d940000d6a4480030414040b040103c1d03030142011503060701c0801044c00c0003c22024444004dd0103004094010990158440d40070f04019907001d02035921000301d007000f41c803042d0001d20400c0c01083c1014002101580700e840b9481c4165160400d15500e80e05243c10311814401c0200122084281080001f1a40c244840a0564514081d100c000c00e00c290f858001c0100d25182e000a1603500001d0501c0102d603140300c1c0d4201120450b400018001c407406045600e06101d1a025940204034035290b200d074030b0036a400440c41600280c0171a8252010382908030300f2171245200c2d00b0b0407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 502739091 1250 502737841 502737847
    0x60606220905340819060e06040c090e010306150f06021b100f1101020904050126031206060d0f05040614100509011401020705030f0a060c110309010c060e071e08070308 74
    0x21213008551041d006504220204c41e85c02e02c0b004140100d8000e90442031861009404204880c6001c9c05924940550340c58203020711071608200108418040c040184a2500e80000c412005800303441318004254100e22121a580c1c0c43d40d01030344800812100e02d10340c0398110940100d82c2044c48404140a0059403520500f000408089440110200424a45540821104a00d035a0381c1c0078890190440c04c010402070860720030f141190501c078204201c030301e400500102060044425075203902440558405903100b030f00103000310081074041284443c0340e141c002400140211507000140200000003004003a0f11591208812070085110381c0ba44000c0e207600500541d42010452408948103004a45280c0d48440000c0d080c840701030280d4000750301044c0d00303009000c43c1d406009200c0209050200803d07184403804c070345900c10a40e0280c180500682e14804214180d0300c51404502800266182c8a8840411104041e00d071454181148904031000c550303001c0100701c650840740d101e40c0c420300d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 502740341 1250 502739091 502739191
    0x109060b04060c03120b03010e1c080105030601090b010e0402160605090f030706020c0a0c121a071b03090e18101107030f0203040803041d13020102060606220905 71
    0x1405d20b00c00154680744640300c070407180e03840d242400303070001c00c8004202406080079005195240b6040d000801c0040000a030010046500c0c041041c5055400c1d066020038016600401030b5001440060007940041c0700148080c0198a079000c40e400d49407141074280043c1d120725094a81d94041e6a0034240c842d0020800d400018407154020a0214040400d81d85803891940f43c104000a2540c09182d01000c0c0107850410040e080340c1c03403a10384400c00041c800d141400b210050803040424560000c1145e185400c10500d40a120014000d00d048032482030745290000205030300112045004100d841007444e00035036010240209955202c1c400306590810714103440449403076040b01640c3c030541c00200004214203005100420140c449070302c02000f0003142e440809030343c003001080746015000c03681c2c031000183e0303001c11000d8201008070340c1d680c0c58240030b0b002901c810b081802c001600b0340300c0400c0010b40f5200d0f40c102c24460501640650300310850205160902c00303100c03003868101450b000d6049 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 502741591 1250 502740341 502740347
    0xc21030114040603150b010f080c3c09130b0916050c15181507050c0717060132012303040b010f06030606020304051002010b03030409050109060b04060c03 68
    0x89690800420208001350b0326203c1c0c5002c80f035800150172085446110100e840d58110f0341c02c20b02c0c0314480c9010843c83c5401d18802e070306e0b4011514544440310490a4030072004420008044150404003504003c0a03c038100400c03080d8880043c20b80541c1262000380d42c01d078524400e90101134406031900c00d071584c0e2105250102da05860034102441130500c18004851307004c000403a80c0010000711070030740303041130140c1d101c103040402e89a00007030703000c1d62403d40014800e07841c1c141c01070316a060082e00c9541c02e02081d402e0a895400c0600e51b1403d10010b14030410340000c01c2412100380200c642c101040865041f0204ca152400c444054059510480207035489024015081071105242d20b03c0d00c08640b04002481e4400c0c1d4060342e80d03585800c0144445015000c940c0000c0815060403c011450280e02035102d0040d841000e125004a03010410258004e42000141020040590350346c1c41e11000081c005000a0082280a0b440e141020400062031401c4a003680c105480d811b030a000255021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 502742841 1250 502741591 502741619
    0xc061104051e03030708180a0f06050904202205010f050703050313060e06091005090a0f0f02040e0303090601143006160e1c03050705031309020c210301 67
    0x2075501803008200c1c00380032030095800741c04044000301c0c05614410745103080140c031288c0740e0821400d82d01302a2040241541200c100d8240c0501035401107507a44000350f40c178640320030045c01400030034400501c198801e01400307942d041c9541d400301c514070659181d0004580480e803d00c202800f00c0d40420144010038003842c09517a0188459407904213a02d600d5a030403065038a100300141d540d502c21401c0c00404482401009602c1105100801c0f45152094240307644030346004016000018080c0f4810511202c0400010143d030050300511050340031081c0190b50341e00840382084180038090022540030410800c601e0b07581c20007040b8642850b20b102c203180b80c5039601d41060500c0f042c8507070807218050003804000e125001004521034088042c0e00050011001452210700c81c1c1040c002000001c0840c1a42e80305003509440c0060312a02c1610748145140b20308460401c01d17051103130300041c0c407c010350024840c3c0d54000b403c2da45a4561142c3c0c0340ca070b1406c0078060170820101840140f12031102d41d481 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 502744091 1250 502742841 502742899
    0xa0606051611060a0c0b0f060a1406040305030f0c0d210218040f020a021b100c1a0103110127210609110a0506070f0b0601031b0c06110405 61
    0x281581c0082e80e080000c0381030703220b0103500020035000c0c00900d05105110080c203501c05680a14001c480c60507134000750b1226014051216180214546d0072215218a4155409075901030116591030150030040d40054001c40c003401c1d95403140325017240d4000d11a02c1c100b10064081c0c09a50f403260b0013110500b0103500405842e03603901401151001655a980c040e2805440e442000142e82d03180900b8001e04080004205031a141d00501504c411504d59082c0b02049015502d04600c9950142c80e040000905201d04040c090101e08e002109204060354041d00da00320980b42e10208040507400b826007100170301e48219a00b0084c14041000301c078078000d40d0315980d03401d40c1d8144240a8559400013208c00d0001c1c10303030702c0e080041c1380a5103904200440341c002c1d00007201c440b400c0118941d02c02080001101c001092010107034041405030340207400003c0d9102c4088010303401c15081a034002c019000c000410b407200c0d42882d600d000048416011070b0151070020300b5121600c288000060000600118 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 502745341 1250 502744091 502744103
    0x503070210031e05010312030e0a080307210e100911011808030d0b03060603010920010306050d050307060c09080705013509010b220513140d080a06060516 68
    0x40050848507800f07198146040718100103407550540c2495000c800354041400281441d0007040150705c0e8000440008a6a000b00741c15925912400200c903501c82d00c5580115540940c03814402035481e1f0b07048442c00b298140d00302c03100c2921002e044030075102000009080c200480180081c5940703d1914404000e0041201c2c440d515682c100d42445c662056040c040150355407a4001800d01c0c00340700054010b003085000b44041d0046444042c001805090340b0285000a0054000141d01030f03002000244002002207422226905003113440c0d600007001101d88611302800600a0343c0201101001d44000c040100f000714144001982d001182440e2200000314500bc10814010289020201415072420400c01030070440856820360b2094100d1070320641000407925801c40c1c000c0c00c64148012607440c003090341d4940e81c060744851141100040d2020380c000b6802807405800144640407118a980c5403096507440e403442c00100c030142d001e0080051010490311014441410409404c240901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 502746591 1250 502745341 502745351
    0x20105090f03280c470a05030a141b0d02070507080706090611030306040222030506070e040501031713090606180b0c0706050c010906091a090a050307021003 69
    0x10400508681600039603083c482c0d003e5001c00200480c80c10400300402e942d209418401c40302a46008003103411524069045040c0d148103205101d0035240782e0341c03071240c401241d40e4800c00b021380144685d00807520580c8190500c1c811808004a04201d00d20801c6103540a0045511100e03c08559500034029148155001d00980b000b0035802d11030407005201510041803030707a240a1014207248000e80c009002c0c07141071144040c00300004411070380d2202c022030b00160348820743c2c030303204018200b01030000f0800808040c000c0100302000401500550390703910b400349a4180c482c1008169032090000904014042c52a00303203024500c400341c0222041016a4203a1507211100f542c00c5581aa01c90000500080062100e9110b039071001400340c00c2c1403290f20724101040211581c0c80c10984101c0f0104100001c2240e0202400c0d03010300c11030769000a040c4a20181800c008002270040c20f951140b8034011400300d15681800100c0c0062503510030b0145017000725030307020400d144211684503030038035483e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 502747841 1250 502746591 502746613
    0x1020a0b1b0d0911010f020607360812070c05100504030816020f06071109060111071412030c1b150406030e011a0607230a0c0e090109020105090f03 65
    0x4000500403040c4402c0c40020401c00d1418a007610303513041d011042c107000100f4106540d03a64003203400ea03405a018141903901082d480c6007045050540198890010035990140c1c6e4040c035040c452104035150002120386008250791000340c01d20030850001c2c0b8501e0f514000300f00c9402c2c0a481d40024010b9401e2a03030070582e032078950702d407660b12101d0310302d0701d16806023680411803600c010742d21400314040e12480e04014403a6101145003203000012489000d01c080011072617882420008005d50241c0300761118a0f0b90764050012513501000d2007441203802d40362140c00c030b82d800015121044000c00007040740c8959814642d079140241c50402c0d402c65034020020000e003600c04003c00041910b81e50014040d50080c20f102d00b12424504485a109010030300c0306038564545044d00c904a4015a8401c0013581c2c0c0b8420341c00121001c1c41002d1503000e0720120b8000c0c0040c0524403000c03035000e00e444031201d07685d20a02508079040d50781d009012841c14020402541841d040c410000f0300042c01f00c036021014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 502749091 1250 502747841 502747891
    0x24050105041809140a1b0b0d0f0e010606170f0403020607180332070608060f040e15100605130308180405101d011a070f0f1505130201020a0b 62
    0x10300152904d40c1e0740a11514810081c0044644084074040582c003101c19040140c04030461003460100e6501640360081540d4501c0940c2c044d0400d1b21030000200141a0344e10b1014010b6400440d110125050740748c000b4240388140110544035540c95030140c2003555400505490801c900700d01b24034400508880440001e0300440100b92a0740e400e5080e2900c4444914607419801c90380d5114641504840c1c42004001d411090322a0014000c0b111403005290a1000c05c000304400385601e00f5511480203801c1c0f0746140c404066014490245141e158941c66503005d0300c207880f44071001c1030010a006010008100c2005c09030950f11f4942505291b01202c020028083e0b44058481075516003940c0410000b000715150b6a0400310212071000240358506818051111001c02c40354004020006001342040440707800c229001d980041902c02030222400c050001c040b81010041e0b0143c9081d002c00c241c010032040d04242903605a00030035081c0c09554801040b0718000d004680b803000c13082c91010500755 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 502750341 1250 502749091 502749113
    0x90a050918030d1b0c0507140103291203040f142d030715052a030d091b0b1608190302070203010c0306060909090206160624050105041809 61
    0x3d071222010849215076a4200002d0002080003030030f01825903110000100042007210071102030201e0b000c00e0159240040c1d004d45501d44120040e105d2581c002081802c600030308040030b410554a07800803081d03072200c00b0341d23a00ca280500c0b0103006c82e51008014600c0f0300d001c0d02c5200305018085150b41d100300c420a03a07401164480c0340641050410101003141401c01c1010000c262405600500d0819407034064464440c0c0810366503080c040c110740c8488141c000300c111112800e803404a941e902440c1074600c0040ca8140011500412412038450305182580305031000d1301c5d800b0320100e03c0d00c142003441c036594200303d0008a4038540d050200f4424001150208041900705850150350344031948101800c44841c00b01c0c50007418a01402132044947c00000c0c2c00680b00407100006040e041400040c0c0d2600581012881582114900340c042102c40d070030540d448250300c01507e25055101c2046103103100c603030045a0000d1000e0108004400c500074841c52b8251058000080d40c50041d203e18003028 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 502751591 1250 502750341 502750357
    0xc060309060f0a0c140c01060305060f040318030819031508031b030315150c030307030b09060a0509072a0501290604090b01051308011d03090a05091803 67
    0x3400c09020007640c02c803080c0708254010b18440080002400c00c0d100980803141c001c400110103240403502101c052825030003000690b812108458951802c80403401c0922403c07a4203c00003103502c0c203040310140c000c1850005a0380c0c0080741c14101440840c50305081c4104840c1e06041548032620107075003002140b142400340100201465403440900000b00300c3d09285a00d05030b00350310800400950301c081483c85241c9000c03c850540344008441803a8005000b06002038000340000028015081e4255208002c2c100f0305070303003450480e5110302c1085030007403003442001e4004c800364001510682c41340041500714206020b0146115440f80041582200c100302c04840680d0358130b1840300b0300d0890300407091103803170300c90044007040c03e07540e0105100b030150303104110481d42c40341d860300e50b40d0380134500b0382c0d80245203500802203061b69081d2090203414000da007203640c420656144c03181d8440100c2100c00088000e07110b803101a243c0010321000c0c1c88000c3c04c4282e400141e00c0311449010090000305081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 502752841 1250 502751591 502751593
    0xe0a0204050c1201060527030c010e03031b06070e090702071403071a03040b06091603110c010f0f18030c0f050703020904080c07050603280605060a0507050d0801081e0c060309 77
    0x580c110340c20005941d40d47c8601d044408220f002100c038150380006401300445000e184c4094441a4103001c40c1c0b55020340e00140074506400049803492080014145214031229541c1511500b034101c00d00120070000c1d907201c2d005821a05007132240c029440911246aa40a0100d600c49075981c0c40b24550301503070841011000000205020603c214907100981100048031118035030b00709a541070f00c0c81d00100d0015402c0c1601c8a000c02e080d450080240c90070781d40c0e001c0083c0f2100c91040303816802060024484206a80340ca17501c104c4000781004195002545900c82041d20b581d55242e0f51000400b0380c0040b2402d1195040201c0162940090781d03001d80e11400315907868000008591742800140c1e044035000d4001070040140c000195140c4101000000182c0286000912051006004070381c0002d81c1004c0c00003401455254080024500c150080d01600c082c60010742044a80034020321071000c16602803146482e8521822481000311003107242101c0441c01c41001250741e40c2c00486145150b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 502754091 1250 502752841 502752847
    0x5010306062c040602160807051b1c06061203080906060102060f070813050706260c0909190f050403122a020a02090408040510030e0a0204050c12010605 67
    0x411090740a00405002080341d48004000d8116400c0002c401401c0b002d1041254000820103011499048a0b6038000304011090b054903542440009984801c60407075042c4070750a500040c0e0301380c00e107460710b41600007002642c654080314140f42d8890030807070099130041d607181d00001e5608085101c03480450310a880740c41c01c5161006106044c001c0c010445d9066400c00320810400600800400741c2c0080d003428460280e07141c10044245e540b00401c3c0040007803040203000f281154202e06200c06c410705000e54402c040c2400c203030a480e082010b55802c80710007000d2100328551314001c2213960b032003509110000100f1000303001001c1511000581c0364409590780f400e1100307050b48000f2000b275a007400d03042808040507041c25803441300c0b43c03c803000c0c1d8155212a03000071400d20a008502100342c0040c08180c0c01c4c00d003070406605950180c8a503921640d4009040b00d101400f82c061010140801c0002d8070300030109400341b001901c0000c010340c0d151801000124829080340204501a1100da900c0e43d413 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 502755341 1250 502754091 502754093
    0x1c120e0606010f0809100906020928081906091401051f0605130b0f04170607030b090f041101030e100c120911060a05070c12290723040306050103 64
    0x4456012400e41c200f001e13039810001d450400041c046608841c00100041c1007905c0d00b44030009010714a90360394464000103580031075511200c0f00c00701a10226480300d055030380d2440c0180d560058100c079801d801000007519004500c01d0350200d0066806410103440d0101c20007446c0d421a1001c03610b8080b400b07d0b00300512304405421008001522041c00c05528040007407603a84254610f80c4202804451b001404907842000c1d981910000c024130b090541c5000100035446490303500803101300c00080e00c0c0460b04082881c00e0841240209080000100386031941e884005a0a00d2964040d052640b100c403101c400304020001d90911050005000074084440f0380010034550001e100808464204003503000405d000210701030240c102101d480c2c0d80e552014009903268007c66102a02c812980b90000448080141000140a1188541104001d030401c000b03005d2a81416659225882c007a0000b1a0580106d048000180c000d07881201c0c03001010b00c948001d54003036001110b90540b5400104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 502756591 1250 502755341 502755347
    0x9040c03060c17061504050a2d030f03080703092f01090b09040906060e0f101a1603020a0203010f060612020405091614030703020705060f040201021c120e060601 71
    0x71101503510f850f4901c0050001401d502d480302902c01c5200b944800b40000e40c1013071810885c2d0080501500302081c540c1e8410254482400100d4074030000544107150300300b18880051103c1c192940207030000303211101a202240c881c02d00a201c1820b041c2d07290703120340c003259198440162118a08110b110043c40480386a00524003d010013410310032224800d00840014006032404101c098038001046101824404042c1446a200200d00030201080c0542c80e06605400d5104043e100d405c51003c81e600c003114000410860070b4941030480900160245170360b480c903000c40440c001d20407541440e0843e00040c0c04c6409482c034102c00e09076104401c01a5581043e03d80700200b40b03001c011424030b46024041030000e54028040320780710880403035405001c1e001343c40099211120503c950345904d0042000740007981304500960780ca1017510000382101c00200749541c032440d4103034003030702240071800540c2c1c40d0b55402c2200340c810b200b0b0818892070a120140f2846640000030b400030071141c03e081c4009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 502757841 1250 502756591 502756601
    0xc300f050c0a060f050a030b10020f12030c030402040509030702130609060806010302031b19081b0603040f0b1806040b040209010b030c03010e1914180706080c0f040509040c0306 78
    0x590242c4480c0e5010020990844091100c0700181d0818a58a400704c0c40c00324000d1010042d86684410620b00580d00103500088654501070000d08171a40c1201d1881d0000280c0030860380e01b60711100410005005081030b4111076040800300c0c0803241411040c3c0e00255622071000e08014070940e5179003081104203001c0c003c0703000619840c00503052070350454000c6511205080c1d04004c0d1103089018880b00c070b480c7d04210741850b0030122000c1c0841c544440d0042d440c0c0c4241350030408000b040340c6804425107401e90840f40282e40c0700001e4610144555034440107820014442c0b24443c2d1440e50007a180102400890721661103599080e080d031030b0038410000300d500e06810100040c0d0040c02006031052800044a05407903140ba0544401c0d80c0f4240603442001403c010311555074100a40302c0c00507603035003601074007802001d6402d034603400c004120030795154401c0c0306d43d4000980100c0403070f0221041100409140e414440b105c6d00d000e840701c010a89245041d501210305954403a820000e002892041c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 502759091 1250 502757841 502757863
    0x32406060403021503100302100f020d080c0a0c0302032217060603030a031a040204030b07110f0c0d02061908070210020909010302010e0102070315270c300f05 70
    0x115070801d030864020a5503010320700e83d800b525510010106d407a9841e80710044008580c020f0408020011031031000344065004101d51007d40304041c4c000d148603002e0704426102c6d1015042103420103005c184201d0380e5101c00c1c0415425070004000050809001d4494031065440217940300740501e00d0008070700041c2c0c51203c04d51100e0340000c0140650b680e800320072a8064001c1d40b401055903801a0140003050005071412035001d880080e00200b003001481150340304607071039241d01e080d07090029004c9440f10008400591035421060304050035152000342c1c3d103070040c00607007132a04007102904450790b448052025440801c0d60300d02044042c0e03078100201c1d50195a0000154141210342020960b0b820040c00000d05010190600f800564804c2001e0001150000c000140b80400e90355850014242100f90000c11208502c20800100d95072107007400c00ad078072020145e2164500003900320a001c00400b941c00092003c8000c044441000c00c1c410800e41c0542c0802e110842d40c2c0c035002e0302d443c0000c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 502760341 1250 502759091 502759099
    0x18091d070e0103170a0e0306042102060105032113031406010b090d02010e040e0d0f0e180c09010909113a02090a0806010f06140313150b032406 63
    0x43c4001002e60381c502d680e031341e00a541c2c0d6460302d0080c0c0040c0e410201d440d0041c2d80511410040106010300e070707241480e001c1d4201d810108581d040140032a15403109010304c6030036604c07243e070040c02c40c0300491075a01e1441c102d60146061043c00b81c01d034072008800e5032003034032003501c11981c0710380d07100e070610004e40180140040280380031031003004203015610215001e41400101c4142041544494209074040c0800205441c200d40340900003401d09a60050682f0010707a544080107498104106505030f0600042c480516079520306521502c680e2200100904000c8040070010311104d442c042d01d031075907445880140c0c860b419540b42094903a645110ba00740d4a000000f0b111195010702d0240b80c030140200d03000360340d0320907031008525030814030f9001021328800e0b24000601442254505000c0e5034041d41c404900440021902c081c90101344d030a00c10864140d0908800651000061803a070a00e504020544415200020782443c038200c0702202a540760040790308145c11642000356010b00212 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 502761591 1250 502760341 502760369
    0x50303040f030b100e1305010b01020115090504020612040501050f250c14030a0302090f010e0a0b0904060b030c0a02010b010f020a08070503090405042d0b040318091d07 74
    0x12a08a0003003542d1201801034600d01000c0f40d8109240500100588003010743c114031810b00340e05441250400401c241c45552800300500c4140d031040c00b0341c0c017000c2c07440c80e121545181001004001007401410483c2e2040080000300c0200c0c1000c804075104500031400000c85150551000881c440010500c0c20172030303070350340030b1440f01008003000141c480e81c94a8000d0140c01c6511f085600c0180030600e04d070711440007151098441e41d050b002030043c2442039907100b43c0004030b6001510b40c3e400107447e40341d0207400700c502400003c54030009005040c500800201c2e52642e038400400703466006a0300f0410401000484010b1941c0900502075046030a103001082456982802512245602030041008900184101c1130010820546030440c00040c0100024181441d01085200c50300c2506580d00e00c0e40a0700c10760309001280b4808560f07402c000140000d5503641d400301c0b000c01c021821340d50020928900410085101c4c41003d00620750080340440020180250524100c400e034814024040c0c1d403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 502762841 1250 502761591 502761599
    0x405031510120320121602031e1c05130306060501020f1c0507061512020a0b040302010c0f1a2e08030d0903171f050108060108220b1f05030304 63
    0x540031141c1540480d84030a4585030600c0c0050400402c5d4812002010010820303e0110102c21003400c003440c0308500b10360104c00501c04a107211618074046488541055001038400758003c2215020f441c05490410310b40206010a4007103414941c005840c1e8a51b24074041c01156010032100d12a407150000511480e170060501c1c115440340c8000307103010000042618401c012554020403c40720820451118031510385003003501c1079202c520700f40d20520f0804000601c1c40300030b00440741900d03011394451161240a4440844804150004890402c10010038400000142e0720040c001c04000400d200080c032491003201c02c111203220b06060340f0318001c0e02080410300000841d41440100d03000460300071110304051701e4060444081c0d000c0b6035003d4003041404462146c5460140010400d1215000d0f00c0340011184818100e0391280899411401b2498050911074940c110944005180d4903803841551400c1d04000700b0346a5201010118400392503260080d00c85501501068004504042c50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 502764091 1250 502762841 502762847
    0x9060c030f090b06040b030307022701060c0c03030309080909090a41071d040201030f0605010206071101020c01060e040b0105010c08120405010f0e03090307090b2404050315101203 79
    0x41c00d44e5108a0b40e0300ca84009684060040e02c09a94005201c3c03a076001e410322420319150121384016050115440021070f10340d0003440c01c8140d1541151143d10032034110b640c03d0340104407004041e5000e42c010b00070008995901101c0e140710b002850050800b50100d4503141d0301d13050f188007101100000e54501c110503040880c41c182d5450000342590903104803e0720040b410a004d0f80c200f11115503081d44010303200601c2482c118080c41c403c2e80c04000352411840180c044800754000c19006030000d401140c42030744a6243e291401c070310350000501d80f10351200c1c011b00312156580036426807040d1400308401e210020341510300401081c00c1509403103110381e4424646e8401c86074202d0300300d01c0c1c0d00d01040920000b503204803102c0c4c0960714108140c103450161f859a80c2c00c950942c0d03110f44108200821190560301602034004000390008541d4507240070300350701d200d403c2010401800c4003480002050b07542007202c0c034a601050814910b42e4184044c41000f5484c1580240d000ba4409070006000a54 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 502765341 1250 502764091 502764113
    0xf220611010c03180b041403130e0a050c0d020a02120c0a021801050d0f0303061d16030c08060607060f02180a172d0d0201050115082a0d09060c030f09 66
    0x1038441c00105c2641c0d644d04d0030f806203052122541283d0302c004500c03102807074480020b82098441216091100350303070328880417003030b43c204071406512410184035075092240a0b402901c084075450041e100500c03040700c0300144541141b01452007540c482d0911806500b0300581410711420b9102c545026503041c00040307180440c601c1001402540c46611000a0510039402032018140d058400005070b200c071484c0c00f0a49200366080c01081f501401580700c00c901a2164031403030b02491311480801c0d40c03801300308030303861301322500035980c843c0c490701001c3c001a424402410b1403a591a21000103206490a2140d003d459400c07000e9140034407041c3d810200070005580b120500420180d030b401c003c1071f040310a003107002400c0989143c483c85c0c1c480002a601908600c0c10703201c074855035070319104205d01300301e4011000340c1e010384020b500d80c455071601d4041c0701a1065100c481c140c0f018a000c1084d00101c080304d00201d01507503580c4d070710400e410249515004e10440000d0081c4148092401915043c5c1d85c4c0d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 502766591 1250 502765341 502765343
    0x2030c010e060d020408010204150e030c01052b0e0d020303010311060d1107051e07050105040b030705120103050c1302070308130c050303160b09030f0f220611010c0318 74
    0x1c5401148002a0707070b101c4003155400626448155144e0356070340007040c003035003050081400e0385081d010003100c02840340a5000d10400001d004007024040e4000541da1303580b000107042203030300090a00640700305032003040710f0510880720780010789203840da480d150a16980d07521b1002150020401080490045000d0032a054404c80e4a50350383d04c0c410815200070901442e10161107040441d99900b0b0103808503c440a10b500c0a400b0b100c1c2c3c58131040c1e056185d041d5400b455010803000e000c1405212030507405141d0100c4503003803040c94040081ca03182800d4500b41d0045a8690051010351402c0c10224810750501071094400d505111056801504030040284003c1000c05100840028801103002030300040102a081da0b0340c0303012252071582e115108030b405481c400326031740c042410b1007000021035030041f038141d0b0050300309030405800035030750790081081c1d035001c0b00e003001599a021002402d00c401407610741c69910800e08081c890307509440e5000b442d81d050500c1e2200d100000c5a20720f0400a0403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 502767841 1250 502766591 502766597
    0xe0606030115050d020d06030f0606090204060906082710150b0301090c12110c120c0a080717040f090c03150501051e0d0207140d0516020f1e0f04020702030c01 70
    0x48002d843c44d540280145000d100025040c00800000d01c80204d40c3c0c0041036000e40c105100b550f48500c4994140c0c4620b11850001440002041000074401c6076010742000c2e81008040c100c40c28401e00402890030410440150b0300a007550013602c0b0402e1103210482c1a60001608100b4945014607a49000520656164a80300c00180310814031403000f00c1e030a660340c0e180070040e560703080c14910b081e500030551841c40c900c43e00d01c0f60b132a010740201c01e8800800c601130041090740e116070740f00b1416030440310084071108030103085040b0340501d0720003a01c0501070240341d10300c81d14078140390102502d2603c140641850716100340f5184610104103c10203896003803c0281c2e4074144200c0c4010804040e0780140500d000c0030440a490361301c0c1e9001001d0b641d0280c00095000e441c01c24003907841e60344400007103021900c10030010640680c1c2c14202c90400707000400684c0d5810250300410000d032100801d119940f0480e07901c024007442e05d14031a01c03c2c00401d0364114186034980e0701003aa0b40c43ca410556042c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 502769091 1250 502767841 502767847
    0x8091c1e2301060611064606081203060303220b03070f0306120f20040204030609020f09010b120406060b030702060f010602030a0207090b120a0b06030105131505041b08070e060603011505 82
    0x8074020b52090b404410094059010a0407c1c2d28075a006000c5405100143c0c01640c001e010928100829240130b03074401006140380a070040b408055800800401c64607804100300c2c00108582600045e500c54a0316482c1e400243c500d00c0402030495106400200058400c1414840404c609000095a90740d000c880340c02c501101d000c8408220511400c45684140001004820041280c0007001c52500c259800c0494150080401c000150b003401840307030020051000300451400c550107a42c0150003a02e002034030a84864040e04c0580c81260a440035034000030a00c001c0072410009940100001c0c4060741c204088550020340796041c501c1025809038031182060001d41e51001188001d24000e01114000d00c2c445c138168000d0001141c65500c65407030000002c018600d1500780f0230840d0381c4a800800c400c4e002e071028000511001d01b0a42c0e400e040314204182d03030740b50240b074940a0f1160b10010310320607103440c4150340358810050038140640030501c010040751603110480783e8000e4480c107000351 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 502770341 1250 502769091 502769161
    0x90303020c0a0302030715020a120225140d030c0e06071109010e09060c030408120a140c0408100908090108150d08091c1e230106061106 60
    0x4040c1c000d00e10450001e0054003040010160004020010a48590a00420a08910000b00481c001d43d010180070912294070162841c40507030003001c0041241400325200900000d000006111740202101c105103000d42c1410794000800031030b05100c0742c505e424010000c1c0400000d01c80381002a00c140228400300f032207410000d00305406824840081c010300070540c0d44114402d00050140c50a1001c1d00900c0c002c80c2e02000f8200c2240e2007590403611051038600d82801050300303208010b2451020960701c1c0010683d0b10001e031003890082000070b03641501c4604000c4400c1c02d00e0004407866082500e4085a000014141c0083d40d0801400b4285204160f40304d5154520390340c2d441443c00c2e8030009415108080080440107001000401da40c0501c0f41b8003124201060300101ca10003800283d061a580b00d401c000244030b40151901c101a441e05040111191005a0f400300400b00350300d03511b848007802119842b16069045284030700003040c6a013054043d0318403006580020401c40c24020120306 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 502771591 1250 502770341 502770347
    0x105070525450e030d150608060a060c080c0706050d0f1812020703053c1b03211206010504030b0f15061b060604090804090c02120301120b01051806040903 68
    0xf55095001000da81d40d5511040c1590300600700c114a10154030006c1c540403400c2803040240521400c00074100740e500034207001c0203071040c0221600803600c40e0010010301000e044180311700001000107403100b070b8403100e0000884094174051059202c00b03d01c0c02c9440514074815146101642c2d400a1081401c12581c070812403c0c078880350000381161144101c42d0111205000c5c224030016110a8044100c920102122038140c14560100180e80c0c001c1100c110084100c0c0000d10511400400701e0b4034080004d40008050100c1042c000703048c01e004500b10301c02e849034612b0640d1150f000d207481464503084d540d9044001e44060310001900f444040010240e040c02440d400085000030101078036544110080103061752280050304203801a070001c1402c0d42004e0060260560703109503410304241c10f140c560001855155102070841c4038040c046a50501460011800303400001d2001c000d4182a00f4003a540c0310040e405035001c1c02440404035102c80181e500e080d0040c2c000ca6020891080904040b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 502772841 1250 502771591 502771601
    0xc141c090516180603230106210b090106080a24050408181504030201030e0c06030106022a10050a140406021b10080402010507052545 59
    0x202075115241180181d038161611180450300110005080012034030a00d200384c4a461000030100380255401055091070484050f280800d00b00c000142e40381d994002c00c900310343e081803000030130403440b0b81b5100b0302c030b540b000080d407000414000340011481c1c0020160b598620201c0501481900000500064001611061101e9248000b440a81414244207115074130000b030103541c030000d00087d000ea60911025081111138250451801c051450700190701a0041590980d840e028803a544109503440402444c00303000291f0040ca10545403c410109054481020140b0700703c1c6004600c00c0f03a82d0300510701034031074881e00c1c0064036040c3c0548191945403000038000f14040c00490042501640050151040c40c40c4070790f002c0018022005100c0d4240c2031200a00001c1c030103000117805075004e02d00400070240b00e842154a100107900c41c240c0704091500c5d200100c800700340d80400c0a800c0d840282d61005ca0620544088481c5550300c903000c905404003011403011886400380008201130f400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 502774091 1250 502772841 502772843
    0x60c070f0b0a020c040c050904090206070203010e300a030f0b0a030303052e030b1803030108150105060324010309020411040504140919110d03020607030c141c09 71
    0x41000c5549850045a0320303040500c0002c01840389505403d20343c5813a016541c5400c0d10780c1ca60520b0404031105200252040c45401d0360060303410008d80c801a1024868010568180780140c840ca110305012014400c030700b08508224040c1d0345402100084803402104d042c1006c0b420001828140d07105900064184000e00c01da100040001c00001e01d90107070402446030350381d0328010700c111102e03051a00340401910000d1136a03101200c1c040c00000c1c904004542c10102030390b61114541c054154003881e650098000c1100343d082200b41128080c0689900d03405880700300c80a07421480c054070030301502c8000c44040d122510174440391003041d9002f90300410f40c043d005482403107030841c082e007d82280e50051261600a0389408401052522030742c42980c05056003d024180d0341100c9042d50450543d003102c15107800340c2d2400310b01030320354407020030718580317032181e00900164940304001904640c1261601014403c210b0011900032242078216022043c58000405420071288c03100c400804c42428 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 502775341 1250 502774091 502774109
    0x111210060503060c0c0d030b0a031a1911040504050405010b06131508241c0b092506030207030504090c02010b2119052401090b01021908070213062709030806060c07 72
    0x51129400bd0700760701003030310170303815501e200d44244603d00c400710031102441c0700e81519120502081c4418502600000d03001030007a000172039407a00c1000000c20303541c0165050b0214141c0b1140070844a884030030790001c4d0341464201984189400640c040e00485140782d25403052016118070b10460b9518105001404000c600c2c09002e21a04c0c076000b01c0003402900ca0400354441c81d640c1028455513007140800782e4500904c1c451030b1520344101a0080e4000b03010880034070a040c48040f034600a98803400150340c50307a60000c2180700941003030101c600c036020007045941911914841d4581d80025180700c1b120441405a0301c0501581441c0341003440a2003100c915a41460b0314110311046403000c2416941c0401040200704071072030040ea0741e108a80103048244118030049000700721074101601c40240050300310501c08070444c0402e01203035070a40200103000a048039040c41c840001c05000a0074110540402c4104880c2e1000b410241005200f58840d80380007924040c0343c0414040b130002011020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 502776591 1250 502775341 502775363
    0x1c12051905070525240209190914161103070203010212010618030c060e120a030201020414180f060a090515130c0c111210060503060c0c0d030b0a03 65
    0x30b000201140d0003c2c81d503050511000c20042d130781d8130034648444d4100b5030207010010301207180c0d802c2c0c00c074820044e506134088503400d10107401242c42e14000e042c03c48940c401c41c000b440e42480314280840744d031007212010504400c01080503090401001100e0300702d9501b032122041050426091551184075002901540040ba02428400c543ca4142e0305036600b84d100c00c04410804010b1707000c140760604c4050f0a909070a401000040d0048002450f06c030009800724030303100d0420b400d103441c08000203000c0300141e50000d82000041c00014102600201c1110441070300d80301003e10b8140c60002400340312021424402040071030361001719910042118003c2485a40b910850904c0401000561180078010391401520050664070901d04501425103074800711101c40e850b40350b02e031a51480ea454200450304000d201d00602003144400c04280040042405420041450f0600c00b020f0010000d12600b801120001100810303e0f82150410f03250005820251b880065005031103a0300103041140c5103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 502777841 1250 502776591 502776601
    0x5060f090d0602190f0c1e1a010509010812070602090a0302090a020702030118120e03030c030c011b02070503030304030c0f0b0103150509190609080415050c1c12051905 74
    0x198000d84506828038a240348110390254003550000300c4900031500117030f048110306c0005103c4100640d80042055049201b91110381e40d007030000c0c06070b072044444003140240100064901240c03c940035002d01c0d8064811280494a14030307850007a100b00034099a0081141400d50311081000c8005540040c80400c150030140c000400035801000280c0c0254200f1081c52000410080d680c00242d6104100d186e0700c0769010b000315040c05400d00d510350302d80810040d0a6400744104040d24a580c0d03481c0000485a442e0142c0f044848031003200507041d90041c0c107003045580d901105403603000e505810000d00c01c52407031074010343e030f10032444000700600d071f1200000c001c0c4a18203007540c3c0071616030b410800180c0c13100c800183c2c1e561408a000d9074813291002011000511a4001100d16031280708950709050304d50b002070404204400b00b807400036001050240c030385c010421807017441030f03540c3da58100c0140301402d008010078038079640500041d0711030011602e00200c10060002045100004100c1401c00d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 502779091 1250 502777841 502777853
    0x70b0a0b0303192a0b0405012a170106050f070515070807200601050607140118200a0b1b010603060b0a0b0c0606190e010803070308160905060f090d 65
    0x340b20280d0340041e86030107000302d200d6905a110704c1050b051052408080d046a60340318004280144100ca15540b1000b01c1d02d0104400401c401540801c1c006400c00c540d40400001c1141516000c1072107181544070041210640180840b112000030b289120f59581050401620b8089920701c0340515603500805c01120643c801901d502483e0996110a140080d0100b00005458050042481b035001000100250728010005121162080603107628070140c07240c40c1400c44001e0300c686600b08101cac4e03500808004d00340d0a00c03a24080c170f0045951042d030007000400c0ca140304901074030104440004050803001c0e030060310b50b040502c284000784000b0f6100c1c68064060152002154098107071240040740e00112041030302c803409010002041c0c3c80c0e03604020041c285001d14150b001c018015500424940c03c00e0840b0f90103414244025030391442c851400a0800340b008014810b0016010089420700c0e40c0482a20201d50b400c23282a0340b5408002412071141c420780d107036250302a40c2d444000040201c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 502780341 1250 502779091 502779127
    0xa030c06020313080a111003060b0c06040b0f011215020706020309010f0608030705030906090d122606010e010309030e060a1107090603020604030b0403030908032e0506070b0a0b0303 80
    0x4080450302442c030ba4a01c2030f0b541da01711100c801403112018007050903150404480981100e8128034010a41e07668412448034550701400f961a42e070341020041009201c0003601840e0408000d4088610b20362508011242e00c841d03503000100003954900a043c9512959015600101c1d000f460445da00d090007141769008100290b00e8014060a1a80c0010465000300984119603001005980b42c402c00c1801c01400350301060a0540c45109094080080b508112525000188944641070011141501c20004101200031040780c3c0e04000b042100b0b81c1d91092898400c54800e0901055031030161405450250801c0c00140c0c03c07010118409040c3c1d907200d10082044055602074422040d11024503d043d1906408040d4100f4000c100800c00520032151465002c1d0091800040c015a19503030341d800c582c0705544a41e14681c541c0c0e90007090141a03d0201d07041307002720742d4400700540b424012031801e000d4044041c250381c844000068100000790011103104000074140da94907640b090442e05045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 502781591 1250 502780341 502780357
    0x31c0506010e06040b04060809011104060c0b0a15090e2b090801060602060117010b060310080d1d0d0c030203030f12150105070b040f0605010902030603010c05070b01030b04020a030c060203 83
    0x250140d00d05031000d00f0110b00b204c0a03158100d5030149045d017050400d60707890001070003100040d0340e5941c1c00c0c1c1880b0180d001400107400c817551054200c06550502c0904084003802c6044064a452003400d64501e502004400320749150740c0210329000641900da080075031841100e0f402c088000c903441120128556051501107858444c0581951200403881c202e502c1d030300031200581d20140c01408241000c411101051413450008142c001d1108046105a0003c1d0307081c001001ca0303024184100740062015429441591521080041d09840141264441205c0d0305000e481140410303c24859400b003248069074010b4100c96032405480007103111544500c000818500d129804070341300e84203a58115071182030580d915801c01c181900e460807d00f0000e0402c40d64840d200072001c000660600500303008180e200310041c1c80349008401d040c00d5540d000c1070758040100270000340d0000f851800d500c40c1034a4110701440c025030b0701c40c4041560040c1c55000503200c09040000000c6640d03002006010031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 502782841 1250 502781591 502781597
    0x16060203180f0c042d330b0f2101030309080309010801260102031501030612050a03180510020706021606080c0a0219060903090b04051008070513060509041103190b0102031c050601 79
    0x1550b5035080090507220155480c6c0c000c0b6510300e800300700604806028011400d0f4026000e4500040e800e03051103001080911890410300e140010018141c00401c02c100a00a40b00038524012040300020039052050141da070340f50701c0322550915100c07440d880d642c0320412010002c65607810022980c4150092950055000a080080c0840d82e170b01081c5245403034692020080c440c031335582d42d043d514501400c03032a403402c4107030000018056851880c44c1c0c002114540141030031500f454002420700310182c1140c5212101c000c1d003001442d5100e10400e83c462343c00f82d0507546400c60050120308140000e02480d01410841654505002d00c550040c048248a030300c0300004241d50f4412600c29000e14800d041e403000301036041c0007045018591095020503280382040c5040c81d40455040034042c260400e038001034021a8011304e6062a110f0300e045514021041ba0035887c1c40b050600740c2182582801080355103403034000300030364002c006940703640752080191004904c0f0500d0030f1005050403101c2ca400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 502784091 1250 502782841 502782881
    0x72109060b0d0b010e0606120f04120e0102030412050f010504141005250e03101a120703120302120c0703030507030510091116060203180f0c042d 64
    0xa1464006a5a80210f91114040e01540e01c4c04513102d00c54080102110b4016204028a46680810302c15051160307200c61070b21107090070b1078100741f200c1500710440d030400d200198800f085103a800000383d41c00c445401076030040a10407072070018203020165048070322540c00c0c001841704106201d1a0b01503144540800c55102e00d10403150380007a55010743c2e01015141081d070120410b1200000360500300911410b01c0c100884c024400300341b41c00c202071400b0300250358901c00d0040019042038102400e06040b114400b0781c0030b11035882a10f031841072200910a4049400d103542841c000e030103541504049501d41a90761400804c101c4007030b44004d008900184c601000030308514003034415240108002d5000341c4806080010354001014011919075518000b440204100c4c080e036022228500c2c0300d010056207a0520354130709200c1104c8001d444030103820105040705440c0d400100d02100d4482280d000c148480c0348022105072007600d0441145941035226010341c2c10f4019084980c04020810588071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 502785341 1250 502784091 502784111
    0x1b04240f020a03090501080c072010020a0203030a030207051e010903110a1106090102010f0e070e0921030a02070602161511040b0a140a030e0607030204031a07210906 73
    0x82c640e440600000c020a207051000e005c2540715100e090345c0100184852840c007152511180369441c032010302c426000d000c050000c179107400c0008403102d4030303120b0b030000f84003602903036000130344a000f04454082010350100d03074001401030410101c030f45d4604810b801820340700d54a070140d02a042d160001d6002c190b94101a0a00d0100010720030b4101e0340025005100000000401ca41c640c480c00b82e00e41159200d000c1c1400c1a241d030700c912170450741c2100c010400716103030144900786c606c002405885543c00805012140d140501454844007240a00c196526510358000038001e0062400251030148017062440480404524040720303180142c03001881c882c821604042660018541611000300a0208212041c00d24000c0d15001989040c4044d44c084510400500364210340d81072000680c41c0d050000d8103103008c1c4011074100ba03040c9400d42c50716045484696401c04421206003000a0303110000303aa5500c105a003481c00304101800100708900050400090151030400346c40c007600d81a0301c54 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 502786591 1250 502785341 502785343
    0xc22060b0306090402040b01030204080d0507060c020d0804060b0a03140a0b091902011b06091b1208160311060c0a030e0c0108070f03020c0610030308090a0b1b04240f02 74
    0x182c414840200450b0407995140d003407002800304944030301d05154081c80302203034011050110704250f4100350795041d210845802c184080e0382460408101f9508120103004100f50310000c415403094101c42d000c02c1c0c54443d000800c0d0800980d40c4050000e543d20710700a400014042480c3d112207000703152482240c1c8900c05e00b95100e250103110300700002c284c08103040041d4010001c4440e9038074042002d116140d102c1d00d404040d1003400c40200e40d14680d080c5008070b4121118205400b0b409820f000110303540c960380d13514040e031203000d6007001108081000807003014410302d44408404441c4040d0b03101d9080140a0035140e412000788079022070f060001050719140005003071000c0e05016503e50f0010740b0b070000c064816019103c5400101034080000100071101084480d000306840011f2411052031403c00a202c61030203004695550400e808940102e82585d4400c2c2c0c01a07002c1440703000548204086075107030300c201e511503149607620b10104103007528141150b110112560b2220302440d10100790803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 502787841 1250 502786591 502786597
    0x20c0d08090606130b031905070803040b0426010903030506010f2613140a02090f060d0b060f0a0914070203040812070309050303160c050f030604060506030c22060b 72
    0x142000e680814000340551800034400311340b00f44400300005540c010040800d0a01c4080c0c1b0407001c0d8440600c4000f002c02c04200500d40003004020040c6041c035013400e540f810144035a00c03820f04840981511030f914151140340340303000007980c44001c01c8007104a28000e0043e20341103a6150105070b00d880da648034540101201030650300c00b2008285080c42014800c10484c030080c240350200c01d81c208800c00050b2000080ea00c0d20107615000f0301d055070040c0b04000409030010942d200240085040c4035817a2200403012481a91001c0840c210740d0320100032488880c9413072030655126018a0000444041d00c1d403184128903038024894100d6034502c0001c2c1d0383d0344954440d20805030310803503060604c035900e030f8007410300103219284c88140981c0d902e000914540151000b91074601d80004460108030003100070500070300c01a20310211020847c1c00190710b5010040000e0200c54480d00094000c2e6000d0051a80c1004c008050000c2c9812002c3c40b15144410398100703428051604a01150b60314080c415 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 502789091 1250 502787841 502787851
    0x3070305030408070c03120801030b0105012c0f1323040305031308070b070203030601030b04060602150c0c03042d0f032a27110304020910080106030303020c0d08 71
    0xd0189503890300d554a00150384a2842030354800c410400200c0001c1c9003165122409219684581c0154114109044500c1d03040e40072905000c0a04903094200b01c803403e00c100d04c0303032180c104038115080041c08105140100340d012075001944000b03041c180300d02075000600031104040f510580c01080880d0301210350081c1e8001d0003003030040c000121100388a05100384600c1c4200b00e410f0500166035140f042c0c03404291004001368001008001b12568076104184610f08100c5042c8801481c2c0304001e510384000c11145112041390400081340200394100300c854102e42e8400300d0340e42d1503503007a1b906031a000d030481840070848454091060500704096400903101c8922103031007054a16661010380d02e044000da01c80c449a01040d045948412611490040004004000c080d80006070111804901e540741031814500c0c5c91681c503507410381c0d202a40c0d80242d05441c2c900d07060700e0f05100c0102d0b424641d400455250f0034050080101036064020340719490390b24080300c508401039802541c4003502128 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 502790341 1250 502789091 502789097
    0x26060a02121e160309060c03020c0f07050a210f0620040807120615090b0a30050a06230901181104021b030901110d080103030e060f030f01030204060503030703 70
    0x30103e03240200d80503540b80111103509000a40306541c0c1d60301e00039640562030f0315003c00d50100342e03424990b50034044074420080c038402a00d20141400001484c00e41c881c01418044510388a8071410540400c0700e000d8060f40051500c0030504403072500340c1c017030080c84600e4040001d26100003440c0b403030003d0585040c0c0341d680c80070303280e054103180214102c09400401542d0207038881c010315265201d201e56500240403450030200c0d0600240d82031004007031540e4461100050071820172140040d801008081800d02c2c04644d268201c070f9410280c4c40c0642140020709414130300300d562811011142c110a90400c0d18602e10180d0380d840314022400c03512a0308502c4a4030600008030000111000713107524060200410041c1042440007038026071074034a020080b40c80d03100107140085e540e00300f40c2ca1520010440010300c010051500000c12070241844000c050050705443c801c0079039100029134584208100d1096280d1402e5201042030728800c1c0f02c00d0f8081c52400d00042150305011007215030b09505a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 502791591 1250 502790341 502790401
    0xf060b0a02070603020d06030609060b040c0c0b06121e060916060e0d0c08100f14010503120a090e0f150306064903032426060a0212 58
    0xd0f00a802a6101c112012145599130380c0201c0021110f101d404c410034060400020580074440c248008c80b6603442604c0d003808410604100014a41ca410580c0800309590b070400801a082e0003600d00400c1003001d4140da8503020400c50240000160544141091402c481c821490302034139610240341800b42a00045c400c41d101802800c18042c1000c0f1548034002d400e9540c1c2e82c2c1d440d940e0900040100c8000501c1e25400707441c11210503405407850b85c48401c12400d08651601d00029558940000000c59000300403c00070402c50080442d100100301e13901103d50180762206240309205004c88441d840c0e040500d035585214140028100d20450000e890500c82084034913503211403507624840e904444180e031054041b4114040c0c14442401d10150a04071401104c2c41d01400f55104411f034041c20781c0034000c03080040e501990102d0116454074128441c0301109640e4810302c0d600e8140b080a240c810b00301481500c01403035000700200800100311080948403a40700c0f1801e04002844808589944 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 502792841 1250 502791591 502791599
    0x60813080a12020c07030b0f0f04031b020612011e080c010c02060c0f030405120102071502090301021204050f12040e0c0a11010501060306031e0b15010917010f060b0a0207 75
    0x1600003001a540d250a0100084480e5607405050340d0021013840d1854003c0907081042040e00120640c0001c00a510449207150980458045107c024006810882154180440b06c444170048021031600541340f140c2d650304800440036103600a10540c5004018030100b60ba2082c9100d80540940e50440050b002101058004450040350140d099901487c20460042d120100304803580b10b040364034000e180c8030f518103c10402881403204151040c1e0340104070840006502c0400002c0d000180c10006880d244030b000031900a0240c002070804102c880010300040c0321000980800546030542160343c020710100e602003150045201e40501c0602e0030021401c4d003400301c00588503840d400c1c40c0041607911607061703890940d68281c1c0800042942c801050042c0500c0800081c00c0d1242c01c0c9000306680155038130825105070081050580b480e019424134281ea100d41e810000410002c105500d1348150040400d000305008000320140601d00300780003030030801a0065920603c06500580350603850 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 502794091 1250 502792841 502792853
    0x30f1602061b09040509100b01020a1e0606030b09010e01112802010207050628050601080403033b06090619090501020f0301060c03030b0102120702060f0c030a0c050106060813 77
    0x30180c2c414040c40024800e10410f0349881c49400d114003042c070700030500118419003090445840010150464201e5600c01001c40d2040b048891030381c111840e100600b94140c10124000d12a5420041540000c2e40c117004101405401c02d0b504c10000100802680e41e0800c3e1200c220702ca0000b220700e007984040e1910003007507003030040d03c84400210300015107010183d82d40e030b5003440000c0310720b203068220224651000c000c0082040c1c1c1c515194039005c1145043c0640040c00300d4000030700042c03c054071410440c1e030002a001c80600181e01e2403285068202041c4404050001d61141142492003140005122184002a10783c000d80b4100c2d82542c00740c0f880040c07030026002441054541359000c104e05c3c0d00072200c03000254000c8c11180e45210074061589002419550f850b105c003070455000804003042050300c07408940b0182d0341102c0e4940d492503102080760700e030b00810040742450f02000c14a4050650460b00d51419244150020401070340ca545041e980302006540b09201071418096190000d20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 502795341 1250 502794091 502794121
    0x1050a0506030c0f0309160501050406080c160210030b1509011b05010902030a0305030405010f2a0c0204060303030e0f07211b15090501030203090a030f1b08030f160206 74
    0x340001d40c0c3ca29011300000907680719402500c490040b9403000c840c401c81d11004400d0340d0054242464418075007071600100801c1e496001d071500782d414400184280d1344042c841010101c03240c1c094030491181d4008032010b00144903d0382c1c0c540c0114080c9a09600900c0b5400848000b100e0584a00c0ea190140f00c88400260381d10503000c80301036513580e4074000540c0c1c0400852145070b1180da6071b582c0d2071519181141c21744504071081500c41c1e080060030324a2590f05800c02c0320305100c0300c0344141070510800c0102c81c0400b101601a4100749045008014541c4c580c2080c041c600251007101e030203103110706030300d55a15007502c5000c81e1424160700019080c945e09844000003801102c507140c2615102c0c0c02640e0642c4258030220b41540407000c01005c0d6508005000000d1009090450640c81c02021281e116001c4110080c100701c00032039043c43c603a0040c100c0f81c440f42e003c5104048905801e01d80102c09074819aa5481542304401c00261044180740c5904c840d040c0540c0501010b440381c0c10034100c407030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 502796591 1250 502795341 502795351
    0x118061206090c0914040212030705060f06130e07030c05060a14130902120610030c02100c05041a07061109060706050603100f0603061b050f0a0207090906140f01050a050603 76
    0x143c1d0340180041c002c0c000340078400700c441d00c42c500c0c0100b5081ca481000741407002070410300080d401c1840f20b1008140c020448642c00440722008540030b645e05000102540c0716080640b6900d0b03e0000c1c2003017560400203040081c0ca1048907111071064440301042042c2c060480174100040e5020070311400941c13107501030800c0c440c2546000c00044d031a400f0440c00e0f0f0b0001346000c01d00c2038942c2d041000038944400d01d000d580c1050305040080c200e00850094aa9031011035004003152151f00c0b00c41c030144103a04581c000c10074205040c4110f62011026140c1e5807103a403003600e501c1d0410b1000c003002101c8004035620900c0c000d0950340b03018010f5850801420005220a6142c0180741a0348142020360094040310607000100241c41429890960100c4019940a4450a81c42947c103c8a15008000c80d0041286080f4803030f2a46000c1e9422464842e480d00451007880c20402580c1c00c00c10140c01030310500455400040080d62503c82d5145107140912400e42c0c04060700c0307802c01107030928400541d042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 502797841 1250 502796591 502796603
    0xb01030b07110607030939051903030c0f05070806070809010203060a14031213080f0307050a1e051006090e160b0c0304050a120b01060c0503030609150315011806120609 74
    0xc8980454216003607c8200c00c030001210030440c42e080c0801c08503c80c00c0038010407104606020300140d0868203400860100805101c1600c0c0c010090022109030120215405821038901f55110401d80d81c454105640b9200440d012001140c40c0d44e03818001d032840740b007024060007040d03880c108114404010624032560103009403100c5003038082c508401000d01008404138402400d08d03091559252080402c400d490b9038005019203000504085041c0d541182c01030000040003402c80701404d1030b0707100c484d0001c00511860001c070a07402c000c2c0d04500101c6912410030840c40201580e002d440c0c068549d01c01c080001680700a2141d030480001a02000003500126401c0540391000f2802d080b80940040d500382100030386883c10170980c2180940548403620742800755614960390320742c1ea0b0102030040e5210b1034110b030014881c107104211511091000a085918402180000e003010752001c0c003541407050100700c00c0c8200842103000c1c01d000c07281c1d5912100408205500c840009248140d405c60350 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 502799091 1250 502797841 502797863
    0x5040305040314030a021b1f0302090f031906020306190608040b070c02090a0203070203040b1804051f0510030e030a0e0a05030d0503011505070206040f0504061a1c0b0d0b01030b071106070309 84
    0x8038070484208d650754a015a1001aa1202440d0030000c45980c8812214842d074400c685080c02c5880c3c843c1007130103440c0c0c04003004d40c40e40c541c90000f44205162122a64004484c80300000300540d0140c5040d02840c040e45068030707103403213980044401d00c51898010703403c92541c134041035174003426038010740c1c3c01205881600e00380303034071401c078103c2e51381c4100b8000002e01c0a05c24a114545058415646c000d60148468010b00d1800003541c81c0202c52071195522880100c0da1660030756000f90400c012910100040d299500f03442e0741c000e4201c1700001c80345c2d401001c1c4031402081c2410000781100c41071a680c1c5415007940c0c80c0810718038500368183c401c4410460240025001a00e03146d015001902100c0b0a12240c14106014002100d01e294072a8900100c40c3c11540146070301c0804550444c9000c1c081852264079420f4144041c0c4103200000f50000341c0c10750740d242846652200241a207109050a20181c0c4410900311514044030100d0310581e0408004034035100e000e0342c0000d240e00c0c8501d401c915 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 502800341 1250 502799091 502799119
    0x1080c16111f09090606032013090f1a03030a140c0c091303020c0303030402060403330207030212032707080604240e0712080d05040305040314030a021b 67
    0x142150011001d00b021600341c08060001207014014800600321518040005c1c0d410601d07030003040520000002c440ba0030000301000d21f130b1010044900607044141d011b000313601c540780d006030081c1420f880c0c40d241440d01100f41403803440d020040300e2044489549604407034540018032000d42e808401e0540031803085202407070883c1c440340661071149408596000b18100c0c6814043d0030160210800da10a030010002c100041e42c0b100255410349800140306d484034119541c1c103040c03c0320700103810113107064824400546051135400504401e846070f0300703603081801e0300341111007980030a48000c0301e446105d250f0303c03215081c0300c1d54603558040d80340212071040750f403401c0b49800e040c01503e05852809903c1031604d8000702410440c203000c0c9029104002c0c45489140311600d4240310301560003580c28080141051000c0c074006d6803403100d80c001040001c1d042034034000e00194003500c0700721100c500040c400348582002005a8080c0e420a8000d0f00c6204643c0050020312000080303400c1d444055580009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 502801591 1250 502800341 502800379
    0x711012f1809070e0907080105090403141e0406090503060f060f03150903070b0603030702031c0225090513080301051512070f020c030d17040501060b070f0201080c1611 74
    0x143c0140740546800b00c0040300001849918a401041482481584001080b01e900c07000849a406501450403100a02c1010419000c41c41050300d240001d4040010340c850f00c1d4940d0004204032415a110b0401240d616814540c981c0300031208026081142400140941001c0311328203040340000341981c200300340800003109002000e0b40d0284007540701003200003c1180c0c202c80b07190801c070704500075070810307240e84d000a075503140307400ca4400c00d50024000007038054020030100c0b01003004003a242506c107410958a101f421110302c41c201065051502064004082c807440d2101a500030b10380070700d10b070300380018040c0e11143d906640154034000c00900b2400380311240c44074081d0fa075581c0d80340c15022081d078000b0704c0c01d09045442c0784290006502840d103142c010141c3d0740c40345a032036041c10340340d500c6007051401003007180d102c056994000601d201c10803160700e0144810074802d80340c01811fa203501c1e54841e000d0060020740000c001c0c4103002440411040ca4201200d0313003004100b031a9800c1000110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 502802841 1250 502801591 502801609
    0xf1e0a0609030b0106030b03102c01090b01090b03030403060b010905040e0102030603070506090105120402120303161202070803040f0f060e030c0f010e0c0910030b0711012f18 77
    0xc0018604500c00d0040106241e0340e1401000d60340b4092041405520009888800304c000d00e1802a41c0c0f8500c0302d5240c1c2d1b558000c00010003400141d404400c940c1000c040c064400c0d120202c3c2d00d10390740400440e0f903841d80c1c4203402c44078070081c00840c28541580d4401c0700a0003100b140030705004046900044c140e485018100078050550000b50300ca0a144041c14940407442c0c000a210388010b00601c0c4203640e018080e03a12200340700e0700030903164030380f030010400c45210f03070310b1a0940b8000002080640c0140e07103650794080c2030315622002e0541040744100101d002d00349000780a0a001c1000c1000300b81d1214803101c40d03c2c0280c91096180700541d4455040782d00161042c0529000820003104840d002d0007500036035090800244000303c925012951200c4800400c1485070581001289180340d4401d03c1c6006581d210800c60414100f5105c054410549520032444c0c070b43c2003d86407034502080502c00c51141c40c08449141080928804d0b1100c140c0201c000300c1c91135801c0954206481e600e098203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 502804091 1250 502802841 502802849
    0x120307020c0a0312031803050f0f07020904030309030207080a02011709190311011d07050616050d2a11060c241803160f110414070206150f1e0a 63
    0x5488a04c01681070140c00c2d1105001103014030344407000880040398100d1304844100031307980842a038620075520140f000d400384040294000701789004000c101501940003054040c000e40803549403039074550581b640c1d642e00c1c031002400507410810121a030030083c0f4144c5e0300a030380d01c1e058507a000d001c00d0401c5040802d00005a0005940988510b02c01e20b00f80308035801038031030046c1020100c0380c1101c2540e50311202c1c41041c0c041c400000300c1c00456070b061048481d210341e105080d681c1c5101381e8640107050700e000f20414040c1c0480813140e940c4603942100e81c101641c0c0d0204c03d0f1000d10760540d080101c03d40001a03000d41d07502455003540b400341e00032891940d08240c46101c1c007810b4144142d41d200d03418800c45103c800d9510400c2001c61200103a840c6001075640100f0560140c03500f840d022802c13041d140b4920360000d05240c0003504440d20201040c4c440c0307265900b107c038a07603560100381240e1407100ca0620b8004042c11754004690412a804641411104035042211060f010200b00b81802c2644 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 502805341 1250 502804091 502804103
    0x61c050a1104090218090307020a030b040b0f07020613031112180f06270901090f050631230103031106010b030106051e27040e120307020c0a03 63
    0x3840e50100148059607881c00030080e50204210b82c07107a8003080c1c00718550413542680315030107000122404010012200c82c5035000c1c0c80040810742ea0b2511218019040c2c41c119a00d100c6800010290701c80d280000380701d0291a8001c00345920340403411031100041110940820403c501c11540701c6c8001c00c00e03030041040c0c04040e02e81d20342c556090362a442d41d40a891030700c01c0560201e5541c41c0e0380c1d0242559a403150081200400007846485404071202c2d03070881c4d0350003409034400010a13170104d13403020101e0400c40e80305110703d96680d41041040380e075580d00c0341005d01001012550f800c103844140c0c00b213000d81040001b26032901001448070010f404941010882c070b094014010594061010010640508000d106950401c0d0030aa00b901050045904010010402d02c0703000c41e07089100508422032082003651b0315454500c1ca603c90741e204017001c0c450101c00da26400300e405c1922070066440e03480d2014050100440c50040300c540e00c045c01d07107801c40c414144c4a400320f58030b1440d40d10085200361 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 502806591 1250 502805341 502805353
    0x10e090c120c07170f1c0c0201050a110f0904090f0f0c060309030509010c150e06101413180501060608060907020105071d0307030b0c0318070602030909061c05 70
    0x25030807560014005160003096182480440c2c0000e4a561611040300c03a480c0d4035036110807108481c2e000901a0001804004d128000003d10088641d486140c01c0e440d594002d014550300c541007001607448a400500300c90b18200b00c0402c800395014054152407030000d01c040360010f2136444036130702d8205c00c0c0c000340c0e800201c1c0c0388118100140401804002c0645080070300040500f070302e000d4681d00944402505010300c542c204010024517852581c0c0301e11401d042044261600340b6080e5440ea011100c0003250314100001148000344002c130160240030040c4cd10b1241d0070b4807402c60020302040d49503030901c0e02c0c0c100c0072000041c80070301400c0064050390365540c0f031600e40038040010004001e00084256403500d4103106540341e02101503000d0011890031454240c4000c40424a07007401c941c07000d04140c5020042c855114400402035001c0c0040c041c0820a0000002005460f5000e80c81580003581c0100600c03003540c00e100e02d856900160040a0811510410110000f03c0c1002d8a00b1a03068005c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 502807841 1250 502806591 502806607
    0x5191b020a15030b190603050c0f03070801060f02010b09130224071205311e0510110712051c0305100816061d06071a07030507170402010e090c 63
    0x3d4400d0303020301042216038401c811840c81c404040c4402c14002e003001c160b01e50002500b607002c40001c458041c0f569441059491501020041c600e107828000d803000a840d0340702d18182d0520502644956030310080c04800ba5071142c14001450410141080b604042625507102081500560170700f0880380075058560350700040e1500d4160302000c00c0340b52045c0103003801a1501d40d02408170101c140c00d2000886055030440030085000070007240c0c0140a80040c500d90803901d02c2002c9083c4040303c105440203003400c1c20044d41614620740110100829520a0300200207000c0381c800c0f24200c0300d0040c416540d5250440d001400c006006405400100c0c0d20366080c096400301255501c03008104003000f0380310051083c0030441d0f05c54841c4c0310700410040d503243c0890054090b05810100000c004003001d556103032501e801d041d8440502040c40341c1c1020040090900c030f000e8024980320364407a5590146003404030380080c1480f80041d10a9040200d03d88959240f0388402c7d00349409a2610240700d0340760210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 502809091 1250 502807841 502807847
    0x11100c020307060c09032d0b07030c020f01020c061308040302061206120a02060f13120c03030f0305090a170915040f06020f03090f0d1b140105191b020a15 68
    0x1050351010480000c400708007007020340720603141c1452860310000421500d2000307003042ca5291f180c00380c40349001c1070612240e144c140d230140c01001c00035004e80e004080b0103032640c3c1c02c0f4005c1654030400c0d50480720000c1c5c1d5070643c512074140103c1c42044243d040a03125004110f081e04a480320440c20b0b17034640c1c00d0004501d0603480404c00d003655000184044122540410883d00414420a089507004118405040c8100c400720028002d103030400c0c04036011a041a41810800d403000f6404200302e0348500500030b1182c01041e206800c1d000003000d40512139a149030340c09408522950706003109001044696940c115038480c0c526062a50360b803514108a120b5402002d254484003d6501090700008584070100654100100841d1003181c4109401e012540c080308600c0000c00c401c0c1d01d40000e0700311030541181502611006034644010b21041c20054400740b10f00c840944458040c0ca00010b4040d101d00782c14020601004002c4030841a20350100b00d1801194000c11502d400e1801e640244c2a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 502810341 1250 502809091 502809101
    0x211c03020a0e030a05071a120a0501030201140703020c012f0c0301060b04080615030102041a0c060a0b0906100306090903030b0f0616080c010b0904110909060601090611100c02030706 80
    0xd0100c02034543c1d00582da0398181d8403029841804103100d1f5020a4454800c1c1c280d040d510000d00350b1303004490914014107000010242400201e010617100044014099000700a80e42c3e41c2c0c2c1e00d038004000350303203070760006403600b038210410400c078442182c5220007050407069801045104600080407403034043d108060944940d600028031400c000d0200f000800c1d40051810b070481e00d105200032605100c400880c1c0a44110342120403807a801c02c0e200005c0b8004540146044cc40441c10303180e0f50303200d602003c426074001e01d000e00ea002c003121010403100d15200c003004100b1030544c10300141d1541c0c2ca44400050f140102416030200355a01001240c6d42000487e400101d4802c0300c07090b181000a08003208660b210800250801c8004500820002402d46c007540320080009d0810b910362406140c00b00c101821414405d01850812011a640f031f8000a04240107150503102c41c1c0d600d0781801011200c2c5100303000000524410516000c0c000f40d214070401c000b034100765000e10382e1540c82c0e040c8a000e0b24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 502811591 1250 502810341 502810367
    0xd1b0f03020f0d020d060e07020a0b011a0414030a1e03030608014506050105030c09042312030708010e090d0c0605070c0b090d030f020306211c03020a 66
    0x14010071503008802e00300011075404050081005840c2c05103021a81d004010b190007103190a1112001c4c0540c00d600082d468081c54844c0003d42030b16a292184c0301611071070704c01c03400c0d4510f6080c00140040340b0382c26a2041110005400c079404d45009455042c0b46034400482800a90440c400e00001c1c9035042c041c1d40040c1124500074000e60340c2c422a80401400307882d0b0044240610501c4414030320710110f130314540c1c14954003040f51080e8001e08001c0000c080a128113440784c440c0c140255814100030382c200d4401e54003d8640e2900c442c40007402c85c80d002117104950201d008403111a04d00320f04800195001e0105955082c002c0c0d8140754141c602244090b0010f12035500054140a405511104411050354043e1001c540381d107a200f000e40710003102801c000c1082c20140200b00051100250f0a0309007210703a40c09011802c680d51400e4102c0c0b106a9680341c201841540300b01040700803a84542c407041130001281c0303241c0d1550644590041c40f00c500e00700001e40004d4280246030344a80302421030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 502812841 1250 502811591 502811597
    0x210b010f090e01140c070201020a0507060e010905040c021b061b060907120b071809020304050c09060f010507060e0c060706060303181224022d0909040b0901020d1b0f 73
    0x101c1c9560240030540d01300100490400c3d900002c2910840e4401d10001002c01c1c1c2c440b0031500840d85600c005441d451800ca00d881c0060041c0000240c10b01c0c142c000c03451880b8464001e445480303c5003d011240c900c851903082e4102030108244040441014200c080d000c80c810094482410200d1186092101607848a58034070900d1030a01d01249201541540010301d41c03c111680303007000c600760425001c095002c0d4000364404004c0005111004c0345c0207024500c00c40d01d84c503895031184100004c82c505881c8003400518240074850004045910a41c00a007154044520450354000040c10139800441e0448200d510740c0e10130010940c00c00003e40000c0b01440340c02d200a401c00041c407443c01090100070f004c21508031181c0d0100d01d0141d191b20f04a850060003507545544114054601c01c0c076004074450480341510141200b02c0440f4183e51031040018607801190719582c413003003031400002c0c05400385554208400e80caa56020300c28848442c4814034003442c040c0310300300050700342e4000301710101c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 502814091 1250 502812841 502812851
    0x20a0905010f0902360103200406030b2407060b090103020d030c0c0f060203071704140922060c02060a05101502190b270601210b010f090e01 62
    0x400180e01c41603030f005040060326800385520030750304400000342c1000c2a550100c1600b40d0b891002c12008030100c0c00ba2001d06c4403441c1e2805450344842d01601d4a41200741c1480b05001c1184a40c1016100380c000034900e1004980c0d1807150765501c2c800c841c0e4480c8000d000260789040110368051110344e008110344c06000c079890341d00481e6003d00400801401c001040614008200b1046c4081000e0500d2501d0700741c0f8241c0340d8101a54950240c0310a8800d45410a004070902d20140304440560fa245145602a000c81505100743c0d0800038000a000c44031a29051400c0345014088542e054020b403000701d05502803c00180c00c200d4081c1103076150314103003010400d41e1740c03c1803c044111071021244084064030500100d0402480a92204d41890103102031420700c0001185203000e03911545440c0e080b003080c5048030b0b680d0b004030340303c1c941103030002d1004000c0c111541b03c182903c015006043c6012401d02d545460051800360400400703501c440c03500388103010640c440c8046010202000b001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 502815341 1250 502814091 502814099
    0x206011802271804050d0306090506150a111615390b04060b03011d060a0b060706090609051b0f0d111c02152d0f0a0804020a090501 58
    0x24000b010000310ba540c00e29400d03404a0183c881540300914007002c00c0b8140c602c2d00f858502183c07522400e824440c0001d00342540030a41100380d03c9190b000c2d00008051082c858200044c4003100c0d000140d00005100800000d0a4a1074080c0500742c45008880f041503243c904103039240007002e40e07045a8100300305407a0704540c5805000805040c42c1c1c40c04020100c2655402543c06441000800380146540c1d04036081c0410411240c03c001e80d142400c800901600803100740d0b032620194035025110450703202d000460000707007690740300b200b46080c0541600c0c40c04d03042d03032526019200903030400c80b281031740e6448a10a0040c180047d041032040600700d400306400c0300700002d4220200042c1070340301e0980300485030204030701d07621403090921016180074000d0001f246501ea0703040b5000d8003a401032020114850301030b0003010444200481c0e000b00b4090640701107402e03042d00f06040740b0360801003204001d101054200701018060408455a42c03820718909031060004001d0191f00503000e0170308040041c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 502816591 1250 502815341 502815367
    0xf0603060602031b010209040204180c050309120d090c030b04150e28020901030c170319081e1f050f010e100302122409010510050c0f06070206011802 66
    0x400d4014a0202a44000742d00c2008900a07c64620344550043c0300090014030f4914105409421102d010700400100e01c0520081c1c03054841210121590f4001e105910401500040900714640c00c07010000794102e11903480107005030090300141c0350f0102040810080020009000003006c0d40c201050140c00c0086a0807950740c1401c800c25030541500d1503e003407043d03c884941c0b0320106d1b0000e182c144e95503524113050030200202d0040c046244103051454620000c00800c075000c2d20307804110302140380c0e191a4211003081c00075144084164403144400c0e4a400592402030154606901c00010328070401c04490180c41280e104600a00c140740c42c99105072b800c4010010301800503a103da00000030980b0480003403140c0006a40b40c1a103000c140141004109a2030b800300d0821503c1e1301200000c1420444030601c02d111702da0f488000b105d00e16200900c103030068032021640004036602840031103102c50070800125000c13801a40040d004002c1da40c2c548280e0f031202140b0201c2145000e1038040c042c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 502817841 1250 502816591 502816597
    0x307091d0a0b06040c1106130203060a0203130807020402162109080304030b0c1611040506040b0a17011404050a020f0d0302060615040305063c1602030c12040f060306060203 76
    0x941c800d85d501d116001c080c40c040d0145640f41e1a424040d11000c0c0f9003601040b4800d080300405034000d2080030b00140f20702c061072080300c1c020303001442111503080043d07aa9810070b62140300c0481c0c026401f840850007200d00c151900000910440510030b100080c0e1116002200d80b81040804106021008014080c00402104c1c01e8a8000c00c8007010f980d10701360083c000b8403684243d803000d03100c1d0f850280240101c0407034014520340110381c00d2102d9202c9404100640f602003c25a500c02004c0801f0401182c52400f002c400c00000350001c160746141e140708940030301d021031b13090316030760060903103e011450311280e510304030001102d1030008030406442c029681e200062a5900a0b015088004400e4132040282c90056500c0812a0b15500e00940440e111842c00f45c20045035000c04604040919441400301128020050103801d080c0d4440d281c0b5400b040703400c002c0c0360941c0000c2140745425003003840010300201d482ca090031360321132400340068902c8d80c41354040c10415203003103000d00400e5400304c11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 502819091 1250 502817841 502817851
    0x5220803070c0e150d08070c03080a080a05010f05130c0332010b070f0b0408090d0303020c01060807060f0509040b060a0c050c030d0f0818010c090503010f060303170405010b0307091d0a0b 82
    0x20541c58034040d00e06002c144580da040944440ad0206031f65184640c445003803807003815015810320a99036074800302c9200420900415605c900302c14030030030480b03d69600010760b0a55910300400e96584210078a080d601d609141c4414010400580e00c1510303089a4074180105260a8000d19102050300c41d030703c42c0320f4881d40081c9901e000700c0103d07045c0b2646000391002e040000b0704919a403010361401074001c7d44020040c0740a035080810000c0c0c40507002c81c4070021180c83c0d03100c040303642031400001c485076404580b020340e005555124921081c3c480e40f0152141980c1074803500c41100c2c1a0030414908007a01e213146100341c1c401c00c09024404d40c012103446481c805814000391070303100c280900780800e05124048500d9841c049491081550050000007100c0d401c0d0000c0002d01d5040100c0c409483c968000071700400c0d00c0000a1014081c841140c642c05806400005a00104100004d0a10100f544800c81d2180c44141d4040100091440401181c0c4c6900003800b450525940e00d030f000b0300300100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 502820341 1250 502819091 502819103
    0xa030e060705070b0d141b0409020d022715041a07050c030105071e0c0b010b03040f0c0603020306010311090f01120b031c0201061505220803070c0e150d 67
    0x101c20040100800124001d00000d07030003680c441400440540040600d2001042c032004100c002c03d001d011300300c0b003210520300c5240f00e5620702820040300c64040c1d4440e03441c0b1400241d00b0005294040c0b0b40000c501c0d8040f155100c0755140084201c10446400340c80001144250010442041003080e90b90080c02c207070710300e40c99458450841c0d00380720713003800c0200900d20381550801080203036503580003443d4502d8105051400c4c5007a105010200c4100c14440002003020307078220014040c1100741c4024681c002e106000c03025002d8010b80d680783c0e5240c119030000c00801e4002c01070202942e00342c0180300000620708069400d11b845c2100190071810035060316810722040c448040f64808503a005072120a0307019040b101c14408062403400b60070701d1402a000194a8070b9800700f44881510002e0b219126030307030f4071203042c04486076640100d00351103481ca00c4074849101c40000c3d54407040c009043e21b00c1c0074401002407949000003480450400402002d06c110450368408400e0365060640d05c03d05400070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 502821591 1250 502820341 502820347
    0x39060f050d0f050f01060f0c201201020d060b071509060b030a05030910020303100b131706150604050303070807080f0c030a0f0e0603042402041d06030a030e06 70
    0x524240d40301c1c0314111600aa850401c81c0755140d40742c560704400c1c00b54415543c664100da90b214400c41c1c1001d4007000910016004000c841d0210b0990b004200103800821443c906000d0a04000750041d5190f0810394035507500829121810b5a040c072a85c802010311111a0b45000344d5540c840b110720080031a08020313980c1e03d4064000340009a0b01c07030f46001c0703070142c101d40d0602e9942c1000c550b84e03041615a90b10880e01c0c001c50440d580e2010003034030b0041010550b441c101030b0500010b504283c105000d081c400d000101e0000410391041d411004074542450040c0c01c0605000c0b02c49401c40030000703403040c0101c100708010005a18000112401a9004912a03444503682e14003510349204000407180c40c410086865448070740d0110041a140b001d41d241d203a1401e84003c0c00355074030001c00c0d5009600c45070074400200441d20b4002c2c900036a80c0e614100740926610088000100e0300240c100200d03501d18850034450a017400c0e0a5650040c0b02180184940580c2c1c0d42c001b050209025030481c000c00001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 502822841 1250 502821591 502821617
    0x7080f0901060308040f09050c0403080a050711131406031b010f02010f0905010203180a0b07030b130c0e0a08120a030b030a08120f0604020c1015030506043906 70
    0x29072040c000fa6502004a075526981d40c00e0355102502c46003d5140d030315240401060700303001404200c1d0210f070790100043c0d0500c0301d085002c3c0c0e0b0740e41201000366007404c181c0b10b88010a0395103054045198419030000508000e8110b0300b0504500000c15503400382d03010904040b8407501d00d00c43c3c404550303024a010140d210727101608a001d0210802600002820501114201701041d005540700310b141404000e41d261100d2640c540c1c80301010405412544108041040b00e4481c1d00000c100420141098800d0f41d085607a03901216103060000001480082c10390900f45000f4400c90000d180402c014a100380d0b004140440350720810301741070145070342c80440045985090041301c028079084075107562160f007840c415850341542141d05484030144a400928189880e05c01e0f00e80e4002c0003401031500e03800100d0384200074110407401c442141d106d03090000000f44100b01307041c0b00302c0c070a400980c80e00200341010f035400152403202542d01001d12542403901c2e080074588004032086e52905600d00d00c00303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 502824091 1250 502822841 502822843
    0xf030304031b060f0c030504030f060b030307050106080d0905091603110c01020406091508040f21020102120106080402031903030f0218030c030c0f0d0507120b0901060e07080f09 78
    0x865000078184040500c90b080404a41500241180c04030740340c039502000e51a1003120344442c1107800401254041c041440402c840c4200410b101348130b8440001d1007800000081d2030754000500484e09a91a140284a200400d100d0400c5041e0b03281840856039040c0000203440d8200105030701424164010302503401480703034200410180150261503600d0245081d4680030b544140180c0d8081a0040c00c00904091051015240c0d802c5564400700d075a11503649642600d4900d01c019540500c039516500c4a583d6502959802205160001603680392090b8444140000581c01107080c020180c0030000940c90100e0201686c000c1802c2d2650380c40081d19080e00205014600a4401c501c04542d0300c02c2c04400f101e41d0300340304000b2070803031701e40c58490000c1607a01e4203109081c540103401c00d03030150090300700803140c1503c0a2060065402c40ca884511100380e01c810744205441034076244041c03107148c917000c0c07181ca0080c103001c290804042ca010310f4058202c48010340350100310100100080c6100038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 502825341 1250 502824091 502824097
    0x1c090f060c090609050102030a1b1403160c08061003020904030c0c120b0a05250c062a0206010e15030a0c06120f180f0206070f050a060b06090a050f0303 67
    0x25004508011280d80e41400034004441400f8400214030502c0000c1034960000094a101e480c443d40c1c0c240c1071b00002503c600c0341150314802203810040c40c01c0301c0507680c1400c1c80a409084d1910729020042081810240b00140d41030340800300036013100d4140314200c100100c0b00816a40c056480c280030b5221840d049075072505100d8040c0c022000e101000c90901800c3d0692400036024070701030145030f1604444070045800c16108111007c0d80700103280321f4100f90f06c42c800c100f54590b052511221400b5154502511035030301010340041d201a247d0f0301c2d405001d0680e0300755408140b005105547c10014103441c07203403000d00304205003484a4415038640c0da04101164540380d21040300959150b842902411440340c0c10040000d079414003803201a14905c2d840f4482044406620048250b8400d4031012401425904280d8110804000200118995912503aa464856001400b1000403410100c04031030302c560301c0b40e2040d007040002c0e803169544e01484e18241c0707104480d07401c620820200041d1641c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 502826591 1250 502825341 502825343
    0x7050f0d020f030703291210020c0606102c130f05090f1902091e0405070306050105270a020405030f0c040e06160e2b0210051c090f 58
    0x1070000420b41040074181028500544143d103003441101c684041410383e00c05042001400090301d0b00c0f65003540c0c80e00b80d160342c1080c404002500c1c4809004038500303003039034490038a080130b60b07004805100c002d041c000340c00c1600c03085074900384280085c404404d05401d0540b00945e0440c60080c00055503955400100340282d0219030820400901000d0b02000136040490304582280220345030f4510030320380810403040c0c8135035001c0c4800c080d01c01d176400c004e001807000e40041c1501544542880c48041202541c03802507009100401202c0d2540c5011015550160007042c051b488000c169002c080344601d0750311031000c83d41704280b4559100030b0024028010355100551610985c80143c00640d000701c1d40e640e4010081e40c09200407101e040c10a584e529042e10040640103142c03202d1180319200c0e00810728140300090449281041d407040142201c022810000c6c481d00e452014501103182c0410302d00111000740c1419030030403500340111503601039060424101c9644440c6c0b0141041f1000005480702 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 502827841 1250 502826591 502826617
    0x80a02120901092d0308190603050609070603061523030705070204061406160f080304290103081603091706060907020102070b0a0c05092d04110307050f 67
    0xd8581000268003802420764199028409241c5440b007000c4004528022883c010481468029803582c04503a03102d07004114003500034450301460381d0302e542400340d40000c0d07010b5001483c0904206820a0921003194052401e2500d001d60400c20031140410050b1030080310709095641c0f50030640c8202c81a049000000368000c030010400aa8540080c06089018000d840c10011680c841040c80d29030340d407010705158415400e0044410b4032403100c03030902e003a900c2410083c000145543da08101c0b50070a40c0d0841e03241d8040c12400344040d03490120564111400e460010095140d40c43d80d0713400c1d00c6039603558040c09440c02040814140500002001003030504e6207400410b070300c0b42d10b4a440b000c00341c0e0390a2080c04080702003501c05205001340e0300d940d40c1040d000d04c4143c640e00c2c0980001c00f41c541d8500240f0005210a02803a03581904010046d18080d80ca10109801e00b00c1c1031000041d140c0b00d107441149804a0a44030b81d0085041c0c07544101c003410301d03650703503044408044c032300e07001c3c4d501d100c40701c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 502829091 1250 502827841 502827877
    0x100c0602071a16051809091c03020904050f0402130e030915210103032a0213050106020f160b1305030d03021201050901181a120f060a06060807080a02 66
    0xb40081c0030503010300c100c5001d8141851038403100f0048400d8420110070f0807440e0a80703c0300d07055516001250641110111045855602260010301e44440f42280040c0200790f0114070000e40c0d0410780100e41d44131101d243c0345081454150f0014195400310484021501c0c1d89080b21803852404004070b8680760030040440380002c031900a03000d00f0354041e8950300600e044180403200101c01c410388882c1aa94107884000100e0305a0600c224030b0000001d00d016200c000c1c64014002d0303128010340d0942c8100c02e039408500356041903c083e20307007042e0011003c4035174400500f05803c000f40400301c000341d45050380f215a450f50002c02d0043c0380c502641081c0d50602520b00c80d880b1081c0c141d0300400700a07140303858a40c52680d96104002c0040400d108240700c003800300000c09003240c0203500c80703d64616401d420048044102001ca05411801c42207170101d580074100342d1810030402c0000d540e001180c610305004203810f241c8010059600540b5105c2409005400300b0000740107070701602e405416080382e082c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 502830341 1250 502829091 502829123
    0x51c06050301151502060c0a0c080f04170f0c01120504050106080303010f03061802100e0a18091401020702010905150d0c03060509090f032208070b1215100c060207 72
    0x30b45090744500c00b0746411300f01000c00080d0000c02e0041c0310321131600b10b144c18014541c1003607458102c07441c41122410340070032581d07444800d00000b074009802c2c040100450b000044003520b1801a400d000e0121581c40255280c42d40d0781d1145584900310b58221011440d13498502c1d0143c007424040c1c10034106404040000b00e003002100022004590041106000e030903d106110302094044000194011040d52050411103000b280c980021800140000000d1039075060740b01107106041407100070b8140c0f0b94404c4c4c0d09220325160b294000507a00d000071440d0000c0d41d8006006030b0004d00c640c5000d042400c0c2c62501c02040d100c16944640302035181480550f109420041c000c10700e6010303140c0b00e030b0250350220310248c1000510301c2920064030f0003586004811244c032000d00403100c2030369070916503044022031410420700241004180503903043d500d07841c001c0c501071045030004042070901303c80d120700031311242c0d00c03944444002d450904141078102c2c400d040603806489808070242900c041d0942c149 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 502831591 1250 502830341 502830371
    0x806010b0c0d08010b04062d020f010c18031e0605070206010e07020a0c1806030c0b03011406070b0f0606070204051015030212160c1401020306040f0606051c06050301 73
    0x320322404660140c4901001c110b605031405075081c01749802e40c00b4148018461103000341e032002e1240200092102c050216814955440c0f02030703080350310050300181d03940c0081a17002d02640e48016032a0400e40b40d1540e00702c0008500581c18400a080d601c6090000e0b03c6110340030b80403840403a0000824480c515210201075070f02e400a1140c1000c6a855500241c8950b1000c03a83c545901c3c1c0c03007174030f07070102d14178051000640e50000021f07076890a43d50031000000034600500a0014111940101e40b00c0d0b2500000b078603e00440500d0314050042008500300050041c101680e000b140b45011b8540350320b8182c086a100d00469100a411624100a205180703800a16030400c5400701e0072041100b00984a04905a0107844081881030694a0215900002104015501900c40d207000d21204180b91192190a045c03122f800886950010521500781132034007a6124a0002c14014800c40b0720707080c0c3c02081403148551125000d00e01c0b0508002900181d0840001080020028400403140718001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 502832841 1250 502831591 502831597
    0x11706040221032814272706040509030714070906120507051f080903120c0c060c090a060f0c05030d06050f181605040b1611090f1503070806010b 64
    0x74103074a118000340382c000d0b41c1c4101c003240c0305e0098441e00d0fa802e01c1c10280da01030076070725008840e84400d01c9040b0b400d08076459545440c280c0e4015490584d0050b50b0f5044d855070092030144c41c01e0300071400d100810510032070000441d0145680840050101d409404042d8101009908201d01480c100302c4005414618a030340d500010b03004405880c84507507100100502c3c110540c0348850b0304440c038421805018000c08006600c950b07950280c9180090501c40001585800c032400000c00c2d00101d804240e65008004880d400705200141a2924154074001808000240704850070050049084410180700d00e0002ca5400c6d0f000084a85811440c140c8a003d4201c601a0740d02603040109807001e03928001100d02e0200c0c01a41c501559611004403200781040e03a0003a41040c4030b010040042d07160f80c0300004100115591203003101c1c0ca403ca00d0049902e0150b41200c900c110300c2c3c282407200d40180c11403140d801034555041c610344088080040f17424545280d1000445000c5c0c1d60001400c0e40c422002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 502834091 1250 502832841 502832887
    0x4110d1101021510050d0204020d090503130b04031a09010b1e13060509310605060f01020f1e0717010c0e060403050c040b0609031b040501170604022103 67
    0x3c1d200040302c8209007102c480411603a4010804801c1802c00032800c1c42d028414980d030001d0400342c601160a0445400d0302e10070041291503a200044003c0084105141000941864200e07649080d143d521480d00c081c40d031048290b403015001c2d0205c1c036601d900b548054807000c00030b0100e5448400b0082c018113001038103403240e8010005070b1100c0f449152580300700030503984c004100c40a1501d4480341304070321099070f0118081ca8140300d50241400350360008500d0440f8400c40001c00c4a01c1c1c84000e00c2050f03401030100f54150350210060748401f26002c01c200b01c0517620140c43c03090f40120a44c18038900072041d03025206c640480309105d0324885040d00711104449444d15615150240390f824002584100d02c0040c00540210058045e50324103500400340351000108024100307030b401b20000f41440c103d01031070031107060924501c0304c0c581024050b9900520410810549400c2c0b001022925010020070092065400442c101e4040108400c034001200303410048988405c40081148a01c05c0402e81c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 502835341 1250 502834091 502834093
    0xd0306030c05060a05040b0306030a0c2301080702151b0a02030910050403020306010923010b0a18230d060c020a06152312030a02030d1404170304110d110102 69
    0x4002c6002e0502c00d0440d507070409941d890619281c034101da419001d40001e0030080e4140521244100030619100c100e101038410444030a02400c400c84e02d0f903c0540c22240d041e4140198001042000c0b80c020490310241c118030030180800e5541e199402d9414859800800008a00440c20f00780590740040500150b42042e0703019010000c2d0100d05170740d50f008510000b5410b505c8a001030001202030b8005419a6220400034035008050740d10000c1c80030400d8101e0a903003e4003080d20b10f4840da015403008818440d2000c49498142131941100c030002d0600624035441d02140002450303a180c5003031a81301213401138800c00c114190000000d4650a111a09035201c034145009004515000340b2101e00721804c645090500001000d201c1820b5810b00086990100c7d002900e04003405040c0003e0120009903030246680302d08503900394040314402e0320060b00e0034040104000010b14201d0130b00328002075266000b51246d0f620724000403904d00c01550260171039600343c01e101c01c0084001001d034240304260 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 502836591 1250 502835341 502835363
    0x501020f0c011802150a031e020c0606041401060e01021509070302030d051314040b0a09050a0f02070503040603022d04030308070e030d050d0902030304120215120403030b01030e0d030603 82
    0x55803d8120800018041d511114107000b165170003070064004e1034582018100860290780c4448203e00a50742031440b40300382c4d90000340e0008030380420700445621500442e8100040c8a400c080d0001c0c500c1c05000e45000d0040401181c1c03caa03008000c840705c40a0300810139a030ba450640403844e103410052000300d0081c840c00e2881401da90055058414608d89c401d2107030349071032500c49140404407417858551b800c20f90750705403c002511910305a402030080400702143d0b078201600ca880880e0300800442d10190b106009000000d000441114111070080c54050b840e99100320400004d41102c503c9107003280d014200403492440460301600899019869955456455000c2500c2c20070740e080340c13590b150700071001c00f02c115801480078009a00c2001000100640306601103841c507070054200c103d10200302d1f0712080c1186010000c3d40b5984900130303089814038400721070b08501e5400c0584014140354841c10300300002e034032aa1205080e03a0402c1c04640200f106107101600404039030100340c484e0010340f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 502837841 1250 502836591 502836611
    0x30c02160902040e01082418010c020607020d05120c1e0403050a021c05060612010f02130906050105040302031f090f08030f06041e0e010b090106020f0c03011e0e01090501020f0c01 79
    0x4507000b612404440d400704881f1280c0d44400d440c02100070702100382c80110786403080291500340300750940d041d4550000c03c1c8900308000302900c0c014825800c0010004100032019044a40306003041d0080300d42c40115803207681840b07200d15441709040b0003507003021000c40c000060043c0019052007082c0283d88483e140d103284004001920281000030b0a1544400d0200301d2500382030b480246211042000001d260300445500f1080c0d0303010040c1000c2c04a0440018000c05034244903040007014242000d81c9030510b9903000c41d88483c400e103040c501111034076800015640c3c0c1034002000c1c060f0701011241c19010740707251180003a0019200c2042001d50b8600081e15400d045c880e80900c00580500c5404220719403030180d000c2c0c04041c14840c100c0d52142c0703c03aa50383d1110500c06004c1c1c11950090708a8980d241001464526180031040c070070380c101582220624400c40c480690290784000208191120342030761805090007071801001503100240030700c0d81245c074001420801e080e06000703020a5443e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 502839091 1250 502837841 502837843
    0xa050d050a031107080301120201030b1905030606041a12100504080301030311060609010b0913061d0c0901050d0209120a08181e011808060408190c03020d030c02160902040e0108 78
    0x500340f0010705e049810001444164603501285405920516020502c0d000c242c000c5180142c1403030500521058010f030620451405100300c9500c030740150f40400120300c0d010420a0260200b2000034010114181c82082c454000d208034543c10303800070028419410249011100c5620901c000d07800207810f121411010324011855a007c3c0b0001041100680d0901c24119401d40c840e80c0e0955200405c412070742002502401004014503161100340814002d8910340752a0380c070014607a59002070100322981150f83c00c00113442d8103400311705c00162541c0da60301c0410007103146802a20382500c6002c00c07150030042d40d1001088a00204148611500c0300300040c450184d12071000c2070340c08403000030029015482030801a071084030005d2004405959840b0860420b54240c03000e807022100010410101d4440302c0d105d014250341850040506107043d20008d4450003080c0315a020075454000ea04155882013000d0340303a201e02204400c562950303c0382c0000095015101d13001e4007000c0c0c80e00004c0c0420f4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 502840341 1250 502839091 502839097
    0x3150315010303080c04030605090303090d020304081203060d151b0504180b06071e110f01210213090209030c0118030b09070905090c0a050f03070b0c0a050d050a0311 73
    0x165400003040310741d0941c0e0301a110f555004002a0700c402040c4400804100e03e4040d490040b0020310145a507424100380d41d40c14401480c1585055600c1000104000e0600185103802d1803456001942c4030f840d10f40000b2850008418003610001c00f0310310f000010741159000e2000d54100c04281c0c20340c50b081c6801507400307000e41c1c8200d180c1d034600d01441401600203500096108040203181c245030003000d40d80c441d91106d1000351407501a10158180d02000580d200d5014050b5084460f800c0d5000600d000034407090710842c000c00d48414010040c00e4048060301a0f912100e00005900c189646134203906009400c510f040e43c4c46407040034810030755075000d0210b140518110051062180d800d50f15070022019004d032207002544120700c0001510b56503446142d009183c80b8020302074030f0540785d00300500d554050300308074480c40700c0c0005115103036800962901217070f080b1141242c5502c10034000341e08180c8000c0010301580103012680034405e902100400c0f01200c10b403020008050003c0b10348540b40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 502841591 1250 502840341 502840363
    0xb031507170604060308040b03100e0606180406030c12170f0313150203070503150102010b090a0917030c0a02072c27010c030b01140a03151a031503 65
    0x2401c8003180720003807041c00118a90202c80a0004150300b5501e5a80070301ea0303403081d4840717180204084280300207410700b03400e8107005149041e8110640d0821900190790f602c5101c10705c0c0d401c0319045815034190b07125900400c0080d0381041909810079501c4409695200da041c0044500368a50410109100301010903a45a80b4401603c24110fa4900c0c5040c0c8000c108840e082d11201012070003458a0611070004510847d0b01f9a03c054070303030601c0301c442000d603008400c0d03807419039041141e1802181c031070340300d43c03a80540300a070041039000d00303410070014441603640c1c2120030700000000c100758080309900900400700194201e80295a4540b0040c004400303000465a600a0f45003090000441041c0c04a03003000c43d56001007105030400700c105100c0005509582c155035124100c0c0101e02707401d88070f0341c80042028200a1084034544094140da441002c036404145599101e4402d042e4050790101d00140003000b5045000c09910303e40100c8503001154480600c4c0003011014409003408101d0070201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 502842841 1250 502841591 502841597
    0xa030b0601140c03040b040302120a0b0a18080c010207030908150703090c080d0906020c03010911090a0209192102030a060e0316060203010e100e0a0b0418060b031507 73
    0x15840d0040119119605203105021a200c14007092038203610078001480100303035030440c46644918520500042c907644694500c03607070300040c3c0010b01154000d0b02d0f080d03009091070b40003c1e164410502043e03040b4602d0b600036004090208101050360700542c010071895001c0d44500c0c2d41c01e9520480d403039440013109804008120500c020a060f18000d0700080801c92060080300401078840500360f20b0001c0a20b0100001040c02e6002c000c0307540c050084a2800405038024072007140251200c042c220081c0c0080e601803040400018020f012650640740d102100524050012a5001e085041c08110340220300e110444420912441ca9610008403605940640074180d038450980350080105008042310364680010004120030946c440340300c95006100d00401610303541417109040d040e20707004200066a80802100b4002e001c5280c2c0f203540d10601c071134008500b00e800c84002c1005001403030341c030f50484641e020030b0104000301500700700031701403096088541c4130003a0140400d035100b06480750004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 502844091 1250 502842841 502842863
    0x31e020d11030a29090705060a2a031d0f0f0103020c0703021f12270606030812060906010315051203070c0e0106020d09030302120a031e0501060e0a03 66
    0x30792015102030a400d0010181c03510300c034050301e40803442140241058500c482601c407021191000031a15900b00c0d120a004040140c108808142d1521503000801c06208200741c0f0002c05006a9158031243c0000d0702c0900403c4c603c0e880d000e0045030800703148800380c240214074001242444400c035441094008e1401882c1500c01006500a60106038109024083e0440110140c0c60740c07900171200b003c003454074185a5081e5500107000703403101d031900341501e414140801318000750000d904d0721800c520001550301c1403c40c80c4c624000c0016a00003064110042240031076000f6240240388074407400d50b00d5640d03c0d5904401101240c2800841100080e8108014042820101e25211441c401c40c5c0c2164503000c11516003520a5140341c1c811004071031020014420389a06000c640748400140c281011683c0c00c42e94042c2d00c07600580106640540701262010b401c0d48282c0008410101000c590844012001a400058842401124003190480c446810142003070754404007202d41108000306 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 502845341 1250 502844091 502844093
    0x90a060b0607020d05032a030a08190c05040e0a05071413240315080727140a06050f060f03070c02061908100311090601050c03040e01031e020d 63
    0x140018500319821510520080300141c940c005038100c0140901c00540d240c204105900c00c203903080701c034481c0c840b540003200702d5103442d00042030382c0469400d410324816070b60380c0c031300140e82000b02400c03560003440c142040380080b290850018802e50700d101104407160b55909540030181d90068540000054901c0c0c0521031030b210240c042e0611060083c805c5c00b84560310b400d00c0081d401600d00544250036426140c40503190544110203100f06443e9a14840d6840c0011958803514144100c686c0d0800d01e049210640c58001044905003609180411580a10920b000d002c0c403000c8404c0d540f01c40c50100c0119462900742040e03820210018034462621000072a0250b0540000d07110707406000740200c0400060f80e40700b0207004040c69500d4020201c01d040d100040513001c014101d00c041c58640c100c00e00118842d10402c1811a2091b10b02d00b910b502c91200403a04c84c400c01c0c100c41d40f240800300f00820400e568100042c1242d02401680c415a202c1b1020b54428034400c0000035448050650320034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 502846591 1250 502845341 502845353
    0x32d010e0703020f1911100f060e0412351e06100507170c0d140a0e010804020a0e0a0c0e10080735240906012106080c0a0e090a 56
    0x5c281d4084d25111145800305001c03103261440d2200354014050301c80186100641c818415100204521074181215040c1b03912914451358026003a40b0820490b00c0b0100405c40f000d004042800301419110800c08100ca40b400c4644070080da00c44485070000085580270303218503010380c1d020b60f10003050401564950b41007a122940420404c0b143c62000e1118080302001843c090134038a104807000d020040030002d0007c19408403201424840001482400006640314441c0c080502080c24407003103503129400012414461540100c08001c2400f0800c0f02c00001604847c04841c80c40d241c902c032200e20740c405c00060501460440d400508504009139246100d0103903104144a080d200720301608036080300307100c104a44810004501c0c4c506040c0107428015410b090714100c88281100705200c40c81c3c00044c8424400342c403940c1040002107400150094902c034044803841d01d0402000b41c180d6400d5926240c100b2210300c0b520a0b82101000104000c1e1203060314400d022040c060aa05040c0d56185c0e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 502847841 1250 502846591 502846627
    0x3040806070c120e130c020c130c180e010b1602030607020d03270308070909090b160305090a03030b01050c010203090a0203060c030903030a020307030e03210109180206032d010e0703020f 82
    0x400c0440c410b00c94a01559240d29070311027080b0061060120310070350482c00140280400010181c0d1051a102c4100300841680d02e04d036040d1991b411041e5540c40d00000a104900403102e0082e502d8040c030014000c0c2240c00003418130a441c8642c13000d0061031074050754281d44204c81142a5030702d5404000100c0040c0c8110182d650020321414160343c0c0946407020081240c600000403581d1502403014804902d0f04800c203111080c3c5280360a000e946000c4204e01d88940902d034000301071540307403004040703c3e0f8090b070183c610000c01c03c0003c645900d00080660b50b5140da4500580c042e004440c00b04001c00b9100c4200d9201d5203e80000b03500c0c548a4000c0750303000358030082541c3c08060b41d8500e01980c41000784010012000300030100c1101d01ca034008680010740303040c2d202a10b01846c10b038824101081d018110035485804558a6032a690b0f00500e000642002000e8450b6240c00a09452400c03104442c01038140c0f00e03d100d0144076542ea00030b090f0101c1c86025084000d08505000015400143c0c80308 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 502849091 1250 502847841 502847861
    0x3050d0507020a08041e0f143007090f0b100f0c080a1106071b0b04020409020405010e04141902100903081602041b170903040806070c120e13 62
    0x480362003450a40b1000342d142c01c80d8102c1c3c0121b035a0741151032401441031181c44003074010103d003602e0071441c00300c6042c440713640060640d004030121500900c0d404804004d000c840c02c290b01003400d4041c0c1a03c82548c8408242c003c412100d0701e003001c084054035403440340c4500320001a0105540c44081102031300e1007418600c0f00003c004040c400035000071000000f030002561161204005000e54545103405c10300300800d02000c100b5000d0b400b5414214003c2e0032030017260401c8118a030f40e1601d00124020701b41a070f00207500f25050000002e1150300c3c00740454400d502550644500b040e034400c807a521003081c454003000b00321090030000007610381104050380541590a11000e4180e80340d07101c1909400440c03280301611428650070301981810701484031001c801d212a401400200c2c40c02404164081c0d02802003a07040d0b01c00070b001188104100c0340980114000c0f688103103810f0100400002d0401401c94400c1c819100042704a40105038200600000415654800c0918080ea074001e25031035070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 502850341 1250 502849091 502849093
    0x905130b061c0e0d0905030d020f1c0311040b04031e050604030318140d1b080d1805011a041b080412020a020a080c10050c070303050904060312090e060d03050d050702 73
    0x40f8098052004000700a15180562228205140303068109400c010707a0140032001d5412420703040c0c00e0641c0200f01d126215903032049841c0c0b1882c680104074001c000030040c2c000c400384001800302e000388440c8013600441c3d00c14500d00c0d031886441c20341c0c900d0906240800400c264089004500064082d80250b005985509101c14407450107071210020f445016101030111f0f000b00662a0341d0541c008404107080301006038075201060f00342e6030323840c00d4801c403250b058219030313520701a41c0e0340c0d207058690303030651034005c2c000340a042c111100101c0741d00d0020241c148100d00d0518105a050020750740d944005645403109000c907541c3e512000b068040048200d0300b1030041c10106001a0f540082450140142800600282d0603100a101400000117101001d000092098403107140700000c00e0741c01d5a0b4940b4020341c680388044003240140440381c000030b1000b9002e00e43c0040c2e05921441c02001ca031900000c1e07045a031619401c0c40380000e800310028002613020002021440c4658100c04d4000780248 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 502851591 1250 502850341 502850351
    0x120b15030318010c031b0b040c0503120d05060d050615010801060c080d090201090819051e0712050319030e01150f0b090d0501020304081201060201050c220f060905130b061c 76
    0x80c41b421242c800c42c42111702c01e41f40e0b800e02040c0103000c9010000381100b5001002c2e2600200031504032402205001c41d403054850000601c10346070100ca400c21254070100f121480e081444416050000100c4140c1c0050f020a00003d0054890030400c02d0030340d00009201d140c505500009805481e0031302d07051b0b041c03114101000600240801004201044079004821241d085103059410444240c1c8401499200042c6000700c0391004a2074500f11100860b03550008181413501c5400c5000d240b01c0818003c085600c01752006415410200c070040411008120070364108607a0354114106000c1c01c40740c1f070000c98041c40320481c41d000500b0041d000070300301e2901c1c2d80690f840f503081e81d004960854030010041a003541304105116031a001d01200d000074002c3d0720b880d202910890140d881d03035044280d43c0c1c0791440d604914011813034000d40f400a1841c02cbc210744406000d0040e440c82e00c60f03c0d00580410914841244240c8500c0d40d60b001c0048c5064a0b040341c014034000191265000492401e6552b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 502852841 1250 502851591 502851617
    0x110604030209040311010b21060a02040b0f0d0e16140406060210020d0603080409020405091003080906030703090609050c0a0602071202101407060912020604030e19120b15030318010c03 81
    0x43c1c9140449540d0609231804410031711000d00f414075501400320400306c0d00500042c003044402c0c9050b51081c0720b00800190719046050b0400010705030001100101d03001d10640d94101d800e00c0d010f10816658443c01c20601d00e840001844202c503007a10403103005030055180d103442e850094000780403c4003071720707004520b40c0e440e03440341c80d41540640d000d070107150750020381080f036420140201d550000501ca803c0300701c00e2864445d40c500d40300304c1d11009d01c1840700000040c2024001c0d801403c130140c00c240200035048076441c0031555080810500751081c030a003900080c6043c800614082512400f1484400000702c550902c008184e4a07042001848001e8820700d000070f1824014040c060700601c004105408603040bc40e405014201d046011504040c0801001c29041402d507000804c007520100c0c041c00c0e4041c459050200942c11003a07805903280d001c030080c4400949454050f41d03407007070300c00607424000c42010380d2440344c01100c15254a071511b00d421958001c004401e0b555010b07040108040c00d076 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 502854091 1250 502852841 502852849
    0x180c0418050106030501060c0f030e04290111010218121515180f13080f040b1c09030804031d150c070509010f0302040e0c030a0c03110604030209040311010b 69
    0x9030440c000d5020399403030040045030f41c0750268500402c1181440c0342654030b5519071480031000c00c40c0280030b120709040c4250041c1c54545c8404170513010b00b078005050070000742c01240e1a0703039a045100e00091141c82e52000002041c801c449002c0c01c034641050e44040038000340f201c20700c038031058100a80600300c2021b060791f20500b0703017601c030f604104003641d051b0300f2810410041000284a049400d4115410444103080c05041260003c6810000520700c0321680342000c801d101c0c0c02c0c1e602c03041410119001030a40700c49000b81c0039041c000e021540d01e00403580c0580e42102d40341c50019002680d140701041c086401007c2000c42d40014105100b80103590801003081166120070240f400d18000507044800202404071002404044902d03400d00c1d40340540080d1241401e000107489a80e80d583e03041980d00080101d004414800380030390703144401c90b0520040c0c00e28544030507281818410356180e6540f602d0000c0b2029a030703005090b03002980b15902d0440e803503107040310892281d65a84c1c0945600e951 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 502855341 1250 502854091 502854119
    0x121a04030804030f0c0804050d0c09061806050f0d0b090c040626011a010e0a0f09020c0d05040b1206010c05100203010609050a03120c0201140c0109030914180c04 71
    0x10081d150300c40d050a10f0b10b001020802410744503020010304405840010390000e0440f411510111100800d602d05401d00d031003180320310740c04131003020319268000500e480711300595070002c1200b00007040340035030310340c140301c1e80f90020030000e0303400140d84d10744c0000149890300882e0002c402d10115880111084049000c5035030580110544298030744100c031360784c403100c0703200c41c0d22088d0b1000900204071081c1058502900c0c03c030f1100e060082204540c111904d0340001032005141000401081c6643c442804000b9448504055100d0056864190b00325000d8800c0340c0444080c8004140780503006e5641070b5641002410442c1088409458a800310308100000144040400b41c0103a8a501d00500034000c001b29900143c09134082020400c0440e0b00c500240320f241206091180d284807103840100c844c1e0b40039a14289800c20003280345401d0481c1513203c5100c5520a84030000507940f5002a0316400009002e841e41c80311130801d07401102d42d078100107260050410b4031510f0070552103070382c1c19016103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 502856591 1250 502855341 502855343
    0x201080711010f090b150f09130b0f010501020d09060804080d090f1b060e010905150c06040c0806070c150b0604090e010509010c0f080c2203050a0624121a04 69
    0x552140130040074080c000040f2500002e000c1030a15407440c1c01004142102009030300581f00c0d00c0001d00242c040c0c820452000692940125660420307e0300c0c201074a2801e40a000301030040c452041b0056949004945000c1a60722903142d04a9aa44644c4e03510f40d50340c03140701004000741c2c0320002040010340c3c050031189100d11840641c4414000d8580300e4019a030250300020822541000d81c09150760080344880941d03d080d29080703190386d4035400d0902a48070b01d4070781018500c944000c200034000000382501c2514182010341e4900d03180c1a204a5441c107100380003134070344000a04030007900c01c141d038071507816200090325460503d5580c61158084900442200c10395035124010031203002d00a200d9000c1c1c058003810000b10b18030142030001c1c00c0840061203003c408400091004503070141c4d50440c100503c20448900b038254480c9856920f90b03140fa00c04031101414029038500c0c3d080e03c2d5000c20f407002c04010301d40072070758038108400c285103a11003010780d180303001982080030409074000c0340c078421 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 502857841 1250 502856591 502856621
    0x3060504050c04050912040905151804060501090c050405120a0227090a080901110f0304030f060510060221070206070b06150702061918030501050612120403020108071101 75
    0xa40b06500a10082d600014000d803120380040b01303800281c3c2d600c1b90640d0182e071200c500010383c0381e503282c2c8544400400160403a038080001005400400b00d080e2442c0d1040b44142c10500050341d80d42041425158181c031441c3c00306105101c14082e50902400c1c0784c0d071ba1083d040840740100d1381600440e4a40307656140010410a400121710584440385507115002500c1800408484681d5102c002040c0100d0131102d0400c4008044016844c004200c0442241010300039690341d16541c2c500746400110007081158003c0c00d00d00000c40074031002902000b00c404c50307009009036554414404044071410385207868521010f00005001d40c0780d0a000e031000078451103221601c2d0905408014142c60140d41e0014440f02c200203550060b102c0406841d02000c0040003007074643c0428405030b4200804460803154004190000818407005401181c060b010039a140c541c0c200d084460340e600e039800031841d1103995804000810044d4841c1c00c1403070b4042c250345014a5855044003070780c2d00755400e900b620b17008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 502859091 1250 502857841 502857853
    0x3190501061d0603040f02090c07052b0f0806060a0306080304120303060b040617041703090c0a0b07030203031801021c020c1207020f0d022b121119020103060306050405 74
    0x440119030581c1d902c1400c0310303028110720340340d51010075503100c0314002401070b02500d0125018240042c20350705240d5028090791280102c000310680d142c668600f041208c003a000d00e02c03602c824000e00ca0f0560b407010554451019640324024040383e5401101203108141d5203404c00511400b00384060005843e402d03412609624983c1801002d40380250021414076a04102c01c12600b41c001500c81e00c2c1d00581d07058810f903555203092809504e540f9807030f80300d4014000010420031910110b50f94210030310031503503070420309c5d202d220304115805503440083c0580d00400115a103038040b1404181a10a110300140c42d01000035840d030b0026900c0030081c0e42460b004038134039098400a01c10b00180101c441c0c612420308080ba00080d0112030005645805080c0c0f540d010403d40d01c41072189107410b1395040048142080f40e404080d00d00ca61804151082c90080f104c03c61101e00c0381c03c9a40c12401081c00500d0614500099100c4005145030708a051641d255000000107007e402040d10490294015041b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 502860341 1250 502859091 502859117
    0x3050a020a080613031103120f041a07020d0e0a0f030b09010e0307020f061c0e0d020c030c010c1202070315050114010311030c0d0608030c030325080c0319050106 71
    0x1031030318100d400080032904502d0400801c01500c110440e44c0d2501132602e00e880071180600141144120b0f10f03040030605640c010468100c98241e5941d010320720864640b82d00b10466140004404000d03520140160409244c468107240320740302c1010003103002445910b07519a02d104803000710440d5801103c0340880041000100340003840707003414503011503002e145441da43d540020f05540c009086a0f2003640b000c107032a120f10b00154140d4a50300c1406800300400284030907101d03079401a90400c40014455643d010105040104840340940c1e01a144e0172a6030701c142c0d039800d91004e0344042140440c0b15584000000c101d000e90240d003c011007c000140a5042c130350010003002004414605060074881c501e500072081d801143c1d07102d1400c49011351282003076000d850250110307a01c08802407001040400300c5a00101c021401005038050aa54802031015441c10f10340303844584201141c50880020001c0444200950744440888880c0d403030420501609811280280c0005c0002401c07400d48407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 502861591 1250 502860341 502860349
    0x30d0f0906021c03050c19093b0606070503071b120209070f0509061917091f020c0d0207150c15230a0203060112050601050919090603050a02 62
    0x380181145101420f20f0004101c01c0000aa080d60511410165907800240740221341d40160f6021f404001e400c0005019048001041c28290740280c9c0d02c007050002124510515400100e414500c51103c500004100703d120703440d5410008004d190054000c12900000030400c1c001001d21900c1400c0758030226041c0001c4a070b4440b595002015020303500205200980c0e20b417511158094240d103024101e800f0800001c407000d00035804c400350001c1c004070b801001000c1658046d002d400c02d5641d120030b050712025844040e800141c41d80c00e081d40050031000f074207aa04104456240c180c643c13015190400320b01409240401c0304034000c0c0107030400c4000344656441480301a25128445c81c5c01d100380501d9403a402c02c0c49581282d0412001c0d6605800521811361031030418035910890b00700320941c5000348142020b0341c001c98005000415240408da6035244074450940525010381d00c5605048440050103002000d40300c0301031030750a207000c4c002190450303070040b500510302c51005082515881c0c4188 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 502862841 1250 502861591 502861607
    0x1c06080106060f020c090a200c100504020a0b0f0909040b190e0c121e07140105120a050604061a0d0e0607021903110715021e030a120b030d0f 62
    0x40400c001d059004580f441e50700003400700345480308031001e91035030300c50300c0200780100702200d04408106441014240002280d1004e040d102c4012801da5600c0310030700304d0031000c8440449009602c00c20380d000038040242e241c0080c007140e19400030b51901d0028a000005d84180c0c0407201295107544003010410020085440c51000049846c2c05115140ca072003030fa0380c3c403401a070000302d01443c105412038204000800a200203115404124455111130030f4541e40c48a100340600c0c0e180010380900c8450381c3d4841c0040360030042c130b070071241c0030144c50f0901d43c1409801d002c1c1289030310640b0383d000803540391040c0f500198504100041c091360f41240300e1028041c0c8020648407030154024004000146802080e00d00d0b00350504603c40b00260280d15080d03c024124060144c0175200c2c40601190205c90343c01401d103044039940840702e44620030092018003880c02400045560028082d8200d0130f03010346103601c2a190b401ca0042042d41035074011915210110303d003000000c00040740304a0054000c001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 502864091 1250 502862841 502862849
    0x12050c01062d03021f03110c0a051e03070816021201051e01030b0f060303070b0a051015021209010903050624090106050a0c03111f05070f02100903051c06080106 71
    0x802c000c41c0e207103800040090803489040029011480b00708030640c0d1099110b03100e210000c801e01c58560802a070032558421810301e08440a218100c03640f40785003068502c1c20f205144000081d464100e4695414100c1c0e0012130441841007484010440142e0b01c0d40110207038030700c90100000d003d10300111725402800e084204038003050609001440883c850342c64096010040d064132007070584030b40010901e90f04c1100d40140070f00400005000c0380c0d001542000303010311018040d000b4119210614900d0600040799500d004d82d002c034042031441901c45000c6c04451505040810281c0e540e5250141000c10407506500b4050207440c3e03065001c8a445c48902182c1b005803280b0460758104140640a44512880c20051110035600341c81014411183c550200004805035144d00c00d10b00034422221404510070013180b03050000040c5042e01c1030101741d480c906281c2c0280001400f2011240c01000c0046050302046010003004c03810000054118941d4a101d080010f035283c40c2864840c00c40e5070390b801c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 502865341 1250 502864091 502864169
    0x210020d021209010507023705040b0105031509040510090c0e09010e10020f071a070201050a0b0d030806120102040b0c0c100e0108101703090102072112050c0106 71
    0x800c040c13641e000c005d481485074142c03a10707030070120401405500c00540c0e031201440d025080c5039100c10032209800680c01c440068409001d84640c943c0107444034081220012440c8040c80b040003014503011a6468225018000741c801c00211556040181c0c0c1400c00300741c9031141940c00400c4004000000940c0c4150004020400b8548411404d6150814500040d4005801140040c1d011129000725920294005c1c10001420384461b00782040d03a500f04c1d10940036500c0c282c009140c03882c0c28090300042c480c0040000c6c201044903a0b090719000009403034140c00c58000e288140d1391000034801003004d011700b001d29a4a5420786841c40d0301d44001d999855026001ca0001c0c02c014640003030594031042800d0034040910303a914403000680c2810f41d80024194a8801d98206070301502000508041d4001c0c0c0c203540328152034040348000102c600c0d9102000400c5c1d601c034240400c4080300e45022101e82840c1403072500300e56900765800d4641c0b079002040304618040070400c0700b0b20040a039032031904d100d003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 502866591 1250 502865341 502865347
    0x91106120408030924010509361006080105060907050f032206090b0106030f020708090d0519050606040c110c010f030f0f0b0f0913020105090d0210020d0212 69
    0x2100c0c9260980103000184280c0303002c404a40004002c0c4150340b0b00880c0c64017404c0036040805140c0302c0540c001c1c444d55006e0b00d1a03402180d00140e64201d1903402030010310001901d003134218102c8000300c0c2e035142000c4850150000010702160b150081400410360507001160a0a2002c00c00040b120003a240c401401b004004101003041c010054070740c00141d44045c401c2c00f076841524044203981c4260010512071501081d241044070081c103a45c181e5907955003c1120500741c0302824200e00c106a0090070740b080c10700501045242160903017210740d00c280141c820a004080b000c0e0b034201281c0c0d504850541080040055504062013850800000f07454183c01700c500590305a521116034001c0d00e4104000c800056450034025040131000c2c0d4101081000321f881d0ba1045000100101d01d51a40700d003000b480109e11600c0c0164495005100b062110a007540d207660064903154400c0c55003c3c0c100000c03d6040025a984480303580b590100c5801910811144a8000b0305140350400c60404d0310f5024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 502867841 1250 502866591 502866607
    0x2206081e07030c0e12011a03150402150c0708031c060e070c032f120a0f0e0a09020f030703060512120d110c031306021b0d24091106 58
    0x444815500306403607060014a10070300c00c1d421a81340f82c411070015040140141e101035102e10560003140710031845954000c010081c1c1003056262007100801001030440c040109001d464580321080401001c1003001307140c110021802410005940c0c403002c40707034001007000c2c00c9040300c0c8807041000c2c584070041002004d08200c40020500809000c100400c2040c0b524241010300170881241d00b6503044440350925a94210008208424000149124002e4140002c05030218006443c07801100c3d071a03510103105422012070308992810300c00e55100c4424000000e2a07041c42c40186004190b142c00e203070341c901e048003000d800e07511580d000c0c50066407196200e80c0c0c1c1c900080703501d000701001c0740e080075034415480f02000c0140c9140d46006402c00000607030114016400001040e050f503018014401e546e5a0301c00680e00c4a08201184625401142d6455038034581400c1c402c1e08103100d8440444c076990340c3c22078042e590039500546442c1d65607410240381801144020400b50340c00841c5ca0600e04903203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 502869091 1250 502867841 502867891
    0x30905011704060e0a0503040801090c170601120809060f030114030a0503041e0e151002060702060a0f14070819050903073306090b0d021014220608 65
    0x2040502001d0381d0304090313440a030040c03000310909038001003100d440300d490b0100d550080100400464003c07200c2e140c00200350200c810640c0000042d031014000d940e00c1c04c1105101418900d2003143c45a13000c2000d08125903503840036041c0700390400780c09600d82d0306140a00d0044a0008103507846940051001000220008110341c10745245407841e0184202a00040b80b840010750400c408407444c0008100307845205508460f90040100e44101c462411000c0698942c001034406400580004001400034a2150405114405003401c006090140300040f00d84a25040d00c84070000340c0c18109000e00500001c8518441000824041005090041e04241c0d40d12030000002d0000c10f402035288486d100c40c1038900b204107490010f10b410015161041c500a0103c0d0142c0618a85441c6494015003402246100400d9000d8404803002c611501d0a44519081003407541d14000d0400400900b000030301c8503050176100c94580740358901c0c24240d016101410041441e110301002608064903910 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 502870341 1250 502869091 502869137
    0xd020a1d12210903030d050a0c08040b010e06060f0a0e1e0603131a1918030203120c25020f1516030c20030c0109061205100302190303090501 62
    0xb00c1400b01008185014080001c140140400584e0601010a44142c814003c0c2c101a200d1100524108040900d5480560304400107541c0030303002d0b0424030010300c52280e65910180c0c00c0a001000c160504040820700175087c0c1c854456400095680c07002420320341002d100e095180c1100ca46d220100081c1500442c1c1c20780002495403600140790201682480008440b4450003000304048107400e01e07004071100d02d043c01070340d43c840c0800d10300307000200004e4200018038800b9074142d010b54602250103050444200024000398411681088040e04800c85c2c000c0c030000c260103690401031900414010031440b86c914140b000c0c001c50042184510840301401280c00280c0100e40c42c501649090a0483d8110900d113001801074250b001030070b4507902882100075155201710203c580c0c03000d1803401107403035550318450007021543d6401940c0100d10f40c2d4104681c4420b0541111045d2a66034000554108014454082120b01032005105042d031011a48020307060070b0909000b410270b02401600c08070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 502871591 1250 502870341 502870363
    0x1080c0103020d02040b03070207170d090303120f0509211e07031e08010503010e07081c0e030d050a080c030108150c0715060501020c0d12140d020a1d12 67
    0x69002503e031030046580d6044e1405000180da0703071a01c926112102a640e06c2c91400b0f01d6801903141741864540001c0051154407440040c0d6411054a185642c1540e28180005030302d03640c1c0341c130340394240c00c054200d00c1881d2003441d4000050aa00d81c00d1036070040020202520380da09031904000d510b980c0c0f400c060008110310000c40c096a0f1710080390608075802c0d084480c04880e201c40800b80ca0303070201d0b030140010b81a910120000c024015001d213a495851800d03100c0d140c0c050700102000000e02d150514100d2a41f691410284609050180000d00b000750140318880410404280c200c0032542c403d0f20b0341d9000c026405090702d9941000840d03580c2d82440c14003003441a8104000404c181041000e550140382d000160310a860701c0300f402800902881c0c010640107225030202010a4030701005001a01c0c1d401540b5902a0942ea11084400301400919600da0074403c000301c112003521440180941700d20f966070918000d05c00001c1d07582d2220026801442407007031001d41c1d490b040022900410f04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 502872841 1250 502871591 502871597
    0x1050d02100c1502030709050303090d02120c040e0f0607020a0503190e0405040c0801052d0a1b02030c01060501050307051206191404240b0901170a091a01080c01 71
    0x11078030404044500c00000c100003090504502020030f0920321035005103015010540307413020a640c42e6000d140ea203014910b01903074003081c2c1c4440385004d0b0501c0415510455583c1040d102c8011610300800e054403110404c030380d0a0342c071645e0007a0030300d00b0900510390422a144040c0171107070200c7d10744507070320302508a408900b0100043d00b05591801120865a0361501500c04e03c994503190078022070301d02413842a070b192542004c2c0000d4890b00d10a0b0000d91a01c0210464250503105810714216100e0007040c034600642ea40c101d6019482000700f912680ca0220781c000d40d81c0d2542c81d01446c0c2907030026884981032080600a03c0381c603a40000c1514200c000c401c0d0100415540c94000605452410544404803c0b04c035801143e07070162071501d008003c1d0240d03400d02800031149100100c0420709814444180c080307400030b01a0502d104020008000c0526284030485440400000f03105029940c9105140c0e50b40c4010341008440e400e000c8103c01d04041c44880e56140103c280d0302e681c5464919410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 502874091 1250 502872841 502872859
    0x3120a050705120f04030f020105061c05030d050f0115090518070216080d08010e070c020d06060e16020c04050403022d010c030e212b05070203030a1401050d02 70
    0x8081c2c40780301501c110715611000b01da03880c02c100d5000d294811044c1c605a00060b81290009801c034014028540500b0001e404004e65580200c6c456501a42c0614101d6550008108050004445000d103c3c0584601c20111041e549000c62184640d543c0042e41c03000e003e82040104500da40c0c035012000f8050464500e454144d580d91400c90a1012414581040f4200320101142c000000100719410302c845480e5038105980b540c41c1d001c0351800407100380c1e0001e048080040018200304a80e500424845c0c500854680c0d01c515409070300c200d045070b0710701a44c0b04c03510581007a29410000001c07840c1e02660204441d0402e500d0003500c4d00300b03051045580c0c900b082040c4807000303100c086803064040c1c10402040400988840140500400c1d6060040d80c4a40b054121507482505c0b900c0d0080c50f1214012450180089401b404800150403c0f807000e45d680b040c030008050f007502406101c1c0e00154044c43e520b180882c91002161400044210842e001d500148a00c0c0c0310000c069a00da5012210300340c5c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 502875341 1250 502874091 502874101
    0x60a05040216050604030305062112130f0305101b120b150705011433040608030d0f062108160f030e18071d13020f030604050903120a05 60
    0x3800c40c0504200074050f10130b1000700030505a166104500503202140d11410f0040c01040485801c0c4c420b1030f42c0a61600581c280b85103020704030000f401c0c50352900a03008001581c03022840509182c0c0c0c0e200782c0c2d464005c04448c10407900d0502c00c9686081e2001c01d0700949107070181e0b000300f030320f00d111004404a507a9507225451a6a40c1c2295015500c6c1098485940d0712503480c150f406014030880c41d9041c04545c00204035905603e4503000c1d18065610803030341100012080e526075250034080c1e403d0b0002e56500313000c600c3c1c0c0018030081035010f403148000720380042800c2c40542103c016512801075035100005800b5102d2414568444580c1c210100035180d8442c4c404801032b4480200d002010034031031808000c01c1540110b40c49003880d10854104c0307080d00440004050462086840c04001442c0f03040040068100040c03404030a80c000d00200d95041201000e1001c03640010681c211444020042000903d410300500364012503002c051800c20f48100795500007501d0142810700f16540f6440007131 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 502876591 1250 502875341 502875367
    0x52206020409110711030105010e07050901090509040f0c05090c040b0903070b0c0708011a0a260f0f0c04020909010501050d1116051c0207120c1806050a0806060a050402 74
    0x103070151024031002c00103082c82e80d202e03034807950040f0021900c5610f406400280c503d010f1040d1412220411480421680c0d0131104039410360081c025141481b4981b500882c8039228021494401d600c1214480c80c1b1003010b080c00443e01d0b0043d4480751003504050300b00000150a04151000c07202018010764461040e6000241064695003000d14030202c041000314107240001ba0700000c03107151b0340c002c10011079400c0c41c4101d80710001c6180c90700030700d11400800c01c041c0b0500d204035680e003138000540d025109480d20141000a009059400741e8030600d030080c4201070600c40e0048040702107600b1460001d47c00d0120300e07409014410103050103004207151440400c60340101001c00c2c41108442e5403590380102e4080e40c0002c20340252264807a0f502e0544001d040034108001800d0150010314400c0c0c50f0100c0c401c0e00003604001100c0c0d4000719500000c40c54090782c0c400000a002c1000810325905000c1804001d00b102d510810490b8000420f00c401c5407603813080902174410540d00543e564550fa6581 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 502877697 1106 502876591 502876597
    0x3150218060c0f1b1008040f1101140c1c05120118090c080d0f02070b04230306040b040b060a0e0c0d1404050c011205220602 55
    0x30035458180040c0c000210540c04903029240c801c00001d08050700240c522001c500f111030340803a580707001c1016a0f01e1460701d140042c06071903da10381c2e101510840340041c10030820007810000d56441480628030586400c103201b83d0701d20202f0421903030343e00c0c0710060025070800500d485498a01c2001190f0700402d514210309900d9080c011607400d9290030344001d080c0555144150340010340900c0ba96401040d00f0343c0034140ba10b031904e030040c0000e00c90388041402c40d000703d2818003d0040d410155010340c0c0d240003900b000218140c0d81040701001802c141681881150208020000101203061203107100c1c180078030694a0f000c2c01d100d8041150300a640080105c100003d00003070312a0b02038120081144401b003440d800d011200040c4410503982900d498000c40e0703082d00956001140300c111160000400c0010345002a403403022200e8000b411440300810701c146078140200d40d015 = true := by decide +kernel

theorem cover : BRFrame.Cov 502697841 502877697 := by
  have h0 := BRFrame.cov_init 502697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 502697841 ≤ n) (h2 : n < 502877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
