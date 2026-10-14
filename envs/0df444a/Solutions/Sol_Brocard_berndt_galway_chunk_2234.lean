-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2234
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:28.563075+00:00
-- url     : https://prove2.me/submissions/b575a900-b458-4a11-aae6-53d0a7e5028b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 401618705 ≤ n < 401798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 401619955 1250 401618705 401618729
    0x1e04020a0905100c02090c0706060b04120204110a02100b1516050105060d020907050309070504110c010f05070c02060307020f031602030613050d110a12020f160f1403160f 75
    0x2500030100d40780d11030344602075000528540803401d0071180751f00519449000c0c80780000c01548680100b1019800307984214200c0c0d02002c03002d4150b21b800d00c15055811020381400340f03016030b0814065200c00e0b406818414a0b69252109131058031440d80e040c0144203107284903130350348081c080094038040319040d0550b01c2e90728040000c1d0050410060990704950014042d40040e03a50380340403074103580001e01c1544a40111100040c00d51603600032035502100c5506000d448140c4104403908559083c0c0f107409080e810716080c4100b260f0042c002c0d1410a0701907810750b660b60f0b2865402c0e45408000e401c5480c06120001d000800010a242c07001c2105108034141c80c019100c00011420440780104080c1c460707040f201d10382034054043d01c0d5500c440700d00701080c0c1d4840030036a20307a0000030440c148444007680200102d482d0160b0244160089907a065070304071519820004601c82c8880c0c01c0c003500e4201c0c1002d02030030b00d203541c08025503a81c468030300201140c156150100b01034100e0307180c4521580090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 401621205 1250 401619955 401619979
    0xa02160e10030f0203012d29150705070e04020a060c0308190603080f0c0d021b040b040908031003030f020a0308041205040512030a0212181e04020a0905 67
    0x2450400090040403074804810380a0b040d91660300340750a0a030307401c0741d242d0343e1103845158401d904001d052004001224004201a00100400030b8850b0000a0b640e0740e803915000f052100300d05480d51005640a80b4800100a0a062500c60364481c10501030000e2055041c00210308842074580340c81031703101703480104c4006d60307404007a110b030701c2c1140c001030207c0e0180700050401c802c2000d00c0d02140c0d02140c000325040c3e9582c0c03030f40c00c0d06501c060045640c0000c0040e905007448000c12112100d04003510082c03508555140e40388011a294580180c0f01315281c44940d034a955664008250b85074110880b680e80e410700549074801520a440201d000c0351221202d0f030301450001c5403528200e034241d10741d1724050b9100e90b43c11849500c1c0d503d10805102090001090940701c074016400a6809480299581c0c4100c890280c42d00d1004455000c040d8000c001500101010810740303a001e11080d2000c2000341032501513204003101000160303070005e00c0441c6040720f55a00100c0c00c400c584003516002550b02c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 401622455 1250 401621205 401621219
    0xb0a201b0a030206090111010b060a0c05070f0b03070c0c050a12060507020102031509090a08070305070b1003022209060c020c010815060a0f14030406091e030e100302040302060a0216 80
    0x807080c030000c0c2d8002000d10078a0040d5008100c1d01103c050450300003d03c0c400004005111138000e100740c40c00180141c050031040100401054000d480d14036030000e8103038038044007058640b0004041804100e5150100f070200140b05070100040d0000401030102e50382ca92807420078a10314600250344490416020034070941c01882264004e590070520040e248240c20103100c82c02602400b400064452031701441e010410030070140010500c669141036440090781000300804001a0594103100c00c0d078030b401c000680d1003510484880c1c4031180307800103940c1e00301d6050004044040001d4601402d00d42d00c24a05607001c47c88928140d0241c803001c100d502d40002004001503151210754000c1000c0041201480c05800340244105607071400210000c900ea20401441c2c0040d502110000c0d1107105640402c8000900d840501c29000020868030240c0e8400600e51039004040318014404c41c500c1c030303000b00d210340c04483c0030710380140003a5610700c01d00100039901c621202c3d54040b10b60400758042048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 401623705 1250 401622455 401622469
    0x50a1203021006290705390f0906030c0d050f10061d06032b08060f0306040b0c070209010f050a0b1c05070318050105070f1106010b0a201b 61
    0x2942039240384e649100c10040e070181c820610610311410b9a4418418080000c4040083c2000300034008031455100d180300c40003210302c02400b540b050314542040040e15240d00d480d080ba5180f002c040f203c100796a1070f01c0700800d0410030400307025a000b00c155040c02050100014440740a038040c40d04a03501190340c026001d0480d6140d00403d43d041c880012524a00024007825642041008083d41e04881c0401d29104141801c485200c840b190550602d28800b84c21a846541c000e00545040e012501114006030315040e001707200602c02000280843c800b00000802c2c0c42ea801d9024108019950315000c0c94844442540309140c4034007141c420215094840350181d81141c440030071240ba41c0c03ca071f10110030203403800803ca202010b65600d45034603e4860650f201740150f0249000082a0800180c007c00345441c028080c0d05001c1c0d200d282250040c0009181070443d00390b10314060701c911443c07604846d01c0b401002c074002070076200720094081010101d20501303e4140c0c002d207200c004084d5030a12030f80c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 401624955 1250 401623705 401623709
    0x3020105031801020412030908070905040209040219090f021806070201090b1804090b060315100902031b3106050a030b0103060503030412030908010506090c0d06050a1203021006 78
    0x14400d10110750489100030b820310300c0c120180005030401e5101d442101c00401c01040c150002001c41c40b0401c02c4039400d1114038050609440f00384007920f4550085140d450001d0002401061001445880a400703c0f40b246c02425a28206102c00c0700e40343c075100041d4200711120380d40800d42100300c107080d01d001301c2101c0c80e0a6040e11503401480c5450204815600003000705610310854400d504510760f25881004c10b03452180b08411042c4c02c1c000185442c1507407080368201e01001000074408400141c040400c101d400c22500507030360b56200054419903000c01c990400c50018085805403007100c00c13081c1e40f049030203a0f032071060148100851035005240382d0702c01d5401091003080008611442a0407100ba8240181000701c0c1c540d90743c80c0402d20310380c41544225803100700788413404205644581d00c0001040d400d4000e00c55414000c000910307980d40030340007a035440c0000079820b40410321500f2a400801e0700505400d40c01e5910b82000c4031000802074100c0040c050340c5480102002030384210b41c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 401626205 1250 401624955 401624957
    0xf06080f0703110105072919050106230403020d0b1b0a1709192003030405060409090c21061803091412030d0603050d0f05070807020d020310090507050109030201 71
    0x7807540704100159030710340c00000d06582c410480f9500c0440c7d8004540101d0300085418040e8103c3d01c0d00110200060851121400c44541004010410a80e0006407401e080300c015005040011998211013040d100c0c51340000c2d005450184000203120601014504c03a0001d581180180d0310302491540300c42c402d803240100450b803e0068600c026698000603940820003804440c0c44441416003160003000c110b804540e003c0c1c0700b0460344201c01c4480341c007000402080c0c0003142414208000584140910f000c0d4400065407104004240400c16040d4401416a581c1ca2049000e049030600810b05640000b610f419082c814201402202c0005180000c2c3d015070302c04d100c40c1d003008ac44107008401d4140312036000d802944c0c01220b0600500050030301e01c81c181c0c80094040d00c1c0d8600141403007000000d110600c0501c0c400017003015004411070f982d40d5800710b041d527514400c500c001441c0030ba004e00e0103034140c8134800c203484000e96075a0000d03645034026030031107a03070a585000446200340d903400028 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 401627455 1250 401626205 401626223
    0x9021306021f0903030e06160906050f03040b09010603080705010c09050105030103080703121b021b090106120b0616110103240e090c0316150e0a060507060f0f06080f0703 75
    0x641a142548543d6600c1d10a18020403d003184800d000e00c0d0900a503a203100c0801c00c0d1040081c40c1c2d4005100600806580c00e06500700034944071680c3c4117002c011300282409010000080380799100b0344c080c034080d540c000d850303a884560074100300d40200310b2012040c0100ea012503022880c0d60065050700d04995001100e03901e0706140765011956585c100a00344050390301c80e0140c1280c1c2034541104102ca40c0141d0080034041c14003e0740790028026400e0241c00703640c0305d600612185070b1160400c00204844900480d07001c40450106290303208058102c01d000003e0144074082140f0440c840f803800300c2c00d0364280a41071007003c4002340e4156034140f541d90344012582c2085001540c1f40019440103071002a1038a0840c58004030b8103080410f49007480f80720300707510280401030b0b072180c0f2046400d40901d4086404445030010584d0b81420b402000d05000d400315502080024942110010000c052003d01402c00c0708048900582014010790500d40129243c02d09800b1000a42004490300b20006d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 401628705 1250 401627455 401627503
    0x3060c04051e060c0309040f02070f020d050a0503030a020405040c110d0c021f0c030809010b30070602010f0b04020705030a140d0c02060a0501060206070c02060c160902130602 77
    0x8003000c0c101a82d98034001e030b4441440195120006000724040c07580266540d1706156042100b03d4448030780c00e050452041c400a000b0030460b030010701c02d456050307407102d59030405410701500e07107540300000803d588400400c10013035103a01d0300508101c410903241400000d02802d001c4c0c41000f0b0302140455240d11a0003281d91503481840000078150002d40b5120030880e8803030564403080d1199905001007032000b10b10404055002c0c4050b0340c40081c40008200c0343d2201e82c000380100306861501d0b03004001001000c0c0a10035040440103032004160203d4400d69602c20000c0c0c068690494482c07009403501c0760308682410700340200d6040c0c65004004e103280004454042e1810002201100420742041c0202e0b0911400b41c818030150f400107800410070361a1201c3e403c025950141c10803030440d00510300707004032070b5080362007440300e03540c100e9281e42c8a042244c0c180d860001c680b00041c03c2c1c441c12581c00221114940c0c0240703d503918800e100f540c4240c17241d00a07a5180071030407400340040104a40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 401629955 1250 401628705 401628709
    0x80d1b020a120e010509060c010504121b03080c0903060a1d031e0c120c010f15210206090a0b03090d0305071b020f040f0209030c010311182b05070503060c0405 70
    0x20301e070341d4001414100d0a00e11b80d43c01140b80c40e0070141c10042c16079076510511042c0105140c22110847c914901000502c040e07501010034140002c1004007484481004211040c1a0b0000c1c4c46a00201804a030082d24008104102800d803454a03c0000c0c40c1c5405410b046550101c00c03589000c05c500c1e2039544d803007a488480b54035035000c0380d801030f968011101400081c510000c02000e29900f10400452005801d1501d4011104507041e500410100408100a001c603910220003003070307035207007002003501e400c60010410602c21590055031200c850f000202d00592154041c44c000e00589089480107503219000341c00322041554444041740e1003d100108021030941d0800c61307540b020b0114190302c940b440224040d1110802d01504585e004119080c0300e0a04000854803c1c0c02482c0500000e60032803200d02452291880e1640310000140340b2240070b03194011012001d501d4901030040810791400103280c0d8a1100701c04440314040c140c070005240c5000110903008071260100c141c542864101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 401631205 1250 401629955 401629967
    0x1180b060d02030303011e0609050f06070c080111120a050702060f070c1a180a08030a020d150815010e0115050d0b0907020706021525020703080d1b020a12 68
    0x110403035001d14041c4441d001a2014000b4500a002c1c0d912a80d48a481090070b10340580d055400c1f423410031900550130001955100c078061a0344070240e4440790344038003900342200380c11a03c0d00958007540c00c000000706894485001810140c04680d8031600c81d0b01c45c000c281d001d4820a507080d6006030301100c041108400303c48011030f040060382c20211800800c0ba40d9051031000740c4205e800608500a0401c80781c1607410006000040c0104058000740440e1345e46c40c401c9000281040400a5011842030646442c40d44040c501c0180b481da00c489482d03545044c55a2995045050303d041c0c5101c100025206441070560340c10780c2c0360300344d1045c01c1022006080320141c2042d00019030341521403591207219110140014024041d640c05005036605081010f49003c06903110780c0c90014294003007094503d1400c2e002c0c044011080d1004560101d144003c91034100640c00c007400c0d0301c0b000030341111504595030000c0f520121110703200d50014070074030040ea2103030b40c1d103407000e001014512030501f80180310342 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 401632455 1250 401631205 401631211
    0x26090901030308090f0a062304030f0809070803040b09190f150e1f020f0c011b140d03020c01180b0f040615030804080c06041a0d0207020405090d0f0201180b 69
    0x4454400303c217000198949405010f059480a640c0c1c8089642d6002d0340c8481c40c0b0046d80e2940e50402410a5038008000d00103d0020200300034024001c1140400c0900c0444000c05684007113035141c40c1c907501041c51992000241c0c612400007021281d20405281c60b0303008c210741030032001d003880f10b1403d1007441e1300c01e159400050801000c002c998229030b40f581082221030030310525112208224204c042d1170700340c01c00e50b03030012584a005020a0391f03038005021580c150512805031454210b5140544059400e4000018075024500d00c514241e075040c1c2c05000d915440c2c0009000d07146002c2071400f940c0e08111400340a0324410000603040841130b10149410510807400095417030741290541c0c0819540c3d03003049955140000741000720b103030104410104484202c400520346413400d5804200701e1034041ca01c2c511500003007800341d00e0301d800e5410340c1c10040e00944103000340d1928070600750710f4024110036940419440e400317508180c3c0c4140b003580358102003100c1050103103070310f034079155540d18000b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 401633705 1250 401632455 401632471
    0xa060c120e130204120314090f010e240c07120b0105041a03030301080a031e0503161b080703030f0c0e120a061a03190305030a11070c0326090901030308 67
    0x2000b1150440901c020001040d110021400040c400e250080c1422038284246001d0f810910050b54599070b10f0006902e5440709003090121025040042441150300c0e400101d0b240714501c2c0e440303480782c81c054010030070b40ba000c0d070684a8aa80b41d2904040c08481060003030200740f12000140b00f2402c0c140c1c4100003419082e441c8621307140411001030301e1036001342c00040c140d82181c940c0c001055081000c6a2000303e089a032526030b1850820010001e020041029030b110390340c103007070b40000d90180424800c08202082851b0a140c0c00d070038014055401008100c0010b46006840700100c20244035144082c0701541d141e07140100c200c01000400d203404280d120040c0101084d050015003030303100e4010031300da491100700e821200c80c00815040290781c3c60400703205c0090040c0300f030009502404480e4090454400020962880007820205018080c0c0003400c66014040110034004001c401c01502170b10181844071a61807a02862070303c0c0905802203800c8000e407001480024044d4200c0e0781d1022301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 401634955 1250 401633705 401633719
    0xc07080705010627051e0606130803030402150a120c05090603190b010c050303040b07090305030c0604061d0a060509011107080c0c010f0f0c2a050a060c120e 69
    0x558030381d0790850310782c2d51011036901001940e90b4000340c1d00050f50320010030800000c0003e4986080b0070650080502101c050300608080080d182c0d0780c0d21030950380100040364402031016211120680d407640255001d034429281203000001041c58401100c0c180b03d00c03035490300c03284141f885460b4081c0044103201e80610030144103050f09031311080050f62080300604600840e5549040040341101c502001440c104822a0028070100304000210b075003142e8040d402c00c0c150740e41d03101c007210b5040c09504010068040010101c5044400080d024003443c050201040140c8a80714203413409101c100048880d5000407810101013545680b20507800395070140041013048000d9282003a5502032b5004484a5038007043d0388003103400c02c1240c031345003900a00304000718104425010341001d44071410002049035011103907082000c00c0c05003044c1c5450728840c1450751807004036040c20b0301425005042c0644e045e4440061258400c040c81d040d1150007074030150344115080d804403140e4030707048603403900f04c08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 401636205 1250 401634955 401634967
    0xd03080907090c03050a060902190e0414040305090109140a09090602090909070305070605090105042702191b0b1611120702090a0b1302090f03030315100207030b0c0708 74
    0x5080c0110f6495850903a00042c040c584020000d040702c50940000360900c0c03042c01058180c821592070b1a54650703450401030b00a010504c005400390920401005803010203406020030190040003801061809807035044d0f08940f18944001c091103c02040c42d84604410760402030640b1641c0600c0c0d80d11b000342405813902d8100d0f0007107013120300c0c01d841c1503040340d0010f001001440b50a02c8041c02814151070401c0c03a1580c0000002c01c00c0c01203000380100c2040394900c03641c140d810b003500017220030301141c0295181d04540c071160b44010302c0300d400400851038130340505200c400004016003040c3c0d0300c10b590103601c0c1c840f0501d0055001100c1040000c0c401d1001090050140c2042170310310040b40801c50b103556002d07a10501109040141115107107600300300092555503134258802c9030000190500580312803041f400500100021181550140000414042c100c4a080d0300f14880d840242c500c0b0054900105040b40d41d86820711003c2c205d003250b000441e45001c500b80042c00c120f40a00ca8044c2005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 401637455 1250 401636205 401636219
    0x1e070e0607020a080610150c060b0f03060117010b0405130602030601021f0501150c05100c0507060509070306060806041a07090305010e060106030b01033b150901110403020d03080907 80
    0xa42d0f1504010965807110701004a88248180c411001c1c01045000e00d46001c001c013030181044144010081595480d00c00e010b2940c5c40d03c0400083e440b90050445e00175594403030b0a00f842010891600c0069400c044500c4080d041c5800ba141c021f100700c5000b41108881611150000d41018102c03e0460080c0c41000c510540c1c00c0c0329200754114600ca0004455241030b02d06400641000010300c18041412090b101280000c1040c00718521508800315910450315012110381c8100400103144514010074040f91160000322902a00d1103100b042210b20f071611442036444804403002408002090800b40501d80c000b003019410510b60300340104050303200e55031a82501c1e40d10a03035000541c0003200401c00e05a050084240035202070808100200c091046c0f020700050300709401d55501400c5a17241e01241050712048551160f01003034849030102e00c4c070840001002580c1c4030b480e40d800c1401c0b5000f40c94030001140d0407254020722480600d10755030b40c2500c0101c8020324412147c01903050000302c103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 401638705 1250 401637455 401637469
    0x80a090f05100203100e190905011d030403060608031213050102042106060609080a14120f03070206241309140f07080601030809011107050402070f02091e070e060702 73
    0xb82d20044805070312454074140301303d003070201c5511954240e103444042c0404d020140c4140c40d001d0000642c04581e400260814038054071410300c54244080340543e400b040c00d038000c800340c420341c1e00c40e84c0b040c000e40f62b48403280d0b5a28007982d2803000740c00c52980081400c040e11010601c2107203100b0400035007480d0f0b4842010302400312000d030301c2501884c600004030030801d50b442984041c0c8540e0034425241414440007a42e11a442c0b01c0c000c20711107040a0f0b0b0300c41003100f00550564800c9400d80550f9548520b8660645a001951074201500c40c54020855041261041071041e03040c50003a5921649070404010f4025003607a02c000400b03640d4180c8001254103400e00c071a440c00030784000e0100710a06000301d8a042c11981c02070100d60031910050000900038000c030780c003440091a000214656402c03416003491103d07400258828800940f00d1700704420b80b11440001802202d0020403a501c0441e5010103065035480c94122221001c00545114002d035040d0744454000781409007000c03c0d50380410741d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 401639955 1250 401638705 401638723
    0x3090120070b120f0708060103150506040303020d081006140a030f060f0f090e0601090506011205091b06160b0a0b03070e01170304080a0b042111010605030d080a090f05 74
    0x80120000345680d20b401000d0301c10390003982130b050801c1d103890300603030041000002138140742c10182c5480301c46410300d00c6510b96401500d0300810903030382c50303a691501950701d91941035005c1c0400c200c0300024002e807a40494110845e031041d1a0185001c0d41007004625a50101c0d154070185642d5001700c1400403858420900544000d209128845040a48020010b90507030301400d5428103102101000c80008114141143c0a580010900d92a2600140c5401c0200c04000000314548401c1218440b00001e1084003031142009540640f5030090078403906204140b980025062400940b50005603010078443d07001c2e500400004c1c448900c100000d0030111642d1008421400d488018041e1085540a5040d00d20502004514084c540f41d903940d10f5114444010b00640a40c200180500030b40500a00c0d800116024040c10321a40ba90080c180c5c0203c558444425881d101011526050001300154010844d444048569403810800c9000e42130340b0908071400c00c1c601c2d280c0c01c0022130400c04111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 401641205 1250 401639955 401639969
    0x5040b03070e040605060406050d0f0e0d030603020a050603060d120203041a1806131401050d02270a1a220f060806041401031e140705010809030a020309012007 70
    0x7020b09440003008140c80480d0095403261404000402000d50040116210a00b4401000c00c01240300000b0400404080402c3c550314020743d101c0407003441d03041c3d110b1001d8a208132a0031040c1340c1c540c0d0038001c0602045030380b141c21041c501e1134800454000141e40d407a251481c4103ca00d85512140c020441103403299103440840804200103017601010180740144041c241c5041d8241704040b030203440100c0072403040d00e5444105003000c20300c40c0d2090085484440351384030155910418020900b824254042651107a04a02c2c809031307045182440100c000c407510019008100c1c4003602c0381c0310031a4018504050304c00290035a164800c00d282c25185d005001c200c3d8060405450204043c0800f5070080c00c0034801c5107485440e10034507032940d810b541520781082c80e050000f101d2003030810003000321120186c440d00d0010a640400400000e0140641b10300381c1e50208642c03545803d5540da80140580600560804d10940300300354400e86a83c14039880c8a1960307908004041211070500c85950441c0d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 401642455 1250 401641205 401641217
    0x13050f030c07090908090613030c0e090c0d0506061e040606020303191b052a0106051011070b0f1c050a0c050712120603020909010207030e090f041205040b0307 70
    0x40401c41e0501c5030000501907400244003007000c0c0e40c4e0b05002840f48406a600c188008100c0480c040c15002e0a80b0180d54002c8081c180b8940364541c0c100550310841d40e1310b00c81d1140c21003805141c1803080c0f1501c10300b50720030000c00c2c85480380f50400c4021903c8905070456030140852040c2a1340e44da00400d4020000794028503a241800700404003245440d01626045505005003208088240200340c503026140b4030b44291580030341284001301a56400300b031885410001d140421400d019404074003103a50465007a00010410380d42078440d40050030420a85030084482042a119010010310030100c1d030880042c075003842052280100600400d0303c03618a5031f500d04100351407241c0d10a000200015051081c02c125041c2e80310148489042c4085003000031000b40c0704c554408540003040995070040641d101450401c50b242c1c000c3d0003200003500041e908000c3c544860500c00c958900480074a01c160026a9954444100104110710303024104001004005a031468190195014640560301c3c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 401643705 1250 401642455 401642467
    0x1115070807060501080d021c111b211e01140915060d08030a0c05130909111008011406070f030509130203061c050102070506010303120507030204051813050f03 70
    0x100480750141c000c268661b110402c1c4030440c035000a40e4072911000c040c29890b210b0b20f032a1003280d00203000c045071440c078400d40d03180803020182940310b200141d1040d540206a0360740b0200d0082d0408683c0000d0f10960018250070f0100c80f0341c081107203600c00d241750020a007084e44134507404c2d107540c0c210744040c166005281400760384501145401d4100f40202c03034140c2e40300d8603900c4082c2c0038403000d00354494041c1d032020102c0c0b04c0e5000c0d10903507007820001c40441c03180a41e100c0710340d4040e0101c64411601c008550000504030b01d4820341c0000800265910b1f409103070300700802c6a8109403480181d6900c010188a9080000c500882c0401902d100c0c2e070f2100d841d006a401442009541c0e0170714071002d01c1c0144208012500c2d03907104011106100881400d840143d03081040c0248640c500141541c0101000807080c55000421217038030f090251001c2200c3e60f40c04904404034044d5001d11a840381ca90b4034448104030380e40030400d400c100d240514542c1111a03503521450050002440c01041c0c2000c206 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 401644955 1250 401643705 401643713
    0xb1507081201120b010e0907080d050c10020f2a0304170d0305061e1306240e1c11100807030b0a08060a020a170901020915070b01031115070807 63
    0x1c16401440359498691030340000d683c6a26004805006000c0c484e41548005103040c10100010710081603a0029a155298600e40040040d0b01442c0042701c00c4c031031600000c2d41148207208a800344401d0703502030703400c002610701e01210303c0f0400c10203040c002c0303141c10910b00100d034144000c00003050001050001410182d0616041540311185041414074000402180b0344030050820280741c4000740d18060004e40707400166000c115000d80c25180d030b140007000700c3c590600d000d44030f51542c2403010403211003000d800c0032a400302580e20983d401c1500c01c140b62050000300703104040030900c207600000c900e000701400702c0d001581c000007082c00950540284640709406100b4882c0d80c900a07140c104507141044520b5a8408020b00007190056001500812041c4680107445001c880320a0f0880d43e400c142c8000c81c042d4115201052084903120f03d0601d503510b8040449443c60303441041c442691f881c40d2201c002008101b410b00e5004081c98030035a40810350003005041c601d02c5002c590ba1a0050fa0034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 401646205 1250 401644955 401644987
    0xd05100306060605091e030615030a0b1f0b03100b0d0906020307030911030a03021f0b031509060a0203071b0201050d060f090506010507020904151523010306060509040b150708 77
    0x3001d46c10fa91240c0361081c55803408903080354454120000142d07603200716800319103419184c43c000303040c0840003000c0c0480300707514820300342010400c20140c48050b40c03038010f220140e00c0140c4840f150f24904401c200325040911340038010301802040e00103004120394071010140d81c01103951000003a9204104030030420141945107952000f50001c184108aa54010b03594101298660450706207004c00b01280015982191a5007000a01503c80e43d800000c4800d100120a079081601809540c000a1724001c0c18030a4a1158009944a070340c0410000d82502c400902031100b6410020100026403a5000500034080180311901c030f0200041c0c9898805e80c1102c902909031410090704100910144e40c030603051b07581250300503540c01109100c5002040007004c070f000c0d0b901c810051000e000180380054080e5001000c080d0f1310700b4042885550011421109035001d13800100ea8107100100850a10790300c08009084050070240d00164207045181198002e100c2c121580703080040c1c1c1c4802051148 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 401647455 1250 401646205 401646229
    0x30a0c020f030f09090411031c030b0303070b0105060705251418010302060d0f0c11010506040605030d030f11030a060f08011503020409031b0302070f0e04080d0510030606060509 78
    0x41d010b1820000c42803c00000c0d4803940c0d400a100342011000f14080c00207860140b039419030002c1c216010103140c3c02c0000c1082c0c032010044070109241121403115410044110f0318100d920211902040e803c4c503042182d40d401103441a01c0038444c0048500300c08440c60ba001241c012095030380f0075081d01d0903240416100800c03003528018582090230704415241d008000e41920b9040301c40301e8a410044010100400c2c0c09816201120300b402114240729800403030b0450440071300002803265a41e500140810788583e4402c05405030b01044007058903510036030150b5086003a80e8804105080040c00e01215a0410b40e9910340c0643d40c1c100800130300b103800f41c480340100f030360000a124207210440c5016100380c05110113401240c0300d44808080505c40c1c01800d80b00244c021a2003452a00750038020340d9107080b07024051001c00c41c4c24012403116030340b407000341c41107070b003d8403503481d040036900d15002404018003443d62106100002000146981c01060054102940c610b516000103100f0000e02c05105 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 401648705 1250 401647455 401647483
    0x2090112061b35151309080d060918080c0106030203011a01030c18230603040c050307050d0512071703040305120105010f02030a0822140d0f1706010e06030a0c02 71
    0x60203c12010b1100045803980b00010551200d01200108003150300f00d1851040f0500e018a800c0c900b80030088250003418141c8420b500c10001c03251206200000c65195001c6107161035208864000011201c000901c1d15103020b60010440c3e81e130340d82c080307402d44000009028900c0b4100c2946842541c0c90711841e40161803918115900300380c03034480c0c101001841c2c02174810000c245d000100c094191500c20b881c202101514540c0e4a28260400c0c00c8901450f0060503c28000d040703001400b8a800c0c4014080035820402421094030070025000d200d40c40154100c8803a4402c010240680481c40c002c0c5202e58040d883d8150769001c058542a18104160001c9040c4400301c200c10004a50000c15980aa400c3d81018102c0d0340351002030480038156803c180b0016034203680c8034020000946d52036003020301854110755070350541d103c3c191203001d0341d81405000140884140030b14407042e2b00000350803182c10306003030400e582540b0128210394822980d0500c070648911400e80c05030390401c001351600c0c1c64 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 401649955 1250 401648705 401648777
    0xa06110d08100308030a1d01150e0106050906031504020a0804030f020706050304020405181207050705180c030a09050a0f050d0207080d12060b130302090a0902090112061b 75
    0x1c01c404442c012140c500014100c054040002030600146138091a8400400d01180e07a0320000f1007a028080c081440c44841900d00c51080003e030b40900305105410fa410f5903d80038109440c00007481416040200011010741c0074808450755911507100a006000c0d255641c0325071841c00381000342901c03142020308800c56100c0340d0300700a0a5886802e0340c1c0c0050341100d020030251a5403c50044014020b101d108184c0988080c02008007c80001072000c28030440a45420580c0e0b80f040041d14a52031a00b442803512060001c0c188508102c01180d10940c00e140010303031603107a03488071440c0c00303a0070008403800102c1d04100e01c20310030104100c6040d0581c2d88001c000741401c141d0b00c6038640152002c0b80c400c0c040746440c50b4040c80d4042d001a030240608190450721424240fa55150f00711580c070040e80500b14500100715001d1a41c064a6443d0303070003420801c20b80c0d00c1d2400c007500c030086c503030400e4403400e0b51510783c268508000300220620140b25a94464549400700030391407104582264150b01e500f03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 401651205 1250 401649955 401649961
    0xb1005010e0103020706021902031e030c0901030905030403080a0315090912030e0c03160314031801050708040e10090507051303020405090a0c06050c0615031b010e0a06110d08 77
    0x390102070505481020b00e00561180018580900a4000c1d8070b10600540c1030a0005815554004003074003d4000b104140e000790303010716071001c0f100d00c0207580e1480c1d4450100700750300b16540079402c0380804900c1141100e182642e00e44030b559854001a241800283c0c60303004050b80f140b0b00064460140050a0080004101e555220f55004070021100c205140d1900b904000e40a0140050b880c0100050300340c070f20101c1c040041d500f4110030350004441e50b00d0441c1070b14549010010070380d1107440e100c00c40b02a04100303e200560795030b00010b00440e4040e41c100000b0841d104090b8856000c5d20f408103c0b03180301070505000100342c0d10014903580420909100192044001c2860041140e0301643e001030300c2c1c0c980d031403040c0c1420181c0c900500003049024001803d00e5102c0e004003580c2c0da95005903030440d210461103200050507200303000e0f81540103c800b500804529158218404014101a440c001d4105c0100380d9200e05544140302055a14650180d80348003404840104901482c10040510b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 401652455 1250 401651205 401651207
    0x605030d0c06020408010c030509160302032e0e0c15031902070c05060316031a15030a09051f050a050606030f0a02160f11030109120521130b100501 65
    0x40009003030102000944682441444400c0d41241d0140c401e501c0240940b8500800c0a40600000e50306040c1394440c0c104000c0c2d05007500b1080d4001d6030b80c028040d0084031321004190365800011103050b40140c140b2011407141300c541b40300340340c0c80c500107070007400103400140d04100040321114841035008004004104192000d075900002101c80c0c1900180c4984403810510b4081c0550340142d60071039000001d100d0100c0e030310803894480c00f80f95a028030120107904007848080307464602040c3c00406248850388418060800785030b0041001c00c0000e1256503544449142002c0e14624072030000c9c0d40300d000354404082c1d00a480c1e00009040c81031001c4e08010000c02c80c2440000c280c0c501c10501400407a0282440341c044070b0441c004002c100d007080905041c0035940c1c4030b03034030000c075280702c0d80c003c0904a0381811700441d1040780d0483c1c0050203015043c031007076800c0d5020071a400011800702c080c50042e4110100300e40c2c003984484000d10091009440c0170300111070081d100151044405008108036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 401653705 1250 401652455 401652463
    0xa14100c050a0311040305060103030806091e0c03070c05120301060201060806060a0510020a0c031b0e061806010c02090405010b0f0105040b1c090501020304030c0b150102061b130b03070e04060503 86
    0x1400d43e01d40050754001a100b940d0007802141c03c0240f0b1405104000018154851311190003824219142211a1944003000c1d031200c1079035008070b0007000d504000030045c010401c051a845440ca0610225a00c0d030380d40c070b442c144600d948001c02c411030040014080203509101da4006000600010001820084000b8070081ca080c820a845400c0d1124014090352090003062812540035590340b480c0c03502c1c4c0c503000320a0310040c404c006410614440004a05001c0c1f19018024036015001840c02c05803001c40725030303048000782014140801c0e03000010058036190a030758450740c000c41c0001b420350481e1040001d044218000b05040000501007840060154821248650141015220103101d40072041015140662014286e9403020003004240750708140880c1043e80f0402c00110755640d4846c08689100b00e0040b4180140e204400260310750000ca203c0c140154881c014141c00c003000b001103280020203980050744182c03c0481031180554102034809070050040320240201418407000c80e5403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 401654955 1250 401653705 401653717
    0x605070602070602041503020405010f05040e0a05060105090d060501031b0e0109050a060f030b0f070306140d08091906080601020a0b07320711100804020907020f0a14100c05 76
    0x30407076001800c9400c1000ca507044034010000c505003440080700f50310000e00290858800c003404100001c508030102442001101c00340c07401130440001c41c0c1c0700d49030180018240100010305220040041c88140d039154101040058403800001c1029819440c200a041c5882035580f13070b103502806400c2c4500c1440340040350540c0e445034030004096961021100203410b483d070080c000c0070400900030080c803055003651031064a017500240c60070345850608030100d91491281841c10110b00e130b01c12499251860300c40d83e0441c0603000840c103182c4d003000040c07103008995001c0c0d4044080e0b203c0422056400c0650b0030f900c140c09001074100809035465414403c0c400034600010082488102d14189105892440c801c0c00c011605580145181c0506409544406425180040c0c10f400c00485441c1c040002d0480c40344582d26602d00d510307264244104d50740041c4c41d010a4ac0501103000d0704403242042500c00480c01002d0300052440d48607a42420504c40c008000300c00c07814005851300c00d94210b411104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 401656205 1250 401654955 401654963
    0x61a1201060e070f02190f0b06090705090607150e030408070602030c0606011b060c03020306030f16030206090d050105040f021203091806010306170c18040b0c090d0503120403020f07060507 83
    0x4c2c0003200880120b00700881c40d5154004038507881d02c0c26050211528008400d0b07031050031011001d403510410010200d0341112860001441040004003a0a2041c0981041445408490748034035140b10300b5015994520f10390000c0f81c0c000f040800030400100040c00c0280000c3c0007551030086c0d40c00711a52104002080941800b00d0414410544028840020035141d0449000c0005000e0036000034060341c000c0d02c25911a21403803d000c0035002004c0751038500324040383e41c24000c051642c5d00707019007a0031404900c6d92040554003504007156080c006c940c030991044400c0c0d0700c038400c41e10412645440340e405600d043c2d44103100403500c588804411000c8119083c008480d00d03035601c00101e000c0c10b0f0f5074000902132103000c0c4100314880d00004514030300d0101100c41840030040c0c611048407812003200d014002c020b075040491501200203008144c0d01c04080c2079491740c02e00d00d8a80b286141d10007815250842031042c100f0082c141c0c14040c88140411260103031690070f1401a00400f20700079510060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 401657455 1250 401656205 401656217
    0x30b0a0209010c0503070507060e030c032107020a0314010c08010b0a200a061b05070b131514060406080303090a080912070605040609060f0813050703061a1201060e07 73
    0x1092a0301411503045002d0741300c401c59560f0350a91a1071501c1e108588075440119058040f0300c40c4900d0003285000041501034002c1a2451900e02c4a94000d0b0128150034007154081010b2000b61700c0b0300b80c0e0b034000755014400c01c0210b42d031000c1c0300c1c81c215140158248200300c1a44014400c19002d0400c60b03280f583c861601402205042d102032084c400c0c1c0100100340b80c410f00301c09004002203074005880f042804161101c540000d1032056072075109200e8001c025119180015125484018203406100e0241c9600b1400d4030600010702d080740c1d803c240d6107a0698a44d001c20134140f500e40180400342503100059420342c14000046a5281100f01c0300414000000c1682e0703510303444220000d0fa02020f40401c0354203003a625100600240d1060154070000b9007410300c04244640195464580080030b680c8059884c0c1c2c03020800780c1c20b805441c00c212581d025841c0d001012076440c0c05110840c96854510006442c5440c0800c1581002c100460b030782e50341458020401c030311150706600d0741b28119040c45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 401658705 1250 401657455 401657467
    0xe040504061512030e040902010c02010c0507080d0e09070207030210140904051003031b02010806060a02030720011107030c0b090604030b070206040209150a0b0f0409091515030b0a02 80
    0x403401410400702c1c41910580c82c4240051244500084091080d0281e100e14000700410820322040daa0821000b9002ca118031442c100194490a10b031201c05004001b60382031541c80308481824202a10003000004d61750110040b00c0f884c107441d0003500300405000030300403d883c2d580420200d0014080721000d212100350040300c5c4018603000c982d500c040081080100349008048103000b10070601080d0001461601840403000151b4070b9542205d0f0142c580d524599144020421603031b2001d1549030440c0014000c440010b0507000c07406040e0000340c040203941101d03150004224002d45928505550300002d02000400d23922040304080c0e07414100d02c642e0f10140c41d00403e504d03201e280c0c80204560091810040d0a030b901141090042e403084900303e109403507084840c0410356008804603408850090104512a05000103000000d03895001900746a0b40f0b00300d042c11260000800e85000c640b05150010b0b4540b5403241720300c0c016030080542a40f6086441e1682d02ca407000300f0b00529140e0009031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 401659955 1250 401658705 401658713
    0x90b0a090506070b100b070506061c051903140a05090d0f02030313090b040605031f0f14040501060902131404090f0f120503070f0302030a060506070f0507050904030e040504 76
    0x18a03006040702030301a980d41d401526110b101c82d07008a0703040c42c0644040602140d1030701c51004680386590013500811040d01c0e600b0400144026510003495150000345440b400582d050000218646c90b10000c91503040071402c01402219441b000c850810b04101708280c803c9030071205990101d0300075180c42601051519020502c04d146401c040d52521020070341c40e044981084400c4140c1c0c01c108001d002e244540414030040e0b4285024017a07164200651490100c00880b05031216410010300115042183c181c8806c2200c030310701c0104c0740b2240400100302c10300c142400b611000b07160070100ac500c2c0c41081c8400c80c1281d10140a000048151141024003941d01c40c2c010301c070b2540d00030f50180007003080346c5070450028031540300884001e071350360503424102401072003a280320380c2053311032134100d003003581040b4000d50004280d056010755800000c00e8070340360381024284c0e25126a042501e401010300345945050a0741d44894400d101d13541c10440000d9004445014102041d00c7c00f042c02d4a980c60 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 401661205 1250 401659955 401659967
    0x12d0b0a0f03050d030e070b030a0b0a09050a0b030c0a060c0f1703070905030114070212070c24020f061003080319090303021902060f130c1502060411060a090b0a 71
    0x80240071402034900d000c002e0241c04a948406403110342c808205030b1a440d030f06035844828621851a134000103000140020015401040d281d9100600ca9980700791104d04200444c1c1c5c0a8407a06c2517199034820414407800c0400401080341000c4509041d0f96141c404024565001020000c0c40203020b00d0412040140d0300c100591105041c010054507840d085030002c0c010b001605c0b81922942c201040c1c68104244544810300520140d0301070038081a0002002c2c6291340300010450b040d00e2610750006115500709120748540101004058100e0b1054200038136104c06201000c80d50341012013404070900f9038484e40400c4035403003126142c4035910751001d4035068034400c41003421142010400c00400d0392503801400c0c40001000e001d08803c4144d00100d03540c0c501101e0901e07448000c2c001003803a54081c0d0058020301440b4084820347c2d1500c8a000480e20b40419441c0405a48990b085c4800c002da0042c0a140030035003900c8031403c207441020010302e03450f2903216081961800044a880e1144222 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 401662455 1250 401661205 401661209
    0x2d030c0a140711010f170a1e1404061b121a0d030905150a02060402060c1f050105032a10030b0a06170a110403120203040e090a05012d0b0a 61
    0x151107588501181c1004002034880200f202d00162030b0212440600c0d008440c0c0c000702c866607490309172040c0d482c80f503044010150650b4054003d61002c9048072621120f000e1100110201c031403981003401c003498002e007076441028000c20000025500c3c00d004aa201d114500040c20103032000c2047c6400440890100c18150b40383c5801c2a540160b00051582101d0040f0440d2002c0e03810f902001d011500c401010b0040000309c20043c1c010001040c05417038032b01c01138250388a81d907003030310b00e04468901d00d8017000c1c0340340200b40e965a4407a0300401071031800f40080d6445580348035440c0c41d1038242c076403030f84091f030080b0700a00e200e0540c40144d000d18038441d505c8142500e1003d0b010305081d0703882d06c5020304061620000c0440007110320001605030031540c00b56064240d04110f4442c2003d0a5646442d0308100d000030700e03170461109000004914000403400344c0510381d02c0003d0100c1820b68104076094540120300c40ca030070a014a11a802400c1c440621848a0000c04000905010400c0081c0101c5059 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 401663705 1250 401662455 401662487
    0x70c02060304080703110c0109051201061d15010302071e0609020a120b010f05060714010b060301090207120e01081801020f0d1410030804090c0509030109082d030c0a 73
    0x80108800c00c4004402400094040c6d100da010309103600a215568a1036070709108d0001d03841241c00c00290401c00a64482001d100b000030484070f0700c840c13101d9155a000d8040c003055080000a00500b0301c2041c003ea451a102840d044d07140030055224401e00c10020301907034210410000320340060100950000c1110740d0300400b03112005640390b0318031780c001101000560780a644030000140018004140800719007024002c00d00f44107107921070000300d0648401c07000c019501c920142c49140e0750300c00154060030328072200617140c1205003452070258251110503000d020000382c158140360303001051a0780c0080480d0740304401089000c1c0e200d000e401800d0f5442c1d12103102060007812000e0a400c4502d000d03130b82d0194010b207951001420700c1c00c7c1c007040c0310240948200f040188014401d642102030030f4519401c1c070501d040012004242140c284c400b050300c00c10302c041683c116501c8201c0401c400e04144070302070440b00b41e48070358400c0c040c80041d2081d0200100000e00e001210b005220320605000b107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 401664955 1250 401663705 401663707
    0xc0f0a030906030b040603050a0821100608010b0c0a020f03160b0909281a031e010c2c03070302090a020306040f0c1b03111e0601060c05060a05070c0206 67
    0xa516015001203518001c0002003400d0804010960415104030f00449422400074191440c0649030342e14298002030181c4071200000c4c1d061801030328483c1d401801161940c04c01c5192526041005100e1001a08885407001e800c1180541c1050000b48085550b034048820007140c654400001f46000c03c0f1300b00c1000382410450700010f820300004041c090401041e01c0d014515510901c0300705101c01c010b04290301320740d01078000112414076a442040e51a881584040c0c2034151080007920780401c0300044c001318020318a03400c0c10342d4000e00407003413040c1041c1400f4403c40512807645070114a5415040103100c0c07480c030312565658082010000864001e00030041c2410640b24400207540110394184c0202c1c2040d03440081580329104c0c0c9484001c5070b40d94040c070310156465251049540c0032082c1c042201c842d0000c520008207108070480e507070050081070030703a80c02d036002c0504020050b4001c100f03108191500c1e23800314202095440c1d201d0211080041c07107a540050594210100240180d00030034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 401666205 1250 401664955 401664973
    0x405150702070f0803090f0307050d03030b0402131707050411090111010b0a030c08010c0203030402010909200d090201170103020312030703020d020d140f19020d020f0703020601061101020415050c0f 87
    0x6004401030050300d07001e54a0201f620003013030a041d51032089101e0550052078078404880030911980c0302000e0b2041c001e00251070800da084c52440d01d00d40b160000c0c915141d074100c2580401004118500c01040c0c01d680a100d444000706050040307000c1c22000505000030700b04aa01c1b058000c1d4044850104020040000c036030b26424160143c0c90240901110b40d8a031042080301c0d5800001a28400c5d54141c0d03504500a0404031020043e1110b2106443c0c0b41c0c4080405040c1c5c45251406044080800a0001030200c1540001080b504071440083c80b04502c5400601c056180440d200c6080000e0301c000d03940d80d0b04d40500843c024841c18400d68400340c400700d40c04580016030b800c403445042040c00b001e00c16071121415480e401000b6a001601883e42154100c00f2102035000b500c90030740c84000050408a0300d825061490b403241004800503002180107008443d081145050083c408000031820542410801c003921500313030660109000e004201c900401c481046040841460f40003541d000344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 401667455 1250 401666205 401666219
    0x9051b03061c061a0a1d01120201050706060b1c050103080d0504030c0b042003010507171e0901060906060507080a1b06020c10051602071505360402030405150702070f 73
    0x11015020701032117200011030006001040d024500400c001030110603516928040c0380d09051141140c0072070500805001d100d01056041c4122001040301d64101980e034181140c00c01c02c01d0f100f4900300e140079480e0500500c0440c1c482e80550786071081d506030001e02612241415aa411403108009040014440801c820440d480c1c8200510302802601c0711254140e0508140c26506c0403690440050081c2446036041000b080095070040e09100201c014101d42e000d50f4040c5840440306105070b603464a404101c0c3c1f900910130398006005516081d0b0601c101582c030780202d403059440d400d0801515104540101c0185141044a15071182003150f88011903081310b51521140d443c0301c5840c614110001d800300000304040800030241c4d034060039440741008050b165054400c0150020010280950303443d43e031020000c4a480301e0303511503651302100b800da01d05040b90025000d01d4015401072040c44001440010401241480d01c3c0d04891555605c5004070714012241d8020080f444524000040380 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 401668705 1250 401667455 401667491
    0x803100b0c0f0622060903120c05040503060c070201120225030f090812040902031801060e04110d0b0112020f03061f09020f1e130303050409051b03061c06 68
    0xd032201c815280c007613540b680d81e6560f407007503803222030091341d802159980040d4080e80004185071007800d1001e0700d413030700095040444a111036480003082000405005a10f800c00410390f1110b0032035551840d107241c1e940001e0206c89007510f80c4117540d4000c1005003200d13407107000602d05102c02043d81d507111000381c1001000c0c0d01f6048c82880215201d14800302e55050080b4401090250940304649402d01d40311968009500c001c0008045900c030b2410b96501c09028095140200703400d140c040b04500740750a0202e40342c004034901d907200d4a85102440006044c3c1c01c00d150448581c040012101030345400450b0302e4402c5e2000d9507606000311003c200980c40c0c41818400d902070100e2641c00d00c151104548001c034402d400d107442c450f080c240000f20341e0340105002c100f1081020b680280c1040c54803d030301c00400303000c2e42045003c01c00c0420144901d2119101d0254405e61008003411420310441c050b812620020708002c1c0120742000400c2c041e100401507035040e59a101004000c0c61404e900b0369845 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 401669955 1250 401668705 401668723
    0x110c030c010f02100515190b0901050c0a05030c010212010608091b04020702130c021005040213050916030305040e091b040c05090a0b0414090f010608060d060f050403090b04060c0803100b0c 83
    0x402c0e004040300c44521120010a0307c04c6d1070407500e4a501c0c08001c030005651a8010948d690b1441c481c201441002440510140240c0d400e040000741e200c0c47c1d81144c00003400e805810000030000a01c013080044500040c11216804110b8500d1411030204008039019201c1c183c00690015024983e511111410754490b4500b643e0b55401d8800590500c0c00ba10240e40003030f83c2c040d6100c1050032403621064003c1d813010350015807400440b800c540408003a00c001106030350055010810204040085403e040202c43d0310551a17030240103140d1402c0200c0c0748010903640f00d075024942e26141c804940f809401203d182c2d003402000d04107015551111500503034084d0246000c0c881c02d02c50209514100034401074055183c81e00100e080b41e00b0300c507084891842c024400c951020302d084091022407258412500c1c089808140800c90381781c036050207088403946501100c1100c02c00c220412000f44d00c18015000c00b9481310b00565240c442c0b9201c0c02307004540342c000700301721400042c6080791050001a9202 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 401671205 1250 401669955 401669959
    0x40605130806161d0105070b092a010206010509330d05100c0c121215080d141c09050307051203010611031213030207080715110c030c010f02100515 65
    0x40e0a21301c0c25503041d0712420030810329000c0707070050103400e00254114000302c1d03024016004880c028030815080f90000343d00d00b0764502d04038102d0561080d1659060001c40d014101c2624805444d08000303442c1611510020103c900ba140ba601c0503100d807203032030020340d072500000034603400c0c9581550030001c1e141c020078880b90021924007043c0f02c0c1101d00420003110016005200c0d50310080d046042511616180142004110b641d408e020500241d0014100d000d402c2502c001e02e0b4001c1400d102030b00340c0c03440240700c0381d240406000d40840414002020b1084a0251001041c1d402d200d162045ca14003510200500c240200c15100c50241c00001c059812500c3e140ea414005820460002d03880e445410450010303100300500249103440d400301900400c6200f80704665015554101c0c003801c140310303a04a210400c080e10401000035600c104039028400071600500481c40e020800a9614000c00d0f43e100c1c1405081c0b40100341c400d009010f412080d60f280103040c031403458407041480c039082030441214 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 401672455 1250 401671205 401671217
    0x1609020c060108060103240f06091b080c0301170c090103080a120605010905010e061207020f0f1b010f050d0f0b120a020a05090a0f090506091e0304060513080616 71
    0x14220b60300103031342c4d0304a13600011400c0085030058807920200c102031401e84c01040e118101068440603910a03200103202410000030380785a100e010030404030304240310301c0130801c0b10018004140c084a007164111041c106000e04100c1e0960707002800c00c5843c0c9003e540c4400390800000501688a0081c0080c403c699519580160498465800c40e0035900078180001c401020030701840d402140000402280104100d05040300789200d810103902c2210300100580204480e144e0786039081101d0400003600768058448c000311010f00850244a26503010304010454100100040c000e50884021203003c05041c4107a0b0004407600c005000001d84a50107000c8070300d621082c04601148000303849500401a9640720724181c01c1046460002e000300c0d40081d6101c2c01d0162000d900d10650417898450b0000e0704c80307454000b500a04220200c454076901d2048001100881e600100496060703440908015131102644030070b0210350103c40d00320000d244a008240b00d5000f01c2d668030b002d10011169030350 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 401673705 1250 401672455 401672459
    0x1c110706060e1003030e0604050d0609030e01030209130f0207050601080f061b1902070807030501060f0504020903030a03050a0603200a1e0306090213020703120e070303170601021609020c0601 84
    0xa204801c0d0300f124180c044108036282880028896003201810b040c005014605041c3c940d0001140d42d0501c580407507089681d046801e04058021084241901007400d04500306004000420038100039078a00d45062a40c81403024110314455054411141c4c0100c01c4400320b40e140c0c411f40303946041780000c0c0b4400c0d1140c800000d450900101c14a441d002928807100c2c1130401c4164400071001038010001c042d40252400802c58650400403100110300800020400c546086048095984030340c00c41d40c003950041004444903280042152030b000304918001806d03965030710705040189001d410041c960440d00f80c6a440c030754024842050002021101c2c90000c13a5108030410440c1d20382075103c1e00b500180b0804102094a03a0b0000704918005860070209030001300d82c3c0380072a8070401c41100030400309141c02500c240340740b1031021041d200b000102022030454501500035030006c2281d1480c0b6480100040b49039200380945e81c207284200350800b901070b0711180c0c0364019401c40238003001e45120715400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 401674955 1250 401673705 401673719
    0x7080309032701120e100f060e0a0b030309310507031a0f270901061a1201051509041e18080708130b030c070c0b031b1c11070606 57
    0x61816018058441010101000c0b580c5400381c0314040b030080b85801540401c16005040e401061021b8447c51400200d403810020200b4044001078001400c00c0d103400e94aa07403644000044911543c001c03503408245103265090841103d0724842039035280d107004407060030180d107542c01250041405440c20f21040750002c00e9400b11080c00d030300c01a403121464456024a0808040340050342d02a503001e414440102c0e2803094401c00c4c191940b81c01c9a540304404c1002d800f10b04c4011071019030b40e0440c0c51408190750440011600103002d03240c8960001210328400500e160104c514030b000c050414003400b000d10308858400b0018002d8440e80e03d042c080d21040e015425200440c01550104040c0d00700030340c50716aa0519003040b80b002a41c5584200045500142600614883d00c1c00983c295510304003441c101445900f95400341f80852001d100f4000d0910388200c11140e07420300f484240d41c075550241c003140c01c0e201180d4180c81007e403605801c100c00e40400b800802d501402080d052001640e9030389 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 401676205 1250 401674955 401675017
    0x1909050a0624030e0c030f070501020c06070c0902180d051b0402070c09110705070e0601030f0b0105071401180b09010614060a080a06170105190c0e060f0708030903 72
    0x2da9154480d40c80b4101c603a00d402a4009054070f200c22044070010001000464a040300c050107a544640c0116803c110b19030741013024900384101130303541ca420300b0360f5070390f844186a0b040e020b0368181640202c1c20240110f08420303045c62000e00101104040c0c0b0280c100640c5810f00504c44641d000905100c02d4907904190085903240303548648903030000b03841d1030350034001042c06c000b408851400c01c10800700840da04205240c0540f0840c9140b0390360b800c040001500b1152408184007182c0d00700303d03056040342c2c0c218098030b240f107420207140035040416000e0795004100c0c401c504002e2003c05120038050001040e103852190310b043c0000c01940307868507400080c03a000c1c1602160b000c4010401c1003030041c80340c5003050300900c410201040b815210324405404860300504040940c1d0768404000e4a4020356203020b4110013207000410029422180040c07000340103890f020b025a40015034083d02043c4241291702d542e070041d6106450303040500c10507442e980400080c0c403070885000302e94110200640 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 401677455 1250 401676205 401676239
    0x7030e010c020c011202130b190e0109050904050703170d060e0f0123060d02120a150603231006020d0512060405070c020d0c090c05160305091909050a06 67
    0x6001843d0407501c3e1801150b00e40380340300c1112030700d64091080030f052a1241d1f5607003020f84101c00134691241e032030043c05019000713120f6141c41000031140100802d42d0300100c184c0305440042d07841c0001d56445040503854864140d000030030540c1c144005006010300c200140034400c00c2c010042c8180c9565090402484000350b0b5050b45a806500c01003107486488072542c0c9c0001401000c0d0700d403400f2100c00041068004000741141940c0014148100d01001c44426500806881003008203412181c000360b1041641e000ba00c0038180d0380d5007051070703544c3d07200301e922130140d265207940c41c440c40e1662102007000c1b01d0b80320391800351142e4006442c1d014061000c0d0b4800b441100805202503a5800802c00134003000342090040c40020340d509405a103900c0701220304c682c01516900fa0340752614a03004115018008007204229040c020390740e800d10400c800c1c81d04250540381c4141c5800030750000a03034075203403c103400c07405685183c1c001031105000d03005140f0408141104108195031940b0410380000c3c22 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 401678705 1250 401677455 401677457
    0xf070803090d0f20210703020111070503070f0512120304020f01030605040f1406180f06040b0603072724050d060308040906050301020918091f0507030e010c 69
    0x41c03007501c035941040c2680c1e00d86140a4484151540c60325141c80d1861850518510340e103e100e0102a252400c00d505481d44001030020342c0c40d000c00e03c456181d515400b00707000003410042600c0c0c0608580380b08111120103171038001c051300c0084d0740d6080101c5043c0898843e0a01030710301e030755850317082d4000802d0180c681480c0c4000d0900d0369490340d00f00a03541c80141205414140d84007008151601c543c410081c0d2201c410304005a0400e0307c515890a00d42c0050070700d445a40c000b005042040c7d00340074140d4014103200351906403030310740c136000801810304075012540200000c401c10204079480101c49000d07501c117120400704804014010600c142c440c1c0035644102600204448007020401856807030b900841c60a942402201211070041d80c19039802a41d84610200e410700500c100c42c420040240021030085160554000c01308000c1c500c100e0540e03200b142c1d680b0000d240410b0500170041440e0504401400d03d100622a201c0108804c1c0d0b00c1c4e500292420112407000e2034140f2500d8582966 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 401679955 1250 401678705 401678707
    0x60d03020703290a0e0708030901020703150914151003030507150e01020f090307080304030308010e25030c030b191818060b100c170d020c0d09080f070803 68
    0xb151910558201c0e4209211000e808003503c04114641010300d00c0d000360100355000c140801518540741c40c109654004c4101d42d0002c002c8050741e84c0c2c0004282e0204ea6018045a486450840c1d030b41004005040d009001c240822016000c20807011810400412102c52120300945682034a01c184c1125070000032f0101d20200100340c0170903d041910b00c25038200e46008103003032440010b850b0076a0404040e07444201408100f031b403164501030086102070034603c0011070030603145423070060200314184191070308031145074040341060803803103199440060469040200f07550f00308401001003500e4086000002d00d0706450340d443d480d11070804041c072181c1406a43d042400c004001030056010795041075103541d112503502d92103002c3c040c000c22241c0074100c00075000c02d803401801046003a080d0f41d42d0401038100462400259002a07099000d4500300c5030315224603440754240000d10680c1d5a190540c4950400d900c2c6240e40041d400081d1a00c1030103a41c070455001d03c0035a500c40c1240980b03c01500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 401681205 1250 401679955 401679959
    0x31a15060711031c030f0203060f010c17120415020901080a05220b0108010c05040b12060f04020c0c270f070c080a031a010f02150612190b060d030207 66
    0x242403030141000701e00030b000098080d062900080c0c0f60110a00d08040300c1c0c0e2030000343c84c0c00180c043c80360303100c0c200c145181036145150150025000c2d0901e006031b281441050751311041884030601105e41140010002550344071031038000081e003400121011901015003180e030740a00348171402034801e0080d0686076111503031650100da0303010740300007403400341c201f028090440c04118458840c1d801040c000c035800d0700e0550501d4802d50954100c0d40c850b41c1441070402080224010b41001c03605030040441060703d2035211100001d4070016030341c1c80254000e00110b03481903e01000700d0307031000082040701c03081d40ea90494038000c1d41480d01c00c0e51401800c40d070080001d0940e215190750590000d2030785414812401295030f88511034010400400020390b56a03e076402c4000c044090034120079090906406505115000a5603102e4114248040b0444d40c00450082d4869001000e0326654030300c04d40c0c0f03c0c80351414841401445540d01640c9840c1c034940480d08908050b11410301e0117816601500c181c0f4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 401682455 1250 401681205 401681209
    0x25060c0f080403031d0a1b0e040b01030b0403050405100e040501050108060607080906220f121709011101061205100b0f150d15031511030105010c05030f0310031a15 72
    0xb0540d04d07550307015071901c0c000100d04a4070522182e005035102d20034503504200d9141900c011207c0c45d400c201c4806000909101c08103465015050442e50302502044c050340da81c1c50b080320280903030b50240d41c101e011200700c3c500c103d800032002c40c5120700a442c02c0181380e0782c41c401124080010307160141c01403000c02850340420340020080000c1c01016240625207008081010714000300c08580210303c1c1c1c1c81110a0014046006021005120508090085403031644031024006000b0720360240d40314000403c0c2016902a0080b00e0f00d5602104c000c20060343d131618040c26081c0201011034442c010310403e5825100035101d140d0081d0030150501c0c0c400e54a0b0301c18810100d01010110002550500c5008450300950041e030144002e01724103811000d15516183d007402c2008004111100d0400481e24070480c207540640f0304480b800d1a08003120307411828080d081d445060254031121400000300081503003064129002c80c1e1040c135510415840c40158500c81c1c503416100d040c0440600000a02e00b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 401683705 1250 401682455 401682461
    0x50d020708040e01030803090d0e03150402030c03060f0901111804020a2309010314061e010903020d110909030f0f0336010506121f0225060c0f08040303 67
    0x503034400c481003403501da2180750b2844a90802d90084030301c2e450000030412510014030040c000715038503007020b8030450078080c002a00c92206080842c0102c11900000c2d095580030407c00c2d160f1107001d01641c1700780c10404121850072100301c484680942c28000d40d070850300400d008548260f0045034265640000701c200f0440a988007020080c00c100c1c4400107001c9118280d000400f0000e80140780c25036070480e4000140075180110b80203103c0c1440c101c1042070a454042400d52466105945000b50600160060b0f034905441e4001030340122400072220308011051410180d0700c1400c0340d49002c03aa4030f100c071081c0d60f03110765002c91080207814080311404200c03003009143c1003110b141c5440d20108942c908017003448000c0010b0b0440140c0c3c03080c5501d001400b07109181d0455401c1d2080c1da401c0d00b800301050b90307500150301d480b4079a02c159101c84100588560541d484000300c101681b0311120744543c001c02c1c00d40303080b6050301c14074900700c1d00d080c6081c0110440c940d80c0820342c50b10b8260b5030b40c1c0d4406030f0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 401684955 1250 401683705 401683717
    0x2060115020c091302010201060e130f15020f040e09060108070b0a021c02030d060f0f050114090405130c05041b0e0f030f011a2b030215040b06030d020d050d02 70
    0x150b00c15404941c0d0b20741d640000301c03845010304642402c6241c0f0180002030960380541d03c40407412070503005201840401e0784500c0340d00d5403c03e40038401c52403c0d00d802c0c41402d5100d05072800c61840800d08004102510009008444003a10f0030841758a82d90400c9403596028460840380790700041d03080080d0105840034006900290054400c2e452200036030060580d5030f6000003005800025410440189510a0303002410315075a0510000b410b001100b100c00d440c0d4014203044c00101108100e00101620032221480c5016000f07001d14204039a00490346205103804403280b04007500041010b08292050f40350800441d4180100411000d03420380711149503040194005040501e4803041d910100800c143d8030031988000108400b980400c00d28101000000c54071403180b14003050300340000c1124601001d81c0b1505000c00f03d288524081c2c3c60001000c4040082c03040c1402000180304100e20b6a91182200342c1c00c1c1c03080783c1c03e000c0080740c403680041d0b000c501040c810301054206805e2a8040c1c00c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 401686205 1250 401684955 401684957
    0x30304080309012706270302060904110f0f1b060f01140d05010c0909150503030702010509060d050108010b0103050a0203070207180e0303010801020a0f020d08040f060b0d0501050402040b0109050102060115 90
    0xc0c403811109a5440703220520703000400410303072000d0402c00c2500812412070748446046c48240310340742190300240c40703407180003440392103076844a40205000248078101c3c0c00c5a90038155050b41e441180051800c42d40141d030348801099850602d0603043c5501050003889071902c0c0303003c02200da0910744040007400c031125150780c0207507005c601d25000a2091051118040c0c0d19140c100c1c03094603200c0c42c803050301c004040c15261000704503020000303130728000141e903c072542c2424200d440340c07844400300b2410f015030055400c60600b0701000156110040d4005000c12500781da007400b460382c9000b10710302030303100584a500044e4030000d020847c1ca0b60707401c000b1243e841c1030140825045402820186503800a8000903882d95000404180c81a006195628016410b00240c0354034900790201a115400050002c1d1001080040c000c00300903e540c00070101400050944820003454100740d4024040ac440c100c0c000c500c0c1850030b4241d58000e411500407648160b000340300913801d02c031101550000c9509010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 401687455 1250 401686205 401686247
    0x161404121b0503030304110307060e1509012a0210031e110c07060801050a0e070914031009051b0307050d02120a440403140c1003090501050603030408030901 69
    0xb00d00e5a9080c0300840c0514051101125182c030300000b00350500c0290b901101c18054498905007440c0c0b0740c0c040760008500c030f44500c01e4aa01000c0c005896003101c164441250000312440c000282d81c0810880d80400e00a4074104100d0384508400d43c21508100c41500c5a52000035440c01c20f4443e94000f0f550003c440503c2c0c034207100301d4a0b45e80e850079445030800400b041c281d030018080c80c1070030300508000b88800f41c8202541c4c1803c00c4043c0891405011783c3c10039400b0702c43c060f032158070308000490701102605010848a085803c095450b01301d00445840d01003600a461422450001380d22020b0f40c0700208000c0141655508200941805202000207401448043c2c4042410040c014408051000f0120041903100700c0b82c030302619084900d11036804804405114141654050303e05480c3e1080c407100344584500612460102c50750440d550003101c1000303c130442a0301d6000342550520801c000c0c0600d440e1901056141d000d036005004042e407060000b06459032150010b14100c400154030a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 401688705 1250 401687455 401687459
    0xf0e1009060b041d07080126160810060812070c0308072103020c070303050c030706060b0d11030108060a1e050403030504120206060d1514161404121b 66
    0x405803a01540010b142c440c02050030030009001e10700354031040034075540c0010302d460191005840c044040c06840b65140c001c080d91100b03020008070107040c618000045950400d2113010f94520700025000d42541401036000350794105030315005943c162a1004050300e4600a441c000101d250010142503640350751000b000404107980400501c1c445000f2003e030300c20310115090648004101940d0751041520401089604000c0403c40c0c40c20341c2e90520701541d41c1d1003080016490340c042c600025060342d2402500091139035450000745039007100384400b0f00205602c1d40090000b0300091098111300d0f007241000940e2410154444050721840d0180c00d00d8021070484120200c540444046000c2903803841840240040040c07e020806500d100410700c9240040200341800ca0b5007000805c104000380c4046e00d04d00c03e503001040c03521009810000a403401800340c2620340c60100e02c14011071001e500c614000101d1b4001c440583e0040051560110066907409900c4c1c48055281c034512041e034200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 401689955 1250 401688705 401688719
    0x30e0609151f0b041a04080303040f0f1a061513090e0109050d0f17060618030309030a0b04060c0f0c1101020304031203050a0c0201020a020d11120309030a0f0305010f0e10 75
    0x710b00074140f41e01206480f02d0820950040c200b0341006416148102400200001203002080382c1d4400d501100c2c2804145482c0b0f0401744d8110300000c001e000744040c0440301004140002d400b44039020031104d89454000018144040f842444214200d6903e440001e00030b00c54039800200100c4007400001074070060340e441d0703182451013091160000840c0700c007140c00c401c0d611401c0c0741d0000c2d233030800d044e0150516200140561180301812140c82c400c0f480300482c1940c043c81a0340c08031001405641c00c10005203400c10001d101141c5c21a009854001007000030351150005d46000031039601c0703101c0b0702d00440e1546034452102101c50b50440c402044044002441002d81145140c8291004606410001403900c260b0b4070381944801168414016003210715400a1120000c09072410035140c0c0c1800a01818146282040d2081041500205021b2550320001c02443c5001aa030313a0304c800c0c0100c00008506a950a10400c01c0d021650340c400d004421248002e030350803407442451064081c3c0d0b02c0c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 401691205 1250 401689955 401690011
    0xe0705010804081b1c0504060504030b0403090b1308150907180207080d02072a23030304060e091e06100201140403020c01110106051503040201091d0106030e060915 72
    0xc20f60704c0350300071049000e0072002c051601010004075080681c2018245480203019000301e12010b8014085070020130140b41c018660b03407014000e02040141d60b82c1c1110701c14504c1301142c0c45000030b0741c460741100d40c2d0901c02080310389025011400190600502e00481c0b9046900040a44942180d08004000024081d80002c083c44001c1d03580141e154003c60905007050000c0c070044401a071102c0d10b140c24140650081c0b2415aaa0381c0002c076000803501400fa800c2e81e9401e8071481e05071000042c0418010b402c5012030603908130489480d800d0382d0342d0001040c2000e451a180703130b114079a04008500a803030f00c001c600001080a1000081c0c41e0340e124000380d1000001e80d426409600b040b2151a41540c0c840c0494440d00030000c0203005291400c004108110501e0300115182000880440c045a201c0c8400c100100a007114110303080e003c010301c11401c07800030b03c2160046850301090880061010031614441c0a142c4041c0c84403451400c2da2035030014004028200000111610300c0c002500d90f6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 401692455 1250 401691205 401691247
    0x60301050918150f0603010905060a050a0f18171c09030516030f08090c1f4803050d0b19062001020c0a140705040203090d030501090e070501080408 65
    0x3d404070002d801d007421841c0e582034000d1300f801e020380d05080040780810070010f1080c0d041248540000341541e16203007600000d110744031005105038181000040710b001c410f0031240089008400704402140c1e0310104514034840c03540d0300503841e5800520300c400309a06500c00403e09020341400c51918128003020005102246022001310300b1127981001ca0960010000d90711044c42d0004026076400315002400e00142020300c072102d020aa0840b0042900c44c07034618070f00031203421011252402c0038000c05810410980c60030340c0c580301007400380017615541724800c001541588805240404040f10440a400312031807032900070941441511601c02c1c0307260504000c00c940c0d03440900c0d4202d2003034810200281043e443c501a0b0040c414a8100e10010400b28402c40d4230402d0300e5444519810308a0030300e8115884140d03c1480441003040300310003c100c0c40c0c5101829034040080b603032a04410303011120035400c144016441060140069405002a503401a01a5440714104195120b111001007941 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 401693705 1250 401692455 401692483
    0xc04091404060c0305150f0a030b0f1e0606040611160b0a0207080a02030304061211072103050705030604021c02220b09090a0506042004080d0c02060301050918 70
    0x4104100601ca82849507082d162004d00d010700c01030070240c1c040c3e009528040420782c401c058030040500d180d614a04170000941d404440900540350003403140007004021641980c403030025030002c2c2503440d00044071a1003084000c0c003a9003004d041c50812540340c3c80321418810940728413500215000321000401006180741c58446035541a014002420304c403003a40180300507400501e9020046c2c2d0044281c41c00e82d030082ca0400f110031104d00c06400a800844106c05480d10000340d00e0080c040c04a02e00081003202c410544c40326481c03000304804071a8221400c8001030014008101300d842c180e002880d03005030b001c1c50f507a40500700b0f51480d01280d2052950360000d0750302d480101000c2c8410880d5200030158401182e0410307805c2c41c0402e0304588002c18290300c8a640da400180c0c580d440d948503c090403ca403803c2c0c0360f1024440e504c000300d070780301d402921110b210700c048482c000c900c5102964110f660243c0710130300b036900c1e103070901c540410054000c4507604554038140d00408410031032170541e040c0c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 401694955 1250 401693705 401693741
    0x4050a020423030606091f060207051e0102060103122c04050108060f060402131d01030519080712170903040e0f070c020f03120d0618140408030c0409 66
    0x1030441000c9141074120b0200c0ca40c0002e42c10690119a800304801d60b00c00340581d50001d03e1795504072007103110200000008030720b00c00001d012a81035030010b502c0d81030751400d071210f01c240011001040c441082d8201560b005910030b030014000650850344403500340c00c081c285011402d504c501500034006d00d21185000541900100c40071900d414050140102510805001e2a06200070504d0800030001c0c4524004c0360006403080302480c441d0032800c010560b0800f00e400c44526086a41d18004082c40107440620441300709074120400d441c107524607154014081454040384d66180ac18610090f001340041c0000e00c400204031100c0781c15801c0c40b0f52074203c05907030307503d04002c0581107401c0040c01c050110a007400402600a401004800030030b0340450f004035600c402440000e15065070703802d104180c40c07070119803801a50181e401c10030030f5039400240d000003114a400000102e4903101c2064500d80030b440d01180224074100000c43e00300100c02441441c098952004c841542c011160740c50b07400300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 401696205 1250 401694955 401694959
    0x905030604022e0806100519050319140901060509090309130e03030103080c01230a021b0d0c0209090c01021203071b0b04060c0c120509010e0916080f04080d090203030904050a0204 79
    0x94448807a41d01d050441c10514207000243c1840c071480f0030442c9011040c407500002144101800905054084e088be50040c084584001e0f84031802040c00c3c8c0340896558282074000c103141c40d09000423486164000001e504041101081080c0210607409103400f041d41c0303882004030510284010b40c01317140150f000365a64800c00c03060302d0842d01061001c000d00244c85a885650b8508a162a6003110354440c0c00750300d075048014201e90426140951500c2d40c85000040c0516942044110001c240200c0d10000717103a444000840e26840d0070700749540140c02182282d0640c0461001860700b06106181c24030350741c2681c4980c0c0300340e050407071b40039030701401c289081104112081c001e82d034403140c1d5450400d001c2c0619680d4028510300c41c902e0402403010108144149900c0b880d80c2c0300c0c1e110f000509040c02410302800d164100c03980c01c5000400124060002200f03148010000f60095510404440c03401c503000e90a0300090162941c202d0740f60000b04415003281d03455026040c090b045030f41c001a5694 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 401697455 1250 401696205 401696209
    0xf03090c140916050405040905030c0a1b0e010e06010305040c0e0103030c170c0a0b06130f050106080c12011a0c0a05060f01050406030308010509040201090302030706030e0c010905030604022e0806 86
    0xc5004040d46220070807030010043c010b600c0410345048070750940e07000c42d80760041c0ca00700b41103000d0038200800602c9100419402c0c1f01072524500704880755000c08002c03540d01c600c02031003441003d000f1000003085040104000d54400d9114503481802940c06c07600f183d8441554050b0700d0700c00c5e070080d80001e0b0780e28990001d1004601003204040b0041d1685440c1404427450709031a81d850110180142004000003440c2c1e841d0000d002da0f0407954100208500d100b04580080148028003484001801030030000e40b80b928858212480d40703a16081c9003484c0e81c6000c020a05a0f48540801860301d10144000200c0d24070800400e1501c5109001400b0b05141416526404d647c0582c0100c0c811130038401c003040820740112034103045d41ca003510761340516512400160346008032540025014030500c100016090f41c142d00c450a00003040c0e082d5203206804d80e004540322402405880c0d8150040c034042030041c5004030280b50602d9118410246055502e221000b4201625110341d01280d200400c000241c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 401698705 1250 401697455 401697469
    0x120708190c05030f0f010606300b040e030d060b03010b030c0307030209060f0702190f18110412030f08190506010e040c030603020f03030a022d0304060e040e0f0d0f03090c14 76
    0x50442c0d8902112745081c40b00080b00d07100c050210381c0201d0510b078042901c6060b0550410a84440d01501c00d00542c54803090580e5654040d4180c01c02ca18604440030481e0f09660302124100c0b4105818103046464840036001a40e2002d4615428590700300321303080c05625802e01901c0444900c80c0319603203a019a005018508010502180e030041c0041c00c1406200d554042e00e10640f005c40c0480040414640b0404004040408048464020110f00010a00029034203008020301c02ea54443c0449849141076500742c2c01550500d4422030390040c031040310340c1e032a844164041d90514041510815550120302100d16200a02e4002038890b5028402e40c180064107044440c0f05030001d5180034501030b4000d45a440c964002265851840714041d030001a684449540a66407400d580e40e955031f510000e09100c008811683c0103038100041010741c4200841c0000c54401c404014013110349111204651080c4404030300310605580342401c1000c0b8540c582010013500740343e017000d521094850104440c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 401699955 1250 401698705 401698709
    0x15070914040504080f090102070503030f03180a0201050403030f12110c150c220305060903090109080a0b07050d020c010e0604020405130f0f17120105120708190c05030f0f0106 77
    0x1d03400c01c02800005509881162506800310801c02d850310100c0300100d09092565000c0d980c548800300d240761f11101c0c2c40c3c0c001c40c0107034407861f2219004119031110740c0c1c640400800c061b020600a02040010034015007054035451801e1500844954011f925001101c00040209100d10700c040b404d4090400304111802844d404108240e00d1890580741c0d60f456071082841c03074079441c000c03005214541c0841081c1c44000d95030140955103546000c141c810303547e4010395400ca0003d02c400718009424000400c0043c00d450700910100030980c4d40742d500703441560194440040b016820041595440b0084c80341c002d030840088094022401c0c240108020b50307102410142d514003610990790005007451444584255112418003414080f9050104600000c03c5c138003c100c1d40b000503461002080240e10341d05a4400701c2c0c004c240600e490090690f0f521680c040c0c40b8065200380c003081044611130390600191442205020845600e89010900380751814080381e547d035010030000f01c5240c07428012140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 401701205 1250 401699955 401699959
    0x213050907030912021915020c0a060b0312030106080703270305040e010b0c06070c02010c0f030f1101060812090d17030109050a091709010207080105100810110403031115070914 78
    0x30384901840c096808003c1d1190040c0031342d10710584412030501c190183d400c061600387c281c48030ad41c01d908081c0094400444028031034090480d441352140002c40559051b503003a0369480b40d0030390702c140081e0001c180c071200d044843c1341d0b180e4140706c082c1248511b20b0540d030711030b50311291560f10b40990030107040c2060f0000c402e030400520501d400c0399000030702558000d0440c5440c9103100d01900058501c0006900040d21044801c081802807540100c0c0305105815580c1d240c0b10a604a240c81034201c9450313002e02c1c0d00c59041030554415190b6000d01030905401c0c001c082c070b490700c8440e581f500030007981c13805001b05071034003c4010440000c03980b04490380a1211142400f030a80d0300d540d1290308080b40441c08040400210f809107060b4400c1109001511850000b0480f070704003d050101e89001d94420998140310f031100c80303100200b0a0261000b05403201c4005420642907a4041d128500b0009000c00303907100381d42d266510488400d10450141e00c3c03546422429508118515094a0b00011114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 401702455 1250 401701205 401701213
    0x606080d020d05070609020612151509040c1e090f06020705030a0822170f031e03040201021204092901020d05031302030601030605091c0203070303021305090703091202 74
    0x10303184540104408405003a14580159504d07a1480e1401c000d228829010b5003001001ca04500141b906200e03003809a130309400d180d40c480c203d103070800500740358903001c1c4521a4424400341e08641030581040c07014145a041000c0c1d100105002d044803400c01c402e4800004030380450030490699180000380140c94644040c04c03107107040102207582c83c0a000c400503c0180e00040c60131001164252040b11482c2080e81c0c582901d549201c0303900a04240030004110b4002c1c03038a40364503024000110703448541c0140c0210510654400d1400720341e00010f005a055000310010450300810000080015140501d00003031800384d003009015005018a188100010300d0755284600c61781c0002c3c1c00ca1a0000d580781c150b0307030b9549095288a07008201e01009401d8442c28002108001640c2c0140380b20311044030840e80401d125030541410a0700301070003000540c00c2003158001181c4250020310200c5010240040300d141e841c0e012480070501101c0c8000043e81d035580410410501d603490600300071907031000b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 401703705 1250 401702455 401702473
    0x5010905030d050a081308180405010902090307030f0201051605010c12230901060f06020c0405060306040b0c0a05070f0b0405100501080d0309060e03030103080d0c05040b0a1b0203060c07060608 85
    0x1403d01c0c4104603800040c0b0400c04000783d6401d4103100510106940303d01d090391034069104400c0074080c465415580704606000012510040074030917207500480007030040003c42d1443d10b07681259054010242c1c1000002c00030b0421f44100075000320511440355000213a644010f100c0108009442e0600c4000755040490040031603002201c1d141c5606070542002da096145c01701c080780146015800201c005428001c001052500031030301541c400d4090f0340030301c4140d960301e00309500c406085800403c1e0340f00c06000b20340000340040241200c0c41450600500c0d011442d2070342000044207000884003146030404100070440140300008403424009030034800c42d41040403040d202c0500803880b004041c1c0e039812001c103001e0503410036800e20110034140e035035031b5840e414039000c0b55105a0100c01407900b40098208014817500c221003c594610356424204070b91007400315a2034130b103123061043e074007000000710015aa0a0154a02a2400c501c0703031a5902054582102524080c0e440501c41d50066620 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 401704955 1250 401703705 401703707
    0x2010e03090f041e0e0708070b04030b0103120329041503030806060a05211602030c0c0919060b09010f080c0d1104090c021501121511040803120105010905030d 70
    0x8400000004039000304a501007804c651183e01e030030300d80d420001810541010311000b03000c21080160b54804094030320641d16509140a60310a80c40000c0c01e254104004202282e0840344006100c91303186008503a8140000c0e00504125500c001c0e20a41101d0000150310740c513041c40381030b0792403080c2801c0719a2140b071a28064401103000f44268040e0b00001082c1070384900c0b5008503094031080d800a40c521042881c5509040e020403101da4441c3d40e0f14500c5104014000420340e0388611404006103403450624007803004810340588200325001111007501800c40450250001074194140025101c0740081e00050031510821007807824020100c0c107121085008a0440e200c4c100c016001180d0300c0120804035a9a20583d0310031403510340381400d0011000c4d0701058030b9803040c070310410300c41460743ca030103440203402c0341140001d1400c40100d03581c5503070340080c0d0000d800346000c131f40d0190300700b0369101c0b003090460340b01001e00703a1010032810051060f0340e0030900d2040138080540041107030605100e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 401706205 1250 401704955 401704969
    0x30a0518010e0904240f090b01060c15091703070c150908180303070f031e2d03060f2d0b0304060f180f050106210303020c01020f070c0602010e0309 65
    0x20b0801d01e0b200b00030b44e01d00407200c105e03c0d20201d004001000360f00c405000301402003405a07401c035400e0980400008800d8881c040583c0900d401c140000080c8000440500c0140600701c0101c50301c0190070301904070f030030216003c2c6110f40c5603074035003007890100741c40c18407540c3c040900588441440c14208002181c6040244e9400d42152491012500802c100084c0355000b00780c002003643d2624140d080825a00006444401500e484d0140385c1e03105101050f03c0c02915200001d64941300c0143c030710005040d4050004081e000790500140003515250b410654007940d41003488000030750180300c4500b201ca000000c079001419074406901031300b40202c4070940d00c170191001d8400e076191000703211105001d2b84010804c240c078aa2090807030a151a04c01044840d6510680d5954601a0000f6150390a500c07000c80581e03a940118295000c80c0d0344c04c1d80207411420b0410503666080c450010703480e4a42004140c4540504d1900410501d85070001b402d4415207400c100c0190010b100350780340344d1203610b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 401707455 1250 401706205 401706211
    0x1b080d14030c070c03050312090a3906181401080112061b0305070210050f0106110f01020408030702030708030a0905090a09050624010504050306011511030a0518010e09 74
    0x146803035900d80300d85200076064083e041000c1c0540312061000802c20100100134a022040112400d0306030760798401850320f4145001c4042c0200040c2d4055901c000d0b603c0000041c80d00001c031800060b404404204607034500140c01007004a00200111107a020803c02104010054856040100b080b0800000c10400e410300c501c0e50300e282556400c80400c06690480800b020300d60f41c003403104000d1342c070b0014007a041c02e03603105c8098020014106070486040c01498440ca84084040c811039203402d0040b1a64100c01d4107001d0036028400c1e5410101d4401e000034001015042c005540352030081c010142000d801d54041d400d968420410301c801c50740c0200741d400407501e00311042c24080c0d45041c03021000e0b0003c103000804034081d650400c0911001594441030380c000141c03032034100b5460b840065401d84510300a0070381c140d10103070040003c042905031201450b170091a12140149042c229186550454604c800c081140480c6660a10300c2001000c050007400346401003030b6070340344070118070b1200002d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 401708705 1250 401707455 401707487
    0x70509090312070c0605070c020108060f0d080f0d060b0a020d0512040206160501021c0501300201090f080109260702013002180103050601050d180c031b080d 69
    0x4007001070790090081d6400b10490b80c00440906c054580704000500c2c1c0704106800702c1c003182c007803030102d051810a01c045c0b4a03000c40c090a100d4100249450b640d2241d0042c03c03442041c400b00b0041c0f0342d00c807015402480001c0c90034614403901c0300c61541c800703070401900a4221040007400c0c00000b05014441510540007501a03500ca6503881001c2210300d0041440c0304050070341d40c00018910305002080c81d881c04010740d08641080b90380d0300c50186060740c20310204a50b10440441c0100070601c440c82141d0b4408610504104000c20340d5941c8003030211704941e0054440f6590b4101a00c1071004000e02c1014030186040c50f030600c0780d6a001034641c1c50164000c081d04001c3c002000822800306025040c8000c0c4c5080d015001100040604070044c0d8000ea0114912981d03540b4008425400307801201c1c05084143c403002e0408503e01880802003000141103440d41407800c0c00c2e070300410000500a400746019402c88401520701c40c100d900080310641c0b01403174030760007420a000340f1688038030541c20040003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 401709955 1250 401708705 401708737
    0x2010b031903090b03070e01020705150703050c010603020d0503030a0e06040201050a05180301021b0f0106050603040b07050906120901050f010b031b07021306030512040b0706180f03030e0705090903 87
    0x100c2e080442d8801500e82002c80b0400001040c042550b0300f080614104075000d900716948240c0311b00500110318490318052042120900601d80080c4c015009854120780d01c40000500c0781d030f2500007c0ca034506010060b00d243d000001400f90070640b5015003001717180440014207403030426600003007035840341c42060030030003070040703440600940754001c00e005400c4c00400a54071b43c51840500e00600500741070000e003521612141080d00c2c038042c003403a821124010111815036481d6240d500c20020020320322400c0003001c105d0441161f44003405083c807200d08542d031603101c0c82c05c80022421610701a041e8424012003100412040100300126a400300d28040106140741e004004038889014803400254442c211f8041080c03400800d42c000e0381101d01502c01c881980784082562003051149000c3c201c0d280390104201004a00507030800818900c41c00b005c4402c4804c2a1214030105080c050300305c00288d151020f000300314500704180800360008544d03456880c140842d45a6581c42079000801c96111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 401711205 1250 401709955 401710003
    0x402120c012c10120608070f060f020f03070308010302090601080906240607080c0c0a03030f0f0c14010609050c0a082a0d02090319021c2307050f0102010b03 69
    0x20707800c01c0080c424000940810348120fa1554040c0203140390310b48007111189000b80024070010000f0316241124a11400c02d0141400c0c000112100000f110100c815480744070200090340d141080102034031400f9940f214082d50440c4108541e00f83e01425032410480300c0414090000c101082c102c1c3c00402c7e654004500c2d07220a001d600c55001040d5005901c0240420f07200305008641008184600b001815146a00b40f031408104a51140d400003500103480c0ca058620490f016590208905c116820080c9108000380d555003c8209440210780841e5142d20040010b9981409003e07080050180c42500700391016400410b940f0000700103c012010320740d00d0341304841107040007010340640c1346407483d51100d0000c0a13a000c0d520500707019000c0d100c0d2204016502e00c0403121700d09182d900805080a8501c000005030345454400400d0b40c1120718080d03407507003140d000a00074191003c048082d00c101890402080481140b44c20300e40c2c1036905010400707009513004600e103903400aa400d00d08506113 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 401712455 1250 401711205 401711267
    0x5220b0406080304170f010c020d050c120714060c09060f07080d0e0f06010e0103020a03150e0118020102060109090c2904091b020109050706260a050402120c01 70
    0x20a503100c1c0c2d103140000180424114030340948580c00c903c1d02c40458003c290144a11403c8411950386900160404800c0e01485441440202074940016048400c2c1d640c2a850082e2150300c282400c03614030810400f030f0701c5900003e2100c164032880120140d402c081c90003021815520400519220b400000608002086085001d5803403500500320100038510032080c046030b072038806200e034940c82d204000000408501010b0054141c80c5d01030400b1161030f2450b130341c04411400000215203069101c182c004000d0b18248502405032090048140312042c1074000a41006c1040c0c00046007181030034105004a19940f941000b152410503003441c0481001c0f043c04c9288a007201e002c03080010000d40090102003903004110f00201106421190b490080720503070888010100c004c110f80c124880800c1a10700580c444c06002e25081c86e044e44541c401200c40344031200850b499500b0b503680d1014481541801507003006191401e030001c02c01081c4103000a010001c402003c000701c5018100300b11a51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 401713705 1250 401712455 401712461
    0x19050c0405072601211a0703150905010501050a050a110f1b01020a020303161a040c03120503072a05011b020d110615040b0d030f0f05041d040303060e18010605220b04 73
    0x2880c5e4800401ba00e1341401c16008016094685543d002c841e4040d00c086010100c9114040c1200d2058540303d10300a50700350b060f500760b0812410802486030710411104491400e11146a00048540107007180c03c8190155500740d2411507400c50465120100510068a0000488240c2d240c05403044042c0600e6181210345900c130016404107104a2030148000c01c8140e0a159040c0c7e0b00c174002484090184100458090104480d0702d000911040314080145210300030f66420102041580006855140c40382420b44902c42249100c884244002c041c00030303410b00a03103200d8421841d00031801110000034a6941304040c005c3c240f420b20742c000700307040b03540c859101440d564400307450f03d0400882420042c000014410400c40440c0f40c0c40091505c1d40d100da002c40e03041d910682d4034103c206400c0b02d00080c19000c018812001c2c10f949a40c0410b07d00501c00304248a039406041010f0746107a40e8014a00f0340d4000c1e0302103030141c501c0d2800030a000e5019081c290b0b62103540c5000090743c4001400003405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 401714955 1250 401713705 401713733
    0x305130c030b0c1e040302090604020a170408090607050c0319020a030b070c06060801150504050105130515210c24070204140705210105010219050c040507260121 71
    0xd584d44807051805848411000d041100d008484040b2160750307080031700c8103a00c1103140c100c001560081d40700c0b81400c1c10405064011340290001c50038928401c0c042041c55020f22000c0e00c00d68402c10110405242c104140a241c41c1b00c01c036001c1c031400c82c5074081034245c009804020301880c0c1c044d001841440c81107004100e0681c004000340b02040c1e035081990700138130750070f508440c009404440100307080c00e00e801654102c0e00e000d0030040d207540a80007110014503018010100f140300e84500024150340e120600c56090400c0c0c81c032041d04014162a8500c1c2102070724131503008860303000301025881c1da080500c920700000003243d503a0711441840000c0c0108030200100400310701c24000d02800c00d03405805000004050070840488514500704c210300ca000911410f8011b90002c0e01009a0380d005070342c01d40042c0d218908840740040f00300c00103010344104943c40c800040110182c1f00c6803400c40551030582071100324030f0460302d504002c141210940c44100c202c103c2215860540104892204440a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 401716205 1250 401714955 401714977
    0xb0402060a1e0507030e01090f12020d0f0506180a080a03110c12030603011a0d170c060a0507031a031b010c060204170c031501050f040207060c020d0305130c030b0c 72
    0x42e004145400602103400c48102680002d1403025142c0855010f1107449040e0f4020542e107045a41c6400322081c501d0b002080126005005101c044001400b10b0090a0075140700d803010703080e580341650b6960148009030110007480c0e80901c01c2500403402c000c0454501e018546004500c074103005012162520032903588181e18801e0010070800d482400313024602a03030b01200248000d1072206910440c030300d04469519880348501d00c03002e0002d09114580094488101103040c20f20b2030600380b142c203045046401062650f120410401803d40c148a0607527480808a06504810010070107c0d6071040d541e192010900700141003046036a00130f514158000e40d024000355170342c0d502e664600c2c03d813880c0d401810459104840c0c23451550300d07001c207a0380452404e502a0700e280d0780c600010056406c00040205810a50030441900030800034080c941c00460b15030002c00e803504403405c00800300d8100400b0009000700c04040b8200046592410034200d940119517141e4586803030041c0d41d80b500c50840f5100c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 401717455 1250 401716205 401716247
    0x7020618120a12050903070b0a090b0703030207030e0a0312080403020f0706090f0e090d0305070c0b2404020a0504052e020706020106060f0903020409060b130b04050a090b0402060a 79
    0x110380340c00000702140710b244140d000400c1d0300c0010500381d40a00412440c943d0640064009001110030308005d48a491103074580b811074181d130b42008140d2030b80900403e400082d000100301c014942c1110b07116040507400e0b02c95030107103455505c0d41901c420300000031070204009900410241482048000c100f880110f0071f41304c01540d560000f4286007160320074808086035407040000c0e0f101c9126445031081208001a20300215920380407401002c0c000c20b00e03014402c0e8001580041060340000c148140c0d07200300350180c500303204084e0007030030b40100d0ba540d40300e07600404c412504641d2200554046900642e207a4018580322950040e1a4410419001d01c6038158054403003400e6002601600303e60307294000b0083e04d51591400c45008031440d03003c0c408101000320401c01070030154000c110050290900090009208000540340006180c0905001d902d480200c0c4441c0780520800d40c01c4010004100b044440990781c0c0b0480950003000a407240c0030103d070800e000c90140285c8103003640c00700122 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 401718705 1250 401717455 401717479
    0x9020325030501060b0708070b0c0d1b030b100e012a0b011e120308071206060203040f0501020c0d032d0305160314061011030301140910030807020618 66
    0x5600c203024a4031040c1d5030b0b036007030840c0054040c8a290450b00a03903001000b4034034000d0b03103448603000c0070740142c150541200304128000e400f10781d80c483d03c0c403507143c00c010f02910710140b00710041c1a20001704d6820311910300b8442e400807286c0c02800c0c500c3c49000c2820140002c04c0d2519182c4540c2800f030402c0288011344480501c100b18815900c03d05036480307948008104403494019103207001081c05912009080d84c0e41400200b80281402c591280042c544113052040607208401583c0e1650310060150348003040070700c05944495000e101522007031004002c00409000000e802d00414040601400369802d41aa070b000400f4a42c1245180300d0320b15449040600326004005190454a000c420030349480210a41071007801032810104082488468035110700b010405d00146140f035240c03e01c1071003151403000340000d10156008210142040002c03a258005009450744000d01c4098203c1d601d04090000407403e50a6404558050b00c0c9292645803800d0f0b80c10401c0000c440c440c0d805180110340b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 401719955 1250 401718705 401718763
    0x14030f01020c150c070807030c060b03011a0f0103150e1005030d0903020901150c020f0a05151b030a050a3f0c020c101215080610050904030f03090203 66
    0x6480d003820400000301041d80c0e25294101517004500c0001c0c000b00082003450080b9214510f240303941d60084100145607822200000e0031180b00040106464904010703030b02c82c171f252090b044691800c003820700744172a005003100d40c0240380c1d290044280c207051070030108031a400c5c0d50314443c01070140038040b46e01100d180754002c0e01c01c1c0c07a1403001328801e11402002242015000e250800d005849844111419055034208030031000d0701300724960819604003000480b5a10720300d064402c031400c6184281e40c0c143c14041c1d001c18244200e041c41d55540100140380d82a0342c05400c5414003800e503d04000c4800d047c620640425402685101d103405005d0a040103c840d20503c4149114804100300a070320100f2170241d8440b002651041d034001c0c200d00b000d84055000703905480e6600320101e000154400c0c0141803c0700b25681742c0000103160b11190401040d6900441050094034040b190400a0300e0241d03401804404020207100405032107000540c02c5403000c110f114524140356062906000000ca6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 401721205 1250 401719955 401719963
    0x203040e07021603020603070e0402030a1d0f0c0603101d060102010f0b030607030f02070506040503090118080a170d0f020a140405090a02090a0e0a0204150203120114030f01020c 78
    0x5040800c15a900220744124000903c01d032508081c003100b074050b0362440d02008101e420050000050100b00c0c281c14456640e2803000758032030f40c0366000001e24012058030030f04030403500452040c142e1307004500d4001c6209000070001190503048540d6a0399540d13182a000c41090f1070707489480c041c0d1103007034115101e4004d0f08203c1e10031102070703008000c00c40e02d00c522041a107015501d0f464064102e900851034040c861340201e5141410501c02501d40100740c0d031440d1901c42c0c11038080e102034101050b121559030340f19881c4500b41c141903044000b01401c200f866625a8640400140f81c0c01250589125101c0c3c40801c0d07904c2000c0a031810000c002014018034041d502050301344002800c02500312408030300b901c050f01c00351600a0709075917156031200c00c950000c0d40100c0c90701d50311120058001400b02080400701d80303d951a0b84000d6200e81c503041e42c50b0a079a10005001d0305540017440001e8500303c0403407010341140d01c0c0324900c0034401951400300f07083c090025031185a5500004041c40c00c0300c8009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 401722455 1250 401721205 401721209
    0x60f06031c23070c05120c031501050901170601060c0c030209070206040b1b0d09110604090b030c0a0b12101d01030c050a03020607080d1806050f07030b100c050319020304 75
    0x200061034190980d99902c034240c403d6050050407408103900c1440740b070810400d01006002c050742215100c0302c0176130029182141043e81c40600c403098400501850500034030f828018440300c50302c0300b0204004d106107521260140503d80c20040a540046c050142d04d1403210011500075002c030f0700d10305084200940354902200c0540d0700343c07035500c0410b564001941820070a041d4055a0301d00b130140e0b00c400c0e84040d0098a1f0192030301d9101e0290310070541d075403c00810051060f0f00380010324992403014182040f841d610801c0c07091580a0042000c1e1600504980140007050380000d81540c07140040258440c4540140e400307860300e034210910b00c05030340b150030381a00d00600d108240e0654030020000e041c0191301009400100501a00c40002ca401c0060b10f00c40d12140400704024a254044816181c10b041007a0f500549480130301500100180145801000518050008030701190200740042d6280c9000c900b040300c14500b030001d0000c1802640c4289032440b03082144000c00050095581d0424 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 401723705 1250 401722455 401722487
    0xf020307020d08150112060b0307110d0305060607020603090f010e010207140c06040b03070e031c0e010e1c05030c010f090c060203071212020d062306030405060f06031c 74
    0x2c40d070403a81c440d02510980d8413600725a514001000916001100d43c2c1c0140d02d09007015a0b1501b2001c568003501c040550312510159650941c0107600b01003040c03410801015000501d071400044c42215142d01044510058043e00e981d83e80303440d4170442c1880c3c80240080d2664651030f00740540450721040d001041018041c42100d00d06900c05508161210181c406140e4820b01c100000c2060440030303405907900c04078a09010418000110109007401281c0c00c00f02510301440e00005166508400e100c1d002071400e05e04101100c0e01c110114450f20703a145501d0b07400e011460400800c22a040084030508081c0e6002400416400c15426000d04040c020884141904d1503011403403510000a07240540d80000700b170410b2040c0e0300c8080c3c500800c00945001180e400b08000c42c0502e20328020b5400030a54140c50038949000e40d4030520821400d0002e141c0304200400a110210f074000900c1500030750304c003110780802d0719401e00083c0b8203803110090040406182000d03038541a003040c0040c0d010111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 401724955 1250 401723705 401723713
    0x21c060e01090f0b0901030f021c0302031e0307020d1215031a060105120c252301020703140a09030215090103050f040201021005091906151e15050d0f02030702 70
    0x14407920343c0c0c2624524142030f5004081c1a0040010482480c0000343c0d00d800035042402c07000c0420071841c0343c00e2004006a015030b000103403450202440e002c41c924101e1002c582d0350309600381440300035101c0c00561080e00800c0030804901c515644558041d002420304241d0310320702907580303107031805070751054a0704840750341d400d100051a6940100c045485c04031045509200d030b0f130380781100b002694110702d001420403e0f545694042500c42100049400e90248442d1000e002e0181c0344400d2803107800c142698940d005011090000e904083c0d0b1741b0b141030040e10810303183c03084203c003119945107a84c0080e510007042c29000c0741d44200c00c0010860325000780d0381030025640f01c0c4d402045c0b101056400034016440321400300c00c0d1a0103a800701e03400000e80020741d02c49a002d003030580c01e80925104107840ea65074510034000700002d80c050b014000d0494001410440d003a4441031080d1140a00c100c80d034811500c01c02403200c500c100101c1f004c0a400b82d0301000100d5a04140400941040b5210800b42c03107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 401726205 1250 401724955 401724971
    0x2040c02030c061306021318050a0b060a120209040606050a0305011a070230100b0d08040314010603060903210905031804020d0c030504051c080703021c060e0109 71
    0x84084100e8038103000340790041c81142c565503d2801c2c0c800070210141c85c5140e00344103000c10384044403184001421703802c400d18109041c0361f0761001102c501070b02075400e552502c10308040f65101e1070182c0b0704100c040e05201c0c01d0002c030240080040d1003071100c1158040d15020700403d072190840042c0032034010699003006580e0701c5039100c84420407881403d183c1c0074020306c4104010b241090b00003505000c0d42d01400103280303804104004900181c02c103240c16406c406600ca182c020580f1847c4d10340841110503144200c442d440707845251003280005410340d2505110b450059009400c0500190383c440e004204848050800070012001c1170000b200200da200c00211340c0c3c400034044c0981c1f41d5080b034082c510305100f800390004c2200d103803408503400540074400e981503601c080c41a60318070400c584000c199413905107019030429540700760100c1c4208031180c000407855401041d0383d40c800300c207040050341d403d01e4000d402c4441064000b050301da81c0c103110000c91403034a8804500e048881000701444010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 401727455 1250 401726205 401726207
    0x606171c0906020307020d020607020a0906090b040b09180f1009031419030b0319140c01020d0914180a06080c060702030613021512010303080c0301030f0210050c0d030902040c 77
    0x81c544102c1e001684140010b20151401c46400c0c0e00c01840140f000d0301d00f54150340410810b0303540358003d101c00c40c1d44013000c1014154902540750382d82d404407410407000c00e11100084403000c0182c6242c2201424101c034401561041003441c8410303480d5021164441040d10000001d007840c0801100080c11400a161007440b08405440c9001e14881c0450340079038022078101c1c01440c00d11040f03076251081300241540e0320b480038200410103000b8444102d03068101c0003603d10706582210503c1c1158811980c3d10000350340541e4450070f0301c6545003d40341c078030501c8000504c440300c0d1404400d004890901400030b29403040d03000c14120b5000000b0703a6045800c032810040c00e40582540a074060b003103840001d1190003a0201c1c410383c81d02c0241509614100d80100100301e800c0410402001c48041c0018424150481d4449500500700c030310716483c2d0b40c11544c0f86148002c901d2030090040e41c061003141061801001520708440d8140c045071200a1a13010040c080c20110006134040d03450030262070512 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 401728705 1250 401727455 401727467
    0x9070501170f040302011506121427011b05090411090a0308280503041505010302060d18120905010e100e01141603080a1b02060c070606171c 62
    0x101c1a00099041a80c0d034249441800c201c00400440465585507001001c10700ca0803203a00141c100c5541c3c218460ba40d40751180200c4440600c4088154203400801292500c5c02c2c0c1070311158038000e403440d40f845801e400340300e0140c41c14015025031080d0345011112840c0c3d02c000030b0201840206c4081c442039214402c0010a031040c40102500f00c8a080c000f440401e42034002044400529440c40403d00c0c0d1a0204202801c0c1224100340003550010070f0109100b05480b80301c0c445105102e0030400b951450b400918603100700a01ea24a0685840c2e0442780340744e803403030003220454004442d403905030a0400c000700b03441c055008203800701e024503401d04001d007460009200078405a495101034200c40d0801034034400c000e000b1b080c00000040024080e0002400d80d81140184240c41b91006030420010503c20f64000d003028081c00a80b500c3d204c0c614603800a103460b0007448400840ba81d50f1054105803014040e66004520311039107401c40d6042c2800300150582581039992079508019401c60011146 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 401729955 1250 401728705 401728727
    0xd050610031a0103020c190f0b16020a030f17180f0615280906170a030f030203060109090e0303010e0c04030309060e04140907031103150c03060a0e0a020309070501 72
    0x10250100c2c10004030750195000744810006c0c05c00b105c0000c80b6214803407250742d482c1e4108450101c41030104000b003200c0070340515004004444071800310303114054000e43c0c400f51000041d00304140c40c4880460f440c020140f03140c1070030b00700428070070720320f003400d8412003861401d450000c0902c100700d0441c3e101751010490318094000032103400078107102e80b02084107903942982c4084071040440c00b003148ad0040e41e60b049008046194020402a01e002c4042180203600c2c54081c05c1a000754400c040060307481041164000e4047c200182c503074494000494081d6446c0d00710320b1550f0b1a0021518100c01d0000155049400c11040420555245c20800c58503001d82d200080c0802c04801007808036602410b105055080082c10000742a5070202c2102803544040d5042c001c90340040c0c409105101a03000c0340038032564160010141c0807407c14035481c15003802002194502d5000c00405d4a030340e64a18044001c3c00001388140c03150404d030390070400a51007956228040d11950342c0c0099294022900e8600e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 401731205 1250 401729955 401729981
    0x509060f010e040e01180510110901120c020c060a02070e010927050a060c0f090906080304060e0409080c0706030e010506010503040b2e05090912160303020f0d05061003 74
    0x4900d0107403020b00c0081c200c1c120b00d04c4090354880d01d10319040c0100340700041016008000620494510180e00c904a03a441084010180004c204082050344c0003003400e1607a203001100000e4601c03030041c04a003000403038040a81d001c00c0c00140390300b0b103d41c00074880060302c103443e108002c01d0340d03146840000c0302c09410401c0341d84450659031031075040190904654450040c0f00750740d0110401e0b5205e00403560851154030101d00b0207900d01212591207001c10000e00b032842c1e0300704446030501c1c2c071a6a583c002c61107400104005000c0c031216549654101096503039005040341c1d00c4503118040141c88550500408002134504152040404014002c05024200603100c07030740b0b152248e0b2603010718480c00400c0e54050018140d9940452440340b601c410301c0606024012412909100030007000d00360141140e5000c0c0d000c0d040407032a0184440c1210710702c14034041308070100d890514080c3e0190041708446807541c00007180c0f8030030303a41e42d54110b680301d10406c4440030007064000c1400d0b0300321a02c21003116 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 401732455 1250 401731205 401731217
    0x91f0f1b1a070504030f0c06080a0c080a0c0509031b03100b0a0b03150a0303120e1b060705070b0f0910020a050c06030c09040615031404150c050c06040c0509060f01 72
    0x319041d0000504203410070703400d181a0340703444d40f291181485030031040411201c0340c102500406c819540142942d4120b00c040c9000e104220031844000d02454000d0502c80744240c0e03581a00c903510703000780c048980c115005401e13100c40078006480e0210346005055028024014a030040d07010000a00c01c882c44203100804090809007030142e00021604000c00b14001c00541242c0001a90f4a40a00900031440b03a40d40c41c0c0c52981482e1407106441d41240c250816500c02c4103404150350700b000801300c46050580d151a01c500890802524004113940f000c403164000050b03054080000070014640d102c8203031003491070210705000c100d0391021840d80182070781d04042c007030b0b42039480c08800454201001380c000a0800c03050000090807201e4540c0400c83c6450104811604580c042c006c0100180842403807006500d0f158842c0040c524821046025540d41d40404482e294003440c103036030480070060b044400500d0305207861508240603003c2c0e24851940e0500040b01c81c540300ca048201034034181d580d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 401733705 1250 401732455 401732483
    0x30c0206072307081605073203011409010615050403050d1d1c0b130210030209031009080306031e0a0f0507051504031a041106091f0f1b 60
    0x941006044180040703000e44200303c00d5020450a001820407081d4a20503004009501d107000340c5801e20716400410421000510407145148a811007200e014030440d260210808039030019005041e103400e104682080c082c00e00c010000150321203c10760304102e101c8070407800e525409035050f000c1d510008100d41d11105031040c0e014810a600ca6a17002001c3d0841d4a420750040014803c0d00300d40c625000c110752032036004d8184008102c1e52a0000c004c050800501c0903a900810050900c010500c0241500010401003c3d1810028861a840404420094000e103803600e10b00a510941e401d40c464418104188500d1000c119020700c40485240244280704082d540c804c840e4501c40383c01e48181c01200e1380040c8603150345e26010710018a204081e681d9600b107140c14026103c08601450b91000c2c0ba004000000e8215000d80c1c02e01003088a145881d100c004d000a42188890010100c0310004507141015480d0484010001d2002980b111a680072587c40c07503181e1002c2c2071700080d2555a890000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 401734955 1250 401733705 401733737
    0x81b031921090c080106150806060403050303041e1502040e06090108430f0f120b04080c10020c0c04151a0c0102190e01032c0304170607030c020607 65
    0x48029214412541c1d0301c4040e5841d0304c0c003803c540c0c059000c050b182e03503051500b21445601000540e400305003200d00600b4035007103071240344d0303a80030060004080aa040b20182e0482c20340481041a0503440b442d00080900d1008805029410031710400d005103401e580480c8003480d00820340e60581c0d10f544000d00f042030360080d28850b0585034a4012644066010b4200340d002c0c08111880c44d245001c61101541c0c52420700000030041003030b808224030f0208200c2c14810505101610700d103060b0404da20740202e80742d80c00c096a2512035101424002c2c0710302c032030514604669401414461a024007540e2a920303d420a000c00d0398400f2114000d0a10202c90074816980c01d51404100901c00002040c144451002d1490880e4400e0491781c0305481403000c1105015403101c1d06002602003880d00340402908840080b1552200f900b00b800c0d0141018440c50756510200140c1e4010001414045081441840550f03242c180a5407880d00107400c0a95180900d4000030300c2c28003403c1e0a541d4494903000c071800d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 401736205 1250 401734955 401734961
    0x11180402120708151c030207050105071203020306011214041b0305120f04051905031e030d09080f0d021b06040503030f04020102120f0307021605011407081b031921 72
    0x1c0b4100d402c030310030703258041c0755101c0101d8500700441c075005c42c007a000c8031801e010786401540d50001e41044010000c4d000005c00c2041d00d02040b0070903003809030300c90301c640c40180e03040a0071000c183c00c410300d00f11030103800c0e090101029000b41e018040d6600341c0e4070700c0d4841d40803400c41c0d404090159840a4801189140d9800003851206940340e8100e0030141c8a10008181c150b92499140d03031080e98101c1444545414421118032080b00341d009100c0c0c182100902d500d034060814003514455844041c28140449a4101c6040c0e00c120200e45070368044c8000e4800080d00303d0300292041c0c0304860700e001d40a00300003401c14002c40c3c010700210f0440c3d0f5180d426540c5110b0040049045010f512a29030039588400044e25060070601c208588070701d08800b001f8a402a803240807071460903007075820441a41c1044950700100824607804d5903d004034100301525220312083d24101141600d0124851b04003c009003221440c105107956140500f0300d000c0744c80d584402c01c0108003407285030b0360841c0d07540b06034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 401737455 1250 401736205 401736211
    0x120e121c02120f0406050a05060901051c1218170c241206190510201e1b0f0f040f11030907050312030406050c0c0111180402120708 58
    0x8000546061010b40c25028000e6003903070042c20b407100200c01d000401600d030040c10fa026607240300030807140c074180300051007801040c800d282c0200e1080d03803003a2890a0709000e002003d9005040054031181d0050020415271102d9818164040d006402051203103965880c2814600b22000508156601ca02009080c0c45044540c50080e0a8030b66900081d1a149000d05514030850940186030f182c0a02440b40183c100018110b01c074000f49800c1c402c41c1d0f914161000203850504d0481a50402c10300b8540035907083d0001c2c018030780b044101401c001c400315003200340c0700400700013640c17000480e00d01307440101c8155440382d03079100440c0000480ca90038804101440d102000703002103440445002e020086654124000e200c03200000108221000704010b8200204002d500038120051104d00c1030a0600024000900494448001c1403503000c1c0d01003a02d4a00617100b00801c03801c1c20b0303c032400216078002c001803903012402c200d50882c1480e1600c02e40340d80c69254150f0030682e542d4140203d603402d40027 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 401738705 1250 401737455 401737507
    0x90c0d0308070f1739040f1221020f0f0616080c07060c0912150b060f070602090f06340305070209040309210c080105040c17030d0903120e12 62
    0x510700d02000304520010a0407a4295170501a40d41d60510041440c412000d8002c01c90f14110700013690005400f5404403200140402120400200a40c134101d0402c2d0307110707142601d540704d0400400f40070307000420040d010721418403110505003143c11003540c107498115020240c110701030211078041290354200a4606000c0d24101a4554843c0070320303006100003101c1a50b9002d0051100c00d5240241d00c5101c400c20402c035091070910000c1e080b10082841003180c014009500032903040d4840d244e1040c0d008000e40028109a155410388540216103c164411701c003040e648101075004411502d001e00841d140c16598940c41c0400540900003149001341080301001210100040c0030761041010000703080b581e042d004814111824443e51607904d1b90001ca42991410050200043c00040b8050850324002442041e03140c01304403203415401280c03100d030001070910b0a032001f00b50b800003968281001c0345a041120720700320030780e4964070071510220900c0c46804002c40c280c2c1c0130750045a00542c0d146 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 401739955 1250 401738705 401738761
    0x509010e210a2003030613020c0a15060f031208070e1f14030901020406020f070b0319140a0902042d18060606030506091b030609090c0d0308070f17 65
    0x80e00843e0a10b030f1030503900750f00d41c941000c000d004c1c884c07400c1751003d540684002e001303500342804441382035111048160001c0915070080c400341c0200007603412100003000e040c040d6401e203075682c1c2055080e0154100340b50300043c05ca040003c10043c050300c0410480140500000801c483c1c0110102000070407072992014003d44241005620702840001e44c41810091b00140c1c1302c6190601c00307071520101c20040546504030110600260240c542a03a90129079213000300129882c1420b1030340140a5041d00d1450910340c0350270494071210540140035810710a4908100f200c4103240004102c204040c80a001202003140588900c416130b0029240041440c1d1510700654241e501c0604aa64550210000c40d40312000c0020515203e090076a200521801c00d000407020440c082c442031100515142c820030548000c549000410441c148503508080c014240c0c0a070207040142110f0003c50f416800651420423907040340f44503c0104440c032020340c000c010a038803556558032030b0740004500011761082c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 401741205 1250 401739955 401739977
    0x4050a020301110d110f0d09030c05030d1a010e0f01030e1504141614010503071b0f02040b0d050a0204090206070f03030f2a0f120f0509010e210a 64
    0xc1c1c28030620018000032000f003661441100b54002c10f80d0041d202589040c0404d20480525440e40f07011110103041407480001e20450340d140c1507030160361060001d8898407001c110740904955030b030b024208078201d40e5500200d5844010044440420b50a566500a041c200440c0e034503500035044a11100382d00415940c07800040d0080c15040041110181d80307800345440c030650010002d2002c0480c3e1154840760325407480c01c02510705a60ba0f0f00001079030400c070001002801c110301c1941444010400c80c0024010122203041c1107909102414099100d9442d00803102c85500d040f924240319240c0c0701e405450207410980820009002c3d840c8103076001481004a040010400030031410b500f07110b5200054003010411150b070840d50102561001d01100d030344d03418040c801c2070014800009091800300044110507e007180c0903c00c24840510f6079040480d03ca004c81802e801c807070f203e4851500200092464681580e54450301c0704a81d0038003001d065002c05c01e0360b822000400e142c0700d19080c000c2640e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 401742455 1250 401741205 401741209
    0x1820030321010533090a080c0a050f2d030f060a0507020a0b0a0b040b060d0603020103110403080318250e09060702100f060509040f0314040f06030504050a02 69
    0x680a0800c8416041c0100028001003403261025405400309aa05010301c03440141d0980e00d480760401c80c1030b0038900403020500c00705000011a400c9030005026203090960302c0c40d250780c2c4c13403e001034541e00c507480d0040301007002c3c1417486d50158240c10042c6918003001407180f0b0b01009180740903401404440301000303800c1079141048030045a141080003440307140b610214581c115400506102c00310b42002c111304011610f00b90b8a9504940071580001e401100d13900000c0040400103409a040030000c40c04040c0c110255000324100c9000383c0f400d0101d0515001000341501c900e00005140c018144085814814808581480f04012100702c400200c40020809001c0c0249138103801036140c4d151051001c2c1c1e00424802d41c01ca8140c1d03008042c0d504007008040c0d1940b40c6250042e03160b87d030307a040450424030f06401c460010507002d00404810b00b41410f00d901000007100c420303400f0401c18150a182d40304070f0000c030780c1182d410280c058031701410140200c02404014205456038420060b80030b000d0303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 401743705 1250 401742455 401742457
    0xb0f030a03081b07211707031d0102091c080403060e0105071209051b060d0501170c0a1805130501021308060612070302060306060f1308010f18200303 66
    0x7406500c070030700240783c101058101486203228039212804180081400250600c401c0800caa04034400d440240b001010100d4160502c0030b22000c64104007821b0040564140e4403090502451a0074084488080c0c04006d0030b1b8814180115081002002008606002104681407482c03060509500c1c055881d1110425a5044100300c0d00c203035520400d02c2511600902c7e07454030200e011400b84201d9480307880d100e4840424034481e054007400070588a81950340c8c4c504503410300d0320382c81d02008156100c006480c3c00f01d003251710004640c4904200071420340f5284400e98102c40300480c0c5044504c621024010150402400d03032003180990240c40400076600b800a003401c41000001e2a10480c50a1681894201d02034181f900903240700150441b03810002c640c0c80203998050351005d55a40f103280110300a803082c6062410300d4000420420181c111140000c011103500790001e02410b801c540103041210313820030081c070b9100750740343e24500081c915444807103480500c070500c454011040350102e811 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 401744955 1250 401743705 401743723
    0x5071e02030c01142422060e0106080105030303010b160c080c030105061c020f030309040204060818070f05010c060b060d06030b011706011a0c0a0809120606130b0f03 73
    0x540c0001c14001d181800c2482200080310305079161448a040c400d0390706a400d02c48001c00300c18031410b10070440c183c0c0c4455030742100c80007852945680c0a40d06da00688002c044600601d98200c2d00b01000054081c45584100d040e40c000901a52540c4d00e8041014059070242014100b407410b6010000302040c4139074442402099100091b244026001e8101400c541c1c005000b148524003440c2e001500000b180020a0320550544001103003444480000e03240d0701400ca41c0503445800010041740c00c0ba80580728074001c1800c1c2c86001005856605810b072980654005c4140c145554841000158031a040c0119401d00844000805491100c0400d02c1e603440700320a8620700c1d459940400c1000000c07811180141000c1144a0030304000c80320503a111a81841135441e0244a03a01130407070780b400d1404540a40c1424000c40740034074201d103000c00c580d4000d00407442c416020780e14518a01c03032005c10424495007000702014040300d10b80250f20018103046201d42c0d0815a1500042c009880401001d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 401746205 1250 401744955 401744957
    0xc0f060408040e07030504080f090d02060f0a230315011205040309060905010c0503090d080f040815070309050c10021005090c150406020307060902041119030b030c03070905071e 78
    0x350380c074185a030070054424003502c40740802d0310700010400448d80000030341c0c030440f2303165840c150384620400004460303d001e924065841200000e048031521a680d0041007581400e07210148a4004401c0018500501918094071000300b0030004425200c10004441f80b00c0b01410a82308424040f45007400f150000c94084002c503504040a220310358121001100910091a10848900040e500c0a4413405040d5031203014080c440c0107402086526000c0e03900c40c06054510980304c80c1c1d1516170030350f10b0014104242c1099020008500c0c124428092601c07800c1d004001041181920002c0c0715044800641e00011402074a00e80c41040d07d19000f081d00605a000051054500d500100b110f039540809407100d441e0010003080091940100680310041e810441c00100720050380040303805005403100104030840c0000305401403c0c40542d410803d250f19550801c01c209102c01819a1021002c03050365055110b003d04014050341c40d0809907000b14286400e258104135401c0b1240a49200b4110304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 401747455 1250 401746205 401746207
    0x1030f020d06170307021311040305030708130f0b03360604021003050f0f0406110309010c121a06031e070918060608011514030a0204030b060402030403050f0c0f060408 74
    0x881c80c43c00c114054001400014500d400d005500044200b1103a501c0740e40d00503190109903903d00000c1050300e00845d00401584e030f484002e454820780305e03840491000c403540c10100c00401c044031000480340c1655010b404151441d00c5010041c0c0e1003040201c01071500b03000c0c2c080e00c0750450780c11008400081d01c1d0310740140384038103040c41081601014500040c0403d4605410040c6c0083c103400043d40201500e00e0300055603c80d4104940a42840043d02440d942c000092086030b0724150b00c02d138889010b41d55102900c61404540754156034070208107850010070300340c0c0590a0b141100086070060b800b50401b03403440c8690b21031400c0e01c420469800020030849031003000100642420314808401038942001001d040c0700000d050b40c00103000750065a9020720800c24054000e036070b550b104102c601680350702c900d00041c1314030107584140800c50b215403c5e040813614074200ba000303490159615484950801142a0004007a0740100d00703503543d144612418803034402ca06000c118083c9008800c10b03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 401748705 1250 401747455 401747459
    0x6090506090f030703210206010504090201081305072408070903020906040c0e030a11191a0304080c06011403010f0b090408130902041e0806061f03150803070203060c1e0901030f020d06 81
    0x20342444416030ac0b480c05103062100350401031f80e0150b4010760101c003c510340c025419090500518200940d0006d0003821183c441c0c0050b0101c02011800c012900c1e569041415910340b8003c6074001c6071484000e410034100c07070200e00a86022b400800f03c0c60305610b4948504180080000c0c9425104241038800c554480840c008504000442c0c0461070888480e1134041d528200c60340349070000b001400954010040081402c002d4810125280110722800321219561075000d680903100c010f98100d4840e628041072494141350a001d00001840020100050340d40e86454640142d0300900c0c01f0a80050b0300440450039000341d1001e0005010089502c288070926a10082090300081d08114a1070740800d007040641c2e13440c1c400302207000e112110011a081c1d0010300c00d0b800380c841c0003440f484200e12810041640d200010140055600072070889030300361182d0b240d600341c03440382681c0300710441c514444030100802c220000b0054210189000250321501241490807070308413070500c000d0301d41c5500b0f00b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 401749955 1250 401748705 401748707
    0x2130e0a05011d0f250305090d0207140d030c02030d020102090906041820030f0a05010c0503010806072303040b1032120a050706030606090506090f03070321 69
    0xa000c1c09009000110214200046484006000e00400c40c0c225140d1303010000d0182d483d1140c1000d003820100302ca2607115031030031002401610003142c220200c0e100d903042e074000080c400210030307040700d852000002034200f084090000d0a01110025801e109a071410304005841c01c2120400c0f0800b15800141c48209201c104104008050015881181031014424000602220030200d0a40c00b00c01d00c2007460b103402a4006410003c409c096050003044034400304e01ea40414141d185920690082140c40c41303075501903990340800e0148503015840031000030300c0b041c0100e0130200c801c40e20662440e00c00c8120400c03d0407a81c011241141c2c00391816090010681006400401415502440b070310780c40280d15900003036080300d00039113407080c2985034017420980312402a104403441a00541e5003c0150342400b0b83c5d120b11a114100c00a443c2c1140055040e01ca4400701d010780744000c0c4501e18200d41102080054191a0001d6030325010744880000000d248495016019401307200f81c40018041040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 401751205 1250 401749955 401749961
    0xb12010501090e010902030618011203020c03010c200304090216050d08042d060504060b13060806010509091c09090c03150509130b0a020306280b09030102130e0a 71
    0x2000c0303418002d640c401440065500c21140c0d054500c140750042c0c49544032000901403500d403485003040030344100000f107540704e601800b4004c0e0341e00a4080702d144503001c00900d4225203036070500034001208500c06662850040c10481c0c0150508002c0302d050903160b801d12012640081c4a900d00c44840307102c41002c000c0c0601c80c50605410604100045141907100d80346c1e200c01d5081c15a044141050030300384040840030741100401d4008008000c1460280b03000c1e4014101503c0c10340c410032074400d06005c01040f600401007030f10705100161200780d00c0c0c4024448440005020795440c0c1c00395a02d02c0076440480700c0c5040c0300c4001555000880e92030a015613044030170a0706107008150818400794420340c60b4100b0710342102d90650f00c1c82c1080d0740d1281d07400080c80640600801d141040c60034860310380110f030099406032204552000c0c0c054001d02000645121036141c500c00b84070b81d4981080145c0400025101c510b03401340016140c4003030f040d110249903545402001450b030350002403081c55410f900c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 401752455 1250 401751205 401751209
    0x309081209150105044a03030a06050d0309051c120c17040806041b05030607090302040f0b03061501090b0703110c030c0a030f060915090614241503010b1201 69
    0x61740800545075050195056589040c0708280c0014030402004074601d0f1248074039040c2e002120320a542d441b0000f80703042d202d0b841510001c2c1c84600f0080301040919105207000d0403141e05407281803a5034076281c1800f0b95407a10486e00e4500c0f41c04403004c0d00205070b01603500840543c0c980e8031041e100b201c515100503807100e03860740320100c14070a0109224644000504580050300400d44103600b501d0071040c0c0d01c590705039411180d00341c05180148202c0340d07009001c1c0d0041e00d01c22202801350b2100b0b4464103048135003045540740d2591040d00031401c211002c4140511204040c945504000e40f1a011a4141d500c441021800103101150008515000b4081c03420001422406170a1050b03101c0c001805490150102800c03882500d8060410002280d000403207241d48103805000041400d100c0c00b00510f00600107459150910708140c198081d0801d4440c03082c2c42c0c5a0b000007441c2182032560446a910180c01500a60b441c16071400806a0b0342c041d60007450f1001c4840d954401044500d880d041041e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 401753705 1250 401752455 401752459
    0x807021008011a1b0f03070611031608090c09010611061620010b03060118051509160e04020c01020901140c0607030f0b0d0803090712080304030309081209150105 71
    0xc5001400052580804004180c86100c03402d51a07214041d000100039241c1403284c8031034810030010b041c1c2148080b010708104c80c013602c2c6c10016901c442841c0c0f081381c0b008031800c00c0e288415400c00c00303c860045030007039040002032040382d9604030b160010449170700007038001c00045603402070240c03207070503007001400e0303100c0b84203012944001d1000d0800740100c081c6900c42503d0800440d008542e168095219008580d802030854221b541d4481d000c000034041041032841036818240020000101c852500c061802c0241000f0a26900c95440220240d181d0f40b80703c0070004091a014500c1d80c0700e001806c28031203000d0005a0701d41e080130024114844c015061300700342340709201d160488100401c01a6206071141004a000903600301c3c07180091008042c09a4040c6c401440d031424031000e41c01030b41c8109019000c0b50031464560458904564000a004250170410800900020f1007500306101407403148011034100481d200403c1c1700400211480840c50744101c0614407003a105802c05401801b00b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 401754955 1250 401753705 401753717
    0xa020c0904240b0a0b1b0105010308070212030315040e030903121201081b010818030a020109030e030a0c1707180504060f020918060609100206151c030807140708070210 74
    0xc10041903229000e8881c004485d1001705060b5042c11928100300040810717800200b0480da149d00d070416054001b0001039018045150030004442400000c490141501d4051410304040c45810400a0680c00d100c1c1c044500041c0444420b07a01d08115400c0300c1031501413400c0e250603242841c0200084164030960140d80004000d402e00c038000c3c0d2030381d591241d0038a05902036075980c12050480000e074082c02c80c40c0f4800021a00500c0da070642c8401d102070b12075501c0c1450420400101580c0c2c104c00c0300301811080380d1130301c20003998444c0341c0c494051f10201020344250607a540b411000c00020741d9001c071146900d440410040181c50320444402c00440c2d0011800c010b01740f00070070442e4143c142881d40c0c2102200c04640e0541c0d90805981e10004000c041c1580c848200c00c00a4840c0c209031141060607441d055090010b2400030801d02d9844078000d201c25041607152021104003001409042c00c2c0501104150030303000d1044010002140a03032521076176400740744140002c42805108240400030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 401756205 1250 401754955 401754971
    0xb0405060114090303161a0612030406030e10110706050604110924030a06092a18050d060b09182d0a1b0b07030e04020a020c090424 58
    0xa044407408a0b42100c0c000e00c0c68440c1e4200c40400e1851040d0808a11207460321080c0c6002c20058103824003100c801c0c41d0300b541c855103910090052404406450103101c3e00140002c0c03126602c2640b003d070349500e5420881c1d040c8071001040000311290141c1141040c080020b08030180710742809040d41082e01a01d040000091106803030a0600030310020034032910f0000d081841401d45580e01042030340c002c00003551349007000b151520040c1113620a0b80d001904008141c07101800c1061040b409454040c1080d2610140d49000c40b1061b1407407010703242100b040c5001040700d45840d00c8115620780300340d03400100701c1c1890081108580c002000225030f401079400c004083c00011906002c502c074081e1524a0740c2c001e0964100d582e48a200300d8804038400c5994039000c0c411041c4400c80c1403801401111043d50312440c1907401c0d8440c02d1005408616584030200361707400c10758010590940984151640003800c60001a9210300a0f141910010702e413440012044040003640d203136000300c140c0c040061071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 401757455 1250 401756205 401756207
    0x12040602070302040b0612280e030a050a170901140f070f0305130f12170906150a15031407032007020a080303040308161d1009170601090b04050601 65
    0x100785800020302840d11520542440e848040540c2c024608681c0c105110340360015981a0007003c801021a400f05203150108003096940f040000d14024070014514011030034006803142c1d0f0200020300c3c10800d041c8051840503981a0050740140040303000400c00441161205001c404007502803c04040c402050003007032a00520211005c03401070030081015503810b41c4d0400d0051500340040c0404c901c0b060040104032801120300000305168440c2400c1112130b100320b002045c8200d8650442764010000301e000010061402c0c034038680000e210b01c0d000c03070b00c1e1081e02d4034010420100340086521149844030b0410207c1da0607511034020b140c100083c6950340d80300030700000c1c46500c0ca43c0f10b0500062070819511820800360161411104070303580c034105480d000704a4071080341c1c04200302c900d4068030a4058840c0c07410a449540c8001c490811407241030030030102c00503483c1c00805001100d03900161070002030000c4440e00c01020090f26407907261520003025a1000b5800c81d10461608080002a03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 401758705 1250 401757455 401757463
    0x30f0305090a0b0a021303060207020916090e0405100e0c010e19091107021504060201141509060d0203010f09030e030d0f05030c130b041403391c0512040602 69
    0xa940c00500480303654982214500080c410070041b24082113081801000340050740d001000094400e584600e120b580700244004101460311030700002526401c0c041010341c00801c0165040382c06041a1920030203504040011031f144031401d09180d4100c1100200d8075a00b14510400c4480c1c01e50b9404500754001c1c21242c564800d0740101400580c0d201412500b021032101038600041d40500703203003803a40491804409940040c443c107001507081030444211980c12000700c50003029110546400180c12008004480c0300007460b080c0c01400c000000d8015075402d0195074554800070700e002601107898100240003000801d50640660f0090a1b41032410b03a1042500a0030b4039070349003880e00da481d451204034592090001c8040c5c3c0e00d80d9000041b4001ca8010001c0c0215a0ba6442e980c84040c40c1c4000c1c10740314001500e0047c02d2500c84101c40c4008508404054002c20420b9400020075005400142440c00544119686841e001c1900020003804114903e001e100101d880b6041514100c4000d42d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 401759955 1250 401758705 401758723
    0x10b0901080607050a1b0302070e0c040b1c0b13020406090e04050604060c09090203010b1201091404030f0c14030301090c05070b0105010509130e010c03062903061207060804030f030509 81
    0x8001c00055030f9451107106d0155544402012420325800b0405800c00030341c0c6802c0750140c140a400014040b402c48001d01d01143d080310070711940c060804400b038811800720041c3c4007918585a4480400c0c000c90760740d20703180700090241c2d0703500180c9881c00d190004244c84c05507082a0310204c0d18006000200b40000f0b5803d03805a40054085004000300e041129600b40f144c0c00091214000b00c0081101036568001e4240f142014081c1e030800d0b07903165030b00c82c00e540301002052341c415141c20119020902c25506070304884110308100180070b420b1740d20381400f0040501c0c502500d40001c80140300c2c105141c0111010540d49142c0a81021a5a240c2007829801842101d05201307000035060030329160200300005035020000700b04144c060005049004c2e015002c90798000a03c0c4c044003058981c070805405034554003410580300844d00120080102e540090b00c0998009183e003e03d500c050004c004080c0070307001c1542c60111500342440e011340310801034611001854101000c001110b80c002400c1d00e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 401761205 1250 401759955 401759957
    0xc03123002070b0705070506060a15030b0103020c0304060c020307050a150f03110a0e0906060319050a020d0e160801060b070b07121b02060a0b010813081903050108010b0901080607 79
    0x5448040403122200a00c00d0b407800600c030350401420041001e4200002d009000d0080b02590f40c01e0342c2d000204040c01c000d82c000d038048004c09880c1d00103614801e03403204021483c1814010703d080300101c086859600158042800034a600b45420300b10f0905002c52002810152035034203106050002007540341c01808005805c102c0d10040d0096624071075040148000b00800308656901c8001100400c0e80310401750b801d008001c50000705a240c00c1075002c43c1c1c1300c0d4003080c440c41382c1d0300d410444501c007034100034080c0f40c1003603002e00103d852805140700d005078045840000b0054113100b42586c40c005540c5501405059140c6103042101c0d40402003118142a8001c450540710398400009542500342c0c07072550400039181001002d038900c1500014002160641c0846803140e88003003154080c1e652101071180018900c7c00802c20892040000d0341400c0d2044502a00f4552402072812510f1002d241d10702c00640c5410042144000c00e10075085800000d44841c4142c1d03040c44030380340e590040501584 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 401762455 1250 401761205 401761277
    0x1e090a0315020f0304060501150206040201020606011b05060717090c18270309032a0607020102120a030903030f1505010e04061205011a0a0f09110c0105040c0312 71
    0x200d60021542c12140091102c000b0381d522800c1c81c1c1070074001071800f4000c40560b0111601d02288140c00050090320807503051303000300a2a0740e0b41004680030403010703001e00300f02808503091400040040c02a14800c10179560b0305c6072072004c0031049181c1000040c100e034600760045641c03040c0c0e680b04c103d2402418a0200151800b81e03c83d00c1c09940d01902c50f4100001c0c02c00c05501e40c02102c50301100034044604114210381d00039450700c05182c03034040c58102d40920040b080c03140302d41e40d0400e0005051100d00500558508003500440c82603107600c800700d20b40000743d079000041e0405406100c0e401041082400030041501c41a007421111925401100c1c148460801d804a181d560364010001801d000c415100c403c10213803a02601802100c280840303800c1649017503804900307003403200c041107a0700100b480c0c110f185840f81c64401418031a1165006c02c1d000c101030004441c09008a5000c1c0b403050f12240c000706e15604060044103182c00ba80c50404c96181504141c9121002901c20320501d0318102c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 401763705 1250 401762455 401762483
    0x2010305010f08121803030a02010516141e0c07060f0f090b030f090f0712021f0503070c0213060617010e01121401020c1603140106050d080304110a0801021e090a03 72
    0x4405c501c64100540d414440040c013030040030b80c1074000078003518162050f45050841c0c254141d6026100c100480120502481030b165500840c580d852400c83d030b40c2d4841443c021582c0d003a1803d10602d600070802081c200000a40201d40c40340900d441c2844515201c1c0241d81403000b1a030640c4000f9121105d405c150308046503c0f0346080c090030814034586e0040310104c5039505508169950514020f91007101520b190100403211010b0781c041c654051303514a85165100841501c4d1f42c80c001c4416038022040c008a50702c01c5c0c806100304405031801b6165503100f402003030424a0314000581140c5850b8880c8001082400ca42c0d0080511995200102034850310a440b40c6034024000d120714104640b0170f020031068045000c40341e0005803030080021040b080121701c992401c0e40c0a034802d20340c010280305000804151010051a080381c1302d070103081014a030050005028060540191307000303940c0052800c060303c150101001c20380141d101e0040c00c10003004c0c0001c42803010313440042e00c000c50031506 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 401764955 1250 401763705 401763727
    0x4060f0c0b1f080601090e1e0601230402070807020f0d0c060e011106010b03011805040206090d0609140303060f040b1c380f13140718050402010305010f0812 69
    0x118024000310f2048030583c2d03035a0b61411019007814800200135025100520030313580d18020006e0001110100104000d920302610131a2811450700000c00381c0e201407910401d95074507030000f480d142d03004001c0d05844030b0030380c0100718000300402052445035160303000000001e07009545103000c070b4003941480c00e04c1082420050b5807400602488014901861002041011901c8050b60603510f501940d01d0603c0503903c1a00704991050b5000381d403155060160001074a4030341c203044003040c0b080a000c03030840e40551740c0307000d2180d0241500c01240c00110822100b81029559034000f44400c41d01030000c40007420100d18010041a40b1741007841c040045141481402c540d01da03001c0242210001a04107040c2c1809145424004140410083d0001154010b50140c9200d80111100c0c07034020350b91440356070342e454070b00502c158100040c02801c0e00011002124046d124082d1180300c80030841e40b505100060071100e058220248489485405019100c80042c100c001282c049070030660301e013003400d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 401766205 1250 401764955 401765011
    0x403022803080f0f0c0114010b13090b060403120c032307060203060301181b15020c10020705031002070c273605010b03010516030b060d020c0304060f0c0b 68
    0x140a2078884400602840c41705015403140480d19884600803c403070742c0b5040a0b000d02c1c814034651212401100c9424056602154000310140c4802084203140c5940e80da80d0300225001d4455036008102109400e009241d001404401500100e034111803c910300c1410403906405813000241c682c41e40400040e8003528258030092510350001e400300e080700054a4003228025803445d103290003000b1004001648119003042c9000365099030007030a400d10400091100850030060b1a03c1140300e105070028103618140701d898885c00e540c22000d65120254186540292340070761044c5002c0700305940741080d4401081d250318070454504404107008415038480401ca0880b101c9151715482c02800b03194444141c44803614601c1d01c43d10081c40303204015010142218402c40300a094000d183c0c1210454920a9218054050005221904211550810000303d030000a0f540106503c005014000d80b40c00005100e081b8500e85040080d081180e5181c08040710041d140c25451305440c01c944000c81c266034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 401767455 1250 401766205 401766217
    0x2070b0901020721240c0e09040b0402180108011508030c120f0712050c010f141305070803030103061d010603020a1202120f071505042301110a05030403022803080f 72
    0x40e9600b002416040c007668229491800360075140003c20040c0c1b074000c1428034010b0200030320420a6995030f8a41005102d801802280d000c4140251070908215002d4a107002c0c10f802000060820002d08480c0c1070240540c202c203d995105211b200d000300310016a503e5099006001d040d141c100d0615184010700400b40010125004c3d40740c0c180300c0703591007005481c145140d02c00900c4600d10b0214454100d80030803281c0642c0c00b0ba10340010303284040c5250790020143c41341e412608280e6580d070310305045410030f070003c884054681c2c201d1070101810001d100d0701040180002c1040529580c0099070000349480b5888046012055060175035903040e20144d54004c00c4800c3d98032440000310680d46589083c0102e07242c0c044a1468004014403450580d81a00c0e0000c0001c100005c08503400000700d00c40d810000d0412103070256440a11790140800b61415204900544d11141035104101c0400e0200e40031144025010b2341034282c1d0f89070070b1426403c44c0c0d044880d0580e00c5000780400036142c402c030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 401768705 1250 401767455 401767463
    0x1140a030807050a15020c07030b070c05010e030c0f0f0730060b040c0f1d0d0f08070302100b062b060f030501051302090a0c090512060702070b0901020721 68
    0x101e042d4090140218040c02d105210740030612420410003042002c0703000311f845442c610380c003078541070000680c04510150440400d0038406011301d1305a07611030030b5602c0103058000c180c0000c00c80c40c0078404c04115031442080c48201401900c1c0700f080003590348205604c00e0820814003007023000d0b03a880c5107143c51803441131302e0802c00c400429141020303c0a01070391060750740620300e0528540d400500ca103401550402d00744c1d0b1203401c00c043c00c0703101c1c40c1040b9880184551242d1a400008001000b680380e803a10b0744d03c904036903a21103031036040280c10142c2e21903180e4001403c1c121564026a0707034030102c5410300704034482418101d540013800c0301c00b1141c0005050b600c5113091008102c943d40038014004480c404c0300288444e40c1c48050840c07100200b00b4009401180c0d00300803c0c0050401e41000e8040886840d1031400250381d440042c04c07015a080c2c2c0c08455402600500561540c10b0042380302900c1303401441480c1c2210200000c0d0385842c90310500c000b00d00c01a15610800100340d410b44041500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 401769955 1250 401768705 401768707
    0xf0b090610120f0e0a021011100509123705070f1b120203060604150b030a020d09030903050d090305030a0509130c180e0108060103060f02070b090106060e061201140a0308 75
    0x1604e1001e07070342d5052010f8143d00c940c940e075101d41d031010711a54a10a240303044801400700c10040080441c0600b41c040c101009601405211555581c104005031140310022034501440901c400c054862045904066000b070044e062200050030381c0140c115a03500703910690a4103a030b059420150703501c4003200500303003602c00e0718000014061030b012000140b0a00071020303a901d0342c403a8410042100c07080d0f51980803c3c18508010080342c0744201c003565012400c40005450183c000c0900400ca940c216000c6000c00e400c80810b00034013804000002c005000360411031503031400d40d1074842d030368003414050408001d4001002291601c03100c0b420300c3c1c22400d40382d09210004075200d0150003403003d04518504045154400030f845041d25410038100d80b51a4050060369085440d84005042c500750050040c42c0c08106040000f00c1a49980344200c10b0f100001940c2404d0500041c0704490000b51203200d0801030006010750030b2040ba0031411910104024040b490380031001c80d41880042d8009488010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 401771205 1250 401769955 401769971
    0x90a090f0b070509121f0b090105120a050d0815030a0312020a11030c01091e030f03050a0603080c0705040c030209060d0c0e130c1b0302030702150f0c010f0b090610120f 74
    0x180015415020700d110130030b1b1401326640d0140d41007280c24005480d80e003c900300f001000107007415607000801d080322505031840f07840d06465880c035240a0005001c00a80c100707041003a075118800711a0b5003120120080c0c2a851343c00d0314000c0010303028200b00c80a82d580025041882ca018140300308100000d003098945802c06000340034000e10040d40141c4420b43ca40c0d502425200070030302504034141d41501e039480e412202c124110014034000f840030000955641020011580070300182000c50326140007881302d82c0c2020140401e40d0b0b40c072002c0c1d400341801800081807964400c0256100024004c030002541a00e455040300e60b10781d01d01d041a00944895000c1c1500718040e044041c1807460707074039090031710320207440d214004800020020f40183c0007440007200500e004148102040c1c180200c10703003001801d40d50714180340e00481055180341e40d55250700f070440107107019034284140f0455142c0f486140480103e50114108200401001040b071450f40c0707401c12660001c3e4044400010405c41a030b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 401772455 1250 401771205 401771239
    0x111006080c0a0f05010512040309050a1509060801120204090822080c10050f0c07051005041e0f0302061b0706030b0310050c090112020c150402090a090f0b070509 71
    0x20841c0120901406403428081500340000304907600300c0d001a0f440519150303410026108008002c0d00450401980b10400036060b5a10304101d005000c4844090081c01c806941c058050381d250b62189040c00300d100010000a510510140489a01686e001c50001c030589400202c1c1d11694544010f03680446240b1410360325442840d20613606110111a8152440c408102c0144c003108008070001d18200314002850745100064201e01c1d480400301c1d1101501d9100050540c44501c3c0c941b0002040403030100718004103c0202e0508000c02c5607801c40c51801c100e800140d02030980401790141800244c8031201c000041c5010001d00802e1003692481505c945000b0050410f00440c1482842508030500004400c0c0c4a42c4c8d00a02941d1805031030044124010340d12001102ca280c60b8080d800e000202640341d00340240c0c0042440741da90343c0b4061506104010301e004024088881091401c02c0e002d0004513880e0b4601c01d0150058511303040390381c0f0450111075511848010035040a04011528411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 401773705 1250 401772455 401772463
    0x30c1318020c10050124020f0f030d111602010f050d02041805070e030a060506010504030218181b0103090f02100c030f1b150e030c030c0c0d020d020111100608 70
    0x15551050550311810b880a00e6a000e584c802c0c002c0c41c4c48554044c3e824112544020752040c081c4c0142c0c0143c1d038500c880303c8652820140f440400314036603000000c40c0c1a40c9040c43c2700394010290341c00501070503c004601d00c03240c4c1484101000f8184a03241c414000204e02030003e84d443e030400000c0a40d1b45e26220082c28102e01011640e9640d210305050125036154040e0860740c1c5020006002807411030300740c2e140c42e006450040c0c101d60500c00208404005a240c100c65412075003543c0712628005d0a0021981c0007600320001d0170300701600203c0b4440101c00151168001c1e0340e0342441c0100d202c07070070b03401d08540e00c2c01c031084000c0d03110030f02c1060312043d1a0401e0303140c000079000c1d450303090350140f980c0402c0d1142c42003450076424000c6000c1c0c01000190a91444042904032400000b940e107c040c55080e00d1627220304508201d5600114807000c0c514820003444688030710584034920340140c0366011850007091882c00034140040e070b001040c80c2d040d00300400c251120121100380400c1c0d98500b210b9481d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 401774955 1250 401773705 401773717
    0x40812090307020a09020906180604051503091b01050f18120a0b0109110409051302033007030e060309014502031903030e070b0d20030c131802 63
    0x54011340c0b03400502107a09100350b0f51000170142c442440c0640918000c0790f150000322810394008000e00003c506c1c0d07201c01454000d441804c01089641e802c0c8140302070301c2c05500241158440321741d800c4000b4140d900c00d00340d446042c0309a891301e441e20350604d10b58030780e855003141c1c1a41200d01412084410840001c410b10114010b011320a6203913200d0340c000c401c0e030351b105081c03126100d01000200090821684003650003108140c00000002c420b9001070305200d1410b09840c610951014a46081000c100480b03000c01c1c88215164500401d554000e4500c40107103e805100340320104c0011010042908040c0c3c13031111800840d40d8012807049844140c0d809910308003200c3c02a00340701c040900407a0302c10510550010010900f409803540d41980d0045540000c07010180c95055140c5d009104014074000b412035011500d0311000c0104040085405150a19400a0300300702d003d03114082c10070449030058151001c45a45a1402281742d0624645501600c80e07014003001b5855516000e50107000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 401776205 1250 401774955 401774959
    0x10e060d110a0f1e09060c060212011403060108150708040f12200307050307080f0408010603080306090a15030312140109020415050708030f060a0b031503060a140f04081209030702 79
    0x1c13860301c0701d81c0c0480e00041c0684410200c0d00c00007045c0a114014010452410710480000d8582011850700c00c0d1204401c1c1d000394a2200802c21003c002d140910a00740940210001041c00c042e040007240c0e003c50b0080c101900b0b0201e81d401040a210140c40058522500051150b0300c01c0c106090080c03804200c00340d50841e11280030304040c42d0745070110898800c0c6030400020b60400b0b502c0c1e154520142e1221820f44401603041000107031f685020b004210003540074403203407031b22440e0940070700c088a440140001882440c3c0f400d884c4103047c01ca0000c8082d02e030103240904000e65086400c00c0180401a4901d101002010001945880c0f0f50000c01c203460403241034040f448000b0700191914020410014902201800010b4000321040881c2d030b4440001000000001e9842001e80f2680c1e0090300d900900000c845035030040c5041c20800c00e6006201c41c6010481c00d003105a2551001001800303464440c513460b000f14060001d404265030385086603100c016014101b07506c100e9902d81c003c2d40124 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 401777455 1250 401776205 401776217
    0xa0c05010e150709240c1b0315050402030a030e0f28060c0b0106080703090204020f0702042418090b07020d1205240a080607180b030402010e060d110a0f 67
    0x6903000707100710100390480300820404001140013104080024040104036010820661550030110783d03101000d0503a8504c20700000d1f080c60950130300340304444011281c401348908290522005890015100070744070b4141c600902196404400a0b100d400300341c102c5035101403a80c25034a40808018030301c0304100030030070048000702d40e01c090554110380c841c4030180ca004401c03401000b84c0382c0a00e0100e58800403d1134002640d004a07800a022030b00030b652026030480d00400c005085003001c2c032075030000c0400100b4038114603082d0b0036504402242400380500900e100d0180b1043d22a50b0f402c0850f4117a03100e0b16081c445e29006800a566160940d1508001402c41c2e10031070284c1e441d8840c060180c1036000c500c118041c80d016410048421203421550030804200000880140921000d8003030600303540c2c0c08510013682450504055015000303007800b40b204100303010040c2c2c0c210034284510b65040d00d040c1d8a1780c8141c002c0314020018901c0d00b5a0054000500d41d800035800000b8440d8942e40e5202c107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 401778705 1250 401777455 401777461
    0x18130f150807050d0c030320011119030608031c020910050307170403090b0c1608030910050405062a030a0f0306060f020c01030218190e070206040b0402060a0c05010e15 74
    0x1005040d40e40150170280d4090781400400d210b907006051340c04494032000c00652806030000c4c2140c052003444001041c002c02c10400380d451405019515813510314003845103604041c140d035124440c581c0c482c280001d100b030017130015404a40569030716502c020306a00000ca081440982194000c88880c80055416404204041c00b24a04680a03540540d2105d81c0c160414100b42d05075800942c00c010301e031003504803640c02d0748030b910103540c050004140a19260021407042c0010b4003503814441052000130b120501171030300d595040c0c81401c031100c034840c66280d4100808001e070500b480010503031401b0000c1c8001c40c580c0c00c10b11542c051800c941c0c041048603607a08088428074500f510440050300200e041e8403541d8820707005030450f44d42c81d081c2510964100300015500360380d0040401d039000c6044400700400b5964400e469441100c038000307080d0038a030541d1040c250013802000203110308400b0a034984594843d18000195035032040003000580108444603a07184541c4180d911381540385800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 401779955 1250 401778705 401778709
    0x70305011b090b0f0f091c200307180f020f032406210403050903010903020a0b010b0a020607050c0a020a090b030c06040602030a0c050114130b0c18130f15080705 71
    0x88440d104d1103200114201009007501c0708896000c1c50140e94040110904030380d414081400071082c0e0b52041540d1750303803c110b480306041074003814003800b03120390803148040040c0800466045a820603004000415000c4c0f811303540e00900856291004030000841000003c5030310181c01490840c903000c00300620000e01d002c20065200300d0a5045100b8003d802e0b45062000c0000340c981c10604c2420480c2c20300a040c4046821030704480000d0300164080c3d59100240008900d1090241200010461802c84040d2020b50b4501d4085c02d002d041102c0014070a40061045c0710719014107500070068a0381986d20312204c00646640ca607001d20900030002c0a000e507150100c101e40403190711340c01441c00c10380c5d081003e1301c1c0c031802c040c4199115501d84900413004608051002d03c80e040c0710b402d00e102880d80d410035180040740100018a040400c0001020f20764a15400e810003260441d5814a80c40076060f62001600203d0800a0414240301000c6121424110f1100035588204201d800503079890301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 401781205 1250 401779955 401779957
    0xe090f15070e0d150203041401151703030105030a02060c012307020c0a050a181404030503090d09210813141003020322051f0c0807080f010b0c070305011b090b 70
    0x20001c0080c4c56501c510068a4580c0d005194458003812940544100d2221803600352000740080c01d0482140c0b41040c0311540620030050301c0000070388000d41c01c640c1403001082c1d032111018406072141c100800c01d1084c0020941225240000040c0e04500d859000000403442d1320050300d100000d4003901503002900d0a0031940d05048881c02420040443c2c071f4001c426800c0802d0803502d4652399150080c2c2c1c03005240b007904040c099440b84d502e007562803506015480c05c8c2840c1c1c2203120100005206c0030403550b80e81c0081c841d41040e02140710031007005189082e244901c40e8500b035140c22070f81164005030303002118250b03000004091300c2030030b1000f502b42d00071812840304032407889990140300001e80d8068441c41d0368ac40c0461203003048810900c00340d45a0024510050040644141c890b9541401281c2c09908580c110f0300d581410036160400750480c0204500500580f06004e0700440c1190100c04108a01001150024002c110603003c5415081562400d113a040e400305400c04800181d0b03035801d40c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 401782455 1250 401781205 401781229
    0x1b1206120b06060d0f1b1d2202040e150d050c010f030204121103060c090d0f03020f12030a0f0507081801060f08011505030a0302070b0f0403080c0102030a061a040e090f15070e 77
    0x140340742d04c0f1178103020030482414840e0382d01d048c0d040d01c403842400c024003281c4002c20107481842c403000f000380f401d100f02b034000da0f00101049010700d00300d40c0035100040e00007914600c41a001d0070300c1d05100c007201e0700480c000d01407039000f29080b00244448a051001e4441a000300d518160195042c0c3c0d03540d0411400c04d4414201c62607000300016180c100801c880c2c8031018241032081c0306581664040070151071410b181c1803409540d40c8400000d028401205120b110b40304048010103110300e14250380c2c05020018000c0c03100b140082c0c44c00b100302c40d9a90039030011024014031108020560b0720360965600034440556003c190700b032044804102442e000858404071603050740240b2800b42800031081d540c0d0080c5000380c4851809000200000e40703640c000d028142020400161245414209101640d00c0e650011304101027401c1d01490400081080380e058925021040c461030b00e40d0702002e85880c0c0070602c0c10f4040d0003100d074401c9405506d4450b241c081c80c02e5a50340810360300d0034010800e0175030784a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 401783705 1250 401782455 401782487
    0x12240303180d020a080d080a0b0f010e090a0e0709290f010c050309040518061e0114060c0111030405071a04150507061b1206120b06060d0f1b 62
    0x81c40003800c1d9032520303040030b0b64410f2000d408083c4190382d86920514044911a003640854038410170055018090322507400f240c01c003115804103201046001070b09495040f4002c4d805203e0820000701c101c9902d802c00310704404844100c80d03e01c0d80d140c041c0d0004001d40f03013200c8002c3d00380000c460030004861002c000900001407001940090040c01903654103020078088440b80003d003d2500b036039544d485000c0c881c502c11385880a8502c01000c07904d007400002406a103413002c005e103c01d500711520040050651300e02c2140010030306070503000280540205154141e07290308008a103580d04100f40c002d103000e07c0c400d2003115017040d11060018645e5481072941c41002d43d080c4020407011a030844050410940c6061061400069440b10400c0c0e9101c1c0202e020040c00740c003c0c81c0e5486a0058100078541340c105010800701e402c4c0321240042442c036440c05046507183c000030030307034681e1020101c48001c01d29a404010000b801c1845101414021a50818030700651012040c01030007001c880000401c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 401784955 1250 401783705 401783737
    0x609080a05070509071101060e070f0203120403110106030501021c11030f0412090803130305060901020a1d04180c050a050612060907210b10020712120512240303 71
    0xc0c141404500c80c0010420020401486c41c0000707844030030f1189101030104a10701034010300e400c03100607200b02d801e1840d400031980100700c00640040c000100c2c0350000d9040c50311500408104000601520454001511951002620320400c030baa50700d18801c0324034482c0061000620b09010400c2600084542a20a2000303000140000d41008280705451049040101c541c0c0d49401440e403860b04030300340c44000706488403030500a12800b0400e95501201c448025441d00c6010400103080c140250300c500041d62031115045d02d0780c0d60355007041140f000683d000f11610b440d80d04220341d52505500c1018041d104444001c500d60500c1c0080f142203402d144031343c0c150782e2511010302080e400b0040007c02001082441c0c18104040da8002c03c14040482c440842e62642d840c0070054089403c0b012030041d07600c105000c1202c0c0f03641d03082001d0001d411030a1164100540c80d029502403048070400340c410810f4100f0440c2d080702841e0b443c480e14003003244000c1d00c20304074400c0c541c0c1c0e88a004040810305030303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 401786205 1250 401784955 401784959
    0x303050f0309031903021b0c0d020613150f121811010e040c0c02040b09010602150a0b0409290130050601080d140711040b011709070609080a0507 64
    0x320300554000e250082140c3c0790401001c00b00c803244d210718030620300007500090790640d04050000d212003c490300c04040c000407e25203000401c078443c40c6200a01903200420001c0d03804240d00c2c40d4030000d000c9004040302103506e890008050005107141440030035100c041300c40a5084074460441c5180150100740d01100c2e098503404c046c142c0d105501070401101580c80005034666008802180d034076601c560703003d00030b6441040261500d407140103024218101c010441140e0006900c0c9030010310f52080185519400c018202502d00001619003090508001100f00501d40b00340c0910300c001042691181c03036904e050350500da9003e118242000c0001c0094075280c1c480000769502c541c0c095159020b030481941d036410304010090344003107803d420000301c0c1230907242c006c08038000e800144c80401d807500805030f44071081c006090011900072541c64090034003e034041e400703030701e2000000d42082100c0e2410560030380d1758081c82d004520024010303210025072418000382c90440e0316030000c05081014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 401787455 1250 401786205 401786227
    0x20f1b03060c09061303140d0503090c0f0a0807030b040b0108010b030d03050601091701020702090601020610060c110910060207090605090f0406150308090108070f0c0215190905040c030501030305 86
    0x18001070f40940e0300ca08100083e041c40c01a0001da60003c500c0340c1440d202810004103107078101403c3e04075150520408004220b001103001c114155010400c03a0030203108508900400c8199643d41c222031f06501c102207005c07061002c041132081c4140d22641c08950240c0e01d411065090762038907100d098143d400740c0c09002100c2c2c0650010303540004d0615151000e15908d03c2400c3c82d4800000a0120b56540055141c007903041c038502e1268000001e0005000c1801d101c0400003000900f485807208000e001d02d125410415103541c0c07001221001090f0060790b0030300d41084030701c01a8512443d800342c03003003d20014003000503000f00001c41e030f4001c107044141d948654078284d0f039070301c0100100c0c0d8440d60b400044a20540c90380c461000ba500451002d911100040000f410200b406866001444800641d115416070300a0010b00610390560b03240e2016621000450400d005150710400700b0081040000540355118000b5412a0000c0340c05200c03c100081e0160210f45081c00098009401004003403209 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 401788705 1250 401787455 401787457
    0xd1d10050a0b030d180f060504091503060518070f05061e0f0f0a0f081009180501061d010b04031e03020a06141504110405040f0b030d020f1b03060c 65
    0x160000e0070200d05007a0342c00c0000d003412888102e43c80410842800704507010b00440e1014041d12428503081880e9081c0140030380280a1403040301201a1150500e083c40302c12040c8007001036a0010f000d1005041802c0540503a40f0070360102a142d01c500d007000078089048056130400c0341c030040c1000e841c1030380c030292204030480d0800781c0740300854080105814003001e00004000c81c021081000c1e86600803207400801e0400040104420400440c0a2080d007403002285a0110f1f000d141b0005240303000c1c4010501c40c9901d491000d03004d9441e001c0c0c000f40d51401000700c021075031105038076000c03e41e882d0811030b003a034042d07800050090034007000b05509220307482c1c00429026000380101c030b41c140c1444d0f80f4141564408000700b44d0b05005003051226220419210780c03881c0c0411101404940c0d6001540c9540e40a0741c415140b041c1c1d201c00303030041ca034032640c1d00c903042c583d20240c242c0c2c610721300f403c0010b90390b240d0060606010340316a240c2c61040591800443c00c04000050140035140c490400c280c0321 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 401789955 1250 401788705 401788711
    0xf060d020109150908060907140d0f060e01050105040b120d0e0607060501030528020d0206030a02040e010311090c1810030608030a030c180e18010e070602030d1d1005 73
    0x10310036010008521440c1c2d44400003120281d43d503130501e006003800f00e11420420b0141402600d588071031070600c41c1d40100d10151005401c10b07522801c0b15071050034103203040d0325002c4e03000d030556280044a011000c010340016058a200b500c05101041c2a0004d01c522440040c40d12500794100b0240800d81900c81c2c070640c2e0034914000c19090130300b0001d4845030308035102070b07004580950217083c0468441c03180440007003c044017071800044165031a004641c0d0103040301c0d4024452140040083c002c648507506071400740c491940321903142d6850b86403c03a0445404010300384101030800c00a1901c40d15802103542110a200c806402d54000600b4004501c9800b0320b82c0d0141600e40b1004a04044104090501d48030349543c0481c410f1040d50020f4648a65104da08545000b07031f04092002d48a800d100d5604400e4110705010104203110a440c01080702001e8095180140e01000907400d500001038a0840030b0301008000070000158001c4115110a600350041c0d008402042e540e00030b00d5006542c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 401791205 1250 401789955 401789957
    0x1504060e01060509104203061d040c0b03190207030e060d14010e090304170f01090f0c120c0e090f07120c080c06030c0a0908030a080a0507080f060d0201 67
    0xba6152283c000071800941202e42d0124110600c408201d2540c003014007031170b40f0070f040e88a000840708008514046207000ba00d000020403958580d0141540b00b0341c40341e4024460140314106421500244500c0564107031170030b075a103030f44001011801c0007403c81200c2c01001144a0046244e80020111003c3d40100c0d10a406121403100c6800c400d80358a00180170b00c44030f0580c005032911151030f41d90030041041c0c1121310919110800c0143d0340360000f0813034042c0c420400d401d054001d0300071078803450700120f240052230035403d20600800700020025000c0c0424450003142844e9900e489140c0031600c5041c10241a030081c4e420704000110340290301c99001a4050195041110207100342480c00300240e01c82904846060440c0b014005607a03c40c0018044040c040c0140d00c00b140c0000d2218000542018900d520010b0600801c9000d0395281c0c00030f056420075691201407401e4003401c88401200c0c001c00a6042800050907035114000740c511174495100880b80c00c0c0c81d2001480007000400104038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 401792455 1250 401791205 401791211
    0x150a1103011206050901110409094b05100f0b091510030501030209042a0e070e19090b0301060503010227010c050c13060b030411010801081504060e01 66
    0x15050420015030292480300070541d1650341c28070f414000c441e00101903416903450030f90384080003016041111f0859a29050119560050b41480707862858400d2010143c075400351502201402000300c400c14034000c0484c81c140c080401a03d958a20303021040003800390b0448420241b0385011940300040c0e11000c520b001808a2002002c1001c5103030954090303414840c8240d01d0409403030b0950b841c034541d1010b840e083c0000d51443d0f001c103142003c0508000c10162000507241c6007171201c0082d11341c0208100fa02100d10581d90522150b24540a4400f50002030305014400d50905200c49640030246a41140c0b000e640d1900504100500341c0c001342c0c543c1552a1740c000100c2e42e5090019007118034440441d10880380c4000c420005a0400301c60490621160890007000300c2c0c4003150303403602c0c408195507440b924108643c22000034109a04200000d06022091000340290700c0c60420400c082030704e4000c070607600d4043c05a0340b5800c18410b103100a0a40001800041ca541c01090000340000008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 401793705 1250 401792455 401792471
    0xe0312040507080d0804200d060603050d14040b09030c03070608151518060f0414040b030c0907080702030421030215010f0902090d0203070308071a070c0609050a0203030f0418020c150a 81
    0x2320040c45d060810340355035845082c14814420b09129060b060185070929001500d1030340c10000990240744182043c0b598007150000795a20140a00b07580058002c0980d4101512003002404151040e2900b4a022000c0960b9113070a0610041c43c800310120508030070708100200020740c0c1c0c100050000c05410910600c0050200e00502d40500040c0a04084c101000080403003440225003040c1c101781d03c20390114a43d00c409840e11500343d81c2000301898002c900d540d030410140d1440c031496000c1e507441000862094000c8410408040070684070303500ba45c841d50791a6603024003103d000e00072900950418242001221060303801049200000b400001e40700070150002820022103038001c3e1800c80000510104028a1041c0b1010240d0a00d9000f80d681c10540c10040c044801d900b00105480c1da00c0039481c0c05e01c070b000c03c18510407540c020100c03656000b0009805000c1c1d045886403d01010140c20128040300c01c500a503040214603000401300d42c0100e81c041c011314400501002d01860b07682440b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 401794955 1250 401793705 401793709
    0x18040309180b01030e190312020405060a030c1806091403150106020705030d020d202113050409080a0c1a160822150e0312040507080d080420 62
    0x500c08080009000000d0140b01000000d42503c1410071901a41d07089004201035805400c4e070a000038a402d89014510300414214440081c403c64000c20751141e00804e20290103503054002540d200a00e075150511006145078100103041e8500881003c1024000c05015032580d1641c00b40c0404c00c01412150111201ca651000d070700c4083e001500140c100d4441445541000c1103078101a01d0703144024a5042258940108030b41a4440c42841380c1070200c1200c4000b05003000960750003140c1c9030040e00c10140400208070b56034000c0e410720440c142008000240c80c642807156402c0c140d0801d560602e001c1e20b100e0210f4020080700070403244085c1940c5504a00d95012003170301c2c030684007e11610500c0104542c0901750f17400043c01c003ca80d8500f40900c4400040c00c807814444c0941c06804101300a035040b1110300034251054012a180c4400b040c284c4005c0b924200c1c1901803070190041e1010702d40c95004039a1114a06000400030840d43e102060000307150a0006081030025080300400b096a180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 401796205 1250 401794955 401794979
    0x30c03020a050415034e3e0114040611130308131d1e0910090302100213050a05032b0905120616021f110f040803030901050a020918040309 61
    0x2940c84002c15004214489000405842c6c20200d41c2410003010761070391034060388840100e80b400c5118aa2000c1a2200311136001466a00022401002030100404090340b0104102003113401381c84079030500001d01107114100302240c0c103040140c0354002e019810740d2a4081d5036480312800140301c6a12000000d000701e43ca141c0701c103d524691040043c24241102c0000401044588107440b01c9481010301c1070358040000c10102102c0d400f100440c00c0600fa0500303a05103500504013001f8076000144504603c181c02084070140d0b0411260740740441d49807803d04d542c41a48151008440c0c034034401c0001004801a000300d0005036620b0010354103511100455442e1035140e5084202d9440b603001d10050070005450920403184c117200030000d800c03241058804400194075004081941c407210b40251100800454441c001110520380d521641c1c0c070030349903823980100c50b8500103520f030001088031038826008503200c109000b070004500c0a22455031050042c4050000c80c24080e24002c00580d800f0352403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 401797455 1250 401796205 401796293
    0x9032003060c071704060e09190c030905010f020f0703081306060b1206010f0905040207051002040f03020a06051804020a0318120e0910030308061504030c03020a05041503 75
    0x703100103845240742d180c122040502d00c07510b1381080200b03000510817140d11410001c240f0b001201e13030040d0b42e10b400929000d40600c2e00c0c2c580100f24103004a4900154240e000503d02c1403140000704894180c9202070000c0b40031342c0c01c02c180e070404200a1900400d00c50074140d034000341c1825110704080d5160365803d00f155429800f840c80030001055a591001f4007441ea10390007042030070040f02001002c20003d088050b24015135201c1c55022621006003c41041070f05070036200714070210343d5075071142403003086e0114a00c41244211200040420094412000c0d1a40c3c410103924014241c20090300b040042d402000c1660101aa1900078038030030318000c91010b000074003038070038003000240e0030200400388503404054501824002c018020420044102c1c0e0044a415292000442d00e40000007070140601c04055450340f10041808014440c044c1a20021217200301c0e10b0300c0740d081e1f40760706100581d04011030b03c1d103581c24269000c0000c50400f2031007040001c104103122414102c12441034082207041c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 401798561 1106 401797455 401797471
    0x70e1003030e0904051510262a040903110607030f050105030f060a0c020c03060a06080607110c0103050405012702090a050c0a1d04020301030b0a06150903200306 71
    0x4141c281d00545010050342c0e03484141c8107400c8800c100c555070a20030070300078014040f0045d260014001603003010309000c89c0e03103546d26404200041240c00d4003079003449603029902c2074120041c00001d01c10401501d0004140356203410050442d24160003040c041c2d40183d10000054400046465000c2045940804d082d40805022030400781c101c03040e160544102d206100401100381c02c503600307503228101100c07400c0d501c6180071118072281d007030589801d410000c03400c0d00d294800d801280d407007801030002158400340301c17125641103140d4100c007190401121030041c08501e4070540d015005000361200784481d041883c081d1010384034904105051107200915208000701c5ca2000b5040c50900400c11034403036035a07003411184440101d0703500d62028a40400858190300c6406401903d030120b640b205109421030342c5d1000400800c1404403403101c15a9203505003a030b010400c403485100a = true := by decide +kernel

theorem cover : BRFrame.Cov 401618705 401798561 := by
  have h0 := BRFrame.cov_init 401618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 401618705 ≤ n) (h2 : n < 401798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
