-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2563
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:58.071445+00:00
-- url     : https://prove2.me/submissions/193e3689-614d-4b6a-b7b6-0205a334d818

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 460791366 ≤ n < 460971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 460792616 1250 460791366 460791413
    0x80105031504023c0603010501120f0608030c0c010801080f0c1003110d0b090a0b0109120302190c0806090708070b0a050c0d050405040f1103070f11070e0403140304 72
    0x1604641e208070424010500c0356103155501100340310984c00300003032036203800349111020306143c0d10b6240c0709089a0607600103139601c0c1c41c030f00c446601400203494a1601c00709080d44419010448031810030240c0301b01d01d0000020255815104005054003106801c0f042c5250070200f40c0683c01c110001d0034040380a0305941071040401c088004034000d100e05114001c0c007480000714805018081c0d0420220000121452062a158900d1420880e1650180c1c94003007011404200401200b910451100b18000e0050303034000441700c64013489207155403000b00c80481c04a034041c011048200038180d880f00140d0018144c040c18501503a0759142c0c588200013141c4000101c1c004050301c218141c2e504103041e4030440300e11501c200300182054010f40106401185080111309190010b402000f000d403107110b080505c0d5445010007183c0c001a000311000c2881550108850369100c108007a20007410100c0348518941094a0014110b10f0140748040400e2414400d001c0490b8000300f941040e0145c1282c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 460793866 1250 460792616 460792621
    0x706050f091305240f1002070918020a09150b0901030e03220501050304080d1d030a09060216032301090b0903030f010b0a080a0c020c03030a08011806080a030810030b1311010801050315 81
    0x403880c023100c07600980380b66403c0044040382584100c0c031289410f0b00c226462406c840d11244440101e07400c42046402c003100c18001001a00c021400500040c8010325022903100c0010f1101d40c516845980041c941c00c900c00000e111a2150540c26801313010709180980c61070405844140b510300032050f01256061f918849109005003903041c42c4540c0c2c140405590700c44c1650300d80601041c043c0e10402d0054014091000201461100c2c0c40003600e500c0091130410042120b4004112101e140d15540780759039414015002c60b100f1002584a0310544004599074a480c1c80440070488061b400742c10040c0090010800d61508600b0380c5074012b25240000800d140e0880301245080d01c460365064060000040b900e4a01d80e015150b42e040e20001c0c1c100d0b40a8541c1800b034041140c0c914460701c402038104159050000e841108901c0d004880840040300080c0c07030340c50b40c804d87c22056030f0103c0c0351200300000301c04020b4002040e0010440c2420070704200e41c50080840d03103a40e251020340364032503001e500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 460795116 1250 460793866 460793899
    0x40b030a0822031a0426040e150d050706020c06090109030f02040b1e041d060115030e0115050907030603050c100513030b09060a0e0706050f091305240f 67
    0x2c02100642d040b884505500c68054004507503410700752010307174104004400441240610301003021620742501c94051526190901440c8482406010184556040125031100381d40d0200c0314044140103801911440e8508031000c3d24001e40449918041c0909010300d41d41c503078206800e54222078102c107124401c0b03003071840003c0c01442d000ac099a40a030f090622010104100b07110702000c03160a4a040100408070010f60500507055a0304000039481580144491205800b43d001044280d04001c1041c3c1c1d0f004481e10b0a48034030f103041c094810b0044c0410041d42c90990b64640e01310020b414104500b40c15922007945070001010383c0780c003508800d025401050b2084003203402d403414604404000359101c1c5048001c601041e5100c41441c400c110200b442000700c2c0c0316030907070711030b000c1d00034815203150280554503600301c8900079025180c1404448030a07180c00e6007200b49003000c290000b0710751524000c0c0c0c500b180002849141951802c12282c615601e6081c20141440d00865070003003510700c0740c01e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 460796366 1250 460795116 460795177
    0x20103020d090c080106080a12051b100c030c0f090312050f03040501061a0c0a02040902010509061908240405040204021c02090405070e100f121406040b030a08 70
    0x150200c1580e882c01c104202401000703840d120079109100c00074480f040c1c1c0c0d00a0950f44a14a400203041c80681140c01501d02d40280000d01c41c1c0000c0b20b4a03140358441c0c1444445c02c0c41c2c42d00040e4031445445000d4888007541c503200300c04400f2003608154840b070005000080081c011804010031480b0f109151805050040301520140d00c210a0a030f56640f6051800501900e020711603484510885011103c113141303d80152021107400b00000c05454080740c0801016021040080c0e05110007089100041d8848200811070100308a40707030340c401c1d2101003008090400041c01e0301c1a10b80c0c0c0d5480d0201248a4850b01c03c3e6250040f20b01149544441c0005002803154101c00b10700841010000440c460303940e00a024a41c900315000c104a5031410780540707440002c6021694061440340010341e5440c080c00e41c45a03070003820300c0d2400a800e00c2d03200074800c0b145400030201c401d42a0500f01728152920340910310080c08154042c1201030780a07507410140f4010310305510352807001c200403188440080d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 460797616 1250 460796366 460796377
    0x50618030405131d03031311040902330f0f0f19080403020106050109051809011512023604060e0a122003031617090f070f050303070f02010302 63
    0x1040122559440b800190040c81070180044240d580c45846144d030340004410f91b80301c1c516191203541c0010141c0d0781d0b903c56001307092a2682c015516085440941c81c0c0000301c4c10310380b07015550b00c00c000e51054500030301107040c29a140d034a04001c120400320511900b00740c1746a070f40712030035090321a0390240c2d0191883c0256000040c40061110440320000e80c0003100318001d82c0240c00800c0080d40381c00c0112070000d860b000381e60700800016404400d800c3d1004040758410845000000c54800031440b55001080316800562440004804541540b03040c041d03644a09116520718003801400352516904446291a40500c1018400000e4140a40c913007141030034000e61000d9403032208480ca40031402030310911503e40040c0c0c18801c100f034606a2a103020954055050045082d5566291040c42c0200b29135010410891100d0085106910071440140212034950190894607071001c0014034100b107585c480d00004220340020052900c0100c1110344140c4c10201c030035661121790006038064400d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 460798866 1250 460797616 460797619
    0x1103040303050414010b01050405012a0818030303040b070309150c03020a08060103020702013207050109020f19031b0e07020d090501020f0619062c01060c050618030405 74
    0x41108240c1e00d54091849284507030000c1110342c600d031055908030b5150362202e50203d1001c010a208640c015044620034040c0c01500c10b4800c00d003000d216030344a070401c0c0700712106480403030622004521020450034040d0f054000794114a060788890810f000090114010b060f52400000306020102e0440d480e20255540c0a00c0305410f41080100207500001030f00002809241c0070070055842402200c6c40190140d40d4020600040f00848840d041041601e540400b0004c2c1c00d207482140610140840c1d034020300c000a03500006005003c032003c9550125031013490b040054040c0c0d41c0c1e0311011401520b81000c000e2104203030015868042d058075420003040b011101c0c0800400550020781d05079010055501c02040d65034480040e43d8910024000c00c416402100000e0036121030f0110740c542c81d40c1515400304880e9690502903032402a120f5101e1323a803d99040642c0e82581300c85000e02c1c0104040d1a25018400c0c423504d61944031300c8080c3c10040c00b065400c3c110035040303a0420a41d40034050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 460800116 1250 460798866 460798901
    0xb01150c1a100b040302090412050910080f060402190c050102090a081b04050c0f130b0301060c03111203060609030a06060b040f0f14130e0601060e0909060105010e13 73
    0xd2801d2881c002000c11120020080b100e641d02044503001c401c290341c100c82e40030784401404d8940d039407050100d290295840e008c200b02440300300301903612407a604510461300e4607070f03c004c1e0030003c050b040000c3c00188840d00480c010003141049505140340c0320548825480c20000b0384541d890402d01920418052a500c10000a0301140d0b049000c11411910810311482c04e145541c00020b00040d01d01c02c881c800440c2006001d8810b100f0224130042581c0001d207800c07000119240d02c2c041e01c09810a0700b01e1000076680c00c105204268100e4071940e103401c0c0300c3c4020041c00c5a0820036000300e01c00109100c2c001e40c00490308101c00d403010002000c84a510060502403145c07584803100e0540c115110390130300300843d088001030000c490041d42e01901e010100b103c95044075142400003c001c02581001c1c542d5607a9021802d090041c056240a090139a07115480c0b1000c1600700000010040d014042c41d400081c0100826038001d914003904910554460740c40360f901c4040c000081024010380c080300b01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 460801366 1250 460800116 460800143
    0x7050d05070b0a0c0c0905010819050606010f0903020604060206010611120403031d09010b0d0b010e0f0d020d08490f090c170f06010e040f0804180b04060801090b01150c 74
    0x550747d0070090503a0001c41c100d03902c4a21400407000310300407140300509079410081c0030860952291300c6030360b04500301d07040040e810760f0f0b0303a070100e0300ca0381c000c0e4071030740060b048400113101c12a4840c0800d0943c0b82d400c401020000055220b41441f4070076488001c0500ca200107004014841440154400711740c02040600c6640e0354101e6280c6a41c4141c18800007645070181c2c2c2c10072580100c3d07680900c1140a03060564140c20b04043c4031180d000c2d10ba00740c0c1e20500f40141a030004115600070050101070f01404c0389801164050740c18a04a0802c000094460b115900c0b0000851405130910240b40c100022504480d082140390080061001c05800300304040404aa03243c2c3c0342140203800c80e11031044030902080b18101e40e444070303070a00400c8101001d07000400d0103d00d41040480d4000c2c0504110703864a03940e1020301d01080180380070500010b03110346048a0900d07052081d40010061800240312101466407109501b4405000300c500320501d40110340c14840c0700c1d0040d120701c1a40a2030141c10750 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 460802616 1250 460801366 460801379
    0x3010f06120b0d060c020115030f1e1203140604020316032c06010509010807030f1709040c11010c020d020d030905030712050c07080a03080c0a020f060c04030507050d05070b0a0c0c 79
    0x2801c5c00c01003e03001d91700b4038103040b601488001080c0110380d0051002d070203402c4107a07030340100c90107000d42c0c1400c5020014038440101d00130652005403001192000518840e03401d034121090310005100702c1c8990320510070460481d0404081008501c4540340c00111701d04425005d44032003005a040c0b56038445154461184200c00090540c140d0f902100d41d00120b07070740d4060099441200f80401405c0b1103446003070f00001180140c0811500e0f0b89400c03d0b40c10007800201103021551001c42280001c0d501812400c828107081c40340344141e20051003d00003840781c0c0c15000c0d5698208030140c1c0c040640c0d44580c80709114044c000c1d115215400016901c01c51810000200940c01c800100040c60043d400001248180003070130302200c0d07505481c0d42c11140e035071003100c1255400140c040c4040d4003942458460481d8103002841c401d0103000d82d2103444508500742507103440310982005000d40c500e0b00c00c40010810000c0d5034070450390114101540c511440f0707011100c598076900010065900b050010502 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 460803866 1250 460802616 460802621
    0x80303010b0d052a071104020310030b150307051011060f090d0801030209060105030c07170d1a0a0e042315090c1809010207150c0f0503010f06120b0d06 67
    0x11403941c0041071181c1d1310307080842c2c64400196450201d9000e13044403801c40078200e0b507002d048070500a0400614006021000c2002e82c0c1c0200c40b00941d06100c80c10910400690f408a590012101107012000715007100102e6035680701070195501c1003a040002102c0b20b407041000c01c038030746c1c014000d64990341084a042c010b10081690813000c43d0240452000c1c4e106d108180c8507040700c1d0010f02410003034458900541d01c60b8030142c90034a20400c108080000300f94601841a59010800c110650751041210a01c0403036410700d4610160041075511f00d0b48030b503180e070489001e40d5089104503070107885038030307128403040f00c441c065085031040b80b21040142000499402c04500200d000b074541982c68604030fa44134420302003a1503201002030b00c5900714004004000e540003d6003030005140092075200e0301050484481c0c4070b500b4548030402100300543c072580e440b4450b10681800d9082d541402a00c01d00e004141c00b1350303c2004007444102e040940345401115010034060003039a400c10b11420000007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 460805116 1250 460803866 460803877
    0xb030321090c010f021207060b03030c060a060504110405060c0a020d1a01090506031f0609060b030a0b01030204030b1311120d0207290f040f0b07030f020c011e09080303010b 76
    0x541d07018400603005194051503001d602c0316000c0d8094030380b204031482240a141c006010a070307602591a0342650403924100b004240100c0120000d24091034100082c4d01502c005400031401f99040c14070b0614412401000e807800e654040390225141d0141001103450110001006540445501e0400040c4500c0100034a81c01c1c1003d400c2c10416038898580d1002d682058400540591141115101303101945c1d6401e85050010000403412607a0f039003204082e0340264100942c81000081403040040d02881703912055070080c2401d5003081c0c95030b00c9403080c0805c003c264006240010155800700041d0354454555010014403903a20300940c0c480e4280d0f2070032420320000140c420420003051107041059005403021817402c80e01100e2200ca144040c1c90b800100411611110500c40400d0241080c840c041c013920550f40c800e070701c03410242802400f41414030b4400042d90445201100c090343c0c00a00105244950b8401040c1c50f1250141210b882050354060012408040004035000c0052401000f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 460806366 1250 460805116 460805131
    0x5010e0109061d10091d1012050708030301081015030c030b09030712030b04050a110901030f020d060311030d081b03070507051b030f0609030d2d0c03050c09130b030321 74
    0xc280700006e1029003a416030303805028000114040041d41400548548054400d03810740c1c0701241d40714081c500d075800a0b007015450740c010300035440c01c00010344901d03e0000043c0c1c00c81141d1034610740722000c081c1501c6c00301404505440d00012107202040080b02e2409921a510b0705400950b217038014010004d01000903c03403420034012404000d0540903040c1c1c1c0001000c005441c0c44103500054008104004034070040c1c0b034080c06018521209482268021800707002451050b80340e8100b00342c1401201440d040520400034148040420b050640740d00c00300320204a10380c0c984484106840b035019007070008040384104a04580380540345a0a0085c440068003111109004101c11503140d4108844454640d8130a000c40c00e40328800f0342166003420000c1144400302c03d50801d83c100b40d905805803c00349a902d500381d00d403000d0384c03611905038410700e80e4080a04048101c00068000c800c0c030b82c80e06002076120010640d4650302841117807545460402c10350010010b401200030364034412510f00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 460807616 1250 460806366 460806389
    0x12070f150c08070305060109050307080304030204060e160c0c031b09060506120a0902041b050309120301120f02010207180b030d170f04110a08010e0705010e0109061d1009 75
    0xc000418007405560360003003890700c2d4042c890b42c0d0944201d006200040c0442c2c104100c82e48006040e0b241400f104c1c001c1c08036035000d0360f40c40e411401404182d4203254458145200c4403c204015035003540d80c0300c0807220580c540202480aa424960a5440c07507401c058200d500c80c4c0b1800320590703040da80d98000c44040c8502404a582d0b5081000190301030b050a4241143c034100008402542c40e5101d2134800b84000c2c030010304074810b00385c41c0b840c0045440c00c00012900020510020301410404540318030340c08c12516240d5810036000a1440000c108000c0003c0d01358042d800071617000340000000390030910383d42c1d901010313407079030500207003500071441402401136152801040d0300c100720081c00d84414145a0915486410007001901c10040003603481e505281c4c0c01d541c841c2c0c0c4000c010b000601e100ea001142105250000300d003010701c50b5010b58188121014441441c2e60040d40e048101d03020707410088180c170131174054400448401485940d000c03110702d842a54030303a080102e5005076032515011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 460808866 1250 460807616 460807643
    0xd0203071206080a0602030a1103160915090302040213081b090606030402090f0712021b01140601080121080403141002070503120c0c0f1e030319020c12070f 69
    0x40324215040390180a85640041350300b90040307012500110b0700945602c10026006481c100700011942080c1d5800780801d0ba440507031801140d03c08441c5010f01844201d00719001142500074140009a01c0000e00454002c40c01c08601c1c000300300502d00808411055a03540b41040c80080c0503440c24014051207068182e021071400e0038003a040d00e2145074040c111a2043c2c442009040401d800103044104210080c03190341815092400034092000742940c4e011092206041207500f903c500712003040c2e80300b910340d080210702da0f03000e446d144c1158240503c00380707144e00950801c507000002020140500c41c00240c00020041c0000c02c1d944c03886850400c2d1280103141c0d00c024400e9201d900405040c507401442600d04080c0d80040d915046442d240000c1d1624841c12010f50600a070300d42d040b05240c00600d000f00303010602d4070b0300719074004420019501d1440c21020080d201e0001035030109410b9408281c1402c4003104021410407102e000001070349910040c600251a0030b03404004658183d040c422 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 460810116 1250 460808866 460808897
    0x207031e1b090c051303031407120804150b1003050601031103010e07020c0109030507051318050f0105010503010221220606141c061e141f030b01030b09120d020307 72
    0xd6806174100e03040c0b0310b807189185890440e0302c4903c1a0180700340490400400000905d01040c50400300300b00c0d00c5564140c5050b0030180700d007001515946582600f0324040d11080d64440140c0703420028507040016540c1c8888004800030021201d200d68004000000401d610019000030742c41f900c100c0e401c0350989041c00d001154078500300c0c44010010f81c05500240b10b00c0c54022a070121781d80001000084c207080303508404100800c034240580382074001c6145405420003e009180c09407400750025403410002001c8805c80841c050503907800c00800402055800c08188100c9186c0c52040e03400969010b4541000d40090103207115120303240e00038414000050501e488204c00507441141010034440a986030840a059042c02c00020394408148511b0700e008184110032101009071900084d515211003a9030781803e180b9090320f6004030002040000601c0c1e4050141941d5000c0304540d4151194206145044810030000740043c4010602080018443d80a10320a0030144d94085600c03520b82d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 460811366 1250 460810116 460810127
    0xf110424091a070303200d050903041404050405010e01050c0a0e15030a0e1e0106060e04060b03041e020301021801020c011806030902010e031209090108010b010207031e1b090c 77
    0x1040401402e024800c00034201e01000c06050000e000b4180421959130141e0366070101030001300320b089a031802085d00d500a1055128255000d41c0c154029480c2ca410030b90842048941104917611454840001804101003900084581c0c0342900081c4914102400701c000b840c4c10018111000441002c41110286424091180c8061384140d0003441e42d1507102c03002000d46034641486840e4407400341000a030700c40251200d0543ca060200008010341000701c010503039030004010305d20660401c102803251543c103c0c02c81e80c019a110b504443c12403c0b080c0c042950300a02c01010754554808500f10859510304030310200380c01000d85c00e0360781c06003010b00191400d0742c000000580d80e00c20348805101d4140242c0c00118004e0050400452401c49000068a4142c043c2c070702c40318440003c5030300e40c0142020f040c900c0c05030050000038401c0c8511400001e68503440e5100140460941103100c080ea075464507690349001c0e0f0029140d0f14040c525440751441a9141d05c00c3c1c3e25103d20300f0048001041c86131 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 460812616 1250 460811366 460811369
    0x1e080a0b040203120304031b1b030506090d090f05060a0c08190e0904050c0118080109111906080411060f0a032a020c0f011403131a070507060f11042409 67
    0x182c403442d44100441e4000700380d2103101123044441512811190300b00f9480c100b104001184070710020907080c40d0019956040118000320002440364210f002e00c070024210080c402503641c10b0b62403070b0310b1310708d0710008550508a00c2c40c09082c0c42400030b02000211802552429030308100d80700d1240c240220014400408004c84000d0f1990b004212840f9042d8801d00759144070b10400182c02c1007590700c0c0c0c20200e00b1101000d8044030003e00407080e12540e400c044003018000d85030036104100c1503107000d034080c1c0403540041c402844100074a400448a40c0d600c41581c040c0d028180c0140d440d550012000f078008e281c41005142e0b82c0c107151480c1040b4850f02a140d1242071000d038007603c1c81446e11070600003802c805605544c1448211444440c40b0b6191402461040400107031180c0c045050341461100340c00e114504800074429031007007040164012045404140e0701180c00203110010f030900c900113210b142402840d00e0030000b0002441d0f5091002103140c400c4d20340e404000a4440d071400c1e240c40009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 460813866 1250 460812616 460812623
    0x12010e011d072109060c02210d021608090f12070306050c0c01151707061d03010e01110a1b030903020910150c060c0201050106091e080a0b040203120304 67
    0x2521842824032190103085400a03070a06001c454030300003d601000c26040c85805609480e81c49285100b4005c0034051500050540d0000c1c101c5418910300c1713507002c05400b01a44e5140c0000282c40c44206500d941114a00c40306500316186d079007214a07140d4100c0c1d018110543c4600c2c01081131646a16215100c1e00d2845207400083c50454034540d00e0700060000140070300700484003440400f4400c4000c2c01900340548044002d40f241e80c1c18801000d070050280c00b07007415194171201007881240d4001c145002c00000c480c80310758045c148440002c1c0900b18015082050354285040c903c440d07814400a460402903580320030b0480c1032442d1082d160710440c9130f0043d00051080b03100700050304205c1ca029410050189152540c9521084c60792200c480f05c4004000003a01201d00301c080c8080380c49100034100191000740701035498201d00402c02806409408107100c03401004150211842c0804001008400191808484242000b0540940c1120240d000740140344900503d26081001c80f84201d51 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 460815116 1250 460813866 460813889
    0x1612061811040906080105041401050402090a0504052d0c04090f06111b030904050903070201020c010f020115090c1b03080a051003020d11131103040209070203120106030212010e01 79
    0x509158040182500e48800d0700310010410020506a1aa0103440b0140c82c40c03000105090401d4079003a8000c80c40024600410307494142480300503920840b40e1904010b50850204e03003134440e82010b5083c031002c86889844c00e1101e8030004002c05495080311403005000040e900c8003070341d410a000c1954402c0c074005103e103440794480800103c00390b1146818000036801182060b1003103901035a4404080f41c0c1100541c0301040441c3c651905004056021410002850800c400b65001030f50318003951101c117050002d84288040d40c40e100354400385d25400700c2510307a1040c07a9a45407480045c580001100c0000d48c50300e07994861481901001c0d105541d240c0d844010541d107188450008210142c2007d461904014000001d41d4800043c82c0c003060081c000801644080c0d0100b00d00c0081e030028018120b810100e41c4403090900350140ca9005406840301340480e9100361080b41588950400800014420000450030342e6041e80a4541000301e1030007038590780d03220164012031002c2441010310640 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 460816366 1250 460815116 460815149
    0x1e0c0b01091107020a030305120601050c0d0c0519140c041e0e0a0c0b0a090503010c0f1206050a060903050d03290a0305070603200309061807030b161206 67
    0x1881548401c0c01c030826800355504220301a4000758010405d0f034810742c0001c0000c200c3c0040c04c8007203002d198100d08242000c510b0078036801115501c0d08610340f1154144070041903542d00f40001400340140400560985110964042c64000550f2a1010364000144100c04044d80c10341400e101e034103038410300b940c00260a020360706070035000341811004603560760040008200c006100c050110000c1c08581001c982c440d5400e040003002110741e584518417030380c1003207144003c090304529180107402441c40c082c06240344c1544020040c0106074011500b06500ea900001e82c541d0010002c03042d64814402c3c1c403102c0e0305c0e58000710f040d1407030382180e039007058980006100382e07180c02d0720b00c4081401c3c00303004d00b80015581e07110079040c072000341c2c06079001c00c1c0c44120324164031081c2940c4202d4141e001340b2040c218100858000d5503140000d0605008165207081d0100f01581046114010f50303000b403000752140390030154003954184004010001c580c1703105003410350000500414003564243d106280000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 460817616 1250 460816366 460816379
    0x11d040f03050409060b04090b0316060e06090d050a0201020d030203041e0201030912110706020f0a08090a0806090307060b011e0302030a140a0605031c05030c030612010c1e0c0b01 79
    0x2401440422070601c1010007000a401e5424028040202064008191994640303004801501c7d40100c0d5180320741c100001c40d070300140d1040e44010541e450b6103404513500400c107001c1240c9104036040c040d031083e10b544035542000703400143c094006100b0b030b095032200c0f902208181c06034001550010203100504001d081d8070b0306031030301e84000b16005142c0824254034985594043c194008031140010790203407406850100d04001c800d000340350510041c90203424090031382d500d910392000010070882d000948144603136a0f511280c4050020042911b015080215125541703a004000031120a42411004051580070700a002007a200791004006007829022088000703500c0204452601942d80e942944001701150080b441748489a100085260820081629140c031181c000c20900e10000c01c075a00c090340c40b0080d2900070100042d115244e844075000141800420029444250320b0250002d070f4503075120801e10541185041045e801d4040510201c4046004007005400c0e1385c803520040000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 460818866 1250 460817616 460817633
    0x200304030815040c020f1207051209040b0604060323160c03030e0703030503041a060102030f13032f06040b070201050702030703080a020d02060601091224020d0c08011d04 75
    0x8002990b9031100026a600005030403901c4807104e0400680c0100e588240c90345040186011508101da900740c104840e60f540e00d561030f01c080c81d282101030b03004580d41d40280c40d0303900f004000e0b55004222940395034585074024028100044502111001c0c00d0104481511003801c45024030340c940e28070704891454030020345144401110442c20969242c0106110103002c3c03000c01c0280d444ac1e07a0380b955030300f090f003046031119448580035a480007000b014420341d41c0e000000c4401e444580002c05480d020030b92155101c1c2c64940d88060100300c180700103000c44420800c2070961600148281c0d4104240e00010b100c40e5014500501c11001d0041140f4009503010700040d204003403005048403036580d280d645079901a081201841c0c056841818480540c2e07406000c560380c00780003860640180c1c1d04e801c003040c103800700c806e0018101c500c0c06c004404114805a00000c202d42148106560700e00c1c2c42e0904000802d00c0346002c400181800002150340d00810118844259040e002e070401500c8a80780c5100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 460820116 1250 460818866 460818871
    0x3121210120c06200318030609030301240507060510170105060102060105040b06090d03080402091602060712020d061e14090a020306030a050105040c050a050f0a06080603030705010f050a2003040308 87
    0xf0303500b0b8401c4603070b903c2a00300000c03c075044906c101d0a100005d5001810304e801c5001e880c60515030030601c0148491702d480306460041190004004449107211f41c0706464074450b60b50042d003554104001c002100c0b500c4da81c140c0c1190003078401d00b030480e0121400035003215826154180160482c0c401000320b4941500500b040310f2009003c1c900e80b00e03c06000400c030000c9017904a0101d50a8010030043d45044c0c80000c0d40701c1001c441e9101a000a5140291240e000030a031100b44074104d03881c0c040c0080c081e41569041060f42c582004401e07200c0303441910005d00c14004511305500010041000c40c03052038913204c0c54070050159682500c8100e0340d40082c0d0401405690144540d461190115400b400340c6401940150107560049062070103212068126401c4035001341d00c00c00c5501140d4503015109811110303d07241c020740644600002074218400c40d10050815820070051007410a1181e01c01070148034403480800502d00c8480c001e4005820380b041060708200180001008240588041903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 460821366 1250 460820116 460820147
    0x702010c020d0815030114061206040804061803061509060609080304030f05010b130501030203010b0108280b0d03110106050a0f0b09011403010b07110603101403121210120c06 77
    0x134039900c02001207421502c044241090b4421030304144021070802001c50401541c092000e86450310389030711803c4061141d4455001080200c15a10f040c00c03481040003009140e2022050180c00e0014030301110b4032201d401601ca00d2480c02500083c0d4a0007410300c0c0040b2511200610704191641c1c80350ba900c2591510301740c600b5500d0352070701c8400c0d940c0c1103c041d2021041c082e000900b9411401490f003164140d40b642c605110745203051240100b041820000d5540d51000c0940f1035542c4142c400014040800710785400c228100e01407000c040e0018040450504000000c0041a0303540c070420240103c81e01c076002d07140304002820301c000440700000700401c03074040c18403c65405070b0302a10074007a8000da101940621001c00e480007002400f5080030b02031030303084507110304604000b070320301c40c04113414816a10700091149921030551000e10840b611144020005a00ea8402441c00c1209440c11161586034040700d04010495046c6d11001070f0f003c5030000942c1d45400d0400d00300380c1c1d40980144088 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 460822616 1250 460821366 460821391
    0x100c061407020d020d2f120d0903110105060a150509150403020102100b0a05100903020907020a0b0f0103050a0303050c0d0e0c1003200a0c0804080a0b0702010c020d08 73
    0x30100c900d00312420324016400340d0700030451a071822000a041035030303030780f05a010030030240c80d4004800b0780c0703c4107120b40d09840d83c07160003058124600e0038a820450408401c4681d40808d0010a6510940c40141094081d4594030b140d4003980310301c1403c0b1082240c0311a4003082181083c000c504009900559107010341c10907500d4694508001085405802508225048002414411546d051000c540905540d440a00c00c480101c000100c2442c030074011580035036040084020760710310805c0d12000450300602003803864180290003d41b20b2140a10035a640400c2e000424080024040d0160499070020090000e080c0750f0b903804c8020708409007645200103403e0101003103034525803150fa60380d90040c100421205e03c240b001d00609001840300310082c50314104d080c02c1414001038101c03941c03080020450f5034070341c1c0b00c7c80107541c2e0b840c000c94040c7c0441d00104000c1204040000d50440480c001e9031000c28540c2e03401401c900b81e03400b8291100050b0082e04130b103400d6074040c0c00c3c034079004a01003a14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 460823866 1250 460822616 460822631
    0x80405160e0a0f050720100f020301080606030d02030d0515030609150a1e090602040b12010e0a0e030a030b010530130b070806040204030804140f01080105100c06 71
    0x10300301816681c010614111808050151100302441140e004802590042c0300070703c1d00c8070024003c80344080200745013041c200100181c000d0103000301c01501e00c0015040002e0601101800000d420034000d0444620507407010a0706484d0000381c008120304d080e80191320345510318000c030004d0301010301001140000f00c60344000556061000900c90800240203207020a80804580170342e1002802070684280b81426011034809052072038010590f6031000821210390b80d01c2d00c00000c3c0700b1588400070441c40480d200050043c0e01c041c4604031424094028075a4550500481c12110407044070b100c2ea034010411620b4240c0070b504000d18a074014140542096105814404201c1c01d144041c00000c481f0440140d0002100d40f0403504020903900d50b0481c805507655101c43c1980190034023050000340310001d00196500d40480d0040d5511042a51f2100ea403100c500c0c0302d2521541010784141e4400018600d25441a1000c170f040300c9001304900b05101090001b5906130024601c01d6603040c2d1144913 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 460825116 1250 460823866 460823893
    0xe1b070b090303090d3b04020a020a050709051003150b04020d0b0108010e01260a0503070c0305010b01030509060612101a12030a0905062d210f07080405 67
    0x6264030074800d0310041c595920b0b0011190382010401d403022801c0c0040350149084000b4000c1020400c1d03211a1035000341c20b10b2040440c0c41400a9080c00380d407182c000201002c03c903034003040d002401c0780318034115070700582c0b60110b4400340e0703500b100c1c1e0700001100d0f105c0401c0072850711001104d003145048000202245c2000109060b41c0c03100c91440a460303110806070040c1c3d41e0068415006201c544150281035040001d001000e60b90b00840038064050443c085084007410320400040c3c96105084070394400b170b203141201c6040c60070b110564240d40381681030740c150350003405211300c242c150102034540703950340504020b96030300c00c50031955891044010106203080c0c5441004031108003928a4424501c2c180100310807544100803a080700d0b0030a01020140700e8001503041c0c01e80d20100e03256034075402c46869010343c42c0f01034001000ca02c1030031010782e0004031445e8000c00c440f01200007e0f42d0881c5401144d840000d1040d205510400c07a4040011202032141c84210b4001e0710607800d45030003621029 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 460826366 1250 460825116 460825133
    0xe010f0318030e19080303130c0806012903130308090109172503020a0b0c0904092402040e130c05030d05030f1012150e01060e061002070e1b07 63
    0xc81c1100890f425000c400d103d072600c1c400410142c3e40381c2100307068182c02d01e4955500c0740070242141d110082d0101c070032420448402c8411018040d224121070030342d0b079584001d00c7c6803c18030740c1c50200d1800d20452901c0300994030742103e1007104603180761103140310255070844070180700801810140d583d407070451002680c000740c0c090510040c01c0b019a110a00da03d40782c00c1602c2c801900ba014032030102c03d0540000c0c0c000c62000b24154104060340415660002e0700308031031051740c6c0c20561191400301160104105000421012600c10341904000d0401d59808800c0b845103008280e109014000061a4030800d0304070055218402c10010524907510b0b4003091900207c080910089400403040011354468101c115600c00601d14100c1358041c5080c004214104075800c0117040041c9621104d121a000c0d42c01852611001c42d00800002d0b903140c80c4811858400c0e00d00c2d922524a01d03003194085480040e200c0c06842c001c17203104d200360f282e80542d04e110000740c460741851007005200f0000800c0685 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 460827616 1250 460826366 460826411
    0xf12051e040302100507020a0e04081b060f0108031309020d09050a0b010801200301090504050c030f150f041e0f0204020409050712090c05040f14100f0608070e010f03 73
    0x81035500d440c1148100168030f018581d0301010008280f003481c000d80d80f622a01021501d00e4038108200c3c0d1518205100c0603c203d049007170f240c1460741200036a2140008040e0b11540e060b071481c6000b6603c0d50001a10381c82a00402000300e50180c605101a800035801081c44103890b900000d01403030195103da0403c2d084441c181c40407034401004001c400c00a01501d850414a60141d0241340b180e02d10682040c0811f02501e01c8075aa06c40c00078040000801900000100040440350803000b404a0359a80b001d0b8181c5a103c1501d243c00841c0d9088143c0300b0042c0560b0384103a07280c43d001014220700b100c10981c3d030410780b6083c0c1d9007603441025072664402030000d060244004641c1c2d15280d68044e000040d90001300700414541008440418588101d2101f0ba40f81190b0101e01361629050540c00341c080c100c451400c0c0000c000c18022200001c80c416400c07a42c40e1013080692650301c05040c2c4644c00200c0742e01011500300000c2e080c00358442c0150b03000b10a1036060001381e041e142d00310100f1780b402c0d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 460828866 1250 460827616 460827667
    0x1804090b0c130806060a060e010c060e03040f060302071e051e030d0b030c0310020a050d2901080702120304140d090314010b0a0b0f0c03030a0c080604090f1205 70
    0xc001102d00404440039028011440041c58281040d4001c00d240c0305080c41070703804000c00d58401c2c1c0b42581c82908191000e9400420138000c807042c004845449074414030802151070386508000904134024003d480b1000d8001c140f6440c0354040c1081d03507a50701d100b403908450341d005030303501400000341c80e001c180c51400152006607186e400342603545084945140085200f87d100c10164201550f00250000c6801400d40000d81c44007202d220584035400780c04808001c00d0304165209600260010341080c04000070300d80d11000c81d501c00d0055820f41001d6804000581140c15542d040e92450310085800520912510311480307001c412150501004041e582c3c0050602c40c4c0800c180905415000c40b03d041100080010b9052540000d07640e075214894904201d80c00b00e0340700d007200919400c0d0f0b00800590803c1d40e40c0c81c90300000b500020040381c10b008010500d400c01158490030544603503064190300450101c00664a44c850140b101070160088082000c2040807608180d605682c141d04a583d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 460830116 1250 460828866 460828891
    0x609062506020304020307060903020d1403040f0b0702030705010c2015030117060106031b21090b1f03170904090606081f05060f010f0306080a150c141804090b 70
    0x18135104141c20840780e030303114004100d040307081803025030f44002c4201d800944c400c81c20b0600c411440c0041e4110300540d845400b0000c048240054003e501400900509108900340c82150b6102c000644030b8204100003d800d18103d070020000300900010307142446400104400c01d01d1400b4081611183e000342c0024905640c81c00844250030030811900d4094102810306200c0f101c0c04c0a0701c0340340d00143c0c03000350080001041159403140ca030402d1b040700e044944403040c4205030040c01c01c444010000d9407070540014002c54482c80c034079046058101582c2d07004600620041001a010241c1d8105101055119984030b584030006081445030a0003003000ca00942025603000ca20314000301d81a004500c2c00c2410281001425500c603400c0d24403210f400d080a407031000b05008110010800f6402480062044900d1281441501c6000b24095002068103200035060745004031846490301c007c9281d120802d00c05c01080d41c2501301c00c0510150702500c0019100141d80300d2094650059980b40138045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 460831366 1250 460830116 460830121
    0x80d0b03060a0506030319090e09030a0207150816110d030e011a0a1e090f0b210c041d01050a021b0a0803040b0a02090928090206090625060203 63
    0x4040c05200c2d4030640c1c0c1482008075107000004652248a0000c80f41181c009848440165034003642e4990f001d042d1128000d4036900c0e000300225a00d50040070f00d030026104608000030100c01d40200c116280c903280c1d0301c00d242e0b52141c3e1090f59401c812a003816060140e55500304089480402102c00282442e907008207103050307510401800c4600d5040200c4640039402040300300da450750100c040490f1443c0f1454424400e44054418581100d034000d0032031141480d09040042401e5080341002007400c4595042ea0075401c0300300c00740040e0001c408140d980245540d107036945401ea000442a5200400700194a000120114219601107410400b80c0350301050840040140f0324914454084504c002d181d05002c985402c000c6001c0200000c1040c485503000030306c180c060f0b030140c0384103140c098090030760380c148105191000c007101e40c0b007080c0d00c2009002281503d451401082030300b5030090040c501e051012410b100f22030b8800c04615000700e8a5030b10101c1c242c20207110440e00c060160a0040c1c0b0dd0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 460832616 1250 460831366 460831369
    0x8030c250302041b14092b080c0619050f190209030304060206100506090a0e15150a170c0a03090c051c0c090b06160c050a0602100b03030307090e040807080d0b 70
    0x1070b030b1076524860321034400e0100c051103031208000c4802c49104003030052651100e0b126000b2080c110120020207214004c200300b03a600d100000c0c1240201c152f18452102c00301d48440302c60840e10300b14be101092400395400b00f4032807402d2142152000201032005450400c406021a145a00c40d80c05003006030310403000c00c4a4044101c5819000d8141100d40398034082245d000101c0a461380d0141c1d0041050440220300f41410602140020350806851070103035403a000421100ca410200c11103010070907480304140d070024102c0d01988120404151541028110311086004160b0b4001c1115650030b6014007103203e030341b607a10712011a243c10b0b480c8070305450306140c081c8405206034001e41c010390a202c80b035051940d4202c142e0b01001c2d103610417060344050310700344007a00014079407000d9000442040045240d82c0c2c0402d211201005190090100d000c503101455520301c41180c20600181031020180105030076880001d410900900b140703406d00c04183c503418007580c0080105400d465a81e1b80c2c40485 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 460833866 1250 460832616 460832627
    0x501180b041706160c0213140403030c0f0f20030717071509080d0f0f0608010c021b30060c07060b1804061104031a060a08030c250302041b 61
    0x520342a42c80b04c401e11114070190600c0fa03802030080c030419030603a5804600f83d20303030301c00003501144803041c8281d402c1c107080290080520014000014150001c4440d1181c02642200360a0155640b200e818601d6103200d850850f9420700980c0841c0420000d01c0c010412040a12070354800035006036644000a05d04007103090481c1c0d03210009103040001450110f0020340075215070362240c002c0403070b043c0301d1817100c0001051007080e8958400e15090000c150075805501a000740e414030380840e04010014402020301000f80d40c151a40300044d401c107241c4c0d4059000743e254907a191b20511403c0c0042109590b41001402c890b5a10742001c003160810622000e4002c0325080e010545162109410701c10710307540c90751303402400034210b603445410048400d42c045044800840c2c020402191000b0b0303440e4090520341050b26198865408407030007044118001c011a0201400c2100034458840000e2983c40c0488400084240d1451019130000150302c65014002419480c0c605000c7e150202c000003900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 460835116 1250 460833866 460833871
    0x70807020a2a17060f060a080105070e090903090f0d112e1d040b03030c0a060f1b080a05090a022e0302040b0d0216020d0803010e0c090a0501180b041706 67
    0x4428492203c0c40d882103408150b03141c100d501c42442c00d02d0356841070302040c41c590b4030390b11009847d07290208020060741d01403100305020350203c034850081c1c2c65804e1403039568081c00c43d00d150f0022485240c40d240d40303418040050202e00c83c42c2c01c0b282a404d0f0b42c00240100400f0406405c0b10940713aa0108580e034113405004a041d003060a280302081e0091003004280180480304500036643c1b4408044280d600f003040c0c440e0021610122501c583c010b1a05c240900300190a80c034006051018050f61b5040941043c80202c1c120341d141c001c0c0d9078481a00301d000e0031000c4c200e00c149010343d044210140e01d83d224001c24a000640449071100e82c03517040f03018605148008802098410f00091105148038011502c240034206009170302c0e1000030034401169045010025844210b04014104200c4400302a504907038401c1ea0580341580e0780000304c0c0091040f1841990302014045080c0b11030740c010040c00701680354107581284095218a904e268541c0190803100205103003141c2024009020401c555 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 460836366 1250 460835116 460835129
    0xc091806082d1b06030a0e030c030903070801020702030c060724050609070201060803030a0c1404060207031a01061e05160303020408011107020d06110c0d0e040c080906070807020a2a 80
    0x90030022046019000f410341c0300710303840f03440008003281460881c4e40100c10f28a40070000d581e40c44801010840da80c2c0d01c0405454000d00403401c002500d00b0f011310a6803541c42d000b401400034010324100708486541b05103011100d10580030390b4005001c0e0503a080d030700031a903440340000301403c0103402c000f51188010111411a0f04112081c0300c0071802200b66604010040790100391500702e404c06036804a44050b0040344210049400141030360b002031980b04586c00f07882e4020340b22001d9a8100c070144802d014140104041102e842c510040c440300c010424251407500509202c9541180700c1c00e09085c04080e0000307500400c0610195400b885044d2520316828030b00c07803400480d13502080000e91a00c02c0900269550207800827081030400440f000c010180b82030354042c0401d020090a000b9070180c80b54092450200744184260150403024003881491001344900d5903040400c940052005003501c00b14040c0d088000001500201c00d258941006040340e6145d02c0490b04444034444240d0028 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 460837616 1250 460836366 460836373
    0x30408120901090b0a0e070e10030b19050106090b07031b06020a03051503070311131104090e12040308091203090d050106090f0b06030708100e0c0a02060105040c091806082d 76
    0x1212600001a01100b1212940c012341001e99412845412084190340050304d80d80800d0708102c1c0440c0000a040302800e0810000c10199813500000c48800c2c5250280e40740e100070400540010900401e20f0fa40765030f04111020310203592a0351444241c1e04500c0380000842d4940c424000e00d464400c11144180100750002c03c0428915140c0d0701a541c01c00390100e000781d884201c44010182d0361b40085961072036550303045a0b1240c0d02c400c0c0900a2518112100180c000d0021034070001140c41d04807000c80350080307626401c0440c210104818084c50680154040c402002100800d1b1646c0c84020030160051000280f5645080c803040181d0311900150100a440d2070010701e00c80d51034100740d80d0070521601c0e00002a5860a100c40c1c0314601039000050403d0010040042e166a55001091040060741c29a4a9a41d850051000f80d410081000c40802c02d250030030b1203800c51aaa2440e0a11a80f0310041602e81d0399150903400c00e0000440c001c41454001c0c400701d43c2d08104d05213504660260b5009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 460838866 1250 460837616 460837631
    0x70504051012061104120b0105180403180503070b0c010b03010504031b03031410030201030e0601150f050712020102040816050f0f130f0c120905030a0302030408120901090b0a 77
    0x8201846030240035502070800802c05000521072903030310007240c086106046a6a954580e00745038040740d13070703c40122034002c0a9800442c0c40e0038405842c9446048114400b80c03a52925541030350492404048041214001d00000480d50340420503031004141c0a080c0c01d0f038403681ca14610303003135824058199000ea8100010701c000642c2c0a1403403c001100c46010240c155941d190440c0a44082d1020814042c1070308184403454054181c60001c0703d1003602c08025441c090340580351200c0303007440380502c0d0780c0f9000e490000c41401100d080e07076080e40c0e03450500d01c0e051560ba40c101024080700c59400050394049070511048404014224090f60352405001c00940341c2000a940c0c48100c2b4141800381c3d002e40720301c0034070ba2203d075008a041c0c540c544060105c00c0f903110710100104015000e9400180200d981404010302c107100c1c0b44022904400514501220a1001e5020b5031001d042142c1800080059988011200d42002d0042c400400007145900d941e0422503841c03071016101301c0041c2e181a20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 460840116 1250 460838866 460838881
    0x12030c0302130510050d0603080306040f091218031406010603050606030c0a2a0b16050901081b090909100c050901081501050c0a061d030c0706050d02280207050405 72
    0x520003100d400f16028040101c0d03200003105c4501901d0341d02105241010804420050340741e010394031411042d40c0c10808181100c00803025500301440203440800c5000403c00e42070b00c80d1032100d00440c4080c07500c040c41a03490b91041c1c03c00200d9001000e03e60003603001804002d500d0700403a60044400c640305030442c04c10f802d6403c1140f00f0f8240b100c083c040454031000c1d03001d07440d0301407451081ca554010290503c0f50300789200324190807140a0401550072907010005401341080d184111410703910f4410659580c9030417034190255401d0811010401d0002c1602695040c02d00c92280c001c0001030100b4001d081400820f5440030756084041c00b409020321000c1766406007010703038020140d10550f280e10b0701d0300005030b8461007220107894590040780c3c0c6200070b005250b00050700b050610760003641e801001c8a0704645900480500101c1504202401c001c3c181c442c50160450368481e610041c50140352a0048054014000e01c82086c10200500040f106405100810040801352002e001c3c0d840e0030351 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 460841366 1250 460840116 460840147
    0x41d060a030507091515020c01142a01200a0e0a03150f1104090b031509030306120f031204051501030b0a1d03070b01180207210c0203010912030c0302 66
    0xc031801d841e580c1104c890340280a0f95a08000c0c0016841b0907510100188029180d000f2500014080b5180d000200c07403a1282c64110791030000203030182d41e100d22044607280a41e01c03d1800134005136403a056020041001c41e00000003400010307810903a1010540e1000e02003c01c000d0010380b01e03c443c580304101042d00030b031650200d81c3c4845c01c0080e111054003089402072040030308403400c600c000704001c01c1a5032183e01401103c0320490441c0c5805083d80032054280d84220b6240c03215400c1840860002d0603e20361022040000c44281d03554010710319059455508090f000151074140340c03043c8400c6c03100500003141000d0480ca41148107606644070300c1e203100300242c01604074076540c1c548a402405a848019034000c5940c050326544c440e541024848880b003070003040029469030020306c04000c1540b003100c101641c40042204100c1c804400780c4851380451116100b0b0283c0000400010395080c42003800e0f0034491241c001c01040210001411a000c0a0024050510400400c0818001c52 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 460842616 1250 460841366 460841369
    0x9020a06050f03190e0f0f01060b0405060d05131a040308090c0a0e09120304060c02070b1c050415020a0206071d030a0206030a091407060315060e090402040e03041d060a030507 77
    0x309404c8165800d041103100080c1040c0800c541075009049140c580f542001c40c5070b48100c06003000074018151100700c2140710344200e100d00743d4088002c01c5a0301e21410700c0e8100d99400740c0b40203108a2144c406880e050040f08201c48500c0b61940d0f0801000308060308007031080c3c3c100c40030000910718170000f400450404107040c011400d4041d01000010200002009035040840d08a0340e01501d030f04041c50620054038107082e000d001f50040c01c002080095401060360f140c42e900001c60130f03c1901d0048690020400076000360389003401010101c503d0b84a03030008105e511596401003100d4500000b00803ca441000c110400e00b150341c65000005540000e0001805601101d0050782d94503126002002044181001401305074003c807031400601e0081100811101c0da40c030140000007000501d001140c00a0044102159801c501c541c1d65090030410036500c188040c000148000c03d03003107810702d0354009600c4042c01c0390f03103c0400744160f0508071025401c0041600d4014003d42107940703a50325160079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 460843866 1250 460842616 460842631
    0xf05030c03130c0504020a020a05060609060a0306020a051308061006181802120f041704031e050a14010902010e03070308030115090f320603070f140d09020a06050f03 73
    0xa041d800b03080c050002e18182c01808010000c541d207421a01010303499000032482602c0c14062480000c11a0400b5604207100c1d1000900142002d404d40d59544000d41042d1503c40c02c0050234449440c4140303c0780303011400307000c281008cc0f00c40d140009940e4480126034007c031041020401801c9a1008001203c00645144581041e42c400d030b0420b0320b8009000740031043c0080003a4105100700008100c0080780918041c0922002900c03039101d100e49070f0b1103a4400100204900d0b111040c0c90a040021826030034803e0060314003c600f03e459581660b9181040c4241707a0355640700b14001c5603000b213290b40d078a01e0300b50040c1c8038240c82c41c0ca418100c0d00051080540b000c2c1d00c460000056407140591001400014013040503050b16050740600562f01c409082d400c1e0651a48484910014a0000c0c0032803074000341054030319501c405085649140342031a80041c0300410399a000c02010070b038094239146200f0040014004102d00400c0074145040e0302400c01d205081040e8400340c4082421a54080711 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 460845116 1250 460843866 460843891
    0xf15060507080d02070c031a07080115020a060e0c011d030322030602030703020712032a03090c080c0307050d030203041a07121701050a050a15090f03080a0f05030c03 73
    0x1842d0800034480e1040414081c1d040344002045410002a8030740c52080c2d034092064943c80b0011540f180d003009400360f8030740c0040751031400100514400c40c003000c0055070725481503c0001e6001d03683c180580e50b042400d031100340c10503d46403d15583c006078a03040c1e1301102c00c481008955545c086030f2244106240c03c140141395510117170a585440015800540d8421000c550301d00e09040003c009421244003214004400481e0030560f520a0003400500b9000109c020401e040344013455000004541c00d071410b05841301c40d001c0210b02410400e10040412a0250414660003010941012202d0300b08a10403080c0102405c0840c4d400416142a5110130017401c00481600801c04000d006000d4006c11900800f08241d114540c00000003a8040c1c0c201c018640d181d03228401c004110740c044c05469000410f03002c0170813100c540e02022802d400301b141044112141c807400c0810b600c286035041582c21410005003103030701c030394000e0398110820545d24000b400c41c01c0181c42c07a8042c0c400501615550780 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 460846366 1250 460845116 460845127
    0x1051206062506060608010e0f1b07031718030a0c0609021002100b041e1104090c111612020f04060f171605011707021906050a0f150605 60
    0x2140c001c01c40c0c01e1031841c1820404285094094200148071110044500e5814a100025038074007034589039058a40c5a1a806071a541300145800b440d800100000450075560584018218039a402055054085e03507030001c4846d8100c01c04103408401400300c0801c00c64008000c01c1a40f004015a03800a5041c41c0c410b008d40740b1802c082000d8240200c000c2d40c40859140d00c000c05075000900d0000700f00d03800c64103205451400702003001700c8803210500200c41c1115220400822100d52001450b11819641d131400e0030303100c101e10401c442d1074614940100d1804070118078008003c011034803034100c00da413080c6c1203581000100314809088041c002d000d20044000d03001140c5d1250013520140c8004074420400c181e0b920280c0901d183c40301c201000d580241d80c01305440c4116828150180d0302d040c1c41c2c02e82c40b1a1503545402c40c9175001000c190840c06132200111100845100b10580213014000100d21410442c0481c4d045803000140a140c1526240768150b901105c00b042c14112406420300d652103d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 460847616 1250 460846366 460846369
    0x30403030f111203091b0a05010c03090e0406020306011404050a0e0a021215100203040b0a11030c07080604020f0306040b0a02130e09010c09050a0e010b0706020705010510090c090501051206 83
    0x11030180e00310b140103000c2c0e21812912080082c0144d4803c0c003140301110000300c0294504041440c001c15100d03044103040c2070510036940684018503aa9210745070900000d6510028040d2019007501c0c2110850b0700042817214645e40080e5000c1461066694940362a14010002d110030180d0301c41d1010800c0000005401200d0325410750b0382902c0c83e00401001c070324140c082294001803036241903100e44022100041090b200006490039140070048003841c100c41d010041c1d840c400c030051549078a1004000d0040c13481c001780105001015158010041fa04040c41005100d14407403961900a51140d0204000b09400741e14003500180c040787c0050713690110079103040e50021980c10424061810400b8840100310543c043d146001c1266240c0319490f45940421113184400e00c0342c02c4122401c0f000500c40541050010b0040b94820b003401842c002866841c1070a448c1c007119038182c40307400d084d005c00043c00359014651100c235a5103000290b0b54280030010740640269400d4182c07030903107440007801c40d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 460848866 1250 460847616 460847627
    0x6010312050c07052710080f030406080105040f110f0702090a020f0702040c1806080103060f020c0307110319080d050a022719030803160f0f2613050c06030405030403030f 75
    0x1000d640344040f03002c51904240d1b10801d091944600c070514451018504444440070080d50140d4856a5608441c0d91a0000700005400c3c0c196039040c2036507441e002c43e402403c04030000c0810b40a086034481d1150b50034010030501e500001c001c0000715004114030864141102d04440813198112400508101d0940d41207411262811812400b032020110104200360459040e504892160009000d0020b040c0b140da4140d010741409211355920071300c803a5000942d40c1d9074019410401500b02c0c0e03841d25990700c058028246001095504880002e882940b584460140f50b503c0700f6540c005500e040d812070720018003140e03905600031011000e10041103c90340c1d06040b06e900c0401c02cdd018803100c15280d060039040e1f903006503000949c1d80390b480ea075142d0150040358041c8520441d9203460030f00c1b00c00482c080d11110341c050044400307403851050741c409840740701504038001d641e410025040810103203001ca15080f0b003e4001885007000f0b108000010b40000110340941e1390500c0c0518900c540008255103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 460850116 1250 460848866 460848919
    0x4030f06060e10090e01180b0406020d0f020a030b090f13050109060606020114091c110f160f05010305041511040b21070e01020a0311160806010312050c0705 69
    0x142c0c400c50810302c102c24602c641c00005a070310400b0100700054040310003508a500154031041042840410384010032807400c2107d52180c06980c000d03150084040d410402c0b151004100000181c3c08108804603952502ca0340c1c0d94210107403840e0f906070600407410560003c0082000e0b003d036840101201c01c01c1029085840d010798400000d100d15a02e405000c4d019040103800c4070300d8000c4400020740c0b200300c0015a070f0b10900c2e65030300d004a0352a150504950010840014074800d11030072007410701d981002c2020035059914203120020080c10240000e0100d0841d900180c1050f06020034000403490070980c00100350614000022001c1c40030103c010345015940c000d00c1100000b203500c6104003030b000f561003039030181e280c9800e0480e901d0f4130080e119901070304030243c0180e0190880c4400240610201d201c06060f070421502811a128410b26000620b40c0006400740c1280e4010002c0107110700c03c10f09210381034104079080050404410781c0c0c5100c0c6204061040a550100700380c0415112181c40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 460851366 1250 460850116 460850129
    0x50723040504261602010e040204030f050d091a250b0705030609010f2d0f080307050f030c12030a060e0117070503010203060102030d23090d03061a04030f0606 70
    0x1442c041c1411224094000c61900000303200800700c0a844a04034219040f00070500311202c442c04180d0011100048217109041c0c0050f4200000f00c0420811003184038410b208100400000348956001840c030340c1f440d071010f024510320781c2c9210150101c00d829282110000c0201308111804500c012509084258020b48000310410500044540c040c009603c40c42080c2c0d5400503d907640d2034042d0307082c0524440d0b0001001000041c0c82d85c0e41e05280c0803041481c0c4d000c2c510020176203130280310b40c10482e10b0344041c4456000050100401006110030001d61500002841c02c104000012030380301c3c4805a00f17502140800000100200c14592110001e03000c0d0141045043d80c4a0180c0009070100280401e0548545600084c441c641402141e204540c1a030266061480302000c0f075018011807a2210306811285400390805100016081d202c2c000f00c01c0285a0280a0300000d812a0341a4106080d000c0281d050a4020b44409003101e0460394406044088140e1609060009040580111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 460852616 1250 460851366 460851371
    0x804050111130f050105180906131806050108150f0a020c030a030b010215150f28150f08070e30070f050a03030e01113705072304 57
    0x182d4030041c002c81c00b10a9600034003258003080c0e102c00056075035004170071a4900d0864895924455410044003040d00500f000e0106440c1e504145030745019580d98032403001032803400c2c002480510049004030780c01001c00001504d90039600c3d103521ba542e10303402014900d0f8010458085150640700398101e848003e92903040c0c0f038036003031440c40080281a00150320350041c8600d0807620f8400d202000c1c41c6000301da00c07640d9204d415940f0010b11080d144a10505c0d03500007103c8050030181803400d13641020307550380c0c603005481c11810000c01c070b600ca80d059182441081802c1c84903001c400d0b003045e00190850060700f0301b0f00e241c03960000044c02041d1880456010300f4501140d41e140d6408040c0801c464604000c15a42c1180c0c5540b03c03e06107240718412603038000c1d13804408001280c020140c00d0319400040c9403079130800d07152400c8189800c42c004c01250160003900c080152165410254030102050040300b00f0004070543c4076a80d40e000d0501810101d03c1c20480a03242d81e01c2546441c4241d4000900309 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 460853866 1250 460852616 460852627
    0x14091f0908070e01051305090c10051e040305071706060904060e0d0201050f011e0306050a060b030915070f231306082d010b0a0c02060f0c0f0304050d030804050111 72
    0x1c80307441c04028407035070340203465102d44070341070546e0350203001c0c41440002d0040c0410b004400070403d00f100344c136081009100703007009922501c141c88042c0c0b400c6080b0003d28250ba0314503505c1c24520b482c003103600034011108424503020b091078012607001d80008046415152039280e078106500200218400030840d440382004101c0300540641000e0300c204502d202105050b130340c90701010300020500d800300000041004080c400201d103580150340116091100007005d03512408002c00f01e902c01c0d207556108ad401480940d0205606280456024401d0b00d000241c01d00304940260140354a85600c1801c4401ca2120001075684141681d92140d030140382803545c2c0e940c4407000f80c0160030540c0c46403c3e008203401a8040d5104200d035410740645001c0074448140e1030035001400c560000014102000b8000c58918050b070358400103815055490000d41d5500c1c242d10841c14074007039018114801e00e42041c802040306503074891401c9401074050408242c60307070b00c03890300900421b1564400404c0708004210b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 460855116 1250 460853866 460853879
    0x14060409090f0c061d01050309010b0a0b12060406030b01030b090c03100c02070f030209040b090109050d031a0f1c08090307090b1503010b0f0703111c14091f090807 72
    0xe001c0d40c2800f95454240c0c07a5102c510484030307444103041480d0100c48902c1c268800d94031076401160300140c0c01c0700024412440c1000140c0320318080c0d01c4100d03080f0000c141d064003c5900014650020000c4500b040010300e95911065040b10510026000c81040301c00640e50a0040c402d1000c078910007000c0d036060134032507000c5500074404401c01000611420b803000c204014030075030210a9075002050078605681f01c0d03841440144005000084035500d0321581d60014508000220466000b0b840111700c912081e22000b480100c018080b0344164081c62140a00e9102d0003400580340b0f20382e10b0501c106070040d08101d6907511511a01903018480c007034000840c031049a0103500c82002c200d5000a903980584102d20190000303000d6022001d0b802c00980e001819800b0003405498428106074528601c446032850801c0c480780d2074050780c9030010581b402141c1d0b0100407800d182d0120045c1c0c80c10019907034041044114120040c802e1010681d000d5880389006017005001400c000048555003525103c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 460856366 1250 460855116 460855133
    0x6030e120f0d1d160b090f011b05100b1c120e0913020108280902150c070905060a0806130c08060c0403050c0103020702180615040602070503070603151406040909 71
    0x3003001003401180e0490421501301403492080b60610b80035581030105110420600c0b802e0707100058103000d000050704c0600300c011160088924043d07006085202e07030180704207080e270b5900c0800500c9540c03005c170204180403030740b540180c10680113506542c5ca58a002416645140258640c550040c0103104104400580700002280c4a1003a41c03a0740544d2030704000307245401d01506844000300d00d8051950560310702035001a1210380003c01c03018114506003e0b0003510f03404a24031140d6600210300511802c5268080c00d9048101983c9042200780b8101c0002d4907400302420000200880b034000c0f00c284080000c040010304801d00a440e62828200603280306580305120440c4c0360300481c0304030302c07041d03010388240d410041c1c000d016002050640c180b01c4075919401440079a0240e11040c01042c08081e0601400140015800415005052200b0580750001c035620400c01c050030301a40418185034038011307500302d643d064070b5654007140b601c000078801c1c041c9070055449a460704103a00240300d0b803030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 460857616 1250 460856366 460856411
    0x40c1a0409060b031e0403020304090e010203180d05370207060e010302070b0103020f010212160b24010c06020d09030e040b09070915020717060601080106030e120f0d 73
    0x1007808005607591000180d40c43e00085804403840c1c00117140344c0b0300e8030054082c1d540e4007030710078030580746095100c400c01022070321800c4054005a501008000038240102540030754000c40340020016103680c031100809074852461b0324016000030440c0c81081404c0c501105804640118910007186218040259540180c1c495400005c0340940b04628650084c401c81e112035401c0240d0249603030940c0c00f03000d1102103011045045206541c45010000705401c0a042014412590401c800c0305c00c0c1031042c1c440300041c0580c0d08103400f00820420106001c0b06a0880d00002c0c2000103403800a4200280280038856807040a1810003203000c2c105a03210840c810036080840c0d040290711b41c01024000350716000c403000c0380412074041e8284201460013410b6000c84805204540f141929001c803640132107824251b86141c0d52100c020300440e0341c0c0240000e40900020301d07081000003185124a65100e030a035181c0c03078842c000021116440c003450012503440c000042003e02c090989000300c50010034a6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 460858866 1250 460857616 460857629
    0x24090c0e071407030e040b0d0f05030901020d0e06120c0c01050a150618210602070b01090c080403140a0c120e0a080f0307061112090d02150f0f040c1a04 67
    0x5071040101c080381405507900c0c0f41d010f944031000c10101000344001040100000d9074041e2403001010009418030540121007480344010303644501d0080b0002e81303402c4565260f1000c2c081c031000a0416501c540050710180c511410a203103003a2a4410045034912070302174450b00650801c5e08009649149802c0b404100f45031002610119903240c00445043c960700c149607849030040c0d001040203030303580340858140003559150f0b4a001070b0320740d5402080360300142c01200e1463320740004110001d545c1c410032694461b80e06140f0041d16142d42e00800604580d00da10011900104803038032000e124030340e010740b86c9610884075003003040940b1000d030187c5041030019106044698021515030004034000304441d080c02d000f141044001c0e903403080031300642230741070041031410300036401c000b1040c91009001b0182c440150282c602e040e00d0007810103c20f4a45945505020005c1c8903843c1c01c01140e5550200030341c103c0c00510b8855203087d0740c80e0f04040e80300d058901c1860703010a02c0107031000024001c840a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 460860116 1250 460858866 460858877
    0x503060705090d1b08331e1905091b0a060f03020702040b0a0f0e09010203060108061e03010e100501090e0325061404061824090c0e07 59
    0x458400c1160240318900607250410040a50000082e0507901c0b0307443d0204030920300010080d105c140b00c42c80c220942d0031900d00c446110322031200d0609072001c20600c1c03401031010000c2c2441e01c0c20720781804034040f00d00d01d51030310070340303000610600306462000040c20f500110a1040d400d0408200350740d02da040d142e030b112495401d03140e56428904074100384200c4400b502c47c03101c3c500c5058070030340c02500035070000d81c3c0054403414200d0281e40c64109890182c13818600891006042110103c04d80000a110503e143c1c4100213015141ea00604600d41c404c10850300e50401e40300071002030b07501c480aa00f100340c0560038200980c0c040400840c410700cdc102e4030414108641da07070700c030a050300b501d6803143d07001d42e030790030402820b0120381400c204189011100c1807440d503981881c0c0d59020031a11541d0090300703d00184014042006528022940d1200210350b0b05e0059280c4c0380ca032034407618601110300380c003250103d02000406030207800c06a12540c00c0210340c0115540d0b035821300013120301198507200003803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 460861366 1250 460860116 460860121
    0xc1b08090a03060e01241505160b010e07020a05031603030f05010f210b04140a05030a020607030f0c120510080f01020702030c090f010303051c1a030601090c050706020304060e0a0507050306 83
    0x40c1d10315610001e0706e0340d0114070400c0352030442100d2007150b20352129020000b041201202c200e0306041e81c03819a910402c12810070b9850003601c241c0310700340580030104640005d480b6402003070f400030598041c8030031102c00300c1070700c541d0385020740c0142a841040214981000700024000001404400131205404404001040c0030300103800c98070642c2c18014800784840010802050504c03000300442c4105104032030f1028441d4a5061550701310408000059200754100668035915028450b0700b1001e0700420302c281074003a28041d000d000140d0343c410181c1d50f98000104850898070040e4000d18407001a910044412501c544c080d5204c01e8007a0b000340700d841c009160300c0c1082ca070728512800c40503041c08056402c0d55011200340d40420200c1d40c1c0e0f0400d081c0440544005803060203c00d001e55400400c00c002c80d403090500b4140164010000946083c840540e12600b000031509001d0b488817005980740d031503280940050218504092080c880c1d1170414003004030018194055a004500712001d99 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 460862616 1250 460861366 460861391
    0x501030b07030608070e040204110c07030302070b120f19060b04051e010207030303180b010e040209010b0306030d05160507181b0f0c020d14010207060f0c1b08090a03060e01 76
    0x490f0b003441070051550020204000090342d00c100c06412502c0184003154441c4000c07001d030040d403c91315080016030020340c0100304141e010065640240b80c258200b60400603106032040c0300d110000c0181141e82c0c0c0d0000000d0b42101c4204041c0344891a411080003500c0d03c42700c0b58200c5404c81d0042501074503c8200d801d24036040140018068841640140030040c00c40da4218060f0188400c0c88503469800e1940f8000940325402c8103001c3e10811008800b0352800703004000d011341c0c040c0e000022809041050000b5038a020404014010f801d05149540c0c2c2010405841c2c00014414003800a01626402250b000020880089400c80c0c450043c402c0740007050444405180d807141c02d902040e00402300d400e4260183d1552440180010722500031150b07240c850440096800d804600360342d40c0010100f0030090f9030f00c17451803070203003004c0c0c10080f1741e41d1250058141158092150485d00d00e00c59180c2c2008455001c481c00c0082c00f4141c1e90b51030340d5910b2f00d00081c0840c40c2c00c1c0c0006500b01620310584 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 460863866 1250 460862616 460862621
    0xd05090312190f0c080304060905150709121a0f06120d0504050d08190e01030e0a0203060103140f011a01030e2e02070f1a0f1b16060c030501030b0703 66
    0x142003600303540780300344040d00035105611050b0203d010b00c100d02254401240a02000d54845c81c054000402c0507929460028103000003813120002507041602070161840d4820500c0055460442c074181d4030b030501d0b040102d4900c043c285040d60350030080d420041c0b040741c410354003400745500b41c40c03440c2c49020f5005903d840d001002070301400a00d051104100078940f41c0e0840c40c06d903000f14503040c40d001d2080c5001c0d88c0095492040000b007032030b040143c005540e25100f50305024400c40c0103416030160f80da0000b91240c3d01031101501c018500c403502403d00d60284075140135110548020000c00c10a0003541d2240c40100c16904d000c82d02d464560390388440b001c41c040908890303240924034000000480281c00303160f01042c03402210390903c001800583d5958449041074010880458101d00500c00840c04040c0248200c40c81c00c0100c0602402465121124281000e440711003030300c49040c1c80c6441e24464000398098070840c00c00c2c040c0841c2c10703059400130303050f6400f4034000340b01607449200903010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 460865116 1250 460863866 460863877
    0x607020c0d110613032003060c0f04240f0912060e0c03030d150f0305060a0b18070503180c03100b060f12101d07030506120d05090312 59
    0x5a081550242100d240000d107038400c25100e4041040c4400180020a4494001c0c011504500072410000c0c8140701200310041c102e01c80e40c00d802a002c41c0c2c1000803030b451303444c064201d00e200400402d0541c0542c8511042d1000b6081e1990701c5c1011f42d084483c83d21406102c00620b402040007038104101d1a0b101e450300f24240c592591a11150040d81d681d2000100a020451103050090024800c001d90382440100307945048040c022907103058103414080030b8001d0f58021402001100c0c0c041000031401b040325035116401000015181c0b01e008081802092501824010783d45d0860810203550340000280d402500002c1828041ca500400c00b2591480700105143d07060740183c01c0580c14400c0e640009100101c003078601070800150103000c070610b030482c02001d0400c1c5030620400c4070800c0e030400914014840c211940c0241d0350231191a584204000c2c0903042090788540010b1095140c140808030040703e40c0f000c441003c07003820b40040aa40001e04954030034000c0b1121a5116100c0005030340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 460866366 1250 460865116 460865131
    0x90d080103140a050601060c061b090302011101091e0618081b1c030608150c16060219080a11040e011e120507054b0607060c1106 57
    0x240580d080d500c5184400202c690092002e1240da1000000039030144000c6009000c00d840d107109900c25880c20f001607440d40c1b00ea6004030044115010702c4107502802150885c0e8080c02c2c0910025610034020380904400200035001c41072240101564800d480c0c1c2c80c181c3d89000359030800071420328202c02c240c8a021058043e24903001800176410a5560381c40c810b0001809004860b40700ca1030711074001000c0160034904000c03d40d034040401a00c1010701c0041c07050042c0c00c107030901c0c611345541e0b003000310301848a44e2840c00302072005c5402008002c2c0e0449010140340002c4000201e4495001842d659085401455060801031a01c0300d20081130b06a40543d0102d004610701c0e0f0382080d03110300100b41c50284100c1129110340000840c9400c42040598860160018100d014204801e1084889448880d0082a905151a07101d80601d103421101414407810301c0e01d14903200301001c400c0d01821410304603484013000410104121480d4400552507500b42c6443c00601d4a440303089407240c1c4101c2c5e548 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 460867616 1250 460866366 460866377
    0x11106060a0302040e03040509130308070212040308070305120411040f0b030a02041a0a0e071b050c040e07090e010b0906100801092c03090a0503030a050d050411190e090d 75
    0xa20051500760400e20105800c5c0b01141e0405540f01c00050b031a5800f92650445030041512000502d540460390316032010f42400102410010030413500c2da5407086e840003411840b00071a00404041c480e008890300038007481104150b138209800d0041c0400c42011809120718680181844007100074094495078a83c002c0c0944111140c9800344005041e0300508210340d6042900c00c65016500c880d04000a40252000a2034600c0c2880016100000006400d10000d1845115a0006200107040d8240000c1036901241030b5040848262a0442c01c0e001000380c07d092031003800b0003800552041501680c2286c00c00155127602080c884c914030000102030004030b0380b60060180807202c2d0020080e07080300720101e031032015481b41c0000f07404003814003149882e04009800200e03490000140070141000703c01440c0b40c5601d14030040c0c89445041d01e1081e00c1501c0d000010148000280c200140074030180065090745080c1030100c902c1701c110f0142c150030140440103d800c122000960300c01100b400c0c0c545 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 460868866 1250 460867616 460867619
    0xb0c0f01060e090c090a060e1602240a0c140a030e010609090305030f0c16030f1d09150d0c0f0519050a060509040b03100608070806100608060a080a0302030306011106060a 75
    0x24092803100043c1403004c0c654644800044081c2501e403058400d104121013507270486882c52009040170075160b0400f1360045d007407130380e5070108a48100242c0c00c0100e8500001e500304800d00190f0703800040610380301c6100380215a00c0850390b0103130000750704506001e00070803480c0d4541c2040c00803100d1100014001450500c00210420080c140c62500080d0014a0f035040c0f443c0c4080a1400c1c0140280c103e001501c0340020469590b08114645880180d14280880d0401e00102161f86801e00422031003641c2e50742c60038640303192103519540d070080b0b80000000a845458004214801c03903188039050160241045249001400040440070303914002c2c0090b004034070300141154a0380001340d005078415070741d1407000700b6030b40d040055500400034040081401894014280d04002180d80123860980008040120983d0300c92039034000c2e82c03410304202c0d05c1783d00c1d00030116958108a420030405841007003855001d154001010358441d6409981d107145480090a5060310307441d05444042e00310504550 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 460870116 1250 460868866 460868869
    0xf0305032a03070c0f0c060302070b06030a0b160905181f1203050711090a0c02070b0a02060121050331120201081b0d05090d050c0a08130b0c0f01060e090c 68
    0x181d403a4602030b405440c5000040c6c4c40b80a039020660b400078004c240c2c00034a0a0402440700d202a50012044020b009145915101c1168140005020301000c0e1a00203100540c1c0e809007a501e00a400040c2030940710003140e221204105000303503041108120072504007041c082402c0109010b81e08903071521040060680e40540e90380d00b06d46021940f211582050008544422040c244280e02ca400049106a034602001c2e04144480e0052101700c0410421700c1c1046400040c054112074031100d11a28640340b06480d02805600c00c41e00803c0c500000842401c82000c610b01001034050080e44c156182000c07c1c03418100c440c2900c1109042d0b608025458099070040301c0c01c50380b013030a40d001a005144208090301659024a0100000e42d90701e101703001c0743c0c0d80b003000501c0d04404642007113032401204a25003a50303100b2010000740011000245201d02c007070840c0041004094070907246440f4940d02492580340e44407078404120540c070380800000d10034810403010380242070a6014005002a410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 460871366 1250 460870116 460870127
    0xd03020c19081c0f181a060d02060f04081c0f0f080f0703060321020c0405043203040e0405150c0f0904060b0408030405210c0103180f0305032a0307 65
    0xf05003040740e0303619a0b02d4848102a4000c90b6008001016008000106850856a60210303060600c100d20700300360400c0081c3d05e41c43d540c00b42d81501156402e0b2102c1c4800350b1a1128480c0d0340143d4802d0207001c034520800c081120000c07050013243e07128200e4a03100c00c4403c4800000a4840e0000111207030040380241e100380004a810510305d280115100780c4030348030041d440003140e0b646070b80001d00540491540764180104114404222428401030405841d90302c0d4160b0703449000c404e00d10b0860700c4c61007006203039040060304c1c00406040e2034944d55a17081c0c14000c1c0c0b00403141602c09005000c544000850440c41c160711495080700b40303c0c14a400c0760008401038204010681c4c00540ea0080441d4074444400904020110000110b40e0395080c4030034040038003109800e10024110219901c00c1c8144082450340a00e402864002601105082c00d08203c0d840b84d80081c0c5680d0b07616604105042d400001503204440c42e10311170b000340f9081041196101d064441130f610075041400860502403050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 460872616 1250 460871366 460871407
    0x70902091509011106041b0605040b22090608061801021303121404030c05190305100203071b1109060f150702060427060f03080702040e0f0d03020c1908 67
    0x615281c0813000d40400c0e05454101d00b0f0b1016142d02044403100d1076043c7d00c03003020001030070192030f103242020310340341d030000050180540c00807941e002035000780d5800b403151141034010143d40d9810b00000e5620301c2d81544902c4140c98081c81c0c0591030280b00c900c0e90050080350081b036227104000b0700e864a503443d540518042c408003001007240580c070500300c0e9100e1501910240d4003806a905807a0314003401c00541181e10100c4402d4130034003003020000b04030003044054150001c134070090794030340c0e500d01c00b00d0301e0324001da41400b104101c0b90102c5040c820211243c80448105a54112446e2105020440001e0b40e14418541c01118140d0500c814542d600c050b2000c188040d040c1c41c00c0c6502ca4500102c40024582e04801c42d590750580c0f02c2e2141c10744d0140e1001800c02810115070a030441d243c2a05520600c88042c1c040c98842c81c604840030003c10030100b4045080003550440a00705600a010354000180c000c094400c042c4400071140300c4c80d0b6603509081c0d112080500d084030301000c10014911a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 460873866 1250 460872616 460872619
    0x30c0f2101120b181f0f0b2e020a02041b030510082107020405010e090606010c150203090703331506080c040e04030f08090c0109140402040b07030302040305070902091509 75
    0x1280221741002e402103001140c4d60381c8449011402c84000703100c0c1c10844000c035028a118806600024952a603250400111621000103a01d18521b1080059241c0f0b084810000d400070302d405aa807449155aa444000318070469034140102d407205c208000303372003945010700c0026400c010b44213125100c5058007680c1d001c44003403046040079015000507040715026401218011580410011918014002c180e03001c0000d00b40035034440065204e915054030201090b0ba25540e00001182c6610020040c61000395804001e0494185030030000320740481e065107c00ca6100008823040380c00030024040e0400444900c4052480c0c140307458000c8825000c060101d014240c01048041880017a81e242248a036010340c03140c40d0900c0e0070080047c03c135480185450029000180c80d24120703a80040041c04840e22309650603021404840040c000740b0642c1d00c0403140402c00150341e010180c0507000340c001c40b800b540c10394418030340d500031000c143d2051004840d400b6010390b4001c1100c00080d009081042c80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 460875116 1250 460873866 460873873
    0x3030a1b08160b07110606040c05120702030d06060e06030402010c020105070b070207051e01091403011413030e030f030304150f0f090b01090b03030d02030c0f2101120b18 75
    0x5403601c03000754540c0038000c80c4190790110141602406441c4588030b411994a2820f4101664a0220306403102c0c0d0140c0454820360310754500000c1288a442a50185c844420301c00e80ca905005034041e6076640b01001c0c0c1d8a046003000c40018940d4003640a8600301c0310043c141c0c62565a880d8011504290030f038508a041c08030500c040c0010481d40c81c0024407642254000300811070400b4204070040205401400506041c0540b02a903a64031044440444000b402c501642c000d46d03400080c05000390f0039892103000310b00010080161000c2440449043c002c1c0c4a060f09445030340149510341104116039a400d92040000c5400241407101c0400900664403000454264102d4010140e0354188406654281c5500f11402440001070411380141041d120030403240404030046522070107080002c480c49580803000920800c000b4080b81c0700e00e1b21028201f9a41c501d0300e4100305008005000003014209030000200b44141680b151500203070300640c5101c80f55558819814440c1a83d5405841500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 460876366 1250 460875116 460875167
    0x83a0507050a1103060c030103050a1709061206330c0a0605011811090d11120601030b01030501060b090622050406060509120102310f0f0314070503030a 67
    0x90701405907042c042d100b00528090703002d00c0070400d8906100030300070183d12001000100001342c80001c2d0b08541d55400340b0180758034100c0c485414454050506999001000014541c0c000d0036203003c0c0b640b00d02c00032648014007841e0844402c0880320311850444805000c16400d40d50b42041a000d08402c82c0c0c0d0104585052010b5900c22054170b100781d000350210244042c1c502d0303202407107000b003550010000140b00d0810714680001015059404405044181c0840d4100d10f1902e4a4000e84009011401103aa81c1c0d42d59160508804800f4030003502d0f5035290800110700d10188104403950444e00408144c10000c2210b400180a101e0100c5800202c1c05190000b4803901e607030191800511340da45031161160020024451400302583d0034141c16441002040d801d0702801080d82d0001c1421078030000b4031600190100d02c45d821981017039480803850301000506400f04d442c540702b60380c86140692510b0707140130700480c0d440300d05000b012f80c99001440f209445a04c5144103d0030300c0c0c0303005400142103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 460877616 1250 460876366 460876373
    0x60601170c13030606090e0d080705160602120108100209010c030f020a05010e0c0f0a080a030302070c0905010b0304030e09040521120a060602160b030c09010c060c0306083a0507 78
    0x1070640d0048881c240c0304e040c1040201601d1054007c1411020041d04000d000800e0040c56900002c10401c00d00002181881e002d144c0d00a84000003584000110b584002e08100380680480c240710b900002c2c0300e255119007803904a40203546a410042e1204003002102d40e5081d1800c00202c4140000c42c428a03a002020907000d0080040e40301c2c8a0000d808030a0b0400c0c140900d81660700a0a4041c644000c410045544005040040c0d503406140050b00c401840c58004803294075984034110240c200000490100700b5400150b004a05c40c2c2c40d4030303030429041800d000880300122030141c0141c0244042d90300c2c122240800580c1c58005100461415000d040384809020040e40c003001025070700d020030710a040d010005602480c405020200d00545007504608080c0f10007480c0380030681d03020405403007a9000712480e010091340140c0500030820b0151000300200380038880e15a041c41100d03031070584604d015485030100418035100c40e40d92440b1032002c40c0c00c2d2003072001120030000c0c10807100010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 460878866 1250 460877616 460877647
    0x609070e032e0614040c020a0c0626041104090507170a0b07020105061c02030a150b09060a0513051f080d080a29190b0a0908060601170c 60
    0x41401c6448044403a00305082e2900c5040d5504444404480c0b51001c140800c08200c03900360340428007180e020941c1c01820000324148286048000c00101940c02c01003011a08025404826107224040c014002c40e80d81c0c0e10741d07072004207071406000303c06115502c4c81c2c10b0a00b50400c0a003503000d02c0032a21304541da540112045c10f03050000f201d840d040b000303c0008120107600c0b40ba0700724100784001e001506081c1c000441d00055122502d054055400d100d10854038203111a50300701c0c2d00a54440d100c2441050443d000d0180708621f944102d00c42d4000441ca4900400d0b2031095407805001d050f058007101206000801c00070300000c8401014002007698140d000c502e0340060080c0708081c0500300c800c20350141030740380041c2c0506c603114100046211f0103c06140a4508150ba001d11240d20100303a0b40410400c410760a000c0850b05007128010484203540b00c020b151303031074440e603400074620b50745c0d03c0e4281c50391001e8035110300041682c0d071002c4466034408901c0e50404900042103180070400418003c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 460880116 1250 460878866 460878883
    0xd0b0d14010209120601031106070f06020a031b0305010807090914010504060b03100603020105031311130c020c091b0307111b120d080106050c01150b030f01120b0609070e03 76
    0x2032a07400040c1c80c10f042c01d00c1c90031100c180380a20300030410b5504507540d0112840140091500903800805d02d401440415100690ba281d00f005c811945c0e180510401009441c5104c0b141c19004d00030900003076002e1181c4600c604807407481019103190b508214181019110a00c01911201c0301d40c00707030718207040e0300303201c2c15001e14402c80001807018101c0f4141410900c03c8103504c180580381080c10400350360054101c0c1e038881d02e86c01011000496500c0e181d68502c044e15821070f00700c0f07000c0f6002842e89216070321039450060f094088441a040c00f604001e0300c080211814007406c0b100703d000c01007081071240a0364001c030f0181408012000f10420051401c0003030000d0307140d082d518181d11401420300c80b183d0000301990401504402c02c18a00c058442c2c1018032500c0200b210010f0a4400745100394403c41c0540758405a401a6075513a000ca1502608140d0f0111410950703030300009420350808200c10030190b4444164401079444500304814810010104010300c9010103401c1c00076034040c0500c48 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 460881366 1250 460880116 460880153
    0x501050a09092301050d110f010912031205180a290705030a1406090f0711030a02030706060b0c070e06030a0204140411093d0f1e03080d0b0d 62
    0x7403910340800c1112680b004107034003150003042080901400320343c101f001c42ea00e00c0010343d0070307200d500445c0c0012078294400d64070090701403804107004810142d118602400c2480e17418070501c013130348402202c0c0d4a4901544110303134481c2e1206174100005083e81100385a4030102d940f511113114240c3c00391f6130503c04110b52100c0007940000030007512000360f2044801054041e811080b041ca4403601082d03801130302030284a00d1140c8840015075242c42400204035990f022015a038407805001006942d0342c110358000c84051b400c1000c04200d0148550030381d490300860f02c000f40740302454070b60380c0a09404042e0145030540181000070015032100d0003141810035019282c0c1c2124581400c080c40c1c0e503207810405070b01ca40e941c0d030706005020b4000141400200701e0f40c414070038400892201041002e9010514405071401c1e200d000490041030241001261040403500c00c00e80345044105c5072181c0c0347e0000401444007400080c03454181c46c1c0c4000340c0c111003d4000e030f14044081d11070320040c80340d84030200f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 460882616 1250 460881366 460881401
    0xc0f030c070c0803040b0306220f02071e020303092116061b0c150309050a060c14090604090f1517010606170412020a08041d0609100501050a0909 64
    0x10010011000b02c807000425483c00510b04150500d16402803501c40541054070801d01c40b0000c8201100c0c42c0032050401d0362080c02003090f10b8031100d0384c0300039400900c0c0944031000c1c042c152038100d40340d49042041140d4000c0c013441c42d10103c00c0420083c0041041420102d05404946126031642042103d00d510002c05e0412007003031070008028404d08401c0040300c1d020382c0001111000520900c0900e003620700400c444500d00c15606800c500500320200044e00c1d034032501180e42c040c0800c0f40d21a008a10030f503070342c440c00c1c26a0b110ba007800174401c0231149030700310030104800c1044900030b622421000340903103000b03d00340c850603c0280c0142499041000001d50300a58480f000009101c0d40000307080a00300140c0d802035a842c41d04610400900151030145404071504074a44244400d415056020300459203031603c1d02c20310540050300d511044294401c00000c900b40c1c2c0f50800b81a03105424070340c18407003101d00f0303c00115410780043c401d11007401840c65002c6040782c0a40550200c481246220 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 460883866 1250 460882616 460882627
    0x307152007171c090f060e130e0a0f060207230316061803021005011523040308030a05010f0b18100216080f06100302010909090201090e091c031506080c0f030c 70
    0x5540842000c0e41c811400d01c101202601c0709234803169005030b4884000c16000078540310b0900c0359420801d0040c00109004106c11110080160540c0604036541c024010b54040b100c41d8865900c864907482070000a990043c03002000c2844c1840d40c0d103400b41c3c4145400b05411482d40b4120b40304030501142180035820414080741103111038800e0340d004146050b00c0300c03504250712601401003034850440f121030140003104082e488144a040314003c66100c48c0c2d1b1540c034580003100720003d180a00490201c03000c0d4420000f41c0c0c070f18482c2690b20079080e12510035444081e1004200d07590820102041c00d5004406100f40000181c00140008150110141c240382061159581c18a40d008200c3c401c40c18900105001503680300070300b40c080d908145400241c00d0014001603601d030400c3e074172010503a0302c0d48007009490b520101c0c4100d8102004061704e403581c2107844050703055444071030079180c1000104004000d0329100b801e042d42c0000d0044895450001e04900c12a00e542c000c4680c0c40d0031510020b207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 460885116 1250 460883866 460883879
    0xa1203090302060615070b090313030309030b0705040b0f070c0905150301060b160b07020a12170f060603070c06150303170726150307152007171c09 65
    0x152941302408a60200d081a0030054004030ba004401000d081600210001071f0340d21820000c4400440518041190007a5a46401450b45055000c1110003003048400b00c1c1019000d501914240d42c4081c541c107041044070040c1c41019004a03100740c0310303240080e074001a02500761185a010300035044003401403901d850140350942c6c00d560302481760500d0030440c001c519008480010b08150703100e0170b2640c01e901c60303200c102c1c504010600045c000240c0038102001d140c0d0084207800520a4280c8401c0260382c0d10242c42178000c2044815a070020300400000300701a00c0b81071100c400c03a00c910400280c4501038060700d03402d00115041140846d80c000c0c40c0070003060701d840c1c02c0780d48401d192400901c140b003580c52405d0900c481204501190300b07084003143c01c007141c0d850440203105d0b0180c202c9500d5550390402d00043c0c01070007080d00220391741004201c0030313005240b2032100d40a222001824114900315115101549142e81052030f80606251161080202c0c0c651b0301c20f0b80020707601c500e034640c02c000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 460886366 1250 460885116 460885123
    0x50904060f03020303030f070212040e0f0702010203090a080a051c02180d20010504090c081503120909040602090d030908010506040204272c15060a170a1203090302 72
    0x10041c08191166440400040e41c0000441c0ea00000310b40d5280e03000e0300e079038100f030745010840c4040c0840100c002c540030800450142c0024800c00129441c08515110500144e00700d200030342d00881650090f86d03080c400f007194440180742105440c0f42107468003886242208a00c104640011800c41d000210054104412034001d02002c1080307e42c242d9843c000e03070381c107248140c52402c40240242c1c140d0310340c1401c1c0c1c000c400f41c07001085a62030621000754005001010396204840d0200b010302d0220040c0d02e5401c00207040544203842c505071920b80312151040010b506001041121200c0d020800300c011038480c42411240e9030712075150300d9103039401c0c81e00260a40c0c5d4010561401584103210400624101011303000710340280d4048180c07103084d83d01441001c0c0946050b40505e810160f40c104820800342101001a10f01c0c0d02c0a442c0c488500d0705003000a624207648580d0f1000c62a401804465030b100203488801c65414100c841c0814681e48200102e040c42554001082e07603048110140358050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 460887616 1250 460886366 460886369
    0x309040f1a030d1209060f0c05120108300403050f15070810030f03020c1c0c0b04030c0b25060b040510030819180e04051005010b04181b05090406 64
    0x46003d0300c66002607910040c0781c055030740d0607803010a0302c5103e21001d02400b540083d5480c4152482403101140440026100340d000064400c055000640000b8118601080b45640e601302940d035440941d1040082a82c8480028001c0310300a208010000000301c0c1044038400c0b24800001070304444080310301c01c9244040003005001801401c0c0c08021442c18000000b0040e617a104442c1280051036040c105d140603032800071a604000500c6510310643ea10512001080e4807c03c41c01000c01c1e11a640506640a148401410001d01c98414009c0f003050714050101100c020500584100d02103040c000b003c3c1c1454016500603a69581c3e083c0541018002c041d0310a05107002c0e041060f00d9955103101c244101030740c03d048103006200e42800346100360300d46006070403140100d00c6415260403d2501e02c42c81a80c04030b03060320459a020400c580c00d401458100c80000310818101854072180c3d0f0001010744a0503011070f9a1804c0c1401e11105440b41c1280c4a4115070300c45071692001d4080c0020cd0380b00307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 460888866 1250 460887616 460887619
    0x33010608010503030403120c0b0f06040b040e060f18010c09090f020703090e0a060902070507080c100e09280506120309150f13030f0203010f050112060e0309040f1a 72
    0x350010700240d200082110102c0c1c1d404541580c4143e814441110313900300c82800103044800d001c0900011404800e54140259000c40e030070800f006106040004840740a00300c15240c0e0411170020359610f01c4446619400080e01d1807414401030b00c40c209900f100d6460880743c0228102a20030302c003000c3c040c0308035201d003100b0340c0c000c500e030040780d8501031701195551152260b02884840010b400040c2c42c2c101c2001400300c420259210a81450400c0d00e80c21a03005010091185003600000d51820781e00ea0702c90306ca0700d516480d000711228014400132110080291040440995452401901d22481d03031808619951002a490a1010402c95490340300050588154011b0221204541d2001c0c0786007142440c0d551074a41e608101c8844441c50b00680b1650341b04098820030010a10100c0302c548070005201302c0c0204103e15010888400b21042230140003d11900301034003100050296010001c00310800b81100e041400c1b20001038103441182c0100e000703258640c3d9508000a480200d54a1120740 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 460890116 1250 460888866 460888877
    0x120b070309151a150d0c1e0e040f0902091b070c0e15090106170402032104031406040803130311240f06031f0204080303150f1e010e03330106 62
    0x2406280d42100e40101007151700b0541d699803100d071805006080060300c20030102d6411040011140c03014001024a5500b90300071f5003042c400000c604480e206141c0160b03402424601c0c0d98070703004801524031401e080b98401d0000104803813008200e19103000f400900a40880c8409460811802c140da4055244002e000304064001401b00c3e40d0002c940c0d110082d158401121203544a000092030014456007030100e4114104109451900c2e050041054038020b02801101e246060200c9a42e00002c9801404856040c40400c004c0650b0850b000d031424003e141000390501128001c90034000312056407210000030102116814050b405290744c0400c01d04000c1415281910110384c4500b121341a901ca44200e007450070080d0b0116505940203081508201c90301c901c0c183d000d4030000800c1c5040140310300d040300c442a0407841c01c45c40400040500519184034040f203c0b0054034100b858041132503041c001d010011445800003d01e0f071081d0040e1034200000c008030101c4841d004441038002108104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 460891366 1250 460890116 460890139
    0x30904092102120a0c08190519020a0f0803040809040f020a120219080c0408060a020711030c0117060a2309060a06020c090a020c01020c1c030204120b070309151a 71
    0x144010240e0b018051181404a56880a4a010700c10740c0700b84a00e90030003681d141647c1c55034940c032001421301c43e2040303980e003500450440d4050360b40300d0708600c00815444031144114005184c2d5000307141c100d403042c000e080c03d00403d40c0018050301d581407d05590542e002c00c3c800240b035809111150301107100c050442c0703040c026803c01d04084e14141c0071a024050f4200214103140f5941080710010134200042e50520300709420110b0103903100042c00d86031030600c00c0000c15985000314421224001c140c641668107a510407030388100760402003c407540520301240004241c188000420b041c002d00308002103c41014108015803590040d05c00f81c0580080a8140003154000550783d801600894600c20981d030344c411090044e1007240d0f103080301035002180350001c4132000580020070307801c60540f400030700542e64822802c9018902c00e00d11042410b107404004606044a19034003c28203280200e429402511089000c020b9030300e448041c1c1740d855640402152071045020303508201101e440c080003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 460892616 1250 460891366 460891393
    0x50613020906090d030c02060706060501020705060c100e0319080109050a020a02030d050c160305030601031a0f010e0604080102070f060c080115110c190e09072402030904092102 78
    0x50040c241c03503e020f0300303144c0316903018180a01c2c02e14406580c0203080c02e40e0386038a850300202070107071031107454094400c0c2240030030140791040c16078044100c0c0d80018440101c000310014043c1000070f4907588140010404028400418070600b00c8036005500d500f401c0e5407501d06102c0072143c2c000c01020342184140054940c00f80c0c04800c69064410f240c101165a0f05c032070304950114030070481d10248020031903030510b003015082005107201d048240c904212840810f1183c1d030f2080e5082135103551000050102040a602401c1c50310304440000c0d01c0581001e031114407290880e842030005840380c4c2c181c10015801c0012901414a842441d0f107800c841552400340b411030b804642100c00401c1c8030341c0409030007281c40e081002e00360b03c2c02c00505040c0490700c8050301010341421801403076119005200010742c6010001012409c6944034403150f02528004201450310034010440002140010051500c1a54650080101c2140a4000795208890815410600c0c001c400d400700c065401c00184074403072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 460893866 1250 460892616 460892629
    0x5091b0403081336050105011b0f0c06051b0a0308011205100617070e09120a021002040807090506091b09030f031c0e0604050d0f03090f05010506130209 67
    0x22654007020a58850002c03001d1a103084500381c0120603c681d192000840384900c031101040704130f400181003044031200107199003c0c0c0d0000d01640e408a10682c44d003030041504010300c50820390107111041c0004445503903404c45805140c2c0301c01300040001c581c0040184070310b0b11450741c1c0601c07000204410301042d034016000010500c268001001c0c2100d9600500c030050141c00e06444050804100e442c2d01d071030310042e021980f0000071a0a209060300850b216a81c02401c5005201c418010000311300500d507462182da10007050700307046000d800c2c0e149003103140a001410144c0b40c81c4000c0c01c00a41842c10700412244018a04c034030802c2c2100034032482003070740c0e902c90007140010000d69603150003d00c0401c1c42c00e80d080000c2c01840c4030000380c120150043c0d02c0607044607a41e18100384130381c090600140d40c0d00c4409590282c072035040100ca011044d8016864201c49e0441400c0114018840c4d4036520205074240d0000d0f92540d448004100c0d0ba85482c2001400c05040ca080440c100714410b00030980 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 460895116 1250 460893866 460893869
    0x2001182c0f01091508030c0a03031b080f06011b0b0403030c080c16020627090c040303050d0f060b0703050a02070e0c0403030e040b0402041d07030515040903110d050405091b04 77
    0xf116035104409024122003000041c081c104080882c0c4d0b07183e0412a030070303589202040090780040c1c60b20310308087c1c07003041100030401d8089580d030b058111386034400c109156450180c03402d4140200c0304505070390002040c1ca00580607020324a006400e240c80d09024090f14231a50f60001086036030b1042254a0300d0b82020749003800c1105030195040c8030b5504c042401403041d0600d0b500c8048483c100e01c4141c03451000391050080c81a01c916016845010340c9001a01031800000c002c18001e01019111103803a17403000d052250354600100c0d40540e64519828107901c13000741500000c0b0005900d004494040000e03000501000386821450700d4600a17a8003503003d1070000030200314680310307420003590703076600201400366000300215540e55407082c0f0303c040f040000543c0d4061220140000d4940d07406841140d205512000414801c0c0c058581000700038000c0740c100b1001d106150005101c908010044944c08080e0340c0c98042c0d9960900302000041040103000541010b844149055145142001c4d0360 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 460896366 1250 460895116 460895129
    0x2010b090717090109060510081e0a140a080403030e1008010e0106120605101e0e092701050412030b03030309032d0a09050109122001182c0f01 63
    0x10b1641d16201502400340040b44806026103040c50144540214048600c10859155400700e51050b46125409101951031000d0700525410a807214800316003030120081c0349491090644014600a17611100590025001980001e68101601410b42401130030344401d03620500308a02c803907251686040c2480030501a0700100900201c0482041d03201d9080384000d45402010319502440c81d110040500c160360300c0c1c0c00049546a80e029807080e0140072000b09007440601201c0080d55582c1301c48903000c20103500c0701c1a11301780040d404100c038828458035014611414045640c0501c2001c01401da0381031190307041c805d400402c21b00160160000c2206c03803009440d5102d903072002655a08082210b01c000080024003000240c2c40000d0758001a084141c5209890305e550054032401504128406070138010071048802690484104e10141080300400c8145800c0c4000e20b091800004030500c298000c1c3c40d0760600f1010445900004081c0c0c07444126542456100c5180c0310a0b452401e403130622540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 460897616 1250 460896366 460896407
    0x4050d110a021206060316121e0501021c1505010e0906010c020907260c220b1b0708120711030a08040b0310050a150518040c02070602010b0907 63
    0x1a0400302804007107080c54000309400e040c83c08900005403110700840d0094481d010740c20044080e1008074550206480d240c010900c3e07040895540c1407000301e140326241c0c10003807803c241038001035001d000800000d000fa42c24203100c50340801c0044256220403418003040c460107035041c072480e68044c4500341c84501c1100d2603e40b549a400040c0c0b1894502500039410031344002c00c109400350001ea05a51400400f5041989a1440d460324040c0440594090380300001c200701c1c18000b4050440c00030000c4402102d94945a580d82c411254181d00029168012041700ea03131607945c40f10148200c00040c40c9040181c40c440211304440142c80c422008010b10320200389148076400d8400308140198a5400860556120f880d2100e03015140c0040700c0301c04042c1c0e0041000309090400d40c602c003003107803d400c40f42d41d191100540140d40e503402025101034025004004000155039a0003174014400326500640941800e14900a00f501c6810744994024401c04040c09000e66100058001001811000707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 460898866 1250 460897616 460897637
    0x40614030c090409030203071e11040c03150602160e01031a100e0c272b080d091b0308030105011101150602070f0602010e06070e03340e04050d 63
    0x6014140203a042241e0844c2c9002c46240c10150004001c004150280c4184202c40c108032540d0000c40958060060648003c509281400e04203500518500b0845040200d42c87e142403400602c2407030b03543d20407030040e404103404d1222900c034560810050032544003001015030551b2200c108a00034000354103204010b50b00081c4103195040303049009802c0c0c01d50141e4481c10403c9915065401c103030720849010f48100444550402c2c034100c043d640350006041520340c0c0d80038071b0780c420030704005010610010340f83e004901d002070624001440c1c103075040b4600158914050a068500303440c03000340c000c42c000111b0f0043c000310380c0900999045481c00d20b000d401c40410f01d00c0700c5014202e00707000540034100c02c0c4404a03045c2d40104040007528141c600307142c0300680c0ca190490030384007840c0e039084082c0c1000c004920a2071007400c5078890f110001d002c43e0041015040403065044080d4446000c0b40115080301c00400d004442d410000d1000984c4041141010707151151148141c403200070031b000c5081714 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 460900116 1250 460898866 460898881
    0x200a020f0310111902030a020606010e0409020316031e20010903020d0501060503060c0a05041a040f0e01090c031109090403110709020909100303020a032303090102070210020304061403 81
    0x140140d8a00310b40041c0143c1d00841d007070004a802148800b40f0041d0144070f1511441d10000503902000d010f98010080c1d038480e034006542039404280040c1e08140c8801c60708002d42c804202411b00002d548600c50903051560515200015024294148080c29521510003213210712142400c0000d9044e5a03034048600100180c52400c4241d000035000341200d209035007405010f50140d01100c40a5007a00d8140d910f8107101140d900c5080700d0781c0c001c0342041c03100707100103441c01104444003006a04a10b1415071615001c082c880d2a5500c00030508624200621050344140201e101c080c0140c20140305d030780c400321003000d45409080b020b94025403004002405151245081c0035070780c05501c007a00d40301612401d95001135072000d401c440c0940c010001103083c0709144200801100d0701580074001202c0255011141c02101da00680e11054104c00c0c0700d80640444001103008803c01000180e8034902c40c8140301c10a00c1c40d84945041d900240802c0100c00e07041000a5950780c2010007413036480c1c3d50f902 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 460901366 1250 460900116 460900123
    0x7030b07030f06230906061c02070503280c0b0f060d021c030e0f0d150902060414030f010c050912010f0504030c0c0b070305070303020d02120f07200a020f03 69
    0x1e1801200504007100010541e03041203600f001405003000156880302a2414040320741170030b0b220541c00c007070100505040c50410040c91190079444410240c5040070701d4449501e036400415078648490850400c445000e14180e2041d41080f078181070111344c807a15a02e900304a0391000300040d4440c0101c00020b82ca0340c1c5c41c0b1354690781c0c003540140043d0380c071503c05200b09040ca0711000200c02186040102104a00d4401502c1903495002010b880b01045641e41e010b4600f10008a0f00c0286070321908000016502d2202400141485503d0361091701d031140704052601c44224011074491b45040036034030880780c1c03000489004401c261040380b2103584c007803140f500410007589109142da207404240b00030103501501c02848035004880c3c801000e500c81c0007807003a81c41070450017000308508010402c0005e009801070607051030681001400c110302d02110311841107045071404000011841001207460b000680d505858114440000300c0540c01c0c1c5516943c0e030542200a0b01ca505050105030941c0c0e002c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 460902616 1250 460901366 460901381
    0x100b0712022103181914190510060e0403080402091b07060b0907020d0503060126041538210105040c0909080915040b04081b0306040507030b0703 64
    0x114900300d165042d40600829a800c19582e00c41c071980003111a01e20356200103074104049000807507050300507080d561034030780c45042c4111400080c0a40c214001100c810f61603440c00c02c0740a0703800f60020001007020b40c404c59009400c5180303080000701c144008030740d11010700c1d640150705590300b1605844601d179041e8651101040e42200e6100010040208850b40c0c000520700c54065680142d15299a1021f90300c8040c03400380d100018205200050322503115110b40c030f603240c840c8006520310066001c0800f020000c12903043d156400d0658405092105c2c610845111403110101c080d4030070120380c0300d2035180c000c28624020352210502070140e26a98012440c0480e01000070340c4681d0811881054081d060441e01950010502c0f003001a6210300d5003e603020081d84801e402c1e00c0c00501004004019a50f0039200c4440c050911002c10441580b500600c054a82c80000b0000d030f00c0201a5a07103294941c00b2003502070b410807000c0c040082c100080d00402c3d6131703024031031440c566a003620490040900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 460903866 1250 460902616 460902643
    0x3090b15010210290a0b07060c0e040219090f05060711060d14071b11011209060501080313090e2a0a030c06030e010c020709090303060f1d100b071202 66
    0x10b00c406411912584080110394a20214155440781c8210003085007180342c9210b441c0c3c0c1a0f404009800014110754040d450070b81c86401d0400c903c0200740b020030101d800020300e1213741c2800c8001d40e440035801001c0d92004002d40b6101141017401c1901144860040d1407000f004c0442045000d4404d03511201178841340c416100040250302e0103000a4400c008080c0d440d41c01207a29030500f01031030030700b59604031002500405140d5000307240c0b000442c0e00c0c8600d6030500d0505542d500d03444000030103601030030b0300800090004680f80c0404040c88004400a9800b810540c1e19048840e00c1c40080400e003140e9812210001c0d0743c044002000150050109103c0b5030307400000c0c06004410410041400c20903240280d40400441208800d80c500300e9040c103185001607401000104030f8003a06801590046100b0324000c2400303a6280c401307913905a583c0e0061792038074800c0001d00514580c50141568058a116124810321307182c420126610312501101501c0040e180403c503410314000c001c660640242d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 460905116 1250 460903866 460903871
    0x60901020109291302060a110309130204090b0f0906010305101e1a03061503190509061609030b040803180d0f0906020a05060105100212040807051003090b15010210 72
    0x1000c00b203920794064880b182c0f42003900802c002c601c042440198419226134080c014034a0040b952200b50b41c400050015240107110410411f0080c0c0c03a45100c0103c0d100b400c52015803070340d0510070054259540d440700103010301050119015140e4a2075001a041802802c3c006000e459000d00d40390305284c1500845c500101e406428000d01d0301c607401000c03c580340c001c080d607039030585c4080084a510065030300031740c000c1419803408000d00d03079040115040307040c4034405202660360520940c00d9980c11100c08007960404020403c0a03504941a4130380650340b40381810500342169034048515a010304060503520707011000800e092012041e02c0c0c03059042c8402c07110448502d400040045010002d4440025a030390f0000890500008550010942c40006007000c0d0f801e202c10f00a01c54540000b0b24210312640380c00d60032020f007860042001e0840c080250030081d00303007010b1180491b42c82d51840f0030940391015020102c0c0c03600040d907420400c103041c1c4455850844004030725116221081010191 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 460906366 1250 460905116 460905143
    0x1a04140406051c060c0c050a020f01020c0d030e10051e0a05161101120203062b06060f1502150402060702190f05090609040f0f0f17040e0a06050a05060901020109 71
    0x218800d0024803c82e101e00307014020b440440c1c07422180d41040200c0200030368442440840149429890403410080600c12100d03a000040d0000d66421040e580a47c00b0856000d450015400d0008412400076000e0915900e407030300c1d1003038002d10001003440c0c1e0309010002081e08101d0781d10444c110342500d007c00c040b640241e042030416500721300aa140c100c1c00f1034192200e102e00001c00b1700070b0301e02c5064020101840035501c100c3c1c00802e4580301111045079504180d0060000d8054070815024044100000b1130481c10034107261404641c0010b0241554000802c2100c00c81c0e04040d5190b02a60544030140ca4100078800700303041042c03040c1402081e44051074040342000490998030102d44080b0f034441102d0b21513009102100405072000382006c241c003a01e10001c100c24018102502d8441c600710707002c0503c1ba0302c4c0c0b00b034150a80c925282c40c070b1100040c100004c0400900264114420380b0040040364649000280c526045104d124000d0b0f0000c101c440d5140e00030341c400c01445410080d914901c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 460907616 1250 460906366 460906399
    0xf0a030e09090a03020c010e01050c0109050307120509090103030c0f15020a0215010b04090e030f0d020d05010503011b0809070509040f020102072c0604091a010f1a0414040605 77
    0x4200300e18960003040303030304005460914000b0340c03120140c0d01a00a401c0d040b402c00c004413002926040310f241803100400072045000c03424454407005078050009107442c1c010324603205000c1440d00c500d0700c007085401d004104881d5981061541102ea06003004070301c12101d4901418030000030303400a01500c01c4801c903542c00c106103070010030b403540380b56003540d900c01c1c0c59980d291089802030040d030101d80b40c140418010f08600d944002c01c0d000a00301200c2c2410f41a02014405522000c28501c8564000c180035251072100d00a076030242c03208400a00042e09000c90044020b043c201b20786080060f00c50105007031010502c001d0000d840080e0201c9054506810304000110049008a0052151120015854201f10091314040a1000d01e40c065440e0b8201205400741010340002e902590703c2c584180046d40d200f85501c4203d0b000052096998580a5884100315039680546c502914020140c00c041054804440c299002c8174104000c101080300480d0081445822450b0030801991910001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 460908866 1250 460907616 460907627
    0x71707060608060c0c070e060301060e070306240509010804140a030905030706080106020601140402130e06040f051e0405070b0705100605030307020a181401090207061406090106110f0a03 82
    0xe41d40b280c4203c400ca6164070500e0704180c401d0741c01984164220a1040c01500362448000b0303003100e030080020400c26111001c1003000d46055441c04c000c83d41d01d1208000700303241056401d904400c03000b41a040710460301d5001c0d200b0320446030060304000c01400041e003009090401912019520b40c1100c0131845c5c0c919024107009264010240700e441162000511a03105441d81c0703050310030990140550386d103445910300c01e40300455012035100740c00384004c0761000400c0300b0b0540100300350300000085062907000c2c001150304810900640341d090204010752902d1000c04801c07240c510110700c55060741c1d0340c1401c41c240800e80d001621a520001280d000b4084005135805a01540d076a0801c8050340e5042010341d00c0c030030218029080100e9400400c001c080c41c0900c04c56aa014020215049109400c13891b83d82400b40c000078415a8007040c0e080030311034244140007600c101c402c484001400d014001961840c0148211401c0003074401c964600d004e030a10a08800e00c6900c070490302030013600c1c030b0042d01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 460910116 1250 460908866 460908869
    0x212070909060b100c020111070b0f030633070c0f080c09010e090a0204050c130816090908040308031b0f0909071b110d0507030609052406060717070606 67
    0x2000360074815804504d1824010142d8103800940700d5560b0804254010b4420081c050036068142c0606500021340c002d1000081001904420500c0d81da0326040c81000703603400b4000f48403040c510300c85802840000000c40043c0c00f01e000741c0507150320340d1024070b804000c0f400c66400030011a0b034030040004210000260641c5101811103d00c001d0381c0c0c031007184200100007202d041d4550344c0405d03064400750500b50303c034a4101c0c403484055413410a0500e04154149650391021413282d022101241c0f1806440c4c160002811030780310309000040441e15445802d01a40c00302802c2580004049440a10b12019505070307001c61005150b1256410164900e60390807103100f46000b8824640040c0f00f4134403442e901703003c2da0703240c403001240c1c6425a1900161105080319458211400c40001800716900300121801944518030100d0384400c24070b40031f8101034880c10081698106078020600740401f10740441d034004030540301da9443d040123081c40310070034a100c0e0300003038903000002c0c41e6828455203401880 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 460911366 1250 460910116 460910123
    0x10303030b0d11011b021c020907170a1d06040609020405130201020d030b012a05010f02030c070303090c0b0c1506030f0a0320030f040807080304060f03090212070909 73
    0x5281e090140280c007400e00100822a0046154080d015800b0700081114040c4401309407880c5d011507070105070443e5a01d03600d5400320b44110301c00c6086103060962117034000f0803807418180d0000a48080e01c1701203400340180c00703c540c03150f001907a180022840b485010240034102c4020703080509084004001c01902a4000e82c1018000f41d410310030b40c01104034141e41a4006c0801a040724412002441640300c00c5042200000010012038041c0c020f201c00507522100f1003081c81340034900142181c000562041c08140140108110300d110035041d5009541c1504010807090000d2501c02d0050440d60000d03821403801050080741404005106815201494007500c140d8503610105950b842e4082c61984042c0d1248800c040060310a980d61070003130f443c11114041403055151801d045800c500714003c0300c0c03400801c040240041c1084a20001e040c202c010354581420030300000d20340c1215a00356014151924002d008548402d43c170301d01344440c2c07503040d22904c0f9111038845000d44030001056 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 460912616 1250 460911366 460911371
    0x1403251202120a0e04060506031603050a0902060304170409020327010501030c0b0c07031a1b04080706032d05060312040b041712030a14010e07140d060b0408010501030303 75
    0x4215140000740a12421608962980c02c0241c602c0007184d0808410fa801c40d080741d11010009034503180c440186004410070141e40000b548a500d0003011150018029a08281010340380c2e409a11354400312a0050307004201a001510352001100d082d00ca50b60001d00c80074400000c204080b011240c6910000c1c0800700082c00c4080d0700703034416090f6a000c1c000600320000740c84080294408280044c01c00310460b005913091079030380b6151620301d4030720f2040c1103140315078100820440400754407070b503161029201d4103181003a0401c07201a0f581c0f5614010401410340c5d80744100240415881045550040294400d180281c0c20040101030601961058020301c0785000c406c40d0300c020f40c030659041d120b81a404038241460910707221801c0c0c80101040d00c2e18084c0064242d0605044070007980f03e2081400041021040f42d660545000e070142d01c0001c0c00000c1a042c4070030070741e01004c00180e00f0192103903252207000c001c81c03000007010280c0c0480c901400003d03000034a00010740080d41228083d4904 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 460913866 1250 460912616 460912643
    0x604030e090f06100f14030a0e07050102060717040f02061b0d03020a050702090a180f0c0b0702030c040c0e1206060405060607020112020304030e100210110a0c140325 73
    0x4a40c04402c080e00d6071980b0070070030075030003000314450914074400c440240750942004013050380c0030342c1d254015a0042c1c4043d4641411036440d503002c010401c0102402e10042c09141342907180100105288110311031031301e03c00d00c0802d05008084811030784080d0000c00240c1e0307a13a032441030681c003800e0074100003059015422500c0c940c14000c0c170940e90969007a440385440c12010b5401c200100c0401007c50720010b40e00c14502e018000760904501440780300b030b90802ca03000d815081403542544a80d020140903601042070200503140402d4003c1c00c01c4e02a5004101c1c01c1c812130050764a44550080c0726000080517032601d21441c00007505c94050802550208215103801040c48003600c12004003071f011071106202030b00400c52960096506c01c2c041d2820500c0d56502400195612045482950059020030719140d6289000c0c46205850000221098076000c1c400b0806000c1c001d50400c0900303415004c00c2c40c013403000340a0044a00300440c02000907044003480f1401000d4140c8507005468648141c100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 460915116 1250 460913866 460913881
    0x905040b090d02030409021b01150f150923100e010e060301052803051204051e0901230604060c0c06080708061320031504060e0a090f050604030e09 65
    0x80c2c8850340c4045501540c0352505003560300c0c010b9401800234007007040082401640c0d02100303104030300c10040000302800e20145004002c5c0e121035800d8008180306410103403032005803500184d000741120340c005289019400b01102024503112601c10b01070b00310031480740d0b0502c4158001d01d003110398034098858000c4a51190706000c0c06005c2402850340012513074002281c07100495407450018800c01482d804100e8507903071420300700308420415400030701000c142440245404424000008205810801c0440300080000c044003010701c2000028980f0304101008070440b5090101e20110140a103552603984000050982c4a1207905481d4000180408a121485100320500800c2c4658030201d4030745500d4200082c0700180b140b00b84803203995100f00c0900e07400045146070030320142c900140c1c40b440d1410650089841040da40380c03086c1d1030b140f41801015030301c410107a0840c008000005915189241a41c05215442c0015140b44140010082023640c4400c80c20790403175003a500c22195444004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 460916366 1250 460915116 460915123
    0x1401060603020c0c2b0308040b150f06031302040e0c0a05030f0a021005070605150f0103060803040e040f0c0909151a01181502030306120607091418010905040b09 71
    0x2d503d29465003060b0f00b040014508400d4035144020243c51070b41040c0c0c1002041e2404420640084001c030310705070100010720400440c840e82c080801d6282c8c0c0745c049103060000d1042e5142506172441004040040b84440c078100c080c12244580c003400401010203c0035281d66682100300030207220740d040c41701c0800c80303043c0403422550a00d61540180408a50365003080001c002480040e400c00005003c0d04022601c3c0340219070003803e60242c4270b411088503109200d0801d0700011100c0c145418408100030116002040700c04903004e002c03034502c00340c6a52800d143c2c8420103040c05008628807204c04a0700c50100da00c01ca034910321031000b07040143ca0302c0c01c101e42901d5410381500c1c00071017404012140d80d40100c0281007003100340d0508628054481488501401b0060b820000503130022007004000c3c00c04640b25051201228000d240b1850001d2001f003024150f409981c0341c110301c0032500d100786d07106c0c42c50954840030100c518020b25a102d107180c1004080c1290b06445154558001c52070045010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 460917616 1250 460916366 460916377
    0x1321180f03080304060e0a170c0105070203191d0a061106150d030809160f1707031e030e04020406050304210909020f0c0a0506070207090501050907031e09140106060302 74
    0x185060f00f9507880343c407458000c00e0b40f916000140c1c042c0c2c03d500380014018041c0c858644100010540d101c500301582c0508545005103484159030017003200c14164030170f558000300d503a0303c1d0745000c88030210900e0120040301131207051035811642a400108074a608210380d508000211000c5465564659035401c41e20200d0060054108408002c42c10102e1b101d4100fa41d07100040d50b048a032903101510408210034082da001c2400c07804106018800346480e03230340b50b83e1000d4200740100880760541d2125480d21951055030412640b42c0c9006008250040c040da03c91220001c0c411916036079102da001d001d551040b5403c5800d4003110140403100280740180008055081c0c0e00c0030300550078030b80c8100003544000700c13800d0064018000002103410030440e01c6240d500c20720140c100703400d00201c0640f40010b65000030706103c0c10640140105d40742da1103101d50110301890045003800a10011115110540070700710103180c200003518080c014411921300c600400304000704800e0f551399508800300d0042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 460918866 1250 460917616 460917623
    0xc0e0a0204150c051501080615030a11240c16060f02151803040311031e0607080604020d0f0515120309040905070503102705061321180f03 61
    0xd000824200d5440b0300350741c0f0b0ba030b80c0c8180125058525010180c401c0c40300245d00c4001d01d54040300420556004c000520314100106500400010900d41e40b0041c4412200440304d001d481c0e404500c814452151801c412281e00000b0101da807404600401d03611200384241840c05071340010030004002d8800c030b0231100b01d011a540034104e0b07200c1c15140c1120300d9802400461240c806403006146002040c0000c00003144545c240c60080607001003810300300150440103840445140501101519009c102294003401d1403400e800542d9450002400074000d40401d48511880c01005491025203584224040d0410001c3c800643c03462074104011074a02c400b0013202c54109018502d0641441d4100c03e8500388104180c540107515400403e243c400c801d440c100220b41c03615410b5450b002401550b40d02c0e1319402502c1c40030200c480d02c90550310f0801520f0050541ca03c0100002030000d8401c0562031288803800c2247d92040100c801400c1b0b0442c038101c0a207030540b0a0001030500b201104000450741d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 460920116 1250 460918866 460918889
    0x4050c0307052e110d02100f02120c1c0f050403020f1609022109030406030501090209150a02010f05011e090c0f0f030207020d08040e1b0d02180306040c0e0a0204 71
    0x41503040c1c45440112100e140144020aa150381c0301381400d10045000301904d500829a54800c88850401e0320564102d01d08294810040218810041c1d9249070303120f030105601603900c18039058500c02c032641c2c04c40f44040f0240b404541070401c0000d6004940070300c0c000e03400c035a1544070441e1030300d449040c5800010100300309220100001401c030f401402c40c0186403460b0700204801c501443c00807600446d848001d5401c0080c0c10f0001303503014401e8034090003a0003411070521400b0700114000750440f44190810b0706021a202e240d007403003508441c5110071655024020307540c1d200042d209101c2454030001001c2c601f010042400440d6100b01c3c807007207001daa900100411141000c1e0b54a60f41c5c40040c5041503020040440540c944004981c072040c41090016965071500c8101c408200004d00380802c010042c9041f07880000911049c2c0e4502c02e070b00500160380703070142c1d8030364010b509042603469014001c0798100800e020418206104480780142e041c016561807005d20403c91145000b4040b0144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 460921366 1250 460920116 460920169
    0x50a18050f2e09020304080c100603050a08091207061101140f0403080402010915081b0a0c02040203060a0e040605101502030412061113030309060f09210b04050c030705 74
    0x5440190006111400c0c00b00710301074403044040143d030300c1180c081d41c00a80c0040d409011140800c020030480d100c030581048014256528951a401142030280c000c10000c01c3c0c50b08a039503901001142561104121040995121409044042c0018642e8501d510b0301800380b040ca15004040b500c24201504100f04d5596070365415551130300d005d80700780d041103c044404901d0b130a5480505c246100541c443d0b000a1428600700b1004142104210700408400d0000004040e0401c00414107254103c4000d6160740e02c007400b01ea24050241c0c0649407200c2d200051100744201580128000e030080d4544c9100d06842c2c20306800c9a10344120000d00691040208102071031011980c046082d110b01000b00d84a03c1e40403500d40243c21901c10b04041400200c000c00c00c1540003c020310092500303007481001001b601102900203101841515454030301121044411684c8941c1c20001c15840800c45000c2e00706400c1044e56400d44002140c020300c1000008111407900005640031401840f02605210 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 460922616 1250 460921366 460921411
    0x80a110f040909060b0904300f21022d03010803070b06010e0a0b0910030e1f0b03060c03010801180b04020f030c0603240a0303020307030c0804050a18050f 68
    0x20b02c88820191140c580d01c00d9507141941d121181ca80c000c60123624402c0751101410011901119040341092030b6952407804290515001914600031031034504090103050141c180d454041d102200c01c0b2504140700044500b00100203808601c80040390030b000c0420001c1d03180364a407041c4000c0c0101e14107a402841920009481100225803104040c500240207a20607c046410580c45402c85000008040303031100584c2030125000000811701d150034082180012070b09500c07010b078070b2402c070310746156413309201c004410781080040d6407001e0100c4a0601c4d00c8030080e00e084d0030a014683c019420407620760300d1f5038002001c0d03003040b54020400f441951165420004a25901c5515503014001c6101450040d512100610302c10256081e10a8500d1045a4040140d620421b001c1d8440c0c581e054041c40801d40c0042655072640d031508103064404007609000d000b0380115442140d000b1400c0d540818290352048403801ca0310f4803040c060000d6250083c040503040002c0341c141e0300144c00c22609070030f803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 460923866 1250 460922616 460922621
    0x615030c10050d060b0702040e010507081303050f0f0a1205010f270e010c020d03090f290c07060f1404021306030f080c160605030c13080a03080a110f0409 68
    0x61001c03410060b01c0c0100300d200380c500f0341d00c540c0c1c06003a80c403002140752010b509190240c001c0003c0c6c3c0714000c104a02e04003001818114001c0c010031000b20b044071000341018000c03021100c1c2c00400c0612070352a001040620441c0f03620500d107180010300360458070120101d840c0545416a07100303498060016003020024415072800300c0400001e40580f0810349460402407080f0241c61648500104510081c9a8080c1c030784203800c16142c007050700d0010ae55010032003120070032183c5540510400c107418401d9202c4c85400036210510010307101039406006000c028240100202c0d88117031014070000d1303c800e407210220f40030120150070b14074594000500624200c1c0c100b0341001b2646400150f06512500ea15a030404003074021680b42ea80000c81c4204090104a034401017204458184040c0d420440e00034000c0c08054850707101100701040300b0008140e040300d00340c0074119080444001949a003002055598140d40c035031031480c585050390301d020b070940c021500169588840c1c9442c0c0791416010f00300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 460925116 1250 460923866 460923889
    0xe06212e1508041101050f250b0c0903060402040b0103090b130b10050d1112011503021302091509031c170601030b0d0b0901230403020601082d0c210615030c 69
    0xd1041c0104425034255034078260035604100e00c000304400408c101d2a10384440d810240c0303030100b0203106010b00f900a650010300e0591041c0d06403000704010105070016805420610f600a0112141d5803c0014003c07004040c403d405020b2003590a0980307514102c8031500c1541e014098211228103c4000490070b0112640c521038005801d04160304500c04000c1c0c01c5030003103d010080ea508a0500304150b1510f40780c019441c0750308403000c52a102d4050005992a9a4018210507118000c9200c4c00d059609206020304000c140e00700c88180d0498000050a00300e00d81c031020900030b081800700c0c0309540710b407140c44d0400c039020f007110040407165112a00c8100d4020b040308180d40d240c024960701005050b0f60002c0d00081c022060b00581000c0c0780c043e0500310160000041a4800011281074540c15503221070203401021480141504c0d0440075800c04d1044000c680d0051200d403201c42030b0886462038084019007140c01c2d641c20b1b407151008400321403a9174007001c2c0c0c99445420a100c070340c41d00100c00007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 460926366 1250 460925116 460925137
    0x100e0106110708030a0c0204060b0414090903090a0b030a0c020a02210c0d06090c0603021c090311150105100c08030a05130606150e06212e150804110105 67
    0x2d00781c41e5200030591865204d0320655001070b0900e0200411418176010310000307007514600035402d05080052001401814404031171045d03030354101042d021b40c400e00c2100c45000c00640448549038491240180a0b4020340e212545640f0b0514a030800c1032010990001103580146003924030080c3c1d14a40001810260301240c0d20301a26000c10402c0d62260500d01106119810206030055a418945418900c95000105150040040d01440c0514070421000400076080001b110185420100e400f0058100c000c2c4891003280b8114030100c8104008504130740003212518080800074408840c041104400149400801d00220704902c889402030740e4008445025074810505640340c0b1005c0d1036840d84562480791041003084500c56000307035100a0880103441152501c4510000704001c3d0020346c80301e1002c8413214002c49c5100d041420005c10f113440c0d1014500f082010500e00c02a9203140d44296405404080501e03c0000e000c1c2102d90301c01c0350841c50002030b0400020054869600420121 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 460927616 1250 460926366 460926373
    0x5070317040807030c0501140a02060705070816030309110402160b04170a0302070b0106030204081009080412080c061f0e0405070f0b030609010504151811030903030708100e010611 79
    0xb1031403402c1004244000d5006020340304d000d0b80b516001601465500c1125200079104103e40d1440580025072250080f003140f500303581d510242d00b028a014001c2ea0b0424504400400c8060706069058005220542c02800403c0009101e501000120301c116041190b0074a1002e1465020892510080d84e0283c00f42c0403c004d011603c003080342507a4001410310000ca94041418014800d00659144c0900b1150408515090809801c690b55450380f00908040d02e0311501c11000b003100b880c0580f0000c0c034074030442c0c40c00406030f442c0000700d982060024465500c07590001034504552403001c42080724031400803941c90f074180a07a01e4119a4000d0084d1007d108554000070841d8202a070a070041c840c090389203451781045c0080100780401a0b004610580c20607001c500410413061a42c800c569823907a1000d2901c15001610020b001c54040300d1003140c2022081000800010004522414003039030f5645213603955021062024080340250301c0c0118200c0018071185010302444003200450800b107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 460928866 1250 460927616 460927619
    0x1d0301020706020403050d0e0306040305030610172706331309030e150307111c0f0206010608090601030b0c09120f0c0414070c081e0a090504090507031704 68
    0x102c509030b0348954006c90f0554001c8408041c2c15a100301500c0e400b803011005001c4034149514001c001d40002f800a0b441034448882104003203000380300c8402c0340318400c0183d00f0a07152a10b001791808811a00e9a9140100800d841684c0d800c0401c2035889a0000c0480c3c0001c1c000c009011840e03c240c002c3c805e001100166950070140e07071000c1d090720808a0303103c400310382c0580d0f51800410041007402200d000d0304489841d24028034205080e1703030340700041c0d00e04024800c0091408518241154118080c204440000c031174030300750700c503907400322004050f02101c0c166643d0302c3c422244520308682d00142d0782c20903001072001809003119039070855001e140f40743c14100680c3c00540b01c002038680d00c246070b9200f101c01404c1090f090101ea000b00ca41190100a030b0b80c6507881030541c143c00141603504104110094504100d5000c040c3c40b807004e0b8413291030a4140c0e0078445003205a004814000200d8410705000425141a0150321031040e80034000e0101c8a2031661940b074440c000b05a41c0d0090b9906110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 460930116 1250 460928866 460928873
    0x5090d2901140f0f09040602030718080102130f0f0302190e0a050106031b051603180b09030709061409040311100b0f0303041a0a050f03090a021806011d03010207 71
    0x341d010740245400d0140c0c40c60408204000882602d4402c3d026501c8907018030500c4c3d8820004d141d115401c0100580d5070ba81c0c03468201c0e81620000000403101052110114051300154050030407069440c000c410200d860700c076214521002d500c1983d02e212a80042440141004215129000700d201305000c101900c44914107407109007104c0e01c0c1d506135542d000422409903d0301840c040742580c400c081e001ea4014000c0140309104c0c0448000c02c4140c00d40801040500c2902d000303600340c42c2680c10000e191340300c052072101c40c3c4c443c2d803046101e44148800451a00002e01c01c4a046072200c00100114082c070740140070760404003c00540a01c02c40012030700503428244542000840085400201160440304208142c03401489441c02a4170620052042006403030442d101d9041c40b144043e04c407400303040708a80070b10440092684215020082c480080700024041085502c22521401030100d40046815808800c88180740003600c80680d60400c031102052120141e20060009450203203540c0f0f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 460931366 1250 460930116 460930193
    0x1090b033708070204290904080903010908030702010c1707081503030408300909090102091c140a030f0c0302030c0a0c0513050103020603281d0d05090d 67
    0x50318006400120f6404500d400d10881e640c4843c0344403486820000d0952044224110241c550701400c44840440d082c405407400347d8580c8030008000b40a218414075120744542c10540344180036600f0444c0d0484218001d4440110b95101e1400d001c145030795240c000c2b60851005003402149130545c600310195510184004c2000e46481c03130041c0080c3c4400910003410000c61140c24100c85418800c1c00c40000a450031540310760000c40d0400c00c43e48410955500a1040c8207040c6c1d44034048011242c0400644003450f41968024500b20080c4a8445211a22110700041c002c00007440c480c00c0d0740304d00740541c050070303ca140207104503410300d205071103d51b10701200c2560641741c404000404000c01d1400c0b0041d5808005480f2040c40207501d103602043c2d607808090000c41c01a1402818011814103142d8550162a44440c092082c0c50251640c80f00500b104403820b003241c022626440780640c0182c08036880680058001540c4403038035104d050300d1f00c1a14411400403042c01d5868401d103c46407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 460932616 1250 460931366 460931473
    0xc0d08061c031e02030a0e01050906090d1e0b0402040612020a05041508030c0f0105070c05060103020f0f040c08010e0c04140d080c0313140a06022104050d0f0b01090b03 74
    0x180c006695a40b0101b0700030f000c05400010150401108000e4207219440c2c0c0380649003026020b4458221000d803034075041d20142d498414450b43c4042d00060401446040081540194000e55003046050f850316400c03280c0d590725200107900070f5800380080140e0f0506504c40d4101501203040a9803c0f5150f20200d030440c2e1003180d160b0f00711740c4074003054002e4910a20803103802032800d04005450503103c0d0b0307546880f030b001440003a1040103800c040c0d02403030319040100d0081240c024004c00c000503290001503d0031f039082c054090b040541400160800724a88115000e0344c0c0c01004a00000c070854007040701c07081074181c084a804009004142000a080001e084122425500003601c14141211450342407081c0600510455019404100041d004a1088158140545800318100d221100390780e40384251381c40a500851a0b41d401410b05c000000c000508a110728284c02c0d0311b90741c5a403031006035415403160582c50b4210601c6c882d44840f4250414041c08100c200c04000c2003403251001440302e040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 460933866 1250 460932616 460932677
    0x1314071503090b060607020a0e1b0c0105100f0506070609110603040f2f100201060f06090509010e1501050a030f090b070f020714060904090f03050c0d08061c03 70
    0x486034210300f00161102d00f2603012400b03441791801c0c91156000a9907184051140130003860540700800c002000000e6041159108942e58030380d01c0d075440084a0003000b048515020748509102d012821444044580d021a1001071000741441181e458800081041c0c140031200340c08150300459854494801540c8260300900c440819944d0034144001000070030b44060008107100d10300300621410240d03c590301d14405075005901c0c152110000d80c01000f068125407110908440002007075540080500141c902c151240c103510b0b40d032202045600721082d0360b080b0500c504205440410751080014100c82c028920340400c0c5c8410071551201210001c21081e96407050703190407c44910740050000c125404684002c08840d0f00d4410342c0001c401d2a41c0c0c030b41d13114030400107000c0510781c5c5507088081c040c4d4001c41140384841043c030300905250b11000c81038040740101004414140d000c0e80c3c10601c41c44002d40914900c4e480081d40200d400d000740e80c101c062010b10a0340f104c543d07213200340030b0050820 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 460935116 1250 460933866 460933871
    0xf2a090906040201110c0619020f060c04090f020711012a03020615061809060d06020301150e060a0c02011209060c110601091512140a050709050f1314071503 69
    0x2c1c18000140081034a00c0b0a1040d984410301a60003074566408980d05007540350340382c10030348600c040e00700c0c1801d01c001c010301310780e1003031105100c501500c0a00410840d8182242040105401003001e016806260409413400003418149100c5502130310400c55000402c07010303e4182c01c076040b103050b6004022001540143c3c0090108030f0340003041c00030506040003c854013810003001c1403425440262a40e500360041c3c3d000d401003042e589034040c004032101c1d4407500035512582c486c10507401202a0303000e8034001038424003c501c958100001220902902179480ba581e014140d0019a040d10f0034000b448040b84c4d5440c50078021811034800d20071426120343d1014003140780d00e0000f928140060b00724000c0b452402016803402482d05000804440c0b8503000e500740340d41030b0b05280546058031101031906000c2c1e1107c1c0d800b041808241c44c01a100903a10410039a16455442a101318003100e4004035440c8440303034031000c900103441408520600401300c60090751901c2002101e00300c5484850003294 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 460936366 1250 460935116 460935121
    0x9040e0a0f1109010b0912190308150a031502030403050d090b1819060905070305070f03050d050f0313140d052109190c050d0f050606030f2a090906 65
    0x80e060b8440307401c110450300c5281d01e50420300402218030400070f10900c070741c03803003070740c0c0303c841e00d0203015054611070003d4204a41170b4250401414540d03048078210310000070303641440d45900c1c181044400f81ca82040c0900310a40303081e09240002e5001410a505001e01841034008103813140c041e40100901c500c00b80265420300b580007444640340d0030741c4200250029608206504401040d0103101500f042c00410520080d080030b500304101a04050f0140c0581d407404141003a180000b081120f10450840360742c40440401258603025410b240c00b072540701040803e030442c0b056090101d049014481400550900442840c5410070080000300444c81c0450303840700d1450200031003065a420f144800300a031401e040d0003511190620b003003508078040038140c00300740000b030080e00b405024090f000318001c030350701d05150200c1d080c1c11038100d0703141c46446e000803041d08010a54800b040745910050046052990200c20340c411401710f0600e01800401c0c01c02815a54a91003a01500c00f40c800340c503c50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 460937616 1250 460936366 460936373
    0x22030c030918020a120605102d0c0b07110604030e13061707050102060c0703080c070c0905040210030c0804080c120f0d06081605060a1205190b010e03060c09040e0a0f 73
    0x2c200380301c03006045103461801c104036210901507600204442c50138007a14244274211046800002070303a00001c4060504005d40503070481c24501016000340e1568955580e0f08904940080300118041c1e0580c01c80b502040010f40105241124280c00406003401d0708604403890b03040f01d066910a100e4002d5009899000b0902400309001030402880a0041842c150310b8400443c81003140080801c04864000740030720040c1010f9601c02d5501c9000302e4405550340035158003038201920180d03c80c4507041081030005019110344960841c840d2508000d83d641c07034640c9515900103d802c00c405010792030801d0089116100200182d0018480c1c0684600e0340d840034008a8009410140f8158401149501800e140711464000c6239400c0341d1880d0758440340d6000325070f4403030702074290380700c8031700705801d001d81c001071112034002610114408100d100d082600440c0c10b001291006d5816410840103e4902c25100008000b5103c015101060300640b02c12a28548013140b40b05846900030b250480041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 460938866 1250 460937616 460937627
    0x103090b0a06050a1d011509080a060506090a140403120b040c0503010e0a060b040b0c030d0914010b03061303031d030c0703110a031e17040803040302010822030c030918020a 76
    0x10303217120000c00803540c4800d8804910300c04180100403039800c01c0c400141c40c4a1249107600d000d401a101910750041c540d2070071001900060f2a0580300b1820032000408003251441084c6000707135000504140c94940b40c909841c142c25a022007500d8a450300280410340c2c8403802101c1c010545a076625640c2e6140081240d09014040c0c00740100700d0030a04100249801d86041d41c0644564203456030791522111021841c500c1000c1c2c802c1a60341c00c1c07912203070510454070303034205c0c84884c08802406840d0301c0c17004040c4c803580304460b01008400c1282428011a121b80c0c440c603d406401d1010503502c1c052240003d156806c88104441181e2015106200f0400142c0994401920540350405003506541c2c982091403014592710803025580e00f4110103219469003480a20300c0c41e010800d99458481285580343c1c1e000c1e01017a8049544180401c0001e8007202400c040b4000079803600c10300d1100b5907012251004513000607400c103d000b000100d40d00600d40e005007541350400900582c0c496540101408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 460940116 1250 460938866 460938869
    0x27020f060703020705150d0615020c010f09090911031e07060f050a080919080d1103011214071503021b0309031b04110d022d040905060103090b0a06050a 67
    0x2500d003070280800082d00000c0040941d5400c0b03032100f10400110315031084501450203000c0b05581407000004a640b04a0500e00c982040e03a030030358141865190054407070f40e03d2007809034001005214104a4800503500400304580314890381c0c080302b40021700081c0b030a015184030081b0b100403810684000c0c04100024401004141400001101a6400a0001d004150801c014001d041c400503010003014020800b5440000e448620400840d0920780c4c1640c100b02804140a46404003908401c00e0f05020b41b812188105d4a64419960550303d82003002207507800d4911a2140704004203480320005e0b00b100c1041400e43d401a2030f100c00880c4100d452600c010403030583d800801c08038803592000b24650305015000c500d01441004108045001810282e80c0c0140f4002d010410025100d0141c0052145816030002c0400c1c1811840c880309091001e42d401c80f0084004210410040510785c100c507600c64014100000c480000d519064621002203482c500d440d56100fa05010790b1410b0300e2102e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 460941366 1250 460940116 460940119
    0x70227010f0e04020114040801180b0a060f0911120114100c020d1101110a050601081b0102030a110312400201110712050d020118080301060c030327020f 67
    0x425881c1001081c1280d0b00a40b0281c10800c4020f0312000061928048030014400c500007003000e40554130b1040100b11000c0c00489106120300041204140c10780201001d0342c0900d5101c2400ca40b500e55600004c1010300d04010300e010b000e0016010328540355000500034925001880d0341212040d04201001c0780e400c0c0039000303108000d20b0250141c0c490314502400030354002c4025004410090042e20b8080100755002d07020b00c0b91540d910100704020800328104c0705144110b0b9000010401019030041c480d2801d0790041e13205108108040d0b01c1090210303840440d2500741e17031402c1c0d10b000a050716128202c401e00310200f230010380400a094140c60030010040010390007105c0c2d00302911701c480b01004665010341006204000994014002e0020a008000096141c40c582d801c034946aa210074440180301c000d5482c029258100c81ca06032252405c00b0b6008028514507802e1110a441c507401c000c4099003015900e0448487d00242c45801140f050804401e5107803021a51040001001600742601d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 460942616 1250 460941366 460941389
    0x207060315060c020d06020f271c170406030902012309040e1c0305061908100c0e10030b03070501051204020409050f0313050108061e06090607022701 66
    0x201503075001c1c0d90701c8070709584071442c294050840760f000103002c00800c80000381080d480001c40c2809014050000d24480c0038841041c002110660301c643d8544880900e40c40e08440910388015240d5500d460f15044a0300c140042d8191002000b60201c0c03540140d000f26010039a61640034045d50b8016003085000110208506580201444505000d0080003592405030342c5071040d2607081542070010320440d069000c6080d207405e0308810003d02400781074a000e030056007820180f2425021090581c2d0640b0400710082a00c07009483c0b000000302000b100c0c01e410040190041c03407695640d480150001c8489039030100320309141104050070f11006620940c1801400c115940100b2103079808140d10580485001940404504007107050648400c002c9056000005050207000c0f44204284207441003aa00c10555a60380e07400d00c00041d0101c11920040c01e0b17102427200342850240f00a0502240103800d030303401d08401d07a000c12060f400300280300300450901211070242c0031480d40c0490042c2402000c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 460943866 1250 460942616 460942631
    0x9030f0815030a1202010b0303070b18060c2a0d020a0302070503031c020a0201060f0e090c04020a0509090c09030f071505040509070e06120112050d0315170f0609030a02070603 77
    0xf60703114001c0fa0010010008400c1c0b50038464000c0d0312201d440300015058a90b1075115161411207800100c500c5084145590340c4608046000155a40300d640314444541c500038009500d10385800d10341d01404c803c1c40a582d40c1400304003040c0001c4041c542e2680050180f6009450040d0508119403c820f0081d8001c0c0a08030413900b0f21807140703810040d080001642d890402400724090320329038104200c0c0c86100000000d1202100d0030440c8100542010b0300c12520b281d90801085c0e1144075610380020f0002d2100502d01e14180582540050101001d14601410700300400e042030003050240c0d0342c5070080d0340304020582003280381c04080b100034a4010b15085c1000c000075210740000c0c01d56820001c900c40c03801030642382c40d802c40380d01480c4800c904588e503035910580e002821003158100c419014262103601c8590081c01803900d4170b1514890784c0d00960500d4400c202c3c5010419441e6500d10440318a0031000300284000390180300c0e2240995039072040180041d1508a0f607511040800d85403107075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 460945116 1250 460943866 460943869
    0x1d030c0f1b04020c0304080d021c0c1502181507031806080106050d09020d061a010e030705040c03110c01050103021017010b0d022b0b040501051503091009030f0815 72
    0xc410075250402c9400503120a0000344c4586980902d811103070203841450f006c1d0308500d400007808099645280843ca403080c1c010181155411456500105001800e8042c80700521094028054404100c141007100e08100000078031801d0f020061403c10040000b140d80515902c0741d080491031031501d84001c011403821038010031002d0f0501ca8002000707404182c1d000343c3c0c80103400400d14190000d01e01500c8002d04e00f868001024403e01c0d407040c10341d4521040c1481e5004e4020113070403000003000b40050314602001d101c003a1048540901c201507403002100c8000c1400b101074aa041c014000002e00c940c10b510500800d600510b040c00c00f0310601800c242c00003502c0401250540380c0c20303d0499210307d03140005001900441701c1e10154114600071001128a0b0228040141d00f03001109100c807100383c906010494000380a500d81041c00722003840c1d02440383d6002507402210030811903140c40c03070110711030040300c640e4602140041c807040501007180d68030001030f64211034460900300000c0d61120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 460946366 1250 460945116 460945153
    0x31009050c09270703020a0f0201150314030706060801020702040e120d11070209070809010501090902031005061206100302130c1d150a03060f17060103030c061d030c0f 74
    0xc801034450b80c0780e0100c0000c580e41684920000308040400010f081c100041d000c1e000e50040440c0100042c040d81d16491190310501408080e6000d0440c80c041c03240c1036132618070900d41d1b9030044520522081000800081c464403910004090342130006031a035240b881040262143e025241245d9400400c12944102c1c4140446450b442000d01c00281a800250031140d1070082c3c07074000e036016505004002c400c036004210701e80710b042c1c4403000f0440c5a88810395242250b85c17071100030750540d0042d010700d501c007030080d40301c0c542140006040d000c98001640f90385180c03220442d007498a60030b040004204500740101210450a0056002e00c01094541d400401d4060040c806c400c040b4802450080340346c84010303608030f561854441059880f444818040d019141ca4407030b0f00c200484207980040e901203140d18508000200201170442039103551070888600d000317001d050703a00070f6580304407645100b45e4210038640c0c064106d000d1501e402071040e0241c1407865100c00401703540c0100031126070324015003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 460947616 1250 460946366 460946377
    0x50403060f112b09052b02071e0f06021f02030c0f030a1103090d120207120f03020c0303040c0303120b0609150d240801020a08010501050918010b031009050c 69
    0x40d40c40f040480c5880310400d90180d5203422107a4a146403a01c2141481004101c1c008100311501d0041644440100c0e03410316880d41002007001030300900c0003403018010031200141c0c0040303038201e608d1415848400500c140c4180c3e5102001581c08112070f400040ea00007942030b41450142011811441c10f5104102c00d0320500890720b660410000005070702007172070b6000307a0381c210440d902c041e280c6c64a58810355030392150324898000700300340804090a280160017203e8070380da03100c1440250801c44803019a1560700c0040d0308001d15400f44552044918100003851081d40a2f400041e41d1a10310705003c0e24041081004d07458250810b10401d0154031004d0485071001000c1d9800303c0d80e164510401c0c0c40c14001c0301111112541040301c0741840c0b030140501e05210b049041c2d8040b021550b50301042d4200c0c42046080c0000c03a200030010846580590040e1506020140645103100c85150080c0d040d404240c202208100000c418002c10f0001040140c01a03c1008001c2000b42041000006507020f030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 460948866 1250 460947616 460947637
    0x20d030c02151f051f030c020a060e0c130e0a0308280501081501120206030a09060e0703050c0a12080d06081203061306050906010c0302010219050403060f11 69
    0x1100c14228005108111845181850b03820304440d40c24520001e031407103058602280700c03c07500460046214500007185041407664a40848130081c6401405e50207800622088001d5005140350b0780045140c6000d8440380b040008081c040d9a885001041018004030038217841207454030100a109030b400095003d140ba40500300b882c059601e46924426034a81d504041c4100c0710a400000b5200c1041d4000a040c0e92030302040d1205010f26407042c1d0111502482002030079446095030f080907050442c0107503040310010728081218400c2d521000151070300c0680094642d42f0030001042440303400c2c00400c854040444035404500c0c94680b43c401c40302d84501024081c1c184c0080e401c0e0b200c0ea000c0d4804002082007a0548014861a1a60f280c041c1c10840d4624069081d00f4a04020003203d0700c039450944000420502950311150011900ca000307141c4200d080d903508100408028010031002225804140c7e00c2a540d542549408015141085244490541050300380c1c500c02050009031290b01c2d29 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 460950116 1250 460948866 460948871
    0x1519030f0b030d05030f07080f040f0807080a020d140310050613080d09030b1012030503060f1207050a08060f041e02060f041502060c0a0509030c0a08012406020d03 72
    0x180c003000c1401003211889850b0705110b0804610042d64200c00a90312881d8070190010b0184d13141003003139904101c1180e06c5c0103401613201c0010300288048104d009045d0180780100d0412120790b071982c80310b620030401c80f00035030312070a6a40d151075400843c840e0301003207515036141503042880c070070451504d0f58002e107441000c0200d4044c0b030120200c1c00c0e04c0c0c001c00f4008111901040040009060b510043c00f080d1070107142d0f400002c4400c00c90030295401c41d64010074550208109803412940d50700050980c59100700c4402d00301034103644103c441440d554540003c0d00d000c43c940020400b039a09168054035081d00808100517080340b02c0382017a60f205821a40c100059a00c0004144002d0f0040000a501620200d02450101d144030b014006032003006944000c89241480280d030741e448103e0b00d01d000000308201e03200480d84120090000c000e806400c4410144c10000000c08007031107a00218070340da5403070104210a000c01c850101e5000c80e2800039580490500000945420b0b96803100c109254 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 460951366 1250 460950116 460950131
    0xf01021c020c04050c0909180c040203041a010602010204150e0a06081003080d0f0b061219020720040605180601140c0a0507031203110d0b040e030711151903 69
    0x303009000104520400030f0007044145010703125141980c01000c107103401440d00030000b81c020980102d41d0302189507804028561103100c1c00411000c1c0d80000d0045030071481c4034009601080c6010219070107030803540c00258a450a010404c10a020b08002d65420041d03841c014545948030300c812075098800d00d1902c01a0350303070f840c50245008122035200408030f500026007861050029480311450141d980414801c8201070410070166000e691080d558500958001c9202c0b002e440c84104250304e9030400241c1800d2403502d801d6000034400c0c601a401d10013003031905101c0d2626108600184c0130842d00c016081005900a05004800400250502c0840740d0010803044245050700d08024800d8111409444a894901d0b200c010741d100403105600f02c0c0c40d0140c4054083c0c01168825840341c0c03001400d090507544554094058180800c0d042507803150f0b040071814050000701250341c024882d05284503010300c10300c0b03042c100c544000075a0b03c1091152a6128a00d103405030310076070b6145001328401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 460952616 1250 460951366 460951423
    0xa08090c0a050f130b0d0f030f09150809011803020102040e10060c0803250f030c09060c170c0d111203041a04020a1e03050105060f180903070609060501140f0102 71
    0x749182c60a041c0d0096200d08007400301725940c503c44540a2081d80e27a42c803001d02003e0240e0b07403a9014091400e200c00702e6401124100d205260ba154000076403030011910029210480c034080c1041c800560042c4d40000c0c003030042c80d104500c000d8101005007004c4a42c2c500d4204020310126500c24000d16000000010503080c11041c26014500d9114064280a80b04501da018055903444a0500003090600000b1040103025803c0c4208a0355281c94400300003007d0303694200d4408030f1018040c4803003030500402081502c02c001d0380366144030384d803a0f202240301e071001114500364141c3d13885150700c1c1c030810400c00000d2001801420003001c81610300a140c0703884c4001001c0f00e14070307045900900520305800c03404082c0502100102ea0140e0020011a00d40d44248000e244900720300300c0d00010403003624031200818007c85544100c0e1401030f24201040384d61604140c80503035600740c9490307440e140140b0070450300c400746582c1d000d801c07a40c5140c50651000080d407280250405200800f40081815121 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 460953866 1250 460952616 460952621
    0x3091c030c1709060f04090e0a0b06010f031b020706020708010504030c030305040206071a060a09090f0807150f0b090901050709030b060109081c0f11100b010c06020a08090c0a050f13 80
    0x1030003c01003100381c0301c00301d10360481c0303594100388103845540b410141141c5104001040c030707101194200b0b01040b086d60f0341c20010354010801c3d0040324201941d0740d0810400500d54100840e41800c15405492010301d4903100901c1e04220f908411000e07450702d000d100002e90080c0009a465505041c041010b50321800090014010300754040c00c185804815541e09041400d1803034800c41d0103e420b0703000540c80701c00000880701981e10040241d030304048200d000c00d4069020b41052b510ad208440e000640b080003c0090711708006c2982035030b42e1500d40d801410301e03002c0c4074561312074500b4000300001c2c5800b020041c0303800185d00c4003903c0c01c00c2407000301d02c00b030744100503e030003070207206084600004889040364030040881910400151080c01d0320898240b05107152101d80d900d001c02055004103008449008000316034800703050014614038800080c0050015001d001a2034035003911030b180104d142410f10341c00c10f400c284600c4401c03509000f15130b034024180804c2d070016142c02102c1712107550100300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 460955116 1250 460953866 460953877
    0x6030b0a03082101090b030312151e1011060a0b19140a0906030f080d0605090421020303090307060203040204060905010314070503150105010305090a0c0803091c030c17 74
    0xc55035000450a4401c000c03444204040a418103820324641e0380e6401c0380f41142c5200705101d0381500100844540d504801600304cae013181403510540100b040c5070000402d03c50141140340444418404501031034a49200d08006010300317803e11092243c5421040d94550000502c09500c5030f80c1c45c20003c1c107645a00301050141c154070050440c06039155180313220380c86501c11125104254214020803450107500444084984c01602407500199503912840da80e000795100b0360849545983c0000d07203a48625055029500520021009000c500242c0450f515014882c100b590300800074070135584000800c446005422480050b1292250300c001400303841c4990004000d28103120011007482a820341c24030001c04c01c10f08440700302c1d275540145922003444002041c61044500010003142d40079401160348042224142c80252825030740e20442c1c502c07150840005540041450b00f0b00b41000ea40b204030846130601c9191801d5a81d82c2c00810344494441c0090400312240d40701846800b006013542c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 460956366 1250 460955116 460955123
    0x90913050f0105070513050406080a151104062c030717010f020c010606110105040b0402040513121119050d05090303040801090f02011706131e06090c090510050406030b0a03 76
    0x11407418019130080142e007181ca250309510401c0800004c5038a00382c03107288220f80001c0302425414140d070302c50706076410540a5084030701c0c1e1074131900d0101101c500d00400103440380e501d4481d1007010381c04004441c41143d10303d5540300349082000d00b030a60350008100741103490382c0c030324440364540030a1510b0240c14004040360446001282d14072841c41d06401000a440d10b0755603151312116608a21030988a040d00e020b0500c00e503100c04100076003090b410155000340758078840501000580c0d500e41161251100480000d00c0d02c5010b40c3c60780d1030074082d00360007040c07031030304c0c58034401032070300e62036101d290b59411907062001c0081c60401035101801510010401390313008000e50301990506031003046014504034001201c8100e00340c041d4203441900e9000311005454041100306c000e6402e03000f4492505101e0701c9a161200d0004c000c2e6a901504028000d00040440c41d18901100034041c0750840d0850b0741f00740a0210314080c081d034048261002c4070440d1901050016210004c205104a40d41014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 460957616 1250 460956366 460956371
    0xb0a030204080f0309121926030f0402040509010905120c0a2406090504050c0103050c04050d061a12030a1d0409140c060f0a03051e160e0402090913050f01 68
    0x455503e00101c060480c40400ba03c1030a000c401400d800c0b41c441c115101d4038000b1502445168010956200201c00301d140b250050300303c0c42269000742441c80e003040f14200301b95600d41041100b141018000c0d00e030443c00b446d000f4401541e0965440d41c03070b0a80140c80d0400300401090031388a00100f000048000d64008487d0242c0c403201031a1203105048103211440c1890070060005402c414034410584660307080400740250300c88140046010b014094100a000f51051102040f25515034214205441c4079910001d0304401103a8030f480101c1a80350068490440e448010016400c08021281d004009150014440c04051881c46250445d1400690013070316040e030120400032040c0c90303c10704440e400d044503841500e00d0200519803040c03080c04183c1a000f8450344800d24000d802c03c030f0f04003c40301a014282d82100351b00c031552003c2160341451400d24484020009134002d04d801c1c115520a481c2549484003200206000c02009020584174854107056841030100034003100c444800d43c84000e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 460958866 1250 460957616 460957633
    0x5011d040912020d020c150310180c120b090115020709020a09050f0d03090b0c0304240f05090303040e06030c03010e010c11010e19080f030412030b09100b0a03020408 73
    0x55500d00003800002c0015104040076282400d0000034446500200144100b0102c0030f65502049035420280c41202d1a5515003804100d03c41c4900c02085201410900000c802003140c01c0100510311000c42101114908035103106039445400d07100d41502c881d030340a0700c070304084a00224030744182a0300640300d2900c04500a00c1050707000e00108201d0701d08941e1403141d540c240003000b4180c10720b1000103000c580c44282c1000082c0740380018161040c58402030302d0805035142c0c10401d210044402d403442d0440c0f0010741d11000c075085544487d07965040d00d003081c100940780c8046036891160340510095200018001001c0b560100400840341d603016000380702c101c9044621070b0203070400d0400344001c580b51124140c2c1d1a28140b141011404a0f43c0c0100142c14910f51880541c3d100f60f44269249001003200c506d00c4920b00000707501440c0300d4018a0310081025500504840202803070500c5841c4c2501846980740940c421841907404980800781e4480e440141940280314680c04003039140500344a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 460960116 1250 460958866 460958873
    0x9080a06200a120501080606090f0a11070c0f0e04030207060309080d0f090606051816140f0a1812030e0a05030a08190507031704030c06050c0c010c050c0705011d0409 73
    0x1014050700f071401c02c0c8016600d80b03841645400c0c003154010381000a500008904000040807aa0407000050000400910045503a001903201c03690030703103548024000821100c0013101520b0b008042c2060301c2d40c0c040c200350390000d440e842c13144515410551211040820302030b00b0011074101d4003821a00f00411110120307881d001d00001d00f01a9a80361030b00c000007815040c01c3d9004c031840003502144643c43d0752900f43c08103000100800041c20083d810290301c0351000c00800814025043c101c0d43d545412920324001c201007810005590b00b074010304001c011140c51010b0000d10150305003420381c0300c1103840022403a400c2d007651010303516105001c220700901802c00001c0112806460950020f141007000964141c8a202001000580c007400e0394090010068101d81c1c22a120f8540412001c0041c0c0f030700019101d040e0380202c0c0381880003c000d00740078000d01c074070f402d044114200a405c01350300c3c1180c0360b26024203124082c1406920009540740c101628000e00380b10324000c0081104903440d04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 460961366 1250 460960116 460960127
    0x40c050d05041b06030c021005010f0506030a0b21010c05040b0703030c210f051302030316060e030a090e07080c0301050f210a170c07060e0409020405151009080a06200a 74
    0x300c0440c003501035071114200c0248c590080304d06941a144209070f1251501d410300000e130303100901b2140103a40d914024622580c5e08a040741e021000d110000000d824946012130855213050201420b0002c200030412074118610306450120b41c050400140c600c038500d84c01c2e55513100e0480361001c00380030f45a441804420030350143c1c0c58510758090400c800d9450035001c04503041803040c0654503a10034441c00c42e4118004800754001c600c504030100d849001c2003110381c40c5801c04001c8801103040c441051201c55000249140d007e5564500004181408a01801e079444103008090040003001c800145a859802c64080e0026481407502d139011301ca0100030b0f490340d43e0701d94100c4030820f078000010101103400082e40c204020076000b4011301e1b0f180941c207035202c0c0040c0c0e4019070070035101d0b100c1e040540e5451040501c00d00349022223061904d100c90401c10b11040c110071840502a00b00420700548800042d19010a0307030040c00003400d0382c490601175005030710b480c40c0c01c490b111000a170940c005a000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 460962616 1250 460961366 460961381
    0x60510090c08180f2a04020702060f09030a06060807050f010e360408040609060f0e1e03030a02060103110a06020604021c0b01060201022106060711120d05070b0105040c050d05041b0603 81
    0x280e82d020091917004104003d0b84030746031002c0d50080007408a1103044049a00400b0041e80c0141292030610065a6030000e440c41940300190070703000700300100518289400e070100c24184c24a410125141003000144282298680c03180e1380c240940000450080440911060309500103000c101c240380600d002c0101e94071a0040500040207400009445400313100012641c03402500c4005025042d00c1c140841291b1a09810f03401c4034250026452640b0300b03000510886405501902e01c56065091015004004e40320b1540240e000784000c11030542c0c0800d503240c000d54100c490700c0036822007082d0069980d0381054080c045c03003040c800014489070158010510340038000e48004000d5040b155819070078100f2941306410403800c00800c0002103001800003545140280a0301282440e04403040c50040135440d00400300358002060814071140440145c01818121028003001426800051490080c040719060060715440030404210042d405401c0020f501d5020108282da2440010003a1014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 460963866 1250 460962616 460962673
    0xf1403090301020d023a020309010204210303050c0c12091f0c03080901060b0a03090203070e070306050915012f0a0b040b1e06150412060510090c08180f 67
    0xc06c91003101c501d060f1000550038014420744541c3c2924864104065403004080000b555402c220201e10007101120080841d280c0405107110320f400c9203405003c4840160251251140c1403160100b003400020340351020805a03d100c43e19500e07504081602a0b024075482c1c0303034441c21041031581603a40f02c46643d50340c034020b580311860f603100d40901c00e0880d031f518000d122801340e080103d00101070103034000740505803014044400c8140d88020f2203183c4a800d40b940c000294890604206034640320306691f40000b00380780038040c03100c003090010b402c052400700300741c8600b0300c6140702031030000000950049105200e0260b50504840c2d1918818000f000c070740840315103d03000045603094000710101c1c907110000051444482d1145800c000703003d90f141c003000340e400780200070100c1d1030200001c41c00340051040501041c00d040c07200d04a00107801681281c0701542c5451a1514903551140810f030304541c01c1604020b0703241c24110000c0c2000c5c40840c0c01a581c1c403404812a51000705030820304600f421 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 460965116 1250 460963866 460963897
    0x1e0402031f120309150e0a060206060f03070506040e040c15020709050f04020d150e0f01050601032702010c0c0302091f0f1d22050709050105040203040f1403090301020d02 75
    0x8440c10714000c00b55034818003500151543d0b1007400003003080306000c08105460706201400d05c90100000e0010000741e00804010380000e81800301c58105070041e80110502100500402420304000c02c50500451117529400c900c0b41c8003207403e000d0400322000103007240445a40c005400303110007030755402c000d2144100107850400040e00c1903403444000ca01459000f024017080051603111102502050b60b080580a980c607403081c01d070800c0411209612203481c00000c42c00d4a001130014088405074000340c6800ca07038202295209895091100c100160b0909006420b0b800300c2c14002c0031030030107030002900016842c00b403100f040200c03070402c040034240c005c1d100c401d5034851140318036500291052100d444800380111890141039030846138411001e41c41200d212005105001112501d16003e076110741100f02c0a0058002d1402550b000d0700050b2010351440c10603a449810000d010342c8081c00341140c2d1244401c08001c14030840d40d80e100001e00943d224004415190029440f680d00d1100c4080c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 460966366 1250 460965116 460965119
    0x30201060e06041a0904080d18020f030601030308190902041a090c0f04090e03070507030b101a09130f050c120609040305030c160807030f02010f0510051e0402031f 72
    0x1a180c0a040d1081c11110401c1314865011800d02c9140100588200c030821421301600a2014040c4034846145481090b0080391500c1c90050014090425007414001c3c0c11a8005001281e0400c2d000c80d004074820080200c2007440142043c0144140d11000354040e081911340003924018030440b2010820841d00d020481d152041c5070300b4207202d521040040e04c1c20070710042042003040c1c1d000c41c0703007001800262440d001055640500744901030f041128031804d05c8040c440740c946c040c07100c50b014006440d510b4031684129250004d560103120440d511500b06010340014450860b04032130324180c80ca4400707000d6030078285c03070041094109040e00f9001d08041000a6828541101818090ba40540300d4614548404584420646c0107119404c1c0c030a01c80c11340440060400001000c5107406655001500403007481d00900b0342e0034042000c12038a04020500c0160700d400307a02e6108030b5008980c0c650103d059000c0c0c10705811040d00d55554414804020843c0e242e2110f811000301e115100204482203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 460967616 1250 460966366 460966369
    0x702010c0908061b090306040521090a0b09041409060129041a12010311100806030c010f020c0301090c1401020a15020304020f0405040f030801080d1d0d0f030201060e06 74
    0x241d018402d0301d82942c069000b1800700b850198003030140d09000c6880078070740301c0d050380480c0c90600291000c85469000000c808943c0c0c45942e550002103d480354041e1800d403c541c00143d4090590180c0000ca40000418010641e00c1d41c4c0004000d00c0343c11200c3c0150710700307080742c144c85040903c508282003940500da0910403030791b0705002004101140070700741094204586804803e07070796005104080410454644c1a080c5100014002e500c20f403a0301c00c1022007a0140b0050b0314058981c81c040c080040b05200103942c001c60205d0704a2720a290008031400c07210b6080f0b00c1e0218404106404d035182c00c03510014040c54000304001c1d40c108960407054200641e004981d0752110a802500100302c0424501d1205283d800a54101d40002c08001aa503907c80000b400c50f1010f031411100d28030090a07550402d50051840c0d4014841080640105c28442e013001c0d160921210854501c1144c05c980c9120580e0340d4940c9685045c0c124803ca6800b0f0800e140281c000d28041c0145015104a9400610079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 460968866 1250 460967616 460967627
    0xb0111070f150c05060a0f1a0916051e0705070602030301060f0c05070e0708040b0601110a0201080604061a130b04030807240f0212010801020705061315050f0702010c 73
    0x8440c02003041c80c0c8298039003522507615103032244900b41003051401c10304010460030050140524412400081c025810721349a108842d0700c0f10390170105000c1c0188c410050342c1c441c0c0b2043e5201d14901c2404114100240c1e0485041c0f00d641034559000030340151a15803120fa100180004600c02c2045a48158827010160703034a01091181900050414403103c84c0700303104900d1408821301c900103c13141a43c8600050b50003403c2100d2000c0058600c804200c01e01600038055600319a007030038213105820500c100c0d582c4900070008003034184040c1001184041d107a591158000708801010348201c000300590400e6941d01c200c8007900304c4000c5400104200064004460850b940300d030100c0e18040065076a01c001c5480c40860100d030320342402510704541454050443d0342c0b2028880140d5666041a84003402901a0404061a8814800303900081c90000d984c5070000010855118110381034a404c0d1a044862103c100c880c5081205020521061120311801914550000d003e1410000406c40382e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 460970116 1250 460968866 460968869
    0x405030f0a0209060d0f05010c05250816080c0d050306030d0801050306360c011b02060702040e12191106070f050a03110f09040c08010807091e050a0b011107 69
    0x1800f51211000c03444914080c000710400a1040143d0a0b04402c1c42c0c681c14210b0b4510070b0203102044000500030349011070b0b24210b890042a0071042203241a80780c5402e1500d01629040002c0f00f4500d0400d401404487d800303803400752142c0c0040354007007140c20000811580050312901d003c1d11842d90f48200040c010b44034517050310b0303014005080b9035541031001c0440303003200c507401a840704044020050358610380c11040f220461403001400203001e01c1b000107080391440100100e81d400790109200050751000102c0c0c04840e01107501040076940d5038000380c01e00c590a100104859030020341d48240d55000302d031341040d1848075107034005200740f406491916868111540b10010f00b0702101c0c0d80136140640c1c0038100f02041c80ca40014103031844400c00c80143d0054010455034400410b03206090314003801003c0c0f00200034034191a055250413503665840816002c0d1414890302c607000c030204404005041e081e5030202035420700850403e88004c100030201c01041d00e00003104070b0b04e2200b01000c0080d13100c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 460971223 1107 460970116 460970119
    0x27050a330e041e1a12030903060112060209031b090106140a080702120408100b011103160614010b07030f0302031e06120601080d081303080a050a0b06030a020405030f0a02 75
    0x160001031501050b22940c0700704210b442c1f030b07180400d2450454801c0000411811007501c1c000c0064000c40c80c0d01d40c0c1601ca141c0d0140002d0a2441e104c8803117a2056030102c40341d90721050100c601040b04403450010407810840c2010b06841078010079031013030759403040d20701032480e40c2d00030402580310381d001c1302c1c5d141d0040440343c100742014403600618030390034200500e11004d0707080d10715101d019440c454204c5081004034103062044940090100050320144a945582c442004e000544c201c41000e80c00a9480c50008034804e0091088902900c0a5554003407010300c844602c02c0340704e1006010301c1d00501c4114003e4000e8078200326450107803841f00d000e0420741007191300003403203661700415420107202d1204034100800d4205c002140c1000e021080400d660f501e104008002c3c048902980e034120b00004108a80140140d0250003034580880a0f0350805060f00798450317a40d5191100603 = true := by decide +kernel

theorem cover : BRFrame.Cov 460791366 460971223 := by
  have h0 := BRFrame.cov_init 460791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 460791366 ≤ n) (h2 : n < 460971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
