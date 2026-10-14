-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3242
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:54.943371+00:00
-- url     : https://prove2.me/submissions/9a8a7afc-8a4d-40bb-a167-276dcd852a46

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 582913669 ≤ n < 583093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 582914919 1250 582913669 582913699
    0x702010902090f0103051b030304090e070905150a090e0d08091507090914130b070c060207051f0507080a050603072301020c0d0f0303090f02120106050f0319020d02 72
    0x20a1449540c1c2090f004900d50304502d0074a0400c2509401d8881c5904104122a0586c0d000b2080c0c5042d1040c03200f00048200b0307028091440e01d0b19980c41480e19030300e08814080d000600320701080e98102d0558001c40b0941c5d44200c44400c441d1a4004409076400c0103140030710061203261016004035806044603602e0f040032102c0c80c03190f8015a00503010640419082040380703c00d0148100007840301003001e44916042c4d007141001644614010840c110b82400150341e2801500e91056039034009004544403441e611705113946d0103010104100d084404445410010414040c107841851150388a942c0c4d5150200d0001c05084058401d6a15000300107011800f0102e18400071b1a5109050303501c2e00c0a41000006401c0107800b02c0940c0c01403090130f5419010420390790381084002c0d41031500083c140c1450410104081180780001e50000340030f17110040300c41054004d00e05965080b6188643c0d41c01c20410180d03035440807110684090000391207800585060030441c8a0a070025080483e050900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 582916169 1250 582914919 582914929
    0x3010b072906030118050309040f060b03011401120b010c0212030405150304061803050415050405040c02030309101e0e1e060114040501030b0a020702040b060a0306060e030309180702010902 83
    0x101c103440c21403600c1820010549824003e80340e15010f00c0d803d2003d010b030141c0b1144d440b44104409240101c1d142c468150031854658071a01c01448034003019500d03961100703280307241000a00d030303900e0000d07500c0005580e0041e03d910070300d41182c0c4161910a84000144d003407100b48044c03003034986414081400009040e840e03080703100202d1000c26044640d24509480c20b0707400c94100c0d81400d40c102e0300780710320540026041811282990180d9003070001803422980222142d100d6a005143c22508000400414580000c05540520007540c1036401c44c00429071920221070b115482000c0c04410750720507071071400d16584210f00e1040c4220541e2210700d100c49420510b030000250842c00c80e800b00b4010848c00601d8000c1d20316210048800f03201a51542e228074407102c00191103150323002d6001030210119525940020390003900507080b00e4030354040010240040441d842220040341e51004070700703d1460080112260b1600003020b0441c00d4519800906052900500d0341d000e540d40c030005075015940d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 582917419 1250 582916169 582916223
    0x2270a02250b071101060302131b0c0503090f0a0f03050a1a0c07021c02040509061605070803073c1b05150a0f06090c0e100503010b07 59
    0x82600965200c40d54050100821405400d04651034210a140d00014103805049a080105840c104003050564610b4500521990340b0007980710358109903164104040e80c00c10700c1400e515040c82078a480803414155a200b8560500030b000340c204100d40d25491074010f4542e44400005015510213036200d0550350b0814056400a0702c140e408200c6001c00c105406980b0319032901d00a000c22030a00345580d20100ca0702030700318024403880310300c0f014030307900004a1200000c20b60001e10600c001e080421250340c8412055600c038074010000d038950105a8024000c980001d5800780c1000c2c65503689220448910701c000b0540c0c8c0500305903c40400402480e098845c040c08100d0411500714048076001400c00340e40c0c0c128445040b01c4411032040820b8000c5501c2c0407409d60900c403000c055071174040c03890050050790800510145015400b25000095501190130320140b92150368891b64840208652110b042000700000342c1c0810061080506140140040e43c0c0729101c22650040364a81201c40001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 582918669 1250 582917419 582917431
    0x27010620100204051f05040902090d2f06070f0605070c0c171504200102010e1005010e06030303040b070e0d0602040605070606050a060903060b061303031101060b0310030227 76
    0xc0c000c14280f00c1c030702d00311191202e01039848282041d07011707040c5d001920600031485004081a0301088040381503d030049811041c6074000c1c0201c106541800c40c1805003001c0d05000c940141d540710300b10056040100c121181681c02c001c800305100495030f03444d005000000c2085042082ca04e8441c40000d090001250141400c0410201c040080c500e8151030080744001e0001003402440920001c00d80300300b21425410742c4c1801d0500c10080c500010303805004030700e211700450312030610700e0380d80303c040d07644000e0683c0c600c8285004142c07160000c2554a003c00d48001c0e0012502201259005020f07000342c0760102c10180c60400000820b882e040101d8005905c00c50100f50b0020300002044440d1040b400508821585421340c3c50810b5001070103c805400b00600f803c1d940c0b4001c0c0d0300c5954038000e0b15003505020104020281d1039260003461f06003004846082c940c03e1140115910840702d080d6407268040d0069002e44a16540820000c280481820a5060b0b8449007807943d003c50903440358484c40b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 582919919 1250 582918669 582918671
    0xc0b0406080415051e0703060b03091b0301091e03090308030f0f070201110a2604050c01080a0506030a03140d0e01020c0c060301080d20060906062701062010 69
    0x2c9468201100c42040e42c00142210303e00e840304004980f16001040001980620b903508455175444405400809141d003204601010200070010340d800d000514030300c1d0703450403040f42e400609800e06050980381400001049043d4a0302048854410a0b004444150080c5420340106a481d152440aa4030683c0c0001180d4826000c1080a80c500c0f0b03502a0884c41a1000b040402c580441e108500e001c1c2c80d4102082000000e40a052022592508491114070b01000029800d061900c82d50320054041e285006c02c043c0f00000380c0144c007a2040780d11407800038000d02025a8556002c81d28541c84000070032070030800b80950b1803100007600c28814802c03503d000040e65845110300581c0341a01c2a50417501c500010801405664004268080d05c0c0701036041802070f58542000c280c00e00003042e25180c00600c00c0c4010040d8015001440c507000300d100355100c2000844500214a40d02c58841030200c2005502c8010409035128007000500340d0001003c10464803903200004d410154290075034400d407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 582921169 1250 582919919 582919921
    0x706020d09111f03180c1502010c080c03010306181b030212011e020309070b071a0109090218060105130f09060f0e0c0a05040f0b0309060c0301210c0b040608 69
    0x10525600c0403020902c2129a4142c2404002c2c68080030503000744480300701600d40320426240c50310030000070540c551050064040c59120a40c102800041a00243c010340c05e10b51440c50240c090103c1078000c851900f201c51071a801c5840c1c14020b00903141d0091269000303420031401040350f464811600304583c504050000c3d10314010003500c5010101c5c50031380c41c0d143c030716140a034002c071410115650300c00c4c0d080543c07030f0381c1c8890481e8240412940000d071111400200e907000c2141c091105081c0c1d13507075200c200405036265001441210f001c0a03001b90001c0641c1603810305001c82400c06a84820140b404a292180751200b21114550603400160078012900b81440303082994050030015200000c05040501c3c6403482c04509880060801450b01300c0001d0f280c810301d842a4101c401410240c21a44242680c03550b04991980c000c42c2c0e4481c040c000c02d0041142e04029004490407504464803c803200401d100e0758424450190904a0707040b480010006503850048010308001c00d12a1071742141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 582922419 1250 582921169 582921173
    0x30c42030b0108060d0609171b0d0327020406081f0f41010b0301060219020609060d02090a0306020a110c090115110a0809010908031312080706020d09 66
    0x25907240714140d5051000c82003c102d0f0303945030050841d61032034100030046a0001c3e51304085886280303120b078501c1c140000080040c8514000342071443c0340c466a008503440e4880301d890480403076003069a44000307221413500080c00114200d141e02c6c0c0083c001003000800c281e075180003d250a41d0f035004c5640c001c0c1d0500081c5204100c0348107027400c19401900a0111811654681c0005e100205120181400351162031049180c042c12162001c205d80324081ca07156114421101290400d00c41c107001032041c02c10312000e0b000c07031229000c0da40f07601902c030608103482c0c2d400300141a080100c10060083c4d0a1200d0b049980d14854079000541c025040142d0302c1e1b2800100401c01c46031a55914401c1c1e12030030321320038140c40b60028181103a407000d0910700c0c15156480c0440d407a6031480c42d0624070f40710b09400ca500780500f1000030031004400b603c805000c21380d01c1c810507850340541d4500c2c80c10324240360800c201b09034618408281c01031003410f40c9441c2c0501c99540c84100d0f0801d4402c941601d0340d03001c0300304c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 582923669 1250 582922419 582922421
    0x604060506060d060e271216050109060510050102010c140f071e110612011e05100906320f07170904060e09031902010e030f180406030c4203 62
    0x10030034001d000340c00b11606c040b901155603405c44011300800d08000080501008042121520095a109009200d02c948908003040171b444250758803005407941800028084d8014803035440892801e4640000c020700405050096410014400004034820065400001d00c4030704030150921845880d500b052920b8103040e40400f6005800c00c2c081d050811440c0c83d840d400303404003030444201500c4481401d4a2204000a0404552099420000011282c0300050f00210400180e52040d139803880f81d041410030b200407041103058840c0000492410302d0520a07000b40080c00c00400d0544d54a240c003580b41d542910084a06600307108490010500c1c101c94039042c06044000e22030303641220b0302401c004043d10349078847c0c64200301c0d240044594100c0780b18001c0d006140d1400d00d41051700c0d00c0c1c04848800e0605503214540c120015110b201c15102d0b1450305202c1d0b07400f1350342c00503907445541d070070010380712b250070b58100541251140d07090350702c3e5070b1051250003a070710305c0300100b0150700074418000054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 582924919 1250 582923669 582923701
    0x19031a060303070f0b0a1d0a0506071b0f140d05071406041a0a15180605030d0504051003060f061707022a0f0405070305060a0f0303020604060506060d060e 68
    0x1601c240c004000110100b84400c02130842c45401c1552080d1945450b2440c0c1c0083c035010102410300d000c081d220038501100490940d280e0f5001d407041e51002c0d640d2401c119034aa1b011a1003d0302201210111004a5000b280c1c00c640d41c1e1260520200b500368803880135180c820323040d100b0400a0000100c0d43c1c20400d11100307111000928000a15050800f541c0300c00309481a1940a14003203801400181011195008000d40b042004025009035480daa42e00540c489003135400c500e4130b421320400180a05000443c1810381c41a0b6071040d00b881d003031a00304004480c22849000400d5182c0c040400c8501a000b080c000078135803a190711004040d40c2010041132a00146044150b420842c481c8d040700560056803d80402c01114040c6140034990010b58001c4081d04415000352410042080d1250107602440c02100e040310079000b0340da036408103140401032a0100800503081840843c2c0020203940001782c010030000c02c00740c1001c21480c40d84045034200d5000d0172014017484184085082d07182c0340c070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 582926169 1250 582924919 582924931
    0x40207300503070e0d021c06050a0e0c03070603090503121003150c140a050f12040c08060c09040506040e061003120e150a18080102070b06010e0f04090219031a 70
    0x982e095192580024002e482804a0640100241c03440001199908000c40011440c2034a01c00000412402c00c0030041c0021505a48840d24044011310b400d031000480c1842014024000e002c4030f803d0050841c040c000c04507003118203110a0240c0c2c0070101da1242c002c0d1180e5040329642d10058070714185900c10321030038000103030350524050f5002c80c0b581c0d2182261418121892185903500c091400894940c0b04030062900c01c00004120b80d58001580d20f8460302440c02100c2c0b05500c651038a042039100c00090342c50702e000c0d1504000c90803140c20190080c6500190003800022400c010300116410840200e83c04641505d08072000d008010780b4001e10f00d03a00c031031741c41c001d4146c0c50b01c00045914004040420500c80c4000b143c980c171064442c1529003082c1699030400f643d1140c0d1070402c01e0107074012000403600e06560741c000401c1341d4441c130403414050b68010002c05100703c4400c14040240500c01080c1e030022500e10400c540118140c6071103004501c280e0302d03040004885240c10600600103448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 582927419 1250 582926169 582926177
    0x1b08090409170711010503011211220f1401050108071d0603090607020f0c032a06040305030a090503010b130c03060509090307061d03190c17041d2404020730 69
    0x1402060301271501c070040d180d486035060820140880002c6c0e0740000ca166a1946100080c0c3c404107070740b5644d00110103803022848144100e8443c10240e43c0c2d0070109011740c1703000804907000124401c2c8a0b540c1d40143c280307521140f245c0202c0c004e002c5207055000700d460b803025520400074001141c0c2d0400410a450302004041e00c041c44400b400242c039603110071509040c480188603803201c07650480c0301080c0c9081d80100b0080ea101e075a80b8046880e60401c401090218440480014503401e042c0038400c0710860040406503a015543d403024001c0c11340c0310003401010341d5410007042e01e49a001c0c0d058003850a80004540703074003580c41c03c2c805480c40c4250f01e401002803070b0342040c1e10382ca00200351110a1030100340e5401001c20400100c6010071001d101800c0801410303241d8103940d6198004009860188981905003d40148144503221043d1b81d00554103100e030500c00000082d1500f41040d1400c001c1c005071400485844400401c1010000ca24080040c50560440512000d009000704111410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 582928669 1250 582927419 582927421
    0x5090708070e0a0e271b090f0f06040e0c04110316022b020a120507140606030c06090d150605030105090d0f0f1b03031b1b08090409170711010503 64
    0x4c000c81400c070050010421040024409001c105400d00d0240a44035131074101c505044400004050418403100094017032032040d4041003c1c144c801c20124442d49010038450324548402040c44000d1540351a070704ac41d03006104920b217603a41c85000c2c254111a0b4949030315203904200650841c14246c0753f4191055600403203018003151148000003640316504c40d050082a900c0c01400d030704007000304100902103140360a038040040d41101c050500c1034001c0310004807600c3c0360000c140e40c6040582da5254103510100d51580300e490200c004156101c4043c1a0b490301441ca0355881c82400580500403500540b9800c040c010340c1002d104459010751150001d0421038441580903090f245121401030420041c1901c1c1400340e801483d20000c401e084514080c0d090680342001002090746110000c221204009400d000c684a00c003041c281440e48518910702080c0750352581c03c107602840070690426140d2180001140124048003031801c1c24100e40360b0b0322007851600e8100380e11601c1205042c458284 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 582929919 1250 582928669 582928679
    0xd09020f030a35030f07080a0b09040f081b010b150306090a0203060d08071406090303091216080c07060e150405061809010909051515010f050405090708070e0a 70
    0x81c1150000c0e03041421000e00310800f6410342461000070703031407070150407400400d004240903034004072407060102d80c0d544a1a0388481c5610702c01c1d610042041c9903c44a0a008540421400758410750518480c000151901090006031449090f540da10f0195a03555040f1183c1c0904150342e82e091f01120340c00710300e03103503181080c0061001407014080841c25030b40803001500340e03105c074801c400b02e035a00810f105444002503c0c0c6002030070f9446c0c003c14520300401c008929400d030000181e9000f070b0303690f0025001d00400c05000b00c03019004003000c0714000407007803010030101d204500100301030344800020b00081403d1400140032203403540e800a00494148580308014603284040d103003525411541c1c665100c40201c00407810110a14031a94080104400000c0c5d000943c1d000304119440740042d500c604042d4500060300c042c0440341a18507905d14a41030210b5071081b41401220095400e1031420282c5540105031114000c84042001c10010402d2101741504050000c000304821285441502d00f09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 582931169 1250 582929919 582929933
    0x190203060915070507031701030804090b0108070206130614101d070e010e2101020a0905011b0f08070605070905040f09030210022505061e0114061606020d09020f030a 73
    0x5020038101302010500310105441000e0072400000c5860f09010783e941c407030501c103002d94854499034031603a10b00ba202030307401e5000f40c240c01d11030074098015241aa550028100701000034a004407519a07907040c003480d035a52001e600900070b800c0204819a07442c200105200241c40c01001242e85000b508104800b0b0307640000d40d1302920b002807030140c20000320389005c910510703514600f100081d10322001c1080d0151055024012200442d503d584130180c2d110700664440113501c02d01c0c483c5d00840b0450402103a00118103402c4035200b0840b45284c0a43d03500c4010444005440200c0000d603503c008000e680342034050000c51111502042203005255a0083e558640c2c0400c210b211540101c0d0251001c592a505503a15040c1c1400020f80210f0a1515940311101210881c20701e01031a8986281c60003240e210301e0503511440350340d56030001d0001c20402d283c0c0017184445284501c4404440000f1154006443e07003840301100420355600e98410800080541109a4080e03440145510049803078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 582932419 1250 582931169 582931171
    0xf030210050d02030a090308060d02300609070e06270603010f020f120a061203080606070c1403120f0f0d0209060f0409060504021c020309070305190203060915 70
    0x10480303444a40303101400c0196218050205408040c5201004020002006801c22240b06101c0d075074500040da80c0c07400b00064041c050070040c0d00268481e9808162582d0400d0344030028a40d400031a00c10100b044820749040c1c4212610749403034112120821200ca4106e11564021800300c40303500d144082c604032031906a441081c105050002b030800f0500390345080d440311300620b82143c2d042d9654000b55500c040554040c41503108280a03035000a030030b4008a02c60102540c6107104400e00d40d44603614203c030000c40240030581e20803410042e54000500b854130200051040c0000140d80300690000c050900003886000012080c007001500c203000ca81c0000c5903806008082d5080e01d410046105a00900400c00030b0798000900250b001c1440b0789000240085600854052040544a1060105a00a0940c60703450040006100100704066402a682c070031803017403c07900c045a0f01c1d100c15181005130006034119032130051003030045d410300707102d107030b5001c06e90400414400c00c200c0ca61180c40d440c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 582933669 1250 582932419 582932423
    0x51c14060f0f0901080102040314010c0c030c080d060909050f0f06060d1e060b030d052805120c0c0c0303040e150a03080a0801060e1c030e030c030106030f050d02070f03 74
    0x41180c11100d50b0385101c880902180c01600081203981c4882e21203000754040d0101b6203100c04484018914002e05028014030016250748040d0229540e940c242e49030710342c20f0400c84401801303000e07003420340c4041d2054400800c4d200c000400c1e200207509201d418101010011105274000032406030f8003580000304541c1001c4140c1d142207002001e4207220320429421a03090002172803035500c000520031a500544001c44044064500110010005850910800e82d0704003000d6a0b0310b800421055103c850343c80b881e00381c3e0610526100804106980d0070300111047c40503101c0105200f440302d10100300d415070360707181500118030789070038801c0d04200850010401c800302c1c449032011282e16210b054032840110303804072104c1e40302d101d00b03800500120401d00900c2c00180100c400091f151801403001098200c03030b00780d110302c0b440720341d20125840007004c40e886030107100d0783d8001481c60310300348503c000850044510140700d104038a0b1550500040d40c2d2a0002c540c803052040c0502d6544140c0401101c0e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 582934919 1250 582933669 582933679
    0x50a08011809060219090f080703061e020d05011e05060706050402120d1e1716110d020627060c0706060905180d08190908070203010c051c1406 63
    0x4400050900640401c42c2e00620a43c00410719402112608048180109240e298005038030745581030840c040074284a001c11541c0700c3e03001040070803455800403131140385074804003100c521000450780c16079001003019103560781d403040100522802c9014a00c084260f0000740c18456240c200002c2c0a0701990101500c01c0c0d642d400401d04555a0120044c61411027400ba9803034100c15500140c4841036040c09070002642c00d04420070918407034442c41210310110700400700c0a4450301c0003000340704a261500c605100d4502141143d2480402118465460710390007441146804200301c0c03648080e054500018010310300e0f414400c0303c804161181c0c0594030072101078031030406040c1440500fa907940049100b910303004c01c2c40407520304482d10704071540c2c00d1001c690240c6a01c04084546540c202c40c1c08012108490f0345038220301203a0480b00c84203004840913428080107400081c215a0021162004074030001440801703400c0c80f040e15030f03030341850000400240d85080c84454241c01c1c0240014450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 582936169 1250 582934919 582934949
    0x90c0e0703062913030c0e0103031202033304050a020a260c160b04080a020f07150507080f0d0b120d020c09130c080d030b0d02030a030c150e010c090501050a0801 71
    0x41c4040314018030045d500301350003000e080c0d80d400307840181c91306c00e0005500190050354414801c0c4458001c0360f006005e611a09c92206003908992031628850042c0d90415402900c0e8400c0319641c0d074040c02d4050340c850680180c0c1d6001402002e000d800711040e007503903100030428080b07580c130304044030a0354044e0001d1109070740c0307d8010180204154810354018170761408841030100b440a42005080e000440781c084500501c00d6020701640c50815108190250380c032402c1151300d442c0320b0b4000d0022a03219032105401c2c10001c1c56101e07440d42018034040516036552010400901c4e04521a8000c00c000034003804220324818002500c901c03400b11064060725241003c40c91042c5807005000110740c00041c100c0d0016100d0b040140c46e031246610060020342801410b102501c1c290040c600c40ea64000c0050604498690b0280c0d81b01c14980e8080d64450030300300c1d180c5200c0803540200520042c9520000402c5030f01c510b0003910000306908001d04100c41401028076580c0c0008406055540749480e000c18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 582937419 1250 582936169 582936187
    0x313141008070519020601030b0c09090412170405010c0f0518011d2d03010c08011502010e0f0609060705040e0613020f0403030e04060b030c071401090c0e07030629 72
    0x5103114000c00b1a00054813600c00150303c65010030014140c902c2580440d002d6164808150f00e940500c581300c5a0200b50b907001b0034005810040c0200481c2c2c03aa04000d52000c030384030b0008848443c11201660700c1c0c0d450b1524500b907143d0100c55910f080030350b410b002d805c00004010340003010480c040b00e0381c1803228045103000881542c3c070821001c52801420420071413810140300e250102406800024000c80018000f194034060140003140e0310155542c5d4120703880c0c043d070741010843d0651114150b541c0c03114a412000e00a00c842c1803010202001000b540c03c1c12903101345804001400c40e42040800e1006100c0759030b0a6410707580240c0111382004210100d424200c2c000d1041c078840840b4280005000420103820017108001100304480c20030119940b52a400c0341803200700e40307040a810b0100141d00014055a401200c07806401000062300d81d0315035982860120150044114115144108100542e15024100141c0394620351480d2403101072545101c85586194580c0070508041001d283c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 582938669 1250 582937419 582937427
    0x604141507110d050f180a030804030317070f1e02010e0d0905150405092d0109021209010b1c031101090609050609030406050306040b011b05031314100807 68
    0x80442241032512105040406000d40140d0482039908150f001e401c4030ba5406038024016a95120f0780c1e607000c540303003035842034128020141c848646544502c980b500400031403500400752001d1403003501c1d400703038101e4030404008299000500c10400c00c112450442c1c12141d000701c4074119549460240440307900c800701c00b0f038050134004480008a1103640003c2110710741c0003844100720b80059501d0003001c040c000e03030301d40345100314016150090340e140b001c189180340c007170306144150903800301c41d00c505c2880080c408010b00d000c0e800703481c2c00c0b500400d82101200c2c82ca031200b42c01c016600020419160708401146c1c0806010444c423200d84029000c0001f490300403002c0c48000300201c0001c010620703851030602c005040700d00d003c1ea128455040000d092030800000c483c06d072203140d1605030840d503807141000080c20085400504222000c000360075000d041a400382d41c010320440240d621600c05000900162070154801103002c0d2030072204051b00e48480c00300b00c60101307052814028958811b00c06031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 582939919 1250 582938669 582938683
    0xb0f010f06030f022101140108040816031e050403020909061005060c15040f1703100b0f09190503060a02120a18020a060203030f0105010801081b0f21010c050a02060414 74
    0x1c8240f2218489544005d0b1140300100d0503200d04900c000200000d80d401110130300011603004042c800200503002c01d6a00401d103010044d403191511300c50340401600340c48180c4030031585180c04100302107000d0046141ca00c0415502201203001485d41c1c0c41c088298407443c2d030030780c480d2900035030380003c000110060a00401c8401b9402850380d440b107040900d03118158401400e401d4405070320700c0d2025160908607504032801070340e6410071024154103099800040b42d0265072440b20702d00d41000060441d446070403a54104150b901303135060300203103044241401c0034001455131807407a10410400841d0144020113507004240000300180340c03501d600703100e01c14203080031000c0c0d030181c200300d000075800380e0000095104026000da5010b05907680c1c4019a121042030240543c03981107203000b01442c054444041c0d54141c0001c0400d8140030014020401d0994204a52628510b441c051203070301280900071411207200c5860041e140140107040203444a4000d40014100309070300c20002480359040000c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 582941169 1250 582939919 582939937
    0xd09060f110408010e150c0d022701030c030c0c0303020304080d060b1908040b0117070b030a060e1302010504030b040302010e01020f0d05062e11030f04030b0f010f06030f02 76
    0x700300e14280d00340c10a00035041485550003943c01c0ca403401d4401500422856224a402003004043e601c806820013003a4000c464080c07503039a82400904011100c0c032044060303103107220300c9400702c404c0444001020350b141e805d200c4042c5410860301541c1154032402007000640c040c40c0041e22512186000c40180c491450a50080c2d81031000203d9410181d10080ca020341d0150170700103100c10400000d46202c3c5003180d0141810403c940104000315444080020031103051003503520181d00d84c81a154642c1003074542c014180d80c0e8040034094080491191034100f07010440ca1413999246038002401c0f4401e50100070404441e6801041c00c060003500300d0200b114120707000355105c0405900388041038104141e112000b90401c00854a9801c5c407000c0c01140030005d440c8000004078099030f10720620a90051442001b800010010b001013040c00a0719460b41c1110032180c0da1440d42c02d1000300c82e000500b24900c505101001040340d900140319003001c42d0b8960a000c92018070f4002100001c1c0921803170 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 582942419 1250 582941169 582941171
    0x50d1d0a2105150108031c050103032102160803010626040314131d060d030804060c090521120c030702010e04020d021207020607020c0901050f0a181506030902060d09060f 75
    0x108450301c0c0071015210b03018011f0440880105829008030aa990070300c4090003041600c6070440f903400251910301c80e0280c0042e400352429000c61140c0e2140c8002803816120060b0100040c4240395000c446581c10150910b407906000c452682d582c294010040c100074140024011000c00d004684020399142090a90a10704019600c4142c0d01c41e00c080c1070250703001000a040040c42500d00341552038003240d01a6645c241c1c550702c1d82e4400008117454001641808034102e00056039698070841045900f030305a0890750b10100913190b49103841240800560700c841c06101d1201100130010560300701607024680340042d8481d98003c40c00a01c221002e1015240c00000c4905008181414443c0240055401c8a032581d56140040341c980c1035005115a0121088004206600e044500c401341c2d40300092600d00c006990f140103103c030903c0c0c48400c082e5692900d1111511040912a81006208504062000c1c000756800591a0312a001c0880748065980c0c24400c18444590b1040c2c0764500f0070f000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 582943669 1250 582942419 582942421
    0x9031112071a0a12180f0503090604060c0605010e070f030507031b030e1b0a05060306030f06190501060c0c06050c0a02060d090525050603090109050d1d0a210515 71
    0x108442c1a4014580303400400d4104c0004034920946100310300d0010703403076500c403c80c0030003540d28108010062070003629544070070b1007007070702130399840300100028440c6480700d107149507440c0380407402e0728016440444000020801c00944039004001070400104074640002e00f5a00c14200307030000d280450072440d8900c030600c040c1200a4240d4000d614022845044502e004042c0d418840302ca4860140f058002036000c60411141c10200051a00020014103440754001881800d0f8605070701220b4000c8503041c8964060048041445801d016181615001e02c01e010701d900c0301c10808002d445100304000700010541d14a120034000c03400442d40c000c0c010359491101d40860405020405001d460b02c1c05000f40084549450071040d03230006103034031105d0006070f02e42420030180d0b820080054446549405aa1300020700910051540c0103242d01d5159108202e400f94800c400650a902c40c010b0108080c2031052820100c042140c41e800d07544070a4241c50300e0b24204c1d081074481d01d9a040001a540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 582944919 1250 582943669 582943709
    0xd0807050706090b0c0c370309080307030513080102030702030a05031302031c0912050c01030915050f07030f02090307090c0917150c0f03070f03062102100903111207 73
    0x150003803112805241c100d4285d42c1d80030440c0f20107c5a000407406001c4407a0500c4402c1e0a0b03007030344000c003103800303810203115a0743e40c0d156542c01c59100784030840c0042c100040442036100700c4003490016000c583e00071419480c00c80006580c1e80b107404000d00a0001c00300020b5058005050390000f6203a000e81537400e441c0404101580c0d08001001c60004166010382c046041c41102c10311102c0c00b6040b10013001003078250702c0190000c0c00c50b01303c01c2d5002d0f00740200c007028000d043c1c020603008519480040c0d85610344540700500720303060040401440d50040006001d43d0350006003003802d40754002c0340011078903103030390080da041708003644442c1d0800300b11a000030703c068000c540311100c0208411150141e95600c0c15100c0d1b01c0c8502091050740c498140089540a032080f02c9220040100d4140083d40a0711540e40c6240031360700842c05503184901c400070b6811801c0541240b1105803e9082800f0070b107007160b4901d0102d2200300c10306800713201058981e0400000401c0740900030000000d140184025503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 582946169 1250 582944919 582944941
    0x30e24040206040b1c0c110705060307050903060c04050418080304061a1216050604030203121e0d15060810050409020d02090915011a0904020913020409021b0d0807050706090b 77
    0x60f0741c10040d8501a0a1b102e03960003006000344048481010742034843c289410003400380c0000d031441d010050306200c5200d40742c90800c104c5014484880825841e5458030003080251168000d241c610304086a007a803001800324400d40303030080e03030103400070a401c180b13540c00d40d503900058032190303a002c0b48008007500f0b503010104010318945d0400c0030740041103445034203003c950300c92480004d4255010141951020070840094404403540850310940c50180c004154069007108509407030f8a580e0310705032425101700240b007030001d08050038810440d144c0200c1d40000407255100b030358007441d00c800c000c500319503e8800a40f141c3e07a0017010b10003241811805180d8070000c4503241044030384600f0012a142c049581e04003020004620741b240740000f000180000f0b500070700601d82d0030074504408490508505c0c006030003c0e0645010050300e817658445003c0016139001c8410a0580003604010038480c4d014031880e0380300b242c83c100a0358820b1207103880002020a9103000e01400d5803001840000d00322 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 582947419 1250 582946169 582946207
    0x2d0e06131e0906180809012d0f0206150a060c11060301080f281419110a0614040306050414060f01050f1c020f1915030e24040206040b 59
    0x1107200300010300641d00384002c0c0d1003540c03a02421400046c408090075620428486091411031100022011000d407062514949001d0510020890482108601a030304101170381c8e00282c60404400c04000700e0b000300e000c07540030b4000c000802c070441c032440d02401274401d13040d650120050304055580d03030742d80d550645034030084454190318080c10443c00d502403040c01e0004964071040c4002040710b6601e60750070b90b0006005000e06041d00400c49000c40b022202403e1012084c0900141044100c8040410540f021590400c030280b00c44d03484a840564011000e40f001e03030340d009100007227545490030804041c0b080d0303003030941c8944941410011410b0341001750504070f03801690b4943c0000c0d044000c000d00c00c8813100e2070040000c0000c060b0000362504284042a059003e0162030f0611100303030703149000c6a060341254100e00e03210081c04014a6141c42034418101150700034240b181d004030181030305142c4004130a040c4280440c0400c0640d503c2c0c9044030700401041903100c4e40d4000c0f140c907c41041d21 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 582948669 1250 582947419 582947423
    0xa1d0304051008011a210405011407090609030b0c0c0709020a030b0f10081f06020f10050103050303070305060312190e03011b050705070306062d0e06131e09 69
    0x410900e040b940e8038022034419041c0e03829822012441c010781014940160000c040340354402ea521040d01c400010b80718001030040740140d001003511070484104181d049800b07002c40042243c47c07981003011960005203581900c0e80409941c2c866124564940303102c0c06500554a013501801301e00245400495004261401260b1428403411040f802002481c080c0e0061940d04038000300c1c01a41c1e0350b44141e12140c0d103c440c454450b84100400d884451080b0056040400507911003001c1010701c0f002002601c1c44440e00303008c1440150b055a03211900e902000e0110401d050701c420100710542d4003809422104c0701c001d10483d86500742c0d100c801402a200d0500c0300c0101d0300100881002d4101806144190800c241869a0711007004204589650020b001942c0500400c40003200080243c01071600900140c010359586d0440d0b442684440c0c4580b4401c0c1322241c04c609001c0200c1c41c020f5103682e602103030803034950700810078191820001c1c01640c1c400f01d17202913000b054400d44030030359032200036018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 582949919 1250 582948669 582948679
    0x2181818010501050d060c21150b070c03200301090c05040c021c1b0605010303020a0209090c01091527140307291306030209040b01080601080f0a1d030405 68
    0x5200e4254221042070141c250440105290580495041d4008850001041c5041d40d01064552261080c42198030162048107880d4544040d0791150310300000301401074010950716040035650b42802140f81d5200044c504031111800b01d4170300d5502200c050030180068000d00100c1e040f850f0503902d0408601038240700340d15043e0800c021038800280b058041003941c0c88000c800c08400c0d002d50300400204940081c00c0800301c0c8242c001350050048a00941c400e4000b1300d140181841084141d80d4010710084c51907004040003a9144c0e80101c8100c101c2e412440511030341c0111a801b01c8544035900b50102240c00701e90940108103480c03041c40011110072441510010803106d0070036441d00c110340b0802102d20359007808900e041e5540341d05602420514121103241412044cbc010300c548200ba0700132804643c3c04501c95103d400e00f03000300100c4400919021059180000000c0c10340803020301181141c2d80140001345186001d940328808414210036175500e00342140b0701d1141d81c2d6100d03000e000c0c028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 582951169 1250 582949919 582949951
    0x2a031b1c0e01020706030e010b040207051005011205120d0b091003050d11100e0a0b0901060302180402060a03110c0111030103140c0a150509060d05090c01050a0c0303021818 76
    0x2807099007560711105050f0702600c01c0794a84507084000d84078040000103a03550303840382d00c40c2c80e5031280300419026128501a10540c000400600d08031941648041c44a030051240040001c001203035014154455110b61600c5450010968004180390600700f60412010b406100900130000e40070000c482c4190100c0b202c6942c000001c546030030808450800543c0312182d500d40c1c45005807c10200d400d105411038a001800d0340381c2e0303580b0513000d913032104d20360759205420b100f94240344981452074040c6054400c01818560701084c0e9911441d0904010980d481c0c4156411041100440390140e003520000d0011280110084020790310030b1000b1281545198410704c030a4070040b90603411124024406071007649400c04000d00e0f03013131403042c2c4000c120041001402e25550302014048001150100080f6072609150107468000c40c24461814003205120192040707902204545059602d46000741e1114040410080c0c02d040c0c500405600a014003c2240d0095000c040503110710030b44420140b40f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 582952419 1250 582951169 582951223
    0x90f050601170706030b0d0b0127110715060503060114030c03010b030a0f030c05031206040b0a0e0c0708091206060a090e06131a01090f0b0103022a031b 67
    0x2181d20340c4142c034001d400481c0c08006560095214400c000381c09043c0386400451075a0f02010000d098101d41b00030b01c0300800b100d000c9100440006003580c0c0c540405c0111900b032208031880350240a0000f070031b801c1c01d404801a1070b034050300540c00410000c2c00f12072442d6103d80c0200c06000800b010140280325440c080b140b545014005c0b41103421006e8050040030640e92039501c0c0d034030385540b002d6013400030070000d081c0011130400023040c0c0c0494000b42044e10b07091610420050300c8441c10071a109601403c4180400c021685000b50030004500d441c96885603185040d801130701500341c41e281e02464003003040007107580c041b44c898850801100c012040a444840030012a0300c401c0c011401e960108001035104801c0308030307569510340242450340d10154842801c221030032007600262082c0b81c030307801c10071411601e40c0580c0048102c2400e00b50306049280a000048540104a0544540050a4040e0400014000c40300d8812200020940620b0001d40851f641c00c01e40b81246441d940c20081c0040d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 582953669 1250 582952419 582952439
    0x30b09031626030610050703021f0b09010b030f16090b04090501030308090604110f01300e010e06060d02061c0e0d030606050d0e1f0501140907020a0b04080d090f050601 74
    0x1101c2d04e00244540c02c03580c03403400c01719403036001200c5c12001e522402c2014910302c0500303520342010355a4100d02080415152050180000041c0d1001781100400d2061000d803664004a659005203080071038000b202c90010212202c0020360320010038020005404228040d854000318166400381c0c85501031034407800002961688102c0b009000300030403040c81852440c1c110152222000d0501d02008600400c01c13128108210300e60030f264a481c810003520100c08114050b40d941d101c420701c0200906030100607103031744501c4000d26a600c94070358075004008640e191000e80d03c1d82035503040ea0312007a0a2100468000b03101d908503030f007140d1140a41001040b8824083c0d0000d031003040c0e64250038408580d00c801d0103008071040c0404280502c002c1149404501035121010070000e881c00300b60f0f9458240030034441c10745080101d0203820614108034a5607000200d004c1519442854144c1d50f0f501d80c100491540225220358608504200e80c400500c0790743c1c0d4440c0081d5000b101030720501e0340c1e100b420076 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 582954919 1250 582953669 582953671
    0x7050405010c0305070f121e0e030c09090a3311040504090c030b0916080705030a1b050a032001020d12090c0e16140f04030b0903162603 60
    0x707001810b010600d0001a21030381c050724a1070300c40c000c4001d600465644000e5000100040c0000040c29641c0e421045a010442184c4506544c2441d004a00050000c603444e60001c0e41454003034040301740410710100c0c04001c08030100f80c1040c03000381a00e03074000300c030200804a020100084a00c203d5040700d00009442080020107170400500c0c03a145ca0002403001800c7d17402000c0d90440b01d030784000000700e11001d40161160241101500710008080c264441080c42d80e0895503455002080c00c0c45580c800290a100300c40d041407110404181c803011755003290405401450300304291003000820412092918410038103100d441e0000d25a90304c00480e62811966070600010b01c1030030104152801a50182e05180c0c011900301004a0f25030500c04e002d0081039401e44e06040448603c0140c01d9400f01000741400070200005160014840f03c11405000e1070001510305540c035404a00b040c2c0041040342c0c190900c50100d2120750380c3c03c0c10f01d05c0c0300c0b220180c02005400d00785a87c82c1c3c0d660340000122 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 582956169 1250 582954919 582954929
    0x1090e010e010512010e060f0a24050d02030304150215010e061e01020c1809060603030301030b0f0a060e09010e010e070821090a0806091c050712022103010e070504 72
    0x5016841c2c0000c1000d1030405071401d01e40c0f556911039400800d44c047c0403480c85042c41c1207504100b42000303003034a0200c1e942e0b14448140c2e030a101c2d0300c8101c450321001040b01258801ca44030501c0c043c0c240001382c258407650b448864580c1c0000740d0b8046c143d8000c02d01c0400c40380c0070061003c4503a40d44400d01c40001d0101c07042e9a02001c0072070100d2007a52011001500c050f8184116011410090085007000a038940448007103400e40f402c0000e844020013115034003e90a40c05581035501d0b41d6070741405680060040030450b08000700203490a50542c1c09030008010307040c10401070382040d816990003003504640c07070510b07542020841802c0450008021b01201c21000040c01c03624004007501c00300c86203610401105100400004d20300e80e403621113100181003440007500741c03402c240c48024946402484c00035654000d01c180c16003080d03002000d8451103500961a240e40ca42240404c0f81440e12061811151541a10f1186080d0a4603006075058441181003211207886c7c0100c10348041c010342c4a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 582957419 1250 582956169 582956189
    0x190903061a0d121e0809070605070f030804080d11070b0109060b040e041103010608031902010c0e0910031b03172a01090f030c0b0a060821070804030303090201090e01 73
    0x1084002030346000c20303040325071043c540901002c0811030904c0c912184c11100e503000403194014401d4031482804064014145410414a03000c2c180d50f500030150b41c40740c000317401e0244440014061100b03481c2103c018400c1d0000400c82005691545881a00052403d4a07505c0c1e0300c1e0008924019144180410b41d00c2c0400440e00341483c140004907080d1000340101c1d01a2542010004aa00c090083c2c0018000b494040c58540d07074041c0c2c2181740040c01001540441e8100b240810345103400180034800e0180c2a0380c240000d554004c00088401c00350380c0028100d82c13046002228003101d22103480c06492141c200e07100c20034010250400b03a801221540703034503034038004607414181101c480c006001e19031150002c1100c0995403514401c03a0203080041c2d010034800d0340c0c44001c0081da401081d40c0601042420012641010240b0340d0b1060b580f00b450b488481c50103d00c1c5e0300c84020b030303080d00d01d45030748444003541e82d83d1030f0b00c0c0040180040b01c0d0300300e02003800302c0f801007810075450452605a56001c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 582958669 1250 582957419 582957439
    0x3020313270509061603090b091f0b0a03080f0c06190c02030715052d1e1501030e010204050a0906090506060c1515060a020114010518061005190903061a 67
    0x5170110f0444100b450402070503540c45010340044e2108600b6441500844080d000496000381c0c5104450311102d0603020b550324060540800d90380b083c42c1c0c1c07015240c210310358945611000c44210198450035082e400c16200d5401000b9000c81c010302c030070064071802c0c0c90500640785400400e0341d48c1d014841000b072990380c14020b10071198041e40e001940c442e0010090504884480c001e065407000007003c3c00060511081c100500c1500e280014469441e09800040541c80c1003044190812201222a0704040c1c031240072600c1900250160783c0074243c000d040c1407a46036240512401030040384180d9030043d0400c3c0000e90f5510300320050724120483c00014000d841088c0f49070b080c0b8004c000b06016103101c40960300b6011521843e0140c50081c03607517000003601d9820401080300d0020b05900141c4520742120313030003a00040100000750490030030380c0d2030b5200c070320300c54025a0103010f405211409451541a2101030079031103090312041f02d00403e01001031901103a40c050184a03003114140e00400552 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 582959919 1250 582958669 582958681
    0x3030906070b0604020f04060f02060106080708060d150606050c06010f0b030c0a090306090302061f05030318042a030c1403010b03040213020c070323060c070302031327050906 77
    0x582c90940c0300d48020801460003680850701003c43c0c10a0704180e000404c1d1003c0c0204082e0100881d034050072450a0010740b52402c07000003086080000c00c40d03400740c045210958100189402d209518006442050001070740706d5a00804030307001120f42101d9482444000541880c1300b5404c14192180b41503142d2031075072241f034452201e40c0241c2103607040210362000040810038074811542000d01c2a40949000e00303040c0400e40305030901c4200346a01c00011a01000182d80c0001200c400848403046146981c1080c0006001001e034480354541d40308907000700c0032988058224402000720141c4042007164030340301c003c0b507810a81c200c0d244c585003010401030140c100d10201440c2c2c13040c40280747c1d402c0c0154015482060b41c002c5541044241d10020050040085081c502a1406800510b0a180040070328002d40e940d40090040086043c0004100007410300c280100c503820f000180c1c50000050b522034050301207200c54601c6131051100246168219480760040c82d024084000040c11186c03104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 582961169 1250 582959919 582959933
    0x14042405060a020a060518010509010b0102030d0e0114090319050301050a0303120f06031209080a0c0603050c19020d110a0507140d050f2119050f040314100b0303090607 74
    0x244902c401d40c881c9044100001d0f49500810340708620020440c60703090851203032203081d0351002c0d02c40c45840c1d0401c1c80c0901e5690f4001700b920018080b01401144510018016900402a2984041c20702d581002040a0324000000034988025501950140351764617000c1100d45000130701406610200c0c0395001c2011912580032000050b0801030006410200d0f21042d108407441d5500c00c0300c0c05111a112071624903040000c04000304000e0300a4202441c82d50f68209a60003180110030505030b850340851920040c0c40d080c7c802c0349007501500c009400b4000c5002c0c2d542d100003048440001c4070401e1080e800d2101240d03051400d41c1c490b000f0140281040000d281002d104101c2982001d4214005e00105004100c0c8000c880302c010040e01092111554402100b441108100341d135050412030b2202e803800541d00d103035164155140c0103888202500707200b0320034460b56001420140116444c048603407004106140c0da00366110b070400c007501454081c035480c1d008220010354468002c0c4100701c046100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 582962419 1250 582961169 582961177
    0x161a03061504080f07050913031b0303180c0504050709060804121103300103020a0608092b021614010e04060b13061413031e0c1404240506 61
    0x15481000e03080c0b80d110302841c1c0c80d0420550141415038000f520402550034403070121a00b0450000c0d4040c04042613440113800c07880c21020030b1000c0607460124a05140c800e80c481e1000440c0e17007039103107508161410a0301007560f15004040c03040f482c100200d403041d805451740c10704950035038440b03180c07682e200e0700c80d402e4003003010130080709010a40704d400103001024001858540251103402c5e4101035019000710070420308010407805a00240c00620150355440b81c01d500b280c00c140340c00301042c1c0d5803620310750820301d0341c80d44201d40716803800f071020020040030740c0161041c0c510342c00c5030060752880b5000d04c28984e061003690442285000009295489110740e2082130001a2010034110f544014000311a800030140300080d501c403400078018658084c4c1c01d0305007024120750700303414150714041880d0300c5500c5100003402c400c180c00400170503001d01101910555084605045050f0f501d06040141000710f850051155182c604966030103418540020007200c82840b500d901507080c84140881030384 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 582963669 1250 582962419 582962449
    0x1109040218130b010909060b03010e120f0d1404050d020a12030c020a08071410020c03040501050304020d0f06021e070c27020a020d0f0e09040204022109161a0306 71
    0x20801042c0c0208481c251070a00070f0006003400943c1c03040394184503040314448034059100c5e9040c078490781c88204002484006903510b40194556850640b202198144980c41e030002d030841c103281d501003003e00070503001c40c8140e008805070b0300102c900e4981242ca03103200d0740009007508110805100ea1500c0303940180c912144600444080422a450f80310f5543c000c041d08655840d02c3d9840351348080004d1100540c2129080801d42c00d003000c8920321500d87c01240120f41c10828084006000e5595500714407890075000701000c54030103034605100e00039600440d48030a880005c0c140315142c00d0056001c036001f498006607598042c504110105540c1400c1c0c1c420211030210021030b13404c14038510b2004240250f03580d002030203240408000500039180b0500c60105104081394444441d403241001d56a219a0458006955250008140041d00c8031354080d031005114000230030824400008100f00780c092042d84c001c1c8219034440b41c0000c449072647c0820f82c904018000310325030341440c80895002c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 582964919 1250 582963669 582963691
    0x4090e2109062b0c050f030406020a03060b07030e10090807030803090f031308060f01061b0302030d110301090b0307050d0b07030b10020c090705031003020d080c070608041109040218 80
    0x200d040003c0e0b0741c0f04988142c052646508118450704100e80c0e84504141c021003400c100e030030b0295091100d4903900000b0000b0300060b030001120106580300750b10403005002c107406029154495801c00904281c0a46c0342180980516001c008a0030301890315041141c40d031100929500b411070b0340b1a4820740001d02b00c001d03a44101c051024841e0030a1010749070074003507011042d81c0b00349400d02d040e103040c60291400180c0c06580c0c2c01404020740c0b24680c00f080380301c203e030020008002840d0491540c4100301d003606107240b40c520b248040805060042d41203d050910602c00d5481603802c25032118480e01c1020b0340401602c0c4294000ba00404440354800040c0c01d001274110801c4c1c1c04144441c0050f0030f401c0042c0c03c000000c1045181292550790800c0c2180f514a00710720305022225803100345400b01900c0703550349104940411200ca802c5541128443d001e4030070349a83e500020340007c0050710221144951224006410f05000d240c091050340c0040000c2841d100704500300152039006041c04442d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 582966169 1250 582964919 582964927
    0x50a090e240d081207021b0109060305181e0106050a3b010306061d09070b0c01020c0d020a051903020622120e1c050d030e2104090e210906 61
    0x2144220020340010444e54510300c8091400c00c50090030420307c1202c03208102e00c80d1a916602d039031f00c2042d900544000d0304001460380c40780300c1c5185080c0c08002c898035542c841e0f801c3d01c560443c0250300c003501c0c40c00440c0c0207101c087e480c0d804002c650789140c01040001400c140011074003410480e41c000841c031a07207000c1c55803484030985052410320260800d441882c3c07030340d034100101c0b07842203245459800b001320083c040d800e10071030700d980310b61140c4108044494081404044c0c481c0070340c101ea1000000e501114040c03101280003035200e01948009030313103600440316502d891085802e20382c688258180c1c050304955851140841c0c0c50007664890714540404800c0c1c1710000303619010702440580c00c1761504903c500c441001c003c08600855101d5000d1081e00140e1800140000382e2110071000078100452540d8845201a180c10401c0003407119950f514490485d040d00510020401d56a80010600c25881481e12a607900c2489800d10b52054042844003103032900c200020b40b48580d030003817042d4a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 582967419 1250 582966169 582966173
    0x30705130305030712080405070605031f0e040219030302061603020d15170f0703020f12150402100906021009030908240a0902031c0c080307050a090e240d 68
    0x3601a08200c90560002660200f40802110003401c04540da00c2e000708949015900d50351140c0c010721912051240c080041520000c90080d400c4201c00d80c030210031120b03640c406440d01960b10564040c1c0c003d8004c814045007600300110300f001600d400d60010240381d2900b040c906038100c104a411410590b003403003000b031020154044d808007002c0f030500700c45549080940786807240c0510300d04001154401042241001804944c110489030125807481030021510003140550300302c0c00b00e6803401e00400058048100c8501010342c0154000e5412550b60700810405403110f5000c0d00484001d42d01a02198114176205d400c07160f9900d10071300d070080f0f85a555071074036407612140008510108170b40907600e810b401d1401c40345980c04242a1000d1004e004560042501c81011a00174003200748580a0300010f54051290000e40c1541f00b85010340e68a00302800034455009800c620b000500d006400103200c0022040d91070251452450500004081c0c21152085058511003280c000510fa00e40d040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 582968669 1250 582967419 582967447
    0x406030303021206010219060b06070203070f1d070801172e0e01060b040605030408040506040603091112070501210c03060303080901061a091f030b0102010605030609030f030705 78
    0x1140300c0d4801684820804006041c88000101070314115400518801184039069102e810003c0d000040000c021141002281080c4030761100a5014400c1050014000804650300c000f03c5185400541004000404100345410203032100400100c1d0f00005008582400c01d0651440203a142114844032404c07480c440c006101182031042d0100400e6200145a03043c0038201040f56a07000800c04181005000d40b894016802000104035000c40044e00700f041c0c50040310b018110040410b5201e03507650070000c01610112000720b48404950003418143d0406041101c0300e907040b0001b800206d810400112420b2000900da1030114030b01c8a07017410b1104162103040721060315030303034003007001c5003542409008070070b0140c28880180e242c603004001c06111000d0b803100302124070a500c4d42c4c82d00302d000050a0b14881e8507120708490b551003d59030b0101d4140d44481c1c000c000c2a0000d01085aa440801d500e403601125498890b400400c145a00f150302c90004651180f12420040d081c0304000804e01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 582969919 1250 582968669 582968681
    0x120105010303080601020c04090c12020111070803070c090c140a0203120f0403030606020624010c0b0f010e0109020405060d0c14040b0d050610051905041814010801020f071b0504 78
    0x80c001c02c1c3c0280074000b6650781405640c040040a0780d0178440e0642c90359412410f15290701c5150f10030072081060504580c459803135a69a110040200d501e0540c81e804003940340d0380804c030220b0315140300003000141043c40d802a48010340782a01c805040403d0082020b0f041e40c060790741c400440c0010050401400c04140c03980c0e0180c0c41d801c0745060a480d261801034100c0e07100741c01050a541c8014100007403807144043e10402d103000d50034402e0043c05c1c2c143c0181c6420042070b100810600c450002c101d8413000c61034440703040f108085800c00541e41d0701d0703c10404901c100e0051582045041007400008040b07a04001107528041c03900190700c1a07001d440c0165070300682c1007012034420005140518000da4000c4540080080311031020072541e10501500510402c4c00d1400c400810b0120103050900401c291401020000d40c2180140103800107a0010000f00c04c14600c4941a4400070030725080500c241c030000340a49852600d024030646074030f030300300840c0f4000c080007500d054008913440c3c540c0d000e10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 582971169 1250 582969919 582969923
    0x31119051002060117010203240d0b13060c05030705041a0f070503030a0e0d0c021011100903080f040c1a04080a0f2001050f0c01020c03040605032707030308061201050103 75
    0x340c0f6040d410710550385075400d141105960340b680184148411180c110711248510003a2290079542040c668000c18001042e60b08090007031400207041010101140180c000c0c494030a40003040840c0b80040140c60900082d0b0f6404000b0340e00384030500c0482d103c10065030001c20f1003054282080800154401250300c002021140c40c1c00202c14005100003034040c1e4401c016a10010307016412692070010b2a403010050b02034410040003904940c042d001e1440e51052081200a98002c00c0319000d032030014003c990021070014401d100000d02d200c9100c680306010700d41c0407083d004000d1400c22000442509407210310700c820420040050649004c11114210b90701c02c0100c1030041c181e40c00c100e05207070100d942c00c4011000b2095140004d03a0f100c1d0172102c2e901c00107241240c459112400007402405040700409080c880083c000c00d1464100d005035200d0603411031100225600700d1000d24a80d14030000c281d40b071391302c200c00c181300080c01114039541c80200500032003203607500c2c0039200b42580c000b80c0c0700b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 582972419 1250 582971169 582971173
    0x4090e0c2b06061502071a12060f01050d0e03130f0e01121e031205010503010e06040323030109020c19120c060f021209060915061507050f100510031119051002 70
    0xc20045a070341003041847d161281c241141c24050400960003c1020040c88184210500c01341003221ba070042d01507074181900c031807080000030b424021b5260740760b0005c07000d030b92805003900d00042c444015045d20000c5c2c4a08080c000466480c143d0104030081d42c003207045800665105481035518184078140d4502c0b40241d5412907400e19043ca00012500d043c2c01c8240240d0400807c544100c0001585540142d494074011011700542484051000d0544050005071040003000045034220794014190710400034003994540345540c0502446e02c154480c0080c01c541c010009c0c200d82a0140d01c001100c10b00034100495108048035412049a12024490003c5400034041c011109810054142d20880c140002c0641030801050700c00b900344018001840b5502011105018041c07c60980d031009500070b040b1690b1503040380f8180d84a24a02c110080c585151a00150000070203100420072241c01c0ba40681064640c40240300244072250b42806405071103000c0091035440e0101d00071010003283d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 582973669 1250 582972419 582972433
    0x1e0a020a120923060702130b0d05100e0d0c08130b0c010905010f0209180406090b1003030e030c1003020d0617031e040e06210304090e0c2b06061502 65
    0xb03507070420f44081c440b45011081101c80307a04a203890302400c8442040e0100d9500b445483e684405401510004d40169041403150221108003c400508850504200d8a0911602d00840030f0350369207201c541540ca0005003110f1500d408170782403000400b03c0d0143d5030418002c85440f50759404141d4802c01440304141e6459100710f00f400028400d071500c864a0380410340c541040d48001464a00c008044040f03e041e905002c1740801019510000071a40d01206080b9a40341000c8050640c154910041d0701141c441e40c0c007000f440c500465401607100000349284600b61007a50105c0003500088203060096035111f002181c444d0b0b00b030341307003000450f500c400a603036481c0039840c2204980301c15411518000000e01c0b0600030020036496a03076002504ad41c404105602c0c845003d90680f0076101002d00d14000058040f8210640e900a14021a190004c5800411402081c0942c00e81c807a0540040c0403554814030040c01e0000c0c0440080501840c40843e0041d00c0e10540a04407012200400142e44000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 582974919 1250 582973669 582973679
    0xb0307030c172b02010905011404051501060c0f020d050a051f02070c05040e070902030c030a1b0207051203041802251104020318010903080f06061e0a020a1209 70
    0x160981c40485003080140c1562904000c074983d103030001205400108403415440400b0502c00d42c0a01e400c1034102000340101340395240040803103001542c0a454a00400b09540e03181c4005801460407604c3c4c0d5551246107100340d4540c444090707085801281e010b050840030310041070003080380201982c020005402c90000c0034030055045c00340d044401100e5801800142c01040e0580d21501c100c030410f41d808210035098400031401d0007040c0d080a85850301c007005001e2030340b07003da01440c4600e200340020411a214544030b000c6105400800d0001039010702000d0201c1d0030a8440e401d0004403083c03ca9041c076446080006084005d8003034203641c50f501240d19991103412014410f5080c4c98011115880c013200c3d10f40d243c00c2c6618511045c00389400001003401d2041d05c500c1a04003a054030000c0141d1201407500030000c480589050510040d0480030849a141c448102c81e40c1546840e111800408e1b2110b0501050300040810819405840c2ea518042004603c6d8180c05180541d01c2100c0d15040c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 582976169 1250 582974919 582974939
    0xb061902161401020309040504061103091b0402040b030a0e010b030d0509091806041e0213090201120203090c0f040207121110050c09010e030c030d09061403060306041202010b0307030c 81
    0x65405410414581600c2c0b81d500c1c1d8020045914402c400d44c0e022603103036614140607002d01404152008051800810440c1e04200891442007031501019000b00c0c0071040030402090707026038016104012000c0010800c50a030350380c00401040b80d000c00105142c0703040f0700001d0412004135012004100005a0301e8040e02d043c00035070358450b0410f0036480c207c0c0300201c080c0e0340d99800144010804c900300c1c526140c101940e03100d040041c81e401482c4030080052480404046e2490300000c90114a43d80300f4000c80076894000d07a44180071f5076000305007600c6140d081090740d0f00f02c4250b41d60810313400c01050300030401c0c40324811000c040c2c075119400306002e010b01d01d600e0558030003542502c251400c000d05c03060011000c120307407444030240391800407240b02c03070300007030070301078505c4103d0f0f03041c070800400030502078100062804480b42611031007500108205000c0003031204a9550b54980c00803800035000424140404a8980c0c0910000a01c64042c00c0070a00d004440d41003580c030750301202c1040040d5114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 582977419 1250 582976169 582976213
    0x120307030b03060a092f030303010b04080607020c010e0d0f020d080c06150319080c071412150c0307170f0115030c020c06091206100521100b061902 65
    0x281407000c1010902d0354988040900c154041403140903600da000c2800c80c0c1200c440c1b840c10402c0141586d5580d69540409111980300384105440f5004000c00038003034070300200c1c1060340c00c24180c45686000d00c2600070005d1850310024201c851010603000f00f00940c0b160070400414610922881d503548003403005003481c02c00700901c1c100442240d003841c5980d940b008501c03204450442c1241881d203982c02d142461490240781c2c50088548100300d80000c0d001450380d41344107108000d540e0341070719800700a0310790744906504040c03070341001c444d601144003015902c00440c2d003c00145460380468907074a500303031115101510301381e0030b011668005000040754254100c190701a00d00301004030b01058280a0345441e48100b01600c84d04021136003802c503481d4501200302280c20f00e81a1105440c00503140011820710b802002c1c09101100c450141003c14441104003083c842c10080268221071405400074200003030700540c000764140042c44d080718502040812950389600580700141b800c103010390b44120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 582978669 1250 582977419 582977431
    0x605040b061e07020414071716320a080105030c010302031312201f0c081801060302090a0207020909030f0f1b0601030c18050115030b03120307030b0306 67
    0x8041204441d08120700c19102c00c1c20030299042a183d50440c0000307002010001d545500b144802c03010000da81e44d01034a403081d16101d02c0742101040e15840c1e00d0400032130b040c02a01c1d0100b207440d460000702d9401c409100440029995609a201c001c090a90303440c1d80200201101091045005220030316040c001d003000c8000c00e103400c60540c5000748801c0354002241c90301500c0d0020641040900b00c0c45402d543c4a604c02c45e03508410480f400780c206030b40e02c90a110210f0601c610024514505075482e0241c400c112185a43d0310115071909249403444042c1c50500300f003159a0b0300707000030040c0c90304600342d88107180000c1300580740c60705070050145000c1e004040544c40c0e0800c00410314680800c4060720130301c4040310151902ca81d400c82100081c2c480e6210105003520544000108012a00000d8026100990013180b80503880040c00d03c141c540038007a5860044003080d14254141c466400003011000003012500c0303030500c10b6081201940240d901d000000d48441c00c103401d1741030070031490350006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 582979919 1250 582978669 582978679
    0x306060503160f02012d1802030307031b06110d0b03070f0b0901050c060a06031403031003030e3d11060117030c0d080a0b030613081b0a060605040b 65
    0x40740290b0202400c0ca882911502803046450060070f58602c01d6222440d06585040e80c1c20700e070407002ca80f8001d07400b4001c3c4400000c5042c0312001041c4107118403034505a90740a8000c6003448141da40541d014105412000184500201c5c84c1002c55013074080c03902c0c0100d01107139460341c41e102c91031514242c40340b01010502035400701200704907082d180603040741110300d01e040b607903150100c10004903000d11660300c031020144500c41c140329902080ea48484202d921492010500004403195542c807030204554902140607140c400f0800b00307006802d0500c0340f610003404941c010301c480080e10b010408210a80f031480c4403001880785086012042d10300da0701c0c2542080361001303071965074440d0b41310300500a41540d04501202c09400141c100281c0d450126010292481001c0440000700b814a04440548505013040c05000c098217010403074034000c9141d521010b900d603a041e1513100d40395001c11409155090b01d00083c04414200b4060001044e00c00d95011400c6030ed068204000d4449031030503c0d00c54 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 582981169 1250 582979919 582979921
    0x9060c0f022413140105060a1215050c0d0c03150807030b0112020307030b010305060403080c0702010e040b1c0f200913080f16020901080309030d0309052107030306060503 75
    0x140e60030031086603800310040c0c80e80d0843d9650110360b048209803c0802407070401c4c0f903400b13000402d4042d00a14400c0341d090301d061440d15500e25030140c080c500c0c040c0192030707148141102003011215400c4280e00c464244100392034880580030707e204076204000401c0019503034809501000603030742c0c00b40c0b009182c9640107140160550b1103c1000f0303d01841240d40d010001c2405608640741446a18000c0d50821f0310b41a003980d41c0d04046031588000c407000c0300002c180400003444081050f05039065950103940d4108072860b11005d102c010808092416400518804652031481c1050200740d841d500c5100710920355100c82c41d0100c00542e040e403618503080d00c08544044551543e40d1459400342c5031482061854183c0c1c2030000320340c841c1d42d40c4c96191040004250000101c0b24040c041454801d584491450782c0c2c0d400741039100d02807029542c3e4540c20414900f024a4131039041540c910740100203440c117048003200c1c150240e00025540750006a8041103002c01d15070140b040800410480c2452461 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 582982419 1250 582981169 582981193
    0x6030a0b01091e09051b0c0d030e1f020319060603020d0b0d03140307090b1204141204060e030304090c0305041a070906050706020d05010f2102060403170c0109060c0f02 74
    0x42c0d43c03403602440d2419950f581c00140c0d00d50900c03005100714805801850340d9001e001c0503288d103075500c00305a0f5000c2820301400207080500040e082030800c0144190520b060b6090514402039440500703003405440142415000020716440341c00d006242503200140d6850300c406041c070030354884540084c402c00740d040115001c030f44c2000c003040c1b4441038410419504d80e0340b52802c0d50410100c0d04480403040c004194550f1844003210814091400350401400140700a8001c40da00e51403d400048504010711040004a0140d21600c040400c0101641d08082d1076128240c12101e489a100002a444109200600c84151441101c03210118640d107070034a4410805000398415100b51400c110001903480240001507042e2102159000d0701800725503510441a841070b0340d41e00800380c441e800c0c0a21040c1e8a2925000ea151903680038164500b0949541c071b40f101209406881c415442c4000c01c110405001e00b8454040024450480040c0200c4080401460a8000720b100c000390b60101241d60a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 582983669 1250 582982419 582982469
    0xe010c0209040303021c0905011508010c0f05090121140c0f0a21090c1a0c060408070212060705130e0c070b18030705060115050a050d0203040201020a0206030a0b0109 73
    0x2d40030307815040243c0d507420341028030082c81004c1d44503074040074034141c440c0081020640100c40c01c040341030607004100c3c0e00d584040e401c070b4590402c0e2101003440c030b4002e942418000d001501294105040000700c0e15140308003501c220000182005441d5598805030180d8a01e80101c99048840c0f6400c41d42421050021403103940329201000c014084103105001d90000c1c034210303900c1c0614908005200480a620300342d4131054140c00340659a103c0710340858081101c4000350f40f51a60120000c0c886a01c0c0c90700c54036083c0d40900070076a009040d0900d520190030b400c10000e4060300e280d40e1019500c408400101d401c6041d1038100401c0712459406218868801c0700c00e1f0b585641d00301c0900706450f100e03862442d801101d02c3c450301c3c15a001c0811240140603001c2015030403640030303200d40441d079890543d0898841c0315001c3c515020035000c0c00220940041540955405803060044400f2000705400240603500222442c06a0319140c5121122659200c40150018910350004050340480075134610 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 582984919 1250 582983669 582983671
    0x20303013006020a021018030e0414250305040c05040e010e060a0c02070905040b011719150b040501060e130204031704050312070210120f0606020c010e010c0209 71
    0x10400c00740c507105070511900c0000d0441034080a8900466020a0030700c0d160003e90410211070b4098002ca43c0c41d02080740d03441c05101140305050780b24464501c007564058400c45000c034040750304070369104001c0003802d041496503030003848041148902607410000c152040c01d541a034000400d0309106c24080056002000340040d104200c902107115407a01441a00521084205500c180b10b4034003404018001980b000c90765447c190b0982d03124948551030142994010f440081141c40c1078001000800c1c03038084da500f4004a29810703641d60b00725010322450360345405641a42c050440b041401d000d00b94600c103180b03080301c041c1c03018400c0358074001010f01250b021f08101402080300d404404c007550540d60454015590285a0705180410202d111400b90090701485009105001c148c8041c85240c6c1c0a5803a240e6004141c02d03005103150904445040d4414168444e064680d01a4909205c05005071009090550700a09107406000001045001d818801d0b5044c170070300310688001350710f03031200312 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 582986169 1250 582984919 582984929
    0x1b08182404030203071209061d0d1b09050103150501080c090a020906090d0b010806010e04080a051b0f0d031b020a110120030901030c0503060906010309081b07230102030301 76
    0x5610039074540c14141c0c210701c40c41000a00d44040c0d100e40884282c0c203c400d03401030390000d64079507c00c250b8031070141c039079a600b5162250740f040ca4813a4140000c0c82c0c400000d111541c3e042010b0f00c132903603201c0e24401510030a0f0000c8980765000c1107030808a40e1544103041c01048800300400104442d03401180d54800081c0c0074155482e000515107025454241c115102008007401e009901900d0381070254944400f800394400b01e000d40c0d030002840b191303407600850007150083c09907881c01c0710012040e01c41d82d2240412521500c1400d00c010440d04041c0b114080c2d01c00c07d0005082050f41c0814003c01301c910340d0321040d074a141454644944940c2c00598500302580c000c1c40c1c0c1088078a080f00603101504009a40c002d038000768202020140340200c09091403e10a032014401401c040340c1c142c42034081200c260742c00101c3c0c1000103009612980200f9031840c050402285040c000c8402c0d034164003016000e807040350703011200c02c000d44002100503a404941040c9030302007102000c00000e403244018824 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 582987419 1250 582986169 582986233
    0x60201152601020f0a080a0b01020c01050f0d0603060203010311130e030904020c010f06060c06060503030918250c050708070506070b07021906140a0608030f0d1b0818 73
    0x440000310030258122071288001c090701c41c1d1217643c00c14006100c10001c451007855142000442c40c0d0550000400c20b130b1503d0142c6441f41001c140c00c0703134400c00384c01000f0b01a5466840c0c102c0080810564030055029601a540200c1442c00010034802d1400e0200403c01c0010b02c0e100e00510092004030698500e41c408440150b6140d40300840503015009400d00e0306502c0e880c11400007504c0d42c0000a00f101c2e207104440c1800310550394420191a80106006a6013200d154802c0080102a1201495010400d21403010703000c2400e42505c20803140c989030a8010403000c51440040c0002004654024036295005000e441c5c10200803808600511000404994800004c142250700920400380320810003001d1080c030881600341100170303042c400303549001d42c0740d0703840070904404150280c0c5096071485801103141600a00f050b4209500035020749210580e260000521002e03034069400304d44119613a440c480d82042510854032020700131008429500204420322500c803140700c6d013646050300c500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 582988669 1250 582987419 582987479
    0x2d09290a050d1a070e010809010b030d0e0418030e13060803090f12120d0b010503100b0a030908121803030f13030c051c0906170610030209091006020115 67
    0x50400310412100b000c3c0c4810212000070852003690182075450b803007000340e075640c0d05502c440c8020381c203c1c2c04c1088490780540124602c2400c0d81c2c0a142d94201b40f02c40035100050410108040342003c1681410803400161110900b00c210300d0001c4090404070f170b080340c04200706490000003075924403034824420b000d42d20210391041d86a8034410740c003041510303420a80f0151074141d504070000f41e00c40141c41c9000c503e0180d40601c1da500c182c0075684103e014101d041314803420000c5d0111035805c80890481016141d86c00c0038000303a13182000d4801554a007000c0c0c991402c1c21407113405d4900c0784000101c1207510a00c20840700466040d50181c008003840e0310129604410700781123070321080c40d40000d002480348043d19a03480d41c501e0706600d0701e00c009540300e0342941c3c2c030ba80044440c0c10320001780f4442021104003040c02d81c9800e4002211640140c00c00515019038940862100c21045660f401d0f1000c0c16842002499020f024506540b541c0000400f0f10509107003582151417512400c0c40c1556071400707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 582989919 1250 582988669 582988673
    0xf09010603050d0c061406010807140408030f0d05060d0f06020901090504020a0c170a0f1b050d080901200f0a020f010612020a0b0a092d09290a050d 65
    0x340c0090040d54110003a41e0b01c007203142c0c01c05064a0200030b0111001c910304210404a1021010f81c68002ca005039900501074807030b05002c48200c1c8c0da815a45d580703840204000030b440c401c02c1004210312280d942c20f07561958210f2106034101c840052440e402500085581c4d000100d8021403003007100c0d400000141ca510110004960140f80c98210b5a00700e84000b07500c41945030400b420341c028900c5641c80200071901e210012000b801501c1c030000114a058003450200e034082e408085d0000760843c20320410300c109442d094641a81d00d99090042035800c03040c40f00200c401e024902540d41d1640083c0585601d8101000c254810022100d41d854004511550494820300c41c002503200f151009005003138440710307201455600c030340c1d04034828003003004001203500c55401905c1031a132260b126a01d15a1034404a8011400c200304071100050201d6003d0302c0d103007041d40e2020050031072020005403c0005260358013440400c210714070340c490845441580a9580c01444a0980c0d405840c0c00301c800307442e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 582991169 1250 582989919 582989921
    0x803090607240c0e120c130f0b0315010e0f0105031522060f0e12071b080d3c0f030f0e0a060c170105100507060c020c0312120f0901 58
    0x1064042c610a061038282000158000d13603240e02004111007041180e000d00445540e00d4801c942041c1d04019072040c500704091065004512003c050440490622042320009052030980700c002c408442c038500c01440b0380c40015000c01e5004e018074a100c2d140b541800c0020b603444079009021011007030b40c02c00203507088031520040c43d181a041450040c400c2801e24006e4058000a041d119840c0d240c0f40d03544c401c0b2140000c0daa000c0036101c2070028907140c6980c69494040040403108039544201510004010108001c80d0554105030b075a040b1500a280070239644154444010900c6da40c200d0701c0110b1210074030048a0301c409468200040749914042050b005003407141e4072407004506d440103005e81c0c0d20340407444d01100b521400080103188418103080d07811420540028450307501000041c41a03003003031540b6019240079400c126050241a660710401d075012121034a0042c0c01416281140b420f04220900072200c00790602414030645012012103400c00800c0c100e91f5001800120300c0d0b02c102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 582992419 1250 582991169 582991223
    0x2070303052a1609050703020403020112200c01020702040c0f0807080907170f0c120303160215071d0108070f08040615060807080c040b030c0304110a1403070803090607 74
    0x3414151940e6003904540c1c0000f204151203011483ca00b003100003819184288200c0b8196a0705850305401254584a80310040000004401d00380050b01e6544c880c1c0d207044d0300507083c49046940050303035442480c81400207540c54052034006115100200341020f6400050a41d40300b001352a003e680780d91003800709442c10020303031f02c0605590040307400035482007008614020360000510446618480d403070140621003000b946041882d40081c130218980f640903503035585000750741d44112058407141d2100c402542e101956590701080000350b8854110003103014403000003000742051881407401d808042e225517000c400290030403101400040400040b540f00c1c001f425985940c0004607610341c18080c2141600f9100b90700810101e030300003a0040c0e00c100481d4103480d03201011609540302d9090f00e9005400140c002c840b8107071004400b0303406844450941c0b00400e480c11750b098058100f40140350401301c01d5006020f041e00100300c01c1140b502ca980480e207829038000c6003120321040102e014140152 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 582993669 1250 582992419 582992497
    0x70309030207051f0315050102030f0d060e1014042f0c0102040914010b160f030e04111b03210601020a1a06011101050402010807031524020d0207030305 67
    0x4503041040b0001c001e1180008040c4c0d215850400120b1071401401c40501060310030b0074010780c001c02490b13168220b50400741c07900505621010904640744c8410780503000080324030710500c203207a60701003100e0305407440000f400d10001e51b4200040101d402c0c40380400d032000c0201102d0340c94001c0312610072160450480740d1300c0007100002c5407507903140c002d00c4018040c11040301e0403503210640045156929042150603064230f058014a4806056950f02000e02c0c0058055003400003030b98410704192102c0c001c60f030742034568075241d40d6200c6c1040e2050710818040e22920507140c2c800e00046c664100c0711075070101205402d080e03103003a50b524500100d18241c24400d0080c15100040806545801c04040050140200b600d03208200342b0310603040b5088035001c49000e400241c2400204195900950080541d10074140061149907102d1095006026400074240d1180400385050301c55541c0c140441c000c0200c0500c00b030b00d00203140d500d00410902074003252104c01c2103d100c00d03150030300e00e41084050b25a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 582994919 1250 582993669 582993679
    0x915030a0609121709030d050606190c0302010c030b150c0c030a0b01140105120f040602040b0403080301050f090609160e0a0b0307021506012309150c160e07030903020705 75
    0x2828a241a140c10b40710b00c000807003c44d1005407481c0414440d00c00c3c2d54480d080d01070040d414208080c1001002d000c000d841190000030400a440a80d030303050b1081102d80c034580d21500c204464030301d030003401c491010202c00100b500e401c0c91940700d90f450582c80302d65001d0115100f0784030b031701495509041c50848200a80c0c54031984042000300b00600c90103038101c410304a01c0d402c04070100e00054030b0a00c2003d00191307440100030001401c54040c540010b80050017100e006041c55162000c0a00d82d40c401e80080d940000040010480c901e070006850070042300c29107039111036060400c0070a07110761000d0117411500501072880311101b0712524541d000c00f28000e0040b42e03600d50f80c044a4030341d07034822344080b8010f0141030701000025454011050042006030364280358a190a00f5071508141c402c106024001d400704101c25184e9981c40d8400c4049030001501030741c0300c40c1003005078a04107105040782e010300e0100070300b084189100b0031015844051410003054040d034601d02241001202d030400c0e5440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 582996169 1250 582994919 582994931
    0x10b071127151804030c0309030210020c03010f0207050d080a02070b0f0a0f0603050d1b0803010b03091006030807080c10062d0b070204380414060915030a06 69
    0x2250601c020a40030b00b0200c0345181c0340b01c2d240c0c0140640075440f1070611203904148004140064410821a46030501030f03e804803c2c03e813030790b0000702036545460000006a0180c00b0f083e10a02e420700c00c1c0d80d50505450401c610f42250b50f90742d1502d519003800150b05210780c00c00000c2d2145c0c0560100e07114030b68002c075410702c203160516030302c1d28211f026107011191601d48411136610710071501c41d043c181c0342c00900a03c641c00c5030440440b0b81c801340743c41c000c00150000c00740d0800151410059070207400203580d03840d00c0b0f1803c8a1000d00e4054202a408070507414408100080703000f000845a8403a00700d440299030b4440140e03598a09040030300300c00d0585180410002d0b000489004107a021113084240503000e0b6000c440c600c0407100c5074000c2a40c00310081000174010700c1c05500c40aa0111414031071007442c01c101a40a41e038110550307403041c3c83ca8281b00e0140561030144180c070092030309a1070081d42414a100031410850004010040c1c0083c00d2118110340d507410044100d0b603a5000c0b00501407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 582997419 1250 582996169 582996229
    0x90b0105190203130501110616051b0d0f02160b180303071505010b0c0714040e06041a161b0201020705060f0c07060c120c11060c0d08010905010b0711 66
    0x940d90100c4c0741c000311190108408101d940c4a540c421541d01980c2000f0710070354441254038204201c886d034203035050000400120b10a80050f00301d44881300180409040342c034000d4480a84100444c01c80c0408540005901200c41100e009400c03090b0707040110a1b68444150340c20f0070b06602e0482600d0b9506110120710402001400e2210603480c9141c41418001d50b41e9a010542250203411644035050708845130038000d1072000c0b6400c1c0d546050091010400701201d8103023038102802a03406544002600000d80359050031400303895002030320f24000c1d516102c0d6080000b4a01c10020903031100604918500c1c10641e07108100d13610107824018401e540c1d40c80754200e0b542c0d0643c0700400c0440e050194500000b00180200c2e801c0c087d498010000515034080c1880c103e40c112044001141c01644000d008045522180050551028104010840020b40e00c1c0003070034000341640076003007040c1030030014010b0580d11001d484100f5404601c6500a80c1c1c850700169810306854009450340d4510341305154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 582998669 1250 582997419 582997423
    0x1202070e04060509160b16060f050405060a0c0504050f06090a03060606091d07021203130501060e0711060720030906030a021306030501060c120c02090c0a031a0a090b01051902 77
    0x20040784030310700f1240e5000f170300030800138141503520440000300401e00840c9070100005287c555007520616000031100c030608410001c55900384c405540710381c4200208004d1030090321814102c8000da0134102e0809240100040f82039003010200c03406023a0208655115072181c201d40d80140d607200f01c0030710110361240c400030050100c62045445042d0b20322a061090148940050b0103088182d01400e540410880401c04a9201400c00c1e000050380c0080b010228034203120310b4010348401c2c20703043c4040c144204018003080c1c02001b25400c0307420107814051507942010500e090140c001e5110700c1540c00d0802990306602401d56659005100082001a1064903a00502820401c011030446451312103604500300d40f400d001d80c1021a200558060103e0440b000d102c04100b000d1a0600c5a20425800b040440c10309440c440403000011844000c0a13800d0b005260785654071000d18540e5130a1100000e5280ca0513100381d00d002c0f9500e14860805902c90400c6484622901e802680c1354600074100035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 582999919 1250 582998669 582998671
    0x4020a05010f020c0d0b090c091905041502040e0a1b0e0f010c020414091c02070b0906070f0b0a05070e182d070206100501050a140d09050604110607080301031202070e040605 76
    0x10240a03103901c44200d80f51427002c1c01d01a191035819002030000e008820001000d002c4d006507099405d080c00324100c01003e000070009410346001520300c2d070a00c4542242990488080d241c0b5000b0000c03072403203100c3c0d40010503140c008011640b4030226400134006892490403400e001e50003600f00b807080020844c1c0030f0343c2c080c003c5010404031115001d43c0030704100480354081c2d01e00f0050300b2004041000e04400000780c444c482c401440c50f840c1c910590b1301d00402081d566801c07100000003008020b244000b521440c1e9200c0e01c075050000c00740c08034500203100864015007200d080320b030700f01c00f05a40f114031a8265440340c4103240d80c203180c4080c09030101e205c01c104449080c014811031000803040405412240c0864506840f507600741b40b40a0f01c292241d0405085000d0a03040906c103640356003d5500881d054240201c001e4031040c1024288030300f07038009c400a91303030040e034040146000246002003240d0444c0c0e00042c02503616003c41400302c0c10050503903c0a40b00d0071501c030511051020540c0a2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 583001169 1250 582999919 582999931
    0x1021218070e07080a0618051501020f0d050310080601170d030b06030c0a03110d0c0801090b090c03100504020a050d0b0d030f11010e03040b0703140304020a05010f020c0d0b 76
    0x480052058900c0d16a103080500406050044074404102d0450080040d075800004249010400396285d0300d81c0c0d110807000c0241c5c440d0198071201401800102d03201485800305080c8054001e82c01d0542410703a5441460100c4401c20030000001107250100151500c080c042a0050304c4003546c2da04082400b403c01450584414061400c3c403190050181c4980d6204a001a00c211b0650703682c3c20b212015600400e0080043c161200b80752110b5001e14402040b82c0410101c0c0002c505c59040350041c18002d0507080f00c00001c0c0b8120b00140380d5543c13449030340e030b01800450810b5541d95803240011403107061944051f400c2400491903820098014000e450700e646980010800c00048600b000100c0340000d4014010820802d002032041c0d21424000c03403001c000800104500c1c0e51641040d2455006601c03142c404100072409070b04240e4070107102002800030384501400d50800b900011142e081c0341c07048074180540e0300700801c3d16500a00001d411200c0081c03507000203040c03c0c00c111944c00d9085440b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 583002419 1250 583001169 583001191
    0x30403180f05030606010c080d1b0210050c041205160b031b03041a07030608031207031817070f0b100e0a1404120203040803040915090b030a020409080c010212 70
    0x8045001c9204800040407900014000c092075229400191055003241c2020b542c3c04008011160030500c41e03000c1c40800400d0320b00d800b0341601c840312009050a00c0304440c001d0140c103003010310503403010340b070103850039500c2204e00c80d28004810f141407454251100720f0b1511085565030009a540b8a43d03018510420240c0c40c110b0025118060328041c52004079001003210003010031101558000100050380054039040015001d5100c0c02e4003851a04120903000c6484520303000c000e0016418081c00420b4000c0500031f90b131201072075a441c1c4007007440c0051010a01008180300e81409030801100000603004510003125003814000d0b5071103242d460040300f040580da500411500c0300d20f8480c480d240318502100419a13110750f610400d488145105000c00c41c8010f100c081150001480240b0040ca002d24000a495041d0303060300071300102590115040519028103400903071000309010300065411100084c01c1c0300c03941b0b41502c960041c003024250943c4082404000600e03002603260160074010700c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 583003669 1250 583002419 583002467
    0xc0601060509010207170607120b2d0901030f15021c20040b120c0405040c0207090e03092107090c030f0501050f0a0b0a0507080307210c02071415030403 67
    0x4640726200606c2d00d050491940041c0005545038491400e95061b1003040b80301168109004001440c510001d242a4800d0b100071480450084c0645050218500c016685011a5859034032100d12648061002610700c04008842e0b0b8210315040c0d04440030603c1000340307070342201803060001e801080c19030120036800c201070402c420f03074444030304c04da0341118141404686041d92250038007501c048060000c811500d8180008590ba69541c0100001c541c001c1d4018404e0a10300302e952000e50b1298101500c80f50070070081e8001c2c035103c500c3c07003417800d403564110954505034003003e9918000042d4004410603181044030004240d0541107030702d0001140005000c00c0e41ca4030204400790140c1d200103036014080d584100402251038014180c4c1c6410703820840c2c104401521510035951003200d82c00b002400f6100000d009142e03000782400da001c0030b5002003001c14805031b03010759100854062000d500c51a0480d501055403184810f4500110b03540400e0b4590402d46000741148201740313071544800d85070007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 583004919 1250 583003669 583003679
    0x304020111070b0a030903020102071a09070905060d0605251d09010510080402060f0d02041d0603060106031a03100b0108090a03020705130912080103020907090f0506030c0c0601060509010207 84
    0x441d8000d448540a02c3c03807070030700d40000c154000d0100c2c1d0002c500f507540074040080495007403108403c10803000300780c880591601d030088904010f0150003860000e441c10301441015128060000c0a042e8880000100740e06c03481d609042c00303103004001542c00303040015081ca416078840025042c804c3e29a1640c0e08a03480b020400040440034001d080c1c0250706802401c03a40b81c8224000c0750014000303414586088550003650313545038003906007a800b054001408110b44160940c8804d242d44001146402e13078108100080d480345810710400c01019151840b007856245034241d81d20300c40a0007400c4407895640c40346103001400c031011003a4041101c580000c0d001d0310010030040e0849a25501820300b0504100030448080ea0214080030b50980d13600c82400001d0700c00d41700b00f600e140c0c241c4503218550315601c100030f030600c030084c81c40042090517081044203121111402066850444200b901e075618416411000d0140030084100361140000000f92103803c2002408420b500381d0a1340e00c040c1d128 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 583006169 1250 583004919 583004923
    0x207030f022a30010b09060405040209060f0a1d0604180b04140c040c1809181104110406090311010f0806011b0819110c1f02150c0304020111 62
    0x1103490114158440d0700d4400c02d0301c0c044465003074040c0703a41400019440222400c2c0c0d111092900304004981d0345100c80d1341a85007620900e54408070488080c0050700e06503010401f1402c0141c0094000c2c55108540d00c11662460b01c403001a180350030440d010814010901c241034001650070342d0180d454405000c0108c1050b07440c0700c0c10150030481d030592030f40741d0b40d4500c5000f48a03a4600d0340c4a005964105006580e02d0240c9040060385a03079a00d414514440b8030319494000b039114501480ca06040a828845001c100d101e1054200e50045000110100454080c08a41c101c6062440c0c0005000c035125030840c03030b4201034a004085007403420100100640b204000041d040d004030f046000001d9003076100350740b90502c030444a480340102002a5458240f40c3c1c000302c1024512501e081f808042c00c56100b082c2ca0814810700d00203180c101015008500c00020081d140384808850410b4a03107042d00812400c0700400441c502c0c121310745400c46040e012600280c404900191140c41c1c08890b503540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 583007419 1250 583006169 583006213
    0x170903030c070209040c0e01030614070e03300417060a05070e040b01050702150408010b0d08160c0f060f0f030b010f051c020c0a060605060c03040519090207030f02 72
    0x4000c101d5441c0082580070000ca00100501c00c99998401d5240410320b0385103c071145000310300c038450208009104003215100c08900074143c50410500e070ba10355401da50001160303c420400640d40004480740391544554035440151210464140000c1c0041c030b013025010b24003121210b000585160b0303102d1213420000e8840c00e40c0d00380006074082509864a1806600c40f0307080c24030504000d41f501d5001d82c0403450400b00030000c41c40c2158081030400500c4000c2c010100013a00840d2441a03600710341c0e8500b0410b014502c9045808a5940c8150341041000c0d003501002d031080403038201d5806c1e9142c000038124a000002c0500094690015266241c0280034480034030790b0585400c0b10305001c4020490f001e80064198050301e0361030b16001e010b40f40c210b2004044041101018000401c8182007510075165103910103401403004000d0f81c00c81d61004810f440540e902120203848401c298901318601c03440c141c0068510920000d40702d401c040e04961100c250402540035299600000e01c00c009103080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 583008669 1250 583007419 583007431
    0x81f0b01081506031e0405010c1d01080118060302060d021309060305060a090809120a171e0705030f030a0b0f041b0c05330a0c1b0c03060c17090303 65
    0x10b401c0318411042c5408005941d00c20640d0842d01018990b00d014550030020550b801d4074980d42d00c030240d00140d0b611900601011507030180c420000246c1400003080160144103c070741110700301040c80004504d03604240015074004110740d07140d101100303006000b9440841903980114800e10b00003401c92990042d1000c9981040c007608195903000b40f400c0103480700003421100600d0400c0310034001c1d0707a140c1c203000034006010b004088004682c42d00f007008a14a8210105501e81070003a40381d455250308940c010720001d42030150b00c440780c92805d0b40c0365000d6031a6443e1410008400c104c02035074540c3c804003100b0b0045a404c0c4a0303c082da418841291840320540c03200a6005205d00080c03806525081202440b4500b20b032121131f128804580c0d40e03034844401a4800c012042400192420407104640140340041d08000040000d007029080082c80032103484003030014a407160038800c64044110045030000000d204403ca0000300500202144141c40c075140d0880000c101210400420703284121 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 583009919 1250 583008669 583008691
    0x1203023702010819050a0207020a081c2001111810230408010603030e010f0302090102070e040f0b15030106080c06070605191415121c0504081f0b0108 66
    0x801241c004440d00d00000f01841e104070b1400d07400c044a00801e2180611804010341c006847d60032501c1004200440c40d400031816510104616514186a0809040b10f8840307040c2023060340003e001004412004924800555217861060000c4c00c690000910b0140c5e42c091401d00b20340da4010400c03088100010210001443c0c00c0c0304140d2100d03040c290101c112550f4001c0904081d503480da1103003035410b40c0c0c00c120001103048154064a580002880c400341000c4d003819030130a8003c20000b0f65030f9119100f0728001c1d18409002c10300744035010032090106900030b1a071500358074000e0840c1c60080601c0201b18002e41c80e08a00007558640440d2a82c00800000c16440ca4500d0a4450313102074035012f4882c4100115900012010071110710503084034000c604003011003403800303044080351030710002c011501651780c0c141c0b00513902001140c02a007040e0304240700200c600d003200c1c08032410f010b540c0004410b031084c403e10044600e07400c1c00119541e49402010b00100d54440011075812000340c5940d01c1103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 583011169 1250 583009919 583010023
    0x3020907050a20030f04031101021504170304020103231f03150b030111130302043911190b0c0a020d0302070203100914060c1c0e07120302 61
    0x803c5642c03d00001c00c10942183d00f8040c1400c61281c41c0e0707011b41d00c110740403001404500020b5070144006405e859203285a0440c41c913158417074480715510000c1d0702d82d8030b6100100250031a8020740c013540d4020030140e035001d84450700342042c40186a00ba102c500401c907104045031080880e503c085800c1d244d0040b1a40c50342c1d44071045200107441a094029815522034400212240d925006014001d410842040e01c640c60f50041c0012603228601c0c80742103180c4c0c1c4102d5038210010700d03502103207200350781c04644d614940c01008680d43c0c440c2c5002c0c40c0c0580602c1403c10700f0000251014000c840c0114039002154860320b048105070300ca02d00010016030849140c001800c0d0181d806404454005010780700406d0f0b140101008481c4002811503250b00c00800d03004007040d003002216030160100a00a182c1401e417030850090041880b9074041c0c9544030a0003e1440600744062030007021990044a0300c4d44607454043c0d04e40842881ea07002080b4400040414244014040040c8142c4c84000d0180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 583012419 1250 583011169 583011197
    0x11205060a050103150305031c0e012d0b030105101403010c091203031113030302010b0411031302060915031819020621160207300311030705060103020907050a 70
    0x113442e05d2944c60020b09072901d00000441d10901c000c001d002e45050044188034190794800045588480070010180c0c5000d0301d403c4040a100071035111464801d4001900320f890a01030300203080592a8940c0650802091042d4002c5200c0148240e03100c0348916035a400460f000d0500720340c4942745100c00612002c030100140e2460b00703c05515540649004203410224032001c004541c001d680c24103d000a0400c10418554284101d840d610341c203c5051003210680851403401d40805840e00758481c2e40c80c3c51900440d0384a100300c0310b4402001d407501d843c48940c0e641d0b0b2003083d0001c5900c20b03064615007003900328220002c9100344e5503402403411a4503502d407a40a05c01d298000c1003a109655506e41c0d030075a00c41118903501c0f8400d8400a1103802d060044107030003400c200e61030740084445210440d4410b030101c440d5040c0305010755100c0200c0880ca840e810111901c200b1a280c401a80c0400070325981488004141507060f00d00070381d124040c4d0307140d40c0e4007207c0c03d1041e001040c0001b030446c081101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 583013669 1250 583012419 583012421
    0xb1f080c0f03010303090315020a02100b06040e0a050103030801081507030f060905041103010c09050102030415180e010e010f03080306010806010207051302030a05090c060412240b011205060a050103 87
    0x34000103000032460605824588000c0541c2c001e030402d4020541c1c00c4000c000300000c100e1003a448031058542503040221a0310f000e5680d0440c5400f415109840381026025603c483d402d480c010312564540b41e41c00e0500c2c2032903900500c0c080c002600065604400401d4100e000107540d1182c0a2009045110341d0780d94900b14000c2041e0042003184a07200c96000038100f01d1409810302035409044240d101000000c101401c440c401161407041c07001d000070411890703801000356000c80d141405409c070000b054031021646400c06080b51138840b8101c850209900040090290694a51032100c00313599072a04c101c080300044501c0001c007041820000110154800e50300140c0005040c011a21148d44039000600320041d01c2c110841401d9000c420440111040c1c009c0c59040013400014004207104080407a0151060f07005041c507050000913039004000d10081315034100300020201c144896044420a4040c101d070215682c0081c80f40e88500c00ca4107103e200c1c0300e0141200501d50901d01c2e1070040150 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 583014919 1250 583013669 583013671
    0xa020c06011e12050607031b020c060706060b12150405010f031514090a030215010e0c0a120204060f020f1635030c07060f080f090c041b030b1f08 64
    0x5081e01c02000000680c2c40d259100c28001113103d40090851464001e10007030803540b46111219101408000101c460b0750003090b0b0103076041e0b041d6041c41c0e85451600340352003d0b090f039901403203000c031000540c6a1039180b40144035000d015502c0c0070b2102d200c00d04040200340c3d0428024480d03000300c0600100002041c03800810307403072006003c0110b038007215000c94807008c1104544440c0d1030342061104004041d4184012a10019043d0001e9001e5060602c160400c210085c1036562001000400c0103600380a04400180d248040509659072a12868003d0280c020986060007501c5034181101c2c048201040c8104031800440c0c1901001d0314003980e840101081ca11b1900c00c008801c60750004040d242c401e20035105042500459942142d120201d203402c6d0b40e648190204420098075401181e440b450345034119030380108101e400e841b001035807030030304448000e0154864a4506200c110400b11140c4072203910f0903450400c0360b07000c14424040300b02d0501c42e001e4034109400f900c011243d40112901 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 583016169 1250 583014919 583014959
    0x708010e2a040504060801051006110a05060c090112020313170c2407020d0507060c0e1002161a19030902090411040b152b1d060a020c0601 61
    0x103118007882441d48820310620301a070712064090010302031040741000d000700c00c0204007a0008008e00c2c0f0704941c0400700c01c0c58074001c006c10800c0d120741046049008103c9014081c0c1c106c005d88000e814240c0c402c08aa50100c01c3d4540071404102d45600284c030244203503440f6240d500b0a10780c00d41610303a19801801c58030084d2692255082c442a502000200442e02c9000c4010102e0364a22104501c40241d108004044404541c0a0600711070015400020303502c1240d0f01a802161000000206807002c0d2082c007003403900081e4284440340071b150b0001c0c41801c000a0115410046138030b038040d60100e50500340d1003040e03095042002e1000c3e8646024001d40074402480c000030781c0c0700c26500140750302c80c00303490680d540c0c244800140c0d100c1c60503204401010004a41e1868203604145940542d0b0045940411140111303d82c4100820f8141440803554100384608001d0380d003040d41c03140c440d2052400764807450701c110300010f2071458251080b2900e1041c4100200590382c030f04040c0030500c030304074441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 583017419 1250 583016169 583016191
    0x203031b0a301401080f0102090109060804290f15060a051c0e0706110c0a0b07020f1c0c050603012711040605030105271305190303090201090602060708010e 69
    0x2001000e8806885003109900a119410f00c0a51425409030300e03100d03402c00c0044076640704100108072a80c005495000312000b0b81040e600e01e0b80d440c1858148041e41c09481c0c10f0440d045500c03400498055214039100311442a1001500d03101c00e445604002d400c150295002801008014840e038014406400a00c100b030ba101d5201c00c00540d0300905a942c1546101e882e98440300092200c540c2028152070a04103003402803980101740c000240000d2a184a03035a000b44001031801c083d03481d01440000d0800007d03010100c621400e03021007041030101c09054900c4c010850001c11207240190440341281c1c190f414000c254840c2540600c40120f02c0205244403d03968201c000780903842c1000b0f44014120303621040d80300d614040511088000310000202154524488044596403007408150010a04031020210701e80c80e06c0c1040ca041150380e089d1640c090744c0756103141015495042104034500c01c0e610492026038904003130b81d0344c10b0142c030f0700c8000c6140c20005104541c0048580c0f540300280d092 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 583018669 1250 583017419 583017497
    0x32f030109150f06050702010f030c050406030207030c230d0507020907030b0a030b0f07080108191403130b0c0111160b04110907030c03060812071707020a060203031b0a 74
    0xf4a04080c0140780d1020001c0381002c2401d0040d9a006a5001d80c501820b0500f031145200030440100f80d440389001f14414180e02003900000d05100d0b1034a111010350008044840b058110018100041d40e4052844644500c2c980c603120544100c090b584442da0240840c0100d45401700140e01400400c0d00c0e41d9000030407000b0000c0820781202d201800b50300c041c0044015402c1c80d071001441c41c1416080f0f0441036110b4941d240304424041d00172107115800c0032080f410180c0c8147c0301030851041ca04403540418000300b000c111814010000c00d01040584002c00c00030700f00a2256220f4000d100080c0e40d0401d111400d18041140c0d9144550311a20504009090104c502c00045c0b0f00f02c0140c803800000f1f0794400084e100a130300340c45a0405414454020301100702c030445002d0703091046206c02000800041c2000c030043c0c2c18031081c1e0312501e40c0104a00680f68444400964a400441d03080303801840c540000040c2e00d200e941214407010700c0e5514138200055403040600060544046542d600011070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 583019919 1250 583018669 583018679
    0x20102060415090b0a14060d1e08090406090b0f0a0518040606030602030717010605040b0711131118010804170901110f0f0f010c081306140403032f03010915 69
    0x70070450311400b06610000351b0b500341c041c0c0e01c4900c2d1707200030029030291a1a091800120b025081c41e1f81c007014400107000c403114032600d8500b415025009440ba0418100320300480d032100190000c0c1c0c1e04080a030740c81c82008040388208400e806480c8a0306410204294a02ea4401804074030180e105014100c08201c0655996840040b6401100d2020000d07410713600001c0c4403c14111211700400642c64840e040604000d291511031003040c400406101001c1003a01c182d03100c00320710080000b45803008000c03d075060060201e4075449424120100400032560141c1c0b9801502414003075500b000c0c2c4580f09902100052a01d980803005980c180b11740300003500360b050b4040212004005005029208401c00c10314154541b116901c1202d401c1c5c3d04003000d0b40c1c00c40d80d20084040d8406440b0700f8040e2902242d00b0008010005026140140311309001044181500341e00320b801242e03101040c4658a400701e005041d0821864258008002e0040004001c2204180c1000b040288130310141d01c0c40980d11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 583021169 1250 583019919 583019933
    0x70303110a090518150f1c12110a17030a090c03050c10020c0904022806020102040e07180603051b0d0e010507091202010c0303020705151f0302010206041509 69
    0x90742071000054645003082c011810300d54014112000c0c6000c401e00e440c14603141e00c0c45c00502c00154503020b203110350441445c81d40c4820031903140702019024400016102e041030402c1c541c0034420800804c85041d1005148174002031000c070001d403c803000c0e5403c100c071400030203c0f6520140224480ca85c641c1c51000100b1092880d100c0298442c900511800c01e0030340600a001c1100620703101903420103449117056448440e40c040d4405c0d4100c50101c4c21000b015003106000c0c5003c20a0800340720030900c0850b80c0380e01540100151051000280300c166554502103c01b0100a480000f00710341c1690b0401c00305001750051500244002407420603410b00501c1c1403a40c0d08030210b0300900e41d4a402d0740d90b080ca2006c1c4500707900004280780081030a41031844026481d0786400000741003092010743c00003031512990590f00130790307400b10903103c0080c0c0407020365402482c00e030343c0c50024402e10300e201c7d030000f51006890790440c3e9040e0041c0165540741c1d1104a050f2001900d0001d00c0ca44070101d441c00a184 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 583022419 1250 583021169 583021177
    0x150c0c1002070332010b0406050604120f2307030b1b070b0703061e180b030d080405030d0614090c031608060303090d0507030309080714040c110609030c10020a050f07030311 76
    0x104d000054450300d444200000c3e01c50070390100380070300002c003c140420303204940841a45030304000301d00312620841c60b264808103a0004126250a0b006051244d2000e000c180301d13088a000d6210b60019441e0a00f25610b80c60b03030607141701c0b1104c4040000c5800a03240d540f07029400501030800049040d9514400c025640001700060028000c11005002c1c0742c5900b14800d070740807240d1100300301c0d030303000480460307600c1240c0d0020b40d0620800720f0001342040400c1040712810711203240e0a00003a0341e103050440c0c801c1054040c40384a480325800040c03100000390241ca105d00c001c60710017401000d0070001902d0f800805860030740c03d0300040000c042640c40b42d00c1c84014040c400c07001031110f10318500f40202862581e400440c4181c00c03140d41005620098016041d004508031000110b0251030f4a0603074000043d0410910319000b072604000507114044003802c0c0b016101010358000c0b404c88030036001248121140c400c0460010b0004810000c01000a07102581c803c0c2400100c541c03005070001101d801c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 583023669 1250 583022419 583022513
    0x7110d0f08010e040201020d1101060521010f0903050910050f2a070f0918060e06090d0305041e03050d020d09230d03021602150c0c10020703 62
    0x4600803180d01038a07444000640108600c840e41080e41c1820b9000030b403900b03045961107007000100f2840030309505003907001400902c40100760304502c041c507400d4103d43c2c80f9400c45505195281c2130800080d014507028809034590b040d955245003504c07090402101c1020440440100300c42444142160f020805c0149900f01c0220b20003a07240e56050324215612028401142094020240810001c07070b150980409131106d0306000304601b50f848614584030b855080010b8449403c18a1010b041c0f8070114802e401180104191000039600640503001c0d03401c144c0d0300901c91100220041d8132080c080118105040c480d141031454262420700000a0b40c002c0c40b81500d516544030f0204040000015403243c03441000c450201030b04441c280d0550721204204400c2040c5a0001031f40b8035080c104484035109950f0040c05a5814820700c1c40c01c0e00103820a46004201d481900140d4620f8a08424240c2c4d4600080d402803a400d8219900c0c1d4103800c903a17844a4403000315861100182c00da910980ca40914 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 583024919 1250 583023669 583023677
    0x7080301091b050a0e1c110f0a031104090212060a0614090708060d0203160b070b01140915011701030f02090f010803090613050910030b060103051e07110d 68
    0x54100450207040740c54103079030880760880051082560030340141c19503014411a0511045825290380407030040540c00c40b11a4400300d5040a80d41080f040800c600c1d850138041d1804511080101d0600685074000d002c00b4103070b01c4041840742400d00c1e01c0e81140360003601c081d16001d100403c0c2c4481528040d800e840d80c2c1403403a1564010f1000011410414481d03000c01c070b0b041d1440d410f041e072002c0c0980002820050040c814801c03c4c50640d02e080024a110182d403c0c07102c4261584e41c090403e1581043c002141c10540c168000500007907104541c00e1000070080030301500e0b849000ca24040c0e03c1c4812286414402643d200040b0310025000781ca000714003034024070480e110030344104040b0307240051460528010420050100001c00000e498001f84261503042c0d8400341e035900003400340d946034452a8080040c01c20094505440c041c0300741105d200f0065510305403100001074060303400031240030301da8040d0007581800180c0c00d01d1a00d50000c03a241050f10001ca6591115030800001102c1a0702107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 583026169 1250 583024919 583024921
    0x2e0204150f02120d0902030705061b07082b1b060902010806031513030c0516081b030d0302090f040f0506010f030908090108041703151008072001020708070803 70
    0x205030092100710384850700344081d040b030100f140e00700201d60040d4041c850101d650f0b04500c100715181085210064000180385d01d072a40d51a1555843e05110410840000d0280c0303980012080c8000609503914044182c0f2003010710300c0300c501c080c02e14280051500030002c0c0300146401862040780780c034003c180074490104900b400c50001515003940501041d0299010012076241d916000080f00e4002d0340391300088801080d0350400b00d07541040e4410203485800358880144110100545c1c0c0380c2162009015582401034108001200500203078680d034140e000a0030301500584294001c2120303070802400b01341c107004540045001c41e50045070004507240c1d40c5013445440c0da0400d400300d803a4210f61406200349485540d5005140c00703280d84040c1401100c3e0003041c00c0006010003038018003910440940c69140038055002c4010081c2032403801a80c06c40038904801d0311521859110341034a4840403601044000c02c080600301d54105a0b2a655090100b50700082d0b50b00d0042925034000c50702c90b030302d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 583027419 1250 583026169 583026209
    0x70c080a0e150310031509050304081e0303011a0a1704030e040b0d030e04020d09050a0b100609080319020102160c0f170d032d02070b1006022e0204 65
    0x44a0188140611044000d0007004a000c4c902d00498041c0e0360f108151502006910b003000e400b424401c40000c1c401d02020801045002c40083c054450b0411140c413000e008040d05c103495180d22082c00f44410031032001002c07480305d1440b50020001c6c41031500d010321608007002c244d00050081a175045000964188074840249041d024804080720112417200d010912a640601001c0751450507500580e004603050602d4580d6501c0400529044810b9403140d61040c40c044c9444d95044907110004400145d01003049485501000240c0d66040001c516007040380e079480d03c44004030a142c2045640802416440b0f4010030421052184203034800d008040c141103040241ca1038640002c04001e0780040c40c010b50900010b111044528a810005103011660047c3c2c5101201d00f03190000b168810041c1500c07044440d4010f05400703000b41e86841203030b102c030516000320b0401d91150b000140e10050301064107003140b04041d40c45810403d5a08080300c0030742915002d0303070400d03444000c01115120710044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 583028669 1250 583027419 583027429
    0x313081005150a051e0303031303021501060f1107090204091d06041208042112050703090203030a03020c1606030b03160b0d020307270609050a05030a0308070c080a0e 73
    0xb400c4100c0b1881403402c00000340104049551a1241d240300c2c007a02019201616426001c40d6003a08016042d00c2da00c1c540209910407403554079808400510611000008a810030326089059400079512000d25080c1040c00710303004440e103c3c0c540000c4c0100a0f0000b03200265200910042500328400b1400544084982d040c0070000d82c00312040d5000701003080000f602144d558440c1d030781182860055500c6504040e07081c3c2c0c1500d10300503100440700080c0a851500700c51041c00c000c400d840140884d1341d0b040c00c12402d454243c000290958010310204d016103029802a0a400444104841304801660f80341c08207042194005030100b81c0d10700160103503040c1440105090102416003204c0d080c980200c400c450320a080825030b111740e010005c1101ca070310501e228801102606204a0390428002c1320a520303e05601c2194003103420307020002441e0400700612802c560300103004d403118104a8501b44ca000900074001e03001c101e040301442c0006448040500000b00d100c1c0e65018420411105000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 583029919 1250 583028669 583028671
    0x904231b03040c060f0909020a0309061d0604060509030702092d010f060c02060c010203040c0e060114070615080303090d09170a02040c12060b070203010c1103040905090313081005 79
    0x1900c51508008001c003050602601c18110b501500e09403401d0395141000701c419401c03039041600d80c5800040d008015541c55004450614000e5008001d80c1c0b04084070030782280c45900f10042d0513000f0400003408902c05520281d80b101c14101038a2a011a580c001800080129160784800d4024045254504a4072210140084080e5083c11995041000d15100c10159100b44001c204107103901104548540c01501c255509a4009544a0819103040020541c0d5801242407610004000881a43c07151081400c6181a00d10491a052440d201e40d4081e280e074034240c03401c2c8002e0320000039140208000452240200101a01e421420070200410f4901954801020320710303444184051900c0105245113095411100050703145030030740c000c1d034207510140e406a030600c2c940480081c020852000900c3c4841c400c8000b00710b00306501209803205548200c402c03806a00902080c032103582c1c240e000c540c00c1110802140d06201410000e0401180c40d40c10054964010701c400e400a022a400390b6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 583031169 1250 583029919 583029961
    0x20070806041a0105011e0c0b0106030f110405100509150f22050a1203030b040c0509010e03060f0118090b0406270201270906060206011a0405030a08090423 68
    0x102c055140c02e00003031110305940c10030941d80c40c1c0e07002e0340c018007030080c5500e044031907110903004081d43e95680050018580c059000c030000d42024811000004000119401d584008201300001c0528070b80403244c070341140c40b0040d00800c03240f02c441d03070030072501c00504140348421110680e02c101071401d070040b44108042e0700540c60701c2d41d10284100d5952000d050281e422042054103604410305003100a41080082981c0052801080e0b1003009e40c0300c001466209801e8948882d8030100ba03041c1135070381000b19594600b0325404070051141d010802a100d080380e049490200b00c01900340c81e124240d030415101110300682d2507440200008207069003c5a00c20851034001058600350006482c401407810b41d0300c0c440c040c813910040d440e200c1c0c030780d9440034224000c41082110303100c1002070356841007070141c0702c40707071803042e6402000d84450401c940a882002d00500b203201916920f0300c45640241980c20341c820748824010003018505000c05034044181e072084812030802d441c403030744015400d22070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 583032419 1250 583031169 583031213
    0x204170714010c1109160201150e01050103090f060c080f01050d031e141c180507030602090a1701090201081b1605030712020c01022a012007080604 65
    0x100304829612588400c44000003801c00c00181d030100c0c6400e0101207051601d141e030084942c020312046c0d58030071020441d02d41150700204444940000c01030f0b580d002c148203046039071459500501003035101c1c1c0c0141c0e0384a40300b03d41248980c1e400f95a40e206461a440b0034400041d002c0c0c007005030158034040c030366005020a50703c29882e0ba815480c000c00c0987d40350702c1c804440031490801e1070050f2081c1790304c0f8402030308046220b032142c000ca42c0c40c002d60154000401340c4036040c85010940c4e02502007504511582c441d0090144074030b15901c0c030019400019680380d00c80c000310f0300020051001c00c100c11081d0038100c00040da0800501c009400940c0207040765200c034802d500c08035402404079080316045a0f541040e03440d07459461902520758400c0540040c21021000d0410f28482c0d00020100c208400980a8030607125041100354510368005a1044844002e001d45030b002d540105002d0723003002d04034000c00c0c0089001a03002880c4c015a98030140c500c1d030045042100784001d56480d80b07000d15107034003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 583033669 1250 583032419 583032433
    0x3040303110f030f2a1b06090a030c08040b0408150a021606270803341107091a0103061a0406120b09040308090c0414010b070507030204050a020417 65
    0x8805402404000d10840a4607010f5002c546090018808039025030f49091040381701508000303034881107402030000b1105079500d84048003100d000100d86c03544141c03407040083c070300c001068500302c80d1442c840500366500f1008020110311400d500740103002400140c00100390442c090211581103076801800c0b12070aa00c1031080300407110310300c603003008480d4201c1e40105e80c2280c0005081014500c0494060510304000d0f01c207000c04c00714402440c401c421052070358400725880b503541c0800c040b9090300110b51190b2100341404044c01210410030000320941100c2986440d80d101c10100c2c0c2c15180c4007400c241803041022003960f0f050040402500c6110384d000040548941400c4250040d0700032801840a9808450000c03001c6902039602c2c02e4004003041d502703080030304000d80114000c3d207408500740a518400600e6007014001c0c400b64407048152566240e103030240e46102504942c0049545005244000001d80e40310301944d40160807038a00180c3c0d4a00e020039400c201400660b5031090740c2c00241e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 583034919 1250 583033669 583033687
    0x9100801030302060a1b0e0a080102070b0421020c060705012d0b1e04180602130509011203020a0b07090812030708090a0c0e0c0c0313050418050705151306050304030311 74
    0x1441850b400c910034101f4402003460200002c2d0320b883c481d0880240d40d03102003030181c2484090300d0860f0041d401254102080a1144407000581d24070b000480c0c050780c0112040d4146092480081030304070f0041c80002140c14600e44900e03810381c0e2a400140c0000480e03405444429414400c4650b05803048402d10b10010b40204294002070000303511a00c55580d9141003043e420404c44010103007540140115941c1140e944000010702e018040c550003070a030070002182d00442001c54041989d0160014400c0b000d503913403801003101008003000200000280c0010300141d0401030f00b0503c20312040480d440c0d180448000380042c0c0c1c014418000c5c0e500c6000002c0104800030800d40a440c851404111240c3c1c8144c23001e141032003006411841c91000213460003000c15142d120600781e03001100c0500c01c00705071540c0310308446541d82c00580580c200100801031450001c20045c551040c4041542c1442500d2400c900e030340c1c103e640100c01084001041200f051351500c41c2d2540074044070000c50500c0400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 583036169 1250 583034919 583034951
    0x815100e13110d030c0b150a0f14010c081225020312100312050d02071509110f060d090609020a030c030c0801060308180109090513140d0507031409100801030302060a 73
    0x2d00c015040a1b00e80000c2845086200078407031121001400306640c545c0d40e42120f608461040c810084007070000441e400d02c1c0d40c400c2c002c501e283c58100305064240107a00d603000045200160200360b50403855506c1c086007580200142841c10010340285880d40212010403140c018001c000851098200e6030030f0000a04000f500c4080c00c00a1408a4903038603400d9901c8020301c00c41c00040d01c1c454800c46071030713007903112a0090302000344160454004050390406211551100040080e4401e105100c08a1500b81c1a0322010724140540c40109583d1842e40114420b04055041546c40c513111401c14420f211400a114000b00035120080003c2403031138981d100301d03024188892001d841c0d010485081c036841580840060300c191141040182480b042c100403003001a401140d1500d160410b4100c017400c0030800b0307013220000c5d49510b45000c101d584d003101c046100d0511182d0503a41842580c081d0303228628038280c00301c41a22a8003640d411420007900c0e2001c010900181035007040c0e020700c601004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 583037419 1250 583036169 583036187
    0x2b1806110c1213080a0803090c030c01050d0c0302040b0c0604140f0604020d020f0a0b0c0f0708100504140a03020d0809060610050d021209011a03070815100e13110d03 73
    0x124000035030700c4402100c0e0700f4481ca02194065901481803091440904c5016001107005860000450700081d41c40814907071a84c04445850b408180d00340203140204140350010f942c1300d203080ca070042c905611041d01901d1030300011101c503000d500034410401040b180c0216520b885a5450040100002620803580d03502c030001c1000b0f00820700b20329084115140d02d420000c3e1407000416110b205525002c40d103410340c2290500c0303440c911881c49012ba48443c003084240c2680d126001070180510016225000b42c04040c004540045c0c00c58125410520b06001c040344803403080d805080e00d0102c500004084c4840600705d4001c9400000071b1040644e10512840d001096608189880e442c02c0c582540c000c0c0198907160101d82d43c94001c129040340b0651015141c1840e000f099607145110394145660f40303401b07000c1c4012a0780010710b4a040c8600300c20040e40c5c4139803003a100e140d800740ca0b11200e0714200c105542c102e041240c1c22000c50304101c0d500901c0e82d034110b020341e02540400891784009001ca25 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 583038669 1250 583037419 583037443
    0x920091003020607060f090b07020115050a0306020a020f0a050d0f1103180303130e0910020705100915090602090a09150b0304021f1101050a0606052b1806110c 70
    0x110004101081002c56081b842c1d207624502d504102e5040c0318144404c3e0024200e50302c80041d46008865002d0000c40600c100680340058180c003826411f513654540291320100100c010b500c81d50821400c007200c00c0200012281c4100c0141507813108419014110702c01141480c0309014490003594841c407800400c0ea201c0707449080300e4400c0d0300403038030200381184a05403588000840540020940103c03040300c050085088000f151000810401c00c802240902200200141c01c030788008281280e198216580250065400d49081c00c5400740001c11031301945011983d075900813860141e80c0c90100102c10050800e0b40d13042c00740c0d1380c00c2c0007480d200003c2c0307020700d65030148042302160564495440441c1026042c0c201090740041606001d000300010030039070306403503083c00c000500f2080240900c0c070440320161501c0e400e244445180558103018030030190300c50204409240403061160140350340d10300c002e00001204041e1420501c0560314400010b000440c1c3c10400310b4400c2c4000640c1101000b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 583039919 1250 583038669 583038679
    0xc06030506091e0703270c0506090d1704081e0c030d14210a050105120a050d0c14061504060e0411040b0303070807060507080702010504050703080f0d092009100302 72
    0xa80e0b40b52040e8001c00c0e8140d03c44c02d070582400c0d0200380078844115107900450261f1616410070b5568000c0000343c2c41049911600320101208002c000b4500f42c04072006121a901c6c9241095210000140b502002150490640e1400b907450440c118050200d004054130607405031164042e00c040103409482c1500d0700d4180d442001400448003251602c030211070380e01e410000c4101d400c0241d4403001820081c02450302c5041210404024a03900080d00c40303841d5404005030a00941c13869046e68101401401070707401c2056904024201501800014450038003040400480e035600424032080342e0160704900310304a6140d00340004074071980403007401600202c0b40403404243c1400460b0a6000d000d034003c00e0b0b081e0201c2c801c4108080d0b5001540308615940c0e4641c4159220f000403420b0f0f07141641c1c00741080c0c01035801800452a100e004011400f0138842c000e16110307142c2a0182140d0f0230f5101600e551b800382800c000c0c040c0d203030128003000c80e030101e402440c1c5060590104c1e1080d9903d120080c0b00d6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 583041169 1250 583039919 583039921
    0x3130209092e0b030106030804030c0b031603020313080721020106030305030f06030a140105041e020108041502090a060c0506010f0602060106030e0c040c0c110102030f0d180206070c06030506091e 86
    0x20140e01d80000071840f0000d0020300c552a0342e4500030200e074100d40012104d081d000c0c0008105902c4420035a84108440c00310781180f1034548401b80c00035480584200a072004074142d010115800d18000c025582c07103501f021701c5160218034a014a04501b4030030340c0131a41410004c00100340d2041c01d5030b80000d441408140c09844410003c2e290041400d4024522803080203900314441c0e041d405648940e0040c0310b26202a180c0d0070b205c0700108003e103402030218414201140110300d42007203400440080e55401460030000000058207061903501250004802c1c1150804200301409600e00600490002a03051404d0a802a480704814005c8004159841214070032a04040041d5100100c0c0a0010024000281c0d00101061600c60058400041c0035080c44500c0d44000b0460743c00209540007a41484444044100030b04a00306401080200b41001d20025035a03d800078240103103d800801c2a1528204010b003c0d9000201814441e440c00b00410900030028907110781c01542c014040052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 583042419 1250 583041169 583041253
    0x10050a0f08090c030109030918020a08010303080604090c0f1809020d02060d090c0e011d041101031104150507050d08060102060406390212030c0712140313020909 71
    0x5030000c0c000019516600b44401103050582101c8c5c810103540307101c3d0b01c2d100d030340200341c40641c1603201d0341d80c0b0700000a01c1781c401000402d20075064542c00020060010883c3c111948907180446400d0304401d05c4030780001420005404082d03211816100c5c2c1c0801841a1140e07500001d20350903540b4000303401101c0020741c81d001c245850b81704070401540502046005610351038a410611024041e91340080c51900030b100508840e8580a0300c11540a000c501420545800440c00340407048040c1d03060712024800851210545907004419583c107a1300d283e11000f66080c80d03481d040040d01030900f8040b0800a0219690340400d0481e0b0007900f00c000890b50041e5000f08507042c907030700400400c6909115410080200f2201c038200607500c11395003103a0040140402d000d40900c0700361414040c8007010803e00c8009440000c0c0023440d0300381030034640c5540700000074080482c3d000710b8000560402041f000c034210b2401c88d000c2600081242c00401d0b1507c17184454000070203000103000c0a00080c8404008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 583043669 1250 583042419 583042423
    0x402090102030c030414010e240a02030405181e0405060705090a080a0b0a0608030a09140406050303030f09060c0703200f0304060c0b01050303270402160b040210050a0f0809 76
    0x401010108907992241c1c1c0c2e10006c05000300350320010380001e800a07a020344618055283c01c0c40a424070843e6030400c0d00b03101106000d50320001c01c000550105000c000b8140e92000d0f5180607a02622108030843d02e412038411700d500300030000350600c1d00c026030144004200002001036105c216410700c280c0d074242400004030301509540c03010b501c612039001c543c0f04010038001c40c1c50003180312540c00e00c004c40c0ca805240e5100e01030044540001303948480c0801c14419a21410566100060310015006032110080b038111f620858880c040244000c06001c0885420801d503a0304c080c2201c0410b0900070555002007400a0164005546803940d50781400c180c981400003250703803440e100880c0d0f40c82e5511800138080f0002d91000350341008401d0000622800c1c00300c100d4006001c144a544044030500070038103020140b410710f60f034005509002a4880e410117200141e0139a01504c032451984ca450701c1040b048a1003020035000b0004103102c080321464101d0140c0117a0195410400c0e80c598070302ca90a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 583044919 1250 583043669 583043677
    0x7060507030c060501180510050f1908070e070914150715020412050709230c040b03040c0302040b010f05091e180115080106080414030c0a080c010f060b09040209010203 74
    0x1510551505000054084d0091003405080b0081001402640e40b00c0002c00c403078002380d201b6240c1260226013200a1031400705448822500c41e4100d040072603807900300d400c3c5802102d40090020030100c0782030100c010b40011021000303041603c441c0c2d481407004008140c0380d03408810000070f41d540c08580e401c00c00080750326041100c42070f40d00c01c64803940e480c0c2c0c14046150154105841c58007070b03178001141800c1d40340540040450000c0350041ca03803801c0846218000d000a222a51450f03050001040180c007400041d0300440c0141000f0032120304500401049603006c12a040c10b00c00702c920f10031102a041421b46804c2c00080303a810901c407201c208140f020304501100240d04c03140305c5404200f615a290140e074182c950351040801c803066400b0003903030151001e00440d000726800300300150000740d41c7e40881d88402500c0c801e980c1007248112106141465403403048030030705000318141e41c0c00c800920480c0d080782c40d42d000c18058980303480d01040c4103105150350f40b401260001815207659000308115 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 583046169 1250 583044919 583044923
    0x11a0a0f050c160f09150509060d0c1401081503071a04051309060e0334140d020c0f0604051003020405060d0608010b10050d0506010e0301060602060603010f09030207060507030c 78
    0x198070350f10003406181c0c002001a01501521114040780072411040f1403089504144609180c21074042c208070801040c8070300102420781c03110141d146c0700001000205290020060310b008120494510b80003d00404c600802d16003c0c0d29244441c10340c01d96000030781e0400c0700d03200c01e03581005030940030100c80d0701d1085402103500003140420b18484080154005245240140010400410440d40795034481c8184840030210500c56000161403545641041c00a00900314601c003100b081c996071b60b1000d811090380e021a940090208900c0f954060220700c4251808407810300c1c48801d0403001480a014501507a40203003202c00b0140e581c94000e03811100a01402450340d0740b201d520408850207081903018043c1d15500b0300f887e1201505001504403546a07164440301d04050041081a000304001000107040080c1100d2070303030107500e00307110710000381c0b0141d4060111858184140346c01c0d910a5015650040d03e85034560740400d81c0403c0400613102c0328039003166141c0c01401c0c02c4071a81080b41d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 583047419 1250 583046169 583046173
    0x204060e0d1a0a2c070b031314070f14181612180c03060c0e09041203060315020a080606030702070b0d0e0d030203151e040e0a1514011a0a0f050c 64
    0x951560740541c440500e44e03104085900680c0c03034014118150105641081075207060119071000903204002410401030382c4822156411b6943c00c0b070f07482500c6240c0c02440a41a1011106424280303100c0601c060400c0b01c520b0180c07410910640d01d40790000b2010034040241d4107013065030038207558010015900e12113070250f1561025003040c548075242444100c55652404c0185a8210302680007030000d058000c00b01c02555507203443d41d01103120f4403060f000c1015038076180400000c0320340c0910041085c00a00058680241a41c0030b4400c0b0000781c40075215030014070030007034000c0c0d0003d909000c1ea9041c4c14006d40f54803a00314005d020f80507034140140c4c01d000d2101e4030012154958007940c400e8042c1004a044142d0f1003041c880308089012800808000d07114084201d410b02b80c004d10150380d400b0003211004189034964010924030040d41001035600d0300308821007000445585030150003622501d0f42e0881c00381058000c0c07442860507500503c2802c07044132400d1030040d0700782e9503500361402c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 583048669 1250 583047419 583047461
    0x181002090d05120a020601061d01050a0315031407051806064509070f08070c06020423061206270405070501080106031107020d02061c0204060e0d1a0a 66
    0x10884c1c201240b1303000184180400011070900c0b030031441c03d44014403200910004030b034200440d225800f208008003850f80340e040c411b07002c00001222030011809584540900510070803442d04007040d0b90b000900c100c0d0284030003100708000c0b2959a41041084641958500e0055080104545014540e4100f07044440c054040c0340d4030101d01c800d503075008080111400b00100c0070000007001c10f503a220f002484070580103c004c0d020700e03100b03900484203090001d000c940e00d076518000e0364415001165041b0f810707540c0d0000b003003220740c5007034206001f156001d0400c80001000d2000c500c0082c50346100d911302030880920f1410541110b04144c0c1040084400c40c603040c14001e6031a4114071409000034045000015500e10071310500c20480b0018150500d8801c098003003180581c0c03102c406070392209041103d01e00c031030401c0540d01022400d0540141c3c90f64505039002c2c059483c51a0200c0c05121501d90b0000020482040300e034100d104c2401580070358903041122030061100394071012544052203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 583049919 1250 583048669 583048693
    0x191d01020307020c0406140907180303050d0b030a170a0c1a040b15130b06090d0309140d1221020a3605091506030a090b181002090d05 59
    0x3400541c4110115000c95240c0000b010600c822211288646000450080401010362900710801034011a1303928001000100014264940d031032075901c1140440c40014000505118600074820004021006418030000741c0c0c4481c103100100ba080269418400190310013501e002d680707901c51031600000c2c07160540302403031118203d140040d103040c0d039600460303400250140c007072007560002d120018044c0602d4440c01d1100c0400341c002c150303d40d5801501407203042c44980795407a800821b40d0081d513496161301d00c4c00b82042614090403445034080c6000e00015004140300700310f261f540020618100039210054101c0788420100d00701c601345078500004602c0c050765404600e1882d030b20b9403041d140b100c51031640300080d94a00000b07251040c40b04176042c200203500e0000d00040c1d00c43c4035104454080050900003813980c1d03000300e07101810341da5a2000b140c24021800700496001d0010b2000e030444514140000b5910071030440c408a1441d0001910615915100f42c0b6082169000049400c00d55082e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 583051169 1250 583049919 583049921
    0x70306060609080615060a18050603040501090b0a090f2015130602061306090f0506040b070e180a15050d0609020906060324120607081518191d01 64
    0x380c8100d500510580307005c11203041c540000f003004003030001c28281c40c1c410a07001c25281c400b0b6010740c0303569810040c003001074540c035001e00842c0311b107110781c00004050429203012007840c0400f07800011007c2c5025504800550810490450642c02400c281d0090041a404441c80881c44048982060042d40380d03202d030040c2c04e400703404001100880b4055580e1603d074205d945100454110707040c0d200001403503000c074034a079003c100d005001c0d171040d041c01d18081c1c540c54a4041c00340c500b00d80d0190410208000140e0021031180c494000311007256000482003180d0080a00c05400000141d5442ea00340184002d15481c41c0000c010103803038401400018100040204491a8268000c070005000074881e45046402c580c0b1418070500c0c85040c01c0d01050329000c640c0c0da1544940d8100001c180440d0b0303080010490b039407240302141d5859950385002c0400341c020f448040301280c000c94900316010a014041c000d82907003c004584034900c0040c0c202d02007009080901120113142d001d6010a00c402501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 583052419 1250 583051169 583051187
    0x906151b030304210804150608100902130207030c0602090d020d050d0f0f081611010c0503040605011e210f060e0f0708030d0203040f06110d05130305030c030712180312020307020d0c050703060606 86
    0x2c0f8dc0740700844250b140d02106a220720400100003412540958001034425030282072034060140484040780e0701d0b680850701c04102d070300b4191441e910007171400900c0f591007a1510302401e014904464a003644800240031520041c00c0e550f00e0030140c019011b43c19105421080d4094072200007440348080140009d84a5231087d14107440d51800e002c008116185c001e44140b225050781c502c80c03d0013500d403809984024940007400400c0050085035240410740c020540001e103805040e000601c2c07481c070820189054030750b03a280b02094000d01401c0001d00c0c0b011013541d5410454500c003503030720340c3c80f031a00304d200b85405d03040240600e203003840c20b07081121000050030801403120410026a1550400080304200103500200014010800504500c070402c000d945c2280c10360801c0d1718204002102842601c98003041e080b0398909421404086c55400894170881c0d500700001189942800c1400039100e1a8042004003449950b144640030801c0c00c1200344000c2d034000d1000c00425403030b00e00003000a0340c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 583053669 1250 583052419 583052423
    0xf03030c06090318062c2d0a170613080313110d0b07110a08040308090105130905090d0905030a0f15020c0105010906080c0906151b0303042108041506081009 69
    0x48001051001000c0ca03040d491050100608210360910b441000708094150b80d040b41f141c2c03e480114003034098450b4030004010f04100c443c200200701c541103484c0e2402d080107060000e510340409045012a46040c1140d80000c82546041540c0060b030404100302020f0007400c40d0004c0035940380c6410700042070600c0d805464141d4401511040c602000d50ba6201e07110405006080200001c000107541c4038000d02c1c0c02c10b4181461418110410300450030000f0580c000380b0319030b40307030810058022000e100c03e08042d0300c641880300445040102003036503096045401031501c11040310302d070300b07005400010700c540c0da0410000707640d181c1564120314003a1000384a0009400d080ca00c010852020110b1003200901340504000c0c5982d0380d0380d0030040880c203440c1004148090400180e50f2081310380d00f4071380101c2c18082c01141d0ba41094500301c1011184090681219005a402c2c004070b0703071780001d2a0386c1294001840c0302000c61184840d030024913160744050041e02c2090660700e1030201541000c45c00c98 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 583054919 1250 583053669 583053707
    0xf06041211030307181806030b1e1b070f0c050f120607030f06081006030b0109050106050d0f140403080a0c0e060f0c030705071e0f03030c0609031806 66
    0xd44100054032504040021650340380c00500000301014032525100346040d04802202d01c1c069038821841c907003c500ea03a000015162a08810310500600741c0d00c0f182c104030015102e65040d140d03c607104000b0400904140c4d40508400c00551464010205498560760400c0d440d6904400e90307e8070314084280c80c41030714002c04501c0c1c000f03612403030040090701e100460350000d8103039662140c1c030403001031603c0980b03505c4540e5101d5000c91103403000c1113080c2040138a4080040c1160560402042a0f241603202000c1130781054018000c060780300003038070000700d0100e5002c40c1d400b80181040f00500b01c1300720b000c00a0300e4484100b206042e0300c803403154044c0701001742c100201c803101071088a80e44005450103411201c208044c5c100115242d004180000d40c4070140c078108038040c3d603214200342443d80101a22110042d2400f0003000c0240c0345d4005100b0401840105c0d86540d40113021000a40700c0586555139516902e02494090780b0050402c0b21103e04030340c0d0454580c8000341c001000c03004400100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 583056169 1250 583054919 583054943
    0xd090b12060310110423010e0f01120c030f150b090105180d0303020a03050703090519050708070801090c09050405123007090e150909030f07032001020711060c01060302030f0604 78
    0x40400c03a042c6c1e00542410fa4468150390448024800030740c0b09820000d0400101024400d40f007003640c800d8441d8011a6030740401e40a0792031200c00f080e80c40502025550512094003002600019030894240150030308280c0c0e03e4895040b84450060300d0420103640081e0b5040000341056407640c0108090300e090384040040351a8000100e0441c0da010340010304a80c8023860b00b501044200341d0b4036481921a20848800d02c0d2a0000c0600b840400d0380460724581d151202141005160210b04000d0000d0200030480c41c6011746440b9039540509122074220640055038041180910703c5418040c0c0354400814200040001d90b509031040031181800003030108000884c403c0f03411601603000b40030020881860f008130004011001c0409803145d000f92104000d0782c00b0f080300c00750103000100d010b0303103440566281c000740c43d00002086c640d19811a92042003c000000c0760003044c01e0300c500741a03034026110507a2800e064010046604080d50600c100e01103000ca04d5000100984030340d200c1c885103602 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 583057419 1250 583056169 583056209
    0x6081603112e3e030c0a050607020c01020a0b060904150218011101020f0316051b070303090f0e1b0c0709050a0f0b0108340201050403020d090b120603101104 69
    0x180c07244000070240c8180603080030801442c1c240f082c9052641802d090f60314040001d1152031814202060071103c1d0f030130600070441565014005400c03c03a2081c0003404143d01c0e01da550410707211006010502c00c41c100c00105090200388001d0704070060302c1c0903045548480141c461011261021001c1d400038001141e90001c0c96010300a07190300700c805140450640d1604400c24070603000d1200c4000410009000c14502c4900c0801184034841c011000fa085460840c20020058034203500f0201c0b0212030582c0411840d20758403c80c41e88060074640350a6038000160661345039210303121140c1881d04c1a220003203a85400c6902c414014030754502e0800400700b5007281542512005200c5c6400300c0c07040e01c00070315240318001c480e0b1100e4541040400c1141c40c4488030107814845d8442440050b07644004201c20960100b002c01e400303103950f08001c0312051801a11616610034595540c10035901c8001240d0507071020400f40c256864a80c03800d02905083c4a03103040580c11078860750360310303001c86010009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 583058669 1250 583057419 583057457
    0x141204260f0a08150924061201050607020d0605100602010b0a0302030c01350f06010806091f05060c0120040e0103060507020307120305060406081603112e 68
    0x281d20240a64a41403124818055940000081c42415001039001100282d55900c910291050248525103450354042110b907031100c0b0300b0103080c64060340701001461680004c0c28001c904448044944582d20706162020540420014400a00483c10641486a100030140c41c21054403501e41c000c11400f0a4041008070142c0365120203501a081200b45091035441b40f000820300080071102002c0745081d902d206800100350b207200c4005520f540042c1300f031083c80c400b0160303000340091a14071058240b90002428a10010300050003807100c2045d80b022520001c0308420040100515264446440d24055406000c1501319050790715017050852020b41892000c1c0c17815150070030a820516030071951030000a050190540c0c007548014410600024120911150085e016940100e5039040800a100c2920900e40281080d0b80010b0a13035440100c2550400c021203402c2640c40340c054014802282c52801140600b90303a0741248020140c9000c807800c2003210943c05552801c221480c0003880072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 583059919 1250 583058669 583058677
    0x1c03020708030f100f0306020a1106040c060e0a030501060b031f080d030908270a290702010e030304090e060105060304020f040f1d0a02040e0a0506010614120426 71
    0x4003070250a20224110110150f1180d03030249065960550503900c0b1240c490a03040c140c0c0c1304890450b00015000e0707046920046e030310045000207005101e20b05007580c480c2c0c4198910302504c1c0801000c400403c2c00350740d6100e0703502c1c029038200008014064454503007102d513500c01c441018108480b400c8504807000280c1d08501181c200310f0240450442ea00412030160400040642d100e8005000d00d52007082c000e0840a20154035103400211003211600740043c0c82a660b006203050403207107141c5001c80c06c6508a44164200070181581d036049544016146d192122078000e405110201d40440c04008551040a045106030100e031996070f13039142004128030089400139040300608018039014141500610790781541c801c0d003c5117190080c0f03280706804e52601240070055001900d19010f50a0038030501c0e85001d5a040580b50070116078855554540d01842480d040092a94a009030240c404040d511446c1950780c45140700c3c06c7c0b50810300c0c106c00c0042a4580940c2003000181a410202c600322 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 583061169 1250 583059919 583059923
    0x3150a1e03171e0a0306030b0c0c01060b09010905040b120717010b0a060909021b011a040609020304030504030210030e1005010303111f020c031608071e110f040b0a081c030207 77
    0x40c083c010300724010210982c00880c400414140c42d20f80c0840040ca50140d1244250320610550341c0b107900c00c0d0300090a488140d03201e003003071080c02c200e500c8090364807804c1c0350203a44050310081804803496002c101150701c501840c44490144010200f00041a06001070200060f030000b88040b01c07120b820032401e1500c0b0b10541c0d0100e80c0c2a1000c000310b48142c0c0240981101103039400c14108074007940907007134440c401001c95113040c0d1505609a1480c0c544103481c090f00c12060110b08601d031a56000d08148600d000281c03091101e01040e103941031103504810200c1024034266804000c02d41d045002404080c00100e01007840c42003280100d5400003460704400017141c1612160f144010701020003540440c8404906020030010440c0008000c3c0780307410313a640f00351342d030558480e0681804107009030a009410352040324014500302060040c1a0280281801c50309828442011400200280340d041d0311a50000011940001d400001041400311404400c03c80b14181d034640c802242248115580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 583062419 1250 583061169 583061197
    0x6170108031b15160201060603200c0304030512070b010e0601140d0e030c06180316170d0f06080d0201090c030f0f020604030c091a0603150a1e0317 65
    0x80c01442105902d1900801d0720800d4074008840d801c18440b0030082290340f00341440700712541c55040b030350900c40c80000342801d250400c0514148401400b03510040940d1510100e0041120364080c20140b0460b4002c65005044452280710307100d6840c0396811404086d01c6d5603141400001c0e800211903031103803103450140d54621078181390002d019160342100344019910396031080e010f085200104018000c08107810010304580c6000345800c810042c19000344245504140700d000c215003044119102d400d50b00801c0c014480d0751178080502c45008405c0e0365a905800e04406c1d140106480d8810410782f0404029203040094903801a0b00340e50610200070103011202d9410404140d6100003e092248202c103012078501150300000c042d60403641003a105052819400c01c020042481540e00340c4130480e2101c4074240c21b410000c0d455010080c032255070390062005491a070307602c0710150030107801e10007680c0907640110000c2c000198083c0c042240c1c6c80200c03000448803015000281ca002e80c0f14140703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 583063669 1250 583062419 583062427
    0xf030b0913031805151b0703030818151e06040c05040506030606090603101d01030c091e020406020f060a0b0d08071a0115020d0c03020c1e03060403090617010803 71
    0x907048034810f01070100703540c02c000c01600c0490141c2e43d502c540c480c0710020720806a141c50012101d0140d44511009003031030307a03001120800010f5002252a40e119441d103510901c40c8169449640c1040d12900c80ca01c0c0c05a5000300300710006500302c0c20b107042d080280a90100e9a40c41d0410311045840c00494040400c2041c441044140740190045a01c841c026144034100881c4a0104049401c183c507401c804468000c410f002104030a604a900181449600e480c254555150012406c8443c050301c64000d0300c5c2c900102500d00400e41102d00070032100411913965543c4e14009483d448800c2c00c0203102c0c0104c0010994040107801902e4a08000034000503c0c1030b09a0750b6070045500c440700445500721503040f20440c2e21310145400c0c1c001d280a032100d2b8009818010000d0810001d82d04c4d044c1805060020030004c6a800075090741883d40a8581280c2d1103168290307481e0718096556038035414407e0604001c205540510500c0482c2c48948826000c489659141c5420030000d009003a03d0b0740c0184 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 583064919 1250 583063669 583063673
    0xf1d06030a090c0506040321050f0909040303092f0406050616020312040306090c0e0411010e0d15020a02012a0804030c05010c0314090304030b0f040503190f030b0913 73
    0x40d1040b811144921000e4480a5490340803510700e400952003602e80e43c500c2128101da840e4911946101d8590a00c1c1c44c9241196181e103828050090190083c00303004820009810507000340d01c041c000a401c00740540300c0d918540c12528804071070740c00080400941005114050a0078010312080d100c008040a09043d000c40180580100c41d603400e80e4584074a0005c4001c1d03031800c1c4020400f541c0138810208800c005800d0641c10308801c1e074485000f090441c3d01f0080070541d040d02413200c104091a0146610f4080d40001e210f401c400403025200005118240510402c540d0091071207450f260020300100c00300444028800800c1c45080640d4540c03040c00620702c51240b844203034400d1280c204400301d01895107a140c03c40300d01c06002c0010035a21440540c0c122011404580d025071504015450300b800c65442c64407483c000342c040382070201568042401c02206200380e070b403c040861147c0d244200c15910051162041701c03881d0004c20324004070074101d818030300c1440e40300b60001100c2c000281c0300780d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 583066169 1250 583064919 583064921
    0x40803040303020415090f05010801030206031611011406090c0301030b0a0c0306120b0a051f14060c06100e16050301060c02040608010e070501080a1406090a0e0105070f1d06030a 78
    0xc00480425500300800f0428018400094004402566400a007103050010034000e1082c0c1d600f00301e040c010702d40300410041c0d44c0d4204803030788504900e003440d0251110321811342e54520500060410342d400d051213802c03140d800c5180c4034481c0000b00e500c4420f5456491411185200a0102601d0041c2003c000382400031543c106441c000715624000421958030941d41180ca211108112507181c081d00038841074104034041c05800203c4080441100244914500403442c80c40c480c05007100720400d180c1600307a45400a69442c0d000a000780d4141c0d00e043c0c1c242001c1892607000b25004a1120008540c0c040802d01180000c110340341c403668035590070703c2c4083d80e01c100d20100882c3e01c0f54076000d0205d014502809920741c0c2c040c0040c020205141007100140040bc80104ad480000d850942c0010f1403402d510640c5030003c000740c0c0c90358000d844181b89440a0002c44142c5c044560030b1105000c08158803a40b4043c00c60541d503986240c600304090070302c0301c0d50715041d40305510440910100302d101c061 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 583067419 1250 583066169 583066171
    0x806060910030c122a0501140906040306050108190c170f0d020606011101180b07090801050c2a0d080705041e090c09062a02040f05160314040803 64
    0x5524500e00741c0c02d40c1d9540d190f400300001c0e00646504002511158200801d00348a160641d15141e44a03051003070940081d88008082e1046a042188075204401c40311115412200f111901803c03040e40e65449050440107407400b80f0900c4101d22400c1050040d50702c0400d906500300f944412900fa00501c1d0400318094078050700d00325021406a4000b94404000406c40c2c0c00c0062901c2d00a01040d01d00400050002c03030021454001c0b590600c00c01c1f40c203c3d0915030714203c90f503170302c080c20040325141c0300340c01c56018026402010380c56190606105180e00f8100250882c102017100e91450311860005d200c0032165600503c40c0c0070788c0080ca1041c40b080c00350452540c00700051038043d0800d9aa010862044c0e5048071303504a9020054074140702009550041c48035481141c1440c02301186404d600034401c010342d10f5001024410615060144075440910325403041c1c00501c18403c2480400d44213000744000c0c0c1d040c42d000c510070341c0440305981c002d00400b80d103041c0d9203b0510b106ea441d0384034a100e540c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 583068669 1250 583067419 583067431
    0x1090503210904060e0405150c0f040b030c040f06080402030c0f030c0d060e0307030309021002010219080c0f0304030806011e140322030203030f2503090204090804180b040608060609 80
    0x20315441c3c0030400c2d00b50340d10894803540c020802008c9400300c048070702c080410050003c0c0b00346070040000010082d8044200c404851212225544c1c0f039940340200300447c00365070840c400030107252030000380c8558442e248c00c0c000c5d4000c4007658150860f41041180081d244180c041e0142c00616880481e883c2002040442a004100c0414100d4074520f081d8150f9011410860200b41d4503030141065040113001d50032260340714002186042e004c031a412040d440d00800700010041000300060b400d411050075160321444941d2541d489007060303e4050400b1070100c80150000e100362100680c00d080d4080c0911511030b660b142c0030070050506400361415032000341068a49110100c61498540711001240505030003940035513120300300402c224400590242480104400c0e021120480c400340c54420001c550060500188412170f91001c5030140c20304c080c0c00341c20618049130000740303004040c000301c1d40300600c00020400d01410b20308110480d40280909040c1c3d40c00031002901030b00346400c103140c1000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 583069919 1250 583068669 583068671
    0xc080d09060e030a02010b060a090e100503030304080c0c040b0604120309030206030f0f0c0304020306070c031808071401020f060601051b0f0312010801050f07030f0618090201090503210904 83
    0x8a8140c9a0906882c400b00d80ba969550001550798071160b4207108180c038080084075075074600440d0b07900040c48800079004941031203c140c8042400c90040e98908001080c000d0140d035241c0c50b250a241155420a80c3c401c8104c0c0520000c0c07200131320300381c8103150b61034030001c10701801d19040652049403999625400c03010700030752810103c05a42c03a000650701c1005034844540ca145041c3c0d9240d02d164201400700007640d20103105001c0140c0e8003191042c1c2c41003e0745411a0409001c0c10101c40c0c050080c0c080c42e000b860f01d000701203422180031695909031941c442c0c4000e15405c1c2040121f0703a64900480c86441500702c0c1e00031800640c4034030014041c405800d03220305c41c0e444000111078200301845a10888503403000a001440c85143d64040c0e0041c010714008104510380310304912841e600c020801c3c410156207010203038145420341d20a01c041c03d6081d5a80c184901ca0f41d91210007050083c2007a40414042840060180b4001540041c42003a5111441c5501c1824222051513040003070040e03802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 583071169 1250 583069919 583069931
    0xf0b061f1b200406050111120a0e1804021923040b090109022a0a171b0c0316120f0302330703111c0603080f1e04060c080d 54
    0x304412640c000b1880c0b40a0168581e10507001d8204801c5a4085d8805814445401411a00c00401107900c010591001c0d030b003190b880980300c104445600100800e583d110022010920f801215130600c07070310480c82502c9a13100c4050300d040c01c0c01c00103c60701c41c01d00414500b9a00903a00c0d5160360403060000c1c00034002203540d4110000043c284d0318241c00c1550340c140d000c10380712201012403400d120501c2040e00c520340e0100e590f1039a0358864841e142d01801ea0103003020f80e0481c07640c480003290002555100c0c107003606d034040700c00030392102410942c0610a2150702e2034041c80c00c90203a00402122030200d4102c8816142d0f9030744060100c840d036025815405a9500e040b040344d28002d0320701d0b41c4c07030a69060b0b022419540390403002e844400340c40d00040500c1d001c0e2030510305503903100300c0e004d820351886e03500799031050b04074440058241c94000500b1000045840303441500240d002d00107448022441c1841c00c5128070003440c0030300075171140c1c0c0e002800514a600200b030849005040d4488694408601 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 583072419 1250 583071169 583071173
    0x605151e070501020708271c020a0f06020106031b240c1e1202010903051b01020705250e06030d2f0304060201060e060f090702190f0b061f1b 62
    0x8a82210070155840c0b00c0c00500000303403003004c0a11251701c0141d6010a03840c0f500310000325003688c0d4070101c01e84034800c0c81100d1100f503550b0200103074014442084048019500c91030024060801840204c802102c1281944404601da208000a89141c0c0056101030102d690031401c031507a900014600344020000d150020a000b035609551440307240700c00040303410b01454100106121150070034116494105443c0000740e0200445d014241075420b864850580071070890300a00c500381c001881407007070386003209515007010030b030403200c02d1810300b0050f503c2d545109e0b012552108594062b4035030002c2d5002201d042c06003400d00600e0002c45a4400e480109034103140100c0f2b401d5002c210b10f588041401c000c1c0d03035424000c1101410701000e40c0781f584d003030000c0032440d0f080700000c4491042254600040e00d0901c00c02003021502c408010b02100100c00e4182407038084c4030450140c030801035260000b03407241004003002000c8400c062644c0f0384142151012501c8145c00d132180305500d103480d803107000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 583073669 1250 583072419 583072421
    0x1404110609153708070810080a0b06150c07090c05210402120114270601061e080402030d031508070b030a0c140f0708130e07030605151e070501 63
    0x42070700c00000c42c1215580190300594401c40c9014060f035010302c02d00548034503a100200e2900142e072030500c07403c1c0342c17268400f640c54040681c00130325441c450070750940103024003100c0c80c41c05800305035061310009034048682c3c4014440c3c0c0c400d1101503448a14100202042c0b98001c1c0d0030507049290050030106040340900d081c8148402e100014150340e421b0100f54030301030b5548aa0078070604004c0002c500350016151510303030000c20084c816084040991152030a0074222001540c05a0640703c1d0313981c40f041e000d441e42c40c407a043e00c288000821a2442254004c1324240c0c0120f030024001e050032200c60340100c0c013801d0b60715610403c0e9903201a002402c03000400c40200a0325aa0b07005548030320301001d040d0215620341c0001805c2109951200001f8484801203039030f5140e0001c6003913510120350a1001083c03061070b2811004404612000802e50f0002c1da10758000d0380a50b600b40511a07640c02000550b075002c04151100707035803c001e140c000c0c3c1e8590f5004559002c0c0d014042e800e001d00368680d24 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 583074919 1250 583073669 583073677
    0x71401051213060f021e03090109050f100c0203070309030f140706050a032003040b040501140c070210090b03060f041407050403030807020a1a0c190e04140411060915 73
    0x40c90102d050041041004168011190340304000441141004c2c0d80c4d0814640c00014901080c00600700000441c40f490350a411442245401004881070849042100c42e6203c03c0800c41841580c0b408842c0501944044102c40c9519090341d070f1484034500315114401c0703010009108503402049164011801501885104002c0c40d03140c41f042c2c0c442d600c2c00c1e0007805413281c0c804031350440b10030b00d080461085c40c5201a6500a5006070040f0070341e5a0700d29001c0e00404042c24007001c00c10a03002004411000e8a005182061090302c00c4074802810742c03001d441ca41c10344d0041c05210316003403001600c2070500521002d42140000c002058030042e298104c06d031150160f802d24000741c4009024001e15130003400880c0c101209100030a484450b588a50b00c0107000055890300310404c6c00003080180000c0015210500d881c1804e010502e009090090300b52107204034494010780c200b03102d016840213002c8640d4480c582010200e800401102e080103035275031011440951102c0d0340d01301101d00158100c060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 583076169 1250 583074919 583074931
    0x50109020a031a03030a0804051e1e01020c060a020c070b070c17060108060c131502010c02010606020c030307081e030c0406080117031b030408030a020c09070504030201020714010512 80
    0x590350860150020242c64100085034041c07243d40100c9030503514000111405030074985440703406621146003150400d881c40b540091500c000c040e0410104201244441400560341003680121503460381741400c0c0d010324034601c0c0c0c190f00540300095091a00741c0041580349003003026540242d0301c410541041d070304513803070a445200e10a801480490103050200c0b40c0401000002c140d19850040030360740d2110010500c020ba1440441e00c000c85100d4070030a00094420608510560252490024001e1100700704c00401582030000025249001007401484124041c01651030f00d40b4035212101203a000342c540040000004407407506010107180614000c18807420001d960340d2401000610b1f400e0103800041960400e0003440810800020445400e0791441380e81d4105000d10040c0c042c11400389922401807400b0000700754410075400f040099202004940140142c0c407000c0c000c031281d0280f40030080c0968800381040c080c00c1800b03421850b200ea41450514505040390045584030744058842c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 583077419 1250 583076169 583076171
    0x510110c15100b0c120f0a0906140a0c0c090e030d14190b0d24150807061101091e061a13020a0203090901031112030337050109 56
    0x10440d60100c184600c040460310301400c04024200440b00d050b403001c291044030094500003aa0243c900307000e02620000810000c00241c0301c01c1030401c070a07900d03840001200c002550054000c44ea45000d01c0202050b00c840c26606818170303030340c4401500c0490700c281086d00d5130074400e83c00283e011800d0090342402c404400140d600d035071128508605030340083c40249007400a201c20170aa001260640500103001c4900100d00260064046411060f844501401d0b0386a94010b81241c030b907841c174101d949842c42030317010000c155841c0c1c2041c01c0003105010f60380d6590401c1c5002c02115125034040032040c2030080000400064581d5041e60410194200500e039038180480745007072100610400c484c00888202d4465089501c0001410000da02c4140329a5154089401c582c840d1007003060f51003840d4042c0c003643c1c043d40c49007031480b421034210728110700c20741480c0002030740f40d0000b1094030701a00e441003203008200341c41c0d602e441500d480003000420013003030104a5040c031340c01ca004080c002d20500394 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 583078669 1250 583077419 583077427
    0xa0c080c16031b05010206070e1f0503090c030c1503060109081c03050a022a030417070e130c121515050a060207080a080f04080a0303020910031b0c051011 68
    0x6000041c00e003006921020f5160315080410543e43c0201c1c2d0150310408a1528003501c2c1e610310001400000920110070f41882c442084e15a0141c000d0000c1d800b0300810411214041784080805540314004544179800c0b004c103030000700084070032074007840c1c200c10b05051590802d91100403541c5002c450268885e100c1000e60000c46040d9018030680d0b8001400c0e0806500d46044501c04000707090607108006040c100d0381c3c548102c201024401c0d900030b800500fa07010300760540c24014541d103024602426400000f640c0c081480740e04a09410700074290300100c0f1452070341c0b070b0611030b44c1c50b140044c01c140c80c0d441101f40514403155040c403840c840021040f1001c0303802c80c24141407080030011500440300355840558103000d08940000e140c00d5007a0710008059035400721101520b4540103e0b0f125031003030700c15840100304042d00350300074000301030382507808450610b0030100480907940c2c2c0d45516005e181c4460090b105041c4518100843d503030048007180c500e424031301c030f01c0e40c12280c00400d40d02c54080040303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 583079919 1250 583078669 583078673
    0xb0913060f0603030507020d0c080d030603060c0203031e06060f030a0e160515090301060b162a0b0a17070e09010b13170c06040315050a110a0c080c1603 67
    0xc881e044480721404802c0201a00307565000e01903200380840648502c200303120b448200b0084525081c0601207210030b40301c20000507580640500020301044410906004000e580c151001040d20710400690350480b146140320303110080d0304403020b003049070048810058180751110090007140200c182140005511092140781c508048900540c001c44669611041101c1c1d40c4000550710800315124081756926042400640100020381c401c840405010036001d0241c1c0c00200b1510109024094403556180011f5090500840303d62440c036090071040310911451130703484094485e01c1803500309444c010305039800c0f0410740c203070464400000440840c07000c81241000a030880c010a41008180c0c1071001b19041f0301d01d085824010f0f0941d00d4000074400a0300c01c000c0190020260780602003d65994480c202040c80e00704c218001d0803028144008a54210f00911030101c041e01040482810302c000480112070098503048103848800c0c0078841c40000e01010300c8841d60003101c0c2e80b0b440ca4000c3c0b0b14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 583081169 1250 583079919 583079921
    0x110f071406040506060f040e0607050c0d030207080f070501021b0c100212090d0c031a0a0b0f010e0907051e0714030a0f050f0c06150f03010605130b040b091306 70
    0xc8055004503040107080c07000003100011310541068048074020304c03080344080800d008290b25845150503104220a101e000c1e074200c0f00074100e4018490a88210140394281601644225070700201400410009510a40d140301c0140a080c0e10510016241103214036010040d41041981c0000e19080440c5140e070a00d420341403401d00789542c1c0040d000149101d1406400e074018807840901550201d4081d03010040c104103014040c2d0b40c00070401009400740c80c040195400c0444001500600d042d2500606203400540d83c0ea400c0d0059403581258240281400001240600710030f00b0711200b8401114001140c80300c410107408024895038032442c44d42017091110303ea110000089410400400841a0f400741000b000e40c42039050140d55105800e41c40c0040f4070039160303da1110700880041c02100d0111102d82e00c501c4404440d08147c2c048100209802c940e0680709040d03010400e0600503c0800d15a00703d0031081c032004000042003040791021a8850f00221810003001420108a074200110b07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 583082419 1250 583081169 583081193
    0x60f1a01090504060b0403060504060b0909060105030106052d03010e031222020a03060902130e0d14041404051806040b01180b09040b0621030a081506030103080d110f07 74
    0x219070030301003249014005c84092107a40005813680b912680000c043c402113402c00110000d0140c4036407903030701c0c0404690f40c0b640700a00425100394240140014603280c04140d100c20500d04d0306060351210040f04e9900d4114035031521382c5070103540310700002c0051941803019041a01c0f0b4000709000d24030303015904000070040d030020320795031354210466000540c80f042404c0060700c0c0c0c001c40001701040390340001180040041000c000c513a0603d20245800706001c01d99001c05401c6490f000308007021003840c0121400703140525248944010944120740c90940c002d10b402c4010351001c40082c02c0c44103221801c00e00c0c119400d0722103901001c01040b22038945540358048005200c010440400c14800150001c140584040c00c40c0700b1407008120250340f6440d220301c50358440d109205c0008441c1e01c0f80b17501d9270485040c030004a40031900203081007c150310345031600030000381001c0c0703140e0840da100119a0000f04a840e1007039600d00c0304007030140681000745007441d000f01c203182c0c917a2411300e0041d0000c80c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 583083669 1250 583082419 583082429
    0x5060603090d1103090604090b01030b040504020906100905040c02031207110703030c03120903120b030a1119030503040906090c030227060f07060e061e010302040207060f1a0109 78
    0x4400c0040010701a004201407652140c0740c908210358412207040c0501c1c500401c25090381c000d1000800240101003544840000c0c1420b0301d003030090b0306a0340200012194100e8010350001003120000d040c500e41111f03410620b850b181001820f941e04c4002040481c1c0e81f842c2900090391001540ca070000d103603042c00e2a07000c4d1541c9425900d00c0c400d241600d440d504240700c01404d000010440204242c02400c0040210129140400840407a414002c0440d000c03050b0b030201c0c1500d402a040c1543c240480c41c40e910b40d40050308204081740c4901032204000d5210407503143c1c100c07444004030016000f44001c1006050390301011800c0390400d9141c0d021640c0e40c25110b014544100004024900410110109403005a0215080c004ca80380811403901c50b403012108001c40000e0710008025203540580d40100030325044604503554200d224003d0f0f03200e0751140340380c4c0300030800400042c50640c00070580da52060f00040380620800040c10140d4000820510b1001d85141c001103180d6807091001c00281 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 583084919 1250 583083669 583083679
    0x8010f0315050601030915050103030e0d02090f0c0c0a030c110406260c030102070308010e010b03070813020f121e010c0509240f1b070b030604150b19030506 69
    0x5495603680206025101d00440ea04030b8071640010b03c540c2c06030f0701070018140c01540b8016801540c1c08114000d180c01d0008901088500c03110354a0360920301c1c0641c40c815400340100307856488020082801a0f401070a03030021180402050502510910289203064840d2b2642e804145c01d40ca8102c0c403001d140300d40140568902042000f10000c0a90403215182c2036410000c84400502c4499003072540d482c1d80d241d0950700008040042603400803400d41294210503c1c0388442c2d0300c81000117003c0c881603407424000741044010650f004c40300305101115a100804c8100ca4582d8000854603c030803404104603550031903c2c07065900c0c00c540c91601c0300e4052901c000c001d01c408600300503046005040c1220b010704155146a4160780c032908800149481c00b108650302c80c007401d00b841445038800d0503142841130805000340101c0c0400510722007529400c0304c0d16804c0d070382d619040c0001005d07000100e0300b440e03000d058000303036030f4000c00001e1010f0004000d0003e40108034034000340542c1c202610041c068 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 583086169 1250 583084919 583084949
    0x609111c0b0c03070507060e12031e24060a09081b0f011107060e030109050102040905100b040302090a11070c090c030b1c2a0b091512060906130510060801 68
    0x8030744c5c40001c584402c0e030312090000c0c0c007560301c3c00d029240c1036000e15035503202600081804440003510006c9003900303401050001660341c0d00004080c248400c020318550142c04c0500108007440c180e405845d04a031180303080c2840941d0703404428544009465003501103038035503504540d14100b000e09005100c3c0282092164051001440f0742d44102c0c5d0300c150750801040c0250500310790b50a40114040c213030404004e5403036540301c804030b80007803106807004d4000341d54007030300040c10109a030143d40440341c0040c020304040e940c0846081c081c007000d501c4866002810003030900018a911081000384c500544005030740b550035030000d0110743c05402040c2c803030901c981054540c5060b044201410f164420303910032441800fa114644080c0148140b4030700c1070301d5880080f42d410540405001407480803100c00080c40f15260409180d84120841d045d295a585000500581400420f2a401290242c042c41448118a440b13800312a0141c410030900c000c6e4890411030103070300c0321034103014000407969a65a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 583087419 1250 583086169 583086181
    0x1401090909241d0c09071e050304060b0414040b0c181201020405120d030c09050f012a0b0906010f081506030a12021006080313030609111c0b0c03 64
    0x1128520202e00102454016107001c0541e225007185941c404501103450100295200694a84c400b104040b8069001400025640c82c825060742240e40155404080741184110084a03264401441907904a860f048480e401d610760b0310451070840040c040e1070945040c5450001c000c80c1c4080e0410f01003e03803d0101c0d02408203440750350401883c0c101e42600004414620043c0a40166406146c0c042c45030742009066400208400100303071420780d030801a44205d07001c01d40d80300405029803078100d00da2400090311075024404050032002c5003588103000d0380000810b99848040d101c3c007201c00d480c500c001d000038110104080b6000d8000007921500303690500305202e58072082c1950070301300c496058000c61000c0e1000e1040d1407500c0d4024130121308a0b9003e0768043d5032800441c140d1f0100610340103000403031071404400e88403c0c3c10350020040100d403840e1100700141106403020703624182e1507000c803401d551b00c04400003c46c4407014001101602c803410030b01d4501130700505107004c0407810410484 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 583088669 1250 583087419 583087433
    0x1e2d0e0102071406090f10080a0e01090b0f0601030f0c0e030708071505030a0b211506031915050a0b100509090606210403020115050303070203030304080915041401090909 75
    0xa241c0350550341135450750804800503400c801c080d0051500880d80c080d02c01307811503100c505a44510580a014018120310403019400c0315110b25015080325800b401142d1688448540c5603040394051502280c11079200e000c0d002240c4030a5400d6001c20f080381720140c06818148890720007880f002c00500025440c203040f074410300202a040070200b00c800400905034403103a904c901c035004806001200818144000840807100380c20b16444907215407064103070804081c0034258890040540a130070000b401c0440c610b01e410711244100e482c010703488550100c0e000a4440d0a2003418806004207001d00c0e00401d0000070400c940c0c1e010100101084541015214400078940041e000e4880c10382c0d42c482900380c2c1c0c500c0002441d269454550b0720085c841850703415001490032004585408048075a04c8007010760f00d00c10a04007d4040d00140000f80109410002400fa1070750f006d00080d91480c0044c1180c0c94560250300021007003a041c210440c800d5a01001110190440c0700040000d091942c032002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 583089919 1250 583088669 583088699
    0xf1b021015150216180501050910231c06060602030406021b0a0e0f1503030405010e04021806041707050616020f0103020417010212161e2d0e010207 65
    0x108180d0840d82c1c149400d10800c15020b004100741c07410a60207071210400158107801404030701e0480c1c01e20001040030710b41200342ca800743c2030441209205e2840d019040850034948004a9288c10803014090000c1e00c2d69400c41c0050306607480100580341d400e00c2c0a804444844d0020411075006000503c42176400080519a031b40b101016920b03004501d0b00000c5640d00c040d003000c03e05107810030900010001045500780603a980c102189407000002040c5a900d0250b840b6560005c1d4038881115007500309540148158800211210345202d107040c08a6066481607000050504004407121b2040c1010301c914000360a04a81041c94007407640d4039643d180490000103482955600705014543e03009a040300c00401d600c2011a062031100b143c428000c1d0810007401440c031020a00084401e0008041d42e600c941181d21003200e18090b007007040945400603403032541445820301070603101e2640e2400802a448009d02254001407061070000c0101c00c20300c2e0000e0642d0300c1000c3c144130807454140c0070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 583091169 1250 583089919 583089929
    0x21008070207140409141614060a08131a0906100b0702010f0e04050108030a03141b071103031902010e0c0a290a020102040518010f0909060f1b021015 66
    0x50031403c4003d00064018080064002e005150b00711a4040d010004940108496090003c00710746640d205064954407000c540c1455104400308199820680140c8615400c0b054240c54046101d40b01d65034242619420284680911194000c2101c080ea040108541c000740880d85014041e2a0024180c1180a05500281404120420303061030030700c00c40300c01c2c0c1d40c03a60080c010310007940c2d2201c80580303c0c0d000901078000241014140c4000403800031986004e6032520041c0d040650400700e240c203550300704d80c8003240c4000541c80058016541040580307182101401c0740300035100c82c11300181c2100d80700f42900426400050200550369030705140c010440348004541101500609124a16100c00c201003409164010801001196055000e003040c3e0b1b100380d82c0c0c1d480401c0c004686880b0707090f003403040010b41c0e900e91505100c2c0c604142c004010f844c0c0b003204082910482c82603081e040d1902000c04000001001080b0707543c15a04114010b0051581d4004000e030a10f10303209908180024018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 583092419 1250 583091169 583091189
    0x5340509060d0f0803060310020c0a0305070f0b0411040f0c081614130e0f09070302061303081612030b0a0e0408090a0602010501062d0c031b0609021008070207 70
    0x80440d1101044000c8543d0301209858a01016142100740c81d00b0646405019214025071107120700024400c50390340b0180701006080c420995a000c407003541c0a04401c440000e0f81840e1140090f1100080d04c1c051442603403200c0040202d18140000c481fa00c0b0702541e000ba0606858001d515006080c69411101001032405100480c82069804c040d0b82e10302c007142000006940d40d24400b00c000c0b00c505807180c00d12030a00c1c60f1601d60729910604010303240c440f040e420120080006240c5a00141000b204110142603083d9498440c0c650541000441001d08445401a8810000e2008001021a6440c1820811032000c40d000c0740c1145103074000c0c0100b07028003002050900040b24103964250790020940106551a120300078043c01007880740001061282103000f0034151001400e240b4044020540c241234aa40300d011503203255428004d0341401a403440c0311029241000c030140115000301c80201d03d0404c0351042c031144000b410440c00401c4182030a00c045542d010400e481221301000b5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 583093525 1106 583092419 583092421
    0x21020310050c190212190806090c09040911060a0f020f1207060203060f0301020d0b1e030601051210090605070810180e031605340509 59
    0x181205411406105041500a00c0100c01c50803001610441d10700c01c8805c03140440300c0e4031a0480c3c0646900c0b500701003d05541168000b60000301c1664000c28503d00200c04071800d001d0120154403841e00d800c4035005104440e1629940700100130103040d0b9404a80320b01034091883c400340c0700098003480c0c030481082c20001c14252018640d854125190000035516080254070040805900402000e03030200c41e52801d2000c0d01c601401c00c84006036805001c010030406000d06014400800d50f003c1690702d40352000f15403681150400c4e81ca88085038290030326681400380b0001d501d10124a80001c49050050030b402c2180107100b01c1d1101da140d0784401d0003e6421400c540074044071140009103800144020754000e080e5031103004207407414024500c1c08600d007150300340c2061799070b54005000030031640000342d0b40e00c000c41d040541507442c08001100380941f901c47c9204442c13159034510 = true := by decide +kernel

theorem cover : BRFrame.Cov 582913669 583093525 := by
  have h0 := BRFrame.cov_init 582913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 582913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 582913669 ≤ n) (h2 : n < 583093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
