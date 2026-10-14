-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2375
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:31:40.109113+00:00
-- url     : https://prove2.me/submissions/e7191d5b-43ad-4b30-955c-0a3d5ac1b75d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 426978417 ≤ n < 427158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 426979667 1250 426978417 426978421
    0x5070807110d14011a100e0411040e040807030e0f10030915090b010f12020904150b09041505070203090f061e0c03030702010b010903034a010314040c0509 68
    0x215000d504002c400400180d403020071074194482c158400c070003c42d5500140e844651209041c003414144c1460702200040754105e0400c42d6045c1a0050721500c0d08010b256840d060350340560036400d65042e80d08480103980050740c4000d042d031094144400c02d0301281c460f0341100340c0078001044489003603480307010325464000e1181070025080c0c420a98604083d424400d12100c1c1c500341c0e20441090280400b0b54040c2030004c20b881001038810454245d0191807100305031103d4582c40440014100b844064a44035030703603034100340c60b2081c0c840c0c0240d20810002e03a8a81d860380e81d01060365402080d6208541c0b05026400e002d03543e902240c560800295419990b40c25000840da01580b44014480d0b40840006509600180004003c0d440380502d40c0c02001082c115030011140c24130340d8030014001650a404440070000b100c10310302050b45140840040211102e04c06c0e5181e500c003c0e6003071140040509000803107582600401b01c02c81e01080e6994600d1a00d81c1e140d030707030f6105940203043c0100c24601c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 426980917 1250 426979667 426979669
    0x70c060e0a05061303080906131403190305040302250603020d110301081c11060703110d0f0605040e0c0904030f02030d060b0403031e09090c0504091811010507080711 73
    0x10301c8101da0030000341c83e0700b4134001850040c0540041e20440000c2c80110020b554100049022402165460141240055661540140700402070203c0704180010496041d0300d0081401034145101142c4002c5080c0c0740c58200a801c1846100748501400180c110404100307114035007076000d5502d5400c0c0140c031460107580c4940104880b59000d400000000b00114070380000044405040c504e4140d06400700c40078610494000340350b00d07114800380d032000c000300f002940660030140301441080c0c01c3d079040001d1407070030070f00341c1e2007a425110034244d40701c00a0015007058080c107001d41022000801c0007255030320101c1c00000d0700400c090304010101e0980402507100f4001c403107801c0c2641c0320510523240c413202d88644c076030310a00c000c6001c40c0310482d030031103400da001c400d425502065450720110189021082d2014005800001c820088104008914154144030b0501100c0c0320b131014003801426441d0250740c0075190740415040c09024042400000d143d03404036003071664000c286141c4101490 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 426982167 1250 426980917 426980923
    0x17150903031009050a0212151203070b1303110d0801090509030405090f0402061303080a030c0e01021b0a08011416031401060e030304090c052106030c0d1403130e0f070c060e 76
    0x101c92500c0a2100043c004050070075400008d4a08080310202510052691a10b54a00c01c46400034500c060031000240e200d00d80803403160b100c81c020304003804161350007590705042825806608d00031900400041c410505207100385540411035400440c901403d100c0054421000148007818507420807001400b151900b5080e02e404404841400c04a20b4503480d180c5560f400c60309a802c0000d08d407004203042e50344214440a075070359061f009011030207001841c0c1d00d144a541100e841e08840201c80c0043e91a9091040000c11a240b0300320113194141040014114151443c2d02820103040903150340c3d000010004150440d4885e0424200e2454200c0101e401d50059078000845240f600e9040d600403508000186000a000c6003210725003014140c0e005114002034514503096800b00b800f440007410081101c2400c42e010b11843d04814260301305051450f88400445410b06000d4081044000520305200e030300401403505c0c810752441c098000400d0984103000181a40307803982d040100b41c401c14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 426983417 1250 426982167 426982177
    0x601020624060915040806060a0b03070e280509160930060603030e0d05060c0c030909010f050a060306120f021f03061d04050604020603040c17150903031009050a02 72
    0x18100b07080040000c0c034131600c40c1d04144610101d9001d1100002c440e0301e0040d50220913580040c0f040703815500d0700e00045070602d8071241070710f4001841000d540c19001c44402841c042c01c0c0c03040d812038101801d00c0184036024102030318220316904052080c0c014581c02040800c19030710740c2c64603010004805070b8940301d41c0a5204401000030b01491905052003040d801060580f4002e44171540c03500c44480500451000c0018080c200d40c2140c07021501011080c4002c001c0500900c08603400d24428400140c0310345001c2e1b2065001080784c00e8208160704200c0410001031190382800c0001d149811002d00044110b91070003054451604840c0b400c5580e409805000c00d01480c0d1700c0c2d0004c18100d400030380100918050001041811030244030310040c820107641c811540140604400d40780c95007401859000a007040714054071411000c10810b0b01c940420032041500c90081044085a00030f1008880b4040c0110325150410400c0090004a0504620456003090800541980c0b845030a100074010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 426984667 1250 426983417 426983419
    0xb120604030c1707050102040609080c0d0303020a090e090705010e100f18030602220902040602070e04170c060a051302030c010c08090d050f06010509040c0e0c040317070b06010206240609 82
    0x401300f001010300005501400940d6019107400c8a11921181020f03a40c0600540072030b403044070ba0b51b01c0c600091181d001740c41c4504041c24041401901c42c6030322013802008482c1424076901400301000b46680c000a8071003015070555084c8580111158010450785440c4c4400e414080d1400d0032400d04c2d44248104002960806811901c8080c00241407000203d41c642e4102d00c010305010104001c802442140e0448485400502c0325a10306024200340710f00c000c105940840081c101c05442840300700041100381d240304003400081c90401c00d072004031540a0700b501102c02d8071440581c0141c40c0051481c01001090038019404456484e22005a1103001440350308209a1031100381000310014a90000300034000c145c9207640e0f200d400b4800001c1c02200c01500c030a0004c40c04200c4040c10fa9001c80d0006843e0b90204d00d81516901c5030305800206d800403c0d40ba14000881505000030102c0c8950030400920240009003801c05000d0803000d901d504081c007172900c0281c0e01605541301821500b80e660 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 426985917 1250 426984667 426984713
    0x5030f0c160b0103052d070509100302191701020f37050403030201231b21010311030c0f060901030617011508010513060506030c040914010b120604030c 67
    0x20b180d1801981702c00c107540300000800d40b000205440d401840480001b8481c40f0001000c125190008000500002a1100072502c28144011001d0703140c541c0c00b10301c2200c2200500702810314001e001483c013010b000c130340c19640e4418009850f1400b01402200e0000c0b40c55544001d404040b82d5103440007542c0d0005002c0340c0e400e00001d80c0341039038105006e04100c074002c1d002001180314140181d40d40424031030245509107034445c0011580e484120703010505000840107681022000514001556a03174022607c501d10352070010410450000320001a03680c040e4040c00144007000d010980c4d60f00d2010b6010b126003408a02440140d12992248005118100001d842101c2590b0454003c007040344400050340c46000022819000500809008548568000c1c5030301d0750b07944802005240240a02c0d074180a1880c48910300c1d41c460140703a00740c501407400c0d40554a0b4030542d0301e085544560310320b40540000c49404414017404104660f005415040580140c085441c1c2010303120720403210214a2a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 426987167 1250 426985917 426985919
    0x60f030201200a210306080a080c07080712120c0b0f0a140a09021f0f0f090909120807020d090510020712050703060c050c0a2d11040c05030f0c160b01 66
    0x210243d080c504055104907280d4103082c90384d4130100c0070f40c0c0c2c00340030380360040c0e001110400010700040c0040114404000075542c804ac1c58100385ca080803d50f81c8908016140140e18205001803a018900c65001034140703e9403a60307242d81e8002c1d1010000b0f11031100c002060000510904160300160f0403943d004a018402d890702010010081050500583c05420484051650900720380c03d0100300090585a05610352a00c502c00c48140c0701401601c02040740309800022956003900411040c64071528140c0400e13072690000078085a00102190b045501c80401c0e0312019401688800036510207841c0001e11043d4a01d00742d29003107190344582d44150784100d4810a000e000b043d0740007981c1c403070101030020910811085074680a000c65010068000201c2c40c0f001444445284268098003240c5840e008410803812a40c0c400c032020643e41c54038140351041091a051040030100012401d000e4214209821501c6c40520018400074210100041022620100780b83d6181d076158060002170281d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 426988417 1250 426987167 426987173
    0x20c06060d06020c0f01140108010b0307030b0408041203170705090a1404090f150c0302070308130323130b182b08040e0603390a030602090102060901060f030201200a 73
    0x1c21582c7d9044048029040010070028010b001d08040040000d008104c0380d42148c64071204584007400844030b40300b04000018140c2079200540310428040e403200029005045c00800c2d0980c0003c0c01c0400b04401045907441590308d440b80c800c2a142208011444050f08002003002084c0201d006440c00c28810040380801c1070a500d0140048800401803084913030300d000950a0b800b440f1801000b05442a00003001941e074910a42100c0b0302a1816a064403c0490514940081640200208180045c15011407840a0b4040009143d03d440203840c10034107100800c030921884d0841c0b481107030f14134080010103420034030710340100c0d0f000c104800c04410285040040d030750080c071401c0d0400c803046000690615002c5052580d00741844420140c2028440311848a1959228650450309180025107031945409413040c4c0914407554006941302184400640360020052078680d403a03050001c140003d01401c8446421071382c1c2803d004e511503440c1101ca00c61401c540d0704101582c07007070140714024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 426989667 1250 426988417 426988421
    0x20c011410080303010b070f1a0c03100e090312190e0c010e10080a020307031814010e0307050a0b0601090518100902070b0408071106040801091104020c06060d06020c0f01 75
    0x40c40100e10450300707107580c2d0403160f9101d010910804801c0b45013480380c2400b10340b0419440d28464408e002c596074610143e120310123030310800c2da40881c610402000308164804802d28801c090000c502008410345046003a0655034407800c0103100e0030392410408512031010000402c6154100701e0010b2085000d102c00e280e586448062000d40000c9a0f441c1a0509041c1380c0c0024164a01a58070347e0856036030108020041e40c40a0810000c065a880815502515140220581070300c59080c018185801160081c06d441c070010f0001e0684e00200b000100140002800600490784010308621554a00e001610f05240300d6120760303003100b01980d0118005500a542c20722400c04400b004100c982c48001c160100e004501d0010b10012000300031401060201001e0103c051043c1200c0754814480382c046100790300a540701007a1a0344645980e0100003000c010100c02803010784046084c280303075400303807036880344090005405483e0010360308003400410340407250000c0d034000440d164000e00c0403100d40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 426990917 1250 426989667 426989671
    0xb09010b0702030721020d0c082a0103330e0106120e03030106020a15020702041104030b060d111009030501060807061d010f05180a090905152404020c0114 68
    0x103c24000c034a008144c54410000581d424070f02100103a19000c40c5500340100100c60301c006882d201280d0300001103541d41080005001ca0700c56400c041c3c0400c450100104217080440064103140c10040c030714101e01041d041d8250b540c10785803e44000c0c40701142d042801504a070f040150380c504100b0001c1907803900080c040c50040d6001d602001440d483e6401d540d02c2c0c1c00203005850050b00811100ea02044072002c0700c0255100c000c000600d0510580d00003012103503096062044500045010401d00c50811003141e4007007820b4621511403041303680c0c0d1a055424440205114103030701c9541e51251441010640c000d182e01c10f0003040501c0d04c909414eda2542c803440340200140c80902031a9004a08003144062107606031241c81c5007804503101076440c0c2d0000352411110a480101107030b1995100904003008217181540080ca580c42400c2c1a42404412500381c1014419982031140d56103106170440040300b01d009100e400011701e000000c01030f204000c9070902c19800e00c0481010701e1000b2041034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 426992167 1250 426990917 426990919
    0xe160513030c0b0304151413061107051f11041503090510020d0e0c060a030c140a0305010f05010314070305090a1b1d2412030309010f1104050a03020d0302010b09010b0702 75
    0x5203c4c0c1c035844401c00162031303041c82c03a90341d0007c0c2c10740071030841c2e00f07406003041e4054442d0070041809608041080502e40190700300380c2c3c503903020300000140500405a180540e10071140c1c24005041c3d001d251000741d1103144510300801d00060040c50009220b60300c200004e60b48003040c6c860740901c45c60140040d4021900010019240c0014085c0e904400602c9940101000d81a1810403030244070680040241802070005c0c44100d5aa08141e40455001401d480540da04c0c0013596505100d020079280b0b04c02d4100c98140340c41c3c81e03007800c202140701003100e80c000f603103260110f030a6807040d800d40e05140000d00300503c0c808d02f201408405028100c1541c055071900c1ca40c000017800034081d08100050b0640d94031a205451440d84030781e9407503045510000c0b420251103200101c10a104031403075580308036407601c5940d546040304c104008550141901d5448444416801c00303080c5000038130742960f20311009100344c02c1700c1e40d540308040c000c1d000a0401e40700180910300710340e1345405c00a90303544003030703030032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 426993417 1250 426992167 426992183
    0xa0f080705220e180d0c2d1704060f030908070f050c060c0c04050a0b0a12020604031203020307030c020d0f20070e010e060301021216091701150e160513030c0b0304 72
    0x503020f0b442c420200c9404681d00041e07c0390b01c0e0140b00684c4802101041a81846400906060800700d80e0341100c2443c64170000146c00e54841c0340c224000d003034109080742e2008250514103418082131010060700c072119044101005949130b20714010b0300e809211511181c015402082600034404041641100e040701510140001d54560380540216541c1d40034180e844000058188903008010b07400d240000e00c040c0c420761820303450740c8a92000c00124206900040d0f0000200844c8a52500449143d4002d40c00104403400203074001030f040e140d49003840410010705180d2507140500807042d00b100b051004090741c200c0ba0304c0d0361007100b43e81000d00030201200b0344ca0001c01c500741814402c880001d402240001e107d0f8443c0d0010901c41104040303078008000680b100401d5040b42c00b0340110301114140000181144100e04071005c14441d5031010b81c08142d40310401486054441c10046189000d240a41d0f031082c0320008000d62003020740000e4004810076801103048001c450055002d00c0c060294 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 426994667 1250 426993417 426993433
    0x30603020415031e050309060304060207060e0a03092723010b1306030e0a060501090c02120309030405150d090b01090b030f0a020f0307090509030a0f080705220e18 72
    0xa1034002c0345031100520402c40e04030603c1c03d4615000b86012458819400d40346001204800580c158205940a94034254001502800c000c3c1d244107400060b003054015110716002c03034401800ca400d8921070a1074003915031009041c4040c0c1200902d40c01c0c45200c90030020f0040220124ac0310388007808406058803100c60001ca44505620706545000160b800c5203603096080c0340088010f00006c190440c0c441c4180142c003c00a881c50081602030602070b08006403800c3ca1100c0245081d18484940c00c800004100303004440714003204441c00c1e5007040d5005100815404141c110ba0b00c950502030100381d140212060820003c18440b50480e00082024400020454109611071400e140e900d02558807100d104c20044c14410a8810f031190010103031200c0c50b035501180001d5907400c42d040c80c103e8200140b0100f0b00b80d0004401400b0001d94580b2906500d015007016090303100e140c10016840a00e417002c881d080304078915100c003900e00c0b0054098107003802c0b4040d035200c140039242d00344903010301c01c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 426995917 1250 426994667 426994691
    0xf07030f062004091109041b021c170c1b0102040608060402091003050613060609090c0203121911120411091605031005061b0106060810031407150306030204 69
    0x240507a00b0b22150950646840c1c504441d142c0241500c0713a42c60318101e010301821189070f580744100380d40100010032802904100480007400c00014000e1403041900000a40d2080c0e5072002d40c0d14040d40c940d840815058407003212962a5000b00d925440c060324031403020f5045040c0c10b40180088a03030a031a0200c0b0780e22028100b000707034020000110f800c1500d042504407543c0c4242c20081e000003002e061702e42140187d4141405031080c41d00507401141d200e1404010348091845400d0002e001440a5400d20b40c0300c070784906401c0405030144083c203c842038500704000f80b03603120103040e2447c0301a00760f542007206030101108804440580b40c4002034450000503042000540f031050190084c6d90000c0c480400094a0981014240440320303e8045004901c0d0344400008240403d006015020380d412000881800e58209400410403c00d00000748942c1400c80c140440c1920340c022404009941d6034080603152900e268000b49503000e409235403503041d0350503900040589000f61428015155560 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 426997167 1250 426995917 426995951
    0x509071d040305030f06240c0c0402030603060f0415060609052823030a060213140607080711090103080903010c03150603021e0301180e01090203100209030f07030f06 73
    0x1d40c09000b140c01000000c00c00c2c0c1d6140000c940c40b1000601d5810842d1002c988007212442c0e04000c0000080d00141000c0da074038040140d640c40398001c450540c61468804e0101e034459101406603544100440041010000a1401555a103e54040c2000b00301d6a50704009c0c00c00380c1900c00c00f0b014078143d03d142c810100c03d20204202d80940103078640d04140c546a45103200d440c1842d8500400c10640710488440e907014465044094064000540c0f1f5a000e14038900400b401c0da44000300c0c00c850700481c0c0441d6101e105c01c0e2940c0e40d8101079019150790090821488058aa5803016841080c0f0ba002004025408000c0d00b00c0340825802046609040c5800342d080340e4a05907084140c40000e1410044140311750014640c006221001c0070945140061000840d0800c0e080070903803c2e008490100c00040c05d115607860808050024041c01005402007910390034003001018983c3c1d00001d540b081514100701800c0055104012a00030300c0e56030803c001c4005000108494007402d182f4030f161144820 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 426998417 1250 426997167 426997171
    0x1e1812030c0f14040b030903130b0c0a031409060309060103030216060801050f04060f080d030b01050a0806010815180a0b03010b10030504110d0f02030709021305041d010509071d 78
    0x50b01c441001600301c840966100103035208202090b40c0401c400b143c4460002c0103140110407820056442c0c82c1404204001561150484200c00a040c030908008910001e021100b40b0b41600f4180c06001c1c1e81c4000c01864882c1c00c1055403c0382e000014002c24104c0094614100d0380a9401d4594800c40c039200c004d0683c1e038920503400001c44042c01070000e480c1c901c1c0031280d445002803001400d1a50317507003070401c2d0034150f1348640c0705134004038841d4184ea9014015402e03501c809103490785ca4014980d00150080c000500203a041002000c0001d04418035016803003002c002c02414080d00658040051001c11001c54245038021306040c0d9040c002d08050042c3c80c61281d00402d83c444001c2001d2040f0000c0c000140180c03091480b00942c500d00c4e03111900301d42c8015005804064089040380185490800070386d02c181e0f40240f0410491800c250880315880944404540203c1e44080f10490148044404201e07101c01e540307040300340141c0250008a00c012103544080f80000c900d40c000005c0d1a41c0382c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 426999667 1250 426998417 426998441
    0x20319021603080a02100b241605070312030516050c070e01090f0b0a05010c121b030c1209080d0302070809030d03020c15010e340819110702041e181203 67
    0x800308c82049407142c0d640660440c141e04911400c005030503180340865001880140e82e5034100107014824429480c030180410080c504040c04503081c091135084000759030100380320801c1004140c180b0b0541c0140013510042802000141a5503184d24490008142c00100c0209140c03070208000d40d281800700c40c100c02c0320070507100d00c010307880350381c4800038250711041c03400040040d9515020181000c0d460310b0303907480b802507503102154201880c095404132071300c0c02608103100c062001005090000920103c10301c40c14500540c9683d40c603d408030548c017901c540250315002d0300e5000d9142e5a4164040d02c800d240b2201180d681c40c100450141c0c00b10428050080048401c50004501030907280321100c407041800b12200a1807000a010040e108460380208001030402080c0443d4070210120040400b2803001e04100c0114007000c1480036102d101030080c0242d4481480404015a51100e4240c40424000034010b0003c000341844850115102c100c0740d08003981203400e8000c2c0f0a01c103071100650 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 427000917 1250 426999667 426999679
    0x10c02010b030c19031505180f071e09021209240c0912060a0b0a08010c020316030318030e03010f110915090402121008030a020319021603080a02100b 66
    0x10301c2c1014054a02c4840b03568100c0740781e444c0000000a49960208091010207020000701c03402e2646041c00004001e03501039000d40c2c401c031170504000c0b001040d908103e8209541c144c3c55201c0105112003d22100e500c003032511031000c2400000f86459540291140004c001698a655030741e01d5600c04c160041094401861a45400902c94003002c50044ca00804000c10055071180d2000340030380f410303100720782c00722829858040a4007541007a004c00c0000e0002000248442c0b45000701c001e41ea401642041d03603980c90a540300500345030003540700301c00320308020b41125140080c81c00c014166200708180c1d14080c2d840e0145101e5101e51602c502801015203401640c030340740410040160180012340300e001d424070200001c0744e0540d5144010141c001d5403007000c0602d403a008940c3e0b00c0345d640c2c5030b01c00300321504200300070035020750302100b142c0201c0d500c00c8007035550202d4904120302c0e1418100759050380d800b4511001c028400f00d40701400e54840300d54205c403400b452240c00201954030300282250042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 427002167 1250 427000917 427000933
    0xc05030d020307030209040c030c140301050609040207110a0e0907060905010903022205150301060905061807020c0d0317070c110d0302102f0a0207050d110a0e010602010c02010b03 79
    0x16001103400100f01e180141c00d08411600280880c1c0e144000e0b000030035036441c946407000350003c1200c103410102402d0541998905408515140700708180305115a500241000800002c0d20894810340c202601c450160340d210f0154080c3d890095840440910070103000181c0c032441417061a081d90410b0b90303480c03050b031b1030360303080c0410b907101c0300c0c13480324001d54095815031410018400c0c5403241c88001d0039070b0a81c1c50b002e0281421100305800c0342c11440d04050030000c00303441d40341c0703205542c02a640390207110380c2d54607604074108008103242960001d0245034050505900c03050009140510111401c5e01d925034010a44000c14400f4000309491a41145511b00d07281460443e4144d5019005461465181c7c1412600300d84101a14001c43d207000d00300401440c1e42240c0711002c1200101510340740c01d114010203903407000e451081038464180714464608100031011070004100d0081c001011107611400a0309a4400c2402098015031a00043d25460342c814090300d9000741c00130300035003000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 427003417 1250 427002167 427002187
    0x3080603101b050d0e010e2d06040f02030f0604050c0406081606050c01020f041e0e0c031f05060a02010504031d090f0a0615020c1011060f0414160e01060c0503 70
    0xc3c0d08402240f00c04c25599100c02c2c0500034080c02003400240303a11014104200900c0410310031500345510301030300c26003d400140c2940000052140d0881d4106074090709103001c03440028036185c0c0981e100c0342e80b4060842408200301c80011964800c41e01243c00340701d559107811140e0b50304d4002030300c18008603003041000c01c0001d000c0c0c0000c0220401e100005403404c8820b00c1011401d91040d03100f078400c01100e40380b106000050043d5200980060328402209090000348500c43d070101501800c0e00e410442d50700d49030346007894425070003000b016000b5501c600da0840044e00030b040859013680070401c021160003024841310550100008020b00c02c01013910f5824007040d0036000145100c41d4240d94100100b429180481d2810011025a00038034000c181c00c0e0074807165003400310220b0140854040111415078011554540c04090942070711456503803800d14684054110300c02281901808840707112070a402ca8110095892281882c400303660b0310b0800b00d5018031f10310000783c0190400e22440c00c00f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 427004667 1250 427003417 427003427
    0x140c0604030e190608061f0207031401150b0910261003080705030c0706080606180102010605092a0a050909040309030510020909070207030b01050d08070f03080603101b 74
    0x100c040050003100c559040c03c542055070401c00d40152000c030380700d83c0411110749419004140c403c0112007a403844103184201c06951118a408001c19242d42c24002d082800701c00d5010202c040c144a8214ae00c060340c0da5034800745503008940b968010300108108060701d03809503010f078800a06e424845000418100543c0d4a40700014003054401400e41600001141403240a041d040d4043c05c00b65548896941c0114034042040d80a030080c000d2181c100552540c41301c099a2441c40a08155101d00349003000403401005203030042588184444180f10801e18a14915500d650504500c40340284002841c1500b45c040c1300c0c03010000480400204405003040c2c0d03003958110707200341860f0040a0b202e03a40c1e02c0c1415134411100c2c4480b5404503041c401407401e0914140c200c2400e00182940d2401c40e15215000d2030140980c60044400c103400d1000c000d00c034021075407180c2e00840c40b0350b038415240c03900504070309003910401d00c640720310040442c0c110032900c6005404940c410b417441450002100581e8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 427005917 1250 427004667 427004687
    0x109170102070b250e01080406020a02030d06141306050607121101050408030a23040308130c0803040e06090114041d010e070806090304060207210210030c140c060403 73
    0x541550284012000a203c0c416101d000d02e00090b40310324550100c40c20044c0303044800000d4000c000318254503401c5641c01c890f901d83c000390004005640c540741100180d02c0c41c070900c445800106c1c0385c1400000c0020512068200800342215104011141c880d11041600d84034001c00d039008030b042208800081c42d2898060002405041a241c1c03c500da113451801c65004540680340b0720000000c100a002c82446690b5160119003c1005d9031140c0183d202c000030401000201803000440c0444c0c09420030080d003400d001c1d8081312030020607446204450312030300240b04000c940c00510300450718030f2074110f42c6141078440a0f600a403140c800d020800000d80f22201c045407002c02000c0413400c00180c280504c035200140d183c001c059075440c2c40165413410310006e2810105800a0005005980d03010488000305d40c50340c1002452900303a26022a032122400d03400030b40c070140d0b0007211401503402d50880b0341d0020054440c184504d06861100e812403282c00c85000042e00b00900040000e806200741d94 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 427007167 1250 427005917 427005959
    0xf07090e030d09032616080103210207050a060c0b010e2e051503040b0a050c07030e03100204080d0e0a03080a1d10090e1f03140f100f0b010206060109 66
    0x4070400b040c103071402017110303810064008440c080c010030807640ea0074607002810744100c1c60400415855515115442c0781ca1b00c900c01901e070045101d49003407603c00c001c22009800300800d8001610b9854802400d81c0804010440300080c04500000300f401d40b11840760710401d004901e004041c5511030840110340324031003008407034101800c1e000c1911b07210348c00301c1a020b0316207030f030381d503a6a0510b41080c0348001c4000b4a01c101c90390510003004010300901e01904c01980e8581820b2646510311000281017015050104542c2c600c0803c0002d89201d00050648080115880d0b0584800401e011b00560304202e00014100840400c070b6032480d80d10a030800c1c0a424612124600b8025506e400501e00c14002c5c1c8200f00040d100c1b420905c00e507805402c0d156001020702c19410860b05030340c0301414116000d8480608a05562a802c03181c0c004203201400110202c0015501c03481c000c900000c008109825421f0f61075858500114a02d50002807803074040c9138140c68480b11a49805852042f5414400c450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 427008417 1250 427007167 427007177
    0x20708010507030209030105132d0206030421090602030a050f130f05010e0d052e050406140622050601140c0d110304030c0b090d0b07020f07090e030d0903 68
    0x61800000c0c41068091402d0ba40c016035140c0f018820503003510300103001318007040010003403031000540b80503401082e0021402141030702070411030003040e407a140c1c07480a50402000410001080038a07402440801084102c01001e030100341c0c401c03114820580104000750340100602561540a14013520307420001f0101c0f90b1900e0700d1035008030080c0b80107030b009001200080605008035a0400c0600030042c005447c2d400c1403c809880b0159581d900701d10010413040042500c1000c040c0112401658103a15041807180c5e040905e0140014400d5110720451101101d0100da043e16050cd507010340003002c080100600030502a418004040c0684020f042c0308540c020f988568800c440030780b03044207400b0041e04400505c00c402424141000d5207004103034104000a00004800b40644400d847c04600e02c540c4403070620b0301003100f0100000c2d000d802b25148008010000b0303800a0040c0003110000c2c140d0f480c65560380c0410f01079501300090031000790000e215120f40e1a543e03078000560396000c0e1500b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 427009667 1250 427008417 427008419
    0x1511030304061d0313030302210d02160206030f0402010306150806101b08090901090603150b04180506070f0203090307270203130302010e07031a04020a08010218030c09090a120207 79
    0x26034950342c0000c0c1443d4042000c40b5042080c150140410080c0c68030342c1d15024154100e164003840680b00c0c40001c01c0c0c01c9540403ca078504840b44103d140721240c6d01030041cec2ea4034146079a081881c6501150100e00290420302c000c2618035100c06c00d4030320610281c071204816211002042540000c1c7d070845020000404604d8014107407c1d4031f850310050240706042e41c0e13010310341e051200c1020142c00554400c0e040000c200000307a2100180503c0305200200024950100000034000e01600c0140d80c696154245a0b4400c0c40404140340303000700116150baa04020742030b001a6104d001d200701069158010080c10418a80c1d102401141210360701482c146040780c2800c0c1c0340880c0c106641410018ac88028980c081640921517000c40c2d15100c402403459602e50780d94040101c1a5000c2c1e061203503d05004101151100408003002e1300ca100c000f035455820300018405040c81c1940018424450110404451700746005120b004444440c081c00d034421040d02c8061171009203205400031031142c828 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 427010917 1250 427009667 427009721
    0x70f05030f151302070302190b0415020706020a0e011206032f0405010f06091d15190e1504020418020c030c0d02061e1513020d02030c04151103030406 66
    0x2d9185040d4243c2d120060f1030b03001700e090003031800e590b58420030000a0908005004900b0041d101c5602c03590112003071003007425016218000e030003140c0c001004103002050f42104540c101b044885054000c0e03a170801508000c44d10030b81503942030712025008001d0030300800ea0b03041c010020700c448440e407801091186c901850100e01200c109a002c01c1c25004001000c1c000c540d404a4088002d02490b01c8003070501070080d016a40c1003501800e000b0079a603042590200640761a600708003801c3c42080c8908840e980d0f214401d11854084078001d00b2500c0444005981d45024400c0d2010703508401c0d611100d03c1c000b015000c00035070024040c102c1d44e12041c411840c290504000700a10040c09502030302003401c110300041c0c01c800e00140703401d0b403042d0141c04100c400048190b440703040110854000d15145503407180b100003442101041c10345140004200705800765520300620407103200e40a4809200b0402c841254400d82c00503440230541c00800104010500b590054062429403c18810104000d01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 427012167 1250 427010917 427010929
    0x7140a0c020d060c170c040519030f110108062407060209100507150902010f120e07060201090c06082a0415021b1005040e0a0b0a061205070f05030f15 66
    0x10011100b03180c403040303d140308a0707010300b100170503845035441c558450802c0c02892005015600030140140201d40d140d80b800004804400e00864101401c0c03a850035280c00c008030141d95208006021030410000705055040068604e80000b041c441c0035544001801c0c00d041a90b48200c0042d1003207a000d0004104030703910010260a4144180c5030903035200f025217084121a200c0310300743c5484034605000500580d070007100d0070828104916100403500c004c10710820040007803904456551203400c9000c280180c055020101c494007901260302c81c1d590b44d075412501140d044590340000008a080c1220b0303400c0030541034403c4207401d813000741001c0e101d50400e1001408c080e400c4005a00c0071020f2682103000c0310841000d00000e860300c0c80880c1c1060000b41c806c0c8954405d441040e2002c0740054004e4100764000e55102100070484003d07103070365500040214044051300703c0c1701403400d0301041c141f900500480741030030307a01d8444500310b0380d4182c041c00c0c1051000303082d4000c00c080c0c000030280d596103003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 427013417 1250 427012167 427012189
    0xa050d09030309090510062303070c02030709050106050f030702070302191d090d05070804030609031107080c1e0f040507030e010e0a0b041217070504061707140a0c02 73
    0x6544285000d40307181001800240c00340d02042c280e81c641070600842511031605401500d900b0300740180c101c00d041000c3c0340d265410a4032100c042c0c0d408424010301c6680503c18070a0640220220703940c0585034a900b0017101c4080c030030100070400c01c011031003d04c8003072000745a210031240161600c40d030740c0360045012503180c0c104107813206103210800c0c0900c0181840510400d42001242d101c503180c640705035030b9a40058a2014144100420003100f0051017004460181d980040207006105503440e01134051829402804101e004010b03000c5004c4c10009220a00352100801c690b601c1140f103000311070360b0f480c42e042c0e45400061503184403405458600407a4001d0641d503070006580d030903c401c000c0c2100d00306683c1c2d10250708403e10200c00728603071032442e941064200306903004070030b50300a09a8000844001651100c90801c04020301d40da00032001c0e00072a05c490b1034404030145061403460240c401100ca03e00410340c0c0c114411404c0b034084c00504111020b5041140f2842d40d542c0000b4100c0c003079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 427014667 1250 427013417 427013443
    0x81e152a040510110a0206090a0b0408060402040c02150c07060e0303090a020f03010b130f14070804110909030a0804030e041107061a2103120c0d0e060112030806030a05 74
    0x1d0200300c0d90901da800010728602614001c803075804425405911081040c0e00a44070300340c08a400149035841103040b0b0020050411352698982d62a4241c1d600c0c0d0501302c406a10403840c14241c085814000700310031880c1c80c40b0b203004480c2036030b0b002d05c2d07480c80f40c104840070703122540d41300024400701200300300841c084c0c515140103100089140c81000200150660300a0207a4100404c03000aa1142d042d10300e481080c051000c125110840028002815881e0628014800c21410700151941200b5030318000c600ae8412041d18074100020300080e04070546803542150310402c0321007a0f00e846840303441e81251203803503e44c25207003030301001800395903084954440000c00000e44008010a42c40313a5415045210f13403c01e800040e15000a07540341c1d030710304115800351101000c0b940760311042c4100c0344170308131484803840d06090251258005400614000c05110300e01400310003007050014216040792205070541d10721821a983c119031120303029009580500c50291014001801440380c0300702e03001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 427015917 1250 427014667 427014751
    0x50901090b09010c052736040b0a02070203070302092e0e040305180d030c061d0319020a0c030f2f060307021501030b01081e15 56
    0x40c6400c0400102102034803584503a0b03d001460701010b074110055031030b10388980940303105501d0b103011080b5100104540060b0b1041b403a0105543c482d41001030020400c81c107488800d0303440c0c21800302c0c4c0400c4100351400350100c00380c500080c51881050b00100807052020b81901c2c006552640070450549003035a400800308004150126616005c040710b641000b0421250144a032801e100c0c003030140400b80000c2c04000000a10340418060f119043d100d000c40501217002c02021810700038511540d14004545090406600345104803401030b54016005d0000081e61400030001900001120020314600a50003290400e8004c65601c4000000641c01400703903400410312490310700e184c0700500315a0000c0d00da010380200e0071030007012002c10780741c8000d440566607905c50140c143c0c9412004800c00c49410710507030010040064170440c45040b03842e030340d0032944c1c4100128440d101d590002c0080324640d601c2000046180e410044096400a090b055601e0910206418940c4118070100c0d00101c502 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 427017167 1250 427015917 427015931
    0x402060f0d11041a03040c0509060d1b051206040b060f0301060801020d090308100e010306092a05090a020703080606070618030807201b010e040c0201050105030d05070f06050403050706050901 84
    0xd4913084050006010b812519031035490309503180c40c804441409041d005000b400700054990701c40b040790542441c0c00088220100c0280501150003030043d00a99009462050404501a03800a619805164445145907260303a03540140a46d40301c0083d1819807540d20f54400040e652002e20080140a801e9400822020001c1c100139054100103400c2e8003271505032100404c02c1c0c14685034002d041d40da101c01c01180002481c140711400c0d42e04070340002500706030585104080621450781c0c5040700c0056988000b01e60310003640004a00501e0000750102d050000003c08900d411401000d030b140c4a008000380d807a205c6a4102e4031010780d42e0048020681c10401c0c44032058100404c041115184001c014199204040f0306844d803140c0220940c101400032204840e9a0055040b40b20703909015108004507203482d00028007815081c0304181c000c1c0903418011801521030401c5035070640d003141e10700100c410565903110040800070130584c10801e003030098100080c10f9000380c40c025404980086010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 427018417 1250 427017167 427017179
    0xe1810020f1e1614070905011d09011503230601030308090f011a0d030e19061107060504060c08160f030e01030c0206061c0b09151501080402060f0d1104 67
    0x100c00d100d00a1003030341c1000e01629440c03400d155410f050056102c0f441070040740301ea014140c0740031600c1d00514080e80c03c00300085094075103002440c1810035128011401925001c03195800ca07410503184406100c0300603014000300c1c0103800058130f1010425503000d42500700a4155082000c282c100318005078425052102d900c1c1d040199090035118103000300300741c0b082103850148034152084180d00400038200e946c01450f02894403400c032198050b00c101026041006240c131513501c14000c040203c0c1400101011004000071000e041d6041a00c03650b1911b0b080810556007800320f00c8003120412420002c01600842e502e202c0f50000b88102141010044645009041403000080e42d0303040500d071900c04821158006401d40d00174006903807050360205040c0c1c2e21800540351443c050800448041801118500050702c1c1c05942d0100c40388216684070101840141900300c10101d001501b0701d008a005442c007440241814030380203181c142703000d0001c902d0400340c0d1401242003103010000700d010064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 427019667 1250 427018417 427018447
    0xc030219020c09040611091008091005040b28090302010b0f03033f100e06010c080a05131205010c020d030e0a080327060907050a0e1810020f 62
    0x500c1100340050450b421075200850303a40e040090014020940780d0781038050500c46c80c001c681103c100038040c05c904905690000e0318922055070008050f102d1541c2481401c000c51080f1030050741e10085681c403648400c1d10b000c6075540c4002d03032451445095000b40111003258030417080c1c001d1017600045041d100711070030040c2044c10507801e035000c0d4008002c0302c111049052403841c03202c0e4011064659a400194581840500c0345070350901303410403142805050900310070660202c444041c042c0b01a55545001185c6404002d42d0040062000b840441405030040b0050101d01021104c00440350f599903603003250a202940040d02c650359140200802c07103605000000e41018039040a0001194040540d651541c241002400e000001302c0403d201e0040700000740c00d1100d5800300204003c0e041c000745901d4803800da030261090300c42c2503c000b03868142004188115202c124a04030103640d440b50304a0f004808146401e2903014151300c0d46403041891010300b0141031284003041e2140031440840341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 427020917 1250 427019667 427019707
    0x190e0a14010510031e060905101208070b091f090c090b1e0303090904081b0c090708040f050d0e1e090105060d0902090103060c030b0d02031b0604090c0302 68
    0x300500309005101a8440383c01c450044070207442c2c00190b1070340c4200b0303c081080083d21043c0070242402c2000504032060340280307005034601d000380d80d292541c845440340d143e040140001d180203814803288011030340300c26290360f0001c000740a0b200d801180d2600b00740100103440d00118070030390791035000c804e0007540c4103103001404040c00b041100c2101d50300080c03500200e29405001103107407051241401d03201401a81e51202015059517581d080914215525800c2049452503c3e02e10701001841c2000005140c070350f900e000b03410460780f51601c000403070b4410f80050081e5104504c5014504c0018810861100203130803589c3e501c000c9407044001c226441c003405800c5421134541104015960b511a244241107420071102da0f96a1422a15440c02811101c40069404401c600000050004640000750f4480a0341e800300004400380701005051101b60700040d402d41c0c04040134420400d0203000e06500c07518003c01103828681d540842e1000c1c0c44440401a0002e9000f05101d0641c070881d51801c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 427022167 1250 427020917 427020941
    0x190606030e061003022409040230041e03030207050a030f0f0503060603070503070c08070b07120e060406470604030503090d060e1603031d0108060f190e0a 68
    0x219041c0c51a0000784140909000d07810007980b1004100100701c07441b00882d0310300c1c08090415500c582c403108209514045480e440038051070395625924806500c0940684a594032800c2a9015090308080c100c0040030050100c0a0550822002021440800108400c24070a40d90802080502c0c403004003103503d50340a010070301c1001d206109599490a0030f4a0307211440d8640b0300e850784d6800070f0440c1d000070501806020807000054207420b0250303518200380320390304a854a070b09001620070190121001e1440c031080300d4100d0000b1800081340c40c1c03c10288403050036070325401040c4814184030240f0682c105080101c00700003144850148a822203100f081c000c49190342842d1858540c81d4a80c418048044d200317200d180011010440c00794022444061000d0440b0101500164050900c0c03440c0e00040e80403c041540c00e4030b084a100900040810040c0c0d00c121650b11100c0520425450a00c1c0c0d455000c02c2507440c5040d01040000d0000c002d1111805481e000d062459002d42260030381c601c44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 427023417 1250 427022167 427022191
    0x31427010f1202090a0f0303020d030b12100c18080109020a08010507080406090f0c0e07020f0f070603051005040c0f0e100e090a140108010c090503031908190606030e06 74
    0x60501c03a000a01da011455000b04003590700d43c10403000403001c500b2500200c0b00100c0300d603408403c0c1540040c4180c03400d80980c03001c01c403994880e41041300c0603101d114410030031390052a200240075031682000d80480c40d241402443d80103860700b02480e02d04243c00c0781c00241c0d920b444010551030f04207016070041060900801607818500401403d968004101070241c0f620b92458804125a880c00340e0049508804141c12460311200030142c1040c00b691684018810800a03660000780440c81c50303c1000c105008254891800c902a0080c0c0801001d0020084100c900081c141d103c13405907180b103003000c0d92400305500d03aa0802516048400d001d00d03006484c0c01040a0400e03403c00c40411104030120b4480000703079030398090030001d024003103c0107201d540910000100c2810542140d98103400507207584420071b032201c080c10ba6901031541c0b10382c801c4011503012000302d801200c40c030350060191013400d490748400d01c400005580d2640d21290010703545048030007240ec4203001981e0090041100e03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 427024667 1250 427023417 427023437
    0xa170105040212180c04050f071112040611030418021213050a020409060e150106090b030c0909040807080c0304090516020d12020927010e0f0103060903142701 70
    0xc1d4080080050030703240b0707081c2d00075802e1a0b07134001041040c00305400200240040d1070807811010040c0000d903481c00c0404c400c520318605100d008904d90030301480549a841c2450300d0240119007015200c501c5451034001000045040102e00078040c281030501c800242c0d072005081502d40c000e0b0001010401d210380c0c08119000010b102094943c14107404030343c0400d07180c0303003800c15600034035658408070142d2140a01c00704100e84483c61890496010b074894084196907000c9100091004071045035448604100745402e5143c0380c140301c2c0c0c22074001c005841c14004c1d595103007a2150300217016a070290348041400c00943c0c00a010702d9503c4045a80b10311548589210081d42e01c040c0c1030b0503442808070742188020541c1180d8103807041c005005000e418290002d616141500302442c0c4420b510890100000c0b8400c000008140d024000c0b00d1807280700b982c60340c0c561000401c9510800c40c10403010620303440000c83d003440074107040c61003404440c02d4140032080350740300520030817a0f041c184240400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 427025917 1250 427024667 427024687
    0xf150a080d03020319090c0609060c0c120f02030f01150f050607020f01120207060e0d05092115010e060406050301050606070204020d0b0307030308180105010e070507060b04020a1701050402 83
    0x10200e201c0205800c0140c0c07a0b0f01c0d50f5030748010300b4540c24583c03c08149090b1072681804480e0720980b04581403a00e0301028282c48000440b00d0990741000500030710509002080403811900032858654050545480c004409500190400101c081c0700c07566691910120411000e190002c103005050410030710a05038900000b10340c1714090030318042d116001e584445000d03a4080c07401128050800741f41150760340c41c0307890b040000b481581c0c0c0f28001031096186003202c6900030011240ca8420081c00c00c840340380c042000080700820010000030f5801807541a2005604604d80c00f8003030509100050390340c2c17401c841400210b61040c0e22841c800d038108002e22406886640c2210401c07501030301d0150359608a4001c0c0e0000d0512541d0454140c0705184002040c9a03004c048107015103101d00081e00c200c44078005450a035034081c00340b11014480e44010070149400341c4010710b0307540c1c03003400007240200e200030008040b43c1150b030448012446110f090f2000e903c07100d04003409400b00701c2d011410f1501d016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 427027167 1250 427025917 427025923
    0x230d05070201080117010e030a03020d1d0319170f09150f061002010908040f1e0605030f0601020a060e0c032103010b1303120509040c0804050a0b1e0f150a08 69
    0x203c01d41178600400701003000c24210a4004000c080d40041c1182c2d550f0b100c10000500941c040070186003158070305424600c06500d00345011000c01e00c5c1e40011810114a032b003425503140188d40f26275081c40000200111850400d490aa1041940011801d00c80c584241d4490600c0c0394004aa501071004004000ca5258202003150300a541501c900820781c52141050b0300501c902540688048404200021803019910404003500c0251440d2001707003192103000c0541c400640203403400b01782c0c24800107000031566a08982c1c40b21052046501e108542e84425084900550010b0a1500f0400065027582010400418005481d040d040f020307400c0383e005c1a99500041c0a002c41400c00022998008111801c2c144c010311f8006c580c000d01c011000c0d1000d0600d6000740e8410b40600d013000354000400d030040c0c81302442940c018000c7c10000e403060303552098920300280544a18000030348500c003401024080d0704c1c824841c00c5204840d80c01c0c40c00014421005030b030300042c03240502c5082480201d03004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 427028417 1250 427027167 427027169
    0x170103150f0c2003040801061e0501050a0206070e010c021905041802030a0f03050c03030901022701050a082a030a3b03040b0313020a09060f031e230d050702010801 72
    0x490307200e0b80780d90000768024294171030faa00903089582003a0700411440242105808400210300c0480e40c0c041e52440150395a004a10707015016030004070004090b1402002610508c0e01c0514042c41103820617070005000c40c0725100d07a18400840000c0601003400c061280608201c401d451203038014603503034002a5104c1d00e400009103402c1c2e16a0240082502600036200074120707050a0340e80780e01e4290b40d500d000703400c0080703199203508051900c40d0b10400404899003200c070041e500d02e49045004d90055585101c0908060b2100070215080b480e01012405041c1c0f4600e942c43c1820f94a04001140c601618401c170788030300ca620701e46881144400110440000051a9410422145c20300003100b0f0f800d50140354014007004c9000030800460409020740340241030702c225000e0605903103e48414040341c015000da2088920090401d2010641d010300d4005250b0b1007040b11603101c203080d41d030000400d6412142124a5142c2d80e0000322100040c081035802c52824a0240e003005507030b0300003d28032101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 427029667 1250 427028417 427028447
    0x15060d0902030a141b010918152409050f03071205160b03010302031005071d0402070c0b09180609060609010c050703031110060302060706020901170103150f0c 70
    0x20310800801152418407441418640100c0d00002c82e004200707081d40c9030a1400e0582d017801002d03400c1004150700580c0e041d01550b01c4007181d00340c00c0d001642e0305002080c4881e06200d84802c0c82e00000368240c91031924240401d40005112034403d0940030140c1a2074036070704058400c01a2481c64000c6440c0051002c0032510b14900c1042c4603045400c3c9103044c14200c03400140c0d484509440895030020010055048a00c20b070704450342d11a89140076000c4980564816001070142d040d204510b20000160b2560b005009200510b0007140340d035007000d20306031544200300a22004c22641600d00d040700c1004441005103420034a1480d0000002d950400000e05a80c0702e03403030100b9076240e00d034412071071095020b50000c1220071441c0c0700d04000d0206481c41022a1240c490101190b50001b840e00507801141d0340540503e0a0100700da83c1d405c0650007000080b4100001340342c080300c00c000c03d4030026000f140991700031108a40074009210032f54005180c0e4034500c03030914a1189080758400d280700c4c00044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 427030917 1250 427029667 427029671
    0x2030c0d030c050712030c0e060c060f090f0105010f0f0f0b09090424091e030806150c19150c1719091a06030604030c11030307060c030507030515060d 66
    0x400500503503550041c10f0002e008804038001740d69000f43c141e8003141032508961248810030000004024080c806c4400c0e2134003940184001c81c140e8400030503c1d0341c020800ea02501e04c8600b0165040382103030001d900c241d0310402c5e829405c01c100552700c201800a007a43e40285070849041c00c2552805120312034889000d110600d0001d003c3c4200d00518180a0740c40355541c00000350260060b8001e016980c20a071100380d05250803050034246042115600c070350545a1215582d5241c1c10803141c500a003100359203802c0c08000d0209401c80c00d101e28400310460404030720090f005402d0003803081c00e036089030090007440e100b09007503220381022102d581180c4910845407070340d6138101c1d0744455003c5045007981c4c542c00c1844480400c20507200ea070107446034201c2d40200c2039843c20109070395941c06850150229000c01e4544000c900318480b59410b580000c0e007141d01d40b11143d520703c000c6801d40f1f84c1000c0040d68480501000c55030601445410122485040c8011000030000034580d108030481ca15803d0303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 427032167 1250 427030917 427030931
    0x30708030c03060a0f0303020619050702070603020705010f14100b0405060d020903010e01290402030105060901110c0a0e0403120b101b020904050a0c060302070507090c1b03020d0f02030c0d03 84
    0x7540b030200d04c501900d42c00503481070055503031034060344d9240c0607203000000200b80b014404d0f940031503128143c401c0099038001e001062030180194000c0d0310600b010340f40c9540f51018695040361318040c1030f0f0340b490700840402c4203240c60012006d80c80c400d50020b50910350f003000100f003107590309403c2e200c40d4000c1402c0143c1e56001c08000a00420b90200b200040d942401c00e0700b20380440000003a0129882200f11500300c81d41c600410080744024060182d0151080c0034548955102c1d40701803d203002000c044900e15081100000c40c03064096000720b88003151041044105640300711074509102c1074682c24848948040001905c4401994401c0b080002c0e46601c4080700c001c5511002d001070b0080c10801035404c180c01d1071a118a41c80d4425240d00c51060b00019901d8800d2080728901e0380c1001c0940401c41c200b0100e0700c040e00351035495104004104100c28404c0121107112609644260001c024040c00e101d0b000d40b00c00522a00d45055410074403560384000000b150040480a26140000b500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 427033417 1250 427032167 427032169
    0x806061c05120a030c080606030a0504050a1a101502060612160801020c060105010c11040c030f050f06040c050f07121814031902031e010b1002061503030708030c0306 73
    0x25010040000d401846440b4034a0203840081c07005041d4024030707035000d110b040c008443c04e4070144000c0d504680c10000410006183d07554a9108680140c070500603902940e210391a04520b02c1c501110100d0354241000c01c1c000d24014000c0320000602c1c000c000076a040c510803002170340710680102664015000040c440c000c0b44420f01c420175411801030100e842d429150f8280034002e41101c4031251840c8500c03000800e8540c003079500c1c0718502d68020181c521441c3c0080038407029000700001c87c001d040c0c41c0d8000d103400d0103090181030b00c201c22040c2041c0702860300c00104000d0314400003500080c07080420003203a00840302003c452009800c410120914441c5010498204440c8002c0041002e402400070441103218600203802c00022404c40f84006c1088102c0704c503080c00754000950681c441ca100201c48841c4201440020784114000225402864040f90541960452040050f08080208040c003090f005031041401001d600940c1003c000e5542e2965034803010780720400c0031102100040d81c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 427034667 1250 427033417 427033459
    0x4061d06010909150305060a05090604080a0504030b01170d110312130f0f050f01020406051804060b0d142d13080d0509300901090503030711030d030501080606 70
    0x180428001013102102610400310310681a0204481038002e0002040d1b04000341e004841c0500c1610019211a850b281c0e02d0340040d600c00035440c000c2c040c09010000110300f4a1918500801100c8042d689080f060744c81582841001512007050100d14054071030ba41c40004144c0e420f50000d070a95403d00c1e01c1d01c0b14000041d19001c0d070010044280e8940d001b003000b03c0ca581600c4407034400c1c82113542c840140b4800b18281d0040340102030004805010701901d51580781807a0390290800f0f00009031550b21a030303100302150300070790302e655030140c0307800c00300c1440964581180e41c0b05600e42c1d003a2514448072111981d552540c06141c04001c0361946c0450710114004210801c0319503c00c0d11980c1d6102c3c00d074566400b4060840e0400c51500403050303c2142c00c8885082e00d016503110741408412003424080401c00c1e0780080c0640c80c10040c43c0c0501140300c0e00c0c01c100801ca514050b0607021b0856000c1c204142c0b030b0020071040581010b007418010070004500090103900f00350704131340580410200c0c1004001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 427035917 1250 427034667 427034669
    0x6120b09011e09060509060907110a06020a17010302130e151311030c090c0c070807030c0524040323010c0906080108011e051003050a1505010504061d060109 69
    0x540808080300000d50110300c00d401110940d400003001c071560f55110409011500d1901c180c5810920001c0040d201d07241081c0800e40c000c0e031700d003400c0e0113442d24449150710b00540c0100072034205500068a0f00002c1d00300d40c21503544210081004015811030307000c100d03007203c03184045c919581c840d0b100d002507001c00d00460195415500e10009940b07001007110f14264582201501c024040d00351082d043c0c100851601da50038405000601d203900c038040b02442652024500034002c0c010010041081c10083c8240c0d4000c501444a60b29040d04002c1001030107802820410030312241d140b001050350010030261800c4036007040c0b8010300c09150030603400004005d01c0e0750016551800c02c0c0c002d1203d8200000d0020b0b5031995650711896a00c54400c030b0308030352042e12107007407654a803290040c40c0c802c55008203600c0440b980821505940c0d0382d50784c41c949182d41e2011114444103402806c202d0311980306090040104440a2048516150000c00c840a5000f64007010404800008840da400340c04204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 427037167 1250 427035917 427035919
    0x303020c0d0519080c070f05070513020d0506120a08070c03021503070e0102031c0b0604030b040317060319060b011403010b1e0310060c0312020a0e041b050406120b 72
    0x581034506120010702d19400141041100c0c1c990241c4003884901c16020940b10703100c4402e640c0d14021090301d41e8088840d0103071b0102c566205080d0003040e5502d40c034502c4040b090f0071040160b2251259120307181a660014650381c000c850454020035030200000e40640c046400c9902c20b5a40c00841c1072082410000c1e40010b034000d0b610003000820140484019446441c866545182242502e001241c507440303854540c90404009405030f11070f001c95640041d8010000608080c0780955943c0d84c50703501c2d00c049400343c0101b03200c00d0005a03c000b4103101d055101c4421005041082003502d5800320500301000041c1c440342e0782703810205040e4050700906018074a44081c2680b00d42c4e66140c1e0240c1c1e83d010760780900d80c011540e424003415245050689000310780240403018000e04103102107455800c410019010030082e486200c16000c100c0c4000c14880000f03036104100c28903440140801d54060729800b03065469070303090300750b240c0c0e90190a503025101da0f0b207403201200f0f0010f94070711f014000e50030030b903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 427038417 1250 427037167 427037173
    0xc1b0302030d0c05071e0b150406090f14011e06050c0c0d0b01080111070507030b1312081027022a06010515131818050609100b0a120303020c 62
    0x9008a41c2140c05409050b02c208881a070300c40c010401b4000740350050000500300f028070fa0108402030400012000b025401410014826980b140b4141c01e4901c40c01c0390f135070781a64400500085070780c10301113035014020040c90103048012000c48031228030894420101004804035840000341c109200035183d03103800414100c5403442070304142030090750a1041c044190b103080e007507001828264040c0c07603582d600400540600b40ca1030300c0d03008581c0002040c40c000e948002c0e400000250070b113112506810a41e65031840e0901d40845c02c46c840030000d400103081040040d111100b00080d1a81030348008800300d60158407041f001500c0d050990112050a500b20320fa84106e1004250025a4034101d4404913855038020466008035011071007a003913a2404d1150554050143d00030302c0d0881852404007610001d09108500546621002c2d08e04c0c044036103401080a002c081141001318001c070802c201402c00038401da071400159840540c0c8220600b80c01a152000700303040c029815612021a80415 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 427039667 1250 427038417 427038431
    0x10804021c060507020106121e0c050a0b0a1b0f061e0e011505010e0105030106080411060f031f061b1406010806070f030501030f02041e0c0309150c1b0302030d 70
    0x4403001400c0f089400900540ca00000004c001c0d01c41c101c210310702c50300810403507483c075112100200c0188442805884080c0761800c002100d031909580c078001010340c4042e03603407501a418401410380300140c01d80103c0310042c9c0301c0e400c0412003010303000c0c1c0700540c4610005648042c0080030003820b4031760b000c0480c0ba54501880200412019000045107410001c00410320648410040d102688000c00c3d241c001340e01400144045070184401c1034010f40250040001c8040702070000764035a03c40358151a01d8030340072080c01444020003840820b203049000c0b202d0002810803100a101807211120020440344803500403040c4202400f101145071088400c0d600d0301c5d138444010580d580b100755440f00001e6100d01c540c0b44c000b4802d2050506990303000004005218003a001c200c00780c540703035492800c0040c080740200c0755452644191100c035080341d2808148440503042c048808030400302d030340940d1402c07e001000010303071050040000059000400b4070500280c2000c07840c6004000425041a1400c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 427040917 1250 427039667 427039673
    0x10020c070603050c04030b04080c030715091a04080a030221090718050906190b181803070804030b1003321c030b0402090d260c0309010804021c 63
    0x81035000d0780e501d03450622a40e1107500c41c580c107512a038070015040c616444085000070b1104030007404c00c01e0f48002200c1c24140c080d1113440c102452023010165607661401600c082000886980d0225113070703122800400e1800c2d494503880c81c0704022007001012b500081203110801540c03010b2851021071403240d250751400a00080c1d840358a0700800820700031409284100d04054060706106002d140c000e8003043e112200500300315001c20010105041c2c441c50081d0300350311100b92924042140c0c1508502ca0300300b07102000225280c00418010070740003003100001180415080b40c2c00c4035030062483e1003540c2d038079980b0501c042c41d0340c1004088814903041154183e0740000402c5003c3c45206945030b40c440030f81017055681d958240c0c0b5000c903100c0b410f98100e1103070113039100c0b02d250400603101500d4024000001031180d4500c58045071015030100c420351190364100080d040100318400703410f10300360314071120580d40d00032044128100304098000804546400d102e01d9044c01c0000c42035026003520b0302d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 427042167 1250 427040917 427040923
    0xb16030f090b030f1e1e070e030303040501060501080601090308030f0c090303030702010603062711120709091202061e0603010b04050420150a120216050703110105030f060607020310020c 82
    0xe1143d141c442c80800d85c0104c0b004401494502800290038181951003c03603100d44005000180302906116089400c0546514144001d600c60303880780c03000080941c1030000142c540c902c05808541003050005040c400a02482e048076040840e104072001151b40324401c507200d40c480d980c0103030f40501001c01400030040c0c05402c04c00a0702d05ca0310081c001e074194540400704080b40001d000c0024003075080610040307003140014500e0ad0501511107403044d404205114501110f55200349052a9910700110a0200d80488020348142900c0030340b5450070b000030b1120740e440001f04a1040c0b80407803400b055081c5d8003503000c5400041e01810a0040d0314140c2001300e4900748040040700c003c01484442c00c600d1a000e12908a0310f198064541d08000d440c40301121840840f08032603918507401c1200f05450217107029442c2103544100000d100190841c642002e0aa0800d111241800801d102740044803242064159108006549040d110802800002c3c0f0385881442080b01c0c40d4070010314440d940e1404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 427043417 1250 427042167 427042171
    0x20f0c0303040c1a0306090414030a0e18040803012607060e01030b03120d020a0306030203070305160e0105030705040c0c0b01140f2704020d0b0907030303060b16030f090b030f 77
    0x4400b20310f002e50356408299107800d811410820048820000a8540e1800c41540e54000d0701840c4d10018000e80210341c0b81c40c0d80d0249009002007000940e0f000806d103040d005014a504000c03003110601e0409a4031480c1c01e0006000340d60541d003000001925122031116090520b146460803a04925907a5601071304040da030103030060000b4107007400140c43d4100040d8200c20a81414129490560200f1001009401142c101000c01d0740f604000800760b54208248000b840c0144090070907461424804942c4080690020690f8070f00d18004110950703000c11007004485040d140460502d8030040c04580001d01054003c10504010700003180054400c1094003403c02c3c1a62a400e412418504000d054910850341403131450795a0b00000f06614544000d07a0030620203454500c00f6100c43d550224140011107c900050380485410030030b05925004610050040e03804540c5421450254200c01912402c406001c3c4050502f1000e415031003500c00b00c00400d84884c078981c480c20700103000d800090301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 427044667 1250 427043417 427043423
    0x11103030705120c1201030303020306121f180c1a04090c0806010e0d0b012d080102091003060302130e07180b040b030123060a090c0809152404020f0c030304 69
    0x510000039041d21814400c0320142ea5100017029142d03840d541d0104c1c069800100b200360040102c0303803842d108940c1003024404407158212425032070000e500030a411545a4407400c90b5107441a566200843c842180200c1039074030301c203030700300109140c024045242d1042d58400400d01e45000e2580c00b40c143d10503030650290000760f8589a52403603d40402c03540d10302ca10f00151a02040100402142800760500d484141003000b000204040314500075004c81c0c690380c00070802e40d400190001c49850038030a9400c01c80c0450508004440c01c40c0c000c141056400e1006440c556610103040305283c504000f594010801011040150400307124000090036280c1990344c001d908040c0300c94064501030144030303007800c0b214603250100103106084103441d09000d8052500152018004200d011080c0104800c080007a00c44106d00e044c0204280c0c500041c22001c40c103404115001d12000c49000f07401861112048501d20740c01c2100100000c00074400e01110291124000501801d0315202101031489030b80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 427045917 1250 427044667 427044697
    0x20a0e0f0f0c0406110f0106060203070314030c03010e090a02040e070306151a07110d060636021b030c0a051c02030706051f0f080c01030227011103030705 68
    0xd40307007520200d6030300545051220540500043c403d03103204c0c803541c0000803018011a0940e00042c4c518a00310760090f0000e80c0141c200041010500d900485101c48500381082c0c80f924610386500f00c0c2840f0700040c01440400d08640000c0b0f88048801c00c0002c5070107400400401103911458080d0307035a2481c61200726035150a004007064100170b8007010f801147e000ca4942040d01c0142c145c1c40d840c40d40890f500b21001507001044000903114609101c0d0b80e280310b51400501d80b07007004804813508170340400d10800070401e104d0349400014032806942c001c0c0d14208002d078444000c071035801c0c60064254090031082c480890003d000f05e0000074a00403450080c001e0b501000d01c5078000da07044410900005001d6402003181d44001f0301264001c652011204101c810720840400307545c502a21507612911207004030f07a401380f001003401e20000324a0042420b00310700e800c020001c031542d1415110104844410316107080301669008441ea8100c00502e581900c0e900e01c0c0100380a0482d420485004583c20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 427047167 1250 427045917 427045921
    0x13150e0306040209040308090a1209030c0e06010e1c050a06050f090f030a0f0306080d0201140a060e0c03041e050d0212031e0703020408121e04180513020a0e0f 70
    0x4100895842e00441c0c0150103024265943e850650320080c2c050702c0a0307280d1088039110404030792080315103922291103940707065180e03155051450b005603060704090010040c090500c01070742c0c5c205100d209c0800080c1c40450762202c684a004003541e0005401410700d0084900070307810071105600151040820703c841a01c26104c0d405125681c200c40d4280c00b413168810400c2445540c0a81700d1402400410315004c100c1d00d0301d0b41e4083e4148001d440d501c07000760703459002d000e40103102c02c0b100c2680080c1701d140810081c0d1800108a08580d0040c00003001c1e4440040442c5c24408807100030084502c4503402c412280005260065442d0080912000180103042c0500e0391202d65000b00c1340920400148030342c1c0096403143c0107020100280004090560030880092294030034080c0c040c0d0060305458103602c03210740c227000458131912552041180c1a0401050002d0344240031203203454003010900060390b17a134800100302041d4440d840658003501034200012260326122846120b81c500781e01e0300c2c2440e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 427048417 1250 427047167 427047169
    0x10e090105010501050a031104150509010807050a021f140f010f0f050609010503062e18032604120b04020102010b030105040c0501031a04110405031e0706050f13150e 73
    0x22a028003c06000840400070b41790001d100b6080f03030480c00c040025091620390f60344821a28086c1107412000801c802250008079980c101c0c8000f0f80c082664100700746003000c1d0000080d1a03410070458042c0c00308004442c0e0054203265030141c40740403041585501ca904200408500c0c0820902c40d20030a40034108000c04c9050810906c081241c00281c01d460600562500654030b1340c100514294009a01840007110190098810900c1100c4e140c52882180440b401c01441400c099010309282d15502c401000055500c4256004416501106480c04070090400703020382d110f594421a41e0000626113441071000243d0310a0045200b60000c0122051220a2600341c40c41102c004d0b042440c130751401c100c154001d03006210b007070050076101c2c01c00002010003c0e0440306c00310304a0030500b0000c41c041c0880d0404000580b48ac003d601e6003803004241943c01a40d6910b1640035000410001080e05903009684c4019108440307055a0b54518490310ad0303451046c00c11180700d88a00203402e0210340042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 427049667 1250 427048417 427048421
    0xb03091612030509010522090c0f1d0402070c080105250c020a050f010201110705031b0a150209150711040c030e06040b04110907090513052502190605010e0901 70
    0x40c140d4540c0324582002c07111401135946420151001907c000c42841c0f440039021240e0203171024041c1154001030115450030010074030580701060806101c1c1d03494540ca98408070544a82c07240c48119400350341c402d014605016010801d038002c0e1801c1d8200ba0030b2106007205216520403c03c0c102c00d241044110b102804c480307602d448103000c1c3d0020501c2c5800c0c03046e81001403100c2c6900c2810b000100c0d20030000e0501002981c0544800d13102d6030000b0031482541c084140030324070b104400b13000400b0322185540383c81207071020842d00705225640c00036401c0416101c03049845115004031248030f495451034140810f81b880ba0413140c3c0c0c452860240170240b4103000348189009001900014402650b8a41d101001003030084e00c150b44070070440146920b50350f61160054403582e0507656000201d031601c4140030245008000c02040c05040c401040011034584003002074030b070812a1080c5144800d424140d080c14a212000034070704c410380d01039805008054100e24120744850a070307150b140c0da400002c0c900f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 427050917 1250 427049667 427049699
    0xb18100f091221020901080604200a090e01051f0c0203160e090c1e010c020a1a04060201050c0708031303110304060e0f0301150302150903060a05040203011407080c0a0203040b030916 80
    0x2010503d1f41340810840c0c14981d10021580103c940f1048440d40c40750103000c583d400100c54080001c0b0030410500690603400c7d84940101f000755240111002c8400765481003c03440780000080010201c10082907540400540408540c90301042c4121a201e00c3d000c001e83c001210710010038444c080721002c1500300000d00340c00b01c440186140300358044030740044072540d0b580e05081c1d0340010303213140114545403601482551710044181107a40d852400c640030b42901c1c40108002c0c51454148001e8003c11146401c032a032101065103a030500d84c4a9103001c0e946400d100080c52200d01c4045404603080b5080204429410320407511401a00014010542600c03555080b40c018511100020001410504007125450f0f612001c018140800c45000c289844411103d4142103074440040c1f00660800b81318500c5101a4181074038441c0c900541c02400064020300b10000703031600044d1100c1481d20900c1960017401d00c40c0001681ca0800c0040160360f980490401200c02c3c200140014a41105101101c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 427052167 1250 427050917 427050919
    0x170601080a09080408100c0f140d020a031e0203010f081c210e030a0306050f0d020f030f15011a0c0d200d0207030b18100f0912210209 59
    0x2146507a520301074440540040d42c002c0300c1c0c61000707000100d11007100b40084940c560b0f00150014008030072100c0106400d2101d100c0009110f0a81c048840842e90501251049503440401590b1012442c60840082c10300880d9018003000b40d0305004441c82c07850700150f04172001282a4540c0c00d845015071920b90301c4400c011000b20790034020155509000b0062411006020344940c841c100c160400c01e000e40f8201c2c0e0101d601da0f000019003180d09501407140c82e01806094408101010958012480b40315a12601030700c00c03000001000126039040224244213040803056410480a0007511646140280614503000d02d0760700b0201c20011441003500c048604070401440d0380f50305400c050725110180c981e42c42500c40500c4004640c500d0401041820302e00a50003007023094590300f402c4c1e0030f101000d0315001c100300303903030a030001100c600165620748980c8001c0005071072140c0031401c8004188114000b030040c2003003c111b02c0126000844c4100214081c00c1e425900e52245000310224402c84d00b01c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 427053417 1250 427052167 427052177
    0x60509010e040e0a0803040503030108010c0f0c0204091704030803040c0501111018080c060901060902041203030f0e150412020321190608030d0e030903060712060b0a0e01170601 78
    0x12034500d1410b03400851071180fa8034291401141d8544440c5810740c01100c0503a003551000004001083c0e00b4400d482c080d03110b07413030506c0386c0d419000002020000f4881012b071040380c070740490b0b00910501d034922454000e8502c9885a031540d5900e00148503400c01c40d800d0700c10f01d00c824000940d550150389580341c1035504001400740e9140361780806008042001000108141c038040240006410100505000114a00810303681ca082c01d00e40c1c0c25100d440e04040c011500510041144440c0c800000401035032505000ca180200e18450360002c06000041c01e01c10303c01e04011000c0820b01181c80ca0040d40100c082e0140c200102c00107a81d6486a4641c50100505941d45242d54075000d140303040c3c206608080000c000b141518169040c0e4585030001c0516420000d8164810409407241c0b090a07903d28010b1410f25480100103512110014801800c0c0002862500d98400c40d0390f01000240401c100b002e625480d2101c3c2c0240b018207407804060104001102d10514103d4100e40b07507101e408140e42d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 427054667 1250 427053417 427053437
    0x9030b2e050102061e0c0c03070b0f01090b030c090a0b0325030b0a1a010e0103090f0c141203040e0c1201030b010603050f10171009050a0b011a19170703090c06050901 73
    0x256104980c007250070100c0c1808144032720380009002c90301c0180204c1ea02c0b510003020b9410a0791010481e0900b05105200f40c0c003406402c0010b4a4864002d035014034140d000080402c158008030b814403c8a8098401d40b1407003003607808982e084010801c05407070041c014444141e5508503048100c0f203542c00c13850507000b8281810708880d0301c00c5001c001017200626010410810a0742c550b2303441101c1c148100d80c5041901410b100301100b04a09900e40c0500b00c03001001030840004030b40d207920450041c030706400c03038500000302d00755004030854041d11f8580300d58842c07542e5a82400b61504a0a00842001a00384800702d0000c80124040701d00500000140c00301d4145031042d10034800e805445191454010806c206c402615284540714849000d40b000c1d008007543d500d8001032102050b0011050342060803501c01e40c4200880c1542c0c040d041d2001d410307100d81035100c41500d01104e8140702100100200d03040101855041d0000716840c6d2144001000850f240d440c103030362900803040300c2400540c044503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 427055917 1250 427054667 427054681
    0x316062312060414041203180206090f0a0e07081603110a0c061803020c0f060403051506041d0c01020708070612050a09060e03031005040c09030b2e050102061e 70
    0x8450b802c03034002800050004050b40e00180a85021102920040c4c240b8400850698240c010f038043c0054103080041054442c0d80085e119014015402d4040c044c100e00d4000e0948920507400c0281c404100e48010501e03001e440100080422038040070070312030614041c49603502900541d906084110715041c18000d54510485260401e6201503a0aa40b42d460801000340c01200310000ca9000364054040c0d41811410300074031150703805419015540402040010801c04500800600007501c480800c0ea112000041c001d0481c103008080e0280b0440c8206411141c00915101c020800707800341c0f0b481d1941c0d51100c64590480340b04403401720704441d40c0f48000b42110350207603034406ea003800b00160404c00c0e5141c0c003003206d0481c0f040624541c0f00005100300706081c0d0034a04000c0c44100c0e0700340005810351500909410030391100030500551400400c0d00306040105101c1e00c0320200e28080c040c014000c01d800300118045c8a06800742c0203000129011310340030390107100c19030303410101422640c90f018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 427057167 1250 427055917 427055947
    0x71a0705180406030804060e031207050c1509061810111207020418080304150510140d061e060902040509040f0203070902031005040c1b061a03160623 66
    0x40640da42c86551003801000240d4940080c0001d4042551040b1401120b401407624201d43d4200c00c00c3c202c5001e00ca184005a4005003004560342d095800c0d0703581c1040005d40e00414010703a1030869210001048101041e0f10b564a000c0d280e0000701c407000d503441c40300002a204145580184a000d420580c07030540c044109000070649680b02500008a501d00521280101c0310115411504500000180b00038424040c024000d1000900400c000e81d0504101d001d40a44080c481e01502030a014106011070380c3e00034001a10b503800503000d11011050b035a44903840700100101c0d4140510307000c408240e0400324400e41d0103590001d0a9179200b034403652501460309840d003400f01e905202c2c488001c580d2211a001544c041e0072140a1400b00c0f500304010070064079001c000e00710411140091801510300d1100c0329070007050700060000b6180720361881c128120f0368000040c1d6018440c0b81081d03040d141d034480d6014202c1d256655042441240c05031507045401401d4403c40162809100003e07681c0448 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 427058417 1250 427057167 427057207
    0x50a0b070e0d050714100503041106040b1305040c020a200303130e0405150702060f04050316050a0c060f0c06051504110a02010e12043503071a0705 65
    0x1400e04000d9200103800084100308020403c4850790400a420070402c5500c1c809192060390459002100c030b00021402000d5000007800605420503d000039001c5494400403a005001000b0250340c0c1d030b61078035403042c2d0b10f815148101401a03203131a0251440030b1011034030100c21035201541000d151031044605003c0b1420880850781404104400800d445201c018031004100e040d00803035041c03506082041c1011100c480d0101404001000c004006501007040d9510040c1e0951101c1d5540356411311034a0350107070f003004c0003e40400004e400d080c0700e000111800d0b103034818240d41c1080c1d038036100b003140e14034800300c4000041030a003510b00b0001a540d07084207500891042000b8600e070050f20001d4192070b21846010341c03070100002d0a80c01564280648042c60300b540c401072985070728415980c3c00d14400d83c40303504100200c0304080725180132007040076029507145045540d800007205001a0301e9a02c114006c0b103c0c82c6110150101140400e41028861a401c9c0c1306e103403c0c480c40f485020609000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 427059667 1250 427058417 427058431
    0x910080a020c0613050d18170a08040f0e06042c0109050109030c0308180304050103090501150e010f14010807050307110a031d04020304110103020f1b030d06050904050a0b 75
    0x24442c01c0105881009460310401007204078000c1180e81d4100709062031030540e0a0310400140702220640250107174410400c680d64071a0b4800c05400c100da1150400d0300d900d00041400c1c400250001d5038240f0004035109031080340b01c120f101d03500c8403c04c0004480c00e810311000e07640610100344001002505120407100d00040000c04e40030410394032a400c40d4108c520850215042480c1311043c9607200380c4840c1d0100801d000c400032115000d00702036880c05240701e81070426807942500401c019081d081040c0250f440c3c680000344e99101e83c0180e5000000b402592540032090000080000d807005404902c44010b0f1942452078513000ea045805901c002c0c1800107119240d6054002140108030303807207204d4040d99840e240081c408885c1c560340360303d6071842440ba0b4010b02c14000400c041041030a00c3c1c0c0403d00740183c0d14103040002d0a03240c081d90200c03040585401d50702e0801c004d4040300a080e4070703114180c1045526225020000104015903014260b5806000340c1800170f17401c0315101c0c0c3c02040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 427060917 1250 427059667 427059671
    0x2120c160606180506121b0103020c07090c30180f030e01020606100e040c0e091e012709081e070c080d0c150f0f0b03060c0910080a 58
    0x206600c8190603104a5440350360403002c1071001000e440e42504c951030704100101c1c1c1c213121511840b020740d42d0b2200c68190344084504440b2000c0c002e42c0c02a4126100c81505005440304560341d04c440c1030041513504c01d614003080303410010745900c0c686c0c0351143e00080741d904170500c40c050f04060701030010410250801544120118440003007191454400c0b2118402d0756083c0c0720701e181c400020304110001c0c01143c01034011000040c026900100740304a01182594005400b0b001c12104903092204407208640014a4200313210500d0b01e84203544046e426030348007080d401e0740d845800d800f12990040820303c11801a070303440329003168290803021406c0e0007100c8140c00c00b641d09030480980d0752200c0e80c0d0040404005118010400c14601039002420200003070456095000400740000e000e0305070040c0040304081c880c0682c01c595500c022610740c1a4082000480d90002820b0300802240e02d40602c40d2240c680064820040c0d1002c4482100020b807108211140d441e07420740e1303100d2001e0250301e030840d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 427062167 1250 427060917 427060957
    0xb0a1d0c070804031e1406091209060706050702060103031d2101060e01091508191e0507030305031807050f01050d061a1c0e030313031205070e04060902120c 69
    0x54421481c2d200e104c8885c4100a1031200e00e46400c060801b41c04860141070f800c008100b02001c9804540c06940095003168207039594002400980d5512860100401140c600802d00003415070000791203040c0c903c01c2d00c0340102c000c0c4a004c00c40d40c1c00303040100c0356840122080081001404012105480e5081c0b80020070300c223032034220640741101e09820403d541596400e2200240103103002c200010030000c0b0280c56540d52400d046203481040b5840a8078140c100f0316540e100b040040c0807518002c2e0400301340d03242d40384c0781d180050007503009136000103030004142122808cc01020a410302111401890591048400c01c010b40300c41c0c10804054146e0356a4000004210300c05680d540e030080e002144260382c5d640e18400040040546240526400b0325018001d80c003520000112504003400001c6050110894941241ca4084100c01d4511560902040c080b82e61307044002811100c070121000d0000c00c0c0ca4240321003c038000d9103014000f081e040700208084a0001c03004080c500e118224000c041c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 427063417 1250 427062167 427062173
    0x5161722031707270308040603020c030d1803080702061306050a1104030f020117040308040f0c15090602011109150d060807080a231b06090409060b0a1d0c07080403 72
    0x822422030340b0a02051400c010500501c3d901303d0700d0030528100c407403006181429500c4010030f900690040a0030715600094010f80203500f00151000800064002d11070358000e80b000c0e0071802079090044000c51039107004684203d0001c1140d6100c0c001842c0704185507034039502c81c1c0014060281501c00713074a070f80b000d540b4610b01c02c030401040510b00501c803503051840c1c07610004020548204806089030413000034040001c2d03001c0b0499400c260030000b0103105940e0783c00c10300394025141d8002c0b0454440180c05001c06074000c0d000808440c0241c00810500c03440c141200301511480c1c00d019401011500c155040034080e0001d08035400740018002011078890700c5181c40d040a582006032036a0010f2080c0c01000284442000e50100300901c05a040d840300122039a100262a4400b01c1c0c40e800401154603612444140c03000c00000a0083c010f412141c00c020004200030320185015061915002c100080ca00e00a4000c54030f800300602c00c680c0d200481d0b40e0b410342105c0002c8a044800f04400004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 427064667 1250 427063417 427063457
    0x3090201050405041103090f0d0c030e0a0b2a03040627350d0f21020310060201110c0c0d050c04020d0218010c05030d02090a08010516172203 62
    0x3905c0900803d190780c0c0c0c00e0001d0700e1032401007403010680381a4019680c20b02540d070b1040712004020f91504004090b03e00c1d1900084c5070031a540c101404443c4046640c400042008a00c62002003081190390b120710008003160703407640304900400f0003044c070b0303140400c2e10495403800701c0c91001e16640881c031440340c5a420321004601c1416402000da034040385011070660811210000742100500140380700d11401001410030384500d0803203000e000070113240000524600701a2410044040030841d642c1c07400340c000710141c90742400f6850045d880c08451449031119034080750804008103000b082041d42040c100030700c0025015088516000b03260f1000a2612030b80040c20a50450b014003589a000300020034100c0c0c28502c074074604101c094158800031400220803220700014405026980b01c241c940410380741c0a4a50000c7c00540c82d180c00c02100c02c0303109840321310b070390019518a016082d1426851001c40340581d0070a0595051091851103082507011303442c0260b00c28100b1604e03107400523540007a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 427065917 1250 427064667 427064681
    0x5010f0e1909090b25030207080d060f06030c020a112b05030717092d180f0105010c0c0b03061816090501020106030c0b030c04030203030403080405090a0902090402010309020105040504 81
    0x2481d0b9141c107005070800225182550f0b005e0755003400200210000c4c42c0560480307030101d560100307050b8001425000d020540f421a10b110442c66000d11503965a500e03a405001c1c0c1078481c00001a242170440c3c107055202042807000c0c40d07000680b16040c44005020000c203000d107402d0003440c201400c091180c040c600f6103803005400b809a8041d40e15400c6a08160f90310281c1f840e60700755100d03803c010016483d43e44c0351031250158460101c010302134440018209038505a17070380d01684802c4003000c448494403240c0c038891090001190b0301d649640d8850040d582d41d49446002444c21a00201c180659041000510b80c042402850509100c41c52600c40e50310321000d40c0c40010001c00ca1000f80c86498208650000030103007807008000941c036680b55a00100010300540700f81c000c00101080190f580c0c9015134010f107800506a0f580e8170341e81c0c43c004156a0152051601949008002075416900341c4140001035402601200182d80d40d580118001c2c144c24004178148041440302180782d8a41d40b091031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 427067167 1250 427065917 427065929
    0x1b080706050705010c0e09270a061506030207050319170c090111241503070609080f0a1205070312150503010e0115060804030302120a0204091505010f0e19 68
    0x9540d6251034200035003580d0144030202d0920804c46e180031010f84641204983c0164a0700310244500345140d0586070000d9404007035143c51041c000c1da6001c2c400c17180d00c0119005210501c1051581e81c0700001e50076401001400382c80c0d82c1042c48110710108100c01044c12100061500e40c00100a8906490702003005541c800259100459640e4665030450010710500e0800401440851002c006001950100c08903408050307943c031000c10802420211240c8040100509503501203850b41e6000b01000c104e0f10600515102c1e80c0010203c3d00c5001c20080900ca400050301d00b062072200348103413203a500040f4106d08006003680c0301e403040e80442c419a02910058030303040701c14524010400d402c0d034600c55030501e85645000305c009000c0980198103800c9520906100d5100d80d500c0c2002d4009008401004850010440c104100011164010400e5451410081000304040c1000d46a07404185c0a15800b0030b111402020856000300c035540e00c6c1c2d1900400c4400410450112294011581c0e4404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 427068417 1250 427067167 427067177
    0xc0f0304150b0d150903091805090d0503060a0e151e10050412020f010c08120610180504020d0204090623030a150f0e06091608010e07031b080706 64
    0xc0740c80824001c9a00303031a03003100c040320101d959450350901c8104d20344902c030216540e10750b41d00416005200001c014128044180c11a8244c0701c1148090f00d007c0310700458074020348050b06d061600400c2940c0c0201e0740a808881542e06000d1311180c102c0003e466080b0780481c0305400e110955039030310017607585c0306020307503d41c0611000d0042c0021652088a04802c2c000e00f400180411a5050010444690100d401c03681240c61180140e07248ae51043c0d000d000c00900161010318140c40c0b5400c540901030130b4440489201c0b004504070340c002003914200100000e007842c104000d14041d00580150a10000010310b003941c5c410220049034010390120b6038000348240e0005044080d0349454901140030781c0034205900c01da6980300380024020340c1c403004103540c1d82480c1c0c1c40341e0380c01d510213a2451a03000c00c813141410804403455403000d8030f807030030074200c0b584100115425006000d42180004940d0090074443d055946202a030140d40700d400e80031a14042c1c3c00980c25104010a05c0100265224 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 427069667 1250 427068417 427068443
    0xa030902040b210c0a120206030a0b120105010f0b1204030c2301050a0501061e030c0c060903110d030c0c08092707110c0a0e0604110d1e09020312030c0f0304 69
    0x403e424203070f485220500c502d103c40c0c410001440841142ea0301250704452196030ba90381d80019200500c000c0a071650020749144503520101c00543c4a00d0507a004003a440b8980d65035840200040c2c400c0c1c0302d070206e0704603044011800290003020401103551041141c5441c22003159141003000000300c00c4200240c0d180d8080c4100644244280b80c0900b48a14180080c0104983c52070118038034910305200301640d60900144c000d01c183e80898102d503004c44244000340320350034014810440d030503107002c032030080d02d2075001c809000c1d2160800a0110b0b840e101881c209a44583e203650304001026600000c3d0350b91210006600d80b00704003000d6000720070364191800c081d0700c0145a00301800019480354000a200710013959416088011544040d0010803a96643c00109020b4800316010140684e00459030984070302540d002080e0032504440c15070704011a0030306640030f4852100019400d0781008001d21242207003040155401100c01108918003540440b0700a455402150165040c0340c6c0c540d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 427070917 1250 427069667 427069729
    0x1d1e041d030711060405100f0915170a06080c01030b040f0f060602211206012024010f0b0a0912050a0b01060315090f0e01020706090b0c03010b0a030902040b 69
    0x1000c3c86840714280d56507030030242000c000c10a402040c03101c00c0c040c8072a000028941512400107031028020319a00c040d508007183c0d0019200840410b2400301040400780000c1202c0b809118200c211885c8200170300381c0040c0b000064004012241005030402c0d107880000c601d080b00d80c081c000c0c7e0f80100190014040d4035050000b811f102607803681d1402c9095039840d01e10354651540c180d42401e003400c006a8020341711480143c80d0b580d0b141c80c1c0000c007040c021160300811500404c22020401150f0319141801300342288607003ca5a00340100384408291603c11300140000f003007d000c0b100081e040c9016410b4880c507421080a82108040b01c0aa00081840c010008844840e50042025003414080e81c25602c0079080c4510043c0aa5000c459030341c1c1c10303441341401542001140d064500d008543d51140b0342040d07009000c0e131342300950390f8803411004200010021400c1301c0c104d540e8180d01074101032103503074114050111040281c5c2d001391111107885480d600c0c051807003041040c1000e00b00030b120001c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 427072167 1250 427070917 427070933
    0x103200304110f0d050309010305060612070e04050112080f0a0302040305060103050102190507030e1306150302181009030b040c09110306030d03050106050a1808060403020703031d1e041d0307 84
    0x6200c00c1c01307544011000f60010383d0000540d41c1139042424040740c2603950302c0105a030750049502610440346404240b0501d075400030000d00c8040d0043d501800540e0f00c07102501c00d5940d40b25001006420100400380740080c10501407c082c50f0140307030162030b103540d0b516003d02e0f11500b0b0f04155038a035800034241e03c10b480140030345541d090007810051309080b41030710054000301e80d42c1d00c5540240a01d0020b19070018481d8844000b03030401500050101d004000d00030300035000441180c0c2d0070707007078080003404070710700f081c200350f000da51694541d0221400c5a9030300c0041640a0720488483c07001020206a003030340ba000d888100701c031040d41142c4900d000000c26203018021440b5006061a040040c442564081c08035a81c1c0c5859041c503601c104008418120703481045c0d8000240c034040c2c40709100c1055404103d01301180d0296444100011031000c101d462200700a08480e807021611250300841c081044900c20310a40007000051191a04c03154682a020121001c4090781c0000480c07004000c1c1c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 427073417 1250 427072167 427072189
    0x30f13030512031f0f050904031713051905120f0f07110108060a0f0b0c0a0606030803010e0c0a0c03031a040c050d0f0203010302031902150a031e0911010320030411 72
    0x8411403904c8640f520120705055101d038091180a03420040024080c5801590300f105421060f05d5600618500348054600c40001c1d03084c1140c1c9801000d1400b83c0b403224440c10046440c0c2c101002c1d0503048035008414103180d1104041c615604024410840007581110291100d1405082101900f41d07100c400105100002096140b1a200c290b009000107140002c0080580d0b4000851b6581c0d443c800e15114601846040001c2016007807034408010002003002450484c0c0b200302040d0850b0f110581104041e001c0d070601040018145280d00011070301c250891541c5088229811101c1031180002c10180c814130a104000f0540014281d48032450f42c0c0700350120a80401030031401c6505550002c0d03100c2404084440702514540040340c00d42d5602009100030b540c0100000781d40e0120544042c02400d0341c4028090307069440d503203604402c04a4000c80704a25031003040300c042d90303002d41e005400a203000c411540141d040407a0307180d5150440002180a05d00501070701c00340300c1c4000e00300100030283e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 427074667 1250 427073417 427073461
    0xc1a0601030e0f0d0f0507020406090b120f120a0528020d050703050301050f0a0506070312050703050114090702160612050601020c1311070f32030f1303051203 70
    0x5546036034107081d001c500c5015000c4c95241a216141489178119254000c0240c00f960103454440300166113903050f40b00503111401500e081441e034044406043c4c41c2e012000e540003894201c1620300c80c1d8280c2000081039600c5980c00c1640c2480e034410000404a1a0400901011130398480c00c00d07039403074042000c1000d080c1c0b00d1800520301507103564018420701061141c54002e2511000711062a994140801c001d41006003200d51940c44a0400801e50b0321a512028001c1389000c1c0801d21152185c01802e060f500a00e0f00240d8144640080c0010800d0040c100c80c114060b00c0da11580152408140301c2c000c00182c0d44003c160b4144001290843d40041c0030306055500103c100707480c43c2c40d03d4500c180002d55070b03840080d0808003030040542d43e114003400200301d8880144100108403094555864420409288015850300b007600031840344c0401e594183d1950082c403000c181d4403c04d04c02000a00010f40c81d15012558030358501d4605055160030040c5880040108019411194103010b030000b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 427075917 1250 427074667 427074673
    0x70515010b0a0509090612190b091b0915030609150c13050d15050c210705091309080307031d06010302060409050c130305100b01050315010f0c1a0601030e 68
    0x242c101800e6032240d529854000c0c40407100241142e0303a92400741008080460030795480c060121081d44010381d0340a002c03503002020f000460101407000588518100314a89445800301d040c60400c66031900c02420705542d81802c0c40103131000e8030107002041c00741c1c000000178203849106601c01080d07440c0085c4890481c1d002400b01d174410745900807402c400c031581a00c0c1b81c544100181810b010040d400009840721509040911402c00c45a9005289020038036105030312800d00c01c1c580101c4440140c0da074100040052241281c50b20b040d04c0d850168000d805000950035410b6a1200d40341e400886000300481e9540b10281c07100c1500400520400690b00302a1040390304540c0003590030b00850003a041e14550b204006000c074003010302201e003ca0154007065042581c1c0e46085070340d450341d509040a142e41019081103065003d8410b990041c1003140340004611a04401150000440c2096100b085414248070010074610500042d050301d03034444440c0b0501d0300f4000581900c1100c061408154 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 427077167 1250 427075917 427075927
    0x150f0506030c1002100c080103150507020c1203280e0d03090303032d0e070503010c08040618080c010506151603140903011a131b0c17070515010b 64
    0x198010401400c280421105569120143c1c20200c0c544210061100341862420b51003000f11034000103014102ca21035040801d807200295801002d45905650b8000981d002d03502c034010914001100300243c0d084078088a09161943c07007440000c070b0f8040e6910f8491400b0f520880c0e0410f074081c0b50b5810302281030b10060803034006690002c00d60716503071002500301951040c15040215503440745904106220300900102c141d1260070000401290380084600e11641000291904040c065540845420380b55002281da4603140ca00c0544030410703041603120002c250260001e80c01801520280305030100003c1c00d89003010910407131011290307448468100500c040030106004610b4101d00f50350524212100441d040140c90550080301000c9130f0550030f25440c0001c0088048000c2e04030b20003119164003c54280040b0022204d07100d007152458502903102483c5240243e80815201d8401d00202003445030120842d81705801280d422141c903004407200c5a12840e51007401400b41c01d842d00180d00d06 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 427078417 1250 427077167 427077169
    0x40c0309020a0e04240605150d05011502030f0705030d2a030b130b0d02060a020d08060402090a030f1713090b030615010f0e030102041401021b0303120a18150f0506 72
    0x381ca000c17000b4058824903244500811a0766070030080003000060000e40d050914040c00b504160007241404440518000c00000c4420181e06603258252068018520b03141303000d1070f1101294844001940c1d0f0b0b200400c0190410842032103131060440b0300740c4c52000341c00002100451160b0360720741640205410f01c200c1d50400e03540d400000005015801c00050750b002c0c12004952902040d10001e5804680071540115660700070075403940390002560b841c0890b076200d808200403405071100300e41cac001846801c1072000178075020401c03030114014400100c01c078600c0400103e03a0350082c003540ea114403030400104180c0b04540200300604900303d010f0003117403401e4003c41c3d01801140721064100900107441495490150031801c008000c051b00035036440f500c5008100e65140c090040c07a0051040402801004101c80030109008200401443c0b0b040f070f2081c0790041c3c0c0140a04181c28060f5130300140c402c0001c4110408240610c40d403215106812000c6401c01211000001c000d03d05007070004002d46 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 427079667 1250 427078417 427078433
    0x12016170304050105161a09030306040e1506100908070906030c05010f08040605060d020402030c120c0a050d05061507030206100f0812070501110a032c03090d0201030b040c0309020a0e04 82
    0x86c1c9011000d11a0200c0220f00f08081490070300308032559100118030a1088040000c0011840355600f42c405000c9894020b050b039a480c44415120f101821455000c580c0d5841c02c800410401c804515100400f540ca810781c2d00c2c01d1850580c000402d05544000c10020410400030080051000b402c0c180c0c0c80d001d07038460280c040d03580100014000c40d603a100194180d41c6100d414010030760054011500ca191003c05900f459101100e01040c0c18041000109034480d81e0741250703650083e9558a40c1086075000700c40000d0700e8050b007015800300c014003030f401800b0361140c050240c2d540203034001d02d0982454070386007040d0b0b085a005103044d01849034042c0142c0724001004115910035040c00c961704c501a04104e4010980042e007458490b070001289181103505800c1400c1c03800c20110030140400c1d00401030010015800c10b0b544080d0800d0011580c0fa04d80030800728070050040c10003040158103040000c045442c02c882e01404079584800490942c108440d00c071011f480a03021150003410b01d5260964 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 427080917 1250 427079667 427079677
    0x7030c090501350706030b0306010b2a010603120315090e03040b03092401030c12030813050c0a080f0c04090206030f04031b0309050306071706012016170304050105 72
    0xd8080985001c900b0301c00c1d81d0ba20701080c1c0b6662004c1e1581983c96810080242c48100c9600b4840e1250200108001200c03100f00e40c4d0002c4000340600b6164000104070548a98000b4040400c5d5030f070b800000041182d81401200100c0d150340d000030a18040185c0400d07c0445811201c04e031460302c0c500c941280d030000215000d0383c82c0000110348036514000c0701031800c0d01c18400506039a4450100c040307045081090755040c1c80c0701d5050340070b5040e2200381d08101c404c0e08010160024540380003003098030045030305070b0b468640603500307403819182d94501142d00801d140d801100541c2c0100c030b003600e404400317202002d0740303100840b0144a80303021600041c58501000c0c0039141a48400004102054080e100609440c102c515011529140d00d00700500148401d03c2130501030301540c0c00282400b441200d680c10903602d100750300209621004011a00c000c0d00f46194032460020b40300740a0002801c1004900b21504a5421100542406210000d00310084451440f50740f0a000500c1541e0f000000c1d20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 427082167 1250 427080917 427080959
    0x1501090b0102190302061317130f06080c0f0313140f0c01050403051203100317190c0506010308093705060f030f060f060a0c06060b04080714010c120207030c090501 72
    0x150b001102230511ba0f000c0c07080e803501001ca500c0c0000f09101e10060548030101110302c07040c0340282440d5604010303251000200c0390890800400c0100c42000c0d140341c3d01070342d0445801d29401e04010040e0b902c0c3c80c000308060344040c1095001c07540141e81c1207010000c20301070120071700c0d000d42403a05d1582c62903510980c0440314012503402100040e03140c80121100740c000c54000c520008044a1030244a005611508242140360016181c00103124007550003425501d038010003d100d16031840c2c40306503164210107549648014500c0380b401c404c505010742d100003d494800e091224004400090003860710982c08140201001d1007408040d5a404050329401280b24480c0c2e84c04d03541d1080021004012886020350140c000324a1103e095403040781d0b41e03040d522030403080106e03d03100c0039032203014011841502c800b031340000b20038800e00101041c010118030341810411542902c0f0355464605004883c10301c00142e101d00010024400c3c002c54a00080884110030011541802c946641c41d2084000f11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 427083417 1250 427082167 427082191
    0x408030405250303080708070c0201081b0d0e0606010201090201020d2102071a010501111906110307050c19120e030a0605090102090112060501020d111501090b010219030206 76
    0x141400018030000e0320b4420510000b20052488031a1101c00e120396000075000035aa0030700240e4514082c080c5640100c2c800d0700d480b50880300607401180d01100007000800f000304d2145000500c080045d0140c4010500700740007082c000d810003011880c081c0f0007018030b4116030400c1d2101c40940d0b00401d41c2d441040c2149460001c52219010807004030071006132280c080707440000c1d101709101c6000129150328408120058450f641c1c2c00044594001c041201002500500454001b416450301030031401c0e8803591001c1240208405541c0c800d070002c4030a13101080e0009041d188100040c00400e008110980c108042c90b1010f0b15441ca0003290070f032071402402041c441d20640740e9000c00016003010b502102c20300091908e90b200034080e421980c5914041025480b142c01c00000d1405140103031f0700c060b402010980c041c0d032011203440d010980c40c503140d40a2840702402a4035405591070107026580c1010036144001c000080c0303410859030201c010210402902c9001a5000ca403181c0c10000803281 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 427084667 1250 427083417 427083421
    0x9130612141f0b04050f060a060f0903020d0302010501030218100501030e15040606080c0405090c0d02060d1517031c0b0301020d0e07030624061808011802040f06060503040803 77
    0x501c514044106900054400c0091080484003840f07411a4078403a0090790180881c2c0c0300e01021010808040c4c0d0040e500034007011083c4103080c4140c02c19614000546400543c1e1641c81d004502248600c40055005075120801441981401108010740d00080c000c0390042d4600544514000041d60041504041d1100e42c503412008041014640501c203941818902d0f0800b031070071305d00604103480b416100d8024042c4090307481c43c0610569201d610148003420301014500c003040360119007030354220390025007800124021440c500c21b10024026000090340018201400160014038040345d0034210b500400c1101c24030036074a2481030b1820b07442e0101080c0b89140100090180c040e091203013809a2030300b418000c035841d000644408507030041d00204040b070216040c184000012500b481209240d90008000a40c4240110388800450030442c0d0b001d552522102030035620700083e2a0140303200d0004602c258540780c0315540c4101d5118404001c1c8600d4030001038594000240080c0143d440400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 427085917 1250 427084667 427084703
    0x203070c0510091710050a02090307120c0b1b0c0a0605090d0305040b0a091401080108060403052b090303060b0306010e0f1305090a060e010606080f1503010e0309130612 74
    0x6100c0a02943c0039074440740481da0420f9a0f40307900c80144145c01c0c0d07003408049110041c3c24070031a0100940034001d03080035800e00f40380c10000e11170014200c9581031406000107051307002e000a0b1480417603003403200c10820000a201803030100c0c2030550511406d047d0750100840e0750054200d0f80e100c4002e90320040529a00d00b0203940c0c0380240d81c4a2070a03030000103a0002c201e0752001103071060356008200e91103031418040044401c25002d004065060b4008408640420b0041c0c002c0c00010000c144612014101c010aa10462040e4125075801c991901401c0302015018014800580811780c50746055240080000b4807400380780204070b002d502c403801e180c0305e82e44401903080156140400c05000d02d00b042e1142565135002c120381031354218503000d04000d4251042c000e42c811100d0b01d0fa00c43c4403540303c0c000c1120040f50090b0804060b003100403243e03505910203028441cac10020210256490301c55600903c6442c00d212034849415614002c0240046282280801c060301d800032080544d00010078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 427087167 1250 427085917 427085927
    0x4060824040c090519080307021c0c060e0906040509060c0c012301210507050108070210050c031905400c0918030c030e040b0d0b0a06060203070c0510 66
    0x20040c0d41c101c2d080540c0200803a8000b080e0310101d030304c15a864180c003c500c03074900c5000515802138180e84e030030030003951300540307442000c41010020343c0052109258055440300b08550407a0712101c049603190310701c00f02e2031410100c240d52206042e02c0c144440e10745040c045440c1c0c05d0041c4100c4400c01e000c205c00c14403240035481410a00182ca150804950240488191940c404d20583d0f05039240e81203005420081c15031915516540040202030703850038680155801c41006200c1402c601c030b1003c0100184c4541d018403405a9107502940e0340c4ca080c1010b0441c4111401c441011807a4149010300180001c4107034044803540341034908045c5180001c6642c951010f01c1e55905600c418618121028020050f007000222500340c0e000f0441c1e01c80a00d5a44035032140998058040380c0081c1d91800868040c1405e1b0121138401400064022130203400214100701c16141a50a101e200c01003180e115110f1040c01c000d440c80780002c5042c1001503613040c1d964070301c030f0041e075000390380210949000358050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 427088417 1250 427087167 427087231
    0x11e0801141005030f0307111c03030603021017010312140a12230403140c030706020d0c11120c010b15070605070503060d1115160c0803040608 63
    0x4600034403412420080440c52110305807400c0c0700c54070000000045034500083c0b20800d0300003a40144d810316250341c0f28003094500c00035490b6040320240c5d00c52084180c00303c9040203000d2298800044603030450040c0540d41c8074aa0240061040c2903040758a901d100701107050442e42c1c84008000301d0042600201c681e4054a0314109030858085403140606420603010018034046800821220071001100d02001d010b00328514034040d80d80c0c000c20003091050380700c0c0310081c0005c01c3d103502e0140c000700418616802404241c1e40c1076404504480f07100b18601945181180324902203400c100c00750704141d240c0d0101030900c16924000920720f9013091085d0403103400140c0c02840b004c502c01c0c25640e4480641e110034004c885591901c00044d98482c0030f07605032409003001400d180c54401c1c0d2075503000383c102c0144810755489150558807408000310440245901941d00e0006000448036180c0a16120990b402442c001e40040c4024008680d02002d515800f04c11580040f02450021520f007030408a6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 427089667 1250 427088417 427088429
    0x903010b0303040f0608100e1f0302030609010207030306050906030619060e07090305100501060f050d0609180b070503010302060306090a1e0c14040323030d060f2c011e 74
    0x116000039405850041c00c0205c41403500e507000e80307664039811904040c140d402540c0d80c181106001c100704c0c2e40702c0c000e0800c650001c05502540c80381c5a8000a15085045580c081305a400040f4901095498054400100402d6507100b0780790404400180c0c0b100c1c0010405040c01035000506000c0b032000d40c1240c40101403200784440c0381e0404540091450f0303c070780070070f40780381c4141081c00184031454810241281c00d281e4407401d4540e070400f01124140d21103940f48540303a848400204246a040c070406080403e003c4452555441e14600494074000c02030021b02400000d0004001684455003240c0c0d0090301292080c2c0a9a40d5094890080030b0180076002074030380c1c035410b00407244d072680c0c090003a40c001034440c000c01c0414403d46040910560000501819003204003801c0308485030708800c1c609900005403802c1c06010120703002150114dd100808080136104100500749440c44c0c003615102d0300d610340601e00081c80440545074079041c443d9150fa040a50740700c91403a44408845005014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 427090917 1250 427089667 427089673
    0x1d0708130c03120318020a05060c0307080f0403110117060d02310b0a0b070b0408160f02130c0e090603011b05040302030606032a0a0b0406081905100b0903010b03 71
    0x1440b402d1140c071683d105060340003c80d103802c4034201c0c6920220160702d030866005203441041403d01044c00b1180d00300860343d0407148422300c4440c0004d11940081c02031381140080307a0352600d181d428510134403a000e0010905004104111200c10080039130310a6000b94184d42c1300c01c0c5040360707101056024040700340002544c2440a0026886880060714040a0f00150341c10b0000190160030050690110b10a048002c1c00030007400000503c805011613010380aa50501c2c00d082901c0e0b01c240000d9403010048a8018941383c90344110b14008004141e102d0f00321000b00b00c642e09626015020004180341c1c0f9100d00704001c00a08a61b03005d4201d01d64002070842400008100d454000d4020b41141c00300b00c0c400d000e05c5000551500f0002010b00c0450b6400c5e4081c0100d030922210003c96030410180190001030159001c503403041107600a00091505681e480c2c01460200300780541c211150284085003401c001c284034418070099428400c0e00c2402442554401c104400280104204070480d034040c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 427092167 1250 427090917 427090919
    0x809040c02060406112506020d140108010507020712030302090406050a1220010f0f09030c1203020d0206190b0a0323070611031b030d1b091d0708130c 66
    0x540d01107260760142c4d200d44018025030413841c283c808030340a0060035000c420399000c0880c403482c460240f1001c1d5140101001440c00b110b904500090320034011640b002d210003480100500e00c424440e480d0305c80d0a61015180d070038140142002c0425144c030000e4205600403800c084155107980c0b0950040c000101500e00300d03a915805100341c5040c4103016103a40401ba500340b0f03e0980d0840c0080c04100050b03407000041080030340c0645580105041940411906101c0400000c0108544401030840b42c80780107074071005032400074a015006440182150414018483c84c25003043c51525075294000d404200300c104600800c8980000703a00c041c0001080340c1001080071207224a100000781424144c642e81900d0316819521009051022402540100100701c6440e00c00400c0c020083c01e0341044d00e203014100300c0008243d8030484588210030181d10f504994644c2c101a2900043c82c4450055841fa0303104044d400448000400d40414880c50b4400101d180c0d00740340400091680c01150a1009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 427093417 1250 427092167 427092191
    0x818010e060907140415030308090715020606090a0c0e010f121b0201060b03040f0f0c080f0115060207060221160b09010b010305010e04060b0f04021206090c0421080904 74
    0x112034520032503111343d071100d0404071182060b00859620080035108408007a1941da4103d4150f0001400c1c100c5900070518046100e80304601c0521459100740e00a01d06d40c10141c003005244900500200c00543c0ba002c10494001d03000302c07100805103401d003440208880c40e10415039000d0740d0070798001181443c01001041c40c0a001411070b0321100664002c010342c41d125840041c80780302c01e507405030a0b5182d520611000a40440b8480d000c0d501c91017410558030391b90380d07456140500100c10614265111050645040e0300c10040302c0040285100501c0b4080c500100a901d074500d410036410807561140c60380c452000d003e07041725141240440c1c24a01c44400b801c0509040105481c044015400c103001204107600c40d0152a058a50019600650b900d543c0d44140003000d0020705c880d003080b11100080015078452019010110b01ca00146d82180703030010400014040042c201d60001da01880300f4010000d01c0c00ba03000e1492507055081c83c1030282410400298010b40d034007140c0c00303810710f404a440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 427094667 1250 427093417 427093423
    0x6060e1315031a0106090f0b09040f05071706030105071d0a0b0a0908010506030a030509010503070c060608010e06090a080405120a0c180c1d1003110a020d08160818010e0609 76
    0x100d520700003043c00007a40ca80c03804880216140c4580b81c6e00c000d010350280700710903594004040d0102c1c000c000040700020080418103950007244e01101190700517081410091924454940c0000114002c00c403601d00540044c256080c007822010081c0560340c0d401395981c40e030b40311090251210080c1246c0360080b1070001041c8002600414040f5420710000c600641400503a2132140707640350f10744904014020004444903003004141d1020024804982c0380440c01c148101c401a241c5040040b03050411104107614144001d0b00c4004c065000d5040040810490f00585023652411224200c004048035003452401100d14006001d5a090f03d03400600b400000c4032004001076210f034240b00c0b1082040c81920700821403040001c05000840c6500e00032720302007030040c800d505181000101d5070528805020f007a0800542100940c2c02006650070309500403900590189100e0440f0034040c100b29401050b81d44050b003000400402c00c00c0e42108504290060700d8803c4104080714030b07501c0c00408483d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 427095917 1250 427094667 427094693
    0x12010f110a030f1e110702090a1b170402041e110c122a15090105041109100b0c120705070302091b07110409050604050705090702030f03010510020c0d0c050901050406060e131503 78
    0x202c5148856a510080c03401380d62050360524002f07808030200d07070700c640912014080440601c071403072002840c000c100310381c4ca10402c0d080c0e104880200c5c0d2196408500140740941d01003554286403400d12a00440c3c0c40c401c03645980801c10300003403880f1480041d2003030b031a0651200001d400c025411003000800c03001544a03030f00c500d0142c0f945154002c500001e02c00a40b03020380711501503841010050000407045001040701440080c121203008003d1890318006421040c0100c80300d40143c0e00400c25031400c0303150b5640002603520501c01581a030040b00c0c3c1581718400b802018200c0c503402c011803c0c0c3c1e6030b03030020002c1a08034007607501c0e502e06880d29540300c98003806000c1c810701c242d001103030056200205a805128040103100c1c5580d0078141042000141415800c0442c4200b040c94000340e210801810030961040355201d804505010411241c1ea00503000300d4016440c18504002542c0e0241590000d16819118001140a040c40e80006442981c1c240f88143c0c25101c4004100020a5044d00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 427097167 1250 427095917 427095941
    0x180c0315040c050304030305060a120b0405010c09060210050403050403140c03070e06100804051606170c09010c0602090a05093309010512010f110a030f1e110702090a 73
    0xe41140080d4041004895030410b1a80000f403040c0001070020b0b019510064100e61300420990b03080c0c0d50748103c004034180e0542e048804800c89401d101c01c1010074000c1800310f02c264140551640d00b4007000030760340d24001d0301a030659510341e8041410326015004480107103400801030700c1c4150900001d56510a1034003141ca000c1c2c4542c0300001000e09001d40114003400d4000c00100b1a041c509a0884860101800a03641c6001b054a8000a0144a005030000b000c09803a0841c400e107940c00c4000302c080c00209226180381c010804204940e90002c0340100303c641c800001a110400e0001190ba1414150400c80d000901c5d101444151510000306034081800c1c13842207d0184000482020b180c0405035000e03420551400041c0b05501d40010040d801c11449000011400c14005517501500ca824103188590400050b142100d940d160080c2043e0035030f20b10b8140003900c0351481c070f41c00c003170160006031810569a01c0b90300c21800c5d5034011140c1454005001d0403103401c00c40204002000280211 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 427098417 1250 427097167 427097191
    0x102130311090606090d080d0906200412150e0d02010f0b0a03020a06110f150601140a020d030203060303120c1b060c0d0504080403020d111002150402040b180c03 71
    0x500039858441030b82441618050049420300001e0424843c516140303820440d02000184540079404000d48606544907002d0f010204880044650341d04407401c828120044240c020017060107242ca440c240f0448040d402000180b0f03207813664050380010680c901400e000c1e405501414024542d05400400001300791903410060788285808002014401c0d102c001d4018801d103d080007985d0027040e08010720b07013402050712003050305000c1e0700741041280140840070301108018880b9550b03010b11105951a09003004925000c00c01002a6440c1c0680c40d201041540020000303940c1d80341070081d5010f00303104c0d1070500b1050606680c40740741c81d00202d03000301c5042c005000d090080345001074154040d0080d6903c061400b81000362840141400038425102103d040000100503180c103408589800d004811407000d810130300041101c49401024801c046505c10010641104080051180c00650403180000c8a0401001181090110040f480c01c0040088200659900e140340218801c0c240801e1b9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 427099667 1250 427098417 427098443
    0x304140f0604140d14030915010816060503060d0f03050c0f0f06060307120303110403170a11061e06030a0b0702340308130503030a030902010e040b1507030e0301021303 74
    0x810b03075644018400c0200146009205e074100c1c0011034019a0401400d0064031005206286180801c01007a8406203099202000c4410b417000301c418100090285440c0103803460602c2000240710754540c0340050301c0710250013250401c25008208481e100410032081d00d1803071901c0d5112903254021201141403600071500000c1403440c010411005803582e214101030819100c2c0c5046001b060501a82090500c003008040f01007206900c0209841641c0e0700400d541c0d0094540061a00602e0402405150701070018001d00c44e01c510915002c1d0300903c0d1902c0815a00d220000c0d142c00b002410250207003005100b8413001a60101f0000e580c1d20010b401941003501d42e006407064500000780c0c00190070203116052001401220041c2400450b940700d45030201d48510020303095612240020000c02e0f40c40102c04210350300941c0c02c01e1545000c0794100700b00d01c02040460304000c408410b0780c001140010303a03441014000e0b80f40440d4040c01600840d22001300300c0b001501c0c3e025074042502c46440c8219 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 427100917 1250 427099667 427099703
    0x9050114040522180b06010f09030c1203050904050103060504021008091509030714160905060306010312021005070e0a0e06010903021c0503070f060608030a05030c0304140f0604 78
    0x11034080359009400002c28000e6416400b40b0781c0d40458502c0c0405132140f4180e040c840c18040610b00807405200c5261141c05c00c000051b001d45c800710811014401d80c00400c00c0850302d607404607402c94031852041ba42402452408861034459106403641c85460a000407040c40101d0b4462b902c40c501c250b0307044071218040e02098680c41400c44803030382150b00000b403405004bc42e9128454101e444a4100c6c0d0a000042e40c6000d10707071505280511082d0b21005803401c042c0041e0410000500c0302180400441c14030710042034882e0310502000d08002c200952034020248200005680c0c90840c40c0200300500b4080c20050064892180f0340e80302d840d0b40c8101103000c412141f011406000140c42d40c0102500d140d0070b000480380303940030044074004032640400104106100420055100f2100d21802032524a040310407500540c00580c0343d80d10501c107864605400c00300f00d036040445551015101d0b5030340c0c540064400da031034810000c10301654000300c094540c005100f0b4010f5214415407041c03015250303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 427102167 1250 427100917 427100957
    0xc0604030c032a050f0609041a13020c0a080f0408030c0604020306101412250306060e0402060301030803090106051f020708010e0a081c050907090c1701090b041407090501 75
    0x841000315125019500300001c5c13a049055002c10407014004600309085680000d0443e680103819407032900d44418102241d20381041d11082d140c81c079400440c01e1907140506569940c0381d81c0c0d80207015040000b0101444460074044d18002c1203103604480d175030202115015254030007941c08900134482c40340406c00e40f100f100740d03000643e40c070001d0500761124502d0400c0091145086498024042d0030b2492107402213800c03483e40340b22110702608030110f10714980002156650360080001141e51003d001c0140d0b00c40d004c890440b42c0180115813240c90b10f082580c01814240d00c81584442ca500d0f198617180c103540d0b11005032008640030344103466030300d485460aaa148600d14521a00202c01410000c0d10040103803200402c281107011641600101502c03c0343d5050300d10303440a42c4044420040d06200d40a001c86410007454401c2a0f008094241c010498043c0141c5030380d151681056441ca44030340d80842d0909692140818040c105008041c207424024010301d0f0004504130241e104484801d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 427103417 1250 427102167 427102223
    0x50c04050c0306131b0f02070902210c09030102030a0603060e060103020a05010c081201080a120212070227100f050406050904230d03021206030f120a020c0604030c03 73
    0x249041c0d9103541c1d81d000c10041039035508021403002d141c1c0d88284242c0c0c210120402d00e8400d9103500c1d00d021002d851100645445129404200d0440c0100017051803100c480c3d98400c010350540341c200f4469207841103100b800e4011100b555401d1b61010040101170792440c0c00403011207000d00800c00008030780209658907000309000c065084820294104850f52007513070300f015418040d0484600f843c0c04100e0320403000c04207034040c000e00d900040380b00041c801030103180c10310741215000501e0104002c25000c03c050064810187c803e00140540c3d80c2c2c440c0d240c801424081640d207044040c185801000a940b4503040d001d82000e4051414000ca0b01d42460f11480007aa9002000c2c1240381d55155103411a001c40140d20301c0e28081c0045007008401d200700402403c0341000d4601503101c080400d400d16174503100518043c030903072099054000d40e01010400d00103192404900d00e07600c402c03824080e890840351001041c2c001d00001000024044e0300281c1ca02075a03c5032210503000a88502003028a40381 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 427104667 1250 427103417 427103431
    0xb060f01021c1b0209040c030605070c030f050a05040b160302071403061803091002010e010516051c021605031b070b0f0a0905120d0806031f110d0c0c050c0405 70
    0x40701d40801010b000d440702d074884015541503020300000075408104641c1741604e00700e400d28000c0c1428410000b01d4040c095101500749040e9280b0301840d02c00820500584035444188640090f449014034407a10484014018070f00c0800c1d669002c4c203400c0989405108020b40c018003e255000c00c602d807100148080e100380050041c4080e4480408080c02c2e03a8031100b04900700d201c100200846912041c030001c0110b1102e80000031243d0180d0086429544000c09003401009200c1c0c2500442c1e410000703840300c0c1c0d04d0f0080940340c0d10500801980081c402c0f00e1045c0014010151603108101000006040d2241080329410900070340d104403641e01c45050003540e2800b00b09000c0002c018070108003800d09003801345000a501c59a4101041021070314000c4140765401044280c40c1d03054000c040c86d900003a00350001c00400882c80404655402107048110002c0c0c0c80c1c00c11a14102030800a07038041030b142c03150800c152600280701030500810b00204503540d0041901c2114180b4152103180e205031703c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 427105917 1250 427104667 427104703
    0x2f03010e0d0815091303030b030d080403030e0c090c130f0807030222050c1911060a0902010e10020102070b0c040506180d060603150627110409090b060f0102 69
    0x80110180c5821100900f90148a41400c1c0c0040450740c4490405000740c00008003600041c1c581d007030050580300c600460340d020381d200103999525254048103407a80140c15260000d108144041d0300c1d81480e4005003001d50009450040c032403401031060007804900030b0201800300740c640ea6480403004090b540716038281c0f81c00442041015003081c4003c0c2d024404098200c01700400e40c88456000c44e042590110b800020100f00e444404c00302d00303000083c1f5951410804000f020a0800a554401c000c1c81c4022450f120301c4100210790055041101d211801044e407440d520003c00000d0003504008019110380c0e00ba6408990550b81b0075007107a080c4d0b031001d0219413030403a507481165083d40704200440e41141404012201141503403090310003541c0300d8100e801d181915402a102614030310b800110003550003c8183c49550141121080384049480d4049400000c94801d500d103409a5402400000e080c0000e40042110214595215032422100e90581c403161000482c1c0e0342110440c030701103080d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 427107167 1250 427105917 427105933
    0x3070215041a1e090703021c0b0711010908041518030b0a020310081f060605040b07020f010509030d0f021507020307030e03010605060a0e090c190507020103092f03010e 74
    0x6402e40069a030255041012801200da005000d540d5980c0c1201d4081d840d402554040c01103241107110206181015900382400e081c23181c40c0c80c3c0072408060854410710070391084150791030b0820b4111f0940c86401c0420141c6072580c4120152660402046100000e01242684032003100b52002d2003007a00e0304242c00322003a92b2103410000081d800641000310a600303405000401a4040181c5400c003088004141800000d080c640e00039503916400020502106101c00d00132a00c10f00c0c25500015011500102c0601e580360069606101e4842819003501400d0290f2440c19040581d220254040d0b6084030318165100034000c0c0d04500554040005810401645011070703c500d03201709540800400001d0308c290345800168899010500410204505007607814103850407052003540544000c100d18a48600340c10380c0001d28118541031014400003044820070341e40309030f03ca500c071107501c140e50f054bc0740781c16040120f05c030180b041d1000b5a680e08090300780781e03420180584503c4504000c0105602 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 427108417 1250 427107167 427107203
    0x706030614040501081b06070f03020c03010f020c030d20070f0b1501120b01111603030801090501030302030702010c08040e04080705060a0c090504110705010903080709060903021806040f0c050307021504 89
    0x80084283c500703071f118406100300d00108980480075105184a0f40091080501810526081d920003060014840c2c0c8103110020300e10102104650103134424240020795203040111540320a984d101c80b410456101140b030104100e424400a4020342c02281c45010564070341e450b2400b03d4074038a00403030010380307501c08202e6940610b40107030030452814146088419a0f040600e49481da00244066103000180d1301081816007081000740900003402041c0281d60550b00c000c0e542c0d100da940024100419180b022007070220321400e1301c002d0600c2003034800090a240c103041c802c86d08020070541e41401200c0103c1c101000500c2800d44408030360b2a0310703c1441c80c203c200001058050382000400d0030402c05032001800070320815214a120351200c58075824481c200812071031300c2c1d40000050050381035051025076a01c1060802c9091039280160103a920000864081c0c01a410b00c4020f20f0300341811042d085e600400594802c1070581e08640000640c25080241703194152400340254250242655074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 427109667 1250 427108417 427108453
    0x60507080c010c030c11160314071211130209010804060f0603021305010815011a090604080a1202061023030115060206010608130312150503070603061404050108 71
    0x1215004035606820000d0880d1038509645440f001d910000e0b54920345440745c01c0c1c0004400b050001100010030301700d4004e10304985141d800c0c0c00302400580e006182c070340910f5802c10144000e080c0b0303400c2e1002c4020341c92a140c050b0400c0c41a55510030761558110307480424141c0b09440a200050f900c1e040c094903107441e40c80050601601402005c1d40f87e21010000d070b11039684200c60620022000100b40d031400c2441818a0010210209031b11465401002901290640f0420580c0e4101100b030f035450b43c0c0d1001408a03c03c035445601c29028484411083c0b0100b180c0c100d41003c0d6a4080c1e5040342d854884941d4196014003681c0c11250324640342c9200310040005480d0714101c094000241400d44598800c1c1d030b81016841540145c2c08000107000c000d078049480c580010f40760600c0c40f00c070012590054031910541001c4580c980d6509030002a01c002d42c00c4c42401400c02400384d40110751100e000402a0482d0b01542440d04414101100141850321460b4100d0307020740054031404104140b1910 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 427110917 1250 427109667 427109677
    0x50c0307110f1203041203090807060c1719062412200705071215050405070504020d1a030a08030112030309020303030f15010e030d0e0a0b13081006050a0605 69
    0x2014462080e0541c1030120400c2094150b0041a00701c645074a011b00d404546042c014030b94004060501c207a000c00907000000751054207500010101e05c0b0306102204680c0e20116040040b00c403071400040c001401e2100b407801000c002c4264052040d10b0b25286030480124220704a4403826540080090000d44030b140c200000d01c0c0c080b240414030103080c8100d603481c0030883e241e0f464101c0b0b00140075020010100301510060605d1024901c85032000d840c0c81360a400248503c1601c17503107642c0000c3c1000010702070038000d041c0044c8119250840007005000800e14265040b161009406601e0003d14000506440d402da03c0302c8610320396801c01c5420728414064100403001d040e15140c003400141d40600107140714018200e41050180f0f480b00c1380c1c25040d100c5003481414860448200350080e100440d00f01d203004800d00740a00e840c11410082200d604075644030819100012803034190428100010b40100d4000307404607060014050041421500d4622419034072110201003040070f00d0045000d82 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 427112167 1250 427110917 427110947
    0x60424060c05120c0f10180803060d02030607020f190c0902091c050309130905060c09010c0b160f2a0804120605040c0f050603040803060607050a03090e0a050c0307 72
    0x110b00030f800034012103407030b00000c08050b003541101210800c0b0400400030035041c50100101404401c0042c20044110540003402400340d0300000b00042c455115404108409640a402c455240c82e00150094071407444101441460090702c2e914007103141b100016044035030300071010340000d41c40c0103c900000d601c865103603504019a81034041882072003690004000c0d000b40b02540c0d549110a0410140710034040603c42101e16040c040d0010520000f00d05510ac14240900c0d0350700d45c2400c0042c0c1d611824100010061054079007003002d04031342c42c1ca000d8003240ca26140c0c2c002165000005462a60780210381c08100c00d040d4050880c03036a82c220790407111038010b590680ca4192a5200591042007020050342e0035510356081c44104007100b403400c0c2c010b00707140aa1028150a2000180007880050000f030001403000c00070070310507915001150440e43e0b004013107411180d02c0b40780141941c18070344103801410240c04002030081d086800f8aa200d14450034410f85559950042a035024411003240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 427113417 1250 427112167 427112173
    0x30e09090106030b090a03022e0504023d0305192304120906050f0711060c0a140606030307020a03020112060f14040b0a0503060106110a0b040605060424060c05 70
    0x1000c25245003805000c1c0c0c185c1da0145c2099130300b50030041e252646400c00c4000700d400c4094030b1030030100182042e002d584c071003400100300d50302c17207000081800c2d15800309407042c1400030785052800c540c0303611410b103d4194440c1c3c110744654081026800c0790022155030b54800000c0400310030465240d800f107800d03d454080b01e801001600903001d20b0440080b0f0301213031500c003041d075105142a04468880c00805041c5003003880c01c07190340503410300d41c041d80200a00d020700150751020142d603500140e0300e441d285101103400600c8141020800c0207000c03402c034000307405000040303086802c000c4111002d064002d01201482c0d89191300440d000140716902e140740e9030381c0d6000454200302502c0e1600003001520021102d404035075003040115540005928482d040d499401c120781c1e01d0100711141120801c0c180388016035035030034040e42410700c2d1401c010104031904081200b084103d91001d401003006032401c110b5003900d030618a500002200e04840760203640c46003080301a00c6507009000340c81c410815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 427114667 1250 427113417 427113419
    0x1b1d13051c0201051803180a0801110304200f0d030516030e0a050a030b010b0a0908011e181a06010c0606260d0c020f0d02033007030e09090106 63
    0x24450619006100a918800d00400004601c03542409000e41202c40da0100c40320b03a00c84280625524402c0710005c043c7c03212104081441960f40412003001420309500920205040707882c08041588111000c580185031050401400d02507045000340fa00000340071205200c4c0c507032080118409001e5022401c0143c00c2101d26903030035004c0329640603107119483d40d00101540c0d00030803001c106160460350058103c404100089a402c405c458111610400025510350f01c07442c007140c180040745c1152400d50700f44901e58001b44840103c043c05080c90f10010440f03501c004000140072000c1d100060120a404105908007071410034010380c001c039050400c0640c40910303640c0c081c240d4800c0d60285948061b082164449002084000c04580950002818494100201c003810003122200c2c041c1c081d000ca080c0c6408141c4a001713503048020b80081c1140c01038114200000c0c1ca031046070300d844080742585220030340400000e10030344140d194583c450b02940e24403801031141021005060340215920380d070f4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 427115917 1250 427114667 427114673
    0xc200d03021e070c03020a081f05070c0c0b0307021002040605030622090807050d0305060d0308040515091b010f0e04020c120406020a0b010e01030803010e1e01121b1d13 74
    0xc018483c903031007105442152803442c010820701200c194840603054020107181850040e12608045a81c0801040080c0540300e6540840b244001008001d00d5014220004690010440c01640c802c94459003110017404540351010241d003d640b280760f020800600c0820500e02c1e04071504580026403041400c01207004005290548140c907000741d41d41c09000071148140300007806888100c10940c28113000f00d00306003000c107041010135031000c2c00f08100d1802240030040280115008011007102400c11414202d0409885007080c182018030070441c0348411505501038207800c1940c84c12a182c84210039019424071001c4d500081e1084118052500043c2e2841030400142019001d180d00414a980c100d04e0000c1036101c0603040221a95003d0004100240d6150704983c15581d02030506030050f202e00100c090b00d0340304920241c0e00c03141880004a224100b000e81000e03480d01440c400d10380d540351205000318000c0d2074051102c3c510f4040039005038003c00702e440e141e04a400301c0c400080c2c1180301c3d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 427117167 1250 427115917 427115977
    0xb250518010e061b0601050909060f091009030e1201060f090e0316030314010801060e01120f2001090605030903030718030501020301030c0512030a0c150608030309010c200d0302 78
    0x160102c020042c8412140e1213103030030400c030f502524007034503050924108803c003142d4811005105000030741508001410200080c00300d0700c12a0744404050007820a0b40c40c010388400c10b00e441c0e0600440f4080080d56040c18140226021211140340c0d14041a003440e1640010301904455a0180d12040199a040380b040040e5440024001c2c0d40c0050100020103003d4090603040e0700c07030041c076030401034180200c1025036a264111801d012609109805601e0700315424018418050035200000b0340f0490f14104451260103522400d82c0c0c0c8100325030701c44400781c6450006440004255100b800002d1f00d19000d41806a04178683e21034041c0c1c0700d0742c3da070b0300c1d142079a10903002203850b00c207030708010803260600c10803200c12840580055810300b8845039000f8280c11910342c1c0a0300d0b1054500d181c0d1105480e590007000508552016690b40e13140c0400d419001e40342d4056810300141c0e920040c50004030390b48d24400e250310098000b03800344003240d003001c0f0081d4001401201940d040c95080c903031203407209 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 427118417 1250 427117167 427117177
    0x30804090b0f0a060806010f0c1202010e120406080c0c07080304180b0f0618041e09110306040b0f040602162108010501051204060906090b250518010e06 67
    0x21010070814019014000825200100c150050309504000d12200350040c544a500035005e01c1e00d010000403c01c4102c3d0030b1074070740c00050030644614803007040b15941900f040740300c030100000b11342211503c1c1001c80e8503882280304010000b18840040742880b0070b07580c02003940c03503400b2040398011501c80b01d10340e046038031a501c80800003183c0c1685e00181c2800d4080c5440180089407400c0114001a022a80910a07181070100041007107010301260390b1664000359000f15010544180400108418001444900420b885031030031008100039900c0d001a026104582c000070ba084591901301036090b81084c082c20842e80160240035004801c0d00c58410380e07030640d000c4c00e011020799a00082a014022100300c400d01008038640051021b0b98002c01110001c0884108100d01c590302c50600c0f10092031643c078000e00082c00d004032001480703000858140281010a0f511250080c068242044c00c4000c82240001c01c0d02481204080388402c0302c0300d0300407035040c10111601d04c4108002041a404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 427119667 1250 427118417 427118429
    0xd051b13030c05030a0b0a2408010c12060f030308040302010204031e0b0709060f140423030d02010e0d2609060a0b1e090702030f0708071118070e0a030804 68
    0x8041001c00501c980c1820002c01454141d02600100d038058070b4454080707a0061403c0705441d140c0c280142548002c0c0c401d90b16180365410700915054031420403034080c000d180c050800080081c0010940070f2000c4c41107030b049845d01000f4420191a5617001d41e800e04000300180e055540c24000000464200c0c0c070740d182d100c02605156040c8004070300e4601d80410700a014102040904030b07090018641280c41c4146d80c40903410461801c1d1030800c0300302954441e035081030780058001d6802c40e035443c03000c1004541d005000c4040c1d56004602020803400c0710048440715850354800364202c0714650040803040340100c1915091041e05408200041c00d049040e2103003111548035800300140c0885070f01c1071070800d03041240c40383c48481d800c1e1480d0300c600c445004504e00c00d10301c4802040310b090080080354890b6103e0400140c8400c42c9040c20841908000c90680d801c03c4803202640c80c5162100c0716143c800c03060310507006642c9414004407020244134200c10780000404c2c1c030200104440ca8064401849 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 427120917 1250 427119667 427119697
    0x6070f050f03041101080a050f04080c03040b0f0d0b0102160603090f021f110c0303190e0a0801090201022e0c1b050601030203010605150708030601090b0a030c03200d051b 75
    0x4241d0000400d4088000c10011f82c1a280c0300c240038003001802c11158216411551142d02d4100756240503046224a92041c0554500024901e020501d080080d0403000c1000700d04103d2196103500580e181d607000d500210003101541418082c4a0090b80a105103034019180c41d10310548540c00300e070f0354482e49480b4005a6140d29282c8076000d60000b0039091410041c806807040d0400640400da42c0c0c000c0140c8188481c070b0009403d05d0300e52050801240110300201071500d05980c9407101070080140580603801402081d0420f04899840303104a602c0c046151ba004100342840030408004001452281c1c0402070810161181218503880c05008540901c001e00380952661040508464040d44014003910007901942407104089007542d446c10780042c24607542c1e03a5800c3c0106c40000403900220160036010545104950741940800d54a404544080140c140e640c41c04103414400000e56009441c1c0401004026000e039401494100da5602d2126003550144d00c036660443e0070080c078000000b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 427122167 1250 427120917 427120943
    0xe0f060a0e1920070c150c110609040903360303030b030708060127060305030304021306080d03090b060118150903060f020304050d03021809040f0203010c11011a0306070f050f0304 79
    0x4a05c01000f540100160424154480121100a09803191482020300385115081216600740c03180000c80b2240b050051040000c41d01915000d803540290b03028a4031a07003c00d050020324400010a0603101011000003042c0185c61035800310083d0a0440c41c1c6030f050f0181640004140343e080010f54040d009900c0070245456415442c06404c10300c0004d0500741d6810204100085070000c411a034110340c058808441c80e4071418503003000751816501c110304034410b01303407010142d50b459800780c0102c5101da100070202e0b8035640011140c1401003403003454400024030b4104000300040300c94001034215401c000d40002c1d500e845081c1142c00025041e448a5000420001042410302005400070050b0a085040c40c01800e4510440600481c00c18024030074080403c0034801034403000501c447d4001c3c000c2c400c07071b07401c02402000105e002032220b6296007402030b50b20b00b0071381182d9605084980078008102c581d03074444d0100c1e00d40340c0c480b04190910100700100000c40b41500c0055120301e0048404034404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 427123417 1250 427122167 427122173
    0xa050c06180c040b1305040813091406100801050405150405040c1e270209060c0109021f05120c090d060605030c040e0a0204110d060e0f060a0e192007 66
    0x8541c030001c501d0b102c0c51400036004c0303181c3c1c0d800c0b801d8460b40300c0c01440014582e90302e240c031414500c0b5004412004c10208031000401150540280f412071601c0710003000740352144d800340b0000302000340d4080c0200343c17810010b1219003016444564450203024030040f02c80131000110301140e0040d24240e80340746410006008075044441e110541d400c2d100c400c0401649050b906545003032400ca18600000c1e0b401104023143d19482d010f44016000c0181551f80c2c0700c8010007480e00800c90008100d0040044c0c036440c05100580d0451181e11306040d890303107031134412004440d240e5414002d00c1103000c0c0303505000901e40c584500d40d045a56a100d04030018102e400e1000b0103152a906a914600c06d50070b15202e001c02180110380c003010325506071400304000140c1b022004c2c00c0e0003a1055408140d18004001401249903c41c060088114511541150f02d90340c0c240440c0d0003071b502034a0b2510301c4c02000325921950b48041e240c0320891806001810101c1d0281070007051054203180040b841001c1407080c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 427124667 1250 427123417 427123423
    0xc170c030601080303071b030311220501050c03160507030803131403040b090d03030f180311062a0c01020409020c1e1b0d140703030807230a050c0618 66
    0x94007842c3e00450551030a130074020300d0307998030510524100b0210102482003500a401c02461800950b1010783c54045070814000281d2580d8411201c014140a00281c41d500420440c0c000442c81c0c0007a501c1e004080c100c40061403600c640032a0544035458000001c14004d502031400341d041c030281c003441c20100c1d0800a100d08840c481c0d0f01103d030000c1004001031a480700c12100003280907140c008112400d400d00758000c040c08001c40104074100000e54500821110002c10007030301c40d459039001c1006a0705200d0f61840116080301c040c00700900c0d4558103860070407a134080c44500d03600315482c124060f6105801c0e600300d5440006540e40100781801c1480082c40010502060a00c815041c881413004180d130320b0f103240441c000010320210144209480359085a00c042c1d400c9000291030003120140260b0b01d009622050f00010b0410010075038480c030078103172080040e100595810103d10310190240c600d5000c0031448040c84000c0040c5a88044203004461040d006855103491907000c080815003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 427125917 1250 427124667 427124669
    0x71a0907080708030a0f031e0b330927150916110703140d02160f050108180f0f060109090b010b070309080712030e060a08060d0c170c030601 62
    0x14070741d04480c00601400c0c50001c26110300c05030301d181100040610b40416001012241d01152444103485808030561150343c1019040b05019904020b01d801c0500c221080014540d00031419064810440c8490018000c0503245044000300700f0601c0e26408202d94000d00100d5040d070407419226410000144048840c0264822080d248035240d489c00350540c00c0c100042400c040103200d1a002c03005191501046458051076010b010365035005414041d0950303681d00065a1001445510440c2e4601400401f040e42194007202d86100313900e08000041d42c10250091203a00e044071100c1518110040070000182d828140740058030b1114038a180d40c034141041600704010040c2010300030000104007611803030443d1490503125440d03c043e85001c8031804616405a055449142c4001c1100003441c160030200da4401e40354411000184010b025040c019000c0c5a0b011814039800190716051265140c128103101d81840040d65480768101601883d01d407071070310f890f507211a1465405080410002d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 427127167 1250 427125917 427125929
    0x11409010909050c0405040c2112050c070e0411060315090114010909090503090901030309090e2b030f0f06170601080604120c1e02010e09040c0b0f071a0907 69
    0x210101d400d60300c1d15136035005840c1c1c0d49805036035110300140511082031400c4001e04240e00380e68601e99119150804441414841030380e802100706200204a402030040b90b8240c1119005800f40525145205c3d00d450401001914003a00c03c13204034240e60351351030045204a00e5940a00c0f86101d911003480440c01d81600442d00c50140303680007003801da8000d01e011003111444d143c0800c00c030803e803078198110b000c0c4c1c2000e20f80000000b0004401c02d6088840107081c0d5000d000204a0f0140102809035680d2841c0d0704080f50103034081d00d0a000c02207800c450700c0e203403809083c007061a00c404141c00302100c81c040c80680384195a40b80c248005560030075100340f0410103030000e11040d4103040d44c0e2074a41c0e5010b000200095140810103039802e01130000002e482c0d400c0021006245524a91841c101d15408800c038005440c0d810b00345c03043e142043c60240215003042c50001030038180ba18200c0942d0008442e1a107061091200400050303500c4481043c010310f145000e011824404001450684590402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 427128417 1250 427127167 427127171
    0x10b010918020c0c0301020f0703020609030a0c0312020c0a0803010f06030504210c080a0801060f030e150622020706052d0a14151005040b07080705150114090109 71
    0x10840c1d030310020620164800c00803801030742c0305a0985110300c0c114507410007030307019400843c0b0b103c102d0303080f940645003c07800381d000d03640c1c5903450007516602d034030485252001141442e140c0e4800b2a114a010060a5014910041c07400c600c01101e50f160169002d01100c260030300000500c02041450005001082c80b810240181e0800b6035a60981d1403003ca24980ba0a0740810301d142c400d446000c40500304d540040306a59913180404c2c0040116100340030303040200740f14100180345a03120b4410b02c5510884107029141c0315440014640d0300410240006e030380b01205032038030f8100d103590461822000c0c42d49500166074160910700303803007074030700060030244d45840d00d0071009200a85110841168200640e988105985030861030000b44150720481070501d40303800401a220b00030b40c1c252552104116400d411400341c061048550340725078010042c504d0820311007040000c0101c03028080b01e511a5043d22409180700c00030b1104030000740c0c0800342d40842c0c1c41002c610b0b81440c03030071140540500c0e030003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 427129667 1250 427128417 427128419
    0x1060302010212071b08010525020a030e150d29030303040305030403030f090506091002031302010804050328110601030f020f130f0b011d0d12140310030302010b0109 73
    0x2c1d44680c1c2d02c20850462507000101d18040000307045000104040301400d51014a0b25032000b40e0080c0402c4689100d0455103000180588401c5002d5400720f03105a4014a06443e203903030222001400031800320340042d0f860b100c01414030240c00c003400e814802c108000810400000b40a001c05814005004001ca079000c03000038651004030890388e005404d4141156240c5503483e0440040620f401d50022051600b440d900411102240440c0a01c1032902125613100394200c40c20202e100c191101305529115001c80001540a40e030030562080c0070340142e07402c5c2840085400030289450b440d001000f03030303544101d402054000d61030314a108024801040c0a6045685486803043c2ca034801070320030014100c12042c0386c0e6590303420500c14800502d05012100320300745c205026003c05501c0c40d001c1401c0c3e010760109024290310725504054000d1603400035001c1500d800c82c495604e45041002c1000155130440060080d600460003440b04500f021005443c43c10005d086980750701c80c46040241c1008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 427130917 1250 427129667 427129669
    0x80426030f0d0624110f03071a0609060310090f020306040b04021008160302030402030f0d02030306040b0913030e0d12020309041410060e01050903160503011515050a0912050105090c0301060302 85
    0x50328150b050300c0b4281803054501101002d0714224049100e0b00c00ea11002502c10108a89c20131070700301700816190603c00e00d40b0b0380010020020303411038a5030b0b0941d00891209032905401d41100460600404206941c0d13082c94000c00d060890841e01690030300b10442c188011820031a0840c01c0c181114500111607091004946081c118064140000c054002c00070074103650b030500852500c00c0501c42110b14010755400040d44a400444401d031086d0b20381142d019003401c28800c0b1510903050000421180300040e80d0903200b09111902d650f8114181d04070040c001081651014001c08071900199114032440041000703460020f207504e803069000703e051080083d8121514800e40d076081c141900c204032498012a0f040c051041c104d9410322951000007400c40c3c80c150240c0940d04281c00034002051109232803009941a440381c3c3c41c642000360704441080d403085018145489942c81d060310010390780d2a81100088201c4415115655907205003e4001e204206080c011441036001f8440f180c65a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 427132167 1250 427130917 427130969
    0x306091e0a1e051f050321130b0f03010519081e030c070e0402100908331f0f180f0605091e0106030207080426030f0d06 53
    0x504005a070503211045084841c0d0140b80d40a009040e0324400c0000e40303880c15403ca0009100c01c210321551403409408112401c001c00d0749004080301c1070603206140c04d030154060b11035001640b294041c480801021440d4484000104402d450a00b811502ca506110802000d20040340314582074065413141004480700101741c0b1400254072403a21580032100740b05403410b501c1594206002805500030206100e01c0d02082c050085009907910003000d41d46d80300540d207918240c01441407950141010f860380d0307244401c1da80761320a103140710086104a84400885a448196400003a4099414950100c4901e0840784002007070141c915041903480c050074421075118400b061540ea0341c0b10198145160130540064000300000703001800c0518040511714010551108240c0840705450000a60341e4070900035587e0780781c0c220080615081c03130102d582925950648181301c81040404210411441c1031003e80354440b200c4e0300c07a958981d262901c6008981c40c1c1d811089408900410920380000f2030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 427133417 1250 427132167 427132171
    0xa150b0613090c0c020405161107061403090c060d060306051302090a0209030a051b0a09050601200a050114010f290903070e0703061502010506010f08100308040b0306091e 75
    0x268800201d2501900e0f045412140102c8040d4006081c80c081c0001c80766540c04001408409544400341044240211501c8640d0341c80b07410300103008210103600d0700600c5c00c005d50b04249084120b50030000d40001060664108480c0d80184582e40c9008000344100c40c01a598080d401c1c0a10341c0d400c01c1030382d0000e000d900340503200c541902e40c003180034089902d007008a070a0058102d821514400d04000080030a60380032071202c1e0003050f0b8500300084902541c000c8600400c0c0585800b000c540d400c038034515942404101000d410302c1000442d0021071428400e11000070300e6010310010541c180141d20000f040c0300d601c09145468101807420200a99201070680a19541c482c140c0c0c51610b400000d140903180d4000c800822240018000c141c0d40540c400c404a842140c0ca0124072404140103130308a40c03045481134085034800c444c41502d40d116908866103d500240d007011415141d441d03138107580d0001c0d082440c5410b4000248200c03450204185580b20081c1c081c104681115500030b2030710b00c400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 427134667 1250 427133417 427133429
    0x5010e01051e180901080304141f0503040204060312030e0118030806060304050705210105162f12090307050a060c08030703020f03150f06091e040605030a150b0613 72
    0x7002c15a903842c1460148030f86088100140403010b9075865009142c1c4980c031600c1103000c0151002c1e0501d00c5403c080708844062481c0c00305101d03e041c2d00190541e1039520007842203034460b941e0384002c400101c0b02904406446055940061008500d04da51401c42d912a00041e660120070240c0c4000203901102e41c950154013591644e460751250318100d868610140c200310384c000c0000108840e140c09801139500b41c40542d800031b10454440208034441926903207050000039500040420010700e0a40c45444032065845100032449617113034203581030519220150041e1400019503109070310301001200042d1074210369081c89285030038009071000c0540070009100075408030025619a00035410b4134100700700e00710b403590380b440c2171079980019481940c90b0354890703030240c1c4030500a420103900359030007154060701e0302ca03070007560403041480123817017420081d4015201c9001040c41e80301409500041d074418102c10b41d2101003030b60010282c4402c6041c1d2402607405204001c0611050003c41c5d0072110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 427135917 1250 427134667 427134727
    0x1d06090d120b040912031505130504032717070503030313110a030b091506100c0501060812070309061d0d0204022208010e0303090c010f050d05070905010e0105 70
    0x114190800c8042d00b002009030f98464900403222090050140054030054a140d8040110f1000c0038101900e0722000d005441c0c0220b00c64800c100000c3c1c05a0140e44c016000b414a48940c00e51b5044d401503408030101d80070f00e007000208080240f20a100380925480707918a018211103800c3c01c02080c2d80e07010062130680c5c51007991194500f07100c0036003200c001610b805004514016201d0402d515803602c19a1ba2105c0e80c800d04500520030a400b00b00c081c05184000c206011080111600300e0380c442e425802503601e9580c9001c001480c840421a506500c0b031081006600d0314041d0502500c0c0440380e070b03c003109114900f9003c0c0303185104c4070300301d0102e590202e5074404203164900100e0028059072610f030060981c62203450349070b07842c028294005c844650000b444036030f240882003a101c0c0020303219407205a0103200b540b03040b50300968100e00350700c00515181d420042a80c15107006d6842c00c0d6101008150700e10801d2141d543e01810180d815002030074410320b410900190401e40c40c4000441d104c0880c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 427137167 1250 427135917 427135937
    0x3011202061b1203040c0e041a091615020c01020d0801030609060b120c091003170903010e19020306071419050408010e1501090513080703020c040e011d06090d 70
    0xd0b100442c0c8044030700320441110100c849032062060300713a005440507100c0340800070000500b10840e440040c4643d5021054064209409000c0641d0100283c04504907000e00507050130043c05140c0c41c0da00030010542140320b8600b45450190800d00c07114044e40c1150840c1d80d030602c50030380105250741100d40c13044d07000498048a0901c980140359154841da8040b4040d0551700e03045900007100081558110703801043c82d04e80f01400c0c80c1c801c03954031005250000080f41b800e80040c000c0090040c1d480c01400100c0c0c00d0302e2020392039041146014010310b1814541c16180c00390300701003003003030b92103003660400c12502101590b00d11414042c1c0c08401001441110703041c501d483c810400c4e6002040861300a200c29900940c1c0c0c1e03520340710080004031400d45000d0002454540ba800b400340190070090020140b038019459804441d4040681a400d500c03440707070081603548880c402c03188e90800c010300014012144011400c81480d60040820480c0c4c00704007440660180810429060306540c02c1101101c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 427138417 1250 427137167 427137187
    0xa081b2802010221070801090b03190f120507060c02010203072a120207080f0a1106160c150305060906060a0e01090e0c1201120c06050306120618010e030301120206 72
    0x180c480c4c070f240c2d80c08646519980801304840101454016040c0361a18045a82ca81c1c0e00c1c0310440344c4840e80d40c0d0745030788403040480c06500c2026140d41028040d8040c1c00c1594402d443c1c2c4d500c80c0c0348418403440005d9002401e401807204510500c00c444140b07200951850420010040082020714803440c0000e400300518150000c281015003105a408005a11310510000010f51641e0a81c4104180707230042c80c40c035440401d07010842c208005e50081410361202c007000140700550f00000304200c1481100e02c0e5800100703140400c00002030500c20074907640d0380c82c2c401d001001da8002030186030060b00030381d06000b11941d84005031a03c40110b860718080002c414401200c10305030315413108400081e01000d0001c0407480c07000424001e6002009104070742d0707a4406070703102c00310010400342014030700c00824003810707100300e00450704100000c3c4996101c0140c29a240d09000c0140d940f840c0c800001200940204800c5c01345012102070741001c0d6045600d41b503041e00342402840402441030000090114070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 427139667 1250 427138417 427138421
    0x180b0c03070b061306080303090115032120010c0f03051014060912030304120903030906080c09041d0601050a14040b120a060504021309110409050f030a081b280201 72
    0x400000c0c03120074172000340d4500c0c00b682c8a50098a0382c6c0203950900d481c4180d002d402c20b41d0101165800448040c2c46551101368803400141c10420004200882c03031440d00d007101c1040702c0b0880f00380040001400158003034003e4198007100340c0ca0014142001e00b003052010310210407000b00d07002000d0b443c02c800108030002d00c56114015412b9441806101111300071980000a54840c602c43e440040410b0b09900c000d84400d5080d2200800090300d07407005101e440c0c4a2030102e50032183d4501200d06001d8004001019128401c5542c01141c0255150300c0c4c1728030040107140d00404058940c28106410140900d0010954020b154016912600c13003a0040c3c170f40c1c00040042e850321400b91000290b10f882c0c100041d01090342c083e440b4100700c0940c447c4041d030600ca031b040d003140d00c10718600464070040c0a22010b480300001c281e030180a080c0e0001501902480140b890841658450000d451b145903510b2580825005e034080d00031082c415a0403001c02a01021481c080640040c071910341100c8040340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 427140917 1250 427139667 427139689
    0xc020103110708030103021201050402061902011b12050c0a0f030509070905010e040605070203190e0a1502010b032a01051c02160201080901050601020c0d0312020406180b0c03070b06 80
    0x154541d400940c82083c06801c0c8007a6050364802c5420690901f10070511034240e42054030040d50040301005029000072a50140c8035034500710b800081100100007440d4400c030007040c4103107004964407600c5400882c1f11441150340c460091140a030030580d0880000f8140e0714450990014940d0751170104004d20000c001450003003446001c103005039a1103000d12150351806481c100d400c03501b0400850900b81c00070094840440c040590600014107500003240d002c2a0380f806950400401034003c01c415212913200016003a0382d40020402c1030300c003400d041c07034001000003209a03188a0a940c00c0c134000c501034203280542c02440c2c07050b00c0b02c1c0d407450009890140e5101a0301d003144002106401e4072445c9c0c06108050b4000d80b601049580c441d00c103035081c0d0384103d50f0140160081c000340402440d05000b6082994082e15150480d8102600c0d0242245d0103608041c0200340010300d4800d42031201d91100f009171010310034250500c03e01d144102c2d900d0090b19001400e40d0100b100045560f225020710341 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 427142167 1250 427140917 427140941
    0xf070501020906040f06020708030a052b0c02010b0f06090a2d030c0501030b06090306010b0d140f0f0c130e0417070308010513020c030405040b0307051806030601061e0c020103 77
    0x3e41e1140e56031148a110005c0b0700c100409401600e9001400580220654002040036181c162401d0107850410054204000c48100301c2e00d51741448840503403a0f8402c0004a09040d0000611940e00c081048028000302c1006403282c1d208110b10120f540b945003505003200d0354044050881c58030a9064461080762620078101303642c034000d001050089034969201111030a0320104002c1100742c042c011180b046e96002d542545c045030040081c81d40110041441c0012542c0000704400681d010000740c402c16210310312041e4088007408005201b90800540003600c0e8a4007519044141c4001d10a0105910522102101c104000740a0003d079290814040070b61703035202c5a4130042840c1c0500056000e005250280800044025a00c4158401c40d103002c60b2060040d400c003490402004042c02c19000307a20b8040c0a9140000340b00e03200d040c03095007a0060203021129030b1602c0d4003410314220050f840201082071200014038016507640001c81902c0003843c0090f080c60003800181c0141049075220 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 427143417 1250 427142167 427142179
    0x1090c1d0a0503150f07030605100f091a1c090506070c1b0b13060302160209040f0c0b0712090e01171606020a020406090615081b0d0b040509070b0f0705010209 70
    0x700211914114030f1040c1171802d01c1c0f80301d41c0c9030800700300d080380c040b801004e80060040402d5098540038050660052025141c10340c02c0c01c1c0c40d4418028503c82400c00b8100e0304502003000c08090851100d5003646001001003080100c00984640d603650700050414410f01c0030703588414047c042c1410340081c42c4682c800e40e030245155038008107071540d8803401520b03c0300f25582710003196280c8603000f21040c5141d101040e440001c165000c01074840000b070412038000e40c21128103000140d100f00c00b070004100c4040455181e5256081c09000890760010b680704201010005011001c50070340254103540319503284003d61198840e960785880c1004044040d042c4423054005220b80d40080c407201110302c2503d051011580e01c0000c0d0090321214029202c0000e07210304046407441c42003d80750340c480c040c01080c895400040c0051180c69011004d20300c00741e0b4552010310894101401032a4100d40c48400400b240c07840e0411200d005c1c010f444401e034620100140b0381c001e101d4250140d41013a01e00501d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 427144667 1250 427143417 427143433
    0xd06080d0806120a0203071815031a10050607030c02060702211504050601060525060c03180f060b131509061509062010050f01090c1d0a0503 62
    0x2074520841202d5aa1045180000d0303000072210214189818550180c0200400c0342001500e1040c0482c0d000444412070b9a0440003075400c400742c11080c02107020312007031121304904003201c821243c001407030720003010542c01040143c0e8a0b200201c6070080d03054034101400700203a02c0003442c68421210081d43c00490412450926a41c40c8140042410b400049038030140505001c040300b00300413200a4455000407004210300c9000b0001030201482000b400010510721210a8080c410781c0f5400b5209140e6480c0201c03180c40c0c0600c598103000303140b80701410003500306540302c0d0110580c148000380700b1382d210700711a420740d00c03000c1301480306400f41801400090007882111280081a04c0360350741541c01d06c0740004400303001c44103030088000383d85c0e150802507051540507561109410781181d010100d02112100c4180c05014040c9003c000e6000400c103030a041c0d04403050403070b041e081800c4d854a001c80580c0d41e2508004070314640705440c8029214002030b05e0014049171442d03848650940500c40f5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 427145917 1250 427144667 427144693
    0x60905070e0117030d0c02120a0201060905060607050d031a180411120706230f1c050606070605100b21070c0b0606220b0d0612030c080d0608 62
    0x1410030603035005849880403030380d81c0c00940c812116202a080040d400820a20030348920f0b50f040030303844260713500444040e0140050740b1001540401e40b07181c0140d560340b4082c03050741014003800760400011035003d0704040854441544505561a4200a269855074543d00035101c088031440da810000300b210814181007001806084c100b10750454604080a4842c481e61504500d40d91070040c000c00201580c0e4105030058918200303040740c021040703103000100746c01e8940040043c10355000008581d0344400701107001079008a0030003541c40c1c48500700303401c2040c6a00c40b501940c484a0b0881320100e8036840e610503242c100101e540000741e98241c0003030034802416114400700648804482080d10780d654462048070034840319013009006040750004100117241003405400c403184103415101c0c440141d100c0e44107005025038407001c280d100200300008945020320445006181d00071005800101941e0002d05040450350010452100403c9a0240c04d900e503128002401d6420100c6105d0300200ca = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 427147167 1250 427145917 427145923
    0x1f020d0f0e070602061e0402090c190323090c0418060906020306150c06040f111f0207060201270f0b0f060a09090218130c0e0403170903070b070309060905 68
    0xc003070f10300948580004a801804000700000c02c0e00c0b011901c009407501d441d420030078500d001038070a140c610300500c891041840901c0c149400100c0d1034800162a03076150040c180d080f80c5001d60581000e2102d0704020010318041058002c503481254001444520071050702d00901e21400c000d003686142c400e028080001e0740e80110702070082101c00385c24030511901034510a115000da103041d80d800440100b00000e45510000c0101d03445180c1046840f8286400f054078003501d65084150007003c4d00003070100d590180030400c00f43c50a48020321219201203422580c042100400b8015000020340348000c2c03000e03404007051110390003030059115003003059007200c001400380c0d54180f00302e075401c400042840075880303250642607001e807605042c000040e00d58150410018034601c080304414281200042543c5141d178040d0134100c502c0281801c0c14103004025520090502d402e02c0c1401c0107112800800200b5181056800031409007155a20803003240a0071602c800200220704041c0d500b42000408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 427148417 1250 427147167 427147169
    0x4060c022410170a060b010e03030705010c03110c0c0d03021f05100b030f040f11040c081008060709171e0d0f03060b1e120403020604050705031f020d0f0e07 69
    0x4100c941600781c898080c04407102088030f48540c240d00c21a03c02000503c0c90300103840d103641c141446100412040b000c60704551040000b00c406035922143c000d16240c03d8840c41042007a20382c001401d10444400c0c1c540d0303440188000a00c0380301008a000101132003003105100c1c045641c02000c41103a8220030ae00003a14043c0c80e6104040407505001c141d1303a0049007582e00c1021250122007058036961a4400d0750240b00794142d40580841648000741d0f00e940c040c0120580450391245064070703000210f008c40c003480f03401920103500314805000c559540901c28070191a44e10b00e80e9a040c04100004500d840c0a0111384a83c50400030101441c040c808a0082c0c51a4410b441e0502c5100020302c0c202c1c221000340c02440500c010510105517003240d4406002010746a003ea02458100c140ca200ba49140080310f0450069110f041000100304051040c0f600070f000540051080303203041031030900145134100c0c0a482041c2d010809940c20170058101c54105c0f818442d040100481d203840c1c0d030380c0b00c81c85 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 427149667 1250 427148417 427148431
    0x11110150e1b0d09060603081306030e060402060a05180a0e010312030b011d0a0b181302040803070f060912021608060108031602010504030c0f05151204060c0224 71
    0x4030300006410140b501080742c00341409802154a002c0181d40c1c0c40c4014115980c068074540c2e5202c0c00440021440b500429004e400425080c1c4218070780706009042e0b540000c001101904107006200042e00e402094944641c040d040141d110030310030302d03009249205010810f074400c40b05140000d07609140d405043c113032802924000300c14030b00030f2416000e64000c201801d00280195800e80c0d0788000f00c0c0d105101c0c84c0e80041014183c4c03070740c0780460910b0380c11003849012041d85a90003d84e85280c800025406109001000d40c1441e250003030b010303100e0281104c003812040d40d0181c00c41c10840c069001c61900b50b8482c0440c51880d0605100950340c4a00503c03150324a0351001d8040f40c000000070700c803030480e20018015890b0204602c658911081e050000300d05200040c0130110008000c011844085e15203104020b4020f4030707241c100042d18150603821103c00b40b00f004a16000075004401552181d0040c10209001d84141000c13031408200740c1e280d8103a071160f02c1c2924444640d03850300c5405204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 427150917 1250 427149667 427149689
    0xe060f0a0e0f040902010207060e01170c090111070305060105010302030406020708030712060f0308030109020d020c0709020a0306060f080402121903020615030607081506070f050c04110405060901111015 89
    0x20b081010b00080759032018011b40541e02000007002614440c0b0103110340c1d4441890080291054600069844042074400c00110b40d0301250340c14680d6400382508914111103002026058030b9503e4564039094103005030380c10140c00000240034000d00d50120b940c040d520041c4641da03440c010f6001001c1402d01011966901e08103180050341c0f440c905501d10549412946041c81c69203081c0040c4001d43c4180ba43c0c444140d000e00600c1000320080c480400100403504002d87c1d900b4009100030120b40c0365812030702c18444840e540b944003981c40449168010b074140c2c1c401204030040704585240c564044880310120030b603d048102090b5010643c07074000c0d82e06403c4603045026240400d9142c4504071402000507800c1070014078401c8243c54100980e2201900c682d18050180c2c80b5010075441d02c00042e9031991010442c40800d041c540b1408113038010507032816042a003003c0c002640e40c4035402e43e07503040258a0650340c8003c0402d1004007030105c00184c0412400001801d010ba03519031700e1084481d108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 427152167 1250 427150917 427150939
    0xb0d0c051213060b09071d0406080a0c0825060507061b03020403050f060105100804110303030a061e0302010e040903030213031b081b040e0a0c14120106080606010e060f0a0e 76
    0x105298003101c1c01241c10741c44203101801090010001034104400c89640989c0310f150005001d0410300100714094000d50a03988a10b091103010f52500b01281c4100c0c600060302e4103064010344440d0340aa05544551801c03950f22499400c0100190104150303030703000c0c901d9568041401e9509a07005000b00ea100d0001d903951502500e500c2a1200400d1180c140c00620302014128040d00c10780250754024480d0402010300ea10050201c0c0c915042110320b90150380d52401c0030301800c803901c1e40058400f6402e4144485860459000074104501140c00317900403902c41c211102014040d1701910103c00d1480142e0829695a050404400294a012032050f811245001c9600600407070414034210385045000a84031403181030000402d65084458254007070700d038443c0000751440c04644002c0002900040d155901802005590a001c68407103069030314002d010022070001140c5584e001809007480c40d4000c580c100403da8078403540d03c3d030044010b80042d076030b0552070704402d07803c41e90761095618400c88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 427153417 1250 427152167 427152169
    0x71d0303040b030a180c0303080a1b0c12030f180308010519181d0703050111071a09031b06090606181b0d0603061b020102040b0d0c051213060b 63
    0xc0c8a14010b0492074941080090709580540c2c0000704100103400c01c1800e40c884540f80c412225036150412400604160705000031460f40c0d01400c82022039641c55058201c0005030702500301125414002e0051341120100c804180c0a0b60010074802c50702c21003800b8440c0400d04140c1c004021a07411008a030030180045030504080f540c8041842901d01c1c1c1400b018240710070221080e00c0010604106030302d80842c45600390003d071231655040000c5000344600c41c1076240071801c0d0350035400e4036104c03010180020004241400c00c40f445e49008040140442c0c0c0707030300c080142507100300d04070581c01030213801003942101800140b142c403580042c0181c17890703a01c0e08401c1001035450103c1c00e80008000c000401d441200301e4600300000d164a10a65150a4840d03111a0035100c50b039001b55005551013808205810340708a80c000084205e2000310714090420b24043c4560040c94000c4079000d90b1440600a024015030490b007101c0340281c0100090f150181d90500f01d801c00e44030445402341440402081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 427154667 1250 427153417 427153423
    0xd0203031e01060c06200a17240103020c250608072c030a060609022a03040608041506092403020a1e0b0406020f0f0f070e06011106071d03 61
    0x503508070303a0340c2490403105a145d40300509408030104240341c0c504611032600c0b19003640100018015500c64072088442c10000021640008004e02e04c440d00c1c0030140006810b14054030b0324284000d00300181c8500080d000c2c0303881c0c05e01c8031544c00042c1000701540703150001240c69032000c6079a00d641c2c0406a0303494000c22a1100c20640380150a41c200035030301011030112813a01003245101a003100d641000d540c49200c01d41e0000c2d8400300386140e00203403a1803546403a01d1030100c40c8540070325030071104401c01e4909581c0d1141d4130400c420004100041010800c001c1c1041100c00c51110040c49551784540b81c0b03000a10034020380318000e10400c1d4003200e07000154056507045a40080c0540d00c0b41d4035007280c000345100b440d55071004980f0010780120b0103202c0800544040c1000e5401007032022841c0e0001c034174108092440d00340030340c0f004005000340d03c0002100c9040c1d42d21050000000d44404c0016109000d0b030300c44000c294011042044070413036101c054a505280c00080c002d0116030a5018551 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 427155917 1250 427154667 427154669
    0x1020705060901271110110709052205030705060f0105040c0c24020d0e0120191b06090605150a0b030109090203070302120312010b03091506120d0203031e01 69
    0x107a048011208000c0722a00e000e4001c20b5400f44030070380c17a41031000c000144400034404411300810b100d82903040d01550208541000b03132000f403030700f04011700341025801d090700340011583c8140001c242a480c05c00c1424000c0d1980143e0240481e400d50511111912003c503003401035500031864103200c145998420782050700c419400850002001000b018850400640c0202d4955030580800c000c01d03911107030740f1076100c1a03445030000207080311892560408584212011115011f000c1c45400880200c44130740000c04001030606042211181c2801204642c83d0f03103000d0500c0385009008428000d0f1508003a12555200081c82070301c0480f4001c0040841c0140079400c0052803c0c001800605184c0d070010000038001821141c60542e072790300046800341c404049807100e0f0004986801c0c8204011665409400005180c9045150030303000d40303603600c4c0b42c1d91144402d06510760204500d80c6504001b2040c043c94002901c841100308c0d10003075074940c0107540c2c000054051090032110200f40d192464 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 427157167 1250 427155917 427155941
    0x50c01031a090a1d061501080c0a03090515160f2f030c2b030612060b01030603021005070b060609090106080c0409020d0506030f070e13050106120501020705060901 72
    0x5680300041c0c01c180030103040018190490241d5400c140001c044510743d01d4040f841c003400050016103000c8588800c1162400300b01c9060111950074000c000790704605030784144019107400541d002146c1006458104040c4481480c0031a02d0140000b190300802031804a01140e25035458282c6940e0302240d15040200c484034558089503900d94000d50140d011910600c140c20845e401d18006100160828000c900e51603840191105408a06018110030035500c0d6001e041c100f1410345030201e500610044020024075403a51041e211f40c40d42c0c040d600040c00341d50080e20956603822440e8000d0450780c400403094070090344001c0000c00c01d107000d10460f4450440602140c2c8181d01c0c01005840c1c02c0009064400c044105000100da4989140702900483c034a088020402d82050030505003004600c42501485401c640d2080c03052542402d40d0b00d400c240742004006284486052484c0100303c83c2d000720492500c608440002c5c00015005031590502a0055403d140c460b10221400c0310503844d00e407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 427158273 1106 427157167 427157201
    0x5010f1407080106080c03060409120509150c0c090702100e060f060409111c02030a0c1e03030e15121015020c1e03010e0316050c0103 59
    0x200d810900e0703801d0000680d41020310040241900401d03544d0701900000105d80e194803254032294005801c0244a505400481d50040155102c4109940f1840c404482421180c03607100848680300b100130002c0011003203550500116140003442c0c81c0540c090101075042031501e40c0036841c80383c080080941003a161260b81452040400351850b40640d01e021808000586d14141e11000b040d01291000c00c1c8500e968461a8071040c000d2009416001c0c65089004021207085980c080d03401084444110002494048184000d240b10143c0000c0b010401e100c3c490800c4141c1c6200c2001001440e843c00041b4810880340c003500fa00c402c0c0301d4a040d00b00c1044640100c003400d02503807804e440070f090780940d1800051225405d440240c814250400c0b01c20140b82e5003548050080f010100c2900c2d210181e5815425121049940a6815004950300d43c0000d62107846007040b11400d032929 = true := by decide +kernel

theorem cover : BRFrame.Cov 426978417 427158273 := by
  have h0 := BRFrame.cov_init 426978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 426978417 ≤ n) (h2 : n < 427158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
