-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2890
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:00.018849+00:00
-- url     : https://prove2.me/submissions/54b4842e-3e17-4374-98f8-152814546b3d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 519604316 ≤ n < 519784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 519605566 1250 519604316 519604321
    0xf060504060e010305010609230717040812240112020c1504030813210908011b030f0608120d0209041811030d0801060f02120409140a020306011b021305 67
    0x200d42c084510304890150008000c500d030b0705c8040805031402441d41590802d042d15111900c14510f04500360044011302d400d0000d00ba1134060300540300004d56003990f0043e0041003442d81124913040403980111400480c4174580000b03201581152155901c59041c0304c0152812003054146034140c40b04001400c040b1344a0314a80e03010148000c1041d80e090303000914071000942d02e801c04004c59094542c2c80ba0004050100c4041140b0440c2a150002010092002800118140240280b034808405071010f140003030342901019003101d00107c1d9090006042400400000e80c000c96000345446901c07007001e50314030322040044000c1c4103811f5403c0e840303031510b80c01d1101440542c0a80d20618420703065441c010308160f04256480d4010700106001070481030040c030180e40f09280d4905128042c5c01211a1803052280c0c0340b0040d0400e4004c1c44506564031429040c19185c24000381e00406040e40c1107195040c20b00008140b05c5200c00704030100038007075607500110b49424035075030103007998000d04111f41d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 519606816 1250 519605566 519605579
    0x9030506010627060309120e0609060a1e030614010c0809010513030b040602180409120f0507020a0305061e131b0b07060b0f0a0b070f020a0b070303150e07050901030f06050406 77
    0x307001c6c0f850192455004c60f0b25141f100e9001c0d4180d2580c41c0c0005040d142410861804c00030303994006080345003040416400401c803041c281102c14259600c0381c8022445509004003170403040850b030300f00c81c10400703480c0200c800706a03103e08030b806429080c40c000d5911200c1890a64803146140d10050180ca00c40003000300384415a030103054684485010040600310100c104001e941d420400070b84058260310499034010300806c14158010f082e4104541010300540001d90001c07403c0c1d1050f0740030b0300302c04100460400e04000e4411000366406440482d410102d03c110444842d038240105042c80d0040415281002e4944a07401481d41c0d941c900e5503070700340b85802000f9040303c45955000c0d66140500c084c80d45850030780070060b40c0c46080c0603807e201c200e80321613182c4d021440c000d81e0810030122004c030300010074000800301c0303d0094170041100f42c001d094080800101d40d0201800150383e40a0100d100e9022044600400302460081202410040113900400003075008582c003c4c80e01c0c1c0009041d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 519608066 1250 519606816 519606821
    0xf180203011b05120402360106030b0f040b01030e1501030618051e03250c0506041a090d0204020703050a090e040c030204050907080313060801121a090a0615090b01090305060106270603 81
    0x20620001f01c0060380e640d8807201601566090189107902501d444282201d9082aa001d001141c10514006c5051106c1044443c2003940c00f80b10200c1003078424006105000d440d005000002e0b2140701c0c41d07081c05089441da5a142c14040c1d190501d43c14188903407120094042040d202c24124031083e03421201d00760f582c164441030039204101c0d2500140301002865103003100555044601c1d0030b0014206150000c000003055018240e0664400c26004900c0013584540c409421414440d0f10782d00d40c1c4208500300941005115845490501f11070780030880001d0001c000007084981c19540410745071030380c0d80f400d4101403058000002c01c2c88042001d4122480f842140030403a60503840d556000d0341c88005894401e12240d00180c80c0c0c0c10b800c0c2d1003200341030404a405034002d140d0070965012a40541d5688151076902c012241d00c40c03529181841203200c2449500d10071102420b240c00e1451465030b515445210501c0380209200c0da54400c4450076000440c0902131180a146c162a00e54649502400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 519609316 1250 519608066 519608149
    0x22a18280c0e0d0309090207050a0803070f09090204081207020f030a1104060b04050a0302011803080406030204091803020d0e010215090303090105090a051903030f180203011b05120402 81
    0x1015419070b42c00600700342c0c00c86100d02e90990b07140c29440d0b08005201d4040c1d80480000c40d900d104070141c0303902080796400618020032150b5201c101c1c07514140070043c000300b110b070030184201c0c0c4100010451004006914000c01d0703a81c1241c1da40320442ca000207505041408042500740c00b40c2d03843c950410140c40115550080d00321000c00c507854403002c620304503000328040e080d0040d0101d18180007540c021079811222050715824a04016100c3d03541c0081500141c0c003410100ea004281417001e50780c3c5010b620000300290070000c00000d681d8a00175030300c840c94190041448181c03803805099900c00d0064120070348030170304070740c1d100d0929034a6240d40c0c0d403040342c0c02e8070319528000c0860355640e004160000b60613040401407588070f03100d41000301110f40310b40d03003181031543c0c0c0e50400c0000800b500a0b2500058810702c040030a80d00c0d801494290ba5008580f0701c41d40c524140c8000300b6a07000016201c62241000f81c0711510755a0303201007064a0118140c00e41400340d00c1107250420b140d03010101d403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 519610566 1250 519609316 519609341
    0x100507110703020f090603012301030309050627190311120105090d03020d0204090603051b01030c1727071509060921080a022a1828 58
    0x59000c80c01110041d2a1081808001e500080c400c002400a181442d003180d000381000b40000749154054144600c80c0c45804041400e01800000400906400440b07120082905445861501d400c001c10f411521b01c0004e195822000b020800700410345524001171040f0b14031001d541c01190700c0f030810b161009500c556491040c50031880405001c030043c007600740100401c20003400800302c408411b0700a50007050000250b1034dc2408000340146050041200031805900a0a4444501c2441422110103c01c10506040c18004211100f61384442d0f00c09440d0f81c1620b105100352620316082000c801e044a5840f80c00504a4511000380b00100d540400c50342c2d240441590f003c0c1881041c0d5100300309109041c0401c00400082260042e80c03160880222040d40340110020b001d03076030f002c1e0b068002200301c10050303119503a803106103819500303405e1a4901003002000c2c0001c101c1e0024194200b01c82c050a904496400410f42a80c408411aa0440540400c0c0301e140d2030789d010040005c2555840e1403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 519611816 1250 519610566 519610577
    0x306050418020f0303090a061202071a0a1b05090f1309110909060405030d0207051e0102041e050310110f040801151509051e0607050303010501020c012a020a08100507 73
    0xf03002500c0c0000464042e2031010780b61f0302c0b8552070200203450080b030844c0c0c00342030b00c1d400308010000500e1403031b81514040c982d80190810342c109034002a003100c8003e52902070030014142c9200f02aa0407a0076288003a83c111818800346420134081028800004180868a800c0c40311120800c50030890b000701a040c15103281a041d17945d000f03402d95400040e2005059130300f04209408014000c0d40040005c0c0b4016412204035000a00c0c000c0000c0401041001c1141d40c041400d02c00d40d2141c01c11044a8240840441d030942d05040000e40c403400075082140d040c40e81c41d80100c1c4000d0807203080c1c0342d0140d40b2000154403159640000350180c864014003000404400c9408100303001081e0243c0114499640c510081c0c0342801c1c10701040d4218804240c0c0e1340210080d255050382d5800c40103181480c802d4002c0c5071254580000a450107054110042c14001c03c480000c0e91a00710f4405642100b281d05845400d0109078008220600d5080c0c00441403070040c5098804084540e4011a0141880d543c07907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 519613066 1250 519611816 519611839
    0x408100b030d050301030b150618010306050406140402180d1415270304090908040e01050303090105031b040f0902071a160309021302121603021216030605041802 71
    0x401d40ca038440c001c1d0560103d0740c24001440481c0050001981c8051540d05075410800c90340005580b941040a6148520903254001c1001c0e583c180500402080d0946051002c00c4c10a50840d000081031106107000e00d9001c24048152001803d2003202480064026143d14245061040c1d040c5504041d81c0c1d500c1c8240d0031400c03074030700b16440700d103204881001a5500400101c26044030203041080c000b600b40c4014000815210f0251007232040d894401d8645d0780c0d071149040100e0344001016403105200b50000e01000e521070340c111040703d5208590704203071050292055900915402180c0100450440300301d804544142c0c1b681c0104411070103101c0e041c401510044248082e0401180c81c903419103200345c0801e407510b010381c01c40d00709144001c00115200f2804800071003280c000e040d415a81e46034003824410103462070034010b4070070005440c017946480741d05a40000c1100740070708852040e520225260b4403d5100342c0c00b84010b03020051040c07010b00100500b241044a00a405a05c00c0303e10704003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 519614316 1250 519613066 519613069
    0x30804090c050301140d030c06181a010b0901261303120915020901051c1506020a083106021c031407080709090f020d0c0c02031e10020408100b 63
    0xf964100c030901002051104041c905001d01400c1c01c02d003c80620103001440340008a190268500c42c403c0340340c1903084182903003412416102c02e6245900d1416190005011026001d42200c031102001c0c00c000426004440f00d0706031360b0318252143c14488451401344000040c0383c0d1410f4020500a688039500344100c401d041c811180d210f035004210708070b02021512180d9460300503154a00c2d05040c15414064860f50304e51581e030300701c000c47d001c480c1e0b181150401c140c441030345440a0070040c80104008902641c0d03202151141003071504001c28407a01806580040d0540340c075803181c15030034050865a40f80d00181d62220801044889088a062a80c0c00c80748a486103441c4025030692100b46501e41160640d40f4007001b4000404000444101181e62066030042440d1031484070001a51402c207004500704031a0a80710f0360040003030711280300c4056075000034820303540c00c0040d032114507820002404c903141603103c0319007498050010400280c000008a40c0c1c000140449005100a001180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 519615566 1250 519614316 519614327
    0xf0a0b01031b080a1524050f030c2809030606050102030703170601020c03120a0806010c05031b0313031a06180c160206040e04060b030c0d0b04110406030804090c 71
    0xa0324011907880344605400428420301000c2c2d0030108019000400448600c01103194548607044005403669045510080c1d500300801080c00c0c01b074600d001800c007000702c030008002d0711000e4407030095002c0100303e152110000403010804104c040351003840c0794045150141458070188025070740207240450000340c0d54004400c54400c1c950503a505002e040b0484010b050b210005840c0c9811442400034076205601c0400c98078010702003060001d911075003a403900801050005102c1030401489144100000700000259408056100b40707603440d1540700c0b07280510b14000c04141c100d40c0b1171341074000810310030415060040b140c051300508516030ba802c4240140183d034101c900c0034040084000600c401284005049601c040c20344805602d96a9000168541c000c0d800c040c040c44a203006000030400188901c054544042e80070f03061400428000400952031240f019240306080e100140802001d5510b69072a91001042040425124200540550440d001d0314202d01c1c42c01c03841008131405003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 519616816 1250 519615566 519615581
    0x6030b0918190515040f0506010b0a0504090b1503010f0609090c050427020a0e03060a0e030a050702041d0124030b010303050a050c0f060a0b0103410f0a0b0103 70
    0x42004020140b40c05000d8a000b0b040305100b40d80d10300500d00780c00b002c10601c4540b40d000343d009400c0c0c91807044050818500b01041070b40320800c41501003112600c0c142c0c000041d44d00f11150040e001603481c2c0d0304030100f00440a0382442c0e0814110020003c10028680300d00d010a40f1502e50f6242d40003615414450212a9101d0725000421030500c001c0007520000803140180c2c2d80d00700d6241d100540381c424850306903009215418041540342050100b1420200080741d4030a8601c1c00c140b0004842d20b08807a102d214017107084040180001b140c078103545407604943c2c58005100d8280042c80ba101c44c60900815030b100310240365482d04010301c0360300c4840a1a030303415a0b81150f0390451326480c540d01030303c0550180c1c0018080c480e084c00380802d2500c050084000c400e407141e0280001e413500380103000c00c0b90125070410b4103051401d43c0c0811040718000c18542c40001c044140070002541c1000030f40c0040d41002e82c1e1543d50a040700308405c841c2d1021411b4010350b440360003030054030381d00070056090f150701 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 519618066 1250 519616816 519616861
    0xb0901050d08090102030412061d060f010605030601020304170106080105071103040b0d1e0b0111011e05100e0a142202040506120f03091f120b0402090a06030b09 71
    0x41407800003041d9150700400036118140101c1e803070f0940c1c03005191328210f52a00d05403903082e643c410003c100b001c1094003e101109801c083d0100d4074045040c1640e03a41b0601540f802c00c032004c030024810b64000c20803a00588408040020110400c0c9400d501030b15660107620303095402c10004c00c60700345c01107640c084c1d0100060702039070401c1c0c200100c003141038000c015102c3c8a55124481c91001407640e44244500f041c0b9510040744901071400054107142c0340400401c400c2c0c2c075140d2800014000c034000c2c808880d4407144049226181c0038903902c011541074002070001c0140c03105015600c00c072580611030022181c01404411351b030340010b4183d21802c4510385804030800721002c0005242540c04607030321100c014407a1661140e000c07a41ca01d080340401000826a100150072607040c542a81d042400b44851540712012100d4040010152007000300d60340d10641c0c44010903403c0f0341e41c603010b6418800024100c102c91640c1c480b80103015000390641d15020b5190003002c100700e1760344650800702c900c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 519619316 1250 519618066 519618079
    0x20304060c0501090f0f020f09090c010c0203030c0304180c030204050603040816080a110f030c071a1c1b03060317090a0b03010603020306330a05090d05030d0b090105 73
    0x390a205880c40415040d00316015541c81100500103101d201d241110207002e0b800c440000304551060040f0f07254071865103841540f100d020081c403080e000a09100080c0286040f5014261500c0030038914002e2500014880c00003090101c1d04202e8032210b0704150365070081c02c0c04604141c541c1074040b8441d134000d2641007601000000c000c522290004c04031380480f160860303041d903000c2d1500e000641001070040002901640d01130351020341003140d900d0040c180c2014614100030405d101c0d680d0182d83c030520960480e036019a170700201e03d078000c0d68003400c1203c140d090b4007405101600c008010442c055a90031810208070540c09100e4410303903040d00d60080032820301d80c880034452222178110001c81a4005100e000c00300e007508120000d907000700500d84015031a810050b04000400c04042e408220601880c40e0700c08402c03c0e1406803641501030b0300310b80e03992034085400c22a8244203400140d1341082282c5501020040300000415080600c1d1314100b002c2d40c1c51200300240c0013020700c034442d800354 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 519620566 1250 519619316 519619319
    0x111902010c031416151d1c021014070906050328020c190201090e280605030a0507060305070e0f060c0a050a06150b07081605012021010303020304 64
    0x3d0007010a40e0701045040303207007030400d05440c4c400c1e040d400060804442c40c0210f541d00d088180424010031420340541b200050881140c03080c4143d42e40c8002200d02407c864840724030a000c0d00a114103841e42c0c00402040c41015000da4000f926000152061b400080d205a40060301501c2101568041d03840311a658481e880707440501b0486070075481c0010507990b82040104e101e68001c0024070751001440000454001c154000034047c1c051030ba00c00150403d54a0070021805a200c5214074103080106d10804d0080318410f00300001d0040b504238a1700752140c1c54000301480b4001809201300d800903030b0b00340510f5403902d1040318058140401c05422078501e038212100303850300710050300000b071428040313031005169a00d4841c640202c00e2816a40180e40740d0802c280002d040d500c1c400a0607864408034a021515075600b04227100c0c28150088500d0461010b0040040a411174103120030303140c044c90130400c102400221564080d4245218048102c4000703011090850703e441d0480c0e816401075401c1a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 519621816 1250 519620566 519620573
    0x3062016021e030f01140105060a050a0810090c030b0f03030c0721060c050403052b080a060b0a0f08101d0a11070606081005010521030903030a111902010c 68
    0x76450070300031003080d03a01c1c03100b21142c030200400c22480c00c0410011070050400c90b02c082c0c83d40c0060f00720314010107042000c040004c1d004401c0340c0c880201741c90071207041d0f900c07040071100030311841d0002e4039200c0c03d110b02c3d8450103902d900210400d0fa0102d0301098690712000c02c26569220b2004102d980f508541400c2120a014150310409a0020444a044120990346d0401120315001060000c030303c1c0803400740300f40312081000c80b80d144d102c5140001107805145500f01641c452800a608108402d00080c1c0242c03d213400c440020114800c4d040e0702d56004075005890141841c204000060559001544104021081404036445441c905d01400c018010100c1200c1c1d0080021029135118032400c1d0440785210000c00001d4010040010003604000c1c039241011855403100104030700b0200180b0050f510880745603503508e40200101d02d4a0100000142540101c0d403a465145c040407481a1407250010300218021a01009460800782084c040c805482000e080103400202843d4450001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 519623066 1250 519621816 519621829
    0xa0503070603090f0b0109140702030301181a030d080117150a020a0207030506091515030607050a02240103051504051b0d0519060b0109080c090601050906040306201602 74
    0x3d513000d07452801c4401e0103500c4285000c5020390001d040d00d603890740300c101c0034a100b40a464210043c0d2002e140742d9407404036008151001c1c824048050780e640e40414003041c5101c0600d84500502405452440b001080003908040d001d2292080320481e0101da41a090404100202100190302c011142c42d00c6d0046200001c3d0441c94588040d4031490a010021440070001a07126114400c010403008003103841070714110b00d018101108403807544410b940c65513000f285456010380c0c0c0d0300c0d140c0d1300d40701c418004903e0218041d01103c09484003004549030412410640c1b4140c81c0500116010300542c1c854842a00d141203a001c0c01c0b84d0800e46000c4030000f2603030380390105014000c003964a54042611028100880c2030030040e40100c00c1568501080011700980c0007541c02400c2410b12a490000b6a944400000040d60310980750000090416030041c41070700c00e0782c07101900c00307a2100d859141441c0204002244420500c501c510b1845a8005180840320b070407070f440c403044070032009607428480c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 519624316 1250 519623066 519623081
    0x305030112060212091b040c021504020a09020c07080f060705040b130902030a05060a06030b1c1e05030c0c0607021c1a15010e03060903030f10051f08060a0503070603 73
    0x502d26000c002100c80000949580ca002d5030500c3c010b4840b80300344070030b1222034429200303489000e0303810004014621034010a5101d4011140152042103a540b4800641315150030340003580c00274408038100080710000546201920300c2a000ca60b0b5034070300d450001f07680e14411181a00024420841070003220708210207403821103034610014420300e0301c0390020320598000316200e08a03595200d0401c437540c0340249120005100c1d504041001c1480c02c40410101040c8140c5803c442c1d4026030108100500d00c5c440918140e1740035911010039050385481e07900d0360300900c0da4410903c40c0020384641841d00d181100c0e10258002d1101c0500d204080c048540700c24141e005030360042d6810130b5a00b0100101c0d498074407903200844004400c5628030000b410940e20292282d01a81c420f50070008003010000c22a038002c401d0312a100d41a070760304402b08441c418150050b540000306081c40984d804503a4160741c0680c03d80351903499259032075805209400c021849510741c9940240010020140203910122 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 519625566 1250 519624316 519624323
    0x10050607030207080102070f02012c06091c0b040b0f0c0a0c020303130b1e070b0c03040f0507030c0e070503060f09100909140c0d050a060510030501051f0906030305030112 75
    0x1241c00b5138400e969801c80e00010381c00e40b0964024000340c0219a407140c0d8a007040010800e0f0500f008814880700940d41d807003d448c8500481c8002004c101d5070b901e4110b24140040d0003032002101da03a0303a140140024034155000c869680e100000325800104140f4810303c14116191101e0a04146d030700121143c0201c09001d9030503001c00c1111038481404104100c001c0d084501c515555164480c83e82c00c066040c0f038031880d03500c98080c04440c000400044c01c4d190080700d11411a034503511a4100f0302c038050181107000381603100f030f54000001c102501110400300c072a010f120390754558401501b61b4503444116485507114103000181082071820000740c5403c100e00b21001c083d0780c1d4880740d854041b5540d010003560f54400e05080ca07443ca120030040500800b03019211200304ca03159542c5c2c2030b80c03290704203401007030f85031180c0c0004c0c1c19920b10ba45040c01950040000d0109050100c008401c0981012180041c484494800301b8001114080d8a00300c0350705607a5617243d0b0f0300e00070700100800384980049 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 519626816 1250 519625566 519625573
    0x1209021909050c072a0e101a120c0f0c030a0c03020105070f0503040308040c2309060103061d070e04020f0909100803074d0d0c030206030601140d0903020f0303100506070302 76
    0x1060909440d0385480c1b01da540b900d182000b041c1423500c103002c800103584901180e08820031680700344400344510160040403040390540c403512901b0041e131980c0a500c0c1600d49030700c004151460203036440040d504600e4040c0c2c000b0131081d200c0d0703035086610ba031926407800c005c100f0800200d00024810705910780e0107405070000c069400c0d150500021200e40d0800ca80c41c0580403159854514909984043c0e0000c2c001d09081007840e16100c1f4000123404100704000c0018460000103504500500d010920450010011035480c90010700396102900300b40520350142d100840000c4050081c01043c1d429554410021b50a081e542d035507800d428115008030070101c00d000301a000c1c054281c5da00c0300c00d5040f42e05503405003050180b0340c0480314035580c0001511a1a0700c0f80c10302d0210740c28a41081c141c0b0b805543c10f65407550f5820041c1c0b0005010882103400c0740380010102100c004981c4482c0f50b2601c2039003940c42403074074902480e5581c0829159400020b0040034200028030b001001000254420f0054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 519628066 1250 519626816 519626819
    0xa0809010c1e090f080706121b050c010f0603060504151a0d0f050a0b07020f010515010c02041d01020c0c0d05071413060b1c0e06071209021909050c072a 67
    0x20509100130a44c0091034a0b48594818044039802c280d45034864043c0d40020000d42081012424800700908005000d20200051401032143c080d0000c0381030200340349013030266580e42e180030300c0240350888003a501812004547c038440c464a0040108074610f0100c1015441501420081d002c1c000d580c0441c0c00c00740700c40b2034000180060160b100341c94018105840107151281010303050a060010391038a030303450181046004511075010407149803013071a024105c0c10b82840410b00410b9000001c020000584001c0c008411054006116034202038042d10200d4502c0c1050250146605100401e2034000460078429509201413484c80414000d08422950b00000450422610b45030003c1303840144c0060302803412180200d02c034080300e500c41c804220401000e15200d40f12803000d00710300c0401415070300001580701c40350410a0116002001151200c064804500c101c50140c400c410b809800c01c0002050f21102e0030aa031485500440582c034904c000603030080c00f00302c02c01d00c00412030055140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 519629316 1250 519628066 519628079
    0x8061207081504060b010c08040614162d030903020405060f060708030106090f0608041113020f04030506220b040f12030c0210020c030d1512080a0809010c1e09 70
    0x10b246040b100c0c0745002c4a0700b418101501aa68000c80c0241404018200f490006106070103c0d0201c41140c41d1050080407051030198052160980e010700f1138245001ea0010b2200350259902a01c0c4ea40c0c40c41088452004080064800801d10107004124441010000742c10590003403580032000078440f444040e10000026003a420100c4141c40c000f1012005111031900080506c0182c914402c41c4078030f41d480c12100070500c50f03000300018010a0041d000061640300c020002101c1d03c0324200a640b205840d54103007060b50064401034500b44039940104040704208202d2402030000e02c085101c15551940716001e03c050041c0c02201c41e03403400d65940c80070030200800400c14031029a008500300c242c0140092510310b1520440300d0b45481005182042c0d000041100e496500411000c24a010581000840d040300c5920076603c0c403101030040300800140303000601400b0159156504140c0b03e075040300c1d08880302251080003240c100d01c281450b02003c0c034412000c4c06468038005401030f49625 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 519630566 1250 519629316 519629323
    0x61404120c0f23090c0706150302060d15051203190c15050103120807050d0e0723011103090303030c16060603081b060906011203140a020607120506010806120708 71
    0xf0f00150144007480c2d94001c09a0300ca0151040301e0400b181c1004590402d005200702c0da01c203200005040341d03640c0c042c40e4407200b14003c14400668000b00a2522580003510520241c9019000804140384e4902c0100d0319180c2580e660307030b20100301c0008504000b030000e800601c2000c1a00c01a0a03c028039801c080000d012240c001c0b00c103207240a01040c154514a04041120283c0d43c0880900076083c04000050354000140d40c1c240042e40e038003080c8154400350180c10004950000029a803a090b12aa141071205021007030b000801e80e9902c11070a6401001c544900480103481e40c1500208007041514084402030904404940d40c50902c1e0121907980c1d80444140303a20031903c8020100e00c07100ca810003542816002d2000902401d0300745400b420765611180305001e040e4641804002c0541418428480b02e4110107192116540d00c420350000a95030b01422a259800504000c852100384100c901404c1e00915041c4c40b4035815850749410441d00b0701358408041d001d40b0070f030400000c0d014003c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 519631816 1250 519630566 519630569
    0x7080f1303110102150c0904090609050a0b0112080a052503080105090606070c0b0c031306020c0a09020a08060909010e0d0e1206071b030302090a060206060109061404120c0f 76
    0x4540021900d10318500400c04400c5401c1d4941135402c03aa40f891601041203016917440340e8000d1802e660b92000a000900614120b00081c2c400740c980156941003241c00108602c1d0710340a03110090381d50b80c3e90050740804900e40000100114018001c1400060240003d095440d00030703d40d00347c1c65a40d81c251301003001d80c1d020b8194001021940100460f00b030440d051904400b0607580b8a140034220303103e48080c8402849180070007100060280003089051050320b500040c54402c0e10055039507544020350b1403c000b01c0c1184240124080090350400a200b1612241d0306911110303166550790301041191500140300d44203e540f1407141d022880e906000f04c0c0c4011806441d51010240d041080c403c00300c0c400c1846817401d47c4048180070301a904440c004e030708070701f500d200003420b0006482c040f400385c0540c08506400c1ba00c0b07402c01150042c0c01150300351050b0000e80e1400c1e180c80c0d8a580c1142c812005511145420808100c00e0240d0700c9540c00c00b40401c1c0c010360200d0725032a40d4607000d00c103c2025 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 519633066 1250 519631816 519631837
    0xb0f1e1207120b0307030206130504140906240111100c030c180303021911060301090204060e040504120c03030e030412020a0e10090b1201060e19110f07080f 69
    0x124082210407a04034004035000d10030ba5004200750792228021a079281c0c0c03d070001901c1141c0209607219a0490728000300054980a03006010002e50a107809141c000e09a8460a40d80103d200086201640c0701c070001414101580450f81312140348010740d10502e40c00c0d001340443c080c2d00c011b100e9032100d501404841400fa036a00003000e11200100400c0d030048807140e501c0040071204108042940021808100c802484420400700410320300740d00c1041d0042e04003a040a400710000618407440d0f4080d0003101c1d420340b02d102c2d44022000c200404c65008070350003002c7e0510181c2c0c0c0360707000d0711840c0c101c08075038070a00740000c3c24210220090710b15007269002500c01000d40081604505240c05c2000050642008070b060500b0601c0143d40412094010910b03041e64038544800e45543d281d44180761050b00d40020040180c482000e00320012003207941141060748295030000b8409244144180301d030b08418250309042d00c8450102c1c40380e00007001580c104000313110040500d5407940040c5000640d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 519634316 1250 519633066 519633097
    0x50705071106120906061002071d0711190b06010c120e0607022d09190903031116060b030c030303180307020907020709110c1c020f01092a0b0f1e 64
    0xf0046c0030080e95642d44010700c0c045400a110170441c10b40a1a070640780c1c215614400e1811380c0da544401c03a500022840381e01460710500700034014001c0401c202d21416070242915180c81e43d680d10041d10021400000113081e01080c0a40c0308400b03125465101001c0340007800709160a044c2e400080d00403280a4034011881070740c01007081e40701500300403004c01c1e91040d1a420003e2408241104000d1034001032003040c1c0c2e80790b810400805120354012900c56805495150303c410100c042042c46039003810086600c01c1c40c018a1340f601e40381c000f50542c0300c500010011840e581c0c1e446080304442500300740001c040e2005212a400503580c100f5600e100c0c00850380180075181c030300f081e13500644008030301a45868004010420023030b40003040d40703021000c0b8044034504112412004a1400e034010b481040554a0030780103604001c4090700300742e02c9801c120804200d50350042c40c000d40346104d0f440391561001040040301c0fa603a0048010b420074521800648408070400404441e203903000400c288903850 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 519635566 1250 519634316 519634321
    0x309040911040b01020c01050304030309150f0c0f03111e0706020f0c0c010c02010801050904051204181b020a0b091f0f051b03070507050106080f0109021003050705071106120906 78
    0x3068480c2090003c000d100602c4e003401460000b074140e00c4080e00c042c1c105030319400d00c44107114140c0c6070b1900000640404010224441c0c91500040c0322000c00b002c0040d00c00411044034621a000e016440703040c150b84603203420107104040604503501010392a01003020b0040c5400300307000f48060401140c0e41400c1550345e840030389446081c490000d9482e818000c489560b1400360760320070001419503030291a008200d441d94100f0380d107421340b00c060003888000005404100074241c0d051a41350072411420900c08c030741e801904100d000d07516a10080040c1c0c04181701354080307000340e4141c035040080300c0c1c140d5a0194515240c030714160321071b0b62203112194070b454a11880072001e00c112688100800c002d02c281e150007200c10600d910015082a0800c14007050100c14800700703600100c02041880c00300c50305400c600b10030a010300410001a031040f031000086400b0179020303006040c0b00d5925941e80754900803407551080290b99481c10140d03084001417001c51000c1d0801c00700710b805100c190001306400d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 519636816 1250 519635566 519635569
    0xc18040603082208070605070f02102a170702132c061003140106080a050c0312031303030c050702180105030f0c060313050a0f0605010303080a2c0309040911 69
    0x1441e0a4104074103c0e01c40c85041044580128060003540c01c1c1d450815030b1281e0328241030046144c071407406540100c4212541c00b820341c04c80c14003009104844500d0800c0202400043e40c4100d107500041c003080001d00700d012821024500170201b040c8020110032100c2403103003125045951124000303035242d13450780001400c2c040e50043c2d0f0810841c002c0003400d443c98941070045840e08148002030816240c185131641c0e100c2c0c00e401500180568004032070210000b424000e541c4c1c04c400d4110360207030182100d60310031041044101e911a0714240050200e01215640071401028520026010003005024000050ba20180c05a03000c8580c0a000080307941400c0815080101740e040d4400e20b5400454603003900c4d00e0705000d603584442c09401d100c0440317007541480c2d4248222250000d0481e10099004000c10026500c01c40c1602c0c041d55920555941c0d0002040c100d42c241c2041c085019210f800d03804c90b02c201e582014580b9500c000681e0306110000000c6400c0d250b400c0350850303c1c2c096001581c00d07036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 519638066 1250 519636816 519636847
    0xc23210c070b07020d06150503030a03091e020a0b0706090c06120c0806010f08060a0305010e0a14011512060b03060a020a020c09010509190e0a030504050111150c1804060308 76
    0x41d02da58407482e46410342540c005981032050401c01814a0b85a1604600100c0c910000307900505010342900d41c0e80d131b601d00000340107100e003040c12201418050020883d40d940c085404aa1030750182c4a55601c500704031000d00650072100044a5450700c030324000c1c0026807840c80e2000100b2068503800c001c014130303000b01c10070b0f034010380c109100704062442000031680e03210035100200031060520310200d45582010480071100c9410161541d800c2c00005881d21100003002400140252414500c104414070290f00780c40744001200b200b2581100705008120390703918000e10340c51240030000744180118002c030742401000c03610700c1c50701b5a0202d0f0b003507072042d018400b01d071a1040458100d001ea41c1014002412040302500040c0300840c01d1204a1050748603622140800f040b8a085582c101c041c2c0c03500a082d0b0f4454080da5001895141e001031443c8000504420b01580f21544203825607941c451a910703541040803054081601ca492040d0240c0752445139402440c0900d048590350720348d0361144c1d01c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 519639316 1250 519638066 519638069
    0x2180412080c04050d0c05090709181103010e0c160c05041a03030f0a021504060515030a0b15040b0a0b040e06011d010e0402072405070c23210c07 64
    0x14008a6030030412000402d00407181501c408a401260300b8030306061806000e1586d421451b0058180024815501c3c0c00948040480b01b0070704408518900101011041e00e14a100c00c844484003400140310003e05580440c2d8480405040079041c4040700d20b0001c40b43e00c0341c3e101a10b0b4440580020310803401d1a0003100c070b118000f075aa507100c240e0351901080c1d892160308190940a4008207450107510701c00d020402d5080b00064520120703041600b4240000d000503101c1c0100001c008880c1c50b428100800d03800f039082e41008074290903a849440c0700502811700600c0d40da120351388010b24011a07940040700300180500c02c14441e102e605094120300d92041c06401c440c140600c191811400307010000b120080388400303280114529102034042400707402800001030444070441d00e608010520000000c0251407404014003250310341200c00d49800030342c4203000d07045107110741c015081045005401c241800c0c1520489011308004044d000e004080100a5180c81c08006103035000d41c001005980b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 519640566 1250 519639316 519639353
    0xf03010c0c030e030c1f02030705030a030209040b0405090a0312110c011b020f100221010b0c0d030213050f06041e0f060e0109090f1b11010f02070b0106050d09021804 73
    0x100fa005c0c2000a00125640e07404c03860500005940c0142c118805c2c4269045e480c5e000b022aa191409648098003a410458005004500c0c00c0428601880e007800b5440c0500008406080700080589044980d5144a1f032000d440070344542800c0f48010350304d4000c180d003c10010000413041100101e0b81c0d0944203990f08c520856105143c252200d40e4003090080b64180804001a5030701700c96600c1c00840c12000c16070108441100c80001090480390b0001c0800c4c46291090303988141c14445e06500728000c40011101c5181c02751342c01d0140b810045030034200d01c10000c0c6428106a0395549001b072802c1e80c0c26030600005c3c0398034006c00440181c1d4170b0040281210f400d00305410044440020b009074141c1c07088a140946030800020740400a0707200d80154185105184140306191300d01600440d854014114150720f8082800c10f014068803c0c4c90100317034040e0f9201f6503a4070386001280d05e81c00200d420f00101d81d842d0300d2400182d031015030000d01c0000c031540c1e0214501d000d003000e007080704601d818403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 519641816 1250 519640566 519640573
    0x5060a0314101a0c03030c0c0a0c0b032a1909091119020705011205041e031115090c041e1505040e0a020a360203090610230f03010c0c030e03 62
    0x7811319801005a9503c0313020504c5440d2101d960100c0c540c40c2c5501d804014180d846090320129903403403d4001140b2030701109a07403c280004020740d01d0a11900d0b150500d6440300240b00442c14840700c008515140c96003460102882d5032146110b0080b141d19040b5070040a070000380e00145840c0c1c00b00405001d20b02c0740050a500d900d044000f8080382c518240040f85180d42c2e81c002401c005584c0c0614003c1c24402020a07611802c501c0c01500d40c142d464004c07035940c815540da9281c0d516506002500c0b4415510280c00120000c070301b404060b01943d031081c6460088500020b81c2400349104200c900c0284a40b03013030a20346007905010846505010145668010031501d4000d41c41c0d0000310400c641d010003295040c0c0c0380c1402e80340d0300340c2c400c240d01079030501803511721a1009016402450088100c4000d07101c0580301c9011240545400b072149030034a00143d42c120b1010841c200120f002d03200094103c01000c0c81240000e800c40b1181010320020480341740b18601450351204244002e00d9054005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 519643066 1250 519641816 519641827
    0xa03050307120e01180b1803090907170c0405040b09130f0203031b06010f1202030a0b0a0603121805011b0f02151209061b0405060a0314101a 62
    0x800510008041500b07000b03200604500702507659004540900605008100442c0140506140005103a0054507420415000301d03807802c1e101c0c44103041d007001c540001c6291030b4102e014032645000007800b1006029506601030312036061401024410658045015907403800d100810081701c444242d810302a040701410003190400b080108800c02c1d400c541d0b4880c0c401200e20000340365101e6240715940810001074000040880042c005058460080d007641441c0c1d1660300800c3c2c2d01d801c400c0081d505520000408000c610100d0b90035400071039241011480c1600c80d168000344600800300760b80010030000701c654980754040d0300c0c1000783c08246031680d0004070030641103c40301c06c0e802002d801e480215111074219a901d40002038525a480c03242903c0b003007040b401d0750302004103d990824902511000076070603800c000d08086212800c8102c941020304240c02c0c001a1381181d5a00b0040c150790749151084030001c0707145244602e07201c10385084407034100010507152190705402810107002c01d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 519644316 1250 519643066 519643073
    0x40e0c03040327060e03010e12071502280e06040b19030519020a020c0909070303020d022b050d09060510080a11010302030c04150206152409030a05030423030a 70
    0x1280458130103140801d4540f8502c40024018010205185110712504510809120041e400390040c1402411460b92a40c1014846000e03442501c1440480d602e4010800c81400c400c80034000e0781100c14508070120201c42000b003419a8050341100420020100b401807041070b1841464605460034074051145050030b0204440540880010443c5142c010454102c014800c00101502410091440c049070800116003038445546020a60050103040300c8280001d000080b0340c04e00c1403040c11400303d60f180d40940c03c000103903002e10b0102000400c01845110318101d01680c91340034016480046d4174104014107032001d511366800450280c000301c1d10740c2d021030182070b5100344800c403c0c01c0159595403400343c5081140300300d40100c0441c01c1c071400c0304400a1344c0020607900c00c0121000b0440311010742402c00403c0032960b4840c9105200d1450403060019541000c0c028101007c0d04441d5103803507594543e400c42e0880c0c0c0010001c10000002510203000140c4020410402070b4054244810580c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 519645566 1250 519644316 519644387
    0x30f130b010b030c09041b2c0f0409050604052d0a0b130f050a05120702091303020102090409050f120c060a09080706020301030f0b0619061103040e0c030403 69
    0x300302626614044006440e100e04130b001c8034543d074001003003000308034907080504c035044140b5020a000a520360701e00c40035040c00c1e00d80e4000300c525640ca003040b0765a0750108016400300c02500b2941c2143d2503164110000d40c0c10440280164803a00242101c00c2d02c1240500c0d51400c144070001301c10f0007041820b0300050780825540c90450300f20041414a50710511080759405680f54024034200342170b07580c07005002c0080f03502e030700c8144260140c1e1040b0003035010441c4c40307020325500650300045000128035081d9415081c0d40041d442400054105032003d00064201c800d8042e090740c01e43c000c0b0021000c10718050242c9054024003011003030405003030201e03281e941c1100505440007295184109014409044107546650358025010f550760360b100d00d00038840181c800011543c0289107800310758180740c01100079400c11032503c040b01c8140d00e0100102c50b80400d441801220340401c020100308103000d40200b9100c2e41980c5c1c111681c0741414640108603a240b01c400007203511813000102c80290710708 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 519646816 1250 519645566 519645569
    0x51014150403200105180904050a0b160206090604080f090a050411090901090c080f2a121015180308070303053c180106090e0d0c0215070c0803040308030f130b01 71
    0x207441140f00c03948d851515034500000842c000d480070300540100001da207007108401a82805503403d81e1040c0e1542c40d0394641d200c000341c4004080140a120445490080e80e02510704400000d01c040c00e100ea546002ca0122050680b4805403d0400601c1c40c2440c01d1408209005100c00d900400c4040301c1c60800a00b0b44201a10303c240403208100802c06242405085024500b070009280c44c90b004240ca41c030f0202d46c07041407020010086080048d01140c0340d0048074044070403000582001d158a40011a01240030344459a02c1c81c200c04804070203c0d004d0070141c60854400d0f01c0025942c20420250031407282c0703607005c0e01c6035003030b444044a0b010b603210b4007030000190515400e40c1c040d444844109003048401c0d28421080d61a1660000c0d00010a4200004004611080d00e043c0076030b6440440d50b50900c544040d410642001002c503d8903c208010310445004000c3c11130042d454920040c2913a10581c816100310202106110102e4248010b946d00001200e8038085002400e81d1200c0c0c000005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 519648066 1250 519646816 519646819
    0xc010e150708070c0306020c070608010e16030f02070f050304080105010b0711010f030207060c1808030a090e06180f010f050603040b06091801060b0c070905101415040320010518 78
    0x829204100840c241104e809550300c00d105546400204800c0d940d601e0181c0300701d0740003c82d294000100074038212001e0f40142e00b5107220709030241d5020001e401800314000c002c29078075400c1200301d000c501c0d215182e1401d68402ca01540d607403460714000754252041a00800c900c540200800c3c00080d4404010000307060003030804540420a84600b9030003802100d0018003800d0074008c625202650085040010113282929006000e0301d40c0061a074a025900d0140041004840284880000000029880b5400074203a411141c41d518100144010544260f903034020740398014088806401030000261005540c82415860140c90b201c030000c4020f84964040c007110804515042001c00e440c105800e603000c002d201031507a07101034000300e070700511120081d4021500013041c1c5013034a00a00307000c0e40f084074180e280c8900b030001c04a101000b0002d0182c8c40306030124588071844440b4040e1005500800c0003010b4a21450104140c0385c3c07041500f07904001c820000e200340580c21440f0080031210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 519649316 1250 519648066 519648083
    0x20c030d0305060d0206160c210f05031603050301080706030c1b0c0305030a0e030105090a0209041205041806050f01020706090b18041121040f0f05031201080c010e1507 74
    0x712000070584d6200d00b094082d400c1540014079030042101920800c1d0054402c804c920000b80c0d03200001d42900700000d0140e03044224189040c4013195030307541d00300d0103180078100b50b9150100859102c4c1000903040400c401050012004002c0e0238014000c8900500203820305100a410007032000b4141c1e02140c41d404400c185040c000c0c2d0612501c0106400515131060031641daa0a401d44060085504162042d00c25800c01d0001400c0384400f00b0303012021a40a0100f41203502c455840e0400d08102130a400b08116081c4000150454a18400046500550300000700c007801c040610004ca10b0341031106040d0f5001b0f040c104210340d407010907281120030fa0081725031181000302c58840c1c00c40b101d1040c0c079071260034005e1094640d00102d005000c00d141c42d00d0140b5094030754024106500d075044030080d1500080c005110301060740d128003203c42034442d4060301e1400d11076070003940b4100002c0c2c02155003640450300b40101c070358025044d8015800103c448d41c2007900b280607004190b118441d0000c4c4a140d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 519650566 1250 519649316 519649321
    0x170f1006080702010b3a0b060d170a090303080f1608090703140102180a03120503060a0503060f010501031d0705040e01200304230c0f01091d16020c030d0305 69
    0x6200703501c0300c050715130300a0030781b41001c51140d840059080d405001d001d05614070220201c1149803160050481544040183e080f0b98070079080203185405801c085d2a49030380e40c0d00b6840b040d5400b80080a17642019140ca040361803c0d4140104922001000e00c024814008203001c3d40d041c1c6c01c1070182e8440994a000a11962203455450508542ea0700084c46800c0090a046000c1d60640260000e9010492488902d41d03400040064103c007a100c05840c011b45040080c0e40c0d1071043d00190781c00207025000c035028950b10340200b0315002049986032200340304440107002940c1d241c05010001d81f000c551030b00074040703003140d107984520317883c85030a01c02c5554070200c0407036407002c0d008001d2428841a01110803207040d458003240754404c4804507081040b0401d03051004a054a4600102e02c060004200e071031000d0087c07010202d091300c1c0d42410321259680000e0072100c1035285015090541c00700b80c02c0e5007840c03844801400d1450481c2e80554006640324120b60b20300041c0a01c0118151501183d0b43c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 519651816 1250 519650566 519650581
    0x18051623150c0a0b060909161a071202030304060f0b012001060306020f0408070503010203150405180d050c010501051503042a0603060509070c020105190e090403170f100608 76
    0x307101e80b0b0107650301ca000b03400d400400d1091408185208140c1a160403d00d030380c510b00350a8886010054040e1802e0301184180320381da40340044042c0300b145030070040d883c0844540b54806039985418a440c01644008100810048a4016110000b00c81c1030244846082c0342c001800024501c150181044c510460141c62864250408002503030810302c2150b40e410040d10040d4245c0c0640210000b501c40c09200050a040501c03c80b4407800300800113648140c0000100b001030100070b04445458007140c901c0c45003440007480300168016168a84035545d0b0704090481d403e40310164800b52064030415507040c0c0307090007602280e600aa11941c104145041d0025000103000201c1c0e0541005818940c0402c1e81a0940d000c032041c2d42c002c4865021a68881000b11030009103400c00078002842848080311101088400031080000d9042c944404548180810030402c001c6605400261510031440d0300005403600040d0802c0350104400201d2a25041052103030342942714030005c00c03180000190f030341d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 519653066 1250 519651816 519651859
    0xb0a05070c080a020108070206010e0c0a020f010c030f1401080d05070c2d090e07061d060706020306040b090121020f030a030f1b0213020d18051623 65
    0x2040e800400e1040307050302c502605980d0402d0b43d900301d010500910114001c64000a1b205040350000c03c205407a61707882001c03140380c50704000c11200a40c4aa041c0d5104409420301840a000301580d80014512602c880c944042d250358000000044011000500000b0000302c0c0c810125902410429503e004a103402100c403406a0b2003021162845115803d0f69200c540c07010082d107403001e200304105510360340c0c004201e40004910443d682d0140c1c401b04401c0e40903c43c40080980c0024440603441144400700b4290307070004c881150308590000070007000b0302e001e2140300b01051007510300c8030540d03041c41400d0841c1c488100a119200340040d02103021582c2c2c0651203c00351402800307540f948146842d000e0000d105046440b0045076442502207000107090f410b45480b903400a0000e8843c0c00d007080c0c3c40000358848104480d48649401d402500115030192901100384102c0c01481c88085011040014111a03006800310150001c4240307036004003600d1450303120500321002c070750303100b85114800403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 519654316 1250 519653066 519653077
    0xd0209010603090203010c0518091f0909140a0c091119030f05150a0b031510020a127101060c081804021201060f031103010b0a05 57
    0x500402600021800c0d40d8103402040106100390001c0c060483e00072415185070040c042a4071035036440e00241e040515008218035000341c9406680001050310f40b05004030115982c1280744a0323034072440a1404c10000101004050241350054091405150f07107d801030181481400b64040d219815034100b00d10744002c64a40504407500304031500d0a0f00d01c0a0003a11a0055074200c00e803a003000649010054000700000144c020000b1281d1810003010b104182c10250140cd484003064070180041d84507010036650300f1140c0d030014030366940c81389054043c81200500032070410080000384050a04041443e001c06d24803d0500707412882e1a442d031504400e45840080c02c50b00030321544900c082640081c0102030560041e5003090f038910106c00700f407403417401c0c45180009490030039860007040028010b848441403c2102800040b0369200140aa800109034007444062032001002025000034003203207082100c1c20280702008419105407802d002c1441614040100014210220703803240e13040340c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 519655566 1250 519654316 519654319
    0x14030c121608060a03030f110a050f03090a090b100e12060c0d0f0203060619140d050712050915090307020613090b0105122205030d0f0606030c08060f0d02 68
    0x586841c18854903040100d410140100e09010041101ea04090702c9010949800d5121034200d45200710b4101e9a002d0f4101e03035403c15000794074503c0c00080d0705210400c800501e12004603140c3c2c8061702040889480b9070b104000c0b443c0f61014400315915000200d010074003060130150218100040481d440c07048000850718140110030030418001318140140482c0700d0301980410400c0c0d00402000100d12050354080d510582c00e220242c030001203040d00e170700c40d5000f81c940440e43c1c05400744040f8103a04641a50018161600c0030003816550044100e65103102c060000d10260424205594440040540034201c2c411110002a02c1e070f042041107441155000d810345545072a082450403421107113000d084040fa003418a1000b15611070415280039440450320030f181c54650907010304144010910b42c0c0d1092030058000310210340c052010741004a030019004c2507140102884000b183da15821240034103150900b1042d01c1c80d03001550503440030054480442c1c82d4090300c0020820205840c000307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 519656816 1250 519655566 519655597
    0xb10080118091202060916061d0d08280f120c051c0905010615120902010e121c02030f0a05030a090203010603030203070c0614160609080c0705030f030a14030c 70
    0x40b00551300042c1244103440503820740300c05800400d1082c00b4005103105040005a20b104443e83e800f848900d030340381541c4001c10602040c002d81c5d9850b5100c0d0840380301001c094000303004145150b000000303000e00d415603514044032441150074005d0a440300805a000c4042c0d03964401c5004140114104c8590802c10002c03001c0f60440075071160040c04a42400312060350034850700140c48100500840315200b850f860b5164914551030313410008050341c2e9000c1e41007000c03185c444c0740c5586400451420410b800c402801000c1281213070701d056000b60040800c115481089010900218203081d50419007042c81c14a54a0b200e44082d0f10181c09a084c0c041c0d81946442c8000081540010040034501c1c030800b80700145694a100588203051107440e0300b40702d441c00b00103420203140141302e00100a4414040060044174031b03111001c040c4c1008002c0910f9074428002030040d07103000c01c000140c503007616004600d01546108020845406221601404d410200100703030442c120800b6255040c1207581a07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 519658066 1250 519656816 519656843
    0xb0307030b0a270c020a0215090a12050c030705010f0309060605030304060f02060f060307030b04020d0f150e06131209090e03031b28111b040b1008011809 68
    0x192210486018940802c102002c15800c200f064a0191034a08446900500380b600349940030300040f10300e69610b22800c880100903107031056880d10303da4005000e01c00b61441c440e907514500246032403038682045109a01640e001c02090782d200944110824640c680400e5030300c0103183c800050b0133907800003a45408081001318215038488070388148942107034211850758a1714449110b80c0780e02074032250380582000106001003200103009603005480900340909032115502d903105e01d40070784901100c0c3c04401d60708986100545015120b400016880944010f05180103d0003050310300c048020031007811014600d01890142900038000c04503c80c2c2400f04082940e01203403254000c64002c07452007800c40c2001c030401c8110301070380c40d000302c0f83d007902c405602514110b201e1040c1d5880701504012484c600c00d61203100903c01c094050400e10304090804030131004020070365212a81c01801941c80c0c01d6917400c600d43c0902c2142c1162103144401c0ea200c1048454200a005584000341c94a000d0005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 519659316 1250 519658066 519658079
    0x2a0d060230010b0922020316020607050a0c14120f0901080f062d1003020c060f060904030809010b18040209010503210306030304050a030309060314010f0b0307030b0a 73
    0x1602014800ea2403a181111201144001c0064203001e03000080e8424004500c03d802e00b004c945000c41490300010201007540b0034440b040e07900c1220070b01034600e1580031a43c0119010042c0541010050900e03d04007043d40b0801424005081c3c0d02900301d41810130408001807050040d00510201d01c2c408954903030580100000c1c039800296920300050f8081d0000309150320401c00f150144400503c105940c0040100c1d0101a03084840783d6505608010003a0741c040d0348042030420104019100035889401180f169410100000e184030100d1904600304056039030303004030080d4040d80c1070621900c05d49614180c98010000c0c5501140c111720b2101010300c41c0703600e03140c3d082e01c9030f4800c40308405140c3e242c60505890b4591071190701c5a284000c4030b1803481042c15000780d41e000c24013404403070820b039842e000107686c43c9455200360045170303a041043c00640c0d4180100c68110f08844607980c015403600d550450000f0340e41c807400701c0c1c044020002c1000144290021900280000c00c94030321b4986481 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 519660566 1250 519659316 519659347
    0x3090a11062203051207080703080603070b1b0f070303050403150f05010b030609090f032a01050a050108070605041203030b010e090109022703073303050a0c022a0d0602 74
    0x4103680030720a072801804444942000c4520040c0c5c40301c2d0366818800149c0d8207441c42040a010a40d26016841e80030610111420150001e91611540c52030001a0404c8881c2071040c484140d00080d00080301c14404250004100c40449a00c45110100b080320021264000c02445181048460400e400081c400d407540020f103005100807140402e06031251440a9030b40c800c140c400e00d0460f001030100080300704000805a141c80c04814002c00c0d07440f4001c104600711841140c2c186020f503981d1005202e015070401082c00030300064100640350504140b409003800c0f802410003010541c69162a030741c41d91207034080b034a114102800c01480355841d24403080180d0410707242c036900c24002c500e0321641010107201c0d060384403501030040d04d00b0b40d041801000003080c64900080c4038140c00d40e5640d03004c0f0440b070389a00c4480501d5400080500b0111960402d45000e96040001c540c42000001d5024200c0f0864000041d607450050040c130f010000804c104600b01d840c003902c1c4501c08100300307141e0380707445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 519661816 1250 519660566 519660569
    0x120f090e01091d031303080a170a05010905090a05070b0d0b040c090501030f150509060f120a0b01050627040f0c051c050705040b0304020d0c03030513080303090a110622 74
    0xe11500c81e40c4210495550b8170b01070012203c102d0340880c401000070650b241c0051039402014a0305404240340580d00c000d001c41c2c20b0f12001140d40d582c50042108220038850590000c04840181400b1511512000d1307450303003503000742d2102401c000b905009000035a0b010031006140544244491541344c0400741041038103100303007804641007002c004d003030020910400e0401d41017806100700040c2440d0621003030440082c01c1980090343c00703402c00c0450380c540300c6e1551039081c003400a1030108891b14010040c40d2060340b1841c0501000d101401d0309040310107a10700c8540741c46100d08051000c0b480040c0191500307400c0c06125a00c0c01d1200c102d6a03610800903c90101080c0d00c62010b0000340984108a0f2340880d4200c0000310280b100340044080c0000445d00180010021418010191902c43c2c2ca08074580c01100460720008940300360041c0d996110f001019903901541c00c52400040440d103514040000421700e41c414200045240d442c4000da98004a40000f0800b419400003a01c01c031580e020b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 519663066 1250 519661816 519661841
    0x6040b0907051333030f08160516090504020105090424080d090b04140112020f0f031e0f0c09010302040b041e090903090509040203190302011a0904120f090e0109 71
    0xc2d52030780d030442c60084c1d0b100044a0040d0b44d2440710300c1d51b203882100401029003110100f074100b0158a82c4107a4449901880d4007582c041c100d080440b409410a62120781c1c0b0085a4508003c10000980c0c0c001d03041c0c5000785001d0f200410804107140d03540000f1121541074100903030840e1008100078400142420a01e4496224100510303107805500d003050046200d0410b2000c0d08074258422544280c00700059121300b4078000d402d08800d94040c8001345c00030a042c1c5000200401000494100702424203640744810f4880410b9040c81108a000751038014480390700100009041a0315034403c2d03041354000d0200444440e142d035280d8009205100380100c10321780b03100c04c3d440080740c041c80f030384034084030186e054481000803480e101c140f00c0c40440080060743d0500413140010040c200162034030342c1c0d0b648a540000703075504040045100240c0c103801c40c14019000d5000b0000046d0710004401c140a00c6420091860341840000f20740e460110741002c03d061514200006600406d5040207960b40403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 519664316 1250 519663066 519663101
    0xe06010501023009060409060303260f06010e0d0b010f05120d0e04051e150901140609040203061c050a150506060d0b03010609020a0e0a1706040b09070513 68
    0x604038900f0165a810804410400356080500c03802864818014030b507180c40a025241495960a1541d00300c640640c4142c022820307007003408a858154035040e02c05105840c04c04203150a1014500c00c00c1c4000074007082c10310201701002c18050f5030701243c009175154000d140c640e1943c0c503142c10b0011045c0d2481f509028202e1703140c0c280c00ca0900841c1207410400340d0381c1e411104031070070380810029000141500b801c1d008807032581c0610160f00c80c400341c17003801c4850740caa0110f4903420601032040d030168041501d440148158919581d1420102e659861003110056260b485240000d030002c0c54035207003030340007101c02400d0000300400441c11000c0c0da400750740d81318401c0715080d1200d01920411a541c683c021804c00030400c520140d54000c0520b4032010b000090f806440e54584e000301e91224035050f02007045104140054501a007680b00600f4203008440c00004110600b0780e6241800341008044c00003038000140c8c5403104000c0140203003c000c12085c413202501401000402114003140040322 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 519665566 1250 519664316 519664333
    0x705070e070203030f0a05100906141009050a120215030403020d0e01080f1611072d03030e12030c030a03020c010b01020a02010e040e120f0a0810050117130203010e0601050102 77
    0x2d0000c000d40e403049242c902c1c002d40d0f80d070341c4168100080000400410590260440108100100d0310400000e407826100210010700c07a00200011017512407500f80c208442c1880a000c1603c41c2d46c1e01404545a0b034151040c2d0744000c1c40001c100406540d00d81e0705410020007040b0a040d4002061007800403113445141d4045c2d0403400448400d60201d40428560041e41c000c11b4101c0c3c1100700070020b035480c518203585940d2111801d41c0c10300c21f295001c03500341c0341003400307120400da2540704603811250810030300b51941d0305c5e654001d000c1c0c0c1402c84c01640300d00d500c40c0c1410740801051084548215000003600d030745d0001088090003d401c03200f44410070350300c4c140f02000e695000143d00000e440e0140c4801c5c121421300400c0001400c0c60308034040543c0918000701c1c0461443c3c501501500340c8003c0c1d9191240c031f4106009207a000010011341401405070410001030741c00164030b144d980307e010301c0c03409103954034100d9046a00c0341c0c403c000d4040d8641101c000840c000490014140c4a09034256510503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 519666816 1250 519665566 519665581
    0x21e061b0141040317150a06090806060405100801150f092c0307170403030f09141306030b270307050c060a031d01090b130302030a03110d020705070e 66
    0x200260502ca60b80240e0840d40c1d01c41001001c03400541c0b00b44203140a0885e91419048000405000d40c4c2075208103d0016841c0403d140c002c0107000544071034a00100c01914110900c0c2d03494002038442401182c1d2034010a03900754003400c002015042000c020300608100d455513240340d060905c1460528451207a0200b4444c000d40210103030980180c0c00b4801d1030740e0781c2140c510a50003160b0310b0680303031004000210000304201010540120803c44007078403249103050180460f4800f081402c02c03c4070307460041c070604051b0004450036200c103403003074269003500d912880000c1960303801c06002c0703e41950030404519010301180d8200800c040310f94a030300010b00c1d21240d0b82c2c068600000c18940013078080040a0403c00050810f15000c0d02e07010940300b1124130329050440740000f41610907511510382d2030611220440e03054100180c801198800d14142c0c0b402905c90003001e112500b010349524414035003e44907000d894030f03c005c0308002c41d40c0d5043d80c0740c025a628041d2140c421400d200b0130000d07aa1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 519668066 1250 519666816 519666881
    0x1e010206160f0e0a050a08061b0c1e030d0501090c030b01260405210a02010b03070308041e0f08010603050c03160308030c04030803070306030b1003021e061b01 70
    0x36101074586804580400000352a00c50502c003a068110f1404c010000e0241d0b0398840308002414901e001d0007540c20b01c07032004142281c2c1d90700f0505454504000442c050000001d900762115404000c03048e9941400c60554210310440518041c1203040200125001d00c80f64845039810029840c10008100c0000c01503602d4143c807105c0503e03001952150340000120103c40c80c0c2c3c400d10813000e403405e6407256138040c822614480280046071002240005505030248103050300c0c3c0300124010014207141d513440c2c4c00a40310f28054600002c004d04546800300c800406440c01030001d40e10385500362511420583d000301100c0c40281d6003441001c541040609011600309410b00b413400554604038290380703c10b90b403540080e03c0010140010000007000c58820000b450040d2482c3e40c0100c1c4692450a02c442c0c1c2c00c07405054a07032601c1d0200c00c1000141d0b42c040080921a49419245255210f0300d400100d00380a030303003125000c60011484c9101c100740e040d40070000d5007038602d41483e440c81d202281d0064 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 519669316 1250 519668066 519668101
    0x20a0f17060c090d050c030f0a02180103050d0309081204080a120b1c0201050f130906080c010e040c1b2a03030c20040e0f0601270e0c1e010206 63
    0x1080300c03c0101c6800c50070321054035142c050041c4211044200d06a010034500030808019100b1504400000f001b1840d00d10900304024120717410312103007035042d1b481d42a00c84451010300e906059843e0072203030403c01e02e0002d4821020b11540d010456181500b440d909030780c8550340700400296500d11803c203010040c40345064600c00070b0020040003400d0101101c01044024007a41804014001a5541c10151009080301c0032401d8a020b0072501d04000401911040d030021582d68004403051403050344d00c0030302d0103000752040720045244c1c0c0c4055800d644006940d441050310100c0701141300c0612451490139065035648090307600c0d105103031100851180209000c014005a03076a840080030507030310b04001d1458818102050040d48141c00040c003203c03145850444150400d000c1400e007440140b0400740145150a00308480413011020344c80c250072008203115500d66181c0c01000d01c0c650811600343c1d07012001d0482d00316000b280500170043d41100403158018800c8400040f440c441000c01c904 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 519670566 1250 519669316 519669331
    0x120507180204031709040e030f0d0c0e100e0f040f09020f120a12090e07021c030203011d09010209040507120b150307030e10180309050a0b07030f0c020a0f1706 70
    0x130300c01824691920040e6114041d110740c4162540140109100c06000511411300e0300c2d01c00b10b980742c00c40340d8a803082c0c48141540740180f250070305080e800ea480d5200301481210030b030714149aa403400075001554461145c0c04094005103445042c8a01c541761344c0c403040641c5e0007110a049000811810006030759060700c4000c0d4650450710207030340003030301c4d64051040c246101c1c100005003d440d031111a02002c4200c550100682c000c9140b0b507414040f04001407004542840c06501c3c540c10884c04001481210010310741884140c4006034000b14294160f4041000051040c0031504291a0061081cad8125000000c003610f401100212860320705518802c84c4a40c444d000d0071983d4086040d40100254510b04407140103801c008142c24095102e440082c0400c102e10302440081030400401102180e08a1030280301d06200c14410800141c050795401c50b40b51808007000040a2400c491078150440000d40190403014040707018481540500700785c43c4000303034540c082c2140440703042c0c0c0c550081e200c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 519671816 1250 519670566 519670583
    0xa140405031e03071a0f0901060b1e0c0a140d03020a0c060507021f0501081002160602030603031e0403120e0a0302010f02150a0507090501020708060703021312050718020403 76
    0x1201c6101515000c04071030b6000790250b80c2030071103e495904180758024907200d240400e403020005c11405c9940300541151103070000300001030400c04541083d02c5080c40483c100d02074a45818201003c010448900e041c420064a0729510f01e4039024803880c80c40d002820300c0c0d0041c01d00c0903221500c20f01c242c4209101a0f601c103a98074556403240c40c000c0002901100c210b015460001444404a1114691130801c400380041c50350b2514000380d0400002404118846004000310343c1c0f03041c2c0c00c0301e0341d60300c0c9c03900a440141d40c0d0320f8250000380355100b100e41c002000a040854900d00444031000b40044070700808101132005280c813411a00080900c6107543d201160000c00c2c8055485254a22488082e5004992000d40c0c90165685100300c2107800c00c218649600800407220350150f03c2100915081c0001d0000d07a0501d50595228200244001c040640c00f281a500400241048100074040003641c05046c6055040141c0c49290703c0c05000d0348880b28212100008607188200c6049903007001c401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 519673066 1250 519671816 519671833
    0x4061d01061e121104092c0a02010c02090c0c0a050c010e0103230c0c0a1104060807050a0e061c030c021815120313060903030f08100504200d020a14040503 68
    0x2401042848101080e04c102888049042100c51140c40b96008403c0c1104845000000d070003d01d072140a007110401d604500781070790060741c0181c0d07018030712541150f0041040da1a1090a695402941025041232042e40030700801d00c140425800046142a41e4036418003e030200103409031040f14012070352800501c1c0d0011682c40c1107400440d00b0860a88c811481c040e0204079880ca4000385440980d595a018030f185c1105103810f108040040c11014090040c0c0362410740052203040c8244640a10142280009440c9954926255400d0261b1340d51807000c1c12000d08004004c1000d1200803405a524440c0c0ca4031a030311100402e5200d1f52f00d00052107010040c58040c000b03c07174403100d4100901c0c807040c096542d00c4a2070b105488040c051580d2050714291450900170140c80b18805031500780516042400b60000c0c0c01044070302910400e8070045a503190f032604040180083c1070300072003500070200d507043e03aa0210f50003d056650342d947c0e400320011030403905c01c000c0e48214428550b0523400841e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 519674316 1250 519673066 519673097
    0x706080402061608030c041409071b11090a05010e0a05010b0406213603020a020d0201050d0c0f030e070f06030519051005130b010206040201080604061d01061e 70
    0x1444268121203403003c45000036520400710350410b840041ca20000400e05001030b200c8626014189941114035962509007807102038000d8201d0320903032843e50500700d240303004c0c815080b12818441e080a4400102840c001503960300030710080c09a4604402c00d0000304811003c54059103041c3c0d402140b00d20301c0c0c645071050503a4620f001001c4000c09164029544440700041d2240e80c220b141e4007aa00c0340300b41258800403800c5400b550f01080550411504900440e50004500c9181e0340e058030f8891f410302282c00140c42c4c40c0644410701c400c15040c110381005040d40824481c1144108c1d46040c44a040f9078803440e03845000c50302980000c00180c507030800c41c0d10703c00d8100a4000d0030b02959486c2d0f1018003c1d05100341c9400301c070043c094020700103080105081900968400000540c410010305012100003521801c000d031001c1d04000c103443c08140300b80e0742c0760f000c0340080034194100c03c01c00064400006140c0d03400d100b40c4011402042d403039010044d4144600c3c0c4084000e13030702e40e44100101c14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 519675566 1250 519674316 519674329
    0x915021c020c03010e16050303030f06040c050d020706090209010b0f0d050a150609030314040308030f04051e21030705031b09120307062d052d04140706080402 70
    0x480001144942c0c98040e08a840078032480700600141006800da1100300c4240041000c12540722034002c3d80100200712000c500e01180d6600140211381c04a031442c10064111340e24001c0c4040039405901c002542c0b810030420340d100f5801c45100b03641030601c9aa032079440c07544901508840052180f4100b01e09021048030358062540310306402d00008800313008030000c8c2d207000305036040040450b12070300d414414180c1128000011a0f8140c1c5c034685402d00790381d59a40c5601000d000240d00c60084004501001000d0142c0e0382d5040d140000041c981a0400c0202e94505841c0d040100d003915680b14102c0040360307907045901c0345560707482c0c603840d507124120000030381c40f0f000700c0b10000c520080c08241186d0b650300e070310b00320f2048010303008584900d42c5040c04000c07102e54008501100c0005c03454500c09003ca6020170400e0142c05900055aa079402c1c000012420a50801d0f00740658203000c41c6011411072007040d010318002d4100b400c1508466541c90b50758866801840c1c003280084002600524012 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 519676816 1250 519675566 519675613
    0x1e0d030e1203070e03160b090d1b150305090703020a05040b040906022205090609132f0f03210d0e010c03020408060705120f0619080601090c0e0603060402210a0507091502 75
    0x14982502b0900c080001400c00300e0a075002003c0c8a81c00e001c44d82d4031503615000c0c464000c1100005055542d00c1c590010381e81e00c1061051034055a2902d030158550f54880d4045901c1c241c00107800d5646194030800018182c10703180c0400c0295140480200702d40c105102a030f8441d20020301807041ca5110b000540c03000823500b40e8202c8a803000c1c00038124104a140020309801427011015039074550500d000c0112136811000b00302d029601c00382001030542110b4011a0820006480c4186d0f50504207011a0180060316200c0c001503080c14008880c803030703169009008032149071013518141d4030b402e00c2c11210b40c4201c0d9545510098180c0200714400b103903022082e0416001002c04280c612003281140c00201542e002440750b821400041103e00d0150007034a80805891609519858400340007454030700014041502403540490010403902a0410b040d00310707070768160864524549042024060101103540380001061004001690b403107100122400f44200d402520f034180500d144070300c1c1034544 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 519678066 1250 519676816 519676823
    0x150e0105190843030b0604110c0c2d010302090105121f080a0519050a080c0d03060e063a0b091e0d030e1203070e03160b090d 55
    0x3407940002e0049410000c0458040054000250b07003061241c2c0d58900e103458a0100d07002001c03c14a5a400d0a20603200f00f09407035210700b4084603602d4480200300104011420001103c1c000100003080d081300040e407180d46003040b01d0207143e01041e4544060354040780307100c120201c004200d40c6281d560103a00601000b0b03006150103410050280c0034184240300981d0710894144910399040c0341c0796036010b00c94000d400c40380001c08a95074260f07640d640d5042131200429005600c02d444000b048000e01c08821403c0c0c000d0b40c21502d034200c40c1c49141d103403480030b030001000c039140c41c400042c0956004c4d0020304c21180188441c11300a06c180300083c0310040724010700540c01c84090b041c6051205001d40225450107036000250a26282200c1c625002c950381c0b0400f4087c8044031400901200003400072801c00d014540840c03100e4443c41968513160034800c924220280220800000560250310b90f0021407080b4100c0b00b050001e0f450540303491450340604caa98540030000c2c4c100f81d044c0310715000f00d514032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 519679316 1250 519678066 519678109
    0x151918030f030b06040b07020306060301050903041e0803040b041e03020a0e06011e03020d110306100c06021306110c01111209060702040e060f0f22060b0409080c01150e0105 76
    0x1030140013a03010f522503000b00c96440300100d080425420100801903004009500070003050800e0400591383e80540e00c150760908a90000c40007000104201150040c40f40c40122030703c43d500c500e0281410f82007801000c002d00c24034104500c00b00c0c424413141003240c0c0c01920700b0100d642030021548100400400345410300c0448144151544103c00116403c507483d950016241d001c6000c12400340d80440c4400401780c1300510a018042d40d942111001c0440e050a28043d644507500d41200680104440c242d90070300c0020380010399681115030550b624982005031109411300b000195603a00e48000c90520690011054420300c04d01e0380d000f02403103c001440c445c20018250300090664220452580242e0010001d1048160008000319000100752210340d65516040001e004d072003038007a28031110f620444030894207000d1039505c80c114240c4040d0082c000d001450502006940c000700311600d11398a00140e2482c00a01c201c10942075641c10705804450341d00c0c01041011618524102008004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 519680566 1250 519679316 519679331
    0x60807080c0c070b0306040b06030105100c020118090902011412010b0a0e0603090109263907030b090c0607020609181503060a0605010203032403151918030f03 70
    0x2104100c880000c0a010103020b17a249441c0050000b40c0d801d6030003641c05810b003440184010ba83c0c0301a080e442d02e2302e42c68400641c0c01c090004850b5003a02402400002010f4000429804142d030400c10026001780c84800c10b2031b501d590648014454000720401d8681c0100051010540a9005100d445040e15260380070701241c0002904643c402d4070590b01d076079035442003001006119289000c0c056400c0c1103e83e0490b20f400d0700c034003641c0302d10240c4050b0b41c071302c0407440c043c00d01180191081c400b243c0451038007034211603012259542c3c1c2034042238480d030350a0400180d03840c10005141d01020000303040720b420109181d09112140d08400240c82d403100600306001c000b8015034410314442c07041c00c149583e00300f0070178081c5801c1c41c1014000414a07418840b05016076600041100e03008030789003041081501c0d8102015103903a850300741165150251081c0d00c500c88072001511401661003280d0b0444003d403030303030402048407104c14a2101100f40140d8050119001d00080050310409040200c1d508 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 519681816 1250 519680566 519680587
    0x1020c040b13150816051503060406030c08150f13080306040e010e0a060605090105010504170a02130b1c030c0b1009090f0b0a14010513020405030a03081609060807080c 74
    0x107400ca43c100c1c480540c1500010000804200000c0a079016259115400039051101142e00c2e481d458000142c46400000410229107459101100564121074455035854844e032001d91200070001c00c951403e14110042a04030403100d40b03540c0a9030070550902c900890302e41d211022070b00020303c01a803155880009241c1008203004984404020b5405444101d846190400490341542c00a90103580242c0040c84242d8220b001c490075105081010f010402c0000c0d081d9203042e0508400a4020151215007010700c0426000f034a03c0400c111425034445401da41c804071024910034000c2c000401124810b4085005c5180d43d41d0000d8039254104542d94944500000b640c40440b800c4442c0083e06200304140800130444507000000301c00c3c1808240604510160484810700601e842040300041800401c55150704940040c41c01130241c48088000d824043c4c915003080720910300c00c1c4428003680203910b1044017000d0070350380341c2d4035404030302e80b1075081c02c80344c03004018400d02d03201c00100480030b40c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 519683066 1250 519681816 519681821
    0x8090d030b063708100e090f0706030c030e010b0a030b181504020a0b09150a0c020301060f05030601051807030f0617070602100c17090c0a0806011d0601020c040b13 72
    0x80c0c88100008215400c3c409806100100c40c4107a0801080303030000c284040d07010301c4554070742100d2407441007080319164038140f581483d9512617101c0080c03254400000b949609900009031000250b00e0420846c0300a107400c5003640d9000b00081e510200c0d030034060002801d45803609400050640032605c42c606603000d801d103498084d00150703085800c207104101c110b24240580c0780240c200443d1150070070400d0ba000c1003542a404484005021002c00c940d68264491207092802c1d98006000307000040d52006131010342d400b50300660f4003034010180013186030f00349a066401d0010500d10b0491295540c50400c400074190800110000307501e401c03002030821819a000d408008810700500b4007980b62003000b80c030b0095100300c0d4142c030a04000603500301c0b540294114500c500c0c03800301d86907590340310001030707041c40304480f04141c0c040d500c1c0b0310100300c40300c0c001940e6050380c1c02001d681c00405503001e58254212012502a40180e00500310b40300c0501b000d4102244881d00a01805100051040904103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 519684316 1250 519683066 519683107
    0x7080f1603020a060b041418160b0306030d02030705061902070c0815010f050102030426010221060103020906030a1508100207020301060b160308070e100905010e0108090d030b06 78
    0x592040180c1e0f014440248030388212034100f2202007000e40380c0c0b500510a070b1800140f0900e1207100340423094002c0e0400b03104c6114040110500004443d4644410481d180c00a551860082c4036090f070084480e40000200d42d0029006001021030356601c844103401211110500d40d48941c01b802000c2c0026114030790341d0098401c14028103428041940c4000024105070700a4819480c549010012039130040116016120911071103031035502007000c44c54201c400c1501c000260f40c800507146401e101e940d005132202d5491104281c1c0f59450303600044090740580c0c0b1103e58026000c00c08508207440d240d101c08800c0f031842c442e2004042d41d4000090400080d600d110040c59000680c41d4110f01e03080c03041c1ca0160400101060a1a56100d041400342a40749401014400385a0100b01c03500c0c0143c40b0b550a03c5002419804080303003038580104051010300c01da601003108060019183d60044102030b01c0f0701c0e40d4800400320541c00070300490184c00d501052a4120408000080e4019010148201e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 519685566 1250 519684316 519684323
    0x21180103050a090516141e10262a09040f090209010e180705030303010b0d0f1d2b05030601141612260703020706021809010636090207061409030f07080f16 68
    0x10322701e16007810009200c00c207990348030f501c58808611042d550200d10703054400e110710a4500044a0390b1810103d0024941c01c880070394044034007000054601c0260004903c100b030159009801d081154041c25540d0f0b48030f004590b40b54109000522a9040c0900648885c400715040455506014026a0210780d8810101d200286400140201503041001105000c900e1800081c41d0309041d0785070f041140028581800400200202041d001d038880d000500e88042c1d40001c3c00ea44076080c1040042000c0819411500c44500b0f0818a06013400340400c4010940f20403040c001115051000d0182910014408001d05600780150b502290b81440909042100d2184240380112003a042006001c0c050b80301c0381c00c005411800398220801c48008820340c403c00c60301002548001142e070300d42141d0640113022000d01c0810700301d003845456080b11403904903407004003a0a44a00416035140c1c424000941c1c6010410000c00b800140400001e0034190450503181d400c5c808a1460462902810207041c5c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 519686816 1250 519685566 519685637
    0x140301030f0209040201170a0903030605150304080706060302060a080603060109050c070303050a0f02040b070501140c16020604210b100f030321060821180103050a090516141e10 78
    0x2010160588552000343c033707044800003920890066044110710008200030400c00c07022410604200540d0040009140e0080c06e042d1030f02081d020040c02240202e6903940710f442000c0002511400c90300c1914010140b200c400c034541f1380e071038074260043d1802418008516603248141c1c2d501038449e1010300003400b8038260207a0303600c4050030b1040c00c0d1481200bc00907151103040500c0020f00130308045076078040103003070060300c040c2c900c0c00080c42c540500d074003110390303030204802212a8501101160300d04c64401e00c3c0e011156140c40200c6c204501007070040c0300301904201710910200340146a00088042c0c40118901c130300300c0350a030102c00c0d14179039070000040e6404801201e80c00c40388004010503818142c590a400c110050040003d07a002042001e4141551803010541620854020105081c0c000381202c0004079030f512111401d080300d2050074010795103680c00e04c11030318080c0d000e1070076594101c510041040c41001044000e403038420340713a01403124010717030002803500d0004030b0219240b0b000c0c00c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 519688066 1250 519686816 519686831
    0xe0a0f0b090307140121140703020d0c0e010203090145080a02100f022b0e0306162015010f050103092d02060712140301030f0209040201170a 62
    0xe040c608103d580244803810030f21000a070090b40c3c0141c0c200d41100002d244407101032581c0c503001008003040c004400301005110104100c854064006018084100f44100800c5031807060443e01010000046801030304100300e040746540c070400800c95012101078070001c0c00b1100c5001185044100040000f08441500d01c002c111a05030840700001e003040e1000d48001d6959500003a031501d0b0003c0c000045c40410320030042458420400c6012086070000840889030103402c2d0032410040b451183d030f00049080ca01c02c000c504010800c0c44c000c04036840154401190443d0541c0c80303030090b0401118090381d4084030007180703c0411003081da0035414001d8121030b505058000d1b10421041d007065041c103060960701740001b8060340b1010034110012140307800780940416a80d00d45100054081c1d030200021444605002c6001840d18601c421030b21250080707001001c4440b4070340001d11000d84213001ca451090050300307103061010b034080d10500d0180b0000520480305a002002620000c0d481c0c1e556400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 519689316 1250 519688066 519688069
    0x40b0418020f0a1220040e1f0c050f0c190c050f0109060210050c0409020a110d03051b0a0203130306090b060405090304091104050a0b030f130b06010e0a0f0b09 70
    0x7640c403103000043d244580c9007414019a940f24042512000300300d40b460001080e094903050b103d980c07220764020000d01c140d07000958007503035800d685003126002c0e4103850280d09000420b80701d5005c80b8103039901c0e4a0b0030882e4103008241c6981040e20050003500441400c442004d00d030042c0a2380c00d502c10012001c4c018148814001d0b4038008045903410702c908440c0c01c0c882c058001801c2e80d80e54940c00c8011980e56038508440d401401a5406404000c2c000f00e0800794207a0811442c41b00c0c2610001201c0818441c0e0104a040e05c01c280c0b4000311101051201c0384100c41e85c02d0003410258440c1c01101d10f031004203220907182c44e01c103a00c280ca40580e6020700c1004c010280884503080790017207800f48028240058882e482e44298481d8800c0c081d0744140f001e04018a070011317a8001c0c2002487c8607003036545e5800d2106a940101c8149541440010008400900d410550040103410894004450340c03807100540d030f8208100c040651111094000240040300c0c0409240600062240c2644510f120b10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 519690566 1250 519689316 519689329
    0x22206080c0f06030a0b060a05070311060105010f0c0c24110f0705010c15020406031d160603050601170103060f0c0e09040809011101050f04140c130b040b041802 71
    0x20403441294110165209031991074035a4200b05000448000b556a00c40c11000c0006044200806411000118170360500c1c03500b203006400030501035203843d90317615140d6410580f101400d01446000c81c82400304640464426240d601e0b4251080b1441c04100b900c45800104985c13191341e507040780003c410480302ca016448000c205480c8085030040c00b90700c145003132258039035040c0d026060400009400d290180010201c80503103202c070001c01150348607140c04009018100d0b00c60405402d070880315400380e103400700041c40340070002c0b4403a0751440c0c0342c1010b004402070701d005800c40341001041414900b20716103407078cc8113000318820070000904203542140313502030300c10800b0070900340844400215220303150a04001c0c1d215904c030252659030f030b0701c03040180c4404c040030100c41c20760341c0391404014820001104881c0960b00405a101c07024041042e80c1e6507444121800030b402c03d070700100c5d801c0c5601064101c014000c40081c008210100041d02003001c0324049642000726401516620055081c040b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 519691816 1250 519690566 519690569
    0x30f020a081501020a0605090c010806010f02030f0a030b1f180302060409090f0c0f08072c090c280b07050a12021501060216080c0f011407022206 64
    0x444194146112588058100345004064964010388590801007070780c804e0014011560340601c040040d81000084180d99102007001140450704c08008a1385039070060450249808541e0f00075480c00b0401d0196500c250800d1100b40c061640300e540682a545d1062a019004a060a001ca103071060482e0300034501b06c4945219203050480100500260700c0c1e1108035000d0700c02c00640421300e0061440c1810741030038000d0029181c5821024042660300d4a05203d03011038001c9012681d81c00e4071441c0ca50f80c400f410f8500704003001040214814003205800e48950706c00c0400e4281c90704420084003156140704890000040d4880c803201198803e40c02e600709501400c040d0a41da400c3c131415a03591a0303156103030400a02980c0c030030300c440b4103101d10800201007000010758941d103603035a4600300070355500340003503010304549900d0310041140d80000881c4802404003c10b802d1240c1d091030015100e41d040204071040340c860400c03016000d130710345211040c40c84d506419801449071990b0075001c103d8074903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 519693066 1250 519691816 519691841
    0x1020309011a0d0209190204030b010801060602150406050711010c090503011107020a0501080a061a070209090c101407050d09030c0e0103051b040f1a0a060809031204080c030f090103 80
    0x10805205141d00c80f0070045a0340741d415074891802c1c0c1c5404001030920b41b03034004580d41c4140001000310800003440e0740c66040390311400c005d208040d01e0740700c00d0340c45d110800381c40c02003d100140000c0c081512600304580003443c40c101414040120500d9500b560402c0c1c03040c5020500b400001c02c503905091203103100d000707a00030040d8146181c0da400500380361042d11032141000708140124041c40c1d425072107140105190300c928032201403101100d44e260340152100341e00c6403641c2c80004044000c0032988180c507200042c40e940c1c1f81d0521101c281d802c0400700358504e104c490300348807205c0082e81c1040020917030b40c0d05440302c64020345140390a1140d400c6a0b0081c8000582c1c00c801000000c60000d0b103550800c03008403c82051800351800b046c0103000d4410f180012506000840081707001500d420310801d402030781c00343e0f483c03922100181c600507030a4510b44841c0d44208900c00b03501020144039600203104e032002c1d40c40c007000c228a66245800115040c0d071a9240050410380035030301803007840d0303203000e5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 519694316 1250 519693066 519693101
    0x2b0c09080f061312140c0606010905010305090a02060d110c16080f2808031504050c210a06030c030b24030a030c03050c01020403083c071109090102030901 68
    0x105103900302c0703c0e0001054014001c000d01c0f00c991000500920712030701c1c84032000c8240d589030302044000a07a1a041620580d0119962210111301c1c0e521034020303107106458041c0100101d804603400e120b130a0f071084c0019440c80d651018501d2044c00504000c05101c148000200541501c0841207901444540c0c841c00243c5d205490041198001007600c954811406402c1c030603d0081301105101400050002095000300104111a00c1040d1300c3e00000040e00b65410020365a0700f40710b2594601c509881c440440150001400384c080314959030507841980c4407004107000d580e07a9516003040400f0740003207034440b01180c1004001c0c031048035869500228040d1002c0440d018001007601d940840c880030f420442e10060820625004904a80810414100031944c0d203590313007800c1030305400080203002d0681a0400d120300854024011020b082c07a40c40480340d41200c0201c40c4103c5070310103902140c003015201c0881e005aa1007203507081c8030b400c01d140056603a1615240f450b003103840c803685c034003101d1b503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 519695566 1250 519694316 519694321
    0x2120a1a010f0305092d011a06070206090a03020d080a020d0921020d170901030b0f0603010501081b030103121101050c09060a2705120a082b0c09080f06 67
    0x20b0340320900410902203410002001e44449480d1420000103e4130700c0488154141c0c800e007802c50013070825120380700d02802009000d0103010310080024480300001d60004050001e60098504280149000780740249400540d07940d0750701250301c99400c100c00340e80c0301402064005009406200d80c141c00362843c54a41c100b1401c2003d100a440480045100980c03003440c3d9004c11510781100c21a60540c0000d400100c025810044040c1c0c1c2c1d0248403458006800c0c2440603800381401c05031070711041c01c028101800d6a00b0030004496486d002094202001100100001904100720003503002e940034514030303046524500000303480d02944505600c035a80c034150801c134291040d6416a00b2070401100e5241d564070200804559207280c034048500440c0c0c0b024410034624414000c079a048540c281d800c810a4969011034640b030700850000507104003400c07c4102400f45040c2aa6440d250fa18a4041261981c5014000440358405400350100d2000d000a200f0400104141030080703503810001d20403417 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 519696816 1250 519695566 519695569
    0x603030806011b021c020102010209040e01270b010e0702030d02070f06110a0c12050408070b0d051806040303020702060d0207030c06050115020c06091807030501180e03160302010f02120a1a 83
    0x80030002c552040c004410030b03417241160710030340446008900042c002c0c4140b20111002c42d000340203610600a0030745040c14625801c1c007000c019080d42e0758104502499585c0b9100710000048401030004085000c1000305825181c1d00b031000c0c0903814040c21410f0008805407030080c3c12140b05010704010000184500018994420b0520b244030b940400c000ca641444441c003501d250049802c00e0b07803213020f8060080394804d900400740c080f0780e900030700501407030b1100300c1801303500400b25801075210780042002402280c044d070000c2402c1e0744050401407414000c2c030032280803a0081c00c1c0440c0000c92040585041c012035004a50250060700900800e034011811701030b54400340d14404078040e240c0480c1c00c543c290307181400800f801c030714405489014904040f008000303000c00d0081d044061440f04040b81c1d82c0310244074000518888600451800c003c195140545640d416012411503480302aa40100d14050014040f008841840301d41241081c6070322400341c847d00301c80318100d090004250b1019 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 519698066 1250 519696816 519696829
    0xb0103180f110301021c0c0503041a09070306050f06030d02010b06091c0501060b1315050d05040501110c070807080102031b0a0903021804110a0501050a0f020f010603030806011b02 79
    0x1400c1c1d100e0400e00d031a511a01c2c0c402c1224494500c0194035520118443c9012500700001c1d6980042c010310030418205500c4080c3c445000c00e45014040000041600b50001c2c0186100c41c3c014042e07000303c2d1042540e07aa00d07a4107031002110300d0489a0401001c3c46914202007150b10000340300307070000b8001000d0070f034080740c034601601d0080751040c0079030381803a41c0301ca2100b4108800300382c006e0001d1085a13102c0910007000d601c42e080c3d090001c04010000684082c49c13100040c681101c44e600d65261207400c00b18540606000342c4142c07415580c0704c44400000700385000030a00c2001540107070200c185441c00490404950384d001c02080e900420030091207408140003066440324000340d0545070341c0208021564008181c100035001010b41c1d0b03407182661b6a68041c0ea1140d4030507410054004945030501c80540b29610600380414410321071581090300521070040d580300b89204940312a04502246401e44126500590208880398103000042d45d01001e56289000700c0c00d0b0780400414240c4c0030500d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 519699316 1250 519698066 519698111
    0x606090b0f090411040903030b0406080a0b01150e12010b030a0c080d02030c07060c0f06020d0b0f0d0201080a1d100203011703030103210507080c060f0106030e03070210090302060c010605040b0103 86
    0x8140d561b506207008250003680038118a107005402003081d1615003100f103940303070b070070400903142c0781c24003c000200c0b11075103250b40300c44040c0c66031500808203029050103c920107062403e8215502e03020f4000780d948041005a42c60341c020340e25201c0d000d180ca4030b240d0030b00403000c8990045400400a1301060b00c00002d6020403030f011450000285800f608201602c0841950300a204d68000200040464120340100310340c2f01044a4101d00c050315142004000e404145000307010411420010310190b0b00c1e6840840008081452011992007551541c1c0c1840000342c0d00b042c0143d40440184680f40e4102d120794a501c00c004003c40c0f41d541980c813505580e9140300390301d0100c2c0007403040c2250107903c907000740d50b001c3d070707001104c1c903140c060100d5000c5d1510402c69400c0e0803003410030000070b802e078401e00800080c201c10401462520b030b015024407002c0091340e1034030000e00800340000030043c2c80301802801ca80001d4400080e0031410301c0304000039a44a030100c2030400d810b140c04c0c030380800c0100346030a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 519700566 1250 519699316 519699319
    0x201020a110a0e0f0103050c062d0c0a03020f3a0203040504020408030703030c03020f0403020402090a0302030d020304060f02121b010b1e010201050606070812070c0606090b0f090411 80
    0x18241c6800180003216540007a0183c071904028400004101c3c0d01c0541602c1c030940070303205069070020901c299030081c2c602105402045805d8101c0c4c10040004d01c19140301c90720703030103490103036174403c16883c252801a00f200181e20900c0c14002110003400500703815810201c1d10060380321703a07407490380110420a040c84180a441600c0100b0b4500030411900100700c0604155252565000c106072a900310240a901090411540c4040786100c2d200711100c4e08540803810f030505085809000082d0840c0106640008613980040301503a02002240f03119a0994011a030300d600b00b2100501c4888030f0b00c0d440c001c1d540524154060038001400750342041a14044100d10440e0b80d0040c6409030401810382c1d500500c3d42500e44590032510340002d02d6046080c1c0007032100d40c40309411301c2024400c446000e001c11005000481d500c00320121103d8101165251a00703468005889200031200300364000c5200342e82d60050001542031148200c982d2003411140a42940303060b484060b008010005c005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 519701816 1250 519700566 519700583
    0xa050103081207050721030c030c0f05090103140124020c011b0218040c080717030406080402030a14070f05060a0c03080915010311030c1207090906060801020a0305010911070201020a 80
    0x3d403030901c1001a0740070160000c0c034039509001c0408508168080e0301c2c3d512400039003031201c44012207002c2d005a0603015050341d140010a6051074003182e850304943c2c1e001c1c1c1019110800c0314683d021000703080b4080c01a40302c030f1030041d88860258400002124042c00199004040381085903a0070404901c0c0300307065008c1c1002250307040d1001860f1042c02c00350700d078480e02c0700c0d10600c018001418040800c1c4e031000411504042c0d194500340707198202c0c403a84408558001c1200388280e0380310b402e42a800c54409003c4030049907099030340380400300340f1116080080d4080c041c1081084031806080d80102030a5600c90b01c1c180c1c0035000107082e2000180c0103800c0c80b0b0030201003414403000304070117038240003400d00d10300843d6108e01c0d0a0740c85500c620240c41c400d1190503042001450504042c0030903040440040c419140303407415803805070540d410141c0e04955220300024056000380024030342140301ea40c0c000f92030340c1040e4000c4100c4104600e01460694140011070042c0d80004030000f0094002040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 519703066 1250 519701816 519701821
    0xf0307110f0c19081b0111151308121905010b0304020f1002030906180424140102011104060203070b0a23060619080405120304380114090a0501030812 66
    0x203c503e0f6580c55002d81321500c2110080410202004008640030300243d82ea2a20f5500100800d50344641801a60240b11041004503034030030341540700e1201440c410300805080c01a03c0d025911044012500c6042442c44412803c44150041c0300e110f000d080342e00740c030f5415424560085408058540c4445000d04810740c501d09002c0d00800c103071141500020a80ca6962410508044501c103166540031b000324100f100f0408842c0a0000900707100742542c0e40fa00c0c000e80707041c14032214501e4080b0418195540c4d15081c6105070240c1d8001e1001c0d00681d001980c0c2c507030b918034200c820120000d18000d600752500c158004c183c511203140980252907858507103e25254a000590948184000301c1d2100f03031814030001015070416841131099000d841030b1081d46000964211b90743c8401c440040044002c003010320102502e040491038440070101030799600709007182140360902c13000c1c1c008502c4000e880030420341d24130b000c0d0140e030341c0454010001d0040354556a21030600b4000c0001280903600c00400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 519704316 1250 519703066 519703099
    0xe010c05030c1803010c09090e07051c1103060c1801020a021c02040b0904050601061706010e10120f021e0403080412020d060603080d0f02030403140d020d020f0307110f0c 75
    0x40032036002c03c02030081254400c1010040c08010b01e0f44107920926060a00d403881c40800820901d04841e0068071008000a00c509640480582800d084540300780100384207502c0e4a081040344d106d00e5031059160380d078403810f0b43c210406407507050313440d0304550064400200603101c0740b40001000c9844051040203020a01c0050040c040803006d06401602a07010041070090018083c1d0403184903442e00e42c0c0c0d13408411100001070710100d403035038081000d0324900c001d1400c1000192419441d0b510303081032910307140c40e20031064034601107080b401140c01140c0207040c0200141c049281c100c1d00c582d22481c241c5107554442a90140b8032810480032a41308142c000d544a8842a50200760f0006040100070b40f80d00d054041a0042d8800110b031514000c8c4850561001c4d01c00c490150350103455402c400d43c0b00d606a032550b0f6005400f22400d2a8084c0300c130f041710900074000742c403902540194060312441c240c00010705070440314010054a5100800c4c1e250200b40118582148403000d80d035880d5640184c80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 519705566 1250 519704316 519704347
    0x1080a020903011b14180d021302220f050904080c0c10020304030506010b040e060d0201121404110303030103081207020c060a200607170a0621060e010c05030c 70
    0x1450140c15508140340c030f1820100d00c60783e4000d0000c0c03544991605c400050300e5038016028a4052904030041e0380f403418001d24161100080300383c402020141c620401001e0b20040e85c01014070f50349200c2c0500308500c40309464030341110250412400c1041c2d000e10304800645620030140001c0d00c010400240070021401c01c1c00460071840c0003070003030700100744240c400070340d280d10074801a5031501501001140d1903052001321030403610f9941c203074072081d103c002c200650441090400c0b0f041c02480f00e16040c1c21406805002c0c584034040314110341d50704d4207003004081e907800e50344032620a4200300018400500c44070284c966040512000085030354075400140d10f85050407176150b40c00300c0c0201d00489d40c150320021b201c0030072007044c072500c440780d03034030310003903503204c0c000d641d504080380000d410310407407000700240c9031350001024801040f41a903841c0981d40f400c140b0141059103031b000c0e50b60f00043c09080d0050000d09918800200f00d100c070407410040542c00050300102d0b08078000550b05440c0310158 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 519706816 1250 519705566 519705577
    0xc120c06040608011a0f250b100303110c0a2309280c080c0906070f06051e0403020601140d050d0e0f0301020c0a1b030b131505070e01080a02 62
    0xd0305481d034540d00d03400c018041a2007403160304140e00c00b04180710f0345014120705039440e158400c00301c0c9080a00c05118804203150b803000300110001803c8410021404510800b406140113011655082e815400c0040c10f0459412a144040c0e12200c0031900f2034407000800400c898040d040400c020142c01c02039a2000041c003600c2e41c0c02003229050291b2004ca80004d407046002c014035405595810201c6807094070f801d81e10b0640400c078ac00000270030443c0710500600080600030301103464010241d5030743c100748040b00f0040d503202d62780304200020410144070840303019003030384070050b032503e00f50350002d641e0641402500307460021000f03030f4012030b02d0702c08038013900355071200039a00180c3c0854001003440c001da02806104454489505030141010b10032150a4004c0c4005480c1e07125443d1030300c04212a20040c140f003201c840f60400404100c07490340711800b505407a010300c60200d6580c100118680d0303c191000c0ca2280c90681809800f581000100c1041d450a0a006000c0c2c3e4440807440001d0240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 519708066 1250 519706816 519706819
    0x60524091c060609140603060a0203100308070602040608010b272209120f0e060306010e0307120c0906060c170412030507120807020a0f0c181d01020c0c120c 69
    0x80018008000c2c040d00300f4411340340c02d5070041041d804030480364000e484094a6103501500442e0200e034441115800a40d80400e48200d034610050f9643d4952800e03502190040c3c0d40568003080170700c0503030f520900883c018880c030440c0909101c14182494040064905103001d240040402145c031900c03004503500e10aa40c00418420701112a820b034405040000001c4035a41c0c40d406060006c1402410100f0381d100b10781c1d80301e14003800001d00384455580702400c41814485003522885e40355604000050140031451100099520207107814a070354606600001210350804000f4840107500404404090381c002080503000326108408100030700c50354000f00160060200220180350b0008000c1422620030000d010402c0761340c81d4112903820060720380d01c005030000014030010500c4500b0710003006000b2a1003514041e0341e11407560070351b034640c0080c0b40c044e40c4940b40b4600c4e01c0d00840b01c00380cde5603904800075440c003250701c034605032611504446103200315500030030881c000c5001c0011104c2c8600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 519709316 1250 519708066 519708109
    0x12040c030f08030403030b030f07051c050307240207030e01050304021311040614094f0c0206150d110607060510120b0109020304030509031e0106052409 67
    0x220307810144201d900844050700420700700746047c6601e08001a09014a80082c00504881420203080184010000741f0011502000803010001b10301e041c4006d25460303104800c4c603800d0104e903145230950500c101c510020039030310504c071070004a034100002650024003403805c0e030780e665513a10001d031820305001c0b203802800d8681030461a420b101403000700240c030515111441d00d00c0104001039001d10500c111f554005041510700381958034041203514020002500c07038100b09036040c05510358900540700000580e0500c400c942120078492081d16902503140c4085e054034603180d203521128500644103a401410621400014020700c00a0501400401040303540e8072038840c10400060724003640c105280031002440014034803202c1c1011065568841349004080c0e20701310a41d002908010001da00780441040303401c42aa4003406050514260143d0085545102c184030f117084074900d40003140500d007640013240101584906940320441d082d5003241e40d0301400c8022075403960079500440001d14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 519710566 1250 519709316 519709343
    0x406051614061902040b0714030f0c070e180c01080901090602040f050910080a080306042d06090608100c0509061b1006030206030f0a06120b180c030312040c03 70
    0x500480c0e8140500c1500388400041803503d00d01000f00e128a200715090b0b80d80130002c800024105d82c1e44d4240030001d0b07400b03032801c01d0141d40e140c02040d0301001488080c0e41107400d041c4005020b030001190407600d00c14001c0007600e18102001d40da0959800c034036041c002c0d5000080c1100000750800d0402e550b01a41c1951202d5407605422030595842c007403a44209403c800207503d080d50030340d10008580c107510042c001845c40d47c88400f610380c005003407240c03c41e8540f1208401855040380190541c0d80864002469020035480602100d00c2600035803007140c01e00504014080d000215015075100038803000454900003201903030701c1e2040354442d03508180086075403440030f1081c4880701000c20f00364051b24064404903620000316009408029072100c01403002c2043c0c2d82003071141a030300500d0307060f0000e44552200c02c2207400c02038074041211200540030402407100014410002c41d010044001c16070038405c0c0c00065241d000d200030f4010000d00c200c001a0604c924048680d00550704140100c0608 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 519711816 1250 519710566 519710603
    0xd03081b042405090604090b01050403080403211d0609040905071503060f0b04030f0501060905131e0f020d060f231003031d030109050d02030901091203020304060516 73
    0x1e02c600000e2401101490420510a80c0039900715001404010f0002c0e2410341880c56240042c000c00155904200d1300b80404000549100b005101a50154054042d801e01100001800b0103002509408000c2042d41c0f0351803203001445030002c03203001100d02075258032a0001150081600f860b028000b84035441c00000c0050383c6a0004c0e001070f401c3d59040c00401d40740c4010031110b000c00d00c181c1c0300f550820003003000410100c251418210388250f00100d040e5540340141d200b624815107008004515108906081202e02e0b50164500d40760441c00148403071054aa000c015411444041c0c05400d00500200821845a20004901c4403030b07401001440c600c640303403c01918410b40c3c40b040d1502d8010205000300e00d400c0305030f0110b80e4035503110401180000c50b205241c009003403006402d036480b41141d9001600501100940200e1036000b151900c1c25100010a238100991090302109074141244001c81c1d800710440d002e803085401e00d40d59925641e04040300715071050102a15402c452a88903200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 519713066 1250 519711816 519711839
    0x30c100e01080a050705040b030403031401141305060f0402070302071203090905091b060c0a2004060b0c03180a0302030d0f0201110901120e01180b0f0c090d03081b04 73
    0x1003100307a0720000c15558400b0000d0480b40d0650b840d1780030642c14803040142c0c00506009541c010b109180216102455003500c1c1c000d1003082e0050f005c117134100e0451607500d00b8251070460031284c1e8420248200d0410801041a8070318400406014a4000442c00d040c18000c014043c02030192a0044900c1c00c040d040040c50200d080c00b0f5800d88504010100d20340801c00201801e0b40d800300b840440e08599080c04010f544ea00106114003d170242c04181e4000c616406500c3d03004141d443c4840620340d008808110488003150420b07510620140486802c442c00001030303580060340900b040e0441c241c0c500001d40c44800e40d0b40020b43c5881600c0c820148268043d40300009102160000e001101c0b00e0030340c880c101d00aa603212800104203000032100050301e5040030741c40e503902000000d0360340d0703405101176020741500c0020764030080d2880074080503030b075000005030b4444035800400381003d224000007039000303078034174005810861740c0b8012a500424500304148010381e0510003c2d0740e5940c80c40342c81d21 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 519714316 1250 519713066 519713087
    0xa060302041805010e07210c05030103050c010c030207120609080403050309030c1002120f0d02160302060f0601050702130e030309240c03040b0c0c07060e2103030c09030c10 76
    0x4122540c0b220004070720103034014031381070300c40d801ca010f800d541c0c9921003200c0b001400d010320314140031510080c000c800081d01c200300050030039960351982c0b5070640c1000c41c070b802c40104d103003410080c40d01500408250f01051030300a45d0101110780f0707044207090610a01401c4e450a0140c00342c00001030010401c90700000401a40505406450052200d0000c014409000011400268002030f40002101511800401004035a0400d55052a8521030601e0490300085050342c0ca900640240c1001e05804120043d07001e00e03240c558000e185030610000313105010752030b0024058030700d40c0858031030b1482c41e800141040f910f50701203075140e240c01801c0d1a5151003034440e00c000000c4001440c424040801c01c1c01d03100d000e500848503d50b80b260b50710b205401000400700c082c41e00c414820149641d5040c0140c000038441c80e81d8100640014400b00042540c070300054031860b03500c644c07107040c81c80740210559a000b200041c0168584414030042820210b071310601c141d014410b541c3c092140c2e03801061910 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 519715566 1250 519714316 519714329
    0x1020f1c050a0e0d0c02040609111b031905070218070801170606060909090a0b01122003070e1506030405010504060606020307030c0f14030c010c0210060e04080a09050a06030204 78
    0x102070340380e07411039004680811a820185400907402c0484c50340c02208050071041c4090700000f02966500686411900c8040440c900020000342c00a003030000017091508081c07d440140d4a01103454240b50440700f0a40607503030a008010441000390754030802c0022403c03000b5188054145010b04d00100035031400d0003010300e000b0340e0106010340c2c000001240c82c840d60340a84994581000b860030000b0741000105001d009208074444200001d0015100c43e00170904408003400c000440d20700307030f1440e490325250590111400c0c0c40908559800181000484044414014458171071ba61415207800001203900c0d00050300000340000c0050550105100300c0c02480208005900c4040890316072050000240000d950241d408000c035046424130241c0c213108096907001444080380003400c58001c00f0401032140d40d202e089810a64041c8507070003150b4084a001c03c041070411214541085000d00003505000001c00c9000245006901030303000340c44001c1c14001d80565500300207010394498010070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 519716816 1250 519715566 519715571
    0x1b0f0b090c040e160302061e0c0f010b0d05190305040915030c121703090c0d2a15050906210a0b010c0c09021602042c0601030506071101020f1c 63
    0x10208044081207043e1000d01c0300c044852813a00c3e607000c214503500501d00c00d4000c40d804203001d4503072203410402490b4544410002d4850360408242c0d0a003154401d241003402004441441d01c0003510101710b120503108064a0803028820600f02100d450050741c00c410105403800c0054659000f103c01c010044038402c0d07a007076040640302c0789011040c19007240c000b8515101c00080d91840c80c55000070b0f5600071984411900c0d0584948005001108030403401e50b40782400f030845c80b21a0700501809a8844d02c82c2c207190002600c1c3c403400708841942121a6001c211012500e24001d5507108101c80390004010245e5100d8061080390365290841a2262504e951a102030502a94003c502411a1581000c0c2c88028185412540f0707020f984082c20350802d00041a0508005950300d10804898852140d40340e04944008001040d02c0c0380203000784802e5034458001000001c0c800601c0c144d02159514091180162510809000e4001c1d41034001c8004000700701c0c82c003420444e0400208444844109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 519718066 1250 519716816 519716831
    0x901140106051b07061407080f0403080711040c0f030b01090509070305090d0f0e1309021809010c11070312110a03021c0f0f1809020c06041703071b0f0b090c04 70
    0x3c2e994031070051103448042080722500300003181d5240040c151042c014040e25290900074616645294810f410842d60726501107251000e104144084180300e1200356003c01c0038440b08a0003600c81d001d00c140302820180c03144401034440e445445c20b407000b807801402201c11402e0040c40a17002c0c0804440c2c2251501c1004000e000c0244030340a20a0b1100a030780703450048184200c240b0014554800d05030380368a0b1101c21a0340181c492900304040c6035003600113090343d0306081480500751010808981c0412024145500182e04003043c2070b801c0300d500443e00b0b010148402c03420758a07492110b1140d58a07024250380328040c1500401c082c0303a4411020514801d2810b81c900590b80c18681d280c51900044000782a4040c09002c5c565400740d06c502c001190714810ba0304d0403500160b074420340c54040503030403040600040064600c162881d44564686042c194940b444000345000d03600c0b000004203400c40d86501003800540182c4a8582d50000c0718601c0c1858040710007651069068081030003186400c02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 519719316 1250 519718066 519718117
    0x10902030708010f2007020904230706120614240a17221104110711040f0e1c03110301031101090e0903040504051e010e151e0603090114010605 63
    0x1140700608005182c1641480b61b41c0e000d103e0307c060010804c0710003910758112801c40c1a511010540e0524503c00140035680c201280103200000b501c00d1402454102a02805021042069044204401d9810f200c0a032198031240710354000340040750903000000507100740042d034007010882190984540b400c80c16112028110308800c001c80554217022803064035030700010801180100e014200400210b10200391050705211940807070002c484076418282ca080c135038240742c012550100041c080400054040e044500d403562008202c03034905c00640e0210b05000c40c06584406080c001560000382c807581c507498500c0881881c0300000c0d003c54411000050240741c1100514891040e01019508061070002840007600015010180d400c206000302c04407080d034012014020011910b44002c54140321950b41344000c03040600c94010300109099101d2454100a003040d0380c0000c0e103009039642c0d62040c069005269007980d20404254160001070020f51107009854009222018540002100c00707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 519720566 1250 519719316 519719351
    0xd1808220605090f01030203040c0e27030a0203040b0a02101407020c0d0302101e09030302091201020a050405090411040c0e03010c030626101103010f080c0a17010902030708010f 78
    0x10403d41d8040903c0a011107103501c80d030003540d0005d120b1080440003c0c5c07100e10504020200f110014507aa82507420708078140342e18414a5850a1010065131401001500094070382c0710360b001c0e01e101c102002440c03082040c03007040030031500b000c07052040240304074486d070b8112402d1040c1c0e02480107204800b03c44260b85441c0c400b10700841e03030603001420344034a410085800350028461000407901e007a54041550700b03440c000d01201910035500140d03107800210030400c1c0d4850303042201846a1044c40303076045c47c81d00310086a080e00e00807205851542e5403841c00d6032010302380155040e0000d0400d98160b10b055003250300080358060031030081c0700d44030207a0405c80807241c01f481403c2d900c0e07e04031142c7c441c1403144259130703e0441c0c1c10b4003950008421186150b05499180300310840c0c21100000412002074022424030246c6087e20162051604420008200d445e1502031061004110360040c1c00b0003800354041c1c624107a020781039603892951490003030b0007002c1040ca460400d9080c2010b5500c0b081029 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 519721816 1250 519720566 519720577
    0xe0c0403060e032802120315180c0f0f090d0c09060512060103080c0f0a0c05030c011e0810120605061302040f09050907090914210d1808220605 63
    0x30103d04580c891800204c1c860607589003903000b114041c5a1302c000c004025485282c1701511020410489400c0c4400b80035540502c9004d54881c10901045000c400b003250402003400303034050746401010071190040c5c03080d0616070340d114110140090401101030b03004400c441010a00300001e5603a40300b400b180f040b5000702081640c00c41300040c0700180755034014200e452078120883d620398003035420307051a000404000b42d504185c543d00402092030b00700f000c502220801e190141600e0f18086540460905110340d46051040c040d000590940060010000a0031285403940b9088000d0a0140c02004180c4080740264803444022001e54070130700031901110400d0741c40300040761400741d01000815002d0b200441c1801400d800041c07150311401130a0760180100c200c1248801524502441c020398070291950a054076104102c201004005a40c51110055004204c260700001050703450002514010440c0001184914080307095225200d0f144008828106001e51511820342c0e450145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 519723066 1250 519721816 519721837
    0x80c04060905281818120e030c090c0d0522260f090f1206011a120108070312030912050d150b0a02070608010311090c040e0c0403060e03 60
    0x84000030032980c10305442c5030100750244121001c1c882604000c1c14084006503202d088150803a119044c0720a90600c9008404400000c0148000c10240d948105120501440f00c06100000c0c105040c20345091000f2826104010134000092410501070a260b0300a000c109a0080c609800200d40070380c0c6554100780710081400820004c50300c0c1c4d8955803091004450b52170071584060b60038130303c003007001e0103441d06d1303003000c40b80685910094051010312031150408a1145a091028246a9001041c200e042d00c00c4d80400003884901046020042e116105207182c440c0014000002d140c1c0000c42c81c001501e11030412190b01d0101c81038100c09031401444003500001d8040d01c0450030314010300050400041609010030b20484604802080c044907922003440904000381e2100520340c1030215201820117070500c80b80550554594116060b00b200e000c41c000c0f040040403644a000300010780e0014502c181000302c0c0780c500100d141e50305410504c4100e9000e420074a180461a00100544991640 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 519724316 1250 519723066 519723077
    0x705060301150507051009151416020309060408011413030f0e120109230102130e0c090904140d1d01120b03121305040203040f061a0a090c080c0406 65
    0x3400c104040107094815500c05028003003151000254091020882450002c06c0019007401707075042c000c20000d00b60381d900e401e85240c40750060355500e20240807500304001d00081451048601c50503407451145146440c1d1203030b00428000f88100054002c0050b1303032420800780c0201c0d101e2401964540703031030b014010f0124408034500c045480c80741d0741c0703414a008000c01940008146840040c21100c2c1d1810903074858000750200c0040303000c900c8006406904400085280803c2103031800382c00002340c000d2050701012680031a0740505024203a500444c0e00900c03010307080c1030501e00301041580ae4000780c80c850054207102034005000b010300c0d80c086d40c1c40d0882501b100e8458001100d4901103890101010b5654104825958400b048440c102c0042c5460301c0b50b071801005121254505681d120520460040003080000341a02c410344042603400400491b2006030b40fa400a01c8038541941c1940051080c0d000040c40c6016421054600c503850300e5098280d00c40c140300c690207104034014200441d6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 519725566 1250 519724316 519724319
    0x20d030e06130e150319020906060d050705030429070c020a1502070f0911040b070f050118200f060c07090603050309030d0302040501090911071713080705060301 71
    0x9000e45000352a240d4010302051402207226000c841140712904060680c84203801041070b00d540c4886400b0f80500c04400400100381c10090700d003140b0243c0c2d50024050450b10010400940b01c0d882924003141100000340298602100001c0884c3c20448090302c01c95484100300c0500681e840c42d036455071005034082c100603691900c06503030f10260141e08980009900d00b00040030700e640000583e1040b200d17405010003d00c2c101c07400d140366a40740c014114807450659204140d00c03001044600710b92541c004a03490344d14900780082d020420007000b420550820300340101c20400030300000985c42c404c2d10426044c88181c1c48020000c191544c601ea00240440801d501d10314059003d050391407ca10101c414407034840b100442503d038142c3c0110383c540c0c80803d460301c80e460284540b811560341c80c6402c500b0b062516000800c0260030380302d000c007107541c2d48800b43c012f030f0a10301c12180c01540100e01100c000c0d01c2c1c0800c5c19000c4d40480103d14581e84c101c00c0c0456806004200c800443e00f0003050a41943d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 519726816 1250 519725566 519725573
    0x330402041a0409050d1101060e011502070803030109090b01080604050a020f0d0204150501171302100915110f210307030905191e080d0f020412140c01020604020d 71
    0x18907107040d41c00c1d9525280410003940c1c0d41c580c01402101ca20840107802100b050200240c40d00e0488481200306904001003031000005c40022141120740014901c400c50182e001c2c00c1e410319015410004550000100100c0c09a0090700001103e81c07040a06800360f0f0b07640c15071107880d880103440050098101c410070310090702d82120541001c400040044110101560000c2d013110001420010111041e1a04000a41e0030204441403000c981406c142540703440c3c1c41c508080207413060020f1250204011b5000060f20444a03180500740c082d0482c404090700d128050001c1d40c005050315214403c1464043c0c12507000314000c0200c3d40850603001100548a0008000e43c000401c9002007656540c0344401084040001454000c42485d0080c00e110a07421b041d07401c2c0325280b09007044070f0340c501c00800019454a048850340701702d800c400241603140fa654000a0302c201c0d403040c0c5544640600070400e201a03c02c02245140551003100e881903014401a0303100c4104490281d0311040c000340c5040030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 519728066 1250 519726816 519726821
    0x1a0901050d11160c030b060d0201020601030305070317070305310b090109020d3503010e0709151206050405010501051905040519031e02060d020d1d33040204 69
    0x8003803140c1c40c0e03a00f040600d0040032100d82c074501c0241c8041640c22030800c1400426001c0c19003000c0241c503036060614103900040e668040c18072004041200002d01d40081c984030f00f0154096400d400b00b003500c60b082042d402405083d0903250540818441c105401c40322800c1e0724a03042c58504030300082c0100c0401e843d24400d801006042c0307145552580b5440e801651100c2c4030756005849294551409000b5281d089102f02c14104d26401141c051007144000c0603144060b00c0c1100d107185c10b03240c070303135660341400300e4251300182d1080034600081c6100c41c1005400c101d0b0625101100b0000b0002e00f6901c10400058440c00e114182c08540208114010032404064021a9200394206189410b17500e4000ca50a16003c0200015900b0610000c1c810010041442a00c81800700001c05c2c4442007500010414803c1c441d05e000d51590004144c0e440301f841e0b82200142c034035202c0d00342c41c1c803120041e550b5488120940c40b140d400e0a0700886600000f10844240540c1030703444401c030045035aa0b9003031100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 519729316 1250 519728066 519728081
    0xe0906040b06040b24030106090806010503030f090102150c0405190e070c050312040b060406050d1109070309140f070602061302060f1c060608060303092b0f0302071a0901050d 77
    0x4000125003102c03160b00c09034100d0405c405120b00003440e40c0758035240d0000c11080281d041750303180790070400c01004583d40010980b1846818084156071382c0d104200181c1c6400010505983d0304c85040042044070101d1801600440350181c60185282d500700c3c2c100d100a183c0d0f4010540d80b50304a002003030456203c1e1400c40102c81c4a03a045038500301c2c1401c4180342400d0111022038070700b0008000c200316824903001c0c3c40002c0100b6118a160400280e9500d451402d0400c860b5000300ac2010014468a02c40d0304440000d5422101ca41c2407052003250268503011040401544c038030466000083c0c140c80014094402c410800701440e40c061715500b007250340e52242400d02e1403410107110750a0010003080c21030680e0002c800001900515240b0068854440140500c0c80703904103000449903a19080c4180300f9240e81e400c0740704183d04108140340016210400054030300d900b000c00d03080806800103001c10940b410030b400d90903441407070290244540301d83c105450000340180684181d0200e40d070007106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 519730566 1250 519729316 519729319
    0xb04020403050613141c0215040503030609060402090a180b010c0302060a0f14090307030801060503130b0c1e030f01080604020d0b07020709020c01060905100821090603100e0906040b06040b 83
    0x150f4005c420303040c61401620003d52221008400c16405100e40c040200c0d260500300c020703240011f4601926220f481e03000080c40030740a00000000030740b49540e42e134111111248001d203011907440c2c4034440c030012031164241404417145400f003544000c0d8080e40295504561560013800c2a0307039041000005800c045462000f80360b15400542c68031207954012074812021000110b403103030014240200714400c1030344281d003408002c0090120000d800600100c1c0240c0001c9450704a403103100848555109e01102031811030f04d4441282d4550002c400114015801c9140101c01c5903250388070945c03507d00641c2e00070f40c403020241c92a800501c107503645552080c001e0050303c2040759078440d204140d03401034910382801d943d1200c007480034030a180301d9150002c0d9030528031410b0f40c7c00c1c80271061341c0d61411044e8030404441020301450171036a000c2220b20080d40036003030a8881c00c0c50101c25007809424025409001080d50004101840003e00030744110740205004501c0c4e1940010700000380502c1c0c0c0c856 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 519731816 1250 519730566 519730583
    0xc0f15092701060f02061b430b0a0b0303092803082508040902090310140f0a0c0225090603110418030e1309060504150b04020403050613 60
    0x104491074010307000780c000d02041e1540032940f00f038a8402410000300500d110034000084042d0241000c140007070320300ca40f120441400030b0740b0f00d540d10b0b40308001007003a41c42c4110b407440a0b0144000c039110128140c42d803140a003030180e6252081a90705440d80f034200309826a0081c4803a250507d000750145000c603101954800e000c9001caa0740d407520007500e41059841400000d14000c0707581210014924070b91101094502c03034061607450002d03074480c3d4420300310090380104501280d0764041c02000c0510104039402c02000600d10f0003c1f106240c2110900c2c00000c81c1400140c09100383d008000d1110640d501400611100100070038044502504c1010400910a000306900c403940c0f00d000040d6000303080f1440907401c000100710684950500303803000000c80000f40400640c200c0c2c502d1503a030400701e07071210551841b104600010080b910000c1e00041c2000e050109010340c02c0802da42104100c6c505000d640c4001c0244030603407207240b2004165038001000159420141c0c99406007040c4101c0f1b00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 519733066 1250 519731816 519731869
    0x8030d05040c1809121809020c010e0601031401050a02090105070b0a0204050d060b040501080d08040b09120418050a0b0a030f05030d0903022b050901050c100507020c0f1509 76
    0x603c40505001ca2440300080c2d9502c642c4070903c0040c00f1a00715080c410314021206050050020a02c4881031040010143d004940c01c2141c141c00e40042407408000002c0b1507440d0383d42c1c2403032110a0301c20000f00c0d00760351074000480c8000c2c1d410300031213403120010303150f09107042850b6540c803880030b400a10747c403c0b099081c0000308407a92030b180c0b20841c440c0200008250100141c0400049800680c4000c0e010f9110740c601549039608141c02c1c070361068024000490b2a1359100159040c10f40b2140720384043c03800040d000c83c014140070181c00e00d801c1d90900410940e03403030f0b50052007240c07800740d5410b40c09843c0000400015603402d110f0002e00b407040b802e4900f04195035000c0412b0340c60309503045001da001504981034001102181c0e0988001c002c0d00c0101404c40e640019000d449009034160400c071000490340c00e120ba04000300c12004034020000c1050380740030180251650600940503200f4003c114140e58035180c0350440802d201d050141c9145401564010407100030112404003000341c003000c16 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 519734316 1250 519733066 519733079
    0x1505010e010b090f130f0e010b09010608060105030a090c0f0303082a0a020703080c030423010e01032a0f0f03020c1005060d05060a05010306050601110714060f0d090512030108030d05040c 82
    0x10146c0c100d808a5000c29040c0c102880142941c03078a0418a00900e11200100143ca42c415802078000c2c03400e0900990b00c2d21759000e004090041e00f5070180070b407071110000180302c007411484132007240e0090b5600200c0c0e03103940340e0b0801d00740441103184800aa41c15528207000d446000141a03003121801240c0c2d80c9940c0381e0351b251040c2c011000b122aa0341012500b007101449080a4200002d01c40300c04400300c080001c00a8003400210305001e0406276034040c1d44010b1291a404581841c540003a924016594424001c1c0148001c004400014126035000c00c0c1e090300034001e6603900c80700800076000c0d010200ca82000100030007400f43d64803454840b0580d02081c0103011043c02080c1d03101c030210305503043d0b040c00002d6403400342015040000e200c0b040c08081d40046894000e0350a40c015042106400030300046250294030414003805a001038a03441c102500e0388032101191003801a10006900d00104040c40e0009200340019074104000d03a13828907800381d0010740d0051003202d005070115202d44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 519735566 1250 519734316 519734321
    0x203040906090212060a0303050409050a0204050429010203040b03010905071b050a0b01051203030609041506090b1302040608130302100e1f1104030b1509041505010e010b090f13 78
    0x500910300583d00003894140038001c13003902503000340d007a0b416a0805285540c0103100b841248541588280e4510200b468040d140e01140e00400b0018401e00c4088404200042c200440c2c29054510640003c0c41c403d86500100a490407505005148c1c0d08582c03901c0b0091003c2c1500400900400101e61001000703003814100127290303107019000503c00c0440e00d140110f44a90103803c01441804940c0c2e43c0c01c10000000122684480c044c1c9071040c140d02c41e4500b182d0b141000f801154402c0382000f1010441001e0340e4002404001d00320343c0000c0c15144030305004220704c40c40c098500042c80e19000100c08181401400c074916102c3d00c111920210082132510454181c82c41c03000d02c51300700b01142400200712200905220340c102c4020080d01400ca41084d10034416032000510f460b44060009610030282c504001511002a0805100f03103032074039020f010140098503c41c1581e01d0100045101c8007100c0b4254140c03666510380c1407a207001c210401c07000000c0c0700321103035105400c1c41c0700005262050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 519736816 1250 519735566 519735569
    0x22030e0d050a15060905010b0d0c0e0a090c1b02011e020a051f0e0f100c090b0309060402011b020307060e030102190206011403030f0d020912030712031d0d050a0203040906 75
    0x780f203210b0b2403540d031001a1055620300d6010658140c100b00061250042d400c0880b0300c00d41041200003103108210000b51a07007182c0380311080d03100d105d442d03000615041030782051a01d00920740da03028080c503a540da488401640c42c130010b0b000602080c61540400c400f03c1d0a405108080d004841000c491076440620b481840d14a1407680c0f0f81242c0104001c0c009070140e401424418000f5109441d80008041d40d204400304080f140c1d19124074104107018001d5004030090050444043d40c0d81c40e244800303036507551040d41c1c12400558200740508405050314854a12140d0003400f8000080c1f90890448048001c010403070f6065500304100110b0483c04e18488011001d180c000d86242c1d0314041101c40e8000d00c2c0f01d1080d0098104026200645100c1c804803038600110400068540306890f01240c001c080c030700611001484000f0340c4100344402070070008c903800100e0384c06112130b00e0513405c008495110f0320b030304000700d07800101c0985800703020b074001c5c0044400503c1281d04103a9280b0340700342501c201c2e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 519738066 1250 519736816 519736823
    0x1d070c060e01140903360a08032a2d0303071e03020403050c060f0c0601030f0b0c0403080318240108011b050304031803060f0b03010522030e0d050a 65
    0x444402814654081c010340d580640c420000e941000446020940180c0f10b81c044140b002d20f03941880864182c000304e0740c6d80300b00000303003416858549640401d9038035881500000e0300b20f001c1c001c5a0002110482c4407110000c0b0000c0580500180284400407000c0c10f55084900d81c21050b95100b40481c0030406148a801c0c542d541a000030340b044106100c081d821440c0f14100b50040009001051002a29520421003500e00fa075642c0204402007166000d6072441a40c14082c04000009102c2d508441e1103c01d80a034900d20a10b446940480750340d0b102e28480202074503000c0c400200e90540082c0002a140d480405403600b4140c2d409041105491201c400740d0850740b444010b0010003001d20a10450500c081da00640d07014050340050201c1c000100001d003000405d00c0003040c4107000325007184c01554454028030400304042180f0700075003403072060140a5840c0038001080c01318401e004e4507900084100240341011309480440e6440e100e402d1994214034003200400016808000d0090794500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 519739316 1250 519738066 519738071
    0x220302040f02030601121a010c08090a06090e150f1c0204020a120e0f06040210020f070f031e02090a02250f02091005030606060a032c010f061d070c060e01 68
    0x10b1031300025000e41a6540c83c0306a00345448010f800c1c8038181d4065801e80344090030415a40d0410b450110140c1c482d000790650005036014000031020742200700c0c601610b10000e20602c641d5281c0c9031a611142c099a0010343c800215003000540f41815040c0707151800200c802c1c00c8202620b038000c0380a81e8800525000020102da802640710800c1d4851070707485004d800068003a010050780041d81d5003901500c064400c07420103940703906003402008024103e91040041e26015aa1602924141c142c188426940f04071969071002102d15440c030385805495008184030b00c284c070b40103e480001c0d0006170312500088081c05000001e40250140c81d0311040c81340c4107500900880c1c0c030500000c0310b8040c200ca16850300400b020720440d0f0740840c22550050040e500d142c0c0302c0d0030b024000c4014103888101d20a425200d9a0f0403078404114080c400301074020100203015059150108000715032035482014004104070768001004294450410780000e1a071034a80040600d40d21784408a4004001d100207507075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 519740566 1250 519739316 519739321
    0x18030f030f14010302040216210818060c0a050912011a030d02121c1a0a140303071719050712090503060f07030e07121e0305220302040f0203 62
    0x9906000300c2003100500c41c030a008104500000641070a01070100a102c1c0d600424100100784071048100c00c2039411140303058955440c1c20144e258503010410401c0011007810010744011200043c209044009100620b480ea49400a010041d0407402c480f50402404004c3d8a200c0c2e59040d80c00f80b03904134400700000709540b03a007044c80141200340e04510f011390071202e5050051500440c2c9600d40554031400701d036655008821f042443c02d44c20170031010f01b07407800440c45030110000010f00700360b80c001d44070f054890b5143d003412030040d00351a80d1580d02d5442003042000090b000c8840d14510070a1200748d80c00c1003c042c0d01c942d001c00e44074074403600040f00803407102c00380039820311002d2621107503003000440c19003400702107a241d03100105030420f000400d00c08a01194803950040321180700c9001680e10040e00c030701100070070030b080300b00a4441e0041c090880c403c00e02a0541c0b03003062035040e202c60385009006440d15000d0500ca00000e00d041c1600c0ea000000341c0c851f8061714040f80d10f401401a66403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 519741816 1250 519740566 519740597
    0x1120f0b0a08010b0315190603150c032007080f161b151b0204020c0d09050901051c03140d0b04140403080a1d031207020d0f02030d0c031803 62
    0x7114603602904940e810007620f40c007030ba10040364012144459019010480d5510807500400005c0c118544004620b044400424003500c03440d111142403202000344022100c1076000c43c10b40e12044480c0d10003a81444c14034000765000300003010414031402c1403504241030a122854203400102c1c80b100c03580c0ca45c2d01c06a003000211000d002d22400c074142e2483e009824070240b030604928211103c1c0034030008845811005031010103410754198001c02c20765032040310030704d1180c444c0038186519010806c107200c08200c80c50300c02086811723144c0c05400c0024070303081c426140000e0701490030180c080c1720040b40d030306401c10800401804030b00882000032806070022130070f00080300c808106052005100a050000095104a0854000f40041d4000c40c0021021611050071040b4914a1080f0311000030901800d820041324680304503000d4003980e01c2e42030318460940d0000f1038825490b0058008003c0c0c2c00300c00340c2e154400311681902c0d240020307032a6881010b01e03141d01d6220405502041085d08855000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 519743066 1250 519741816 519741829
    0xc0c0a0f0606050112060e0105060d1d21211801090302060103170a12020c010204180906060602071802030a09120207030b01090b06090f030a1a010f0e070f080601120f0b 74
    0x100a0148040103110700d4101d07c034840c2081030041034841c1100095503409a2001e41004120000403109410305c01c0d0010f003066a01c8240260488910103500b4880c14120301d9002600d04000002e0034500216800c0140320640070070040c41d03000344002c110080c00d1058030034030940d90707000d00c00d80042c034203541107040052516016120030341c2050004c114460f03440794031903091038210214240c0984c491700c1c00011140a4040c036048515510240b0b040603241c2c2c1c06075042a90100e0040008100c125207410089813914454040c4401d41590a52120f0340d0324402d60083da400000400c0001e00340740d0566803a0607124026520300c0059010305814010310840500003801401064810420f40003414042501400740c5191644648035402c46c40040361404d12078005019402004000c2100c8135142c0c0b441004001e002e88200b216a01c5000b040340c4110360503076401904140c0300c1117004004141d01b00c615002c0104206d0400c0010703442c2000c00701c0b45008260003000c0c400008a451440b8000303003c074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 519744316 1250 519743066 519743087
    0x50106020c06031311010210020c07090f09020a1e0902030a1a03160308030a0b0904050d03050901090b060904060f1a01020c0303071a0907080a08090102190b0c0c0a0f06060501 77
    0x414030303007042072194100e00c0130500c0080562042c4010400600800142c0c20520140d2800c50700da030000420b010b00f901c01190400a0300e14042c41007003403140c911509811100d203590025004a202c0c0d0081c000140c00449080141d42555184180c154550300300906a8006072081030050f61601d0000b420a4000031155074680019030080610010b54085260480110f1002810015000002c102c00720603540104c0c0b40c0c01c101821a008908151a24650f1035000d80d03e5030300002d2400c00070800c50981030164a80113a0040003400e41600d615040084010000d041100c0c104d5440030420090300c500d0144154404c20010820103441c1d01200181c104050304803468030a80040060703100090360040c0301c0c482d03428024081001c0d580c0e2080218034104080d04490014451183e41c90b040120704001082600c0b420390a031a48204142807524901e0782445000742010b00e40e00c00103c0107801813029201c01051a400c80b4625100341e00d40803d54070841206684142c3c0328030080c040c95800010006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 519745566 1250 519744316 519744319
    0x24080705011b1208061f020304150203090405010303021606020313060f030e061f050901080a0b072001020324010f03150905090a03030c11060402040b010c0204021c0b120c0d06140a050106020c 84
    0x1b6040b05000c64000d40300d201e140a01c4612040c2d82c400504503901c00c200b959079000300034101b040196160700300a5650900c040c138040e00c80000c00c1000c00c0c860b1000c01515000500840a100c83d5410480c0582e00a0b80c9003924408041d907500010800c01c0d820040b85d030040401c40e60078206846017441b9441d0010b01d0707400660050307140c0380041020210010740a000c00341c200c1800b145c80c0d140c0301f9080311803501864499040342010642c25100c1c400660045000e03c0040894501680382c03d0301c0121400c0708030b0040341c00b04121040e0104218000e0300520414214a40c48010351522840020100c91040c0c944080d039074030404941d02059090b12440ae44165642082002c0b01520340e00c00380e58180040c8000c2c007845d1120000c006036401030720790a0384190300400a54032014950320861402e500c081d00b288031036040007240130700d505042c00d0b12400c0e101d000b405003038041d0a00040c0281c80305c2441e000c03245165103c02420300340809102880c003075245070710017003855403610070002c1c501200d8241e4103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 519746816 1250 519745566 519745609
    0xd0825090503070512070e0a02070c030503180f010e1306050a0602010b0301050109110f09060415030e0c0a060203070b0606090d0b1b040f030227070324080705011b120806 75
    0x1a41017203000038014048130050752410034140e80f07401c54000a4026104001c0c040b000140c0c004c000c109000c406803035a200341403621008080300c4810003c101881c800c0e00d6000c11240d0ba01609141480d241c440c2c00341d200d200010610650302d0011590501c1315030321510060f50b4580040016240038040d2600400802d134017400606036000c03907800d0900c0b400403d0001d000c00000d00340000e456940589005043d210710b08e0316010f1001401901070502e1100c0441d25006907400d202e414589400320106844044d1300443c00d05003203540c2c1c02e0703d956018108a03400ba400f4840701c4c40c00da440c01c142224043c4165010782a5040c501401d00100d11020300e00c013082c0100344414803507140c483d402c901c102c03901103e214050441355545508440e00020301c0704c0d81b1940c81401c101c2c2581d050380211000c03c00c00107010442200070f40b407884408145004581c400c1e003010700100a190701c41c81500714440007030000070a003480700d40e54403e1100300d8410001d001ca14004108403040c600040181c04805081400c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 519748066 1250 519746816 519746839
    0x121124010b0a09050607110402032502120d0c0908030a030c020d0201061d1906080c010f0e0319021f0806011b0b0a0f020702040203040605010e16020d08250905030705 73
    0x10f01080c005000f081e000f0703c0003217110000d001310520b2000d10008007400841d0b8a041c000010707108d444090250020360009000003030400d0784005a03841c182e910003802107090804500d41c0c0c00240c90703004015020008403480224a4280a00051458407900c3c0c80c0041d02c0846004040d0501c08002c8110040d0391420400304100d09010300400c5c045c05078028101d102c0c2da107100e0303d400401003000b5540003a0703103842c2011800d100002400d41803c0d0003603c4a96841c1914101100e01490310811560075421800241c096040f034400c004a04c40c0c0300910a0311400f04280c445600a00d400c40c030b50b0002003450341405100e5821425130300c120994002c144411600365110014064805070108111560707440c8035000c028107030307410307207003410350040041d550f81c03c00b801d100000e01428001c00d2501900c2001090540f645040320901d103012a8000c0c0c800341483c941c040c0d0b1708a0004040f44142c0c090541a801e100e8090661454802055120781c6030710360801c4c0c1814035215480e04002c1c01058800c2c038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 519749316 1250 519748066 519748087
    0x30b0a1a07141501030f03031d0c0a141c02010e030f03190c02011706120d0c1106131503111b1501140d0503040e0103080d0e010504030804121124010b 66
    0xc001e070541c6e81002c4003101001a07072034102c00130030400484000a2030324080e12030f00640045408240e8060490b61202010348030071540e00407860030b40b101c2d64803615043c0030082d4203200c1048030301c000e40141882ca60064400740804c3c101a403440070001280c1000030305030410349181e082c0134030805040c604400300d240c0079400600b440090703110303a646040c40540098078580d220380c180807090780e01c0310507100f5203074000c00301034004140500210f51983c017504500103141031500a9590034200880d4a840603841c0a4000004402001e0220101a2a0b0b216644801104001030400492074078128070b148048500082c105010b13142c10061344680c10004200f1030100d0b525a04032140c0450340713602990301a16041c0e10b103200f036520101c0c0c0c0c80c2c06c00c0000002c0c000c1c3c3d00050f0000c8048205e0620050404140103400c030383d0304403401004282410041000320f0f50304922030761809a1400c01c100b0b240307443c010075403a0400d0b0100d22041040c01c091154a442000b8000134010036102d0840f40c00d0034031103407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 519750566 1250 519749316 519749353
    0x10c031b02060406050712021f0f20180603060f2205010f09182003160305031b070605070f020d0b1005040b1c020114040b1603110a020a0501030b0a1a0714 68
    0x1103a080c9c4580392900c101507070005074030200007600f10f83c0307140c6030920b112100480c2e250450007600b081045100b10540c5503040120403a8400c0d240100b00141d48aa082e0410404003440070002e415102c0e03500f488813011040744034243c06000b51441c40203806103881c0045003500d40e0801c81d0440c0c28450482000040c0c00c66201d860700c0d4602162406110b55140046440c20112603880b18280c0d2018030000113004c03001c0300400c5003003030002e0800203002c83c10302c88550703c446500c11040000c0c0100200004250740e10b40c400e0420348000c0406c4416002910349041c00803041c0c1d020b900b074404420042203c2d03e0540304040318103070b003075440031001c00e1040e41c42d403619404094040c2c140184000d498014882c8581150050050543c56030340700c180f146069a10400c0401c4c0c210301041d41000b070451104000541050030907801000805414184001103000d000f801c4d42c10f50f0480241c540100f1680d01d0a00c4140c9405c544071485910740c4000d040080c20394044401d444c4241d00320704045520b14000301e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 519751816 1250 519750566 519750613
    0x8010b090a020a050903060412080709030302070311010c06140a050a0b030c0d081b0a0203070504140a0b06090d081804150e040f0c17060901020306010c031b0206040605071202 77
    0x25580140c4a684403c01a5164800c01c452160b050250b80e04101c1000381c0038601c902c0908055690441595504200b5200448640030107005a842644100001121140c02d10b82064040c5400803041c0035659441d8140c90b003000c0c100d08417201d80000c1240c10300e5644626580141c46a13010b0140105003004284c40750b50030100280901079920b819428050039402b01c804400d202000010203001f01d800054136902c000d10708900c42d0244040002e090320b4603024020300f848044007441565281c045880c8028440b401c0407d400c44014491404207949140c5c050030118001c021003aa40e407007640261311100940e03844148500e280841c0700180407280d584a105032180c150b41c116142d02d4500b42010500c100000042c840740e182d030030220b071900c003201145590401c000704950254562025044c20303404200c501c0d900160502045c000442d20404040400e0000c0208403800c812040d0040380441d400b9030004c0010500015000c010041c48100b035501100342807006e07040032541e61010300f6035000c24 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 519753066 1250 519751816 519751831
    0x91219030f061a0a120c050d0b3c0415050d080904091101080a050432060c03061f080c071509110307082d0708012408010b09 55
    0xa071650000000c4003640108040c00c0d0b0f00c010755000942902108506030b0040041000040c060100756900010500526881d0b07440d640300c8500b0300c20360060b203c004203041c100303450b13000804c038082c1d164902441c5d100341c9103072140d911a10070404005440740c40618528500c18001c500c1d1074070b814902580c10540006841c03040314004c4000207207060090244c0985201541e02914200340c0314100429030310781003800c00013a2102036183d44e135100020100d40c01210098071103508412418542110b26880c202441118110b454801c07a0f4030007641e15001c03003144c1c0050701400c00410300c40e01c0c0c601010a520418014100510001643e440c000c1000401411901072001c01044240c108044402400740310b00b9510b104001c01c401c90300f400c00d5020310900f0301ea0b010f40074480300403949400104072140c440181140031440c3d43d1420400310241c402c0503070782c51164001d264002c110400b00b8044c039202c1c118161141d400078181c000c00e22070b1181a40d481441c00f607140115510311070311912022940402c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 519754316 1250 519753066 519753071
    0x109121e050310090e0f07090207110d1205031b04030605011d070e010c021201021303060b060f07022b1203110a08071809060308041a0c1002070204060f08010509121903 74
    0x117442884524120369241d07a02007034003900034040b500c003445d540a450350314040e100d070a0b04401800700f8007004042d4000d010307165110780395107001c540f4041e4004503000795140f100040042c0001c65601015001380e04200d81031500c0710300420005c25102030070041240300442c8081c040c00c0040d0301500702001305028605012004d114801503590702c01ca20820592154000d66450b640352950100d1a03040340003c03100c907840c0040c0421581007032400d951741294a000300a103000d60355003c11001c00710a0b1038080a5100b801c9513803980403420b01e001e2840512034940304002240100d405010340f041101d02c01c039000004d0040707068241d40f10380c90039005500c50400b40a05074900c80b400c4450340058000c24081420400d0020401c55090001c01c1203404122850012894500a469040c0701d0303035650280e02d600c48181ca9031041d001e42e0003024001d10081000900e00e503110720195481215510100d0940d65503020000c00308010302941100f440c1d01c000c1c0700e141c08840c2401080802c0e03103107584010141e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 519755566 1250 519754316 519754331
    0x4120b0a0f0b06040e0709030b0103121e020d0c060204080f0d0311090d032601060504060207150e12010608060c07050f06040c2c0408070201180506070b04050109121e05031009 77
    0x1801407c2d800050750300031054520640e1641817910048481d41649000200e500500d10402010240c0008888207660301400b0010b40780301048881c0101c680301038401c203500300400200083c01b003003014034401e400005044514001c0c0c00107000ca4861054091036000100030500c0b1640c2d4012900e14055450305104600443d01c1c14641e062041d0b001024260880d45d000100391140c0100c098402c9801d0b036803c680c801c503102c03086445c80071052102c03280490409201d80f0300c1440c10080135505003468000010b80300d680c5080851034158107440304d54101c500001e04405100c001d0000c44141840e4000414241c00c0c69030354105c0d00c107a584602985200c640c40030204161704503010120315503030000d0b40e101900341410329035040da10000742240440c003030085090106802c3d01c0500110317034006007901d0030f01119440d180d40d080d0004004071340fa5580ca140704800500d1008201407074090319a074680c00801070110b048034209100003c0010302c201031040000d050f41d0030140710291918550042041d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 519756816 1250 519755566 519755581
    0xa030305092d0705030a200102030c030a1d0f22091712070f0c0f08090303070b010801050a061419050d0b0403030c05031306050c04120b0a0f0b06040e 66
    0x80d00d201c424090340303550344008182c601069209000700006030090b00c3c01265580f04041c1e4490f0030203030080c000c00032065803e10441c16205441411081030050784e151090364020941950b01070308181022400480c0c0e0250b044128101a00c1848029201000716501060005103085040c1c072503981002c14140b200b400840e040d07045070601caa8805001c030589840504005419045104000c451184c0c01d0700240d002882100a090084119102e41e0110300c5030752140d180c0500c040006a480000411011001e13031070400081c5500c1e4040c24016100c0d50411049030701f0340d04040c00420600342810f90500c051118030454403900c0c0c00c126502421400d103410b0425901400d944055402034180b10894180500020f01a12485c072903601041440a42c440a032030030300060b221031280c9002040c0500000700503611503a08500c0c0985903600b825034a880c0b144505250503c01c0322101e2020b41030094210560042c0804900d80413014061000030b0808140c050043c0c2c4140c40e800400d1801240b00c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 519758066 1250 519756816 519756823
    0x114060a120f03090b0a080118140c0f0f1206030f030306030c12011107050a050d1823030706050a0e030304060c0818030d0302030402100f052a0d080f0a0209030a03030509 75
    0x105000800e6a491340c80d108800790003040248140340a402c04e415109c00d175240d043c4141d8a4a003407003806c031039094459080250264102000400f19124104401c2c0040346405001d0412400020004046454520141400d00b032514211000560041c003d0140d503940105402c00c06c1c03c400d40c0c4401d080f0355a4014130b8003400d4803085180a2600001301c10301801008038090368581e0154084540700303200500708442c5d02110b1044414400b00110040c401d00e0500b8406100d0000c000130300004002c4140002824003015500000100301d0016401020030b40100004004031800c0300954201490141b0286c803040c1e0286c802010454002100162024011041c6560340f8014007141c4a4000028014000758030554059101d032620817849500107206250038410242543c0d1464200510f10a5601a42169800151240608002d401d040170710400c05290008044d55a04c002400d00315140c400010002d8440e4040d640104403280e440d88001881a8205a151500080c10b94605a06506 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 519759316 1250 519758066 519758069
    0x80409020a09051e15040b0409050c0912070611010203090615030f010207060f050109050403020a390611070b2205130605030601050d0b16050f030106020114060a120f0309 75
    0x28410305807855100d503d01d415110782104502605c400e00d54420101520160707000718850208001070400c0184403880190b004185c018240101503070a0204190000d1550b43c2e0b030241410540c0d0201c5c1c000c106c2160721016521040d16800021495418080b80382901d030040140345503035100c6000c1c1c00a001c0c1c4c50400c106082e0300111402103407200407620300880030b4040c030307214032003400e082c10000301d0315125910075a8010359041d0020101c000e0140c5d1001240c41040c2c1c3c212114100e0040002c01460354007c0c1e88080c0381d2540c030b84601c020700b0840c0181a188140595080c1944103000a11050101800310340800c1c4040c900400300e1120b10385d1480d40c40c030486e00141c1c1c112181003500346589000c0c0d0801ca00346c640844c01d1307030816a228014000c2e0121044030281c1a91103813030100ba560300c0451800c000d085070500d4150b180c404c8080c0e00c991158800c0e8801d00041c1e54840c240300320030302d0f04c814440d00038a046880302c1c011880c02810b80400820040d0140031f4140d0300208400301805160036a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 519760566 1250 519759316 519759319
    0x303170c1e0301051008070e1e0d0f050d020a020105070303111605030c06010e1003020d0602091503010e061914040b1e031203090312040501150909120c080409020a0905 74
    0x28481c168a080c64881c0d0800e100b140c1c014140040c0a154a5014040d503501c175998594841225180c0380c0b04211036611841c00001004c00300c044a115541c945070b08004465000303c3e851804001c1ca440e015160019244c5040115000410010b00513a8410100d41010740c243c0f4020138010364941d602c0060b80302c2c030008607000400e800401d80030440c01201030145c4004643c02c0d1481c5aa07100082c420f05081280c0320075a03044018828401881c0503c1030410341802618010304007001e40010031001d1011921000d601c100100041011261800041c1e0340b1003401e0307440408000e001515102501614042d40c15014482c00c1d4458954840341d101c0e0896003801006c482c42c81040305000c01c030b117a0231844990700a0080000034540030500c44c1c102c9005442c08030080d468900440300c2c0317041e1a100640111125502c89241c501d0302000d0042c45006000319800c0040d055005281980182c404c50014506103c2c140035480081030901d410380301210218980036a03103060f50101200c50b500380740c1045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 519761816 1250 519760566 519760597
    0x60304050f060711010c020105012405040e040f051216060e0114010e01090b0a0807030609021816090509130618170a02070b130306020901050c030a020d0e01090303170c 74
    0x550b513648841050004880c02d40200f100100480e4200e0913508240602c00b0080c01541c00e50300c20000c0a4512a5007801d640380c020704090302e8103070440b01c0800c1640c06079000700141b074404092100902c0038803031140942c1c1c50a0328007448020201c1009640f0303103000c1c0ca22540c0b5100480c01200c02c0d002100c00104030f0341c079500c841da100d5010304142e040c2800b4002281d0300c1c11000e203903030381884032645094400590082040b2441d61f0384d89805001c44007012a00803405800c09460380c1c40c2001c1550082a040400f082003000d003003c014540f0700240d01c064402d030031640c06d102516103600b10013201583c20a401160181416802191100050030010310610810364580c4204194030064850003190781e0036194a03c0c2ea9501c0203e4034001d00c14102861480810208000b81c0290300900751782c40181051401d04402e500d1190454114616103400368005204081405078007840440c0080000d0800792010b50968600910858080840e040f0b40c00300310b804680c2080350300040d0740f924200318142d23 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 519763066 1250 519761816 519761821
    0x603041509050604050d020a020108040f08040506030106120b010c0230030f030402100203030f07030c030b0a090207170c0a020409080c030c07030c0501030c0e0405070c12021b0a08060105060304050f06 88
    0x10f603564008803815511401800040110705102140308041e064059581440c2034039141c4507011321480f12039003122554400c010000700764440a014500800b01d503111035400600988500c400d447c2d45280c1103040040348010741c0016518021400000b5001d0484001082c990840ea01c00341001c65642c444180b00c0841c0c5032000c10240e00c01148034030f100360344000b48074010b00ea0683e62404165043525240d4135000001d040d80d4030940c0103e00e41410b40c500403134003540107400705e0005003a9070070003050f03a41c001400c08240101964000d016840e0038030080d280002c1209015228004014005d02c0740ba110424003051001c10b405541200d200f0b001038036601d0742c01c084110341e181c81520040f10124a00c0301c2c0060590301a02c02d688100d40a0389400d000030150310108801410010000814842d1003841580810f00d80d2141c81c001c0a83c175002828031001130848044402c5017100080e10650350780c035003030007941c1d00452052b04440080d62003989a845600e802410581214080c0c55544170340b404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 519764316 1250 519763066 519763073
    0xc020d061d0106090501030807410115030201090501050705010f0e0606031c02060402010e011809020903190203030405221e0b0f030c010809030d14090d020313050603041509 76
    0x8180c4071061400002c214484c0d40320345800c2511000d01c07029055000074464200840d2203001c480c0f01e034040b1262040d00103d003600103e1902c15006c000501101d2610030b50300042102441618403202304c0e5030f0300c2e8012a01d1540020020420380c02a5410410b0210314641000741c00d4004001c02c0b0301c0c60200b884185040c90500b695210100c6c0c4403482842820f40507036180781c08900705000c1d2801075001d042c241d0344036001507a44400c0d2070340e100e0421500801650903503c0c0d00902001030840d1400150341ea40320841058607040c652075080d0b0000010211540060b680002150100d400540d40743e10303080c1e5480c00340581a0081001d000400f82441d0034003041d42044031040c841000514001c1140c0204803091281c43e8200d104051b4142c0c0c00420345196640c01020344d19440414007044070b10b400c0f0108251002c2d10a00c1c55a01d06080b040001e00103a04018415942c2c1d0340d007070703100450400b505000c85102070001e61103141d0080d900000410141b100c00141c1388070b02c01a00c2001e010b072298514 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 519765566 1250 519764316 519764351
    0x90504060b1c0f02040216020d030306030b070f08011406071b0303230d09111c0b01300203030d0908071b060e1c06090c0f0b0a0804030c020d06 63
    0x1a440e61203400035905440200b1120a81502c88641050603d0040c0c0c160341c2c2400020352041c0d40752000701c20310f0547d140040c0c1da5a00b000d403c5600c6540c01107459031851401d1085000080d1210742402058031005405c02d91003d8514119903c03801344140148441020900c40e10a00380c019145003584185028136203072046089085910a60310b61444038070340c1801005c030843e01c3e046006050800c102c10014512590002d00c4550b01035109065400c00007000113007000e101140f0000401c00000d0020280302050114a0041400101c070f10180c080c0d03040000f03050a540326400410044291038103055450410030780f400b40026003030030020b1340700e5800c124400340c1068108440c90701500c2154604413002d18045021940c20340c5403000b6400b100420806480c40181c129480b90944082080104406016001c040380c0988400c0d8049402d103184280b0020035608180c010791010006601000c0d030055496900903054034210200c40c009100280c105044948090142c0d03081c4517500441e0102134 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 519766816 1250 519765566 519765581
    0x1b09061b03040f06180311010804020102011d1501090b010504120305190801051e1f03140112020108090705010f260a0609061a030402012f03031005040504020d02120709050406 77
    0x70340f00e44006092208036411685040c6c00001e00202d600480c125055015801d00c641140c0305000115020251941e154130701c100980718013a150303100c4032000001d00718001406000d000144018410712002d01c0010f404d500c03642c03003500d00003601f0421f02000d00d44610245d803410301c1c0b044003031001c040c0c8841c3c00820a00e0280074940c8104400d0841c1d002a0104500d03002e000c1102408514030701031070240d01d910010703800c0da4034420b2640b11a150ac0710301c4414086940605803045500b0394580407400010034201c401404640d15500101050016a80090f4000061489850b04500c0b041100081c82c03800300138110402203121000f0140104010190407210640300040e00400c542640c40c12450001040300d031040d48019020004103000d548144001d030080c200391000094404441c803a02d0308903070083d45542c0a681c20100500c4815001d85201d94002c120440e4280010708058001405003815910000e101e5148203208000803182032003003100600c482041048940b600e0f0620001600300c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 519768066 1250 519766816 519766829
    0x103020103050105060306011d19080d0f05070503031303050c0d020105190c08130222050712060302091501021c0804020907031e02070206070b0a02121b09061b03040f 73
    0x10302c800400d40b41000001d89102d01c00c160340d100b04042c2140c14041c008031801c01d403d03800040c580c40c1d0581d4200c40020040040c80c405009042c00000c243c0018100da06c40305041040000800080b004500000b05407a04241e0348420804a44480c0c41c0076030b460b108030141107046010780510140c4c03407074042d40124032888242c00c850b814080e03824441c44c115600d52801a001c64460400720341007511903c880441284080d200c041c4802070100c540790880d1046c04011421512681000880e03a400480070990300644101840110b003076600003201800014203003103003485e0008804903680c1c800c010340100400381034050b840844002c0002440c082d81243e0a9015028803030205513814030a00c03d514034549a20361a08600b202d40c441071002c2d51280310160390000e02401580042202561480d014000a03240180c1e10703100c8100040140784000c01d425a580442e0140e1a1501d500ca000c50700d143c0d05c02c44044e681e81c0940440302109040702403500e6103901c404140030a8007100c41d084003040d100e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 519769316 1250 519768066 519768071
    0x3010807151808060907170d030504082b0f02120a0209180709140a08071205070312090303020c1806040915060303050a080a05100504021b0604200d0f08300103020103 73
    0x312818020448182c1c80d03080d6446074001c0201001191003942b00ea90414400c00805107400002c0031083e07000c1604d80e120100c074100c1443c4a8006521500c2060500c000d07501d81582481000f455181c14100024903070b052680e00040d0220040d07440420000230310f10a8140108a41004c0c0001424690180038a12800c1841c2441a80302d1420800c40d00445e41008020308510b400c100b01070544000c1400304070307014819074001000099481c90180022001503490142d8585142002071505d98240e440b24050004500c007075418503180b03010b142d44913030140c9000c03460081d18604840c0d0407011408616020789884004820594044010100c02300d0030b907219049602c80030055021100282e480002400225030100618180783d0058400c405112b00741001034807080c0050350515000b2074044440c1920100202021401074440512100094603c82000d890384c0e1340f40f0850750401030300513208600200e52007501a0700c01e08200400c03c01e030800311000010548017000d503007400780800c070b01190 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 519770566 1250 519769316 519769319
    0x3120a0b0a1e0e0c31090c080c0712050a21090309080601080a02091504051f08030f0f0c0109121115162304030506010e0c03010807151808060907 64
    0x308a594050700903a040008145007244580d1100700a1802c4505000503410003110041d0201c5c0140c4030100a044040c80480c15030700d8100d000300031050081c04c03901851004d1141d000418412801c0348404074050500c540c1c6c842e10f00703200b03840122511900c1c200d0207151a1030199003680c15008407002a11039203581c40d081d034440f4203060315484d003401800000e40c0322540031001340c94483c48154120224030801e851a03c164030108050314801c986801c0420314003030661400814500f0800000e204900240d4200314080c241448640b02e00c4c4588200d850000c42c1803042440c0a5110b0042d45038000d01440205000200242c4071191000b4194998011101240103007100241000c0c89140425450a100a03a5010a540600514040321004045c40c04a515070040080c02080a035000e00010b007c6076240505402d9910f40c0102500c03040b035003c0c80100302d003907000210394042e2130480d80403a1220799001401c0f40c40300440c5051610b400e0400328000790406021442c9409a0b01c00c0080d41d0003d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 519771816 1250 519770566 519770579
    0xb030f1b04061203020a0b15060a110615010c0201080c04091e061203080106031d0609010905010b0d0803062e09050906100e04021b0a0305040602070807050303120a0b0a1e 75
    0x21141054084e0151300100c041d400060301c050b500316800b0b00c0e610703071400000e060100820059005450804080380d070781c2040e030159680800c91142d0013110030000400d00700340703c0b0000748290101a0b009042c0304040000c01c0c0d030011000141d402410070103004200960300940c081c50034110800502c103000d45810004105a801074500e075400300d802d40c0701c0782c0451346015811002400d402d4107032500007040600380c100c0c1010900815000e0100e040012039203503d0350924038211003011141e14455072020364010300003202c0000340c0340c1c031600c12540501d441c0d03071000ca10341e0b48080040341d001c4000010741caa5a03100303411100d401e040c2c0c0c90644018a0340e5a400c4c0511100180702c850a2020440c15100140c851400b40c00812070064a04840365403000c180310210728041c00910108c001c0b03140414140235503581002504020031140d4002c01c3d01920b440e01007511780c82084c0100f1104588000003d1070640c0ca07410401d013144000d0030192141e03980b09000c005408007038031585000c01c0800700000d80c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 519773066 1250 519771816 519771839
    0xb091606030e06160c2f0f0d02010e01090306050408041701181e0510022119090222060306060611071e1206020405040b060316030b030f1b0406 63
    0xc2c1e40ca40000789500d40b41d4081c041a8001d07401d100c08208482002039a0016504e2041c480380060743c440f10400300c010b82d4128890340035003001c4080c042e030354a05a00c450380d43c8006900d540d0580a081c5170a098401c080102c03016802e07500080d20300fa04103030038481005a610002c201b202c01d0764403208252120514502e013030b242d10480703140b0100e807030300c0764200420302c1080d00200b002c10407260803801032619504d081c10300950204c01804281d0102e0b64098480e0030340e07548a5100c040203051003045c50300018028a440300f00e180c074504907954080d40811512880414441e00d08002c061180410b214000000900a140001c8403d28100900003800c036015007960b800040b1100301400c21117080c0801072554400b403e0007403601041c0094005001e14810704c11740c41c0d10340280c601584c1c41e402c2c0800d10003030b80c075000c0c01180100b80400405c00180e420b000425240075003841c020900c0d00d82d18001a1a150607214407900b1130181050304224020314218400d0054011748ac14050180d607411800803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 519774316 1250 519773066 519773081
    0x10501080f04051c031e050a141303080406090c17070603060b040b070606090e15060303030402060708090a050301050702070305010b0a0f0e07020709020f03091b031f02070b09160603 80
    0x1d1680640c4c1e4034144120ba038030214020300c071580340020711458081480c070740c0411030060404140b0781c1c0d0701c188482a41a03024444c445a4004036554a0b400c1406d0a9064034402050103010031000001260401031590080524076410042940072188c07662441100b100c61030030b01032510300c200000020f650f4020b0080c1403c5079580001c143c10945042c0403002c0310fa200e1041202c01079610600424030301898403e00e807043c110600201401c2c03614059070400c100c800b4002c1486030f4828020040103030745a0007100c100c1d85d030007480035071140c0c2c01c00045818108150403080d415424103040008290b4005800d0040b80e009a0081c040c0748076090070320081681d240504100c140c0250000c0c0420b649840c4104e400407183d2046952080e80c8010100c2280c10a40140e0160140007061007003a810400003101840324401003a80b080381c401c000641e03100080c1d038840c0d41803640f1481c44101600d19074180d91103036811684400641c80c14030605622800c440c00444600d040c02107000c00c0d150b101e40715014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 519775566 1250 519774316 519774323
    0x14010e0906250201060509090307140304050f011d0a1806090204050603131e1227270e070303080f13020f0d08190e15040306020307110703030503010501080f04 70
    0x40c00725010b440e40d4005004032450310305540d02d03000001000e4a41c06960b51064048201541d1621071515054520044950503000913070b006010600c100c0d645c44000541089003400e0004101c11281d0344039207040d0029812a0b03002e0390f8600c00003640350514800451102d1414400c000c0e05807a031528004278062405241c1c1c100034107100040f8001d40351000e02c0000c60042e1840c10040803490003503a4840c488050840d0802030000c41074007003039048244103503280004c4011001000e01c600358450300104501ca40700c1016600c052842c0c0542d8254580a050320f08041c0c244891000d103d40740d40d4030070081c0b00c10ac000402110025101d48040d540c82c5002d02101a40c82d00d042100b602000b05000003034480950007400041c01c800000c200c20001c0c007030251146560b0342c00103801c2c0406404040140c0505006220111460070800004002c86080d6035100d480107890f511000c0c4120380694060040a00030b102c0e1880100c24140c00201641c1221000d9a56911541e0350f465100c20891090368000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 519776816 1250 519775566 519775591
    0x70f08030702190b0f3a0c090503010c1d03030a09090b13020a080402030c0303030c1b0f0a1401050a0b090c0915031509010803070b1306090614010e0906 67
    0x21001441c0814a90150b581c040704110045911058560a642d100126030380382e0380700001d440500c00311030340007200c86c001c1d40c0c0a80b540410405c01c5440b840c00e004404102801d56074008106c07002d4010074109019040160080010300d2200034098241000c0516030350740e48170102c80407076462400100300e41c240d041c3e80e5591407a1900e00710442c0064640703c0300d41940700c0b40e01003c9540040300380c4040c102d8020580e49601d01403c040c0145800d140061002c1e138002d8004000b007241401000c02218404219000c01c4d0000b1544034241904240804c000062a07002e5401741c6414001c9030481c0803c040000c0008000320f49a0341c200000303c440c0252203981001c401c8001803c40c00103d030107040d0f0350303170040c0100d41000c1880441d40d85c10790040711880883c1503440349210803070403e030045a0240020310015440c0101030788804d00b04100041684054010700007083c401c0087c0d07500b01c0000c840c4c1c051014041c1004030b04813200c1c40d403c03d0017440f0b40c5032014000580c03050400036855000c0d80056219 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 519778066 1250 519776816 519776827
    0x31a010509100c080d0b09090111030c090406030b040605040c060504060221120165040b0d18030c021e0901031218061707030f1805070f0803 62
    0x5110b0000c541e10301c10340502c8580d20411021941c130900505a40c88101e1000403c2d0b0018002c0007058400a801000303141e1404c0c145d4000d080c0d0a03422246c00a20a000c41511164501c0c000380140c041034200500402100d02800308022031038010711300807840f40c41529242c1c0e85644c0110351600441c03241100507401100c11000d4210307032121940460180c2c401540c508588a46414014170342a401541050546124104074074030070702c1c03800e2403044cd201d214084005c41080d1a5686407100408900c0840c400da58110790308120a00e011140d4511010302d0388544d170315004a46250010b01e04070300080d041c048007404030003203909038440040c7d0588a01038003003120780034441e880e6034000801a08140c030200c07002050395514030460003184100040c1e10150030310700c00102900500b02d045003140030130840900503180c105400841a81d084401145d00340c0c1d5174078040300030b4851070095114031844c1c60404180d00342d000c603140100e03074001c07422200b019580d07000c41045a440ca200d45110350b00309000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 519779316 1250 519778066 519778069
    0x2d15031906050d1b0501020c01120506011704050609070f121104020f0d1a040605180c21040b010b03150d08041a120f060604063606031a010509 63
    0x8003a00025804040040c41079200c401080200107014019070741d500f8043d91a040441e10001c202c0041e25007031000c0c1124101e140006010071140c00200d0940c0b54072100010040c0c0d11074a14030b000500c610071005c005041c6820310316100e0405803080f0a0b41d008800c0085004503088030104100c6500010000d42c4840581f038480144460072031140d4015000c014000f007403104a0098882d0018012000518a141b02c10088424921603513141c051820704038200815910215002c07100f21200c40500e0f810303034803000207128034441c203030b4210509410036940740106105841748601c00c0e88500100401c59884018841c0349000c11112640f10f41780c440714252442c1880c1c501d406013039209141981c01d164403540741031440c0c00c1b070401440981d02d01045240740740680d644d16903000070f42d08022004900340440401c0d080c0c0310b103004103030501c147d00e40d600c5000d0040000001a112200851500360017868a100c110005944190710010b400d18900401d000d2100d00848441001616101c2c40d00592a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 519780566 1250 519779316 519779341
    0xc0a06050d0e0c0a060906020106080a120f0c0b010306060e0f191d060a020309100903020613080d05090c040e0105160c030507050303090c280b0c0c2d1503 68
    0xc2041e0507000342c081c0c00e983c0d500c9030b15508000d8445074031101401c90412030003d0844069500c291103582c0601c2c1c0c020041151114883c1002c1d40a20b0b24100c400a102c406541c0c0007035482c002819404050000010311015a0201042d504c0d210039041c2ea9031601d4100310301041040c0c0b0203070001d510700c41e800030403d8002c1d40710341e1954410003c00c2c010780380c0909501d07040401c1242c00d05d01e103503000400c119040a0500030035500310001d800c100001281510300a58444000b000003881081400e01102400820802c0d2000313a00d00307003010300051070b091508a44808042c11624050342c10258801c490301c1040c092240304580b42031400c1303910082d040048504283e00d51040d82888020840980862802d100640c0b0440210303009019144031042480020740003003219140c42209800750640c44c5480c0c203002c504803500254625210801511800d0400c0c8185810a5200b03035040002c0c0302c0c203001410300703003030b440c40c41d0f41444400f00200060118000c440300740c126426000304005849804401d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 519781816 1250 519780566 519780581
    0x706080703201c05090102130803040b072607050c0f040605060d0902011403010303020f0c010824060c0d0e0a0b03060604030b04030306031202030d0c1b02040f090b0103080c0c0a06050d 81
    0x8944904000c9105010f08552095800d058a650001020407540401090980003400242d001714135040c504145214a80101d40707000303020390b602e21002800204002020703090300d18583c586030303500c18652501c1a580c0040c07280c0e06000d01d4442600094902d014420071040714005012035180c58100d4601c4001041e028a00b01d0502c81072940300202c20340090b01039806148250001c00c01490300b401040d203080b034501d03003180c1080f0200c0100301c21801c04401c1e0300c0c000c2020214421113004441d000403018002c040314000d061182c4850200155440419146806000d44400e50680e0319186207403030621049400700e4000c01c0801041002401c11440194414041e00d0009486a26179407080f447c1030388261840010303440852003068a20070f51045d60b181035006d081c5601000010011489001d40c0500060b04c01c0b540ca42111f040d901054102500c015070103407011215603100c1c0b4109a064002c1000307070015100c1e035032001a071070505180840c240c0300c0c00c1e11154100f4a02a41c1036010384000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 519783066 1250 519781816 519781837
    0xe0606070b10121a160905011b05010222050f10080a39020c0306130501110c010204210f240e1c020105130b070203041502070608070320 60
    0x1100d90000e5810302da0304071214482c1c4101c1c00c4d11400c46111002034203210000d401918007001220f03100311001c0c1c014840808481003800c04540d056080c18070420000300d02e0070003411035400019881840285191603210502207074101c20509501c4100340000c0003098030340180c010101c0b840040ba00c0e070242034401d80c000b441c60008102d0600111130f01641380c2d0600700e0301e9041d0505440c0420003911085615040c100c0e18070003046c0051000c0700003a556400505442c180c00c2c0c3c801c9200e824031400f90010600b1030040d801c41f50f0340b0b204000150b4000c0d0b01a02c030382c50418512141203503c4100c1c0d030304080d80c519086001d040030000151a502158102682c00004400c00080b182500341024014403100710140001b0344000400100059100016400d0f10021640740c0406c2156002d02983c0c03850549030040309140b01d6545011003a89144600d03080b135581194041c03070126000d6400915017003960201d540340c001d107407114102641034501100303440040840f495041c0e202c0c46008800340501120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 519784172 1106 519783066 519783091
    0x305060a0611030c030c1509060708071206080f150105030c0108040f0303090b0f1b031513020d0f0204030209070c0b070503090a020a170105010e0606070b 68
    0x609010744000d000c0341540e250380e00c0b4030400503200341071014022a5a074040d0202c078039584640c44030000484050000c0081e04c51480468505d000d04555110042c2c3d585600308141ca81e80712008004101d20f949542c002140001001035107015854180034003445a285982d148460005821541c002e902c0f10080b18030590b40291520383c051341020200d0a078840529084002d050b6840b0b010700414646e8040c0305445181d407214a026001c4031055205d00340c0002d0002e8654003044600c1800706400e468040c0c43c5080c020b015034403461809070014541968204080205c0740c07104408201141d001c142442141441c4003031a41000c00760800c920031000d04d99481ca0039040081504080100c080f0214900036400c203c03090301d40794010300e12130105440d10450208140c49050b203150640c01c0800000b4800702680392680500302c00307080585442496150b500010002030900d02c00e0741c5d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 519604316 519784172 := by
  have h0 := BRFrame.cov_init 519604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 519604316 ≤ n) (h2 : n < 519784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
