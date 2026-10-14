-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0676
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:05:01.233101+00:00
-- url     : https://prove2.me/submissions/ae6244a9-eb3d-45b3-be01-67b3dcddfe59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 121402877 ≤ n < 121582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 121404127 1250 121402877 121402937
    0x6010614090405010e190e0d110f0105090109030e0f01081506070215071a0705180111030a0c1709090a0509010e0a061406040606170a18110f03010902010206040f08040312 75
    0x4840003047c50301640c0d8502c3c00078900140002d040201001150510407001c6818401000b44050704080c400b10b4005d00f58058240c00140c002c030014080c41c035102c540100350075816529004181c0356001c411202e168640d00311607120500300011401a02c46a5071490200342640c10a034580f01141480c6011000003c3d0080200345401c007002281500442941d6030f03402c64000b075007920351030100140c400140c03102d15401c151001280211100b0f81c080c41c3d80010602c201d05802030f0301e91144100185024441585034406010000500004541d0f80002c2e80800840c00104070314070003414550030481c0704403003511210b840e1903541c81291a20300c10aa0820010b440820106240c071300c000344034070503ca0070748000e010b10001007042110306401200c0c58403408070280c00171652a1814505c50707030302801c400b4040c44918420001c1490188070711030100341c06801400580d981d40c0e0f6080c210b20f600800c1201e19400502001c0080342d098540182c56000365111b964014401000c692500d848403c015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 121405377 1250 121404127 121404131
    0x20301080616050a05031f03120906090b0702040e03160818091302010c0309051e01020f0703020f0d1a0703020d0b0a050f10030621030f1106010614090405010e19 71
    0x20b031090b981c030030300b00c8104c1e01d028a003144e1030703860b04180ca8070792080580c01448441100358000c401c4c40010180e0424600c031716194030003280d554403c1503c01d40b041e840344104014040c008500981455000000c40d081c080d01503a250004d490601840d500800c001541c0c04900425851004072003480600c1e15068200c0300300e0390381e103841c0111549101c40c081c0300074104041c0400781020140210b0809001e81001400010218841641144a5049908024014460010b0b058803440000c90084192a009016440381c229a40b0612181020681d802c840c044d800240103004805a8440d07140602016038026a450080e500b24005891603500c03213501c5045c014008201907502e04500003a1014140c400f0604910700100540080c480307a0f222210110a45404568402c00056246d4031140300e600d82284008103202d04071161180d402d554086940050010310409014641d0a1141c1c400c1002143c036206c0034a012506440080c0e00404071500c081084c030082c10460503012a61052150b01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 121406627 1250 121405377 121405411
    0xc05010b031905061e040f050f0a200603010f030303020a18030303090209061806010f1106011e08031207140d020d06030309050607030806040e030c060103050c01030c030203070c170d0f0203010806 86
    0x1260134011702800081c42e568202481e881006414025a501c0c407500c90140c411603840c0703052141904410320940c140c0004030344101000b500d04182624140d8060220040754141107035010340c001d40c007000300ca0003800080310303600b4160200180c03d40060740c440d40d03011400011b240305201c0c85403406003250f803140c4040c00d4040d00d42808812401c1c5e201c9001d00c0c00071a00744a2003020b81c0c800e00480068886402080c0001c519000c04000382d0313600f0400ba800c40f4a03c1552000400d0f100d02404c2203200612142c50f001c14402c0c0e2007541c41c100d100000400451a1199825071407040341d018810105240d603d4200400c181604080c10301e0042c2010780f0820710b411441d0340c00900c42a00200501c1c400c9640b8a50200d40c00020800d80d0320004c20b620407510039584a08100365120741c0008001c0c00a420500680500740c460f0007528040c81c050703115074000d10103d60761a04103a1203010341011000c0244821007054100d07000e123480000c3d601100596035418000701600380200208030038204070f00380803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 121407877 1250 121406627 121406671
    0x27061b050a020c014a1206040b0408090a1e0503010209031f060b0a080124080112050a1b1d01030b0103081804060306020910110d0c05010b03190506 65
    0x782604443e00901c0e01141984080e40180c0220b15880010001c140d580074890002e11a00060106803640040b0a1000107610404118400040800928864000d540410300040d14003110a07000ba01c2801021b04200c06407021034482c80f41984601a101c2d40e030203421103000100c5c031071103015140070f070000d5242030610700120350340300c04140704d00040c3c259003200442c0f8000d8650052014200c1c0716400f40c4c0d54540e402004240030002c0c000e040803582c03403107603007425420392401b40f4510710314a131180c01080c0c0c80e022885164045010081d00d20f40120551f550006141098000c22449450040c151040c1000d07540e8407040300c815072190065400600510119000031a00360440b0350051601c2d548540310081980203070300040b00c854010707040060110803c10190054031505000350303031101c446062550200d4181148420301100d5800c045045400b0740e00c610020100035000700004100d50030000c0c0440c0c50049aa1092443c6000044410041101c14000241c2007922010000c42c1010124 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 121409127 1250 121407877 121407883
    0x171e0a0b0948040609030c06050909011802070c0e010807050301060b09060f04030b090105040b0a1407050f040e011d07110706050a0e1c02040501061b0627061b050a02 73
    0x450010b45036907005a0b407190001d414600c030820840c020b0307029a180c03079882078050f100d219a030104403a02500c4080203d81d882c0b01e00107982c1e514400170007110b41270b441c0c0701e43e400c00c030b00d04180c82002280c0c007000f885000c940769000b040f00030302007075104100700d6260039511070505501c2d81204d4421f9050820410010500c0e2080da0708404040b03030420f9580180034951a0316120f40e40c001044445044c04001c0c0180066100314860750143c898a95655071b403514187c111040b0340403640007074000001046295100713001400218041c207c615141a0b00c413102540c200c0000d070b02c0298071308242c0d110030090380c0114a90035009126401c0c064000d0f0349000e1903075191200e45c02a80e042240101d0208225481742d20b942c100004050040f034006018104042e00361005000164059820b1030000100c10b4800c2c101d2015141d500c003642900304155031b40b414007408030460707401d140000c6500384100c00c00306031001101551040500044049140c20840005031201921000b030180511100b9400c54003c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 121410377 1250 121409127 121409191
    0x80d0203181209030319051306110601090207080d0b0604090603080417030405031905031c1a120c040209030109060c050304110a0b040b130801020c010209120a03171e0a0b09 76
    0x101d183c6d602c0ca03402d111012649070107007034800c0083d15580e4a00080041d0455014440540c816065800580e2150610806da10071030380001c101d004104100c203d1550140e10000c06000300402c00ca141c1b6588118141c20344c0c40341e800c151102e2400040801c4172500001e0300d101c1c2d2041e00006141050728007070000362984071003d45107090202940c0c08404000e018800c80700100440301491034030b400d2560300400280003e1090303a1107040b900100b565249003a4602030a413240850040c502280c0c0308040c070010390045090380d0740540d00c0f034102c6c0b000203d0601814900104c0c40d500d01d41c030383c6481d00b001127000a0010140740225201fa1702488400000c2d000c55003030710002a00383c0d88d90b00000c8000c9080d041290b01c078201c035500c0880ca0016408040d001000c4104c0e00300c4098010340441600b4135141ea00c50000140400c41341c820320081c10076007407601c652000c0760680c044003202c0403610001c420041140c01c0344002d81c1e40c900302c2c00076240029000d03400000c10b0784500c211000f050000703404c1900e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 121411627 1250 121410377 121410397
    0x70302060708190906170903030a020d18051f09020607030807020a05060405070504140f0103020418052409030306090415091b06020105130c03060207080d02031812090303 75
    0x3541c030103004101d400c55910324103a42030100000e5200e03a005181c4115401000f0000c3c1050303150310800307040341c105140102e4290002e541346840c1d81940000030762050b03403880041760300c03200c006459061070242e919000e4000e0018049280c07420140000c22080c0c1d98001c50b40615000080003d0b845110650780c4103941401e00e0a081e17100c0610507860b0401d1628024414480c000c2004100000841c6940468dc804c0d102401007002840e010180600b040394a4425800303500c004101520b001d4002d50180241a00715128a28060b1200342c1084c103220702c0c0c291342404001c494525050030344160780e0b001507110080d50540c00d0850020326500c0000d4405098041c01c603002c42013162190b40009445e9902c04146082100106c400003d0340060344201809946080009299100c03c4240ca00d00198411500200b050840c3c0d00ca40080d00320000603280118180088a40f00081e440114080c081441101d00c071a0240c0c0c1e01c0c145007400c10751501c41e4038030086c1310031440c980300041640d1640301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 121412877 1250 121411627 121411639
    0x1410080a030f05160c030b0a06081209150a030203100f0e07030b060d090f0506060409030c03080406020405130207060b0a0b04260105070908120301060504030b0907090c03150f08070302 81
    0x9603100220f4140c02819014400c502404190030704105000900c482100c3c82990059420b079240401c1600301d4603580b145210a03000401003100c00130300d11000f00342c039240c0200001101000940b00d01016000101d1304004268004140700019603032202620007441c110020361805170070300d010301c4480d000c040d1000e8185a2508260b503015074803001941c1203034849000802415850742449000c03c49006001d6815001c0e0002061460030907015a1001d10f4144d154003c03000d40c2998103d03050320008000b50307074080d030a000c0401d190307880038201d12040003410405a02c0d00c8103800c05400315401d004a59103d011401c0b410005c90b0002d03010b9070222020240c400c240c126030700801c0c00c281901881140c006529120422031516007010826040e100300b802214502c0210070b0001f9400d210a015020124400340810000280e5007220598409414010b80300590340d240b030620180d941c00000c100c00b1a440d50030414400303411031550f40062001100424040e440c1403052910343c0310a01001e4026130b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 121414127 1250 121412877 121412897
    0x7120510060f030603020402190809011803080907030506010e060102010e0c011b02010207050a1d090601060e04050403020f06070201020c0c0a12060908160f020405090c0916020c030109061410080a03 87
    0x39001c0c1e84410005d54004e482950f031a010000580c807001c4078118113078049a28032000c2a06140144154100001d02e01041c0007562259102070380c40c541d005054103a02e00c00c1c0000440061000d0001c54000d0140325038210340c5042c600b0001e401d60707804443d000101e0b4003c2411f16503681e4013041c4807006030051003540d10303c00444d00040f030411540d07070070081d08a800400c0005800001e64500601ba0190b00c07244041c0b900c6455a20b603d505081c0b06031000651100c0001d12146003591000c1c0c0c001e0703c2401100c240a00205189007090800c90780200980d502140300e00c5032001c24460b0040b200d904862041109041c80c401455070240694023510f0076554204940030410b409048070382044444100c0c41020b001c52900090360300c60180c04074022410b1001091070810f0010700d54a4074100102250500d40d51803c1ca081170342d124110800451049680001440e03c003881140d1846004c0c407004219840d2101d0385440041001e44104802c412442c020407a10802040d912400ea0749442c002d036030a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 121415377 1250 121414127 121414157
    0xb0702010603050114060102250b0d0603050d0f0f0306060801170118050313050105070b060d0204020906120a05090307050303070513031406090106090506030c010c1e05060712051006 80
    0x41c0059000101290300c0c112808000456a1103050312601d026805c6680041d0604a0402603418213041e0601c64200c0700c106010f444500740180824101c450710004141c0d941e43c4900c0d107821903800303000e0080340000300e11082542c0d2000700020748031464102800072500c2c0c648000d044900500c1940e03400d41052200d106411820340080040e41090550905061540d08283d61a940020000504692058400951940107900351030841d90802510380081e0b607180c0c10310484500c0362200301d90060307081091824036664030002e0404440c1500f9220210300d48901c000086980c05803d00115510502482c000200b0010480760321080fa0301d0403a480381c4904510a01d12404d0350001070018913500c210003407040d40007500900c640b1849000348145c81e618070551040b900140d40740794064110080407041035002c1c00b081902144100e11101c1282408007101d040c2105000b0304903440d4000d03a083c4014140d12455034042100d10700002c11050801d02e0802e941d000043c482c0f9401e0100748101c040c0d44c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 121416627 1250 121415377 121415381
    0x7060908040302031501090c09060e101e030e060a020c060601050d06050604030b190b030c15121608070305060a030b04030c0f050115140a05150c030c0c011707020a0b070201 76
    0xb181d000d41110181c02e620880761140110034010034010130f10f403440d00c4004030300c900c074003108482003512482d0005d10110107100900012032100d07401d20144078100103015034031a00140304210507070f90000f844e0071613110b050304044020742048202e41c010f0028104141d0f0201e10b190b044002400e02981d03136100d0303100c00c001400c0254070895000c200410000107001110001f00c3c8107566001ca41481180c00c00c45c0d410441d40c0050700c0a401d94011240200981400701d07030710f048019000e44807424400c1e00d0751647c44240c002c80c0d81220395041d412603105600c2e08400001c0c1c12101a05040c0081d241240c0850500b642601c000340204245802180c01c3c03502629040c0e120703540100c0c4c080c031010388906203680078045188001e42c05030460140010914501c1c0c490310b01d075010060000322031602d03000401ca909a5582043c80020004128449000004000a02e01d050300746000c1c01c45180220005010050201103240860302c24108020240360b01107401e80186a01c100740000645441700100c2c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 121417877 1250 121416627 121416629
    0x6040803070810091107020a081c03020a030612060926030c07170703090e07170f06030c060a0c03030b0103050114090702011805070510111203070c0804030803040311030f0706090804 80
    0x4241071034170300281440500e001c01032003c58003d0301d80d1075610341d940242d0b560ba041400c009101d03040c101c000113513105100341c004200f0310000349000704d5402d031103600400c684910100215201995903034944100180b46c00c2c940d8840380c0c103507425030002d421075600e6081840010441880d10500241071000c02c004044da0701100043c515019440708550300d0040c00005a50044c40e02c00c5040c01c000581c8a403040042404a1a1025a24105448440d4000700c52440505855814081e042240d40c0c6a2104c1c8054020042c00f6501c130800c442e0541000340460b246002c8090415050400510140521076042817205070142c81e210340742d0740c9c2c1400407801451060300b00840048c031840818284907001500b1010389400700c0f00307640e0740340c982c05041e01c1c0803406112a4109404c1700035240304040070380026640c04031560604c0b0030060155541d201241c1e0180d0001c8881ca80701005004c1419031001c2e06064841d1224029881c28820080e01c158034011180000c000c5500d48140104000c008806d9030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 121419127 1250 121417877 121417889
    0x30f031404030806090a0506060933030f01060203031509070909050c070309080d02060708040503070f1a060a03050c100504050a08031207020a0c050d020118062006040803070810 78
    0x411400c10740b40040140e0010381d4010b1040480b200803812000040c8107250007000024031503440e107a0800b05102105d0b040e4020300c0c00055110004040680c0e10390401040c0c0c1500010107644c910708444100f08080040c0c1101045610610800501070440c4480c4d81c28000c04036502a07030703965030301821580c040007178200103441404e05003444101c034108409004e4003407094a682c005030ba01c03140c0440c0c3d0340315882040e00059200b1400b24054900406143d41c0080c080d500703591401d0800d8a0305a10a905071a085507290001d803414251481900c106076000041292a286040d02d10380312a0341d08e0007178400b51485420860301040c0b04a018800f1a402440017030502d07040d05030f88400e0b0589035005544c1100c080c0c050035000894807440441c40744c004580c4240d520400c47d0a04042c0940407e0000d0200d06001040d103074040550502070300a001040789540c0c1000c0300204c20003a0b10142161003080940380e200c4000e00c00015041c100f501c2d4840c1070362030b210a840e90340148501c00c0110b40e6000c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 121420377 1250 121419127 121419161
    0x1a370903050405010201141e06060d02070f060501210b0601050c01060806010311090412031a06130305070501050a0503010e07021c0804030e100c0f020325030c170604030f03 76
    0x1481010340020260040380e42c01d8001300300d00200700804400c5c46404480d16a0724141042140d499030a40c5084107130421805421603051508001c580000c0741d0026800b41c480c000445803510801c4100c1c0a1203026100d40030002025010a940c2043c4d10107040600070000e98001001904691152040d02c0002d03a0100081c8101035030b030640070340c80d02401e0200380e450400d042c003c141c0c02d040066002e800386a005241d055000441401103000300000004c00c0a45805042409626610000500100d502201035100d080d451460110316010091388940d06129003801075680c0d1700d0300001a607044804009403810341d035a9401c0101d00302410b42030b400c0c24112080051080c21640496a240305070301c41e4481c0f01c0002080c0702049920f20500c1c41780310014004050240001d2070081003807881d548042c04840c19022801c1d084181061f0f803481c0040c0c20407042c8410001e0140c221108401094903581c60500784501d00351150321200c000300f0140a2114071020144041e201b03a02403000c0b51180c0d111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 121421627 1250 121420377 121420391
    0x60f031c080f09160e06030a0f051614030307030c0215030c0406090b040b03040618050f0c0414091c05070818010e0f0f01031d0706020a1a37 62
    0x101800103001501c000301c2c510902400100c0603480018020007082c10682240d80003840c3c40d1800501001c001c00f26a0140100054800003400718004841d0452203407014000101c00c942080308001401d42c8400002030150381800010307200401200c00103a01817a00344e030b20241600102c0c2400e00e03200c441c801d144000008101e020325070030000d00144d070f20700c1e6181e4080c0303590b54280c1040350086014000c004e41040000c02c0000c0c0f805d44c45884c0c80d80030704100c603880300c0c2151282818008010154211030f0000000b14440b8501407141010100c0b100200d03020505092010907504c101440407074070305041d41800c00034442d002c1e505030b4525580c000c9220795500001501380034940c181d0218140810b186000710242d9290400004c2d83d03468000c0c00d4070401c80c51613401107010b01195442c911101a84a1844000e07100900661010340b8a68008151150442c900940d408c1c0101d4030390001006014140103480c0204802005074200704604048992504048440703008280b034050703002a464128 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 121422877 1250 121421627 121421683
    0x1b07031203061a04030b01150309050d030606020d080103080a050918070e0f040e101e0e060417070302060c03040c0e0f0105031209010e060d060e0a060f09020a0206060f03 75
    0x2400c1074a60321008020543d010480c25480341c081c5000042c16001701200500144211224032100c0a24524010407840c0c07507a00c60505003011280e07030000203500c0300e00c140101c6804201500c40001c0c40c0c90000080e61440c2c4400107503000f82c1400d8020460001008000341d41d554049100001810368900e00505080703401400040f03003c203146004e40d01c6200c54481e21b01d824400c403080340c003005c03000d007005160300c0035080c2c0100800e9160030401d1280b1000741170800c0891143c0d206c00e81c1410014002820715003044007012440b41440540300c00100701510000e540810060f0300700418200c156181d840e10700d4841c02c0c00e04183c10042c40d010310079081040484c1300820440c100e034000c0e000c2d101c01c1c81501e42440081d11525198270302003010030320880024100b44006004820f415100042c911b40c460039034032003c1006441509846031542804c0c0702541b0000050700060080500c00c51030300714002806034960348000e14991188149403104c44d2291014418501152004480c1842032000c080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 121424127 1250 121422877 121422881
    0x41508010212070f02100b190311090604090f0b0402063f071409060c0105070906030c02010b090105060d06030602030c070c090b010509120114070c02241b07031203 72
    0x100c0700c00320b12080789001c540d006005214044100020340d02804010601c411907070b002d0b0084050054128803201200d0144554400101020718818050040d046643d401041001540900800c1c456440c3c007100c2c0002541c40c003a0480f00e43d6110f61218a1941c0b03600018500d03000d404a40741d070520500c07208034805400c4a5580704405154550480756021103032550b000f2800880e200400300e6a030066500b00c0010090180040541c0144513510f02100346031107a082d07030029247d50005c03400b0302505015403a014010300c80031452500c000c0218034480000660000030601c06e550040d1000a0428100700940d0068005180c10210955590500400180031540118030907038600012040204003100a4050301500340c1c0c0c16903415040050403020003801c0074003408040403d6585466050105618603080351003140c1c1c0361509042c2d07241500500c94962002802185051480011a0340041464090301d41c0000070000400200c000c02d15a00d1401101e0707007029108603032182da00e45001d9455 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 121425377 1250 121424127 121424137
    0x31c0501060f0c0809061e0409060e0a0504031b0501020c0a0305040501031401120201081f0f03170c060a11070b1003020f0d0b0703021e0a1e0912110415080102 70
    0x103682d60150412118000c40c0c0c4010640e20003040ba0700c08100700056450560040d200c550062940d07550740003182d40410b50b90390320951003615042d858620402c603a1140300401c2303502c582024810f01103854196070040039096400c54a950340d0166500450902034258140c42010300d41000300c41a01a082c100034000e50001e11403140007a0904c81c15644141e00420300504030794a040f8045401c400d9a4010340c0c915000a091400c20130f50042c404502c00f9403a4400341c001c03d21034428882c01d904600b400d1280c0500d1802034044210200801e40e1751f2076000486541c8001c1c0c1c84d5000481c5007075406010a2889803200141000d0048800e01c5008003440580e1011a40b007154180050300302d02c41400f1158261080103801d203040755000490683c020f4005081c496081008000c800c0703400f41a4414681085150400181070710703101c2c410103111a050b801060405041860501e0b1506040403200c1e40752007002445400221140348803038550707801c0001c1010b4000c8640d00382e55280d4200342e0003074202e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 121426627 1250 121425377 121425389
    0x11505030f010903080109020a0c05060c03040501110304050a0f02030106081002031006030e0303221205090901080c030c0d08090a1e090c050d090c05030607110f0303010e0711031c0501 81
    0x245010454003901c0511a1104407a819142c000440e07282171200002500012160010710010340380110020300b05115441c459181d102109841c2d00b8a810b146d401c588807418104042d501c10000e0001180000504c03040d42d0b0f51003226004050b01380c1c408139024107001c4c0d0040c215803203041d507454041c2640c0d401962141360400c00003400240c1e0f498040f4161241c0071803800a60f0410804914291071903a44184941450b540310503481c04142c0d00d05038100304c201e1006c000540c0220f148055840c2a1064900400f201c200511706504c0e043e000a450302c031100c003154400c980100616040141403c10380e07254040080652040c15a210a11641e4000a0b0f2210803290b03404600840d40c0c2c2c1c114400c1c0f1075035200c2c99032807a09092070301103290000c145a11781036440740c9602d14009141c0d907040201a00c12b11059990740028004404443d190540b950a20101b603042440140100c0080e0382c4615405081c900d005010000056007103804e5108007020000c00951040400340b181015421082c12161 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 121427877 1250 121426627 121426633
    0x307090303020f03030c0a050307180e27190201020f0d050307090f14120c03120d20030a05040c0e010609031a04030212030a06091406040b060a080115050c01150503 72
    0x100107122291240b0041b601202c80c42c005000b04030301c5500c80c030041d40c0e00500b01c1c200905e0044a841e041900402154003d1002c4d0311880300304a208000f03040070804070300c019461206201380c1c0f150184c1c0c43d41034014400608100070740352041960710030403406905102c0803042d54544144880d000f825a8011904500403d0b480c03000040c01c0c5c840c05583d64200c0f4404490f414007016501c0821401d001c0b000c1800b0a94442d400e10200c80b650b00303000d401c034a80c91004030281d440001a0b004402e640b280401c3e011030000401a01c3d541e00c0c04401100e5104003440c60009107540c49242c00c4040d809a504034140c1c01031110b002040e0355400c1102c100541c1e020310201d01486246810b80e402141c0101d400070b0050700101d84880206200e07001450b0020034444001c1002030b11120080215000700300b41a03a031144035400c0c00a142010b201754251400e050341d1070392815032104400f8001c004103108000c4104500792150220620400640c1d202c0980413000744450704850304015114149805403500c280 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 121429127 1250 121427877 121427893
    0xf03030b0d0b0f040201140d05011404060302060f0f070506190f05061c0c210c05010e15032802070b01060516032703030c05070b030613020915030709030302 69
    0x12030402080c01c0d0040d4000034030141039446001c1c038070102030054001c0703050000030500d02d42d50001c1540503242000303001000281c25803503c10300b00515102450401d008514141c030910150312100111807001d000751071490354551540050364a0b82c4a6410058242d029160070302044200d119404da400c2e1510801c107005440340e01c2d580c0000c4980951b5050b50146400740700c2c20001000404000100c3d00418503000201d03551030421034607102480b68010740402461441c42007056100241003e00340078a0101c0ea40103456001c1032074440248100e1020340d00c04400110804001c2d05c401d6210710224880b078080101b005c00d110081c1d0801102160780c00104000451400c2c412426140407950460f0402480101600c00350303246141c002582c62521548210b5400b03c0000098660045119580304522901542051170501e0429009098064401c009101c201e9980742c040461802600d800146d90700c040741e0004103030441000000b8130340c40000c0304005045805c070f104001203e001342c01341c4d135100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 121430377 1250 121429127 121429129
    0x30112140c0109031104151508090d020c01120b0406060302040e0a0b0102100c11060f19060602070e06030a060608060a0e060f011514070b060f0607050c060319090f03030b 75
    0x241d4040e240c080d0000740351680400105001e108010180d0030050030002e15200390610004002c285d07a08004100c6110900035034840b42c0c4050141c1e4801300d554080c0800000001000751901c40f80702000c3d0400118581c1d80076421600d600440e05c00000910801100750b50303c1026010b5003043c8034078151240708030001400801e55014488013550142d014240300e400c81c5039004024513216091101300038000b800b078400c550081082c02d0003000c03440c000b0340980c64511050075140c0030b4614915240f50500e03108108880d0001502c00541e00c051007400101d580310008240303040310200c4041d109605205000078441404180203000e810244010320443c29034101240da1104256094038030944250700400102c0c0e500501c80030010f2280c036140c909808034510700032550304810740a4941c01c048406000b43c030714196040c12500d09054500c00c2c02e003c1103488480d00c950b207042c0114010300000002804809108481e01c2d00600b4822040240210030b05004d10400f005200840101e46001c05288403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 121431627 1250 121430377 121430383
    0x3090803070c0611010e07090b04270201081801050a0c091202151b0f03090405060d020d060c030e0f0102030108011104030b010b07050a06050a050f1f14130203011214 73
    0x1c19604000c0c2d02d20114540035040f24450390368510703100d8039540c51401005400092000030020000e01c407000c22441c0210080108540c607186d000103003145d403c0c00c100e60105500c1c80108000b902420a80d2442c0d4401c407020200c01100100500780c0d518020400840100c10ba100400c0556282da031024071584840c0b10414030104414040c1d40503030b800c20510790981d0f158004083c10b40390b4480000e1242503c0760a149800c0303604a0403811034101080b8600f29041c584180ea03840042124000c1d00000e107500441d0f0750005540d0090300180d1941018100580642c0281c10456656011510041d82e00c8004c18001c1d0801e01038410f1071750030b0460741c5900c080e8010a40b030550781c200b40030203600c0c2d20b4990a8000b55204c00c0c421200d034003c0391480c20100e54580725061180030881800710b100d2500d203445090004000342030310300c0d010310380b01051150260860000207882440a03880748513042c0b8400608943c412804041d255030000002180c8403100041910405100b04580784070201c000b090151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 121432877 1250 121431627 121431637
    0x20601090b0f0901030b040309140f130b0a0b0304060c0302250c03080c250302031e070302090a02030f07030c0e0f0d080c031e04080d210509070501021e0a1202030408030a020a03090803 81
    0x1c0d01010303918030701208cc134100f240141e0b0003050321400100070140e44081384e24601281c0c8202e04503000032007040207000c0140124501c02c080b5240c214540000807029540110039080f04000d048840c0c9501420400410002d2010f140c11100450722000d40032403150f42c0c0d54103030a1a4842c60075110341c90b020418003403c00d0382601e0340100602000f40c2002000c0c1680034400640240c1c83c0b213044030020240c2c4031940c10f24000d1620700703800b60f601d191100603c1c00d0b0100191480040510b080140100141c4c09044c245080d01c0c103c4003e500c2080e01000681c9118a904002d800ca8900088010740302e40000014032601001e4948101000419101c001d0140124400e4403400d4100045404805200301d915004c02003480c81f5400444100300c00e4581294401c85400c6c00540c0014010b000568040101810302107540c8064480600c00066458440f030761074000800c22030b0407916040c890350007030040e10301a00300c2604a80d00c4102141c0002d5542c1465041900811548840070039548004407c90b2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 121434127 1250 121432877 121432879
    0x60f0e061506031e040602090a140a05090703020705030f0304050f0a0c18091e060b0f0607060b0622060909020f030f06150c0312010f0303020601090b0f0901030b04030914 75
    0x1e030480c1480c428480d499000070201042c0c080e19460150550783d1000da0301c2d01a6015010040c0c45140b44000c1c00184000d40d0000c0080c000655410511a907420001c1c00a5500c00d80d0101255120a04280c0207405082c0300205940804210340761428409409548201d001c2c408583c841451012038030f449207405140a80715400516040c0404000110605048100d000d000036843c941500d95100341c800c000e41003030290441003001e005010242c0108141c14608803804003a00206000054461003034600060055440d1046424195200c4042d900c0c0d9915000310049800402400c014171110940980004201039400201d621402413013a640e050b41c261094030f246480d5405036020100004000305e502401e001407000c0010520006032030842100c80c0199100c90f0918a0300c08202c01c141c00c466444040540200301080c0e001852078111810b00e840000c3c0e00c88030a0101d44c3c0796541004072500034034400000000c03c59030700110352140d0f000380c0e640d1204540701c061040303580001008003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 121435377 1250 121434127 121434151
    0x50402120a090f021201202b021e0a0f021902040e0c030304170105010506090108010501081302100f110703020901060509030f010c0908070803030c0a2a060f0e06 71
    0x495035001503008000d21401920010803140450303000401117250401250900d94540b031500c0c401d1181104401520640004100d003081d01086101e507030401800c800384c0c0c2d1010070782c80910501085038101c501180821080362014003004101d80c1d030507440594460006042d845801400620129100e0388242c00317241c0d08161690030307408203c00b80c00c080c2a9046240528148481c55940c100003c02c0240f5920690141c03942403800c0c40e608551701640014000c2c0350812a000050381e01c000c181d81902e5007424640282c0e1100c20128621084d40303400250420100e0045040c0641c1219103504c828146a41d0341110545013160283c85004a100085d04510301d02c0050207524010380141034209009001c651004804e0b01d440ca094411282003840800d1a8110502ca030303c50912160300601f1b8100029803a40c24000d0b003c0340c140c8202124142004007512a180034004182c90300c240614440412b55503003000c130b042607001044032007035055400340b41040c60302d0b000d080841d820348104852401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 121436627 1250 121435377 121435381
    0x13080105011d07030209090702060108010c02070305030d051314070e180c090c13030614010803030903040b0a05070212100e070302060301120201020c0d0308010e07050306100f030209030a030e030705040212 90
    0x4001030360b42c00a402c0c0b009060b020b20003504640c8554042503c034112542c0101844c1d4501243ea81c01c581b1004074100454008500900c0803903000001c81c2c12102640e00c0005895503041841000e40c420701500406000d02c50030140400c0701e00003150020744185501840c1c040d220354603400039001203240040c2d01c0f90088401e050b41c502d0400d100d20390062842c1d00c050301d0b141c2c440e80b159008201681003140c042c1d0b03079103905e650b001d20300c001c006014040c0500218511304020b603680d545da00a92140c1031814200191070070816100b84281c8208a50181180c40d0381845d04004a848640440082201c01c0c40c103400c5c2c0004030800030784042282c1c0c015000351b113541d08103a03004d882c415a5002c141d041d4030401d40c96045940b503880310b900f50b2a00070b5840107a25410280c0701d2481e40e81c040c2c80740003080000d209120039580d4082020340000f0709802c0182c07405184840c00c0d0301a0017000d00403a418000d010307070101859000380c40c68150610032025580044e44820821080b40200201501a007600ca00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 121437877 1250 121436627 121436669
    0x50c071e0c090608071403030715050915010306020c01050a0b060403030e27070e011706060913020a0504140406030b04150f0204031109090601080309010f090f030302031308010501 79
    0x5084481401188010800340c1c440b00400192100c5900c40c42059202d10070401550600070403a003501482280031354075044064a42540034100945010101603489000c100300800402c10029030240d20b403200c400941e588c1c104440250001c400207a029401e0000080a129451249000c5034000902d12400c00c0d007552812140c070002d602181d07401104480d01100400c131100400755207000c098580c4500c0c1c1c42c0c907500082508802007101c0f810700030b041550f04011032600b400301c0d5100d0015650145c851a0410000f074914202711040c0f1121440091209100f951050040041d9080320004101603601141403004845061001505648000380440c0c009001081e9046540300340b0718002c03802440c549650012644142e1046801d440a6559080c25003010035249900c071040001500c00c03585401040c940700c4c4199030341e260400940c1600d500025016102c3e8102500500280d080b01503100d01d0065926440103240380108010b9480014030140140070b194143c84500c0e001c0418254944 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 121439127 1250 121437877 121437923
    0x708240301020706112a06040f0f0f060c020708210c0a080a0f09150c0318091e0e07080a060b12061005090a0c081302040b150d050c07 59
    0x1855265408204150100d0444d003d43e540c9041d8048526a82c0e1540300e9840041340586450300d1403c803803d1441109070200815040e52080d0131150008401030b141c42d04d124541c11250008154003006201182801541d9008550035401c40d0211a105500c61082a42c1c410385a5149103054842001003e10908c171300014001400c00079048812a240c9590b5411154122060303500006400300b500201c4594032548850080c00712815014103421060001841062011005014400b0201c6605906010041488003c05042204001111a0036802c40c009400c014108000b24109a0003081060003c1803440445050708028207080070039545000107010701c1490140d0100e00c940740749400d001d062044030301c0340280c004000030440c00d110070080d0242d806070400581ca40341050010703443d03800c040c100b81c201c01c5d60203603450300d0620351000802400c060091290000c05140350309101c1d01d040009800c01d00c116090034051075480d80c0e103a4a031405500000341c080d480c0c100c28003101120320 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 121440377 1250 121439127 121439191
    0xe040509010501080f15040210090f03080d05070306140904020120010506040b01090f1a0d141e0c0a0503090304050d1506080a0c05060d0b03060702030a0914090f130b0406020306010201050708 84
    0x390400b10ac00c955240d21400b40820203500907a01d0002c00038903640d2448841c42507603405041403d00b0041d40f0b0408805071442c000c004299406006c0d090045030075607014807860524920002002007050904922282c0608015a503003402181080c42403a4150f0003048000f0640d01c2da8852403160518201d0522814132000420800c0c03a0010400e01c40e1203251401614000e0203030081c2c05446061102140300c00c52101c4200170501c41340c4000b4070490402c5c240c01c031080001c1030304e0f00341c0c0c40f9220781290500790320482d03000c160700c4040c5402c02d0003081648a5501c2c500200d5410412440382c0d9072000c40c1e229500790718000c280003090f140c103110500d0920080c19503110070590000e00310610001084c44d184090310301c0f10250f070011401d4200c50354094844000703021000080d81644e1502000b203100b0440240c001120280e00074000b80c0c3d0307100d400c1c2448c12303142d07044501030100f810701c1d040c080c0096105440341c81c015420f050002c3c0080d0b006e060554000e554100c08688401c400851011400c494 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 121441627 1250 121440377 121440409
    0x90403050702130c110a03080604090c05030709091e0302070b0d02090904050309120c210f0105010603051005030105090604121809050a0b0a180207030e040509010501080f150402 78
    0x244030760000b41e100ca9506580051451500180c007030307800800030f40a43c0103100c512940b6400b0803414030000f076000e000c00d40c005600b5500455a000c442c0346c1080da204c1d0f55006203426200c0d4040004005030140c1100b04054002e1545408503a200000706070061403034080030703025a000307100401505c507a020050511700700c0c6050050812201d000060261403007924142c4d0306038400b02d0000342d40d2030050200040c1912141c010100a160400445c4a0000445c5000690300d400090900b400006200441825820340000c000a41c3c66503005001032105a0325a01480f00040006c01c1c42d060511801d8000c10002c4000c02c2181d849a440c44100c013824048401000b140707080b00c00c030160b070390082c0001a00642ca0085007a10780150903004540704489158031404001e4000c01486aa40805042070050540301680e1800703175007410f80c2c0030031a20006039000382c600400c1044000045d40f0075410788480e00d00b0742d0700c266005c412403aa142c5584c0c2c940310210111030007080040c5485403c41602d514 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 121442877 1250 121441627 121441637
    0x804050918030a020f0f07081e0f030301060c15061d180318040b10050403030c051906090203010b1509090a1416031506090b0313020a15020105011a09090403 69
    0x1480007890340c00d5030001d1000c9000340e4483c4010a05840061000d07a8001c407a001c0100b48141c42c1500302c9540d007071004a6080c09c0000307a00d01d9030f00e80300240503160140261504a035078959560030010702211651000313541c0c40c501c42044000710b4803e80501c5085500c3c1105038564049003241903000c240d0041c00000c01d44618058400303160f107050001d00400c82c000c80c0403070320002144c4144001c0d0b45481445030322582c2c406080a08180d040420340c2e080e660145040704e0503040303030303d8082c0ca003010400c01005030240c6c01011908111043d089009442d1080d00207000c2901d50704240260f0043e554000075440f4800d00090b00c107406d02c0400e06500c281c60f41004105003041e0743c035000465400b030310301000c0340c40d0040310318901e181c05000f031040e80d0010312034111809182034002421840e942c025030701316039800800314194001450f080302c40039400800c40b480c501c2d81c0e0000fa0341d180c0752015080e00554280000002d4041d4240c816016003040034060a1811007090300704803000c40c0060048003440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 121444127 1250 121442877 121442911
    0x30c031509010b040e01080a0c031e1a06030d08010501080a0903050f04090203011a030403080708040303150e09010b0a180b0112140403090510021e0f010e060f01050303040308040509 80
    0x350712407070315074002c08000c0c12076075030780c0c1c20f00050748046a03058010008691000070386e40009403400c800141201e800840040c416010108074605e03095000030f0140040c2d400d410540300c071098502c0fa560050000720f00301d0b141d10101c103d003031740d0740780c424400d050210300b103000091203080084e00003411081c401d1030038500d064031400420081d500241c000808941d804401402001c907100e0302200700c10104070500742140f503d43d80c01061220014460410410110042003c141c007a0b00b140c244940f41034441d0301010344510803139420341005c4401d9450b542c00c0c66001c4030ba5003020310034842500c450420916150f40c09510020160102160142c100a0780d0f2910b082c81481a1160505c2420f092502c030380e040c2030609004180c11041c0c1c03c440c0c410030701c801441c104290005110360030328650302d480094110150150504000001c03c44602950904030007242c0d6580220703246100b04200d0300d001c4816600d4000740b5a9070701840c0401040028208018000da141c0400081c0e40020360082c104840c0e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 121445377 1250 121444127 121444129
    0x17040308071b0602030903071b0e0a090f02060c010b0102010f0e030d110c0f030901080a060501080609040c050d0b010302150403080d0e0a080406030c0e04050603030711030307120c0507060311030c0315 88
    0x83e40200d40c6c03081180c0010880700c08029400b2540b451420340a250610328904205c5540a0f4140c007500c0c2c106a03e940b5012030781008058103940c81c045800603c80b580303a0035030043c1d050190522883c054019460000744000b410b10510030003240841c40c00042d800c0c050b4448030381d00240320074512082c2031030003844040c0c11148104454007501c43c0f000003450f107464a0000140408502824549999080c404140800c0c1d90000b52141c0c41802100c0c41c41c1c11b5140c605014180301030b140c0119402c100005070301c1c030034018031280045c100d174401e4512617882042d5040c42c410345d010f2070000410034502005540b01c888640d4112a650300607210a0795040c0c0c503039035208401507201e035000c003000c01d80301c0c440502d41d59080f2140745608201500c1c24032031450140006134692250500c02401d214481c0143d0b0703200c0d181001512499a441000642c170814500c5000c1d040c1010410115054410b000010600750303c00c1c040c0764082054000010b0541d21031181c4d03c841c54200521070701800c42c0481c011145 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 121446627 1250 121445377 121445381
    0x1603080705070302090c0a080114060304121403100e06030a0f1b0f0617090c03030d090c050603010305010516020309010f0806010e04060e01080c220b0604170102090117040308071b06 80
    0x186e0304a840c0b0759960031600b200906600c1c0143d100181040b4000c0001322640c880c9400c0325849503000c0e40c982c80c0700308002001e40d009075054070f100084450210400441c000c08244190a40b1303c14961103030a6903e4400b05551080c030400700400150346502c582c00000c0d11140c2072100c0f105030001134078510f9100c1503600300c1d1403801d43c09400043c0128000802d40c1441010040e00054030b0380181101d91103401c0400e40c3c9100301054406091b58580c002e100f404544010800a041c0003012143c0d20350352804c042d800381a0688661007540c514502427404240000119a01e030503041c0c44031540101030700019500345500400c41030601c114904400b1050342c49100360006095400d041280a5052040782031800040380301d014000c019911303150303d02d0351408120441031402d22201040d440d0340c4002180141c080c0e94080305201c4014240d041c208032042d00980302164080ea10502042c060a60300751085805940182c0824811404a00c01c50b00c00c5185c02004074002080d41205030752035407520f00f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 121447877 1250 121446627 121446631
    0xa0b0406050f060103090209040312021c0c0912200109030210030f0606090503150604110f0c150f0601081815010f05010c05060a05070306050414060909160308070507030209 76
    0x66669650410021015400b04040360000001e1030704000d2940c040e030126942000160000d07040c00750941c1d5088203196941c0403105140c25008451009980c1c03c10550041e14281e243c0034049aa212008100c1228408210340c8098000c0b47c0700c4040305084c52000b24480c3e059400c1810414156400300158541c04842d0040b041c0340d5400291003190407890310200d4020741c10132800c20000b01010045954000b500c2c0c101d115060440703015980f0b0303c4001034000c0a00d030720b14006000c401f0468450200c1604040e2460360030314015640038192642c581c02c040f003800c0b20030a101d95079000104605503c680c82856111650258501c181007545100c1480d1245458801d00166420070060100003034488218000f0102800e0546110826503a0343e9140e41c0001d0040d0070046d9a540001d0015100f0313000310700200b201902c20007400600001d01c8500010448016001e1001140490900c8400150081c4119045451890600c1c00e5641e0b46009034484a02514580324450012001d62780300710401d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 121449127 1250 121447877 121447883
    0x106090903201b1219050703060501080105010308040603020c0106050604180e01090807030c0812070509010305090f0613060f05011502060702160b090111060903310303030e0a0b04 79
    0x40c4280700701e070064401d044888001c40b4480c1d084004030000b610050032006080e5041103403455405550880001c0c501810b045020b40c629800c0c50305402400404100702c0c050301d000310001c1c00340d6a01c9404240c00c0e02c000b0302c00101120f1003004200012440b96000d0010351030104004160740765214006086900035800080c881113030618100c500036828881c0310030f01d0034650001d02c0b11040544460481d80514140a0f0501580092000c1000340c000102c0d1180502020141064282444024001d07008440c4440c0400e20700004518036010000708400043c6c1d03400300030400395039440e20040b1f20b8070102c2c0040b00c0d611b49606c1282c403500400d0090720301a10f680044024007881a520007442d24034080d11010940d040016000200503800703131040140e988a203516551004e516004031440c2d10703e0510782c00c0302d014410a10024000100083c0010005010803034003402c15400c4041000d4003050908403100c50382d200c2040000d000382c0080c04080400002c0e0b846502094441c0d046044007100cac21 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 121450377 1250 121449127 121449137
    0x10305030a090509040b0a020f04090c031401060e031b040b0612040203070e0c040501031107050f0a0311030a120f02131e0e041101030b03010204080d08042307030609050106090903 79
    0x74040c4141e201c22040000d11003124031005604298449540302c801c060100c420b0650005040c42100740441d017250002c00315a402000f030b20911550040c0140041807031100c04000340c200024048d44038501c94050014010040c02e150b10303125010b008181c80d0042071a0704651904002e0817190b075081d000d004100510f140a00d401e00d094070415092107950740210596090440500c60b04500c14810303642a20750030300b80020f92041d8482121041d0003600c0300103115209442015800e16008288104c03510321a4035909403a0201700c1c2c2c681d44074001d4030507170400510200c8c583c0c9007016458004115000c00d00e400185800100d5a5a01d1a16010b0700b0000078000c0720b0700400c0da0102c03c0e040300030051590031007480050601303643d401d0030104d07401d44050426840d0030680380981da0a504680040142c641181c1c1d02105004019006500440c2c040d110040002010481095008410000b2035a4103006d0a0b0f020700b9681d0b4440200740320b000c00c3c1e90540d600c0b400411502450b104445090f8080d17268 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 121451627 1250 121450377 121450387
    0x40608070e1e0118150b0708070c0902030606120417130e01090207031413080304060c03080f07170415110301090b040c02060a09060207020907170f04020102151503010501030503 78
    0x100d80002c1c080e50305a80b4080707607010040024905034003180800b4460340c070300428450881d03480b41600e0100c0b604420880c60001502c98100000e000061140c0c034407451034140032607903136480381040703000485401e50040e07001c1020f420b40760040041c50783d100d40700304003a10341c40034400078000454002980e4030382c4001584606200c240056002c850040c400c1540c154034100c0d07182e4001740b0795286040c42203101540030440749484a01c04054402500c00c0e138086a4503580d840700c004154034000c1009801103400315003c07814200f885610244a00c0880e11059915280b08038015500100107109a80e41c4402e24151000c84266004075182c40c1c078445545034580d410000c0d9007046950300c0041900c12132405849103070140d004104103a022070000320004075000c070750900d24080d101d0103034003e500907461001c0100668200d0481d121124103015204001d03594180400c001c2003094030040d0140c1e204161000c1d0564071803110341c2e40405295151f13503141c0042008282500d200382c004503810703040414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 121452877 1250 121451627 121451641
    0x705030a03050414120a03050c190207050a0509040515070c080a090f0905070e0910120f03030b18160903060507090305010e010605010509060c0309130603020f04090308070806040608070e 82
    0x4848040030030000175040c9401d030703414032070704030b00c103901c018414144c80340e0014615400d22000e550104001d0400304a45074280540251140c4c40b900400344111101c1e074000c11141050340d640303485030368803600a184400c4400d9507800c11010007000c4000b0081480003200c001200d400c0549200c05054864550040c2040700c0d40c1c441c203d19801140d80e0714508410404002e030b000940a0880c5400c0d507031a98540c485070072114180384190000a00d64109806c0e10007003020345003074000c030207000350740c1000301c40c415400f0402c0c400d09030a10702d15410b142002082c00507070070062004414003c1d081c01c410845e81d950f501016524100c440101051a200003041441002e00617036082d02100002080b0882c105030029155002d00603465010308004074400c060884108119464800002c040001d6401d1402030710300038020701c0c04201c4c095001c0494031440d0341407500440c042c1c01d5042d00c0b07032411661100e600700c402030001401654481c0d180d8200140e0700e0303c103108840c06040c0e008107190312440c001d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 121454127 1250 121452877 121452893
    0xa0201061202011706010e0a081c0c050607030b0420030403021b180a020d1b030b010c020d0b0a090606060c02030601050306010506041802040b04090f1815090501020705030a030504 79
    0x58024a14107114405520051380c2c06800d031525504410708030141a15031400407902d1031081102a50030121890000c20401800285032901040d4441c611380d010303e41c03030790840d0502c82d54a4020b181c0d52241001c108414040d401c646502170010f000020381301d100010076540030800c4c6100074a92440001132009069045c40296424142c640315989900c89040118101b001c515001c4d4445020810206120b00711a0701210500c000d4070000b8007208040c100c0e041002000c0071303100000300346015a40c405030b50240c0e189a200ca9001032194400a0302501c880c13800d290002c100c840d01a54980c041f01c00070f0b03c1c40c071901c4054252540c5058204802e88185490840b040e004280300f940290b004002319640c0c1800c9905a420700700702502e5444e40414554003038010ba0f000030140410108010403109056844003851118132482403005030350300c1b0f503966902e041019005d040d2458580b1801d40d10442904080d080502c540001464910303e612980d0540c0c100d5448040001c3d100c0b403d01c000d100c1c01c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 121455377 1250 121454127 121454129
    0xb0105030d030e030a0e0112020c0c01020d0801080c010f051b0c19030b0610050417030307090e070206040201050a140711040b01110a230a05010606031a010221041a0a020106 76
    0x141030402074043c044203415030b24050800c0c8042040036407601107100d64410034810707100300c07524041552180003800240d500d401e480301c0340390300500c03071940b000d071403140303c0d20f08a812196604082d10714507000d0b4004540c103541e140024418480204102c1105402070082d030711520031b169011740000018641004090341d61041c841d0b50801682c581800030410252480d508401c041315142c1004c00c02c0003003a91280a60b0780300c5a402d0050807481805500044010751040300d8030b40d1000c41c020f4131070381d041e03400c000b0942e1124016400b86000070300650180c0003d080180c1c146c02e0a50407110710303e0300a4840c0d401709208031040303907840415603694103003070284506000b400d00b026401c1002c0118500e9032900c3c008005001c1101182c85401c040c018a00c50301003442c0b40340300380ca0410605050640c0640003920401c0006403a1604025610005071554102950164041c2c11982420001001c01300700c804107801e056241040001142e8030a804680982e2400540e800e0711083ea00801034212009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 121456627 1250 121455377 121455403
    0x7120501090212010b03070c0c0609030b0a06031109041704080f0c0a06021f09020402070605090f0105072f01091202010c08040c030204020703020c03100906050c0a050a050c12070b010503 82
    0x140a041c0034007803021140e0381034400503542c11b510782e602e031801144c0120001c440541800381e00400498480d40c00386403407041d039005c2c101c1e8002d07540b1107407690783c12909a0b10000c2c04031550004002c040385880c0345003a402c41c2c024000140e4446120201600c123a00c0f55204401c254402d03200d030603c1d804180010704582c0000c65005003400c1c0f4194010351680803140c01400003071030060f400c8013005584e600c610b02503900540215241e01c16868140300030101039409a249118503002c1c0b00c8000d105024082c4141c10329595034400f90301c290020036015900c0c10340303004222036206581403945400d11542c0b0390907010384031182c030311191248040d003120b21881104040000d005c0c20440482d440380c08002c116941560b0040e03a413800d130300f401ca0070100740960340345d418001c0e903401d0400700702c0c2c58100c0341c040c5008480030400c907201c0d09011021031143c0841840842da0030301401c030020f40a0006800e41c1d078000340c06d40d0070424030f0b80504106988801021581601401d0050183c0d090400490300c003118 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 121457877 1250 121456627 121456631
    0x90924010b0316020f03040e0f090703050d0c0c03050105041101081b03070c06020d14010f05090919020d0f0303020a0e010216030b0601020102131805061009120c08060712050109 78
    0x4180144801d0a01c0014004000540460280042c4501c208080001c0c2c0c4003a0041da03448603191801100090001e90301d6074000c48540020900540c0f0104041048952000040841c228455425100c000d152641507e07814100000000820820b0165601c582c0c0304e0b0f101d10060500d0a0000350180300084c01d2080950007e19100c280c140005088a41041003803c0c607044035031007440e01102074410b841e54500000e040c9081c022010f000c1440b114141d808a0038156603094590f41400800c41c4100d552102507071202c0303030304c100c44038040c070300103500c3c1d0b0018080c004c8822480d220f0300f5002c1041e14007240003e0b80050807400003135101c011030004c09030901c06040300d22842121903070f1000003404050141e000100100e6000d07030003541203803804407ca0100c00c0c03540b40c1d9202e2010701c1820b4450180456401c042c002001c6140900c240003504c495502c07420529810020715031148036201e00c0c21191000c0c840c1021030140c50400c401889044c1c2c60740d80e40c001900f02031850050b80d5041c2d102c03054244c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 121459127 1250 121457877 121457879
    0x10504020127050d020607061a0a0801020a020a020f27070909050105130e1c030b0f0609060d050402010203040306053315091311030a05130f080702010e09092401 71
    0x856442c2e400c58104441040041c50a0300006200303128425000701042c0c909001c00401d02004904042030b031501300e82080205a5604800c0d09030711511000c1001038000c0201c440040c504000c0c040c0c00004046e00348540421540e1010388003c7c448204d0000f000c3c0000d00b008442e5502a003110f0140c00451418405549002e012402d04404202040003da40340e9618200c880c5c410441c20f0424080c02540c0f02402001d224081e008208802442c0d0113190000c91001180c240700e0704403028100003a101c145010765107001d903001000007900407411404100320000125140d80102c0d40070381c2108055118641405070300d1140600e403030702401e01c0f0100c0400810301070781e01c20000c02c00c0080d010031641d0b542c1c02e128001030b401001100440140528180c0512251410350f00910300c5400300303550400c180c1d12500c00a0b0100031144000a16460307107007030940001111107018000701c80c81030500d000c1d03441080c00080ca20000848a1400700d43c0314100d5002c0c00240380445040d8074046494050f895 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 121460377 1250 121459127 121459187
    0xc0603070305062803020108010815180708070e1f0324061508070f05040f0b0a0309020405240d020a141c211803031d030109050105040201 61
    0x902004040809040d511400034020703403a04d000d252000d00d0b240c8030440100c1200c500304038000d1018003081e400a200c100000c0b510010000c1c40c1c04604414410f4080307030b6aa441030f00e001900c42100086842d004802000400040c1009640068100507099091500e40071001c1c4c1004142c0a03003a1031300c040c3c204410004071740100c003440c4504400300e92650b0903007029000c00b800f810540d0700042c07007000000d40c0c40c0140c5500002c014064103090f40c0700500000c001400325008d000e5402401c1c0007070355400c010004580b04c0c0c0014100c2d0006070402160701f04aa40019040314000c544e00c0c010b2038100c0d200311b100c11524000c203c1040b07074200c0e100c680164050300452103481c0700340109110521003034016003207940e440000e24640b9481884802c0303040c50703603c0d00707007131460340b1500e000c03a103424102a0040160241c401e000d2050501c4a500203030300e185071003ca83d003d198283c2044c006903403280d1161140c8081c0030b00b03a849801540045401d080620004040002050341140c00d150f40e91908181c0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 121461627 1250 121460377 121460389
    0xf1107020112020d0b1201050907051008060409031202180f0d0305030613110c07031b080a060c0509040e0102070b070c08120403020c09070e030706090f050402070c080d020307060605030c 82
    0x9910002c00005885814802c00c0000034900c0003c2c00340e20056801600030015415004070380b0a071061003e0720151592a800d1003408840c1ba0f800c10081500900043c4143c18143d00c034030003039402464400d48004000c5601c208036485400c1d046480906d98000c2012400c000b0fa0780c9005503400d030392501c566461903d004080d4000a08084c0c03048036546c00080304008950462001c00c900c047c07030241d60358261240c07240c3e981c0395440200c2d20311000c109481c051101080a01d03040315946c10140803e04880d544050040c58000c445005224041c8900c0300107440c0d5200360718022245c02c0c001a50794401d400c2000b00520010084070800030400d0316000040c58020550b108a00a81952811500e0b540b4040c0d08103011642c4154000366001e04208c5110340c001000610b0000075029204015250034007241c0ca2003160092000301c403031b0113404101034203084e4020301100c0e014800811381c00d500e8405a6007024685001240140c0c00402d0040c1444828803540340100030440060504015000100301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 121462877 1250 121461627 121461647
    0x6150809070f1412030409060e0f070507020f0f030109080a0c051002070f080f04090203130209090c0108061504050405010801050f0705090f15090306180f0a02150c0f01020c010f11070201 82
    0x801998603134081010804208140c0707025009011082c411941c07503034200003948204641c0e80c3c0305400400046881103004200311048584c0203460120b103481c2250038460440d098003480d9406650380e200e101d002c0351407440900b903038402941d9000844805414418a4034039007a9007030b10010f104000301d0002402104100030625400684241c6a071f00760100364609000f294006102c241c00042085a030341c80070040021114401c07603503d08180c88802540f0380d41c000844916007c00c1070036010442502c2c00150388501c0d5004042ea081c030701a02c0708c0c040340584400303920064083e0f4582c03040c001a19550a42d8030f600031740d140380407810070030b801d030000381358102812960303004580d88185444443d50000841e4640000901160201d007000f003411a4003102048854030540a00003916207110f10204000400640051101000f503154604400903540241e412000c24490300340300070317001c140030700203811682400e500000c0d01c0096a41c0080543e4a003c0b4002925802000b8082c0180c0c2c010b80c81039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 121464127 1250 121462877 121462879
    0x307080307020d140601060c020a060320030a0209120d0806030f0d050d090503070f0b0105010c02130b21060610210902030f0a0605010306060506040608010b0d06150809070f14 77
    0x1281c44105400c2105508135407009a41d285e014003000840c29603080302d01c0ca6141807090300d03404882592940c1c118200e94400390320846036082c001c0c050011201e044095504090090001850100d4400000d03124500c7e41c030b000704858115040ee000101e401c04281a40944158081c25420100780380d480d884044001028051100c0400c0d4101c2c00b000e0b83c1e1118855591103004c40344d4515650400454030301d00c1e079204803030b4820003400215565100c3d0b030b1170315078a5502a0000015040c0c56081030080c202c83ca1040b40c01041d08011030700b5480200c0700ca0210b06001e200a003d46041200c1071040c0b81c006218502c09224001d048440038112a17104140580302e614000107520341e65200090030606040f10010039407040c904001c0511003035910060482c2e105280800c000d50351007050283c0350080d486000013040d12100100f20035224039004058040030303103000090250701d45400d140384125a044174000a80703040c040295040040001002a0001c81308010545c1c3c58406680e4404c01c0c101c140c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 121465377 1250 121464127 121464139
    0x6180610050705150a05090615010903021302130b0711040212010608190203070509121203071803050a0f030807020a0506010513020c1009030f032705030912100b030708030702 77
    0x402d041c05400c0c805040001c1c0b0400300503c10381084408840641010383c0e90304628000d05000c1b9100841d110700e01e0711219011707150310060616503003c0010310b02c000300342414100c2d0204402c04801e410301c00504040d00d00c0d0045913841e042c0a05006000010310400c05014520402407403102c0f0030f01d034106c141141c0407840d06038426603820076418822100d543c0307280d10690002c0b003400211a0840c002c5c0c082c0780c0c0d003555010070311a029400c55a56a840c024a60451601080400c641603c00c60b0410721607000c1c40500d56440366203580300c42c0b404101100c19074690f440900040c00305540701d100d20303400840a2000b0403103804551546601c40d881032090f2881515007040312580d030b02079501910341030285a02594030f00340d41c0d549441c000d803241e00c40440002d012980c5105403d4024810070181c8801804c10300d100c07e01c00d50390b06111405080c001d58242c0b0051100b580143d640060b60440e00c2c40810240c1020000321058205a91440003524400c0d04802405e0204040010558840380d07011540c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 121466627 1250 121465377 121465387
    0x7020a1a07050111030108121e031f09090303241403101a012706050a05070501020a09031401060302090a09020607050a0b1015051912140618061005 65
    0x1005941c41105402032155007010542c444080d01c11003d107040703c2120f02a00e0548403c00a800064410a451001c50800518803002d000c1d602801031035014401e20101c4045c0609414060309001c010391020b40c1040c0c844904200f0140e1502600c9401e20b001584070181554128494410030b60b980074581e140c00f203807150741c901da82c0d00300b09504019072620000c0006801403400d00b80011034020f06103011401524225000d007451b81c10b00c1811300e031060f000a9240342000821a0142d10400c0284100002804650081030b000c0c801032a03519496210034103418a1480c0011581020780042c02140c0d241010400150311030501840c2d01140340f01c00000c01c08242c0c400103a6078020b4110181c031750300c11440030101f0000d0030400d0900428030900c8402150741c0c0d52154096507280c203164200010414880405591004080151300f40c0c2c00e42440d200c2070071060080c004450608500c01052050f40041c458207003016500c4007808030180b444d4000c030340390100108042514043d020300030020000340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 121467877 1250 121466627 121466669
    0x5090d020405090c13091101140706050702070b0c01150626061206090f2503080a09090507050702150307141309050f09010b010801030b16020309040603030306081207020a 75
    0x5828868400918084103180c410007008010038541d0130486d919801f41608103c2c07503004030714002442c45801030680c1340c0001550b480c80075143c0a44602c0c1903202d1360703001044907581c1d400a000e10b1986e2000018000300ca0360440061055244d2003d01401f0f0ce0300580303903030120789081c1c1c011a00440603a450842d01c444c0003040c000d041100301c0c9003941c0521030510400301c402040075104809035804850745000245503284804002e42e10020907550448401c1001860302e00c064420038446041040702542d89001c81d81c2079480889032440000c00000b980811448c3c80003c03001074409001c441411460182c0000c0d0000d0700c100c0754580810f9010a4000e0712010079480d00018200328102484907041600f4400e49202d01078808503895400c0078050f5566503c190302040c101ca400c0001b4422076102c41c800690f0301151700e400d00e800c5000402c0701d44221b403180e01505001350b21950f030002d00c20f481c1c000160300f03140e800e08504040382c004010040141c5d49006950041d1400e002040982600d030305 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 121469127 1250 121467877 121467883
    0x160303090603020f090d030509031015051309020409060c1101020705030306190803070602030105010311190f0309020a08070f081c030c030204030219180216110411030109051605090d02040509 84
    0x2c05c401d9000d540c064400b81016030080181807a075409804543d03940c4c120360307410401c1d1415900609049505018100902d251250391201c00300b00b40c88001070b045400390041402e0701c0042c203041e10240e840d60582100c255004040395100191a0300071400c01c6205d98829449102c0506880d100b038900e0458a01c4450780d4a960307900a104540859a5030701e2289400c1000c0d400034495240424905440010500c3c04401124140ea982e6102112030f01780350071003910000d80b40a15001095500c84486d00140c0b2074160b0000070340400c80c028440b40d454036420380c0050559400c00c0031f5641220300d4600310003001c1815400d03401074078140480c10702c4282101b20300038008c5a0010758846e00c4082c43c040700d450550303581001c0d1290616440f1880c46100d581c141a031088461039480e0f080050518004180c23200b200040b080c0c0b00030f0002c6071042000940d486c0c10b41081e0400c81784280d94809000e00140c03c2c0601c10b04156490400c01d00740210440000c41403180c1c7c00000c0e000759255400187c000d5824 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 121470377 1250 121469127 121469137
    0x114030f060403170a0b01050706110d0e01060810290612010b0703030e0f07030201141303080c010b03070303050307120608060106110c0d0c050d0c030204050711160303090603020f 79
    0x400d00300c0e2030328a09420020500450702e015200362005030700205511003171034028801d1161040c1c40305450800250b0307c0030000c082d02140708030000e41c140011410314519020b01221840c21200115005003030680311401c01e11007400300c0140340c1c90803420707680703a0210140c812002d603450111101412103203c04200d85201d0425400318010075040085a6808181d01519106019603800c111328030707560701c460341c0e540c603e4580322060341d0050408000540c4180d6940c0300f00c00d101c4d8950350030001e040c410072031204460740007120b40250104070508481024400c0da03c0a40c4110028550380d880d68901030618072003c4d000ca4108581720681c10110034a60304804d008101d46822a0869079550000503c85103500d07507640031500800705d0419861500b05031540c2c0190304005003c40d8a0720340b80c02c100c406e00302e0610854010007011400405660389100721841402c0f1a15014001e80a068810f401c00c1200148010042150102400803e501882c41e0055903901d00780141d41d65042100c140d961b00803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 121471627 1250 121470377 121470403
    0x1b070302030d021204051509032b0203040b071202040b0405010507020f030a1101090906050a210b07120507050313060c090f03080a0201051617280606020c0f09011403 73
    0x6600082c80c3c1392400d014840c40c0a1820740300810400c00304041426025134401d00c03203900600c480c450400943c8155030400141b00382c0b8060f445428903d08080e81c00840301034030401001400c003e48603821010482003001c40362002c41c43c080c01c16501420034010f60045604000002c0307125011511110314807070071444028210303050083d4600c0c20070707608050384d102940064101c1c43d00082c20078060040c0700c1a9900108180b24030781c10808482c2c00c0c110408840c6030203440ca402c1c80c401044000c1c11986c0074030f503a035444005040d00c288031070050701d0000c2c004c0d60400000b00100505040460424207002d980035001140400c500c0c40304a44030305194000d0b1940e180d4a040020070000300500400e10144144c00a1040741d8440a5598040000410705804608400d44c1d0070800c0644401495200d41505240f0b81c200f20341c03c1c03401c40b00c420b0000c25611070030382d52642808695010402201101000c8a03e045402590008074544a4045c454410001c076044501d030000d0f07900b801002100c801c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 121472877 1250 121471627 121471631
    0x9020d0605131704050a0b03040303060f09061a07021e130c050702030c030d0507060c14190909050c0421060513060b01050702011d01020703051009030e091b070302030d 74
    0xb041012510240c0e001c030030488910403da129000603c20180503a01204c80081000051a1403e50038210030740c80113108034201640c1d010b0105800704501e400802800080600168050800c0c0903501d1000804086851090040c40520010303034034064405c5c0a5112110802503148010010030015210410341d610040d080c01c41480e1419407043c042c1129a000720101d13543c4000b120141900d50716074003107900c0020b104008100110302c0c0c9810120300d068040c0760100440c0e052264a09154001241400d01d05011060441a0b171394041015405850122000c100c03a04080d4100d1245214610683c00d0082014221020307581e818492251402d4001e0001e006c0c502e41315002944486d0461000c507480f0b46403a0451100e540702e0030030b640d011541a100d100301301c1e8a002c21032030100350f00d8504504520480c0c801100265044c00703035020b030309001040450000703890318001d415103e0003503003103026041940070005c282e08014200c06265a880219969842013414201d040d4460340d1024586a8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 121474127 1250 121472877 121472881
    0xa050307080c040513260904063816060605030106030b0103050601080307080306060702120d050a02010b01080c0d05040c0f0b1905070b0402010e06120114010207060c0b010909020d0605 81
    0x700104902c82200001c5904100c50794a288210f4401d0a07640f20181101101c01302c900c0200440c0355181140e14030903c0301c80c2c1082052000281070300d015030404075080c0f1511404800c04907440c1e03800051514461a070352444007045003203081707601032134400c131301408182e490354814030115070303c0354000d450090b000f44006078481c1400d100d21807080c03000b1207403071080800002d8040b00200c10b854483e81c1c011170307481c9103031a824108401e5400c0410103990105100c1c540c00a5200c00704110000e00100d500c40c5522a888203001900b100c0030b5140560501c01024200212401481d0071108a1100148000b0b0140c655091490103504941c0040038000c5042074007050481a60014221034000b015501d40110346148040b5454022440001d00400c7c040011600542c051070b124070007144094130700307428695503524071080100285c1c406156a008070311000d402d56130500c40c5402400d05803c0031007038a10241d03103080c2e0f90541441040d140360b03a20654101156501580d40741d403160414400d01c424 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 121475377 1250 121474127 121474139
    0xd020c0118170c070308071514040308130203030306040c090e0711060a14060907020c0607030504170706080408030a09020a030615050111030409050c091807020601050a150507020a050307 82
    0x450070354291000c80010b04421440c51241d011541c3c00340b5204080c0003164599561301e80365400ca2103080b00c0215094900308003d80c0c0c240710780000401001201c4005081c903080241280d0000b03003540c030300c019a051180016072400000c0302c0d0088000c0e10700091114500000f140d04010f40d07080308410496040034404200da001c201404540f50740d80941d042501c0d5640a1800c444818554212280600000070074501e45819900e80c041d2180c01900c80e510300b8807000480e294410071049001c07070302c04030302448034450062200008014180080408504145000c0d01c036100c000c2009048140000c0052003406054202e41d07489640a01110501600d914140c000380c000c9201c10b00b030b440b201030070004a0b5840707640d400300401d00910145290604200480010f400d00410f0345e405441c041201c04c0303164491038413909903107055038038148050801030b0009082401c103a004600c90030042e581444500007410b050164110182001d43e92000380348085403822180764099641802081f10014035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 121476627 1250 121475377 121475411
    0x70507030804060239010c05011e050f0403020309120a1a011706011406090120060f0108010c0525120e040c031109010c080d02030106022103060d080d020c01 69
    0x1070300e2058082e01d8010745d400d09140c910030000b580f00804102203102c0c000300078003102c5080043c0700040c03400007400020390b19a10300b51110390340002402c01050150b620745842c540b04081c2c00504540040c8410305040d1402907403030140c4800e55100d00000780380940007141c100301584105501119070359514040b14151803060744240b04500310207130504c0010b04480c20104505058440a980c2c1e03072101404001408100e404c4561564144001c000742e14000425803594020340c000c46100801031841d2138241c0c0032502e80c0682c8801590703810195803240c05600107050b01da51050102044040e0300d04064610186c1d003401902518000c0704900a20f5101e40c00920100520000d0301c09001c6001101e42c1103044600306403641d40010010300400901390311030401c88030389901403068242082c0c05422024100d9000303900641c056801403488500c1411198402c0400c40c10104c2d62504524203500401c52810080c0c000600303140000800080303c45031981945d401c40301040080140c5031101c409403c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 121477877 1250 121476627 121476629
    0x10090c0e010f030504030f0f09050d26040e0a1e0903020a0302120703080f100b0f03191107020108270c030c040204150c0503090904030c150c05041703070507030804 72
    0x40040c40140c4924001e0f40a4050343e40115815034800c83c01c00181d010131a200341054820b8420410040350014595030350506003c1c00c18080d2040c908020030424940103008804003112800c08030510040120000040c01c46034080030102000c142c0560050306105045000280318854501e410364400a15078002200108240304e5000c640452031112200c0b252030054040c018000791080002480c43c0d04909007294020081d0501044400e13100c151166143d0001d00a040c1510300200c2081500084071a0383d85a0b20030b1312604001c2c51400c40c5e6181014482d85101070306100c0c1180218600400c100c03200c0914030380042d440c081d6210001780710358850141c222000d2107449800300780c00c0d06142c41d200310340450f011900500c010300b9070003d041c1c4206441c01e00542d40e602060001903e0354a400815031300c524032944d070300342d070b00c01180c5032144c0503900301c80500243c186401500c1ca03800350800f0450b03041c0c1d81c00e800714001040b1101451032441c030440500034140d0007114000802c00c607104000e08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 121479127 1250 121477877 121477879
    0xc150306040b040203062b0b04080720011209050a0c0b0c0c1206130807060207150f0603170f0c030c0708060f07020a03050a110f10061a030601050310090c0e 69
    0x1010201042c0c042005034001603403c9507000c241b01c4020883c1c080c1040304450780154103180076580480d2a1240201c01e0001c880c1601c7c45031001500108000741d503051003e0340a14050701e424064002030000340862200e41500c101c2c1941c40c0540c805001003004060303101a8041c68810381c2c1516280101034941145124094512800c5c1e022903641c030b0071100003030703040c0a007000801040e038812081d990451064881500e401d58200076010200c0d4660004080c4207001e0800914140844006001200e104824690400d40b0f0f21005100144408600034a8000d4050b016500c2c0c50071000030708010710840c0c80750380941c40002040d00700e00201203906022100c0d4001521003980d1103812401c0c01900803104280140c2091011100190140c0003501d00c801d8103190001d40c0e180344062042c41d000003105102c5040d8003603601002034400f10b002e220043c147c041202c1c0c01075800030240881034000503213550b042c400d021000542c50900080f0b228010a101c1200303001e03c0d110440003070b180f49034103030b2a2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 121480377 1250 121479127 121479131
    0xb0103141005100f050a030206030f061c0f0c15080115020309060403050a1703010b070204020a050702030102070b1b040605040b0304030c02030d03091e15050604061203210c200c15030604 82
    0x456242001d00030080308d0b0040c00e1685940d0302c0c0e00170325200e450010201ca0340819046100000c02524410040d800c40c440c000d411700020300c0c1d080c0204a40b042e903002582c510b00314bc0070f90700f8040d4040f0140381141d2800c140f11794200101c420990440c00350303a20050b0020380208001040c4007000030180e10503801955603502c800418014552240b009001d008487c440070403c07500142425402444060900d151860420080e030f40060300360307800044291160132014090141c040c52900e00382d01d40400d0032801900e400d02d0701c4070291050080703204d281800d61000c0001401c1c1806078605489082c0e00506807a545152500040c0041c01c0421040d103006000441204054180031f0880141c1a004007444201100e0105150050100200940c2d000b94542c48006203604020346008040c40c03084e2188048442d005881550000031540c3c0b00e038109042807159000b01c2e0b084080b0540c404041c11044050781710091425192010002040d90004501408030001c03280304e00246005a00440d02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 121481627 1250 121480377 121480379
    0x1206030c031014090d1e02030904050114010206150a03021e030102040617060d0c0308071b0b0d05060303191101020c1b12010c020303220b0106110d0c0b0103141005100f 74
    0x990f0340b440480314903400718140c14202c0040701e410340901b039a2164148103c926001446d00400c05843c400c0e80691100e040340404007403250303010f0008507032140da003a1200031903030200000a100301d51280710280c003a01d212912280f5804951840030807040c006402556210b0795403200900403885c60300c024201a00d1030303010401310710300704523546045a00510100203450544d00c074005c1d03c2d44a49021034075000c02001004602d541032905800030442184110f80f5945460b452005407a0001c06070f0307120327030010840024043d58483c000d98500c8140d00e00f513100b0a840b0540320b030091103103076804a0f20b80300c0d210b001105006210001c016000003030b5080007542e04075004a07820b071003505104402607007051000540c2c003030038110b60090200c03030403100828081030f9844840000300203030170290004445035640d40b1f00c05400c1000804103c030310301c0e01604001007626403044085042c00010149582c0e03203c0008248020030059074490010303d420440741c2000d040c0411109018850030462202d1444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 121482877 1250 121481627 121481641
    0x13020f030105120a030503010b03090a120503150105090d0b06120303010320030109150b0310050a05010906081606030903200c010305090c1e06130303090503060a0507051206030c031014 81
    0xa04c0c0018643d0644400e41140d0038402004056000245000802d101e456180c00215821400c1d14490b103040703491302350f52402e01c1802c099183e00000713001418010f0405c400d008070740328980300c9150030b44c0209540c0702503162000010b095502c640c0320303030626102c0400044103002081e1990250b64104e403109146071065901030509072140c2c0070025004100c14030f002400442c280c3c0089085400050694040e40b040200075800c0300c2c819141100c0c1c0070703961001800810194800d14010f403070746500414001e43c0d0089034101042d00c034001c1400701a142c809100405009c0c0d4410a2601c1da02160500900c920b102c40d2a0707100c006804250020b0309004c003243c030512000c9880110004041c10310580c20040c02c1181e10890291028560444010004142d15166591070400038503c40daaa840000e840e002c10589040e0000c3d1000c404540740900344440701d90000c086540141d06000c140e00769a41c0c2400017428101d4040c0040e03050b00070b06144806203c2103900c0408070b0b0700b0286080d0707041d0715414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 121484127 1250 121482877 121482883
    0xc04050f040201140f0c010b03070618150504090203090105040b0a15060809070905010803071b12020904020a0305060109020c1b03030f030a0b10031b0e1302070213020f03010512 78
    0xa1200d00350003503004041005540f0400340c2c520903065002040307142404a00d243c0405a00007142024103075542c00522256140601459004007000d1419003944041007001065001042c0714183c040b804090140e120750b405082a80e00504654004644031300e00607401502900c001c8504440921010002030418806442850844c00f1000d81c9484124100399003075584681c007905048940c85006d00010700a0194092140a80481d102540d121002d40ca4452611082e59240501400d4110000c0c02140c680100700b1010070b40486041c00251510f0005c1560000c2e1342d080a41a80100000070824210f0b0b03030018502c1a40d000221a8525031b5000c0c400c1000e0f001c540aa0780c150420040c0403603202c4100082c1d074110344945d0f80020b001d5144000110f80713144903208000842d48601a540521209115400e02200207042c608071496034040001c0711004402c0c00c10407030700d5010541005540b60028882c010301c1025004541c0e038102503014005903002403041038841c1800e40c4012a01038408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 121485377 1250 121484127 121484131
    0x150902071217070c03020a0c060c0209090d080a0203061206010308040f080606061801020f0703050601030309060f02060a181e050f070e040303020a0c080d0606080105040e0a08070309051201020a020c0405 89
    0x82c03494518541c50b50002200d0340b10900d00c068086110710312084020a1160030090010603040e19110540000c51052029085006294009581068045281041d004403460303901200808005940b030b41c0d001c000401d0501d0301083c1075464410300002000308084040100306407100300b804038228a640d503201e00e907942c0301140e059030004000d014440c0350380180105035001e0f9005005032005042e103074100c0341c5007200030352054409070701c807400400505070003c01c00c00c06840e00d071030300640d8240420070180d52503401400301e03c030789a6036070549541d11074081e0405140319404035900c04100400212502d41d00c3c071703020040c0d629001762810814420340003c1c02e4811100c100403003242d2541c6d503803000e40081d000000f601c01409040e0919a000550040c000c29001c400d45400080407410000c00130119070058000740d00961816a04140f45200000c00506a540c88150f050380e41850303140c01c4403ea9680d40c003032600178811082000d803071801034002c0d04011200d90b08550b003c3d0600000c0005407001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 121486627 1250 121485377 121485407
    0x503010c02100506041b0302031b040e13050708150103060e03090108041403120a0504061b0207290c1f090f02040507030905030f09030120040b0d1509020712 69
    0x441e06542100c40c05540000ea408180100000340d1b41402c880caa48080b0100c042000000c0d50010800c200d18135098580500c00a482816904003400c150b4505051003000d000401d60000780840c43c0f0400c0801c020280191007120241c9200143d00080a242d0381000e01085860500b410305200e8508000016680031b0341050351881200d40341d0340c0381c4c100709032020b02e90034400d40401c10003600301d445021f406502505488030000ac040c030b042e0521a00f1a42d205e01003000a14006050498080d030004d030301e00a8510f80c0c618580e509580c07400125060007982d40b12021020045107442e01d0010201d90661007003807607607000d149424504503c90403148003080c01000c9070640c0c080040503007030560129a11003c40d0074005046c0e90603417070300e520755004034841c5648101e000030301054a04080c043c08460041206488031045580411004940207034051041020004201c1c1d000d06012034102030074130350480c04841089511010600c001e5848240161034000407900394030001441103800c9588010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 121487877 1250 121486627 121486633
    0x510020c0108090a061e0b040b0603060f060d0e0d08180706050c010212010311100306150305040203072c070c050d110313080303010603050106050703020a0f03141b070503010c02 78
    0xd500103498100700038090424920801d154000001d129100b10301c01e9109001c21041909a6440000283e80803140c009003d00d090816154a5495160503039400c12011518000d1003031981010400501510156204003424070f003044044010104d1a5880307401d040d81e54000a5640d40b19000341d04100c80b0a205e82ca5014140c100151446000070b81031030820040050703d042c481c441680001c00007a0070580e610300f44060303001020710b8074141e44070000d40b20f42018002185003400402c20080c100b00346405260311f8900040840d9014007100740600384803416864032440d0020b000380300407554201c001001034040b000c50301150040c401c140c0300f6503001002300340b01050b00c00704a0307004010101ea400a1700c8188142c2c13030441320000a140c00b0301004002162a58903014004081c0c94042e8094018010100003502c0403035804a03420004a800070450418404a80350849008400b01010384030b001010901424900c01d01c207006640a034030404648c841c5440310101403c07901d4090466000d42c7c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 121489127 1250 121487877 121487893
    0xf0105010c020a0b0307120609060509010e09031c1b0305150112270215030103020a170c04230106080601120b03010b0604030308040303150b09090402040b0406090e07051002 76
    0x262140c00141401c61015040c060000d59955854070140c109642d00004100004514000c101241c4690002040004001c4c05050314001c003041c4003803410b00522014020360303000188144005c0040b01c02c0c0955012050004000030230a01c0020544a060000008040c2c04110402d07071107030103541d0080f001c2481c1c035411104000015144101c2a100c005006520380260082e231401e543c1d0301010050b0a01c40c82c810f01440d61040210360001c898202580b00340502c0103001584461071101c0c140d0307410400101901c5021080185044035021b00580e000d81850040605207074000344110080003001040036459803100801d40360320b50100c402d1800100501d0500b0f40c0f0410070341042105c0e00001d400000e8800748880402d506500542080d03021810540502c01010b625128001345040c03d000007501c0141406113569261040708a0188182c151502007400e5607225403000c986600010002c101581c0d481001101500901c840304503c0e01032813800041c030742041e120200102a266002d0a200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 121490377 1250 121489127 121489129
    0x7090603060e0f280507020307170f0304080d020f041205012009010f170c03010305060c040513050a0f0614040c11190507180f0c1805041808030c0711090f0105 70
    0x501c4d219040301190a01e001c0c00501e40745003482668002c181c958040c66451289003009801e100210600c20090306082001e4610b906040c0e00b901d8000c0c4d4003903500b503950312a44200340064080c001c0316400f4040c00040c00034902500a516264891142000380315440c4440e00d25000082c0e420b01c80300c201c00c800c001242e443d40c401c4a000d0b210740f00d5410001c0b0490f44204c654602e0100c00c8400058442d0000b005100744042003186035806034606410b1441c1c03901b8000400d40806065401e4600d00d0748403c00300ea100d500c550000400301421000400000e41e8407203e407071003440384602060055103882045c0040e240320703c4c41c2440424001c0c0041c00e601482d40ba20288010b0010025502e6005003200071540038051280024240c514100c00300348003000c0c04808084a042014400078006152001c188110000040d01c1c00c40b4030032940001c0c01840346030084d5001149010040580100000b000311a040304406005014007910106420f10120010302150020a80d0340180881c0c82800400403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 121491627 1250 121490377 121490401
    0x2c0708060111030714030d180809040c2001061406040605090d170a0f0e060c1c090f0816120803010905040f1217061f031a03030307090603060e0f 64
    0x10381e034200003100e1a04e15140c45114240e00515034401d43c5030000100394080584034054680561008020f07480c4500160b9110030301445000d6001e4003071034030f035411a13081e5030061b80501200440c10206100220741001414000c1c0400d018000300551a10100c81640c2080070035901607844c01d032251454440362000304840e00c604242e081b180307030058564000d084407000e030142440e21443c0d07c0d4065100760158002d0403e84101201c00e00400f803e01070110b607200300180b061a42da503c002d1240314011420811103590507150000c9606180c87e600c000785001c00006c00c04400f04111400ca09119183c2e10004041000040041c0190000740300620000e149940320a40191140c41001c40d403d4842e41c4440518148654403c08503005025178260044544809a4006400c96100301009020317400030700d09049407000c0008048da664092401003020004041c005240101200c1d04e9283c0303103800810310683da00074400085e0500d18002400c088261105000d4135018051a416640e100170201c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 121492877 1250 121491627 121491647
    0x51008030d1d03210c07020f190503061303171003140a3003141302010504090609020306030709090302150403050d1a03010e031305010f020f03042c07080601 69
    0x41528090284a0410300382000101400c0600d0b200c103600041015002c103213050130040407a001c078401041980d0050351200324001610f1805c507425003118400c4008100c3d4080a9081140c05100c0c0d80301344040c2480398000e01450034032070ba03a215060014400d48410718442914000c0e0314030003801c001d100040322441207410751240e120480744106070701c0d2549051080078100300c0741d1100514031104c9a0707005405200f11042c0320b50805014180b1564241c01d00903200500c030840c0080c080c000d40c021680704108440c0103044004040c0280c940f980f1022000750700559400e07110b8802c0c84000a0311a0040c01803c41c1383d034042d00a0140c188a901c044080520010021000c01004001e040352081c01442403e0004411a1044801442c1c04040c1f5007142c503034a12807015036005200d2681d0b000d0320000220240c031000e03c1c110383c5030f51160300260b2030308003214000d94650001240106681e25102808140712029203004180b09808204004004200782c82e11800140c00c0c0c00040c01950282007418 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 121494127 1250 121492877 121492901
    0x2003040f050f01050408120c0a080f1009021801020105010618090c09080a050105060a050105090906060f0702031c0206010f0b1b0705030f0303240109230a1206051008030d 75
    0x740c2e40426400001d0848030100d4080fa2803501c08030b800034034210b200c0c1140b50b01c011603804061606040f41009868800020040501586c0c0c50000600e4843c00140402c020001c01c1400c0d500c03444545045030b00640d03d5141d0343e005620301000002c03040d11803690b402c1c00c101c4030100041c00e24202440320000d0a800c100e0b10040c4442c502001a51007020007041000a00030b200002e80340c2004002c1200c1c200455001c103042080900c5a030665581708030310341d5004542110700550704c4510030140e40076401501000395041c000d104203c6107040e0102d0921144069503800d40d1242d070f0322094010800c000314000e0741000c002c18041c082e60750b000c0b5401c41503520300329406c540d030f00b40d990400a40b4103040726400c0c078203540002c0203103c00e008c07080103178601d030910401085008500c484002415100c2c60321442a041c40c15400025282030103481028200c07101510451070192103442c03039440e5102e51401103036100c4c60800041d1500c0c0301983c8580aa4070307104051403404c64044002009040340d28101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 121495377 1250 121494127 121494133
    0x7030b030a020603041401060e060a090203060d02150c010c03093f02030405010201050907050105070b040f12051207032d0204241b05030a05071b0602060a2003040f05 73
    0x740096596880510310503403080100c2031451105540840c291080c0f03030f00c00e00c0b40102d900180076081e9101448002621202180141c581c2d03225400511202d05006000e034000206102c449059002c0310018422510417200074071800303440900c11821220080300107415400e244120354480200050100c4101004031032190039245a202d4180140185401e241c000d60700000d1304121558080c090580e1141c1e480b005006607034642800a07205200b0014020080052080010100020b44000510450300f101c003008122800000103402640034145803049543d950b40001d000502c03d00416110354201c9248500c20114900c400029110840d00d4038041c0381c0910000c42c6aa0f06414030099900f9049044001c86442e41c002500001d4105803150070858040c5000012900000445490b11598500280e8a136040d04120010220504130200da02005c18000100241d000072164094010840b00700406034000a13801201d20309074006004c00201440058045100e030203801400e18012425 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 121496627 1250 121495377 121495393
    0x30816050d020102041d06060712020a05010c0201020405040b0405161202070b1003020f01140a1b0f0b060405010506090a0306020a0c0506040308011a1c2703050711010e0907030b03 79
    0x20340d41404100584400140c0d8040760402a0301c24490320b9130041660f078442c2841d5405d102002c101c5902c114800600040c3c3d0080d100c02d0b46610800000200a030400020480d040040c403000380070b03500c60300c50544902d04164091702903150921585010308400e0400c0aa101400842070b6454407035444500e1a0700d03801d21101d004280d004044500c20326210b50b0158a035420f504c10801149980100c00c1e04001c400b004512040c003902e000c42c0c0c0c0074040742c20000041d0070544004803100034081401000314280c554410100210000c0d15402920210360501190b070b220400d00c1554003440081543c0010700328410070115802c0d50050010340c285142c648210b280740d80ba200e03d042ca0950f0211b0010302d0340c0c0c00412149070f41c866800300146410729a80e1402000c1404140c0aa00044900050945c0d901d981032000601d1001c0d05508074020720f065044110707605003c0c007a40c21160058904020450004150f913118840f40c00404200800400c0d43d9160f04d4003c0703000705180701d503860301403040b040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 121497877 1250 121496627 121496633
    0x1b0b07030f0603060509061602100e0a060e0606090a021908100e010b18010503061f0314090a0c050f1507080c0613030f02010501081915020c1e16030816 67
    0x507440518018400170546041500809203410303002042840b240c0e041c3d4101ca036602d80c3c0822004100004508041000400c0700030750303414240d01d07001c020045890042945c0321100c020070228807034a802c1314885a640d8801c00b2550682c49510034420b8030400e4007030017018031303030003a1003003500b0408890352030310002c0d1100070702060705000303070051144030401041200c41030210010314a41c00c0c60078603006007035080010129440505c01c5c541011003c55041a0702840c0f4400e90000641074011801e4060358105060b9054851a40707501c01c0e51060b208250100d0a82406001e903141042e010f4841c11211500404181751608481c0003200c10040800c03010500a000300545d030f00901d55824400c41c521003520300070780300b031000d101c489096904103001080810004126000c01801090b085103200c94549045405c2044076400c00c088507202003810034040c0c0002035454034030f000c1100011300305070024100c642d0719980d8685050303039559004003d02c00601080040d1034941210f420b00c88941c0d009030703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 121499127 1250 121497877 121497881
    0x31b050d0218030d0801150509090a02031306141902070b0604110408010f360803070207091d01140f0c090a09020304110a0f0806160915020a03020c011b0b07030f 71
    0x413460010f21840e0061088400e00380c0046100700702c0d4209645482d00100c003180d0785200042400c030450758048001010a0062004103400540c0301c0303410401142c821488600300324055850000c81d803440241e04080751514030803207009a07000f02c1c52403000c3d07580004100141c00c4014450880020a0100090042c000d006100d07141181c0600821010f604030b98607642d002c50152183c41c10070031038110b102c00400082c2c207034200760741203c280b80c1e8030340d14103600360b00e005c82c40d900072481c5514083c81c80308016403c0700b803e41c1e591842e40084c451000546500d4000c8002503503082402c200c998085010303410814010b010440c2c02070440e4018640e241e541904030703003080b50f05949034803540e00c000da40c5180c02d1013500c024001d1130003a050410b062a0485035641002044006603d05c1100300c10252070007089180000c00411150011100105800a45456400008401602c80e80118005a44c0030b00c600c52840a10a40c40891024540c1c94002c1c00180182120342415551000e10151000314 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 121500377 1250 121499127 121499143
    0x406241508100501080430050304140106030506010e04020d061d010b061c0b0f06070f03080f010501080f04030908030c07030b150603011707081606031b050d021803 72
    0xd4524100041400300080c04212000302a00c0031070720802e60901040c0e8204000c10f400542020000d00c0c8020f00071050110b409000c0c000d181d0302c8190030380c41c90815902030000d41c8950300c00c0fa40d481c41c0020282e209402d9a405000081c2550004d40040c4405069080e00d168010b0006051011010803900e48100b1100802440300441000c2542c0c0b1200031000d00801c840da901c00c0d14502e190181c3c21240088410341e801240300626261019000c050b80c8500c89100340500040100381e8902d82450100c1c200a0348801c114040b0700340c030b00010003080700f01641b541202c1060b190100503540c0ca0307002c06d03801a4024003c506101c106240070607032441c200050548501c0e540010a4254254181501b400400910350002076020b800766512545410040e80d0465a02c00f90480403102905189130801c00640c10804079881440418442844024072a90803110305803006c0050700e80c03540e448484200075030040ca02240b0201b00100c048110365004142080c4820030882410f0b00010000c0c1c2450a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 121501627 1250 121500377 121500389
    0x1b0c09092f12120d0902190303020d0302090406180213090b0112020f271206010b0f070c030501090f1712040b0a09050a050d030e061e1302060309060106080702010e06040624 76
    0x1d02c034508070443c28000c002c41f8000d45209242030000d891954000c1d80d600c1c100c41d0003801c064021401c900142c43e40e07040b2001032f044048140148001c807980c4200250070004814180c1410784070000b60a48452103007115010041c0d44005100c1c06002c2e441c0d010398001c1c0c1804038584c104120103e840e01d1003400c42042c20000350f0b01e958640396520100144541c808240841c65007000004200c003202e0b2200304c6800d6848181d81a4882e82d0b581030148000c40182d0000e0603550a2286610400c00c07100c000840c0a48584502c203864041811000b825004041113010103098440114020486072050640d100e0112480491000820350300c00f400c20011200c100e404e68000c04a82540da03405014072400c9e056160010810303031501c00485e001261076540041004d890040104850108070b048140d091038002d030595030b03a8105100c1c06130391114248a680c00142070300b40450040ca206009100c500146140103002640302c9440d181e0003081780c40d001c00001100d10098508404a0031001401402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 121502877 1250 121501627 121501631
    0x120f050a0311061501170406020408030c030406140a020a11060904090f050c040506060a0f1404030f02040506190b30041a0f0103031b0c09092f12120d 66
    0x4484038038a0300a001c0c1c0110b040700440c1c13500b518a640e00c0300c4202102c916041903400300d500d803414400024896a001190107002c0001ca102c42e1810010040040f161150780c2d1100500c038522000103240128540c8030300507007081c80d51321301180140000c0d5840b82401085a07240c0440140081d04450b80703030754201d400394585820300d01030040c18050200c84080540c0c0c240040d142c01710004070a0300c20080b0000c1448a40301c1c55584a6105548241d90845003d282c244c0d65903e904180b00030011210040388243e0824000854904002500018030821100d00c00c1d8203a081108100741500000b40b4820000746036500c01c03d41c10102e0078a0044050405c0d1004c0d004d00b003506000c9184004500c1e2000c440e41564140001c6030100d010050469415103480c004e09403a50408080c000c1d50f80ca00070b00541c4403403002060107001503010f58400d40c410250b0a04005260203001c900a40843d041c4001c911502c1d80ba08043c1010b080f0811703031410030390644007800305071130001c0c031240c0040203804005e83d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 121504127 1250 121502877 121502897
    0x6120504060f0c0f030b0402030103080306090403121104051e330406111c120c030e0d050a1b0503040605091305040c0302010906080f070e030c030f101b09120f050a03 73
    0xd0b00342c846c80055440a460551070756040d512030140301d12000d04198054460b010000d81030502c1860503004c1d05506c1201031000c0c001c80d2103030100c0c03601700e8012644034800d03003090612480d96203424005941006020079024208840401c4800000409a2441004a2982150480c6070180100f004e08074544948074111020541d16140440c45143e040110141181044e405500500c00c29681d0714a11004200f04291503c1107019040341ca800c64403921843d410200d02a8008000d845c906038107544043c01500000e54009052003504c01c09011398208110510010b0b00c02c1c0d000346201c1002030482481200d41c1c102003001c40d60100c40036510200c61280038000c40da4440d40080003040304d86080140350a02d204d8040040001403c0041403150081908046850034822000d42070303402020340303038025031102200b07807507000c00702c903e003040b9252010600441d4440c005043d0b0200756070399138030780d61410481b100b8850401201e0039285088042c1c0003600041040080c08400782c8642e4030307480c4070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 121505377 1250 121504127 121504157
    0x50a0905070605070f06020904020f120f070314040f050f1e0c0103090201050d05061f020c0a0f0303050a1d060c010c021b03100b060c07060801030c080706120504060f0c 74
    0xc201c250b040718042040400001300440d06440341032036282d0b0041d60060750303500d0300c100280081c428801d860020407008180d40c070350801c1d0f403503010344100407100c0140101e035140b5100318101c50600e400b04002c9030b2048081804a0011a03032096610300c00c400300c1d15004c040e6441d0601e00413040c0180e000008180c221803103109030a100c1d05180d0242030078207118188032640042d1250240744059581700742e5402c00a4243d51303554800941e81c1e0369400d200700b8884450b0320001d44410305803180b1405507111034000202c200a2014a004594240da25141081c0411408407448440120070074004030b119400c01205550301001484621400b1000048010b818000a8180980e1103a0110542c030642c90880a07520040343c00c4803c0c0c52142c50020342c80980c2c80c0011518050070f2443c000a100303100c00441c4c8180c000c00b030039058034010b011145106540d00310480e81caa0490046034009216102e81d504000259004107070070a100c1c10b00414030341800c811b1030702102c000780444400610491181048 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 121506627 1250 121505377 121505383
    0xa080d02010606180315140c130807051507050c060a08010806060a030201090b0903150108160b0310030f02060c011401050415030f1e0f0812060103020c120306040906050a0905 77
    0x42c580c6080101c44d0398101c2200900112151002900e110010001c1d40d40280055204009040c40040301ca410303814036040350343e03850f0045481c0b030483c5420700030007080002c40020600708503200100142c8140030710300076144030f540220108440501c030b00710303001c40560380b800d0107002c80c90362130360320841d0541c90700440a1074040b01820180c01106041010301c0540d920090480139925036194180e5a02c4840e40070a140191103650807680c01c0e1078000120740e04001090281c4200240511402110744821002c850b0b44015126422000c8810004100090500c000c1503000c0d4002000d0038200100ca100b04c0d0709540c07986007003100d100702d101d0041c0302919192099480451084048450039400d642d0b40002010314210090201d00143c1000d40d800359a80142c18109a03115848032340600c05441d082d10326405c0b061140440c002c0f40300018040d54800c2c800d842c030b1018204002c5c003c400c0f540b0303c2c0d40242d50000c1c18032a0400c0c0c64420100202d81139004090040b80d07070105c00250740700a800c103141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 121507877 1250 121506627 121506629
    0x17030a0c0f090b0a0504050307030f0204050912070b0606070602070609030809030a0909200a030606020c04020c06040f0201141b120f120901090f120e0a1802180a080d020106 76
    0x10500101d86000706000c0c0d8081070079020340751101c070200e94a07400300d281a030391401107038031081c0d041c810488080204544a4411041944203880902c0039484003407506803111020f09031641d0b440d03401e11a40d4041080004c1d0300350026030203041c1c107290881c00d8403010141d0740b111405551480d143c1d001c070400c00d540900556480304c0ca4101071414030f1690100100148014403401280c10707180c0903001c07440c585101e410402603030028800c5030f4401e08813102401400d4184116000343c000ca4500032401e04160086070302c0700c2d44640261015642e2980c13050020740d844038069042120320001c40d04d408401500506000108510240300e40c07105001e468030303040b1500c1581c194000f040c0225281034041d00701343c42c04040044a4180d540d80c9200160b8010400008060010442c04404400340702c07003c440c2d0311900e00c01f583d4040a004611090100c80075852044200c0a070344801382402502d21940540701108a02c00c00c0310029200030001401c40301d0507080300c1842d0308944006c2445079024800d0b98 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 121509127 1250 121507877 121507901
    0x5090f0901120213051905060a0b0307020703170a0f121113050a080a03021c0c0506072109020303040501031a0405070e011e1409030a0b07020318090408030402150717030a 75
    0x200091406c42c01e08602e5034050300030040c8081d159008201140d59480d40076001d0320250340030b41d4807840c100e80021b542e120244415540b10b0071507181305101018202c202c41c1d100e5035136200d099408103c580115040800c0000020600750380d81030000f2080c84420003003540035034186a4251450074803041041d001006d070f100b480c0306d51185401000103600410100302d03103404010b0341030703101c5241201a241d103075200d10000c006014050400c090150400e0301c80940c4000c0602c060a0303481c902108070100d4169203006585030707106110820a5600c40c1d0403280c00c0c901488418040c0a10803408242640e0040d92890045601280d1503800c65910060340040c84c02c456506482807980d00b80c0c0a0144403400c000b000402000142d0a0040d48040284405036a48583c107140c8038941084000d489802403c072112003101c0d002d0000940b4038050039610300840d00061070314655111a403c00c444052800e803070500c40360080c00030380e0100c1e076114509952000320b81b0f50303140d40c1d2410003078820460703400341c0f045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 121510377 1250 121509127 121509131
    0xa090503070f0b031b0706200a0804060209012609190c03060203060f060703080609010803130512010e030d02090901050406032609030a03050715140705090f0901120213 74
    0x700141c007041c1d0500c2d0b003100d8804500640d00e4a42070034052071000800010740299000007102410420305900450f20310001040f00c1000e0b020010b070764207503440354002d0100080d43d52008200450101e40c01040f116005040907a41c0709064101d0000105041c241e50300668101e90402488070818845442c603003407240c00c482461080b90b078a82c1580c2145010140c106903000c00050b81a48980307404082c5804000d041c1030311251145070080046030121000c034013800f1144000211100d00006840620400803000328825050200784040c1d01440c00480d11603640307a0880100400c0144010104468490310159139214104140b2002e820103900c49800f551800e201000403441250032481400388004c012100070300f51303200d041201e015840316070b41c0c107005a0300c10300109600880109010751141d85884004040400301c0403c6580f8a42e401100807031102c0002c02c0144610020138100b10010101e2503040b4003c804181210b10036003140c84000d15900c044425880c0c8a1500751594000300d42c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 121511627 1250 121510377 121510379
    0x504020102030f030a0908041206200901110703060504080301230f010305070c020301050907090b0a080d12060803040b2106011d060d02070501020a1b021c080910050a09050307 77
    0x79038920845091095050f80840441d89070441d9030860b081a5400c03031907054881d070700d54550381440c42d040001214641d02e40b100c00c10f400042651142440c502d6081c0c4107040450400064929007a042040482d43c0075051010000940c207114080c0140d0003520f03415100d604081824490101c4135240c16403030001c440713074050140d43d80c0001c6049144e00b8070300441c05807106241035942c500e011000035459400c00040100e03d000014100d012181020303002c0c4001040d170802d200400d40e042c0a0f280f03198101044036400103003d200710304820030080c0d40c001010f03030fa903101ca9800c0d9085a0082000044006490103400400c54264085944d8402c0d441c030b01d5051a00019000444043c111240380540c003158165980e641010f44e02c81c06100d190a40d5900004e14129000f50721000565001ca8081004440132000800044030081c3d800b800c00030090b000800c0340d00b03240c0707004241142c484034104004443d54036000200c411103405503c0c0d86403501c0248402420454550304182d0080c0c4c00100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 121512877 1250 121511627 121511629
    0x80d02070e0709230607020a060e18010f050103020c12070f030801060201021206040f0906050c0a091505090105130323010516090b0d09080304030e0301060f03050a020907030617060405010f050402 86
    0x240026074510304e904941e22189020b4045980d500072500c010354066041000061700c0c540160070000003601c201e540741b4142b02c960800d040003071000e000342e50640400fa24148070a5011f41e00900d014080441200c07050075518011181d581c2c84031a046a642d100c0e440900100340d00441d429000d00381c103000a41c240107010783c8001100710010442441039455000310310300c11081d9800300d007403282c100d0001c3c00703540352000c032084803a4020f10170200058808400026006030104100310403122940d960340c60040390200440355034001d514000d10301e448a2800100080c200d80380e03d07080c2800344516a840007004000d032400c50303900400d00065a440c007030345c0e4641203500600c0c0000b035a20001003941ca40070b081050000400c1d191070000c0c5019000001d220078190410b155142d4007500310001d1162640b00c02c050b110b000c0745448001d0040c4d101600340801031616006440d8001540d2400041140e84c4a61a085d1703121070304000340054201100740810710000303010b141664803440c402806181000e80c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 121514127 1250 121512877 121512899
    0x1080f13030c080405040608010b030d170106030b010e0607030c05100e0d080907080105011e090b06091e04110d06050915100516034107050304080d02070e0709 70
    0xd002000c012100d1090420002e4a0b01a80c001d090080c00c20007200d51144213950091000c018114803a2084c0046c0c80f24640c031580910300550002502a40644d20f8a03a056002d0320306049003a05000d620b0700140c0c0030f034481d0006815a280a559503004d641040e003801400c01000140c50040c881c20b00114141c1510000b48020b5503462600e0451480e980b04e00045060407520b4000c0e04895003071030f000180580c025400c143d034041688408030450340c1e42d210720608940c143c4284c540c001c1c0040c40700c03529074549002c8841011000204080d90000d0000000301110800100c8005416020601030341a241d80d206120180c80c00780c442e160300f070418a044550200020303e00714402c10f540e00e4840100c41c4550261000d2081b0940000d2980e0018900980212030003828060850030030f6290933803120314402c60340500d8030086a030780c40c00360010744606c072207900c43c84055900b03120401000403a48401c1100340c0d2040c0c9142d02404800b420140c40411607540603220f54108180100140180100c00d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 121515377 1250 121514127 121514161
    0xa030c03151a0a0c140a020a060203030106080c09010e0904030906090b0f1210091a01030e06070e04021e0d0617030307140a1103031021030504150207030f05070501080f 74
    0x8442841e00c5035101c1c4802c44210712003120050030b019040c43d21405c440000110221160b10844042c0802c6442d000c04982d01d0009204003130028040c10085403007000c506004094900e070603d41850780171580c60201c0d841100c00d40b03049000030741860080044680c0b20f01c440010b4003401d0812841c3c039000000c803480340d0003440c04402c01070b04030b4004169581c10a01c1c40c0c82c0204480341b003e0119024203540344080a1035076400501080c00c008000c0551000407a44501c2848070b504c61150b41c9103440b007800025081500310050340b050140d20210560008005464442c810040200300c0c6400d00c04203010f6082a44002d40d055841402400741040e000039850010811490540da1a0304800070104e8907c1c0c468008101c0e90302000083c450741d41000940c09042e01c1860340c03110f0052800e1210308551a100ca07001400084050100348020f0081480c140800003061045401868803a1212403174400078240403501580b10309030030010355810002c019800034074056045038030f18281c0b00c1101640c5003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 121516627 1250 121515377 121515419
    0x50109060f031209120605010806060109031211160e060f04050115030f0b0a060806031606050f0309150106021c0201060b1801021f0b04110306031e01020904020a030c0315 75
    0x10445043c03040c1841440190000c010740310541c04607204c42c0c10050000c20003805900e03220b004500000d020340d4003840170001100da001645905485645008440d0511408aa416203005554540061070fa000030b001d00074200b0041080051706190f001c0160341200c107a0f02c9070107503051100400211480d1062001d00e5015401d0229451503d151580010314403250040c0d230100c0c0001c8040b5501c0c0c2c0c05940d981c41000c060b400c8030020034002c00d1445400003140300d4500000c00801030120301011040c040e507007001c141d004943c40c44008980d88520540240c001c1d000603442001c81d84d848081c0080a00c04100150008208203403c007807800e040c502ca0300c060f03c040c40042150b5401e440e4070070043e0450076010241e01c250100c0b201000280600001c41115204e00d0070f0900c002c010224a4084a006807401001413000b003244482e85109c1d00d00e04500b40c42595820300400d9401d4403503000410400d0300c41e80c3c000801c0c2148400140890b82403e03c1c640c0407480c003402c1400301584114100d001840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 121517877 1250 121516627 121516643
    0x515090706080a0c171e040f03080a0603020f01030b0402120108161505030c280e0307140d0308041406070306061101020304051e0102040512010b0a050306040308010504050429010504050109060f03 86
    0x2445040175289828001c4000a41c6606c0b070042000380300d6108840801244039039504416500d81070741c4c8030296062800045e41c0080c401010086643c003941c400100c072040544094208109034403000000142640010380c0c1d5001a40300400400184100401510300c81861502000764828014100d000080180520403000141502164010303c2000d81c01c00100384101c1110704038402c020400390814080758060300c07601c0340100302800c0085d04600449006040000c89000700c0d1000c0f80e80b0b4102030810f95103052850400001e0400511080e4031072030140e240841c0f510319108000700002d040c02da40303450340d91043c02030000107503011803141204181c180c1140301305000c0c085054024851548801e038440680c01c0e11420320441901b2145100320112a0700340c086513110103041e00c2c1d4808541c000c00041c0e075000140490301c0c099010a4220380280e04600c82c840c0b2004041a0001e9a401558002550000104064076050040e0750150042841c00e00c00c4e02d2030591032884c1426a8000180390761 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 121519127 1250 121517877 121517881
    0x60e060304140d11010c03110909061206010b0c060106080609060d0c3b04150f0b0607080706060501020f030a030b0d02030304121e0c0605070515090706080a0c17 71
    0x5a54040780340b1110041c2d5072001c8240c80044c003908400b1890071095402c0811140c0c4460181c030a020f050b160280c902840d02c00680200310403070000170311080d400a0708481440039201d04012081c041c1103000100d80e41c030300e43c490405251100503030081041210f0681000055114240e14a80000741a10580d40804007441d0071440118650802800e02c08041c6160040008500d2941185110094031803150552a000b15148070030440e00903200c1002c000412958500703c0c0d101e110b5024031004009950b008120010380725612404040d56011004201002482400e00c0b448000709001d0004144606440c1111a100d0060520840600d603440038000641d44500106404241c1c3c003c0c140c03543c03991103050601001161100c1a0383d8189001c00003c0116501c5d03003209500380d007100f908407900349010421101a441500221198060700440040e40c42e101494030b0b0050680074094008642810002041c485004044c0c1c413000703042481510f12030b500554003820b8603010001003010f0f6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 121520377 1250 121519127 121519133
    0x906140f0d0609021504050103050a050c0f0706020409090b0603060907030b070f02070f03050624030312062205070e031c030e150c0a09060c0c090c090f080c0415060e060304 76
    0x42542107400317900161380300200604501c440d4014001d03504262410441d9845d00502c0008030f550032510022101000c00080000407a054040c0c01818031428001d45020344a842940030344a1a00c811251503801c1024842245802d102e82075000c8210300090021504e103031200824a40044d101c4030500c0355401d140c552280c0309004030000b0703003240d0403110041030f0b6070303e4070a81d195412100c413407102030940c0a580c1980300707011400c44810b4000b0001c6040444024052040704000343c855030b0b2001044c041c1c0b05030454011420900c1300e0000317500081600e00010064610031020540511a40046500381500508004480b1900241d8900005c21101866809141c0a2075280e0500c1c0664a0340c208640392200d20014040d0307880f1661024146603654009641300c5404400013042d0300301c4044148401c031043c1c0e02c135030311100480c42c03c02c01c01036540300401c0200f00c898000b102c0e160014098018036082078060000140186166140014074043c3c0040160a0000d0b00305d104860000202c1c081c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 121521627 1250 121520377 121520381
    0x607050d020705030c1b03070803190519020109020306060a03080d050a090203060a090302211b1207110312070206120402010e040f0c0f020d0207050411041e0906140f0d06 75
    0x41e0980c00f03000c8950b5145443c121503580d05550075a404103541202034005e90781004a0000100c5d000000118104418410818181c1172400690000c1000c288100d80c581c0440c426680c50302d100355000000d060480c2c1c01898103040d401840b260081e603005000f040020307542c8003210340c070801c00040022542c0b80c409041d40a419606006985485130720140440d00e40c01e40c1c02510fa051080d001c50b07142201d10000c4482d003c248d90042d21a85401f0310012401100d242d04ea0688140000c0984402c2c40072110000c2846e00241c02c04e89212400e0496488641000c1104482c0210038a10440c141800707503001070003e1240340a010005c09000300401d04690050701d00043c5504010802d20080c03c001e030750203004000c0400074500040228140c095860700110702500f40b04031590242c4001400d10701408040d0800d12446160114100300c001848200b269040d01003003500120f980709186030491402c10340744150003150758280c04200d00c024a0317803000098101600140c0340001c00301e0780c60a20f000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 121522877 1250 121521627 121521637
    0x8010b0f0903071e150906210b13020a02120306101d040204090506040507080603190c030203060106030b0307080c220b030604080c010f1a1c0507080102070c09050601020607050d02 79
    0x8652221500d00d00e42c4c0c0090040d4002ea4003c42d00c0300e41002402c0740e045402d400e00f881080003003a002c41d03084a10031a401c0c11090700c90440013020900d0740a9502043c6103042d000c0e10f031023209074003003031003024698140000326012b400e2008003419820080006004500940c03065000d00107003100b004c000f0200360208800c4094018030854039550b6540030231018010856140344581e01d4440040d400740e00030050b0798000e070300140003055641e40c418500d0428052003a02661002041e0000100583e410000c2038081c0c10a6a0040b4140401105040c50500240c05c8000d0a07007001c141c016140c0c49042e56900105829030040801c0c40d00b989040c0010105d016079140c00d40142010841440140f100a004040c1c3d180000c00281418074404400c55504500d181c0d608120080800c00500d4201580101849103240382c4a28000380d980355441c00310240d104403500c0e50003144402c14400700340752050041200c12030911143c504000003d480c1c0710020049001c6c8075010500010b000e103154155a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 121524127 1250 121522877 121522889
    0x3090302120301090b0109060203030f0f0703092405010e010b0a080712020703020a0506060607050a022701030501060303180305101a06070f02042034080c0d08010b0f090307 76
    0x5982e9611169400302130440303134880601059440b240001c1480c400001c90b0f02c039001c110010705654a5001c0c03c4095150090442d84c10151104410320129051030210701450400c0381c60010b40e02c00821252050300c40503800381c0e99440c2c01d0001004148003200c115003400c10580303000481a0307100b550980747e100034051601e189034030101d01e0108264000035001d0170240268101d0b01035075039010407c2460300c03a15500400d1a0064582d041c0141021803096501001440605000c5000120700c0700b00f9083c2603006550341c1e0f440740020003e01d500f14110344e690011f000d006034400e5095499444c0e82e03e80002d2402c080940e00d01c05c040701000e0307580b02d2040403c4018684c5070354480504048c054220b5104060380700398600040c4004020045076024088500004814100740d050050b290a2402c202d0003a081c40012082030036840d03052041c1d0381c1c4054810540141c03500b0385c1c040740528107000700d00140180301907500140711410130b20080c0c40400304942c3e0400c0d61001d50001280c100b8103180c0c004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 121525377 1250 121524127 121524163
    0x312030901090f1514160c061d0a1416050919020a120605030106080c01080703020f160b06100801170111030708010501110102070b060f180c13060c021003090302 71
    0x101c041040604c0201e48102c0d1800040c8001000e0118101c4800000c1d01c007071031891840c81d50340c035a8a010302550b000c202d01038200040c00c2001c0d81310b04540512104480c4003940c20100d009020021012900041c4140f0b9000418864010f50039040300d4210b00e00480384141c040000182049106501640d21090541e00070354403203c0f180d2014054000c03012109000604220f00440d09080520031042180d0212004042c003d020000641c1c00d0030000d06501d003003640805c05280181302100c0205460300c01074010040c039104a04000e4240c1401800f0188241480c1d980200000c1d030213800c2906441d05c24241c140701400140e9441d004242201040c0001c44011040155003070304641e8460403540280c031035004205602d51364500700d1041890007881610380001003480c900f081c81003080240c0300038004c540003180c25111102400320884152408040005941c0c0114001c8103019004103a5400c000301d00480c151300090030441c4c0c01891a0030990707140361034400d240c42004611b000ca0081b400c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 121526627 1250 121525377 121525403
    0x618060c0201060602240103080310090204030f060f02120a020c1501090c14190c02041e0518010b030a080708130303090501030c0806100f02071a03091605031203090109 74
    0x3074041e080d40e02c100700c094003171441095016080c186d030041d0000104806008960b08642d85c0601c0b80c1c1024003030b0002c43c01c4161010070103a405100402c09140175101466a50b01c0c10314248081d194900c41c011031060040c0300446000d11050385190b00320b0060300c2c02580714051803403610b00e020a980b02440490301c3c3e4600009001c0c03402e9000f0080018a0754030540031848444c02c48180340f01e80c0030740d01c401a100100820119100364414540644024070114900020049000a1399400f402e0415180d6544040c0956040201291101580700e140207110307441a0400103621441d0103200904030140000700c0708100002e00b0100c81e41418083c1202238640c4d00d9080082007251280035903404246400c00f68400c050003102e8552003008010b00b2100201c0848000300c414034481c1103664154820b00c840864240018140700c0c00d102524000f05403680b5252070002e10307003901e00e003000c1d914840040d030603c40758401164501d0321483d06800d0550300d0719004845070041024900c043c011980c4a99 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 121527877 1250 121526627 121526651
    0x20c090c09040f1e02070c0608060f0a0305011a0307060e01082a0301092f13090606050702010e04050709030b09150703050601081e0112060621031101090f061806 71
    0x102181401c00d1141c43c1c102c04002145a04c401c0340300349030740600045003e900070000e00d4411030b030315640590040c1c501d42100c044180811701c101625001100e2994564688080d8212203c000c3c6420540c103d005000e1289040c1d400741c090b165a00c5524100503501002400c4210b094448140d0b1414111202c0c804200300340200e1060f4200380522142c0c6070408282c00c50748150780b00c00c91006102010400c0140795041446004d0340d20034000c900034400000340000b403592091083c1c0e00140160b864183d500c005030701c00101034504111145100d540f0300f07001d20070141e40c041c800c03005a951015100800b9211190000e00c3c001480c209441303000800000c10241d01d0381500480d0280c0401e8950404940340d089406c95003070009407400d280c041d02403004016001034600d48810160051400241540e00c54a802e00150708200d0000e000001d11256141007561000040b0f264991100080000000c582d5a1541a03184046d026000c16140c0c01e00618455402c2d080d5003a140e40640c00704088820a2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 121529127 1250 121527877 121527881
    0x31107080c0a020a09020702100509040b120c120703052d0f1006050301050403120507030e1203160528140d0b0405071103030c0304110a030b0a050a020a020c090c09040f 74
    0x2c0703002c0303000f10084a4002900880d81c02540d03001980104003100364103407890210740316004100c0c41d0b0750068071000092525211a01c0500f5038004a002500d0b0790400070051000d1102060304111260b40058030405c080340d03000c030340050045240e4901d0140b5031070301803401581074400700d180ca079030303001c0c40c0c2034500900c80004800b041003051a40a00000e07540d00109801ca60381164082c001c41c164244241c009800c41e8080ea40c070070403508000a1036030506440c1e51400e604030600410907000001032102c1b2030010381c4011a10002880c0c00c0c0e103821281c840ca14100503240d40a0030851035603101f80c0d10350074040d180c2c1010808950614540700c82d000c1007588043d020080c08540554900700c049655588200d07040740030702084030021491600c0d003090400840c1d00081054039024407014110f00b55540e280c00007401140a501d0217105410002004022100c0180540780c0451041020705110768010400c01c07207007003045503030f8030791542c42d0b110820442c401e05501c0c079800f510700701002e6500b185903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 121530377 1250 121529127 121529143
    0xf0b090f060906072a0803070b0f25031b0e0f0618060706060e01080d110610030311010b0303030a0905010509071a250f02030c0a0e07031107080c 64
    0x4880000c622901038003800340500c20740c402c0580008082042d0300203d40c52183c1680802450514030340010602c594621261007550400e02c010380000a03601c052240c00041650051030000401c869070505800340303c0c0208641ca8406003000c041c0c424441400e00a0380111000349030041440304a2204c040d0080c8040000c030b001034451018146014032608058090b034001c0c000c03403203901d490b03600c10b481042196006060225450f98031110041490044510310600810b8a00b0007410805074440740500074480043c0501403070b074416010426005503000c0e07a501103d4041c03d11240d03041ca0000c1081c09410840c90441d0188000014041031551980c40303c0c90031801440204080d841d601002501c0381c000f4461702c9072400b000d20f0010088149403000340801105502004c058901032042100349010000f01600c0c20000c0482c5481903081c01e105100c4028000c444580c4218203041ca40303031540f940617090030100340c0e4030203d84103424442c01c1100c41c0e01d0381006880b510340440648039039a814035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 121531627 1250 121530377 121530379
    0x90605010f030c08010506070c0305030403030c03110f1905010f0614010201110306030d05280801090b100c03050a11070e011d131b030212010c030b03030c0c0f0303040f0b09 76
    0xc90300014039a01d200f44184014040c40f80e9a0462591030101001901c1d00510310640d8110f041079800000142c0c204020720046110340c480070954400c03070901504001c808941e427071071071300290000d61850310082404200e82c00103801c5a00d40d01014101180140f4840190340000351900740003180c102402d0410104940c0264000d102d503002016180038039000039141c0e15016070080003400e01441c000e43c064101c1e03040400c1103035219200d002c19411090843c00c40e80e80400c80071030051117119500d011b42c040d903100603201045c4202d6210402060141d40c020040c0802801080001c0318900c10310348100b02950000071603100e030307031a03d16248118101380700301035481c0d00700ea903a0010000e501d100e80348101c4801040600020160301c441e02199a1001003002c84103680c4d00101c0140c0d0f500c08480a022541c0f000080d0022903844003500315082c5462082c840d0f402400441c2440800085c01030410b9002c1d41c2c28114000020080f91030340c09541c01c142c80c20081c81070702041c1d0030824005412640340c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 121532877 1250 121531627 121531637
    0x61003021512130501110406080105040b0901060206061e0604080322030b0103080c0102091f02060f061e0f180906010b1e030709050411071719110c0a09060501 70
    0x4007100075080a0301c40c80c4202c6000c2011480000d0b0a03440e14600304007000d0081001181c4c55001e40540d4549a015401140109a0b001c00510440c10144a010145041540c00c5007455061150107540c4801c0180214805c0c4a03d1500c400313109000c150220411401a1006032a1600c42c806541c503900503000e03280d0048031402d4000300340100e06402000b140c2d0040d003090810390854a4030141a401b00c502e19030a913408101080749504c4032950381d144841814111080901e44220081c24494050110817400c10300100344885036881c00305010b40110400381c3d0105848001d00481c500d890020801c40d0320010815200c030031407403003441a912403040101a40c00507a280d54a9104600400721041000c003074a42142d1001d100d1140250380003200e07812701040241c0d80c1e07070000e0103035000d44804522605011911004000c0c90820000f1301a00c010000c42c24800140035100d207001c0800c1c8200200910f1601909010724140614446a40c0c0a02650441600c550395030000d490703a4441c642c0090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 121534127 1250 121532877 121532899
    0x20f100203041802030708061201150b0406120b090a0c0309060c031401060801080307080307023f1c02070813090b09090c0a170c0301020c0d08060a0308040e1806100302 74
    0x445413080fa84101113540b5001c2d020f480f03000a1003c06104a2081c12a40d0350342d81c805035000c111130b9220001482c61210386031381d0b241404401080d01a01d028414540d0781003580120466070f40c0c2006503441103809900040858080c1022009000d245901504280c80d0a5180c01003640c10f0704102411501e013840018203903a54502140e00754402d218010580e0010301c40d580c0011140030046410031290310485070b92103021008009142c801d1001808042180b142c3c5401003e140c40c5508001406180650700f061010b43e0030210950b25060b00d94956640000d414080003c01403d4403035902004401281694071903e00b00c00600701112003034411201600040c608080004070030100c0c03c07001d440075140700d2134025540003100c04000d00c018680030305401c80d201c0b41c809101030659204a2002800190400c0350050050000504120f0145201e050700380040345031401141e003200c0794207030000d48907611a40880e909402c00c034150300c03240c081c802c107000005d0840300105040d0b03802107131071603402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 121535377 1250 121534127 121534169
    0x1b0603010b0d1125030207061704121106100e0c0306010509040c090801020f07060614150d0207170306040b09060a0e091606090e1f12020f10020304 65
    0x1600092144145104081200e440c0ba940c50782c00203035000700c1d0032a0507030070b11242480000c0440120b44d8452644003a0a08030000d040e41000704078000c04903410461480050200c0c9101d0302c0d500180060814030194244981c0107219600840c40080c45d8415200e1038101034545141c200035074411816145058808110400c0c0c004045070300900050f124a46413840c04c006100c0681048070480b01401148800007416171807c0c00189a001500001c240c0d41e501c41d0700c0e16408560103604a16511101e02c40140000d49507202442e5882e2311118080343c8a02100d0030072800b80c4985140101011540da1071030300c0c8840440003650049204507000d1228911160511480860464545920980d950310400550510928494211044c0004d039801100b01924030b100f0000b669202000080f218502040306040039070302240c0281440700082014201042c0340800306045010b10080560021410707007c541d40d800e0081030400e0301800120004440c2c11000e51644c0061048810004400240c40c0107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 121536627 1250 121535377 121535389
    0x30a03050a05010f1203030b0603010618080a0b07110703080f0403031209030e040902040204170303100902070819050903120d0c11250b030405101a09060f01020307141b 74
    0x44c0d9001185064140d89000110141d44101101c10b80905580e03800742142ca13103076900258007802894031824038840c94407040d0140c940c119401000f450304103240a0300021001c50002e5001121482e0002b80c405000c0003482c1005a681e000410f9514001020f922159030400030300111381c0a902d680c10860381e030726060015036000100040008001c0246990180341c02e43c01740d14030900141c001410300c0c1e22800380d0005d00703042c500d0544040e40040100190b82c601c40203400040d119000055090815560302c0350854001c40080d00c008100780c070005c98030302d44038105a0700c00850040440b20b00310b1060840300c0c0d4076404100581f00356410f0054002c8070a018003032154007980100010300102000d0400d030081d001620344241d1440d00d45560004a00d44283c000d540102d01460140c80304041d1842c0d0001151009405000161800c034401c904a58412007082e60210382512140f88442440300100e08602c030f140e4009000140240f58a42c03840c000041d0118400706a01a00c0d03090740c501010494 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 121537877 1250 121536627 121536629
    0x30516020109030e150d1107170708040e130803040c080105070f090b0f0412082106060712050d0905061501080f0a0e150c0d05011e030209040218010602030a03050a0501 74
    0x3000c10143e80d004401030800c50030001c4405c00d80c9241d1800c06010b243d8120a0301d0303c1c0742e805003e080e40480d01c90b0138000b002d1120281b1b0110700c030301245402d40d290344101c054000e5200392200856030070300162201010000031408103501110203641c91400740341c8104442c0741401208543c0d0728140c005581d081c0220004940041c0a4403400081340c03070100c10b10120b40c800e14034140791300018040082c401140071072400c1c8003481800d5481e16103202c006101440880740300e21f482c00203c03c0c018030074a40c840b00d007280c4041c8d81004881e400d444e00b080098816105030320034048220b00e4074061900380000410300030b000b60781e600341c8045204501401103440210039202c03207025010070702c00b01d00618043c1c1d08c07047c006180c050940c4c250b0131103800c1c0e80708910400c503003007070b01a140001c44902c00185072080c140904060441000700c0d070714242102ca40041c2c0384c00001d00884003200420203650707030410380d4016610b82c05904030540da1240802501c0760880403070031020a0400000c03130607054450064034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 121539127 1250 121537877 121537883
    0x30307230c031f020928031205040506071412161110080f100308040b0c060a061404090602040f12050607020c030604030f36080a1101030e071203030516020109 70
    0x880c80810158100a500011005606c54007481d1032201103200c58508044001000c00d40c2c80c81d051035414200943c0d40c0d500c4441c4108502040180150707a00c0f04295000030703801c206c0000a4840140d40d0515010544080702500140411a01500c00010701e90441081c0f10b03107080d800c4481000180700c824450707500044080b40d152000905680301d203201c01c1c0d51000303408035800d04440e0b49445200305580690042d10002030f000400c00d582c440c3c2040390716003084101104001c41403902800d20318125040e040301d440340351250088014802d65405a6015000c10f07941c50640542e45d00f149005904008400c0700c0f14002c80000848141c008949444444005006071004d542da40c0c3d070403508545004171100038010440b40440360030500140116607008426501d00c0664070f0b540403c0500c400a5200c034505034445001c07040010751080f8198480802800c001c11b040c513001e4106414042c058116050610780400008141549038000b5401000e58096600100c21306a100300d0a980d00802c000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 121540377 1250 121539127 121539163
    0x801020901090807140603060307030b09010209040605030a03080420120c030d05070816060207050115050f0607030210050a0b030609011406040204080d0c2a080f070503060411030307230c03 83
    0x140285d400d040f030003583c0c850310060a8840a680766543c41c2042401070319011611f0398003160400860900b48941c00282a00324001c080036652a60014040e2400400007400208084d418140c1c2c0c03c03d15a1040fa0213400402c2001c01010540e000780e40c90316104483c074420f2003804038070340700c503401071085400080d00080450318000c00c0c4d1154855030071390903d0440e1003d03400c218010120b1000e114407040f0009283c00c2511491500e403c0150b02500f43c2070040c410202040400002030700095220340600c00c0400124141c2d840c0e28280008115100e02070341c00d0302039031003003107500c540651141304886961010080b554603500244400c80c0a94019004158010b503458030751130f03010b0b015548a551041c140c440036161008001680680d0450364400200e40290081c001d6090510031608100c00e1280201904c0d0300d4040003c0d9640310242000e004400d0919090400e0385061003102c2c0b1090304240c0c503040d088040030380d60540c807404082d1031415001c1d40307842c10784900e404603458038010206a50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 121541627 1250 121540377 121540409
    0x14010f0503130c0311040501090e0705090c0409091a10140108190615140703020717010615050a0e010903030518040b031b210601030303050a0e070801020901090807 72
    0x540359648040c155481c60a000d92000303000551011846001c2c0d07204260030b91019190708244419200c040e000a00b0740741c1041845608480d0014450040300c004a90010342d68a90440c104114480c5030004903c241c10703e02e070309090100c1c1c0b504c084080f6102006982c0d40340d507004a45c400222503801054031842102500c24825845140082e4102c80e0409441001000448641049542c1c43d131024000529800005d0651600800c0c00c0c0c03400302a4109072850404da07643c0003900c41c2464000e09c5001c0310164040e100f15503096111364050034040ca540f80a0108140c005881078002a241e47c001598040e0f02840729407003600d00c5001c030b95040c4c45184c100070030510380e0010b0a000703619154015665031440c0c540c4d42d82c20403201d18600b42e810340114030f601150044c003035000e10004040e500c400c03284030300000c3c4507000691641100d8140ca0000f903c1c1e21000600409803c480e1000341a9124003100811110010f60040c032018000f622401121aa5615a0f540302c15a510500e4650486810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 121542877 1250 121541627 121541657
    0x70801033f11100902030c0409050f0d030605120f121e0415030e03070506010b0304020d0204050709050310060f12050111030f0f01141e01140d090b011401 68
    0x24840e181c020800101110a40540118080c00800c5600d40300010740b901d1042d100b400400c1c08189032207031000d40306201c0450b8076000300f641c580c40b070742a0502031540c07540d401c030910030280700c82c646590b090002e444aa8891400c000c01a0038140510361081107a459841003241c80000c180042c8801c800c0a0107400c03400b4200c3c10241d4000700512240c428900302e003a031002c12010002c00c0079040002c40800310b8a0704107001000c0324108189502507510405c11100031450000d40213044400001019036280d95a2011a8440710502d02c000d410600b001c060007115a04a03854030250350094084403007001820107505c09032000303407081004202031041d040c8050300d910701c00c4150305030060b40040390302921040800c00310ba004445101950b070529043c401c640e40200b4032a40100321410074102c10380310754800205440c0a00341d180d100c0e00703000c45146846074081c603001400361012040450312016103080b8400076006100c0308a07200b160301000401c0c0d1000031a03e07040f60a1041c0d550b10b14014500e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 121544127 1250 121542877 121542923
    0x90c0306150310090c09020c060906010602010204030f0b070e04020f09121902090c1315020c01021c03021605061303030b0a060c030c0611070804090e1b040f110c030301060807080103 80
    0x5401da03610114282c1c0806c41504500080400c103034001c00a103c5850301442c0346050190680050007164010013003000421103c0c0c00c2c402c2c0300b035080103080200fa1a41ca00c00c0e1910300d428003280350070a002203401119014071101030101c0440a4070030b0020b5842407e1003940b5014040c1244560306030141841d005418124225548900386e1909145862108001c2121071a000d512643d1030100540da8622101d50510116440c1c1c05d00380002e02042d1340e4036200007404406c810024040560104003003120045050b21114102d400c4002d850407400c05044c40020440110401e902080c2094040e4900341803180c0b040e01101c0041c1c0d034030302c00c0026960b07003200d000180c15829280c0039240c107100c072803100c0f00c03d0060802c1e40c0b10310b0340b0704e640703920782140034080c0c4803454101500d503004040704150f042d25034071518100c0b10080f0342c0000d80b004076055120080040a044144101000c56090003c1c4c80c000300450680308a51581c4040ba680e0f4007046170418401d01004080d04260600d024801c940b403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 121545377 1250 121544127 121544141
    0x1803260a0b1207090b01090e04030801050405090309130c110708030406032301120605071718030d090b0114150d020a1e030c0806040905070b030403030b09090c0306150310 75
    0xc21001d0040048442d851411107650009111295140b11303ca0041d80c00001c0000100486179580c001c2c0e260546001c0c1c046001445214011900d61000480562040c82101c800c0318006140e081031256041e021401001d03109018004914800c40e84840080006042421502000000d520f481d00b000f03411009040e01c40d9510b0015595218407a08040c000c91401e40640350481030311102905904048041e00c6014105806106002c000c948000c100811425031041d01c800c4400e480340c3d21880c00c90304d18071803002c02c441c0c4507180113801c00030400c080c064181200c084041c0c0031010525407042150031200c44920842c2003400700010305d41c400180d0054500d068403400e00310851b0480c683c00c804c400d40c801001100003691178078440200c40d0848002600305100341d40070814408039a60750b0ba40d81000e405603281c2d480001c400242018071a8002020441001e04490041e04019002c13596408d80781c41001c2c8a405250300140402d503003907180707103049000100148020b040030910f000003002c103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 121546627 1250 121545377 121545379
    0x30904020a030e030406080a1103090a030c0c1503020c0d0305010803030112020d08030106031d12040303051e0c0f0705010c020f091503060c09040e031918091803260a0b 74
    0x11040341403c402003c0c40030b0402051540c54603200c0d4034015520354101d4442d521112031601c2c050007403000c043c000141c82c102072071349820130460f23803611410b00300b031a40461760201030500e500f40301810300190705030080c2045845000c115070300c401541314281c080e07034800d010f086c001e51b0080c401001100c80c885051281c1c103001901c0405c9580030394843c800e16503c2600042d02198540c0543e1240c04030402c3c01c90b0307c00c086031002c0c20040043c447d0010a80c413a6200141c10010080f13260406c1c001c280441e04505061080056640c07801c45600c2d68448d115100340707001a0061020024a55014040c0f422a9660013402c100c009102c5004200c0c1e20000541a4451620383c4481421280c03410040c59010b6142c03851040d444001407410081666a0742c00400b1058109200700714203400303c03084480078a800d0b0b0410074980f0407a0822074800310410742c0940d10f43d030704200164108644660712000d00500aa650540da401c10841c65600da040c100d551001c00302c003072400100380c102a60b001c01c2c01c1c100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 121547877 1250 121546627 121546631
    0x3071b0605040f0b061e150c161802040e1303030b0a03030503090d020a0f08030612060a051006020606030d0302030901061e050a120f020f150c0606130e030904020a03 73
    0x20240c90310001c036401110100d072610040b1407080e040c001800806a8001d00850341c0342c4c400a243e00c0c040e100d18810301310007401060301043d000d507403401c900151002118100100e4008001292010740e05c102c041c410024100820020991116054001c42d0144c8030800c1c50918141c0324151b03c5107403c4054601a0100b594418000045d50340d1444880b004501980c0d46d10303140d060920f132841c1031640003000003096600500f00c440015641004402e0002c0d0000760382a01c17542c0c3c4202098100c41c600e00000783c54000c560400800c100e1a902640c0203d0300c0401604440c0d48071402640d40b01e4040d1003455040d800280c0304440548070750001c6da80603019400114070159640e0241040d00c2c060030b001800c0c01c10700e00050120b8204444404010505003c001d141c1000c55154064145130920010703009440703001c0070280c10f03203072440c100700c0300c02410344c0c010f540c0c1410030440b948440050300d800303100c0c1c81142142107000920340907488420300c4820156107081c283c44c1c1008003d512208444007415 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 121549127 1250 121547877 121547927
    0x5090402040b0d050610090303120902030c03030309010905010b040c080a0509030903010c170f0708010b181003090b091606080a0f0606020307030801091e020309161d01050d080307 79
    0x4041c1003143c0d40c9036000b00e030500300441044210402c5214603410420411010000b00390b00011400e41c001d1501c1d40014100c11900110b82803200414074a0b40510000041c04507085055012a075094000c100820800c1000c10402c0103503524901108005a440408200d41d400c4a0b84203903004614981103920b03140940c0c1c04a401e4910602c680e001041c081106034150b084030070b143d940d0005c5101d401d08014038050202408034041030154201c00c0d2008140c0da0490421217030030449219000301900381220011a00030083c0904d01c1007104e190142c0c1c000f00312145030000c0c0c150282d281e5106500b0302281444003c594200008100f41e249940f1118000040c6a4620803540079003901d6001c0d503680c039164140988250010381c82043d0700f0b49003c0d50180003620300a0a00b08038a000c01c005a0349031941c0e81c035503291a03520351903007070040c100c104002040c41c04494150300d00310310300c031400060743e0707035242003240350780102d0b401070700700182000002e01c018801e16101d5000544160141116 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 121550377 1250 121549127 121549139
    0x304051503060a0503120a0810062c03071215112d031f0602030f0d090312050a02210609040f0302070e090615040e0709020901030f090605340509040204 67
    0x30084251b029110010780c400a166200c2465540322080f07103406140289050740082c018402001a400d8103204540ea50a61000c981c50a10160078020304642c44a0348840c041120101035000031280720604044c3ca072004041802000e0305020040c080c241090303211000c1404001150340f650880080480d20561300031101c0e005035004034180341c2c41c58010020709184038054619500700c002590f2040c000c440c1040459000c544400a003600003261003482d600d0142c07461603055040c44c0485007428204110031000354042c1030b240b40a03c00301013a0085907c0d100203110020340d00d06821401083c0050081005101e24546c1741d8030074811a46000d03900c6111b242d0301903040e5003801e40d940104046c041c010340d0045580c0c40c0c00400300e400b080024455440203644040c18072400350025004030741d21050380c0c0640d01010940030980381c00e000761041440c0440040808076013116110b000300c02c200c868600e4408a007060034990009034520100c3c1d01e00c050390b2030740028024581c010303020071010480d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 121551627 1250 121550377 121550383
    0x3070504180606230312041a04050607031101150605040306020304030c02100203030603011a030a1401060b0a020a0605010b2b020d180c06020102210408091f0305090304051503060a0503 81
    0x41402e1510b140b0320f140342080401481a400c0301082c406d502080308014080f6501007120300325421100c425a4000c40c5012101031809554071940c1c0c0010080390800034103401800b20442c80881100800886a00c1000f40c0b80b0120540031300000030341c0a000600004aa0f5030045800600901b071400c3c100741c8542c00101484401e4240100503000441030206a0900f40103501e00015100c850104408206000c2656050301c8032024110340084080381c1903100c020f41c40100035001c1c403120b042d034071110004065601c040d5280f00719101da10300320002404001d20802c1e2140304080d4280308414045030300358172a00d03d504040422000b40d00700950a8446e00600c42c0c00c10300050403c004c1114040350408603c0841107070b00040569004100a10065000c85483c1040c0860083d041b1842c0e241c4d801c0c00811030050100c2c058000c038007a8820b0f8132206040c800140c0a140301e542c184811390710701e01c945840b8052403050310b40145440404c1000e000c0b0b454050760b401b00001e8402c40d1706540c2ca40000349 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 121552877 1250 121551627 121551629
    0x3070c03150b01020c0f010f03140106020d0801050303090a0317090915030f060f06011b020a08011d010c0e0105030705070f0303020417032a031c060f050f03070504180606 75
    0xa280c6441c0039010403900441d000303102012009002820b00381c0d0701c140110300c1244480d2203141c1040703845401e441095010780d02070982440502c000084540c2c459001964906402d100c2e0300104c0c1c602c034000901e51400200319208558007404d4055120700e159515003091001119150f1000c40c00d01112840703440c1d1144891048810ba0300284203104044241803c003403811000f01d4064112204010155023400000e5030882d00078a0100e8560b140c00d0304140e030401c41820300a50040c42e41c2d4002541150540010300d2a51144490138541c070054071840f4222400315900e5004218492080310f0190b010700059680403200f030a2103072a001d40fa50704c000380404042421408250302050500084000340d0f8602009440e46000b540703010140c040b0300c28405401e241c0e001500b0b03918404411003090a000351201d1254141744054601c545004c004090400c5004004055414440008080c6040490060b01c003501a000e440028200000c0c0030181c07404c014220f1405182600100000344a886100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 121554127 1250 121552877 121552883
    0x90e030a11010b01210204090e010b09071b060f020c010c020609070911090405060102030c061003120c08030a0506010e12100f02040e0a02030636090d09060c020303070c03 75
    0x16a440389004400303466512072040110700360707142124080160340c001c0e44001c09500c02445034540040c0800c035a80107032103039811054209041c07020715020b0013015013041c9141001180c2154450303448003012282034846290380d4010010910850380425010740c003039480003114110151070440d40c13100070f9007568600040d2100581c0718504102234110103004800140c03c003110140301030900d180804195000b21144684034503907030000315150341c4c0200100c0c0c040c0c09096040c0c5280e4a89425004e00d0aa420f1006030360307000c04c42c42c040d03561034480c824031060340380d00c124038033300310344600d06400d0003000014522410320001247d0401280e940d4081c400644901e42d00601c6003842c0e2860990949091460035039026006200500aa401100d01c156021101540041e107039502c1c00006801000000d40c0c011132829940814241500d205d03180c03100c0000e9082c00b9000503240d001600759504c0c0500d54880008005680900100c1c1c41540702c484c1690009080764141310740398403501c000000c290310803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 121555377 1250 121554127 121554133
    0x191109040b09070807150302131707060909050609041e05060c04050a0b130e07031410080609160b090102160e06150304030909020f07050d111603050d0305040c090e 72
    0x1c580b03a501080080094600310f00a07003030452500011510700c440c0c0015140c24150041400841085500d04200007030907141301040702c803c4502411600e030a414003541b00001e03042c2001085c401d0290050303d00079100074000280566490f121756101c0341e0f1007034244d4001c158071450130000c942c00f040030034040d01c02d0b51070065a5624100402c9000f0b4010361002150300000e01c1020550020254000200d076181e10500d9050354500c001200181500c501c1682001c0e4124107001828251105000c2551010030403540140c5235503416984d100e00c0740c06680c0743c5500d0342a00b031060908101c080c2c01107100c180102c03035101c4085034041c00c040c0340503000406030384900300c00c102d003c0c80d0041d0b140d01c500418409491850400d0388000309600150301581c210207400003031151500040784201c480c07164212042c1d5880607220f9500803c4007482e011511503902c0b943d0780f0703583c8401c01c1c1c1d01c00c1d1003100da000e402085d4012a01d102540036080091040d51103070b04100340020a00084c0c003a030303c01074500b000a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 121556627 1250 121555377 121555381
    0x70e09040605060103230403080c160303020a0e190603020f090303040e0403020c0d0515061305040c180c0804020f030f07080303060a06110c19090c0809010507050903191109040b 78
    0x1000c0b07403806a03030980722150008501500c07520060302d01f50800d806181500c2503503508600c04110b4030580017001041010140d02c082070680c50b0740606170f00d004581e100d01044034404200804002a0341052211020718038040203142d010752b008103c035070058203485080030308500009003503401c141d0111040312441e00c10401099414442403030b074000e04913004199294076403542680e505111502d00c3d4580381e0140070502d00e940305038000e10310300141c04c0300307000b41e03e024905200181098422038120a1541d1000e002c1c8560074014502e1010f490b95507032a580d6916001c2100266007054041d800d4000c101d09499008814010ba00c05064084010740c3d0324106001840301d001c10f581e00c40300030410130401c1d4510f1040c01249200300d17150700301c81d41303500354005400405800c0710940c003440c0030601d03166600794283d410081c220300c244490402003041c0e60b5008000d807218410310004d15850381291848180510f40d2210344010140900f18500da2903800c4404250441000e5806890340300300002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 121557877 1250 121556627 121556629
    0x906090b10080c0412260a140f070602090a0306050408030f07091a070212060a091703010b1b0106080307140c0102010b06030105150f030103060b0a2c070e0904060506 73
    0x360584107204078500303008a072402804500150155024440203980280910380520645100700704960007402c408941c42482e184c0d030190780d80e01803101e41c4045000c010842c6031407500b030b000750341d011512084d245107000910f50b181e800a41c04007041036401140008080f0108840b441898841c80c400c80c1c03c0c641d00d090a0030307004500f9500030800000c02c401ea10043c0100344120250f900c420914a890300d0303d41c0706034800a108820302a000312228840e040070000070301b8840d0000d4071064000e56003500ba9104010b1403420511090080000f144030030004d03505081c0d0500e1002079000d1030540009941621070b03020341c1c196805183c080c2c905500c00b44440000490900c40d440d69150240003c01c50bc0d69041e02042c1c2c80e0105214142c070940d5910004418110100c007111300404032800103943e0396840e0301c1c000c00101840d04c199030240210280104490005c0004580c0d28104446407160006000800c00c0e541000208004200211318074040300e1906c0d4814054012486031202048514040c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 121559127 1250 121557877 121557889
    0x103032f070b04061202040f05090a09060e16090204030c060807020a05061e090a0c05040c0504030501060b030a06060f020a0215040e28020f0f0304020d0c030305070501060b04030213090201090906090b 88
    0x205440307001703600c1088104080c14001070f01c10104c550a0b1160082175517284d05a10041c0711080b0040c2c81c25040c0130b1900c0c01c00402040007a80e1220003550035500c82c2d12032500c98100c2c0214003004003170001108043c0490740c01142e510b58000807500c1160300e043c500da5101410408180c032249100802c9507423a540d061225180c559028244a005001d4404a070b1a00018041284500c500480e038030300340d00c02ca1034415804c5030003541d0042300a000507076491700454115402241c202c0703a120315046020890a20401364410400c800ba4028480f0320a01d07020040d43c60414040c0c1c10034110308100024001e070301417a046210301c07480c94442c2c90000503015080909820081100a914030400000101302d40070015a1803481c0042400c0b0380303030b0341c4510103c3c04001c1c0c080070203800300c00032200c00420950b01c04000c142d014814002841a29541c1e060000b55020f5400000d52022500800000300c6c4025400804424014501040e0040d0344020361404c582d01600514000383c0c6940004545007052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 121560377 1250 121559127 121559147
    0xb09041a092d030f0c15060f060a0e01050f12180d0c030f032702040608010606050f1b030c03030a140720010f0203010807081b09061207031a040303050f0103032f070b0406 75
    0x1548c1c08400320340c0210010706144510902a8148001e4500b02c2c3d925074070800c15a149940e540ca261070351042100480001c0f644210792007180842840784034089040f02003805e01c01c440142e1203070f039129a810303030741600c3c000f039048101e904043d50388000c9511040079204901d0004040125003a60784a60b00601068441603008542c050b81003142c108100d962040803103d924280c486000d4485845181482c425094250001c0c41032102080d45411b9210102c0114000c95a03d8000c00c0b00d212003180d4072400810485886011416020012490081e4203c030300030082004400055407000c2c200c20f1604030780083e00045020341c0041401e01065004109541c0c8030107815240d04c4100c001100080d242000c002c0c0200d01a04c410440521003050800ca564055540b11042d0040000707404221041c1d588101e0382a00041c0c11309003c030b0404414014254103807030b007650b01c1c1e0b140b0130b80041c01d002e03040d41e40c08050740340001e082c59845010103080c07005101500a040700301da80c6030300c4c0c44d87c010410152 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 121561627 1250 121560377 121560379
    0x30b10080907050f04060807080106060909060303020d0309030507051c030f110a03021b060a0b0a0501080702060606090a0b1b060106020319030c030b09041a092d030f0c1506 76
    0xc45041c0005024005480b20031540111403500c0300040c0000802c001d8981940510103520501001040710032041d08040e003610342a40d03070440300c1c42e581c2c0000005d036201c610000d00980c00ae407408180d4a8843c1d0403c44286001e03041040ca00001c50b91541d14000245101594100c0d0315091524100c0d418040da9110781e44184c0c06000e00c89009101d00010301c1613085840605038001400f59080880310020703608a0048802c1d1036183c900198650b02a04040b1505407080b04140c0380440c2660055501030701030600e070ba00400040d13a501d001d2002d1030380041c1d0142d91040107410002108501c1000070301507498062240e464220244000706d14107071041c1c004070709540050103d1254150f2003902100d01d45110b240104860440200070340c000e03c580450240c204000400308003d0003e02c000d010303100b116251405500c1d9803000c294548070b4a405e01010010b0408000d515640442944043c42c3c050304181580c0c034061612000c4e076400c0c1d00402e00340080f5006408c1007502c40710106205540440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 121562877 1250 121561627 121561637
    0x5180a0506181f030507080309010e0a0602031602060d0911032e0c090b0a050901020c03010b06040b0711030313030b060f060d0c020708030d0b03070918022205010303030b10 76
    0x58600300840c080340108010000b00c0f009200600401200018400642d0440181c40700c194581258584075880340310340e103001c1511401d0a6400381400c1401608580081c0d014504003844401c603040a03051044050383d01c02c009000d90342003910144a0300707901910485c000d50003502c4034000e042c2800d0000c0d42d400303403c8032003140509000180e9842c1404002401c0400160092540c070259035004068100030051007000c5070062000380c00000502222400760211410702200b601018280c40c1400b4916400c0b07602400108505210390028010300ca209070345a181e8034025001184c9103070445840724400112810302002482210034405400c40d0040d101e903160400414041842403203400703190344400303540d5030302d0f40035181c070038070100d0060840401542d984085210001000d04514030145109004036034000a050f0560310610103160540c00d4116000f15941c0c080203d1480b982d02d4403001e44580c40c09848420086200d11400781d80320391000108030000c41e003442160342c46420ba24040c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 121564127 1250 121562877 121562899
    0xc02120a11010503070306090507050703120e0d0c0809030d03050103020a12030203072a09050714041a0702010203041d0103031b0b0103110105070b090106050103150608190605180a0506 81
    0x1c14198224084610a08026969032103040c4110300402c1d2070381c810103900c1e1500b0b00340025558800c006140040c00390752080c208001031007045040303618600003580c1c190702c6aa0300c4101c4038080d450030b5981c54025004281820401000309052003010404240029503450044c8110324281d803a07000504807480034414000b50360b0380c02035680c1c070a0410191886100e0380f00d0190b144000ae5007050755441d0280044180c540d2501100060003041d1268800b04105c0d42611a90000c6041034030200c640f090106040800c0303d0b000c1510581c07000d40c090781180800c000c0030845600a8558102ca0a2003030400291076144d41001080070000d110212a048180b000300c90209042d1405107042d0780c0c011540794102d00e024801a1040d01c580d07480103100c0d4041c2410030046290650083c801c88000380c030b041c06050711402c1841120782c0341740501c402080103003000c40e072801300b1121024500410b05400041e0103494200003140c1811003001701c6100f41c1034404000c405102030060310b4100400303030781014100e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 121565377 1250 121564127 121564133
    0x703050d0804060b030d08040501060504150b0d1503030c150b09180f0a080405090105010806031b0103020714031305011107090917031806010506041d06041b0c02120a 73
    0x405400c9990001c00000340c0c00315007031000580c015489004c0040071a14030344030808001e0000e850484054900d03506c0d114000405041078020076008030f40c130a140e0529207081104500c0d0356040000c0380100243c1d00c415112000064507040e2020354000d0b1070f2010700700c905140140b000c29101006610300380c01c2c401e03005165200c1024142c0c01855551040d04202201c1050616002c1d860f05100072512039464480d0a221140c0010000c0d1403041d05e420040342c0e243c6006607002c000c1500c040747c240c0d020000011003419103020f00760f040c0c10140b4002d1320340000c4e51540002c045a0080350702c00e5070000144a60003217106c24840004240a0a28850004080701c0746030f11404144503081c03407a62110102003c1155144910603090744004145890781042c600804444070484082c2203284101c0c00007160a10b0b0803020303281101c01c07005c100c4607400d01c1ca8406072603903030010741000d030890784680f0356845003061506c0703544012500765604e80d404020340c010481440a8400203040980042c4084404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 121566627 1250 121565377 121565383
    0x601090b090610020f010c091a0c0c0907212708040b090307090f06030b0901020f09040e030d06060201021801170a0506060c03070c15050910140d050a06051002070305 73
    0x1102c0c400321840c0405400800042e07040409507001c4102075403900341c541d08040d4001c05c1001c1030710b410320f40c01910304900c04030401e060311500010540942c08101102c09038900a02d0b055030161407031405580382d500c44142000c10760022250119540d4640e0b0800081c1c901c07051005250305000c2c07410494210554641260900c142d01903410032420020704031007561402c00007080100381c030582c10031010404c4094100240302038002112011180c0740402e9540105001355a2444c0d903a0401c0c92611070001c080000400420200c1d40d05e900007406401d01041c12480340f04001c00300c540016030768210201c840b5004a1a0814041c14450354041c1000c600a29013141d5900100c0e0420015185d25504000350070b50054038410f02551200248520401114210100c1151401c40414400c010350708010b682501600754500c0e084000a0441c1c203130301d1b100c1c900080030000c11a00752480c0003951391001040d51011103480d044c183c0c45400410460400b03626164042070148043c007079103030660f612251 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 121567877 1250 121566627 121566631
    0x70303051e0117010b0d080712080c040e0a0b03011d010e0d0507080d02040807060903060c0503040b060103090611131401090b19140703020604020117090a02150d0c020f0601090b09 79
    0x7020f0440303c109102688250b1140301d1000008140d50400c480303920340070803950b214900894045c0998202032070f05a00540006014000003030805003402d0510903514030200009010f10000340d00c4501200c030300e440070320803500350ec41c401c0109640c00d071014400364291900e4002900d62548000c0010901c0c5a1000541d00c0302c99021198690b120001107104000e07000c3c0b900880054014101c0001c0c900f50066007030030449200e41801e002c002c0c481c3c1025500d5010031100034046d01030f82e0000814642c800d50005a51620070b07480040d000d074860800d1151500304100c110204801c60100b80300d0f6401070080c03014402401d00e040b8203541c0c24030504020354080d8900c0c000720650501260082c00d401500c00b81e26040010700240d843d0102410001d55410007a503060707000c03c0da49958070104c100e01c404164403170602b0000422a080840c0d0034028040011100f00303020318001d021010035000346004006600082d81d004020380d22410b0011400c103c03045c1e10075001d03030b8540000c450541d121000402e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 121569127 1250 121567877 121567889
    0x100c02130908030c03010f0603050606071b030c080c1201020a0c021e09040809120c01050405010c0602040b0703050421050c0f130609020a0f09080a14030f0a05070303051e01 76
    0x144031601180110001e841420700040202c0408400c00c448070849a01442c100c0b03200c401149001565888107804503101900c24503041041081204041080b85034401160600300d6030001e040f81c2d030381e183d0000d644525000781c00c1c9608407100c00070751442e042d442e03026121112070007185001c400389005414498000c0000313010300d10340f402000c2250580b01300000e103800c002c0e01403082440e180c50941c0740360b80318641480c4500d00451028001a40c0000c22241c4000b042c0c583d43d140c14281001912104030134003080b1510b079020480880d500d40c040000e3716020744682c68080c0c85034103120480740800124860000b511080c0c0a00790045000042c02e4134511605440300503152070f01c2c4021a0044107002d446041107414002c0000715104c00364014451250540c2c0d4581445c1c201c0f003411140c2d61054030a10000b640201005000328080f1020407030650205011280b4000f00499546030310b03005094100d0104002143c590103143d0540581540988001c4a54034040c2e050a4450704e10701c0103008030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 121570377 1250 121569127 121569139
    0x20d03060f1d0c0c030307030903110303040b010303270b0a0201050c030408031308091f0806030a05070e060409021201050604060906030302030304110103020c0a05060907080c01050a030209030a060501060804060506100c02 97
    0x1040d45034820f4021a014800000141c81d520b00d84184003402501e2181412400076100000e81c40c41e0348804019240241d9000030021496403071900d0488000644100112000c141010b900204818894011009040e000407040d118000804c001e401c507040200103000d06501001044005604031007200da215420140f00304201642e41820740c40c074007a4201d00741d0404c01400c01c80c0013240030141d6002400300c166403030000700e27607c0c98145038032803040080c0204940e00054050040211040001c0e5026070050000504d200c140e0300000c440d003480d54503161099544030184000340c209030080c0d10150039030301c3c1e05001d07007851680c00a6881c800204040d240c03010200004990f0307880b035011603015505040840e0079425032410203945803181580c401140b88613541c80002c1c20007010480503429030058603020f00744628440140d02940c0070382180d95060099124690001300da52185901908190b038030441d1900d441d107847c01c1100c0d070140c00a88690031220074400041da001a983c6501d0b0b41c15a20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 121571627 1250 121570377 121570381
    0x70219080a02031c0504060e01020c21120708010602060c090604051c060c050a020f0105011a0c010608060a0603060b0f030601050607140d0c12110316030e03010c020d03060f1d 77
    0x100b00d0543c05442c1d4064210a0504039110450300c1e030340c021900550140c8810003403a0302003d5254200e00c6070452541c05c1d90406102c15200300c003401c0702040100a42141140b8000e040d807500d0302e14040c21524040495043c1006000d400d81c1080350550040300784840034941200a030003c1c51a00507031050a105840b00b4580c2c3da442c403400c50040403038070303880142448410114400a015508881110700061142c00d00c403441d14101402014101d80d41000009000d05c110640b00a00390710082084200359203400380001c0c03840040044500c109003144002541d43d0861070444195070140745000e102d413148554515180da004562141100c00032602560780d100d003840c180407440c80b810f03d481842d025a1102103501e0381c1000448050030b126469440ca0b0035083c003004c0c0c800019819070708020340c0c000e000400b0340440000e5a11655406400c3c0400d90b050748000003403e54000890000042c5c0001d001881c41c0b58150007090040c02d91010b0290405080210151818030311144404100c448080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 121572877 1250 121571627 121571647
    0x70b010e040203070311030f0a060b0f0405040b070e0118030302150106030504050c13060f0b1206061309050604090b07020d030614010509041808030408090907030603080a0e01180305070e07021908 86
    0x1111100d040a200280d075400c00d4035007032a900800030446101d00ce1200584108414505440ba0a11a950160b580c2807036032100d020032a2840340280c41c00b418050149003100d000d10303184860317000962099008119944031110818005c0c03e06a1080003803505080070f020006001051818104509407000c403400e0000c0c030f03811800340603150b11500071500031180210342e0541b4a4002e20311402508040b01c4c2e6074880406112030307441401ca00f0030070512000414401c0135071a800c01500018020004a0581201d0f203c0da0725540d4140c03960b101607408841c7d148200ba4140c000c1c50300819030700e07482c0310590401000180046c40b5800f2101d221351b686030000900c0f200c0044d04c0800303050300310500c035889146ca4030f4414041d13404040290b12074074401300004e0783c951117030165000345ca13842084d46061041500040d10340c80082480b09050048a5140c1d00100d04c00002c2d0f000114001c0004001d11450102061007801d00075040303a04540120f400111181c082c600d01700c3d4145d5010484607522900a9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 121574127 1250 121572877 121572883
    0x6050a0c0615090606020601050301151203050d0219020102070605091b06031305010c18081609090f0203061512010b01050f07051504030507060b011706060a0201110307020102070b010e04020307031103 88
    0xf07003000c015a8034150000c01c6655000500c2816294260000c0080e000703580301c0300781101990f104804240c0400c030030a8000a10400160038903442e540005418503100094820103d0300fa9040040142c0d400309010060040501641d03030400d00d83e1000e0040c16056025000040d05900a05802407400001081c039400503105402c88464102008208401d00031600070003078410041c1d50b000b1021082404918100045402d821031010400c49001c810b02d00b00d041740240030664000e44050b81851810409030310140881c910440c03031101c811140c01c07400340402156498410480d0016807600003e5005a41c0001c12a505080402c240c01d4450b40c8502d4203c1c6010203000107900701d01d040c0000d21003095080070180840c0c9100d0304050201114002c01118203184000300381101d84105000b00306281450b0000b000e0950540c40042008407020b000b10602d0792060310000c0c0140e40c0000c0150510204c150503d0241c0101d451040c694101500000d586082078000a002d042030040c008026513010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 121575377 1250 121574127 121574129
    0x3051209030a0602072102030310060c020409060509160b04050a1e080d020c01090608090c060d020d050c070209012c060a1715060105070f1103030906030103060b0a06050a0c0615 78
    0x3c28000d6549410318900f02041a15049030b8208200d080381040c00300a00100035a44180013181c03403181051f00d084011039098525180c06d0760003030b42d251158004200d05009090bc291a03080080c81d8140f0704000c401c011004c540d00c107200e20030041c00144955030b0f842c1c8203c012103010464040e40e403484210000555040e81c1c4c4030000707510554804000c2e60b6000300e141402d5136801d8031a003103104c0d660b41d41900c42580860b02c41d0503d03000306512698518110000d00388441c2481b40050822091005031400c8440a41e001d29844502207090b008601d001c90405001d40070300c030514a0524011586050f805016400300c0c10300041840000e885601c0301242c00c3c0c020b001e50904480039568951000c2e48501074000549522130401001500c5540503074115503c19511180780c41d0400400d44891240221a00103036070f040c00104400c038070b541c0d29075028501035405600009071408450080108854880e445a001d20205001c41c1203030300d8000843c005035035040400070035044a40070b140c1c100a055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 121576627 1250 121575377 121575383
    0x6050604110d0605011d0d14030c070807051306030f0308060612190c030c170a1d030c0c0306011208161202010209041109150a020c0d030c02011803051209030a 70
    0x4241600718990903000036046074001c6c3c071405191201c01c2c1d006000c17116500c1c00140c0101d00420b039900000c1e0848070f12600c2c0055a07003a00c3c18111001c01d0b150030030f4040d9010300000d91001400303110361314001c0f0f00780b007400580d10f02c100b20081c91995032800c0300b5174100c005414002510001845602c03680f0482d2a000d80540d13100169190011900e4031003007005807000c070aa850090500c091500074890300140c100181c035550f1f40d20a2101018400050042c09035141c9074032030a0301540128091000b0f103940e4464406144c0742c070450b05006103020039800441d44207502900040000e01c4a00f0603d40e1045c1d00921482d82c0c1c2c14180581580c00100b107040245100c80d4401414031559041d4094503079803400322401d004d450810080c051813805814482c99100d1044000f09551190603001014480000d0058545180070710000a545604042e410f40100b5030b03070f140c107004641c1d002803890042c0784120302e980e10b06030031521110f0780e03100c02c0c044503007243c2d5000914401c140d40c1003101950301c0754 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 121577877 1250 121576627 121576661
    0x41413030311070f1a040c050607020a080a1a1e0103020103020703050903060f010801060b041505130f090917190503060f0405090102120601020318011b060c030605130c0c06050604 79
    0x205a10300400710b8140c0b1541030b1260440000441141c02c0c45c99183c2c1e008580050024506a0a000c200521548903000c126480065042c0c0051441410701c8845407090140b600c0e9100398503100c500e510002001070000204801d0b0300200c603018441100300505581e020318006880d482c0c0c130f10381610a48a641100c43c0d06208080401840d485800041381c143e95000c4000e000d003e640d06c45002c1103018500680e042e00480018120780c20b841240078100c1c0c005900d0400c160f890b603440015865501c0c680152112030b4464072240203004000b500311184000002c2c541d4a05a480a0f2440000c0c0907861181c0c20824000301150690780c844d042403d10302801002001142000d0540e54002e501502c2c042e8101090600000e03076540c00402031390081ea080201e581c00d14551b150044070040c280e2000303107295495601010000c601d00344a46640c0d01c5043d140020300c0340c100400c1060290301d00d851100f1250a00040c1441e80c1d074030940400e0865803044d408a8192615000900644a540e40d071050501c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 121579127 1250 121577877 121577887
    0x101806031b050a0605250c0314010207020f09070807030908040902040b0d0c03020322030203070602070506090f0303090d0516020d0c060e060301150e01171e0105041413030311 77
    0x451070305608480c8201e6640c1c80b2160303500320941e042e010b0b1800540151a644548200d85c13005500443d07071444c403038500780190036100c1e27441c401d801241c0003480349a60760201d1040d046042028644020b42c204443e415941c1c40c1001005182d408001c1a18040507240d404031010040101e0550300581060300055480f035480d00040b00154012040d943c500c0303424503942495450182c401c0b0307030040c0078a6020b41c00f408442c84a900408401100c110704601c020010000800d60a2000d050300c0b42c4100080d044a0030208002807a20140c41c02c500350fa50001c00c14814819400182c80c1040c0145060075038503149060111400c80b602d241003e5001428603181380d08100d48580300105864081d11503040758400c1400b032110302e0009005030b042c80601c40a129181072302030301c00c120400f6414034080000d006903000c9524014400c1d200c65a8010200644a0303d403482560f00c14090303e03080d90200040703002c4100d030100c0c000014080000b4016604131403814035221360030a1138161880041d903940c0da = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 121580377 1250 121579127 121579163
    0x210b070c0501110f030c0a0504030803010605030103110f13090f020603012d08031206030307061104170604050c0f030a1a0604050703090f060510050904050d140310180603 75
    0x50321203400200e540e9480d00b520a070075002e030001500c032000068007040d402d50ba03034040440d01543c491541d1005124081c4400000121800c0c003c1d0301170050313641d07084d44a52451500401c0b500c0204100b500c9801e0003d80d0f0141c5440d03644a190500100d2440410136241504000015050b10000650070500000003c54201980381d001c115001c0b03001e50402e0b1070703010503c103219203642034010910303140c07c100301c0e80300c203048152003c94020350020145d80c07412401c0d94808044814942c1c6015000e20081000c0102551400181c403d08558001030700c41407400b60754030754452950300c450910406042241078485d440800c00140615408555501c0850108009000317040301200d01da403045081000140c1038070712900a4040940d80440c3c0c04281071269034503c070103031000034014601c44035801c0000419035942d0b10a1400b41c6e00507c042c00f12031210440061008903141090030b0b6001c0b0801c18400201c54140070074046030001e40107040c510400c6440140070b000250310141c244002403040041c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 121581627 1250 121580377 121580387
    0x6040e040b090706020604030507020d060f090606030b0601020a0305040b0304110d030e0411120f0a0b030106030804080606040501030b13080d0f0e0625110f0706020718021201210b07 80
    0x25000c142c2102e5400755100c0e0120f90394182142d0040000d20f0a00100700107081800400c0341c0c56104410200b0f8551900080404480080000f60344058684804000b444641d24050340c00260070b2000c1c2500f02d031a0380300540319114a02c41c41032400030000001d42031221002036424940d10003030032143e4204090400074400d0010502a9110350300d0000103161a1400404955408080d82d1003a80d039030384d9028100031035184c01048403e01907160240203000d82c0d007c6c0320b15805144501c04441c2c45508046500e032501303030b001707121600651801c1c2c014000300e441140b055600095452100c51800035901d003907a0b15003c0c042000d000c840c20b024403d00c2070801034105c41d65040c0240100c07003c80ea031705201140d01166800d0081aa510030b0b080c070111030340c400c61806402446000860341c100b5120400d091411007284e12510058115190901082c02503c0c0c2079544940c1d00542541015030f10744040039414010f2207000480204414046081118500100707251a00800148030b40d1a1220001d84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 121582733 1106 121581627 121581631
    0x11010b0a1d13140a0303060f0501020309060703120921020d0801051009030c09020c06130309120f0f06021b07030507030f020102151005041d0d030b06040e040b 70
    0x70124242d40f02e092101d400920041032910102d003801400c9031042c0d0440400404441010841d81ea800426101c03290000c07661503035169103a1405903410031585050a020300e0600d024001804507001200003021000f40d83c083c408441202c04076265080c124010010070070210040c49603040109400c10015211b040101000f5141e07141c4000049456202200d403d40000b400c1e25030b00010b222494001100792441c2900901a98001c0d0031007401d401140c0e010007005225009200070040442e40494003c0d03501100400c0f1814060040d502c00c860341100840210380146030910000303041d40449410001a00381207040d96205400031481601c03c0e81140708208000d810381450ba0f0190340a401081d00d00b05401d4070300004d1105441d49c010b0383d0074030041c0f088089025564041201290000c0f1841c0c0090701803017040009001d0301681d0031040c40050440100020000c0120b1400c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 121402877 121582733 := by
  have h0 := BRFrame.cov_init 121402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 121402877 ≤ n) (h2 : n < 121582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
