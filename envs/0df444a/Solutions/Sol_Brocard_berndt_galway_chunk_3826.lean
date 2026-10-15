-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3826
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:47:57.860683+00:00
-- url     : https://prove2.me/submissions/7094aafe-6a46-4224-85b0-40cc257839bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 687949640 ≤ n < 688129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 687950890 1250 687949640 687949649
    0x70b040f1104020a032a171003021017090f0c011413090203012103080109050619080d1115040b18060a0c0815130c03091401050907060c0b01 62
    0x20088404101e0400034051496696615401400020304001259154000440d20000130328a004001c00005407000e40ba5202104a0002551641d411500d00c0190301401c0d0000349111126250030385036000708140c0c0940e0040280466100c11900302201b070040b807040d40c04081000504820036218101c07030b0320792501480d41c50401c40f91031801c5c56801707003802c21252400d183c3e10990860070790b9180300c000650000d00c52014400b244001e103102c18156100f10038012503040e82c4030440c580c20013000344000c02020740040d0b08185a000110000d00421200c04050120480148404010024000d01c181800710010704141c020010740e20a80c218040e007244c20079803190b0800030b650741d41d00d081d604001c9a60419203462080c40240420071a0700c1e4000d03000c44119583e01c40d0540c1e00d152a4000052140c505190001e06100407103c0c64800b5502400702c203e864a030219202d0703507940741c480d40c98502032035a2801d80d654005010360749400304501e0005000c14180b660031515143c030340c140b41c050140304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 687952140 1250 687950890 687950903
    0x10e04050a06020901050d050a05010e06150a1b120210050105030a050705100516080a120e060403030b0a0b0a090f0504090b0c2101180b010e0607140c04110a02010b06070b04 76
    0x1c000d0700c45c0e80180140d0314406a84c4804003d40e14000031804050902807040c02c6c000e5000303e01040884c1401000401c0b215401c003541d91070444003001c212407a41034144c485210086400a0200181254034003040d100c0d00d131781c011b101802444410101b122010703804240710741c1c0400c0803100015000b0400c001141c50460350405a00c55000003501d0b1481030003400c00d41590a140164100b0200348041c100b219555680c8401e030342031407a10101100d903032a903080c6c059400100046c0029129803c040c0e08660040c1c05041075564981591860380c00c51040000401d08650040c89580c5241034080001d00701100d0500c44003410380c030b8131a04881c02400035510540002686a040d4040c84840701c840f103100580c10005c1c2da5203005005a401c41c080c019500c2d00d00703021050f26158130461415240c000c0042202c1c0c0341031160340da40c0384011602010b940c4a03019604181005944501c102e085600e600d90740f96a071844a840001c0c01c641c100410103216040501c454404910701054503507100350b0122 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 687953390 1250 687952140 687952147
    0x180204050613020408031801031812110304141503310f0818030f061617010b0421033504081801020f030304030806210a0b010e04050a0602 61
    0x7800304140000c2180b07101255400003a0001e0740f100c000000340f20301c10f000e17a002c80e8500314000c01103095070f0000c1601400b600e1004036603070100e00e09001036940800303103090212034084018411411504285d001c5800026855001c482c02e007000f0110056000070038600a01c1d51034526500946000c1400c0d14400407200080d01c1b11035031204e0441100c2c5507401005440340d4014924040702c1c554010703400ca81d8411150072080750141000181c0d00d200c0c028001c09071100c0c2d9108003500161098500c41c0d0b2041281d4151100b4800d50011419400780c0303c881465a511400c0c45880303018050051642d9501120301014140880d51119180311412081507821481480300c20480703181355003444141d201d045404041c041009445c1e00184111504d241c448614940f00500590b107030900001d0402c801d410420000700082c0c4551403d960124000b03290720421b0001e00c50b82c5948501c0c1d070300165541c1e84110780c00310500000344040790043c542c4400c0c1c00380c0c51502c3d550301d0751191440c650081c00c058011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 687954640 1250 687953390 687953401
    0x203070203040b030c07171303110612090c0123190327050d141602010216030b0f0c0405010f08040213090602030f01080d05040611070923010918020405 67
    0x3801224010100e6502c3c4580300c1c14013441ca50501d0384a5401100d8100e4802810400c3ca00100140e42c503900d00980070070301040c6141c490b91484803035194680d40c041400c02c072024091b80700e441c01501031039000c401054020100e10000d450009044d0301c030740910700b01a403035206207031501088504003211400811042e1400d0345040c0c000d00000c00740007066035140702e640b110b19100c4a01c9840d80078015000c64000703120090064a83e00c42501c400e1201c0c110402072861008103082c80034210a00c10301c100c80b11264220501c40481807542c10840724111401e0612500c01c00b01c048d0300b0b4001d0503100c1c3d035524143c030307103000a0003011003540000140103003000058151f40d10041580c4200040c0ca00600680300d09181c400c000358400c4500e004060083c1e0000b2554820003c3c00d010b4041c0540c40d0300340703001d0800b54240c4491100803c486100c4c03041c0c100100e03c40c0e8040c01b40e1038030b20100a0402d625100c2902c00ca111006050700801142450983d440c0d0145100003110407800e901078400207401d8644 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 687955890 1250 687954640 687954643
    0x10c090305121e0313210905011b080a02240105220b030d030f0f0924020c010c11010e0607020616050c071514120106030f0e0604031e031e02030702 65
    0x40c9103c816007000110801c000001205641070982d03104007800782c0f5000b0205081c070071610303420341d44030700059a1100c240100d50084003038480c58183c04103140381c148801da5031010300c2d83c400754120f001a003000c05441d132040030700b2507020b0041e028400302c1c003007030b6040401140182d01803900d04580700c140502c01054040080d4000d074006800502a101e0032000c4d0a400f0300035260784581030100302d241803001156694548a9505100d611141180041c0d81030550226200918041c10800c1341d4204a0150540300c24030801d1420141516900340802c0c400700541c0c215051900103011640043c4200007803141d001c5002c0b035002c8421107091410f843c0c07501007190741e402008070035003643c810003c010428414130200c1d614040300340d0391251004101140c031980c05010340b1900078a03003e944c1005001d124040d4002401c81c0d900f200c00003840141c0030081c2c0d4606030050702e080e40810441a44040d1001c00981c0c1039000e00380b0790605020015107144820030030b1280c000c81e2036000c0da0100118110a20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 687957140 1250 687955890 687955927
    0x1090b06010f0309050a0302071508060d03030e07150815040b0d06020307140c03040f06023909340c121404030b060307051002101508010e0708010c09030512 69
    0x100442154501d003018171f8041e64645a40c0900411090a6880d1042103031050384030b24032500740940720350080070079554198040d006080c04c0d041c03140615900451020503440c1c041825286d01d80d254525810a00c00d520320b04038003030a405001d01c2c204040c008042d1164422020410746c04200143c0c0e83c2d9640c2012107064955840c0301c5c1c1b074a40001001c4101000020291090b100c0d10b52004240d259181d400f039907961243c194441c03114281241c0c11700100c006c500400c085040b2202580544401c1c4000114101001c44012005040c8840007100c3c0c066100c2d0583d2110143c1c0c040d210303071a89682c4d030292011224810007000881700715002189940b1a84c07480c01449002000e0b0382c3c450752030b1301d88418001c9040300d2181c044d03c00c5440000340ca01c0e00c2011030510707440c182c016054882d200b0b02c900c40500809075220855040c5120001904102441000e9a10399a20081e0043c0e034102840c0b6425100303c9080b180030000c00c0c0a040c00070a4000c038005203866a41041d0a03615001ca0f03038200044c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 687958390 1250 687957140 687957143
    0x221203021b1906120b042018090a091b122414010915030b0a05090a02120c011202071a0405101404020f010c05030328020c03041701090b06010f0309 65
    0x1803140302c00140305a04418140d0440080b61024000110100248400c490303080038054808451100c00041c0781d4442401000c264206202e8030b041002c0748008500d500400380c6241c5c1c003440c0e0310041032041c03203074108241401308007503418040040e1400e1b05001d034400150f8800340c42040c07282c80200b46400c01107030801130801001000c3c0f2455180419000381c00e01c4c00d1140301c804a003844000c1d07400685a95142d4152940100b00032240d4a8041070759000703000080c190080c40c42240c00381c00c003698400400500d0460010020502d01c0035507000100141c8200c81c54904081c01409500009880d03c42913200c43c3e040610075642a17621410980d140112007410200758502d48021000b2841101c03103254400c038000d031642050740c1088801100d00c512800d01c081c00641091020030500c01c0c446881c0303000f00100c48030680c4000c4101038100120b03400300c16003d940350310004040203a48220900c0da00050517101c000c11401c000c43d101c541c0a214010000f0741045100649281420700903800032892a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 687959640 1250 687958390 687958429
    0x1203031b0f031e11190207240c1a07090509040804050f180c030117150f181005060306010602030c06040206030403050c1605011d0a0b031b221203021b 66
    0x101030182c0c1d0960035034880c0015607950003000c0c0e82402c1446c000121482250000054107055144000c50f141086446500c2c9404005604038414041413040300e002240701d618800e036003103e0402040180138945540d01c00c5005600f01c01c208008161198141d504550003500c03d904040c9502c1c1c0000c0741954141c0500a5940c03005050040515001d00035605995242030500000641d983d9501d689040b40c0003034030200002080050301010074071110582001c010f0b031803108010240c070200b6040070200c0c50030401c500d81d107000700020340c5000c1140c2801810316001441c6045c2d000c10410391601d0300280b010780911070000101d001c0504c46c4044920500c6402c0584071742c09a02018403010030740780d228180c0002c84880314425141802c42034900800300c000d00c46648107141c0052842c5641009203042034119004c10b4021b40c19031040018041400b217842d031000d8803554100c0808140d1407507005040192040d0380703100c001a070001440c00124103100d90030b03a03011503000d00281d5040304550300003001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 687960890 1250 687959640 687959651
    0x50613060204051203090108100b180625110d020d03031e020a120b09090c01080c070501090c080712081c060503010612110d0b0112030908071203031b0f031e 69
    0xa48130044090020341c00309a071220840d80710820720250104a9000e1020707048070400131b800c866042c9013040540b4080160419003402c1485200d03800c00e0145010204d0280c0d04a8443d804110403d250011080004c580c0c00c142840681c0106442d071004140081c2410758481040c009030884252910b0588040355040d952445404401861149400980c00405003803025031040c6107003181600788501e0040005055000130070004590724100504207081641c03041011802054083c002d41607903034024045000c01c5132070b05103001d20f01040d642c0a1401c91410400160004540c03000f00e50018068019240840917092000b40062100394045507040d8a08030000a420283c4e14218000364000c113004111301083c00d0a0002480e03100c900281507028000043c0700014840380c000b00e0b0140207107042542244c4030200c0c9031601c1000c4c1c11a10803014405206020180d050090f101e05024003480010a510084030162900c004049024103154855400d03102140300310141d1020803441c0d4006220 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 687962140 1250 687960890 687960919
    0x618072006010906081504080a0c02010e0423070201230c091e0a0b093006040f0b0a3e040b0a02070501050a090320030f1b0d05061306020405 62
    0x203007445c0c481c099081c000c01c0280755141c6a80300e403492240b600500040d142c0000d42404403079144216000301c0c10301c070009500041d152500d2140510481c0ca041c83c000400c40c0300e11302c004411000520b140110385c102034004039202c90050103010f1607030080e410801c90391514860324551f402a9244507401002b0b00f00c421304007401c88000700c82c00c014207803540c550741526000c24115900c100703071066400aa154403030f04c243c0580001402c0c1d440c00f01c085003490300d0510b10421803d0010544054a100c05034050200c20b02a030041c04030f4100c2121f441c200448641c00200741101c1071881000540c80c2021071500340c81c8034520540c40100101d4001d19036031140c44903100b45c05608503403504001449a00c10200700c6500078000c40d281d6891340c2d102c24662915640e0341c0c581007400d548880e0000031100010108903202000711050960004000d04690030fa55000c02010600121403184503824246100700030a02c0802d4490700b10140d200c40c011242d909041041c06403080307500040d00140101c90001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 687963390 1250 687962140 687962159
    0x120203100302040b0a05090c131502060f0a060311040b1504030605150a0807090b0103020d0c0c060e0d091a22030501061a040b13080303010b040e061807200601 70
    0x14241c0348200c034100910441c00051108003030142c025a5004140c0402140c0340b13800d000c014154800303c07942c66100f440c1d00c030185246130100610350007001d64402c0040c040304004c00e82c0f50580c0880750901c10451a8515101e07a0500510740c460300380541c1d903c5030342580e40c0e2900d6122229a00300482c1c01035940e0750300e1a0803401800101d41001c0140140e48443c0392a03e2720428040489624100425550b03091a070800024440000301c281459400c001d41103440005008100300784030f80c1d40790007404e10a5070a01e90103496002c1c50a40301c981102c43e152840680015400055468050400001840800f0a04460b2149994000380041c8080302c485001c1518980752094034070079402400348951300d101c0c3d80c02003401e40180c2110200e0511051009007400c101628404024481042c0c0480e500c201280c00c0d03600030380001d6100300340010107115102d15100e04070340240c0e060720b54100000d903540017120b8943d0b02903c250200103036000c160000c4080e4400002a61141c101a078855503035078500304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 687964640 1250 687963390 687963421
    0x9030a020909030a1b020102030304020915040f051603090803190f0501030b0619031a090115090614150d09020a08010507030213080a020d2306040f03020733120203 72
    0x5800307080c0440c0c1000017803400ea10700c2039040c0c00860468585500300070042d6030007004c520085159002400481d6541e0165085d142c202c1d9070009030500702040500741c600c40d00d44810341030500f00f0900100050b000001c90354495070110508007028480034040d0041c2512410941d404e45c2080c00100512403070203507440c0205421241550318001802103054800c0c0c580c40040c3c80448000002c8103058000e05e00301c2e5011f0004000081d40e4002d03188034030440720807500714082c0207565403000d0007040084c4a15181e1203808462140080300c0c128144c0005100d4032824200c0300f030320b40c549035007107458204440000d040060000e1100d45032450009000303410100c140d2005464444002640f1390000c81e40c1c52440e50007804e02d40c900181510b8844003045482c0e04100080000c5441c04690131090105a02031407282044d140400b01c1c80c10003d1811810740c104c250100b80881c542580c401c3c03840080450b83c0c507040f03d01d03020119030000c00c1e0759802d5004400810781e400041000b85402800341007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 687965890 1250 687964640 687964657
    0x5030708011b11100c03021603020d020c031513111008040c0509450304050306010f0509070c05190f020a150c03120e1507020c1905010509030a02090903 67
    0xb03584000012100b19848003003501d041c0790360f4003d40c1e000400356000b60018465600c1c10f00780585080041c110004003084102c6d800c0d00160489140d00a80d01d6040c0071000c401c0200b01d0041c5081c444118490111a1025004c60f1003950041c950908010504211106404004208030a43d41c0c40020280041d5011a000c1f20150750389400801c440c030f006e403116400745203041410505502d042000520000c5031009060400110031400e6220360820b91040d20300c1e022800145403a145007400b072624201040c0c01030043d0301078100041c00581c984030410381d800849803410440012250034243d05103464500800d0030070035052061400d0203507403000d1612251003a41c4968240d40c3c0d0322101d0501d280421084e00020380e101d5036190210340f08003c41c103a02d01d103d200000324501c0380850300f4030305900d40388842e1b070001002d401c1108258042c000c1c001040c2c829142e50340348040792a61200b18400600507030b410300070003181803d02da403410050b00a4480d4040c003010440d007086c14503941d903504804034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 687967140 1250 687965890 687965921
    0x8060307290c150105010912020d030c20011704050c090a090606121406070503181005010e1e0403020307120e04110c070b0702090f0402121005060117100b130503070801 74
    0x1e030f55114521003000c0b41c00c2e11310451444289640ac2080c10211500160304000103c0c4940f4081440320380300d0441d401038440c0c0300b940d404110002410040854075810114a403503400c1202103403011802140c01001250325240a640b0102d00c10000c000e0b00c00054221840e049000c00e000468180d000110360080402e01d03118000d500e8240c0e59280700721580c000080007840400c3c02d440200c503074a2080e8400c80152128001400202e01c100d40d004d0340624241d0660205002c0b402e030342540314003102e6004141c050000e20703060f2030182d602d100e480c80c024102402c90340e540604a21910340ca00d404074004106101001c042220500560400c6c80004102d0280c01b2000840a120100b182d400c3c03540941060307603c0d904c1124460314070070b0042c01682c00c21100191035241e102d061003440303018054841c0c00030346c908000d0001016645c0329005034a00c0501d6805001e10701603260650011a005003144c541c1d101d24070550a0b01360340d12035200d00d4052003000030110342e4036019086180140c1c041d44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 687968390 1250 687967140 687967183
    0x3020a110405090d05030702240a0b060307140315220f0b030a0204020c01021909210201020a0615080712060c1e03090606030b0c0a03060608060307290c 67
    0x1007008221402528400202c2c1d2001a500403418080c001560f0b0011450060302c0700c3c3c180c4100d0700c01404101c8586001c1000c1150204104128a8842c0018a00d016943d081c11850140e4015010380500480309054600110000f884031042d000011348034500070788464180c0451415500190500a007481040f50800f01d069080d010507100e100348266005005110803006038081c0700096100038401d14680d5000c0244889000c07148801c280c1c1030000c5d503200000c0b28074016402105215024030301c5811225030500740302603a800603803a9251a00030300300080740054400104040b8215a0010003940240c0100003a42484a07900da40403e0050b0000e2004000c0c4900440345070707804501c0d041000b080f88041c440081d1090f0300c80e0885e03070f101e480c0000b020394607501c80044a0904960320810350a00007500c01c40c1682c5405080014090750400e036400d4248040001c0e280c10050180014001a000b29007030400b84400680c250300200c00101c0d42d0398003402e02c055480b02c0105414030344030410607 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 687969640 1250 687968390 687968423
    0x1909030e1002011b0809340e010f0905090c0310090302010b030f031c0b0301050a021b0a150e0102120c040617041502180a0e091612020d02010c0f03020a 67
    0x103000d2004c03440c40c0400300713460340b085460701654a10700c0070707000c07610324400c50400c01d04c03e0004405000b000c555181c0101114944058a8102481e5a80245c03100007001001004051421854ac0c2d0030f450010070007290b2035852809281c030b4041c41c8800c040d418400d43c0039849404203581e00680e0341038002d500030302ca42c0c002201419a00c520510100210354000c0000c00816282c0940031502c03c0e40400020030070340c5a6400007030035030f6000d844d00c403400c503400109411146484000f10000039209405000d44803442c0d2615111340d403101902440e010b8940391600c0c80d01c00e080d8101c0d101409218100d003090708003103410060a401c00d0040e207000ca2503450141e00340180054140d031042d5844414844104410f10441f07020790010009001001d5001040c0011650741071849405014804440341c003d1034031039071003441c05200c0407550141401a200a2265501d00c800080f141038040e03449500c49180362004030303420700803841c020b054a1041d44c0f8810416a010071081e07042030058030840c940c800f00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 687970890 1250 687969640 687969643
    0xf020310080a050a032a03050d0615020615010504050306010315060b030f0601030c111c0305061507110d02060304060b01030609020913092a1a090108010e1909030e1002 74
    0xd0303002400d42c2c0e004000040001c6d20a601040190064460366500c4074051141032040600e00d600440c0410404074038040100903e110f00c40c000d01505405c81c13900001c00c64042d4035410042c4c0440d5407005156007030351850340a001210010301c0081c0c1240c05543e0f607810b201510b01c4100382c0038907135941400000104045c0c50f00c2a24010a0310700640c0095031034000044d401058450203640c240036504199412603502030007207070034561044508600040da560002011180f0080a05109103540c1d00d00940c0c58484006454095038000003559a04c4278520001c2e070824a1345c14000d60141c1d001003007204002a03a00301110280007a01e00307104264881e030145060340562051103030801412214125910b1032a00065113080c003581136031101d08549140a541200c180c40d4110348007802c0d100c10040c80d450014240f207548841e03080b490403c045000000c181c00c9040c4900c002c0105003502090744200c00d6450300352581481101002074007680d00c1c0281c030346000d040b22948122560011400120300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 687972140 1250 687970890 687970903
    0x1e0509031006150e0406050a0306090203060a06060f03020705030408010c0504091506050702190302040c180b040602072610060602061e0a021c0c0c0203060705040e01090e100f02031008 81
    0x40f00a43c955040308031242200d4442d191400107600c95103403500000d09031114404c00d00514060480468040864010300d0320b49507001e042c2c03071030261034030008000442d440613904008101310319015030b80c0c20480c14014918000d80d045009607505e490402c2c210ba0b50400c004104030352400a0070f0002d0915401c41c00903014207803250f100414800c00480c0010324042604107540705000e8550407002d0344a40118080304c01194608005c00d400007548444820740400e01001062000b160f10f00d098180207009485425622442900300c0845080340380035400b184c140414840904200c91002040c0c1d041e5002401c2c0314811040540213000c041104200d83c40c030700c121032400707603000e502c0661291030111000354480e40c25038100301c2c1d00480355020300142c0e0003500205295035aa0489040c61360040600700200a018101400401c00080062201340f41407941100c0f49004005916002103840c1c07414000ca04401c0b1804a18081c0194000b001a07400307140038400b400c8502c0122911458000d50320316 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 687973390 1250 687972140 687972149
    0xb010803121302060c0d23030112030305061c08181021060b040f210b0a1e0c171b07020402210c03011409041208071e0509031006 57
    0x114000081c0d07240c8070110500b01d403a2020b030081d468500300c2035846041c84c22020480300080d0540c140b1121003003805845601c0078001e038601c0c900e076501d00307000fa500c4c0c0c0c8075910703000b014952030b040081d929075290b01c002854040d08208030102d018440c0b8045810b98040c0c2003401000c28a43c0d801c41460a11541c0d0320407e0150703403542568851030300401e15624041014980c4080e44450010030300e409600e01500040040c6c1641c801410f00300041500c95201e000301c080e00760081000c002c0c010500010f901500301003207980000b0b04081104152040c00c03000f102c62021241010318100c840d69100140b501c10103004401c04005e43c4032591040f8400b1468601c0000d03c00c4c0510075480545099070082210b05000c031003240340400c45402c41c515040044408070036102c0080010040e41081c03108440c459807003124552143d15055640304071940c074014000303041220610028502c14080c048403c0044003881122071070007403944005003260b001c1820603019000e900804881c01501d07009210980307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 687974640 1250 687973390 687973417
    0xc060709051c150603080405090906060619030b12060906060f030a060213030f0f030207060903080a050309010902060c0d1e0e060c07121515030209012706120b010803 73
    0x59061000764600c0c071803101010f03104415840707600b19080e1000d110b5038000f5489407140301c0c1c65900d0720342040756115000301491300c00c4e0001b50400c40d8599440c0704882403003a0105d103043c2124100c1c00d0884c0105000c10b00d070390704071800801c0c44012010004009110b054124103c5015a44084c10b0001401d198101e10746c26600492030000000c0e03054000c2e1004d42d4181c88008580c96480d1101c50410242c4042607442c41c1c5916140c006140d410f008002c0600400d00b03203020910b165a884800520071041c2610030400b01001080c6480002c6d0810612540c00402103501c8800300152591617249000b0703004049803400b22121003103101c02c00c4d802c480800c103072240181107808505000702d035400062450414060383c04081060180c84084d44c0c4194010565084100d02c01140030301180c000040010001600c1307003041005070b0303d0301103030707070641c0e010309200d600f44400d03894003080504100100481c01c03802c0a40105081c0301e88480d01e84010300402c81c0c0f10075644e9603e08540c482c0700c0d1542031540b0b03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 687975890 1250 687974640 687974659
    0x60f050d0f1a0d032c030703030c0c0e01122d050c01020f1209041d1b0f0609030d050d020412050d020c0105070b0f1008030c011d010c02060406090c030203120c06070905 74
    0x650030b885c04c3e0304554182d6940950f0b000b289000906180007038000700d02292a030000f00e0184050813440c0409001ca101c0d000070594141911150b4410302c80e040108a0484205076280072507031300d0004860301c100c0009100c000b450501e0030b107880d409007284c0b460041c400d45c0c801036501d4071300103981e0520a286590052800389840103000150818038460b24003402d6400d0745224440c000c01c107961307843d041010040500c0f0f0301c00040141c007062080748140b04000c1404201010794007c26180b09604003810070503910011203641e50080d000c0e9511440748013004010311418441d01241c2c11000c00314a50030f84210b841c0100040d034ad1401600c00161424107840e001554040d40080c03815000340e01c10b2002070f40555070350082491075011030701100f81a5118500070000c2c040c002644980507070840d00a1000d000344c2030009540d644000c001901e00d548072a08a0306001ca80e044840146030003070190350709580e001d01d0f0300c0c1d160361010180503150300c0703a00300203035071144038a1200d000c1d240001c2c00c0110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 687977140 1250 687975890 687975917
    0x140a090c141807031a010905130e1f060504050a0203100905060103090618050c030706140904141e01050d031d0117011409011707060f050d0f1a0d03 65
    0x44680c01020000c0d0010391003141c20b0756802214424512031006654041303903003100d0180c4074110346940d444241c1403000e2860f00740081c1c0e4556580490641802d0400145110544070051501c281c00422800c100d03c01942101d270032806420550541c1c805076400c4c404d0352140c0801804910084482c003101050400c002d00850016400440c0c2281f03051501003800c070003949441c0304403070030200085124200d80c0742c28800c0280070f1101c4c81440c01d04501a001003440c0c82000391126095500e02c0d1542e00c00010149540c0d641c42c1d00100044a00001c010820300c1c10010b07064811040b0036030709c0074000d181c0000103507526040f43c1c02c06010354103a44104001d0103054450540011541c0108e041c49211200703070000b8005502414002d142c0e4561601841c02583c040c45851751040e080f0326038031201800001088580001c0c0d01d0200d80661500d07d00100c241482102d0b5800742d01c8005582038100024211201196000100c4802c1030f509070200c40300c00d11041044201c43c0e44402404104046840c81 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 687978390 1250 687977140 687977159
    0x90c09150912110402030f010302030613020108011505040b0d050601120b10050901031409100f0e2e110a030b0f10120b03060903031503061504050c040803030901140a090c 75
    0x504580b082c290940c4182c1803e0000e07083c3e80084404812005140c001001585410840b082e0050b0300f0481c84800d5094540000300f80041c14080ea04c21002c1c441e136000c1ca110302c01c6040307800400040440700d44075816107440c40c02a06003510a5800a9528000082c011080e8860404411802440e0346600c00c10100c05444035080364080905040d541c5000c1c052441100c00a60302c1180c041c0050005600130b62014000c075030510440602c00361174030640e44030340040050046c0f030400032141e604011940131400d28000342c0500050139212414950585000c0c0f41c403101818902c1044d84040c1300c9142e80000740034024694400301c5511502c50131040402c280076000c0740c1000c542140d008200e412428010916101d000d07520080d06900010800440c1041c484010340c000fa02100070740102d08141c0c00c00d42c0c7d01f2850840a80c4155942d0020804d81140c1c241100c00504240c01a0707612071402c0c0c100c0d58020700600f11842c3c244c2040200146040307103544990111154003004a4a00e5030030300d030492 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 687979640 1250 687978390 687978419
    0x20d1a0711071e051c03140c0a11030c031006061b120c020102010204080312040209010509010e040803070c0c0e09010509160308130306050c190306030b040b1f090c091509 75
    0x11848480c0e90b00401c00e500c0e550036041d02d81c03481741644035000c611494028048030200d0310044908500703000d003006ca00c00c0070a21150880c2c00014292052204000090034015224800c44e49441414100042440319030000d100705d82c496110704506407211082e0b03101004540b507000b0084080000b02d01c0340075004040281c0114010701c0010308103034490000c0c51031a40100e68480c4006070183c100000c61624a04440c0542402c1e1040e01e6954034110302d90b00c18840241c002460f404020000071a003d104483c402c03100fa4002c0959500140d0f102c00c81100c100c0d05441811003542001c002800010000a507008030803a000f40c010a40303465500c0c0c0c0d0703a498015059010022040b101c00202007083d50244a0013400c5043c4041c0d92102c50503400100c8800351100407003814240001000820354030b040c1294046d80003582c40031246e490020702079004a0703a680b4201e00c031040101c00b103500d0780705070700041e1290f05603183c450405884180895403d0300d410000c0000403006d509c01d118114101c1d480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 687980890 1250 687979640 687979679
    0x1140f0708010b07210e30010b0a0b0a11030d0207030807020106060f0c0606030b070305061801080705130914010e0c040e0a0303150b0304030309172d07020d1a071107 73
    0x20140c007801d00c800034000719021f010f00c0c0d4012020800710300d000755001c032591849a9030080200800715020000ca80580c509224140c20750001003616801c05010713203c24801e405130303481566946e140e556515402500102c0e0140c0c0092940c90005188074014403489095134600e0300c45070819031603240e0440d840415040115240c9445070310010006566440c06070003840d040e1000f140d203142403424440380c002000c5640c1c168481140040240d10b401144017000e9403000c0c0c481003d0848085038100142c6040180140b041c1401c0341956070400040d84035100c2540180c0980d0425103610742044252080c08504032010b41101c14146e0029000f070b07111243c002d00c001070100d0001d695170343c000c86c1904200c4060b00480d458490300010402007100820300a50741d806050b0800c50100c800c0591074011504084080880100303203d25004000262403505034000d0000c0000c03206440e015203120100d41c0340c020110801c01c081f42c60103000d184403445030500e50006121462038402d1840b4802c6240380c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 687982140 1250 687980890 687980897
    0x70506030703020d053108030f07030e03030a05010e060d020f0d0c050a061101050f0c0702190b0f0705060a06061d041806020a02211b01140f0708010b0721 68
    0x5007140c800c40c130703000c1c1ca807081c905000c604004580c2c0881844030314020001e102c0300c4000300900c0ea0001108502565008042c0034074440036130740c802c4010b60041c12400540900da11010042041e40314a582040d4141e900c61410820280c072103100784017880b515503800a40c801200000301409050110f854114a130242c681154807964660209111501036004080000c00d00103d031051001c007409031940181e0390b001d000e680e624000503800c0050040300c20091160351100440170345c100000050360301420441990541e038a140b40004d1183e50f01999046400b402080b00080c5803941a01c954801c88105440c0c004030401401502c10020030381e55001584036960307500d0011050030f01080401c849210344e500603a1244005000b80c64465140c0f1050400d43c40494101c5110900070260340021800c0d2094401c00415507202034050110b140ca180300c1c2c2410001004281824172500c980070b0b200549a0602690b00d958440985104007100a884444c4c18072640c103415640d0700d0721081070750b210315 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 687983390 1250 687982140 687982147
    0x715050a032f07052803081807060507021c030c081605030d14090105061c06063b0f0103120c062f04030c090209032b030b0d020307050603070302 64
    0x5860b604960891404a1140a03011545a0800804000d03420020760a1111300955440e520106200406a80001001c11075810040382c1000400300f000e515400540095819079511114010030a80101d0000c2e8401c020300b400368001046035400d60a0900e8156030750b2441d40301b1039280d40c181644403014000018440c07901c1100030a00600140200c0100840040b50750306416403601c98504002d800030140343d01d0081440501c3d42c600030a503482444100e01c0501c034030041d080800041c000b6a0002d24150390100307d6040e0015251341000400c100c031200440d204c0d0404c0400d40e9000d004440b59208030486a006001003586107d501b9100181031a0007659004c0b55580c40703040c5c4202121030b096160340c48500c072003009080b483c2c4843c3c1d0204580381c00d0510b80b80d034880c07090b02ca11b288205002c00d6400210680700d03842c14041c8050b0079180200c019048008100b900c3d00345d240c0e414800700040c0c500070b1301d034945203044070002c008140c000340200580d5003010300b00130301584007a104401b40b50303082 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 687984640 1250 687983390 687983441
    0x15030c1e071208060109080f0a02280b1e0a080103020d020a052101110c0a15060b030f01031203021801030b03031b010e150601050a082d090715050a03 66
    0x21410080b50390030030340e1140c19a00742034001501c3c44206810092580c0c001d00c201c12000703000050741025850301110700015038100814085505083c210013000d010200f4000880c02040000042c0781242c040124031591418038a80d40c4401d000c5c10009800240180700100054034201503100d4881d4002040c20481b260b8580010b01c040074005403032200e40e00c4600404858040a106515003410082c031514604140741521300e40741c01c02140c000b4a10048032001120303100726503100310003801502018558038108800d42040217102480304031394406814403c0740c4460300c41c2c0290b61202d480e15504000801c80b080040d006031050380c2c2c030783d42c05100c00d11403091141d65481968142c0003031000000761f099241134035079007000369000c90303400911001414404d070b40c1d038040e0480729001032500d800c01e81600c4000c085210780e1402d03004d501c80c000c00d03041d0001050042d00b01540c0500d00120486c0c44280e0f58009080c1403c000031034040208000f80269607542e402070304091803043c0c50003001c03401203007403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 687985890 1250 687984640 687984653
    0x503040b04090c0e030d02030a03050903040312020312060d02060301091e02040902040e010f0f03020d1401110d1a011d0d0c15080c0903030324030d020c15030c1e07 72
    0xd0ba200c010721585a115036080c4070703041412410115400da015011101401901035564800d0310141020195100009800c803041481501d02450380209403804070a41500001e6076900203003694600b00d00c43d0000301d10f01e0320300820042181079010300001c2c1541e1070028420700504081c844100c60407a1a210800d104003188000c00241c02c074642c00684907428903026203031404050b00210032580c01164103004210307450303044404403075045070203111106071464401c100c1031082c402e5200541c00d04902d90000700070140034280000706100208a00c541c040005c9020a191a0740d150110b0951806003200740321840c05900c41e824040d10f20070281c00d040c1e458210440030b80e802140c121901044510320a40d0195031181c101c900855818204480c0302d001948034880501280d00602c004c5c8a2000d4034500c0742c00c5881c43c1c0f00f00030290382103509082c0c00039495421200f1500e1058a507580d911a1060120702070302d01680c003945056040a01c0c060011456566011003012018002d00006000584 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 687987140 1250 687985890 687985897
    0xd271401110609060106030f0b030c061312030305010504050903180f041806020301090b010908101a0d06062412090320010c030b0d110d0804080a060207171201030f0503040b 76
    0x904018113080d03140074402030498481394542507600741071940200e4281c2d00040c0e10550141c0031070342c150340c80c005220542a01c1300b003a4807203018050030784400424160558080c80c1200c40644091049039502c0c45016103920030000b506d94800c01881c1d1030802c509080c5220031200d0700203040000c03c500d072841003498400e1300d1001100c1c0250000014064100e0754050001c29481c2802c080d602103040c00d03d80e503110440c44a0240b6034655484440507120401604605403120241010b4501c0800703003001400360440380500c0f21003002003442c88049040c0d510000700401c00907924045001c0b00340003424050000c2842c181e04000c0001800c01c040b071418040c0300c00340e210ba100005809101088040d00b550f440c180101d2140c44100411404901500e185e0b620600c01200c0754030458100f0315041003240695000004c00340300d0101d82d81d08114640c1e0091801c40c4c00ba12000d06030040c40f800c900e410b4461041c050040c00722540041002a814114410b00035110340141c8e0f0405454074080c00d40340c4c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 687988390 1250 687987140 687987151
    0x905043c060b0a080a17180603180c0f060d202d030f0403051c0222230d08070f11010e010201060f140a0312020d2714011106 55
    0x203642d4864001e0510344503000d02d00624018010700740c915400c0e2900b003e01c521181141160b02d80005e002d040350022500031095401000f44251780300c1c1002200c0b29074500500300000ca01e0300c14008080b4541c60b100d088407402401c0202118600102c091110024204203802072950305803c0281015402d40d00018024045040e5030001c4104000d000c0d190404940f40f100c649035100070003c1c0603003641844501640603403d4100684d483c001a900b01c3c40d0302042c00119440d061010640c00700031100a100030600b4415000008295602d40e0300c0340c81028003c0079191410081d10208200604002a6a0038030b6070245804034140502c90300e40b103080203035600742205c0400001030035070b042d981c00050340b00e80402c082c40200002404d041c20108400306500404441d4000d07801460050356030380702040090f541c4010b00078460207800c04040d54030f201c54070040011031413040401d80302d40c0c6401d0740d80030094002040c0d000f0036890040801540380c0e5400304141008410010700380340001c200038403405403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 687989640 1250 687988390 687988403
    0x70e0d0b070e03062802070f0b01030804080d0302041217070606080c090f040c030b0612070b090405250f0c02100915020c03120a23130905043c 63
    0x2080100700b01400d03d48020003030031000074044075035161417402c074013003203000d510758000169140c8540c10091880c0040100c001c1c440886c0a0001c001c0000c964068403c0f520740c0400c641c1c40b81070001055003640154003030000040340000d5017501040c6580c03100c4c00440e011900700b83c50800300303880d06401e5980c02d4010f515690f000158101860400d8000e99601c0061240095024181039a0300741c8941c107248001791203946c400c004600e0750703510300d040b0b5440c001220080320f4216a80d011442200c0d000000c48612991400000030455860084400044011a0117600e4042d00c285070a50780c9441d00c0d6044070404c03100d41000c100584501c3d400c0011000141c4400345042d151120500c494141d40c600c060864201c040c15416a45001404001e990b0a0000c89a00c8130302031002100c045005684502c00000d289031400268414203009007035000e03440d0742d43c141d0b0640b52140c440a0b00c900360b0b401000201d0244e0412005a1000d2588414400d0809500000d0510100303040c0c04108804055940 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 687990890 1250 687989640 687989657
    0x6061e04091a0103140a1a031f05010503060c03010603050c160b040c09200705010209030618150f070c060b04020c0706030e060106080601050c033a0e06070e0d0b07 72
    0x102c038440301d0444400c07602440d052091074002e01c2104036051001d000310000c0350f103540034a641e0318030040f41c0300c00d41e80002e02212500c80e0051000e0306101d0b40c41b034541e0200c0746007200200e910300b07020602d144102e140a00300351850b441c08034224020700005200a48102052200392420480300e0f104840003030041b1002a180e0134903081110050010342e00c40002c0c50300e00b814030b4241c52880440103101c00c07140d44080b9180c100c2401c025019100c1c0c2128164180103030710421000c8901c001102107004100c104480e4202d0030000c9062071040203407000d140c036001ca0000562070382d2145800c0142c140c842c010215032086103d010500b0b9070000900c6407110313000035400703016141d4944190380542001100030f002651502001500940028100b117040003c00142082c1203842002103552115071040c07002c0d0000800a407030b4607880c0c801c440e240c5c6210b040902010284000d402000d0b0b000400401415054403050815600f214508091a03002045084164042241c40319014464107050301d42044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 687992140 1250 687990890 687990911
    0x403080d0c0315140a0509041217101502030c070b04090c0c0b040303180803040b0601031103061f020106081606020c090403050d0b0406030602070f0c0807080606061e0409 75
    0xc0e52031140d000401c02d454105001c0c818040446034000b10f844e4500110307032036030920010842400c210380001f0340180d5a00203100812014a103000c02a0480380d40310318111a80c002014440001503810408000380340d4000c0c40311150140036451492410700481389800e4102807181d00703000f9070b98003c80080c0008502004207510320b00a201d0703424150724009264a525941d1a100303039a0243c005420556580000d0030305c0700030403104000d1180c001c0e06864480c50035141602ca2207404951302030000b410550281c20541c556000c2e40e001d20b000404c0704041c0752009048002038410181a04110742d241c540005101205000e03400e070f0500d18115040ca10750419401038600000d101100e4001c2050104110110754400305980300f1224080d004148012105d000801822041d0006410b0034400161241040204100c45141c0c44c13140000f50a00d55803a0041a00c50220f4440c070800c58001100054061802800400612180070341400200640f02d54080c103941098009150841c1d440800340c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 687993390 1250 687992140 687992167
    0x1c0302011b0203041a0919090204080c0603060f011d0a03030305060f012d200c0109090e030f030a0905010c0c051005060609040c030615051b010e03070f060b0303040308 74
    0x580100e03540003c61501d803130102d4409803c003134203c109000c19004035200b44590741b040d80c40f1681a800f100030300700c1075866825400082d441849400c0a612504003809003908014080d20310540c03000b0503620300c5480d11001520384987c41443c9060071011410007054959401c02e40d40041c501a603030005040c078050f0b051000c1c520102030318034184042042c180668809540d0a15411190010203c82c08041003d0654103440840201c5000e9124584050000311300084c901c0d00c003c00c01d036600315205964031407800071204045400c00980d0420006c41c4961a42c2000075502300c0d060310000146000680c441a084558654058000510701040741d41401010010f14100f810b0345e900c01c0020342000d07000990544180f81049014548a050a52030390703009921400003001408601610789801040080c0107900c40c82c4a0244262281002041c0000511400d0441c1140300000c0d4603080658841c09902040c408044403150f8030380d0078000168a040c0050300c02144a8000c2980303490358040e060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 687994640 1250 687993390 687993431
    0x30905090606030103140f0d0302181207090c050c0604050705010f0323071106010f090e0105060607020d080f040803030f090c09070f11120d2403060b1c030201 70
    0x10321800e51042444002c1e9200d400b02e90469a1020f005800c2084600c0032038100042001ca161540c059280c40c41030960701f41d001065a0030400e40104c40d144140c00c108180c12511001e001c081e54040b08050080035940d0f1300c000c002c643d25040c61410011121740f9580341110480b0111402e030420601000b141d43c11280b44034041c621803c090180004640004042c040110400700e0044003000100703c0c0d40e4060390400341d82c0360101080d208990386038030f0f98885200315071046280c2e5618000d1a42c00001061041c50b00400008104c18604401e50b02040446084580d080d03c3c442c0c2c0821250300305546480090009108401c0a19103914104a001c070b030062000701a40d90030340024444e01c08558a42c2a4154880e843e17003030403442c12171141421180307040c650000b5081841040108106031040c103000d0040e00095820038001d100100c44c189940a00d60b405061203c4840c1c1014400a89541c000071903c1c02d01400d094070340b2a00245010b028084080c0680150350b545607180209a100c0e5680d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 687995890 1250 687994640 687994649
    0x1e0a02030706092a0e0708180102190806010c0503120402060c030d09111e01121b020307150204050306041502070807110415080a0f0f05070b030a0501120c09051018090309 75
    0x242c01c130b11464407200f100c41050003410a810003880c2000104130681803c1c0703028481400100071503c0310003d00c04140d01075251400040400d6516000640341c0d07110b440b120b07800700da024000d503040441d045111040c140020b030040380e005000b4400380448240403c0585011048600c002c1207003951424015440800b10a0140c0238040701711040c08205203020a1045240082c41c081c81c692081084185c0105146178200f8900c044013610f0041782c3d40e0000141948a0250850743c0007240001824000c0b440b59120301c5405030400400140402d00c142041e0611445042c0003600d4101d60341c0e1808080d5100401c203c3d450701c0b420965840c681031600c60080c2080145c1e40401380e083c1030000d4540c1c5c50f40a44e0b03004100100d80c5199404104050403246003543c2d0000844044646518680400d500103d40103442e6616210000500100030391010752080d030810025807100e401c002030380300606001040101020811080040c208040b0342c03a00845070010840010344844508c3d00900c6100749602 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 687997140 1250 687995890 687995963
    0x20c070f050d080702100e1201060303030f091109180706030c030c08061e0a150203090907030b0d02151209010b0102070806101e0e090309040c051e0a0203070609 71
    0x2000001400082201c0400740c04446c02d6901c8114510100c81e1000c10000b0a504080500380079643d02805420120680344680c4051104226100e0300070201c45c0307554800350089082e420407510740d081c41d940d080d80040b04414a103842615030310b039403480e08401e580200006540e803010f44640c141e051041c5a5848507500d800c1d2060b044c40000582c4003413401e11945e10f62808080e030080c081d681c8404420003014400c2c1213001c2600b0b5020041e440ba0080c00403207005002131000602032602c40e1103484c9204030010a01c686d20310480d0248001403d08032903c0304003801c100a00c10303850a05000e450310501c414030010074460085000241001c60b41d6000c903030300790300500c1031014100c84485503606450003e00b41c0c20741403000b650070300408c0c2056848004110092030922101c41c00120040083e0b440a50342400920071000c1d080301c651044805400c0124070350b40201c0074210a010040088007031a104803804e10119403689030846a20801c202e0302e8500400c00140c18950408044242240807507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 687998390 1250 687997140 687997159
    0xf110a0507140a080a06150812030705030c040e150111030a02060a02070309180b030613031d041e0e0d050301031e02011407081305100f030b0d0204020c070f05 70
    0x50340d40e640c0c0d8010740607150003640d14044081c01c540f2a060940010b084440c11100703007050509011005288001048450024101020420780700c0062406400c000c0b00520314603556a44c203003295940c1001c1d0031552200d03420070001030003159003914140a10490300166030714141200000d801214484034041d099001171080e066596004241694050b09580c4050b994080394075046a0303450782c641207540c444455070050140c030340042d400055900e005508450194036403c000a0440d40c0a000050016802c0f40d076888440d0f030b403084070084910000c0c00100f04c07050805215034100410543d58403a040e034411120039405c0b4200003c014400b814244079103594119151421500c1801d40d00405007050800b100085900c0341c1000800f16036900324003515011149401e04040d80102041c2c503155207d44c5000c03465217088901c0110f040855111aa450584820140d000d0310040103840e51180710500c0748000741c0c9660008250740506180603205603414007608007040e5000e900554045d00040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 687999640 1250 687998390 687998393
    0xf0507141b09010f030b04020a09020f0d0606050405091302121b130903050f03070504091803020d17190908130f08030c060a020904150b0d0b22090206070c060f110a 72
    0x4c00c011004e0300c0d00b0807003121301e030380d43c6d400400d41c407200c1940002e80140c4001510115000c441024160380101101c00740f05c842d9550200b00d07007500981c0141d03035005600c140400c4201c00c40301c400c24592480603004110143c02030f010a42041c04800d500c2d810f440501ca4400001c0c40c0c41e06240c0c07081d180d031100400004c00c20713450041c0140a4864422400d503000030109600b2800791080d00c00815a468080c400201c1c01103d00f504035225580817805441109803a102c00b90049104861620604a0400b134a41d50715071158481550711084080c1a5a210b1603000401d1401300100011028a41c0c1a111f40d071400b615424084002e50101095030000e0148080c02040030441640007084035501580341c001c008001402410700e4580b240c0c207030f0034016000034901410b40141c03d80800e03442c2d0810840201c007050241144440118203141061541c9030400180300b54072441c20240054561400c0007103d555030701401c05203410900110350f02119500703020303a1206500280b000060042d0141003406e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 688000890 1250 687999640 687999659
    0x20f0d0e15130b07140a3c06020f040902040b03090606101b032d02010b010906090509151804120c0203030a0e1c0309080d0314070f0507141b0901 64
    0xd000300f407000f120009982d42841605c400101c17036035040c24292425906145421503581420049240c0c031004105424070714510b0401c1880f00d000c005001142e604100d41d9503001c0250703c16076181c1d0b030750710061201240c3c1194620291002d032021807940d80d581d04201e0142c40c80c103100204824450302c44a000b405405600860706040d680961001c10340440c414034060ba80d14020f81c0311001025014406030b256600d008007021031b9100550000c0000c0705001004450a401c6401042c01068404108100a0038002d00403035110703102c0014034080e600007200007500d20b221140c4030040c00c0d02c01002d01043c03001000b0782441c024103500300041440d04076400301c1e807280120103891050007140d4201d079110340c50b080c0840c51305085280c40c03014241034603d40544148058050360b40d0600c01d90600040340c0c1d00a104140c4200480600d11940d0f40d6000011205010055440700811100b885404001400d09000100500300240030300f039103084c42642c203582980c02042c000e1061807070710010000c1c40700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 688002140 1250 688000890 688000927
    0x281505150f0a030b0402070204020a03020d0e121b0c190305010b0f090604020a02010e0f0102070c08070f03080a02071d01290a0e040e0a110310020304080409050601020f0d0e15 77
    0x508001c00ca042044c40024001c0c007454402940150000139207240c9160b2540c020b1044401c0d50204101ca403042d620a60b5880e40b0901c40e03401100d10800038040c0c1c0d14501215035079440c4c1060121003c0d020600d01280c081d204441d08080310403c003200070300c2000004e02801c00080c005071000c2c00c3c036044400000b4031006d000f1309003600460380086d10b542071510070740001a20000130340c2142e0780c4042c2d4260740c40c000c4d80544016201107095190100c0c4010000c0349642c1240d140c001408140360030741c1c030780e0822a440902018194440c150002400c90380036401c002c603011001c3c19880440d80740c00303440383c5400350115500041000280c00c10003281104003d481d0020000e1400c400c020001c080810014850b6040705086032180c12000c00810103c8a41c170460000c0a4040c2d4040385281080030090b07000547e4005c0248505000074004814190300050703002605104903407160080b42001801c4c4808034502d03200140b141412501117003004440300b0761615001c100e4a103005105c006582e2482c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 688003390 1250 688002140 688002157
    0x618030807050c04050f091002030c0a0e180403050307081302011d0301090f110f03061306090c09020a030506031c120513330c0206281505150f 63
    0x4604201801000c00082d04400c03c082c00400150900080c4009000802c4410740036521410300c64804800031802540c0c002d000000c50641800c1c1e0340c0109407000440821082c2c0c04c0544c1d00304405040c5400303a0b40a0245002c1e41718243d480c11314030401014a14001e00c1e2621a0984d0303030700030b40140d903c0f17486041c2503403a000c0c0101c501030621000901400c84080050700702c50381c8100c4c1000f031010128100c13403608404c582d0b0441220042080c1515184221080b442c003030079001d1010003140983d081010180d20840c0c018800a440c5c1442108903000300b012140007a0b40e80b0108400703409d08000c0340060710801c92860074110a1002d0040840e2521042c2c010556150b20109800380c1805184244840c1e200922180350309040c01c050b030100a4081c039030021541e0f04030f01c1c10700020980c032030800c0c2e90101743d002c2c1405076100d2000c21104800a41956081180b55608900c0c141a501c1019041d00110642021081c60101000010300d2154000d001580d02049000700c0c6516017005c031390044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 688004640 1250 688003390 688003403
    0x5030d03110f0d02040905070e1e041e201e0c01110703020303040b01090501031101050c0a0501050a061409160c0606030609030503071d030606040209040f14060a061803 74
    0x1c120312600e0900340548003542000001c0070510420f80442900503005440040c1c038200321642d140f41c811103080f5080c20304682c00c00c042d0340014018110800d60100c1f100d20140c00401c81d400200c8000304844101e40348900b9a55271040030804000c2e00c00d00280030349030302d4504c90742070445040005a842241400030740800300e0002d21760541000a40003010202034120322640c07505c0b45410040d4481c2d0045608031440d042850020421480500c10641a25000390242658582c5680150340990095101003118070500c9125000284240102d6215200840700400c4075481c05520240305040681d00e24450181c5000b0050311288081005040071001e1900d15108502800d10500070b100c640c101401d1281080d00074820b140c0c00800840c01905150f445c10300300f042e440c0b122518401c20300f1032143d05812034000300300c503032030700350050800b00c1001840007402c3c11000404a0840d000352400305806820813003007002d5451301254a00080115041c0044c00c4005100050f079244450300004051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 688005890 1250 688004640 688004651
    0x306150e06100e151903060819112809180b040206040803032505120103060209060909010f03060b1801120f0b1906060f020a14010902030604030302190905030d03 71
    0x2491090192003100d9101a220107800d20404140280551050002405040680111740281071082c45480c0480c2c000c100603084280c02c120702601030300303070301002525440e018800141003961000d2000da216120400507914460004806008625144e07010242461400350211113114550140e101484d0b4413046401c8903039214400920f01b401b4980010589120100400002401480d4100c25026440c2080001da8049507011250be200302c0f861100d410048000400c0003c616402405001900400d00747c2403640000100d12540001d80c405014540c24903410402c1c0b04d071510802034121010741d038100d03100c1590030503c40040810320a80805683d09000780341444148210200025401020800f5174140000700b1000070b45061818895546800780000303c0c41d020b20f81940440d16290017902c4103416540310480542010320340c5142c955203840740c0400690307052102c94030661081d100181c80b2081c2003039441e150349040d1100c20a2000c1144107024a560002d030705941400c044c40c000c40d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 688007140 1250 688005890 688005919
    0x18050d110411160c030c0e0702100f021b07090b0607020d1707020607030305160504061d120a081b030f0f07030905031c26070c08041208040306150e06 66
    0x842e4030a208001d034104484620800c104090040201c0031607020300114002180c440d402d1452a01003a140003002d640b04100c1801d00c04001d4200d15540030301301c6001400c10320484505a0618000a031042a50700513403000d121042c8284200f5006900650724141400a59801710b113402111a00242c000f8582210507400e0a07603140445243d150b01500362900d850191501501804d0140e99042d002554240c2d00909180725100366001c580080e6924180d885d2540000c48810034096941c40d0001390340954140041800c1000c540c0892065441e10764840f4210341e400ca0008002c2c0f8940c146070000c206d420030240100c0e0031f2710b104142c10841d403036588180340782c00d42d145104c0f90300c0f154250051142c90180c108842842980060003a2218000712860841036503001d5080d035401c0a0348910100403500003403180b4034031b02c00148680700040c41d240e00c0340c84480030142007104c200c81c0080c00003020b20803c101805180560b001c0140ea4462050900d04001d80b8204010941400303007006490061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 688008390 1250 688007140 688007171
    0xc070b0a180c03050606041b0e061b15010b07020117180f0c0118030f11030f011410050d0507051c060e030a020c0111070920030718050d1104 62
    0x484406580705091501006203441e0741d00c52198441a181400b6500c001041030500c4e00030100001c100c1e00d102304243e03d0030003099800400d0412003503003180c4240581d82107900d116036544040158400280001151300b01d010502240c141c0250180030f0b01480b0160050342c00108400509181f4818004942d603090040010f0300c021118100c494400e00d058545800d8000c07480c030318805800c3ea03c1c1211030310a210652403042d45407000a00070342d01011000c1c049000140c2c2d41c5c0282400400b03039a840340101481c542541c400e4008000589041c100307105030510710703002010080005513400345c205406a102c464a48009110b81c50181f002d000014080e40d01c03107840b060345958041800c00015060150f41a500c5c0c1040c1e60010261103400401545903009404100350040403000410509007050100c2c2e001d040d4a111103495840000780e140c51905644020314824151a50b55032176445c0b9203c2850203040311031b4081030068200100000100303148483d94051442d041d900844c2c0320008130070f0f08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 688009640 1250 688008390 688008401
    0x16061b0807201b030106050604030b0c07020f0d0501060e010e070f110705040c030603140a050303071101140708060a1703090d0f0203030a110d0912060905010902120d080109050c070b0a 81
    0xa080d58059030002c0c00f01c14420010100c503070841603000b0801c0c00d4550083c00b02038407a80c080030780001805030014444001c0a8024030780103201a200d000c1c6807020300f001c50480c24843c103040303c00da5111031052020706514138800f4018034540c880c0c055242448600035101094800b131410400003400901044800104124002000058820402c141c1c080310024001c2807540402c4484604981c5c1e0f54081110003c3c80c1081560440d02071480d40d1283c000c1595500100310300102155244d0250b0303440414141d8030984290103d49400c04a454400100f04c018407990b0003a0250280c66102c5070b5001400000340c80c03a4020941e590855403c2c10304102d03004481100c07000750325201c0001c0206031954854000301c2541c40c51421501407000026007900c2c4200300d40500d81c2000ca400c100038000c40c0064000030455130094000140203089034001c00c070b40e403c003000d003400305070b101491360704483c2c2d2b01489460040001481c1040181030082e502c415500c6801e070060000550702e80400c210290b2030384070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 688010890 1250 688009640 688009697
    0x515040911100f031a030d050313080d02180406080601141513031a01050105031902160b1008010b060a0f2a020a06050a0806060d0b030316061b0807 65
    0x40203190142c0c0307038009180040403407554002900b0410700c00c801c408514284480070b0f00041c060020a48132460460b2150802024405101c04000301d1202051503d001080740c41d981d1700c00965200c00c221440d4000b034513244100350103603242403010803c0c0180443c1d00b074196141e07056001c403621080b00002d22070009600400110b03000008000aa15070303080500d404580c4a01281050890204450042a84c3c248156804a00c042000840c240c440d002107060075100c0d00c00040c180400900304181c0e80c2c081060131500800c080c1c041c0402000f8981c0088000c028000003841030900b000082016406524450004e000060900103e09402602c1940d400f580070022581c1025540d0840d1440c568001e4042e40902400b280200b0001e110340f040328180c6505456440b10f035150001801031681c4503100f0101c0c016030f20308008003103070343c2031004003040d08150304994843d00c11810308004451624040c844503118544551401e1a04080050350283c803c1c10548001c82002001d4609408503184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 688012140 1250 688010890 688010899
    0x901020a200f060310060f03020c0105130b150307180216050a0c0f1212140403061e05071407053d270f0c0e0f0a0515040911 55
    0x1140c44500700e01081084115208880d00003002c40307100203101c07243c441600c40504800d8804802d000940c01110070540d110924580186894603490384a4219102500d000710401c40050f160014003003840d11041c0c0050428000500d0340d1090b1001035560017007403040c8058802501005c644031041a03041d642c200b141003010042c0150a0300c0c040740c89503003107001191a1400c0d40d1001c5610410040c8200590380401084041805a5244c3d00510849002070f5410060798050700f020000c0d00030054002103200e0000400c0d284199900032b4032126022072004292407070501041081917001c1103140d1a814084501580c90803142040c1d8244105808a903040d406060f200da107001030400c90080c0c4241c07605400c002c0c40041c04124800380d035007021003004010504000680341307a6034018400d0240388150848500740040399155150301040b6407281d19888040310801004005850000740c1c000a1003a01300440d181c021805004160103400c0d041c0126540c245500412110f00d1840b00d60500081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 688013390 1250 688012140 688012163
    0x601080c010e0d080c0d0f1206030308011205250302010323040f0f02030a0b060918060123031c1101050408070f030c02130515011b06050601200d0801051807050901020a 74
    0x5032448640710000c2c0c0000b6443c2842c4523805445200d0302c0c0c1965815614020240d02c0d09107146900721074004252100e016900070070404409056000d02c4035030105034105500d501d903000141c11206190102c1c4144554030340e074540c911040c0301e00070b54455407010300e0046a0034035050030500340d20182e030002c1d01841208102414040e41d5110f903403049200311100c666540c0c5070105074604040c2c5242480300e030340c8002c0c0180460707074421501403850860720390380182615404000074a407841c242e103000424101c46407504040380d88200c44c0c402e003407140d00013403110f0b080a58400d030700b80c0f2406d100540b5a425154914040520502501400d00c2d0024007544516803500440c030f00070b00c010ba50310700c180805402407141b10350144507815004200f900013403000e14415260007014040c002c000c941002800b0006100c501e410f040581c2c00d13005008000c2000e4803d881000e0b01d1054180c00441c850074406014120f500244407210398054850310740b00380c4498203003006034070349648400010030098010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 688014640 1250 688013390 688013413
    0xe0f032d100906050124021e030d18060509030f0d0b01120f0605030712020303090d020d12020a06051308090f010306050d0b10090e0303131a0f06030601080c010e0d080c 74
    0x64011a040e0349002e011b03010000d5206030460340c121210014103000d60021215104203007861004442c11380d1950341900e10300b034226000c0d541200c00100f1045c0b95000700c1014041400114420a070780465140c0003103150911580010f9560300890440000b450b840e8100d01410f039103c4c050500c1240100001882001e94521215025094500507a40031f442a004002500e5056a140c01401500034010354a403550100a022850039415026a00602802c00303000c00a0409000e10500b44101e81c042c00c0c150840746400070036038038040d041101d686018140800800c01440881d04034400c1100d003603810354401300050317006e440c0c207a00c003da00c000000e094070244824454650b100e8402c4100c0d41c41002e89036032440c8210741c80e4018404440e4030074800654100c42c440b001c407079254060b0508191424030030b07846955504040702d40c044408190014072400c1d044c20003030140505160805424803240041c0003e0042c00394849241c401c0c1100740307a040601508508881c40341070500240c40303010001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 688015890 1250 688014640 688014653
    0x602030702010c021c1b02060c420c0c100c05070c090515100311071101081302030622060903090e13020d06090204020d09030e0f032d1009 61
    0x8142e0f0010240c060b00c62a001c01403d8528030451110351901c40d5100141d01300c035154480050080103d8100004110098044408206210540919000e5030000540c0e840800e0344a008180c109010800c1a041c1c8d26401c1d00407400c010341c0800040d03001c40c0c446602d8a003043c606400d401403154a00e1074140c40680c00c5a00000401d200ca000d4000c2d80710705691040080d080380c00868125a9200187d404008545014420314100b2010392802284406604d400480d00d94402e540c100e803c0380842c000c90307800d940c00652183d448088a081e00350940201d401080c0c580030000d1080c400c03221f01141d5840380d281c030041d9000c50240c02a00412030102c00340740103070200e070381070264549403c01200041d07c2c5810481c10f08141c240d015041c080c0820f0785640d400c01070810200c0407640030b60207007c00b0110581901ca14000c25019030745200c00b00500d6024050304503031003114203000341c0144903000030101d1100c02402c09008540740c00b050705001c2c12242d5050819040842000500342601e14040c4482d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 688017140 1250 688015890 688015901
    0xf06060311010906050414040c0c1203020403060e010902030c040c09030b0c07030201050906010305030a14091206060108010819020f0d02100918020a1b140307030201020d1103270a060203070201 85
    0x2a01d80c82803113a292802503c980c001c2d48180107a202c6514030b40c1e83d140c101508942041074031418205d11403100c66540843d10700d404040f0000007980400c08000707018280c01403000101e107070030080103c2c0403e0f0f0042512a60640d58a6001e561564000410103209444c001e0045070890702042140c100362085440c0d690128205500660810001c151001e101041060480b9400001180b50400420007a1107009080c9407404000320207126945940d101c280d4104030b03211340000500100c1ca09000050f03c4094180c0000780303164440300034581d49449607449140050b8040f50302e84461692500013541c0100305007402500415103a001020b0107800079901e000782c500c400d40c0000781007800d100b014220300542e550310700015140c3c0c008140011a8044580400e800b81c881600d81e108520201031565004000480060707600064104110040d8400e07030b000c03800e06071020b0b850350038103908400400121201182104210460130107160b00304118034000750f0740c4010155124688030001900800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 688018390 1250 688017140 688017173
    0x90705120c0307050a06020601030f0309051c14060615031b1603081b07030809010905071401090518070503070302070b0a1e050106051e0403020306010e010611010605011b0f060603 79
    0x10a0714001310303d0340340140901c01582c9059005201c143c2c0303103454144c5208140d0b40c040d01413003449600496070f40c42d0784c4a0145424800c16101100c41036a00e00101c0fa200e260030040c28030f400c50020b01907540c0d500722a45650030040c15060f912078031407081c89802805541600c6074a01c0000510050078060403180300c14490203134451150f5550740340380c0341a564811401003440c0603410410000040d000b103a015800009480000807003804a5a0343c1e89804c009030000c0c00f11035a0703032000d003650751b0740b08404601402c42501c400d00d0404902c8620041c5020240a50040c4040480046e500c81c1c800d50594010682200141c28242880b2004000a007118180c5000f0903001c00400300c8224480d00501d8101c130030715980c983c078140c4440c04a0a0200c400a03a91000401c10080000965000c0108038080c2070030b4200355009514020b00a0400e624411006042e42d050580801a036a0490081d80c80d81144c9080c4c180400c5581c50b041000c420320807002402149010808803d00030581c605007802c1c2e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 688019640 1250 688018390 688018393
    0x6040903030b13060f120206030703020d0b0a091505120d050a3c0509030607080711010911040506150d0c0908010c020f060c0c06010506070807121101110702010c0308090705120c03 79
    0x5e6202d00303417500e02d40210300020b5009441040030414042c482c0c0e0041100380344027400010828440000940007150700e510a500240d150700764114201c00c2017117004014507080740c800f290858034000082d1621440620503041c003001140c650f0050740141c00400e5070b6a880134036940000301c1592854400705103c5041e84d5983d124019403040d960040d002c07500e202d40014014115a40c65032012144442c1c010910700800031f210140180200090280101882c45902444100c500e00403e100403130308010003881c072510898006880e1a5084e20490f414148090000320700f04240724003c0e13400d030100e580443c450f9840c0160300001d00380d0106440c50140011020742c1c104c6c0c1c44104c1c40c0c0105010342c5e42c0c51034584d041031700104110718001d0020015184138000301410f01d00607482e41c00d80103180f94040c0011036020407000070102c0d003e12504588003104102981480c00175000280300c00400d42004060102c070f800880c0d61181e04020190042900400c000264002c0c000385d99202e04117400d00c513001c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 688020890 1250 688019640 688019669
    0x1170f030331030503061002010e030d050f07020304230402190f0e120309011101110c060f07050723100f140f0402010e010f110d112406040903030b1306 67
    0x301002c000703050308241c01da0703541401d503103c80d01081000e251300811041950342c1c0c0c0c00910400e5000b070001d0a03003c24a03402c00a01ea1034003220002075071030020444030864004010600c0b0a0a042c400a040c2544111300078070f03065001d070041002481450502e2040711050061044c505522083d01100134001f5a20300000c003017614203000021482001d16030705a04140a040095403013460700c0d54908a19800208400f0714035600c861103540410300302c40c42500844204403800c103841c000280c001a240c90041c0c0380400b2501d07512084021212241c4440320402c0d84428806410422280034280300f0343c00b009204004201d103001840d50741d098480c80038448001403000d171751114080307205d0b0790182c443c00e10f101c0e0540011070380c4441320a600414403140c020051030800342048420005442d0340c4078034070345281d5500b500340351880e42d01c803100c11039000c80362001c1400c10742ca180b04e80002c002da43c0454028410300e02600603104041a05030031803c040d00e19110341420b07070410301c01c844510841c80407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 688022140 1250 688020890 688020961
    0x260702010b22020a0302040b180a06020303071209032c01030b060705030904050c0d050f0403030f0917030a020f16020a0501090317090409060504240903020601170f0303 74
    0x5960700c28a4a03114400042032000c800a503c0c2c00030010b0201c40d142c0145030130f403030b4070f40b00040d43c20424a248501d040c0580c1040719080c081c041c8806800300d070004506520340300d4001003840c0000350442601903183d10a210030540520b5180781d442a82c010841c00f40150b41c0032075541c011a1064041c000b03410099500400e041643c110384240e60043c002d549800443c00c14040030308805070809940d5501003180088440040c80303045e01900020407019918101400e000f029038045940303a090382440d0003102000500032001503550764505d60314150721b95031007a039050002d01950201d807110b0140020703000c503010940c101241141d40300715240c03486607458000444400c1e00c0d900000b8081041009081c0682c0ca0400141c654210010300204200c003443d40c69030306655094808448012119114031401da4004c240818404071041c0204005c482981f030003036441c4018420010549502c1440403030740c07841400f06000e01400101100d40e030781403c40303000301000c1c103480e841665000d04400710300303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 688023390 1250 688022140 688022149
    0x1091e0b01031b05491101020a050f03030402030c061809040213060303020a0b090102040602100b0604180515120a02010c021801150908060601050a11070f060e0406050607020102120703260702010b 86
    0x102002d001d03030036171280e945035644280020724040056070641c072407204001c5c009401002210205621040030303546a081c144145860000e92081c0f0912171300c020b220104000310200c140402c81001120070814907103850020070100c02c0151540d42c011818003901000340b580004075011000d10510422501d55900e480c12804c030b0040d40221801030b04101121615900340d030704807403039a40c401000107142c555a021284a080c070050140c601c0c1c252111b0402c4505007003001950104403003600d444803040c036100800c3d43c803031940d90306c02411b01a03c40f14100030342d120350301030746112140b100c0c6d291b8155031113030138201042000903928070000d4081000032401c0d110200d10940110410b07100e10703080c510030800a540c036440022185003940704032140056200c1c090f2041c0001003980c0c2e20fa0382c01c010010310034401541c01541200e40528410000d1000503680014040d0922101103c46511840c0078a42103030400c480c15030742500b80e040d50b02c0f1060b420384201081405098190001c21520700843c0c10300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 688024640 1250 688023390 688023499
    0xb0c07020a0504150e091203100602160b0324060408010203041b1a1c110417060c0d02031321110118150b0405010801091e0b01031b05 59
    0x200481100f140c410018800d80d422041e80201010090711f00500084a0f02d00141e041100c0100c1e845004210801405806104100c099160507105100341750400482c99014400a480c4071041c0010b0349503000308a000c0030747e41c41a614000d20195031541d480340041e000c1e410984060340d5110b411500c10b5000c0381d10b1032007038040ba000c05685844c0d04a10003003444003a0041c000242420784038803034159504000b84142144900c175000016103442c01c2001101d1044818a5421010b51201c001e00240c1030352081543c00000070340720301585e00d503142a060054140da11000911326051403038840c507100f0546d40315040c01e80076641d40341480004c1507021401e03038004030458085001d21030922000304880d0100122409500440445c0724030104020808582023603100b01060795491158200308181c410300003804002d1141010301000d142e4444c80341801040c400246035038010003058142100700c192031801841c005001241c51012000d0b408011800c44c0420340421400c078031512400c10030010311 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 688025890 1250 688024640 688024661
    0x905010b041413091b141909022520180f060604170c100201050106140d060302100c060b0301180b0603011103011508070e10050a0c0b0c07020a0504 65
    0x34805180140f108014221880703401d129100c41e10040802c40840750840d80c3c00d100211175010901e048040b075844403e1880e101d1180001482002910351072a212a013580d000c04c10060b59442d002a80c450062010114003086408440303c0d0340c28008900d190510780402031040c083c1c1d100000082110a1840280c02c1d0400f011090114018010ac0b030038083c1d1040e00542828681500d8650034490360440803a81400c9034001c44444d070042c2040000082c4131513150000b0b00c01541084005400300c000901c481c10051070100340901d038030b80c540d000f9000540c0c0181010780c880509a10042031020018015684281000c070340c2e039420b08051281c0e403596200006100c8540c5619542c3c06a1f20300302410050789507481c2c041c01004030322030a00031402080c40240d10040303403080c03c9000d064110020004010302000748103000c0c4588503000c1e040d68003060740c60007640c0c502d80340c40140e900c0c400041001e86103d0000080200c0c0028074030040015138000c035010a0510350b00c008110581b10a0b200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 688027140 1250 688025890 688025909
    0x150905010504060c060e030c1b0a060818010f110d0c0e030712080405090a0c0818060f0c160c050f030a0f0f0507180b04110901020a03050306010302040b040f0905010b04 74
    0x100700721181c403641821280900c0b0316030219078402c1c0092041d155401c4011800025080400d0300c80c2140d408800800c827502003503d610030310138a88040507110802c004c0020007a0b8100d02c1ca4048151001e5020426924814104014000849031000d0042d00a0326108a8440c03800c005558014020b1143c941c1b8018003c006201c01c60420fa40b80410356a0450101d4880320140700100d040d9a0725510b0360303c06c0b084007600080c4240c0d5400010500c083c080c141000301c0c21403801c40b902c00135022444a501003041400b03568503840340c40000c0540e114080d041152004060000d40802407407180e10021200e0031140348800c02001020581c43d08002c00005002151380e541c2800040c0e80750ba424049030303000c5c0083e1944155150011400703110072000e500d2141c1da545401403040d14040c461401d1407100301801a08103440400042c0d40c0300304090000d000d111003c03001031666031194045501600c4001d0344140c0310313903552518400101c807038090242103a082c2800031404803c0b650030745007101c4a01d40c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 688028390 1250 688027140 688027147
    0x50109090b07170a0b19030b15060310030215040509100905010902090a17160e040615050105030402092205010504050f0d050d0e1009080702010e030c0f010e030a06090506011509050105 81
    0xe60400080c0540c00c0c90320740000d85d218400001d000d80a0000d0019805241c0c0900c603441c045c040c0c024400c00341001248540814030502856400d0742003c5010f4a5050303524103f1402e001c40d600d01d45000f1940482d9010810008100005c2031403200141190544034003444a80d8985000300107038003501d607109070001c048070420814400403081d09407030f610100058920350500d10030719003003508d01908030140d101e030600c06220400400d4800d00c0c64102c030781030306c50b40c0060415000034500d1001501c0a8400c010711004640c025480f00c0540842d4201c3c0c2c50502c00003e032514010340a84401c840960b818066427052410310303100403641c1d10314900380b41d9075940b4001800420200402c03a000b8114407511503c07811600c04900392040180c0c0c5030055a91540342c00c41032000400000d14014218002e805c441d40480d8207450b13405108441103424240b209802442a011901d080340e070301000703025182030182c25001d10a0124160741030307450181c4504180541d412081d26121010720079540061001c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 688029640 1250 688028390 688028401
    0x60903030c020d0e210d0f11150103111f1710060903022b0807050c03011523090a091a1b032d070f09080c01030b06070501050109090b0717 61
    0x50706103a2030030b0b41a01c1da02e000685a1805c5918102c203c4100344042070021014111301508003540d034144144600c02061040246d084e001d9040c5010b201c010000007510708101456940c40580700380502407945507410510410b0746c020400e1010603500071901903c100461185590740c40f929082e02e041d511000006031560b402d000c1c80040e0201000d09440c03121300c002c1d002c1043c46007540c42c184d008080031510b074a154140903040c0410169258800e0b80352640d45480703004140c01940441e010300c01c0310080071004294502c90400380c030411540c4a00c1e10001c00c400301065511565589014180464444210001d98240c015084e520443e0120254031090142c1d801c1000844d80a200c2e00711f2408080c807802c12040450a10380c6008034802452800c0054490784104001a60740180c41d002c0109840c10200c80d44030b080183c006810141c41d1002d441441d03c902045401c142e603c00d008024644c2d486d04100014034250804031075403070b004008542c20611407100f0344900d03082079031700140c0b03500d80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 688030890 1250 688029640 688029649
    0x4050d0e0a0503061605041205160602030a08041b030213050411010f0c120c12020a030e0604052214150f09360d17010602150c0d18060903030c020d0e 66
    0x5c224181c1c1000000c00c004600c1121500c452410b9500c41c034020a107003042150035540c44012604180304541c02444069103560784030b51041d42140d00181c4070201052034403c4ca240004040c1c0000e034000f084480c450300365074603a074082c1c0e100b54040c00481c1c9082001d140111211502515401d000908042016011640596401c0c503600d445080c0016010440d568140086642120f5480581c200040c144103150f046440c04420240c00ca071400d103000e0800c0c0001d1201d880c07010a00707201c800b40c01c3c0924801c51044d0710121240c0440500314800d1b10b04107600c08080400b4503011400341202020b180d0315402c03c412a070f070052b079207052100c501d0028180540081d03902001d80302411440a00106c8600c0802c0c840d512200000759142454054841c06807030f06844117911400c02c40d40700086104400144091942d040b00c4140780055446050302c0103900070303004241c60b56404403251804d0788201301e480d5120a8002d4841e88092107000460f42c0141d0301c541d8111081408524403244007000fa142 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 688032140 1250 688030890 688030921
    0xc0f03230a0f1a1015080a0e01061211011b0f0204090204110d05010812040e090f010f0c020d030b030601332d0f11031204050d0e0a050306 61
    0x300c20200c81c1c804000340c4480c00d02407040c10302600c504480c0c041c8078a20500661545900866001180360301501c2c10424041c5610340a450408000000c80820f01e074a40e1500003003030401d0190001e02c419520b03a004030641e03030302001048502c8100100c024080c0d5005100040d8000034810b50101c0044040c3c40b45880341a403024120b134401d07942c00545005980e40e1048680081103c6605034950301910305040807074006030031544895000c492851a001d503410102c40c00d0b95100302c40350810341c549031703419072400030200c001180d15424001c1001c1d43c08010340c404ea81403c10343d27003200c1081c5d0503400b0035812a17945405c3c00e03030950002c000502110038018002c0c1d429500724941d460100c0e151101c54206a280f481a020004101c0710f194032200e407990840a10344040a01cbd4110803600030003001e41101140000c400500030701211813100ca900c14029038002ea2091142c1005524051801c07507214000c03030a5500108440d019107180c81c6c1001e5280d0350a0700d101070700400301a03c0f40c4081c44610320 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 688033390 1250 688032140 688032203
    0x20702030a02040504030302130b07150e070f0305160b03150907020c0a0905063604080910020114010609030804030f020a0f09020703030507080412080a0f180c0f03 72
    0x400d04100700010703201c42c41150700c140d000c2c0d94010307101c08800340307000c401c111b2581c040c107500d000901041020446480c4060494204500c0004901c075607611260304084290303119800080c00d07040700105204011170150f20711503100c101e8412a64543c07000d281140401da44081209450b012000c00b2410f048a066402103901d00483d01031408600001d81500c0040e0810080207407202c050191504207160500d0200c0b4218041d80d40d1107001c100b5600301c01c4502c054001d500d048801c0440c0c140113990044480807100036114416504421001078040d0000000d00c40302070b0030120000640d039114040110946e50b100300141d180a103161100004500300e240140d070b1020001c07000054010094902e100148140000944c44800500f0090101c4000400c145c0c1405030300f900f00030020710800c6015800580380d09001229444940e078480045c0050009100c00c1072800c01c0c44008003e00709403104000f440b0b9140301d00303219210310350218080200c0c4001803440c81401c02406004441020031034000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 688034640 1250 688033390 688033393
    0xb16170a1814190b180406060503010612050c0912010203060f19030303021c1e0f0203100513093507110618040204030c030b060a0605040603020f0c0708151b0d02070203 74
    0xa5845000d24900703684400050000241741e01d020a0b01e60600e0302415006280a0a1140c11580b4040c03020b010249489410101e8a54a00005101d904034901f59040000060801a062468800f090303000b9841074030624403034100c070401d030b0509141509841400c2098041c94048461940e03a0503006500070501940c40c12030031291001007403640380324142c43c01000c00350070303030f0700c46000d400306000c84030340c1012025624010010000c4200001c81003000322501a40d040c07a00300c202ca15101d004250354000101034081ca004100010300d0b8444419142d528140900511241d030407032180d026100d0114020142014902103041900e08580500240745080700070420250300c0800280c100e03803080d0000c0340c0038072518030705000384024418426441082a140307040c249040800280007800f80d80318000405400003000701000ba100000d0b00c800308030001c2260741d07143d00e03102082e48030900c1d6901c00d00c50300001800a01c502090a080610075001111202e25140c10500d001000c1e60020740c040e80c05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 688035890 1250 688034640 688034689
    0x1603030e0c030706120f0b0904051510050a0302011103130f14030f1b01050f0a020106090b010e180a091a090610030f0807020d0b15030709060b040b16170a1814 70
    0x1f94a0340c0c2c080d00d104034490720107031280d903011114403110000301924000c05810801403d03c84e90302c0300c0d0551800d990702420192000241034101d03d1451084c0b4150741c48425521000040c080740a82c282402d65603807580c07020005040c04141036569100c2080d011407a8009005140300340070003021309524400616080c0d02d05010305a4aa600da801003040c0c80050703649440c1002004401d00c1109407041c42480d022220a54180002e441d8102d140c3d0300445046240000c10a2000160f206079072441d4048640c5d0b03068101e00d035958020040c01c0311604418002c0c40d0014102c140110062400d490740000e90740c040b00c3c40b03038a0b00c42ca5074000310f03400ca800240c03006039800800c80003580244620004078014001078200710625080c90700381c0d8040c00c0014100341d4103011064028040c0c6041d10240f4502581b94041d60070b14130080081c400b80036182e040100746600100218a0051400c0c95498960071504800c040300142d205040b442981c0802d410040c90032400c1c0f9114a40d019041c14500300002c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 688037140 1250 688035890 688035911
    0x60909021c021b1e0706170f09011b080a0b06040810020a0512090604050c01050c070e060f09010b03011d040b040602161205041a0a0813081603030e0c030706120f 71
    0x781011650b2180d107544000800444031604c01c000c2000505120720303041e9244a116a0a003100b448050442030303030007003d400000d4910300e09520012926405c8540c50204010030b460141c40c4950a6a0000d0440d05024480541c1c1c01c0400c216001c46900c80000c042c2800507604480094012101c428100b0a0810060000e50340070322506019900c84d40141169050625105140441e150708607414000203200c510300a1002282d41d4080381c03003e0340100c41d26070366040010802c0003581501036202c040d4030008100f040005001d54141c600713483e400c608918000801600c105000c86d0001c00003c814800900000c0302e030303000360401d800d0100c10040003110075a00c1e40741440c03600d0220710000f0000b02d010071050398203041d402c480c41140ca040900e0010b03510801011108001c164103682c48042c40703081c040041140803900e1014080c030000c250a900b40c64018080e00a60201e816284544401d104003850040b540c4801c40d001616961808442030030841e01070000c0566104130281d54040341007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 688038390 1250 688037140 688037143
    0x1e070909050c090f0d02030607030905100203040308060319050d030207060b040e03190e21100632011205090f10090209010e0c090108250207060909021c021b 69
    0x24003482840c44107a8039400008203110450340c501513024840d02c4032000901c0541c9001c41c0550f040b8540e490041808442414000d250403203c290f0000e045100104000c245948114030500402c4218169002030010305580340c1c0651214901400ca0340201303000f04919030081d4000c103103ca202d010045940c0b081200001c044070200d940594150300000340d807110010b581c14007061400d03128240082003468034004541030103101c04280082c0c02c0d82481c1107940360010480d0b10440150b00500b8031040d6200c10700d5804c150201407020b40c0940080c00403601c0d8025440d54446022010794441c086103a6180b81d2001504000d000c2010b1030042d014800029034090104010640700e84401050000082c0306200c40f0400503400080003009000c02d0007512107285c0c088034009003007448c0030030306911449030000e001c07402c040b0001405140a1044021076801140301421a001d68a400c0d501c5a0380f015034100380c3c030031025005100701003500304024900786035001d8079060300c000d4411a0480d040c41e940c075 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 688039640 1250 688038390 688038401
    0xc050712050a120f050a0b120307080705150405010b030c01050a080f07030f0c09030209061804061509050906040209100b090613080703080408010c0314060f011e12050105091e070909 80
    0xf13680b0320f848600700311007140680100d15a51100b59400c40200010b00031443e224081c40c00014040b54001500e00240b04003001650010441e1401d00300140c142454918000d05184e0383da580a40100303804070f1100c0d07018005450b444985500c032240c0c1da80c2e4070309081c0034144008041c5014544e442038411407907141032260b640c0300c4240f80c82d00d03514241140100304c10b616000b02514415264101000702c81c0b15002034050f007090344280080340744641c180b014014002e45402c040c0940740340804000703100c0000034005e4041c600175601c800b002c2d09c41040060a062450203102c2001d2020000c4074803908140c00100388040004202c01951601d8260007804c6c0b086560054a1079031010a081c0304500080c4580802e0b0005801c080000c0450094032a42c80c134001405076206038101420180a41d01403007034414099500901001c0310800b03c00050901440404c030107501a1a0400108240c2480d95450b40a59460f402102d801040120004c0f03060000800720020003803250000901c020080c010b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 688040890 1250 688039640 688039661
    0x403060b24040e06270a06030206070b04060c0c05061f030b0a0914060712090501021b010c020c01090305060117100204030302030414040515240c0609010c050712050a12 74
    0x1041c0d85a24200c010180f01c000039008900c1591030400c01c1401c500841004c10f03141003d028146050356449400c44024001584040e4004c1e90026074202040042604544594469a42000780e10740500e41141c00d40c0c00d09000500c59801080841c0c0e8284004c0c2101404210307140383c0c0d45e546c0e501ea036205000310b04180c54001c1c07000e031914202c41c208413840840c1904c1c03c00f03000c01800e45240c511710080504080d103050500440c4d40b4040041401420740407111420341d1111408641041170440500074183d440e00c0b1401402103c0c8540c2c640e41c414a1002c007226003010080c11544d09207484421101b1b048002d45a051085c3ca110450750009400500002e42c040d030040d589692616010000ca407400c500000d201d186441d0410005135140c010b4001c58100550354003070034010b089506449490014142e0b48408004070303042c5458040040d0f12032140400900034400d85000c07040070358460103a01802400031b4411445100030030b2180001d020f012086290001d102801000c10800f1540700ca0340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 688042140 1250 688040890 688040959
    0x20f03100e010903020601050d0302030d020a090b0a090315020c030f0c0a170705010614010203180604080109080310050f011b0606050a060f08090705010f0c05070e0907060f0201110403060b 83
    0x1c2d46040c143c05001c2a401040196460440c1c270300140e400a40b01e00c182441006420b41c00301d54001e08074401d01d091805008052803140d82c500f0754420140110103148401c5980c4450510440141d520b540283ea0740810694000c50611030302400c2c12046800c020854010b0b80703e144036410124102c84e04250850450300901ca80d15556800c1050031b40d481604401000440e4024041969a000044800c680c001502d240420f03400000010307107510480d03014400710343c2050120018401d514000758060910400b844c8480760ba140140000343c25240c141c107005c65058001019042d400c1010b405915206410020b800e035120000100100b1040d00b043c030001d410b002d0700c103858507044443d4a0b04402c041006240f114035201c002071181d000c250307041c410000d19806e5501040780800002d030107080c0309a0303842c02910305200c646a0b145090f10444000610380c41c12020114010b00c1925000f10b20b0081d00c40c03030b0504640366003001c0c01d0030710f84154210250284111640d001e251850500007050344 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 688043390 1250 688042140 688042151
    0x2070b0a0f051b0304020123180405040201050703050309070909030806010e040902060405060c07091a10321c0b0a0e0f041b0807060806010801170a020f03100e01 71
    0x4208400700c4509614402006141c001031140342004081031111102c00900718036a00e6403284012603900d030466511400029440d150259080b1007100604085000c038216262500e04000800c020390310180e5010740803400c20086040440d00c540b000396413100e40c58003202c0c00196a550000304807043e0100c2a000240d500040c0322541d81d00201c0d00402d00011281401720040b10740004285203c3c6200f000c0c841c2200050000c83e20300240704440080c034140c0781c100041d000031a036207070340000c01600040c89084604580000b490040c81404031003044001c2141c20060302c01d5071020343c1e015074801c8009441c403d1201005810801c107400c02c1d0a010064003049050541d03080c0640003505411040d1500403e10800c4005416550004d47c020307000309500c0c04a000c91908a24222107641140709940a014000304195800c403140714028132082c3c1c0ca5100c00d81c4d848020b5101c43d21560004c0c4081e800880c41d00000d4a0302c003ea815030190b00a0a4410354058100600b0440740051801213080c0d4640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 688044640 1250 688043390 688043401
    0xc03230306010908012a1713060c0207211e030e0a090c14091504060306080715020c0103050a021303060603021005190f02100608010203180309010909021b0102070b 72
    0x1810032000380801c2c0000e001743c086e100110b090f035483c5c109110700c0d84070100c1400141c0e20700c00c0c40003d82001188001070440d04107144188003503088840f090b22200c1c01c2180c00017845100041260840340b40c0444a015203030140c070180b070b07030002c4100c06070760a4a0390140d0702d800360440740c840d80c01c240c03007030b11680c2d0500da104090165156141d4400c0b014a8507020540034000d8000c00c82d40203502c3c50a640740d42c0d41040000040b10040319000ea04400440030401044c0140c02d54880c600303840145080300d08040c0d0340c0c01001b40c8007002a011200680280030388044950107500a55041442e240c00581030040c01c0d50190001540d0764010b880c0743d40c581001300158203040e03a0b1a240c0e1031a81c46d0003031520702051603144500c0b4040301410204210004032240044c400c0c0102d00c00503080d90402d0141960b545400340c00307034005881e0070642120754070340400076540c0082158104203060719136481c541d240904160003500201c010507008103010000c40d41c0208207100038600e0301e104400140d00360400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 688045890 1250 688044640 688044647
    0x150602030a090807050f011101090f080310090605152d07060e070501200a0203030a050406020607020a02091b09030a0f1b08030304060b06120f16020303010b04060c0323030601 77
    0x390f484441903401860702071140e511007451003100c0d10340a080c450040e0300850300b6940185280100540840c00c4020040e0401403120011400317090350745000c0042a4907180124110b6185200e1280d000421694054017146000d026002c00003081180c800383c1c011868055000c401181c62000034020f00040c0c0d44100403403485860010101c0130000c107039460030800040c0076000d0041c0da4030050b00d40d1203180e0301c42907403c0124815165001e415603403542e440001c00742090b0480d00a03c0c0c054040c200c001a030440c4000340079899950010a4039296031103030802c0071541074204480041c100c07410003030b40c03a0b2610304002d46c0342c0c4944580c044144024041c1007400c1c480e100100c8001d10308040c80020040c1d480c000003929006a0401000100d0800220020306c2500c580c91600c44406c282c1002c1103861940ca11f400c034410003100d0020740b40007803234100481e1203100034024200ca00d0030500c0240100c1e4402c061a030116407090901e1002c0c11600107142c920354000c59901c002c001c0000007000340b256403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 688047140 1250 688045890 688045907
    0xc020909100c0207230901031419030801090507030e06040b060a052d12070501081306140702010b040b06180109030c03050c0f0406051c08040b0705060a05062b06150602030a 76
    0x4041c51004103a030b680314009081b1041c180700c080c21541541c02c0782018180140076440800e00c402e111002c04115070714024115010034420100c03c3da1070500050512800b070302856000c0030350000078004a644a07594400d40c0240505540e4100c1026807005c00e094446101240640d4101116000104442c040d100d0407090708801c10b5000c0d0030b4000100710071400c0010a46e050358800d0809070010783e0b601c1104001d03485841d10140aa500b0010400e00f03040d81d210803075001da81d9a600038040d104003101400107441301c00b002d664000c6410003881c84402e4002c4040c000c00481403520644480d541d445011103103a04e900156940d420416080c03200385028004c1c000061810342e424800380d031a080c002020420141001001035004810800410860b00200c801508070000d100340c035800c2c035040140e075844d812070b4140c08261800000c5009850200e00440721280c001c2c0300396852000107542c030f10204040c0d0350b00700c0d80203484942d074000c203a5014a00c44003802c00e5074011900e900031500b00500000c4e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 688048390 1250 688047140 688047179
    0xa0518040905030d090512070f05060748030234061b1209030213020705061b12180c091501110f0d020102031b0a0c020909100c0207 58
    0x1460030000710002100070050711100c160780c1c00c000501417560700303149003003000c0a01c510511040000c0d12004024000c035003a102c2d98003440813105190768054040d50400064a504040d02138030f00190159194042c01d03101d40c1c1610f81645107082840c100380084e2003180305d20202c0c05078100c030348401c4c00c03a2a10003019154240e03005045c0e00f046252404954010078501170501000594454058a184d0082a1850541c1d0284102c04031100000009014041310301049200b03140c48504031000d01424000c1c0d81a40d5002000360180d600c0740044000804134410070301c0e41c44141031200b1000e411203000414420000c0d40311401c0341c0310141c0d4056080940e8034803443d210300341c01014800055011500d03056070036401e080180001c00c0822003030307250200c41c003004003491203405120f02070344d41d064029601a50f0f00000e0340026810404c41440c036405080119030000d4019480c82c2d001d40f4000d106960481c0000d02916404c80d4024850804e0300d00044203000075900c04542040480ca5115030701345400d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 688049640 1250 688048390 688048399
    0x20a1a19020708030c18030a05011508061006050901023904051003020405100503060a0b0109050a0602031c09050114150a0806040b0403090f14040c03060308071b05060a0518 76
    0x807035595a01402804042c0c030740301200c400030034000d03c1c000d007405403944c81b54001001c4805401c1c2601d892400b038851011009114080e0090004240000249880c021410181e4510711305007001c200302d903a07410465000d4114481e81411039003c0c582c28841349440249400200600c1075011001c0c41c41c081d000002500491411042001003403e223800081a02d078115800304e1a83c0350729100c0c001022040d00034940c14002c2e802880048140c6074045031900c5820389444052550b60002c00c03002511a1150b6405a0400c110304444108021882001880740ea01c0c0000c0c92203090300e0703030350868120344140f6107212020001d01c17404004401950300366550440b00031007090304204c0d8094541c1005000102144106030118040500640407040500807203843d4100d400d80c0c075074012030400d10900110340124940207014076503034802d028400070b0f203401600079881c000d0f080e91003410382c0c100c004181090000f400008916640e4042c010403808a4560341c542d03c0c1c01342900c00300000521000c409104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 688050890 1250 688049640 688049647
    0x302010206070c151a04021201080610121202100f0c021e030d09152c011a01270803040f0504020c070302010516440d020a020a1a1902 59
    0x80c101381015550030842240030404044c00301c0c0b11440703042c081d0b2199910078008190440d06600000c1c19604942c40201107504c0b5840b0f821591010349294014030a40e01c100d6182c510104600c0c0c2c080703120602103441150b001e00c0d400b03400401115980c0c04036406494032000f40044484c0c1c1000b1188a81b0719820140c451000c00200c0a55240300f0009003846407034a41d4182c905209056000659940d00c1070418800000011000401c190381c4601540d554458403041c00007440c81441903d8041e80d800b461071403401d441c0c0b401518407040c0c1000090b40036800c02c2429079104005c1901c8001004940015601c40d41070211840b041e04440c1c100c0c80c0514814008a13060901c0060b103003003103a40a0822507940c0075200043d0b82e010040c4100a418a00c0e058100804000010008081f0003c442c200031020741084902d1441441400e85c0b0f400c1141c0c0034840491140c40340e43c000c102a8000d0700444041000654a003c800b0341c0030b08850700d003034101c0c0c020000030005840702c40c41c454041076401c524 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 688052140 1250 688050890 688050893
    0xd0804060e1f0e01050702060d060e0a0b0f010815100305090c040e0303040605040c091b0806010203030f2706160f052b060509040b10090b180403020102040b0a090302010206070c 78
    0x403030300c0c2c6081c0340104220040c4040320260740628216003101d600580f41c107a03180b150064403006002d891080b50700d4481d112001480c807049610401141d0340f402030072070b00101d851500456000c0f40107030808110b00e06d4040c0f03980c50781e51500a140c0024409032002b04091604e0b401e140c2c1025091031105010702d045c200c079010036641c08000c07030354400e0348243c0015581c2c0f51030400340d02c2c1c0d2109030001c0c50424585231820301080c1042c4004483d07004103540e81c1420343d4440004a0700ca0105031011041d4040c43c20120701000a10613000c042080c0c0c0c0c441e5440401c02c213070083d03841e01d40700783d0701c0341c2d00025005851950701c2c1d84102480840d25260500f03524000480494080140381d0921840c0c120ba00d00b1031900e282000c40d04410b000709001490103405007002d0810038540501901c0080185044c9800050458164018021180001009201c071480680c940d030744241e03002001101155820800401d18280020151060702015030310044064250700c006850302d54058012000c2c030003003500000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 688053390 1250 688052140 688052179
    0x11100b0f0d0309031b120606030b1302060a030905122109160611100603200301060f1a09091006090605090604151103040b0702090612150403020a020d0804060e 70
    0x8580d445030314183e2051480c03481e01d420003170a4016100c000c400400c51002c0c001250000011340740561106469900c51514091150456000081d0042c5082c001804440d00a03800344200c40c0c010030a40340ca00040a80c140c0071a40090a00410700d1103050031454030561800e15907a01c00d002500410103038110a02d10300d600380c03662180301b040000d1060100e40c1c2ea1000c0c45440e030018080001031100341e8076854669040300d00d12198003d181d10824411440f0316050050900b100e6005101400140c02c10a00c4e03000c0e042c80080c4024103980401c401080c0c0c0d120350100c10b1082901c02e100c81c0810707003030600040600c8516848441004400d11100284c2d80c2d4080441d02229160f440d42180c2c80041c55007911020300a80c041e400d80c0c00040380001d003a04080004085142c8200c541104c035617144010000c80d56001e0350500181c0d80100c6003400d40c9601540100d401ca030080c012243c1100c026800a800124100e0046803000c802140800c01c6941000d007512103007804440c01c49030301c81d4150200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 688054640 1250 688053390 688053407
    0xa0203150705040905011d06010207030c0b071403040b0c160f052107090c0f03020c03040b09060d050705280c08030a020d0501120203060c0a05090f0111100b0f0d03 72
    0x46403a01045000c212841d000d407045500422040c0c0c03041c00990b079030382c071100d000340c008900a019201000c030001c0e907590320124064094075401480c0c0c050f858107020210005401041c804ca45002030300c0390a01301c50400300050801011540809555911300500141c24005a05020340070b0442d14074003480110701d614443d600395101561440b1500c1040c0c00e21200055003140211350300d028009004c1845c03001608019552000c90322240200189004118200e220782003002d240ca400034802404000d55220080c480960024040ca041200384000780003151000c1c1c0e110300101e4800280100707035082d034840d880e070b0003092203940409910200744082c080140032040100b22080c00000540118034035070688103580307580782c4100855a181c0e50303120b444040320a003e0f07100c0e100c4c500010f40401141012141c52030107554889080404d24410300a1460064403c5c13030601007800c5114004650800c500307000c00710082c5002c030701350140718140121000d4a500c40d5000300b2800b0454030221b504403091 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 688055890 1250 688054640 688054663
    0x50a1205031b0d0b090a06060e0a08100b1503100e010b030c0d09050708012d0b0a0605071505040813060822050f0a120801050405071d030a0804260a0203 67
    0x769558144400d43c00001d28190041c030b54400f1210080c022105035a03030010003541c04035107488050030b00040401114001d01d10407482c180d4003424100b61041040d8120036651030024095080050301d03058280010f4104880c0c0414450848500300090304a0031032050041c10440350782c0d072450510b202c00070714501c40c01e4038200384242c4601c005810424104061801000500c008010603002c4040501e50720700038500302d005420803141c2e030401c0f94000303101e80201014002d220400241c9001b070b083c2c9840e0000d420944072440446e058000100e4031380038242c811446418810f40d50103650342c80184444140e0000d104102482c010040100040c0c0c0b215400e099050807554540600341c90902d1500c0c01301c038142d1f842d6024050140d002c01458503c0d60010040503101d560442e0380343c0c0240000c40340c08803521400120f00642a0350a03100c1890ba100324688040d050700d200c0c00c1507803900078960f031156101031510851541c00b08036160781c03030f00c0703801c014040764001d0a00803039180c000a680351000640c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 688057140 1250 688055890 688055941
    0x10060506070615091b02060604060e0621030d0504062003070302160804060f171b0a0e04110d06050d080706020f041505070c0602030309120309010b03010207050a120503 74
    0x10000038080700d42008002003603950405e01c030780d651504860080a4460703090b103000d4441d880101c0d00030b00c1c1902806040c2d421900d8444165500c00d810006141c440344140309082da034a401c0400050424801042e80c80e040d214042024240342c68814121403c000c001c1000031100c00da9171000002a03000c80307401610920717002d601c41544401c5050134020000b4010140707100040d00244181d0400641c00602d8140c1d2602808040481404010b0800c04c03160008003078640803d1a100c00102c1018140302801407070820b48414018012030708a860307010382c0c21030b04079000c69408503050b21400743c0b402801051740c41d11084010303680c40d25840c1c0942c0344010407664001c10184a42285141560010030014501d4610144801e4000e0300d0b651051609507103800050301d002c01d03202d000004507801000408000c0401c2c0c06c000c03102180d00d4202405040032075480e10611680c545c0c0900285ca1190f0040010703100d01c445038030700000080400344030141800740c180108503807440c2c16441d0350041c148800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 688058390 1250 688057140 688057151
    0x4150b031203010e2e061206050d0311060c090d02040b04091502090301050a050f04061a03030d02131a160503090406080102030613022d0f07080c100605060706 70
    0x80019092081d1030108aa4030070021000043c0b00c52250207240c00740410907000303903040d402c03070310000c1102a0424040000c850510805c010091281158414290361b01d5130000320507488200007149440c4c3c12509500241c15500c0b0b05101000034032040360045d0030380b0526490408403c0104000070b0110f14081c0c441d5a4903a6600f5043c1c48035040200050380c860b034241031203c0400c00d420000d400005d00c2c540030358a080006095425035114540c05454a0703080c4424590b03890740e441002c0c04d09404d202e0a10003e00800c1001d50314100080c1c4403e042180c00583c07144680003604001d00d4135a800003280c01c2c1c2e4500d6940300c140c820340032204010f46d04412000101d5450030124036601c511a9042c1d00949480780001c0c4480c019806140550720403183d01b82c4a0307819018803010381c0a01700208907828900700341e4424540712441d428048a07804c44209080c04440307038070814184c0003030a080d60102e00020303205114000034000320b030000b000c41404225107420a808200240168800105401c0d40ca5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 688059640 1250 688058390 688058411
    0x6031b0a06140409110403060c05210a1104090f0b0405070e010f230403060f140105210a0309081504170d0216030504080705010509090408070212031809010602060415 73
    0x50040314090002e0b040c003030005d8000310943c240c13a58410700c800e82d407684c60f141c07080e050503104004807400340c0f0101400c034940c40c0350ac085180f025100a846000029942e0323407422007066014014000604403481c000031511317841540101130300c00403020244601e103844200300d989501300c01d000499000038071380560b20f071034181004c0d41c020604000c414000e0200e01894140010450010b00980348180c005012a40c18078003c3d00c155110450101c80071212000184541d0801da80c603142c07101600c100c081200f11505070010704010b074202003a00010b803254030034030012104010b121800d02c7c46c0b10f0030714101e24003629903109003542c007250000c10810020b00c02c48106426010b45200001c400c00c035500700c0400f850b01815513030251140300164040c8100006940d03000f041a0b41c20f449000d003806040b40d9940d0782c0e0a00c554065003003280d01411601840c08520410406003920a120201d00280310824600f002503002c0f0581c000c81c03c55110408000000300020340e060f500d540140004101420302 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 688060890 1250 688059640 688059677
    0x91006180e0c0a2d03080304030917060103171c020403050606010c110103090f1401051609030f020f03151009052d1009020724020f0708030703180b06031b0a06 70
    0x45290018003042130282c040240320606e00110300941c4a5180c08c0d4500f40c0d0741f03100080c1c60002412508041e005040100040f6030a59158a51078850b00342c428504291142c01050301075152144220466001c04c05004116040140c0d0f50884400d08240085120643d25921406001d4145c6810161940c6a00040089100d100c04032f4a90002c0030080540340040464002c0000316180704000040d00300440b09a406030011000307403078100c2d042d1202c0310807503024420845400103126801d4401c119012080e04c00256440e80640000440f080e501454601c09906a03600a4201d10b4100b03c0104043d10100404050f10252014104100a01d03602c84a0711400415650301502540780000303003103c20040038080e000014a404100540800d03003c81074041203004032801e80422880070400780340400e100002440d44a0150716003c20040c1101c0c040d0600c05039420740880780f0304241400e001c0c6600d070610911200c440359401c00c00002800100060401d030441c40f9031014410703500302c44c5940c1c050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 688062140 1250 688060890 688060949
    0x910090e0c1e211203150a0605130902091c0201170c0d1503050d08131203140a09150207020f030d090510030e0303010e091006180e0c0a 60
    0x40140b00c481c2c60a1076004080c2411491441c0078490b04000c040c00303104000e082c0d0394024a043d101d00400e03500482008000c601c0d800a005183d845006c00c1e101c200341c0d41e0b41e402c00d00c00f42609a035425150040c1a0040d210306500e5000035031158014030049040c1d46400e00f805402002c80e44a0030260796550005a8441745c016881c9584030002c4003c003d00c02001d10018802100708510401c85a0348549242d11500420b00000300310741c010142c42c801862140150703030b130040010044030401500720342d00d08446c44008080880465162290b15002e0b011402d9070030b5021803d185d0030300081071030741da851003088514081d04500310360108150007075442d0143d0b101c0300b2101c0601190748101c0d20040180081000d4070483c0c0c465201c68443d01c4400d8480c0c055401030355180401542141d0800e0103117280000c00401c2c1d03881c140300d6048419601d01071805140000c018040c100c145060900281d8015601c00c1c0c4001d45c1290301c080c01040c0aa104d4400c288111001600f00d80c510350382e400007001d403050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 688063390 1250 688062140 688062163
    0x10302070c0e18010204180c091e090c0e150a020a0611040e06030f0703110d02041407020705010c030207090906060e07050405100c0b070c02060c030a0e0f0910090e 72
    0xda4240468460840d640140c0502c504051540e00fa4810185140c282c0c8624020903464a420b45819580c2004903045802026140d0604420b1207803141a20b9048001e092194140340c01c0800c0300b0403005030207114200c0310781c0c01e501e81107000380d41207008140b0312180350025a10743d81000a138203104c01d101b03101411302103900040134001d01d1000c100516007508640a20b00080b60440c4c0401c15620307001401a0409030014054484d0601d5500d074401845e8102103200d400540b11440d0000523540d0340b044084206d405525900c0074104040000c2c640741c842e401c840d040c41107078000d14000c2900021240300303e440c03404012440d100ca9103044400360010364030a0041c444460148000c441d04440588241d84c0252001c406480501d8411105100d0160026103954181c00106842c1d6108100c00c0c3e640301d0016110611b040364000c542c030300d10307440b41804500044225031454074915040081c40902c810443e00c1d0111400c02c481e03880c0302080c2c140701c0c0e2003201c3c0c0d46042c0e1650282c420702c2545040d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 688064640 1250 688063390 688063403
    0x1110705031b0306090c0a030b13022e0e010c060f1506020d0f090e0601200f010b0307090c02121303060501090f1b1e02070824010f0513020901030207 66
    0x40902c20410034041c0c02e22610720070302514000510680c0009003403042000010302058a061940c0c40e1160810300142a0380e000b11006000c40d00562214031107490080031a40c41c617548050700c2403030343c503412030101c10b04c00811480c2c5044244aa91102651071134540003000094520081c4901000820058424000c6804018030000e809600810500c2d0f0408c0142c0320f8210581c61880c085a10b01114000e2408001825012a000e544582840380c894803000c1003d00c40a030340021540d1418024100740341d003d0b0b460700c040c403899040c10b000c11802400441014820b0340b40d04000a07440745154032a040c600b800200d03400c1c11400800c3e0740c441c015a0801e0040042e544c40d16600300140681000308944141030010000c520302241d109558450000d941e01c412580741c2607121880c0711000c4a003241140300d086000f041d90030061201084180310030460884000500c68910314103201680042c55004828230200410b4858101d05441c032081c9450050b0385100e10001a0024014114064040e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 688065890 1250 688064640 688064653
    0xf250e0702010219050c07030b090a0f0c090e03070804050f061201150f18032909030306090c130605070221010b040b03030405210c030a05010504030f080906060111070503 75
    0x140c0e5019401454150304180f040181101c0380c5900356a107124007907414420354041002000400d0320f03a017003240c000d003102003520f1f41115940c07606054200280c10540746000c0018080090310304e14030075080e07150101b502460408605440e658401c6c0618030500380900136840c040e4801d517549404582660038590b000342500d50b12410300070101c44144a62030b01050b4a0440681d0050241001000510b40d407554a00e4050440e43d07811496500c2c00c0f5044022519200c2607042c44621200d0360340300d401c126000f544c50340785c840100113003400c01400040094808110381c01c607000503081003000b5584030b410150754554080c07021a2020303100060b200100150444400303d07c238010741240c1c0e10350b042150148038172401c5400b019100e00c50361003107543c04003461620032114620700d08118200c0d055542915244001500820304218101c036044415941d02c200704800c042d040b0148050300055841c0c66601c030b251000050340e640d14080e04180c14040025100000c02c0c1081028401500e03004c0d0a5480303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 688067140 1250 688065890 688065901
    0x9090105060117010b0711150f07050111030613051b071b091e09110901030803071b02010813050a0203010c0216090c2c1c0209090f250e 60
    0x3400d040d2001c5001403e02c41940d2005800414503d060b03d19501006140210560340d840d56095800c0100ba0402030b1407615800f000007a1001d440c0c80e0441054451740e071106807402a00b101c00b03d0005002d0b1040a0003404a00c0d100c2d0200300b41c00550100e40014141c940308003100c28490114402021a00001140c1040042e640b0a0003c42c0b201015405106030300c400259040c1c410809004403061100380c5941e0070310007280c004c4d007051809912078211040c0e049010030f030350038002d800076035402800005010246501c960640d0034100c420400341c1c901007035540001c01031788000d80868030014003000388130288042030107142201a401070080240702c3c100701d4083d48800380e003800400810b5402c80e0005842c0700c140110548004103689442d600f070300078080b0307850b00300c445205036046860242480c1540d80310489407011600d01c0b508030740400c40c0c0510400c02c03140b00c001d00c1480c00347c01103010041404c90002c0c103207100196080e140c1159203212000703c04100d0701c9901c4040c124240209000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 688068390 1250 688067140 688067143
    0x4050309061605190b1302061207110d03020703050901052206120b010507050705011808060703050411040e06040b0a1808030a060f06021507030e0f070906300609020909 74
    0x36071180c40792080e20f1384113041c280c00800c54042c94070301a10320400b80c80080ca600310300e05911908180300504443c1027501c500b8041c0a0300e10300321800404241c41a0f032160824400f00005c0d8202c04062809619240480d03174000d0050007404407160622101203040241c20175420014040a6020401c0e4a00c9603504c071402014183c0e1810540c0e0a0b80c5042000000341d40303d00c00f00c51406401c540244920b92400004503900c02c03d032921480c650b06060ba010030010010700030540107441907a4003140310f040505100c0c54809514410f680b15038504a01c0c0f05001001280180c2e02581009408080780d494118070005040c00942c454100f5100744100410002c600c070146003d84c01c100800c101c01a19072084103117a0b102e034002c010250748071000014419882c0038030b40d0b901204602c3d000c9000d0649182c00d610300303a070382e0304c0031001e42c0c205520a202440d010310846004081440e2908180c004c00c0e00e4002c1110641c4500000300600d9083e100117000a03034002d625041c0d8007034552002c134504160f086 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 688069640 1250 688068390 688068427
    0x11070501090b24060a0203070b090c190e07111608010510080102090108010b03310204050901180303270305040e010503150c0318030406091a0708120405030906 70
    0x102c64640840d0041009034050441031030259511001d800b4451800200708540c03a0861512282184000c00c90b0800240c090590f050141d290b2100a01e605c049500030451404800441e290240394501d030100810350075004869001103183c1440401001480b4212341000d07940721590103050310380c080014650702d0550003144a045d46c44004250552522142400d0388558001180013800400040c0f042805c0c440040d0740141d00818114016034502001500c041d90307200d408070341c02c082d125800042d0b0515000301e55200281100800035403400645a100d40b1302030303050240030503580d0314400720340740c103228204600030203810104105604c1d545402082684603000c0c54107800d803250000552800c0c0016500c1060480ea600302a0540e116180704609401c018a400080c9040206400c5541e00500040c000751000d940c1c1c0d07409090a01d0107010000c11000048296030b181084030001241203a020f0391169030500c040c8612613181ca080c09441d5020b2b00c910305030f110304000754040d111b440b640c603070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 688070890 1250 688069640 688069643
    0x18060106120e0a08270a0b09030d0206010503250801140405100605030601060507080d05070809015109090c0e07080c13091b0207240e041107050109 65
    0x184482d4a201d0b03001d40d02c507000c1c000010103e40c0141700c035a0740041601940268a440d0b0085045c9072110750000428080040e80040d108940004040b161400d082c4070008014803176000511041d40741001003a559101d81d80d000c0d50a40b03000045403202c125050680340140941d000a000c0b40d058980b400d20203820039101210b940c4241321800d10100c445009110848000402500e483e070703e400400c0c0c4481d440301c02c3c1168210010400e8424800d41c9110782c60046640780d561814503d0a80402030071608030b01c000701c050b0880240d2090311808200541261425003640300c1c00d1186d44284a0804094840040d031640540104003188201c00d6038040c0c04035a0146100306c00d01661a0407803004080c09485620000d030200c0000f03111440c0da01d0041600c040101d080b281125604c20044045800034448291811107400251091035810810301c4040d05612418030100d0403114402002603d1000c04034013800300340603191110795599485001c10b0004002c403543e0390b06203031030158000c00442c0d50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 688072140 1250 688070890 688070927
    0x3070f0c05120a030801051005041710050105030102180f0a0e0103050f0d030216240f2903100b0117010303030903111911040b180405120906090918060106 68
    0xd201c000e80c0080c00d038400f6501525021480e0b4201410b210f80c1c1c0c55610082000d000702027000150380741d84103544001200e03a1030003600d0410814901c410540f6010f0f44a140b01e41c0c010720902c00d900b00c0d40700d0212020381048960040c10146200442c500e08160390088034a540d21400000a0000c0400e00307440040700d550a9a0105070545d40c143d0032409a43d08401d02c440b9200040f4001070b041c3e1a10750070f10240f14609940d20f01201c15400246c400807100441060745801156020080b290701070421a002810106213000c03100000c26641d01c10101a160760580b41c02340f03991035901802c803021410011001c100308568507420042c02400a1400490000300104011414580080f0750906500303039503e40c803e00d40045440d03890220300841c4200c1d9001c0e41d5180c1d140f55941d41c18980c0d00100788500a403001c6450503007021420300e550458107912041c004c02c0104156501c000840b101002c040728a41001d403980142210b1400717444040341c0480c46040c0010604035084a00860309c0c1c1c41918 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 688073390 1250 688072140 688072159
    0x20907020607031121060d0602030a0c12091a0a06090c0302120609190c02030f04080a030801090902150703030912030b10023c0d0f030614030d050a0203070f0c05 71
    0x100404c4c601c00e41640d003240e02050b800b5090f444044026045c3c005030000c0c64034121840d1601c440040343e00603103140c0c0b419075540300844807164200a5000a6000c40f403420410051140c81c1c0306100850801810020401600056480c4299a00c0600a440402c5007005498900701e005402036000381000780102401703500085003454858100d521072400507039803409088100403000e010341303c00c00d07006040d4007003803018442e84c0c941c0c1000f401c01040001c00601600d0740c94200a0455141a0400c0d00c1890074910b04c84c025855088200d503c6442c001c103803a40d0b40c3c146050442c010192014024641e024070020801a01e51503008001c1c5400101c0b80340d4450508500c09aa8074183ca1000d0000c80c5840044400d1500600d04000200400e0455840160440c00b81ca24289a1104103e001098031580c2908519030305108007805000320030121240102550f000030f0342c400c80142d55000700800054400345036032003031059400e5146d1108070302c0c00700080c1d481c00440d840708a002c0d050141d02e102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 688074640 1250 688073390 688073411
    0x901050904031d042901080c0c2a1012051302030a060c1e1e1d04090312090812090109020108070c0503040b0415030e0f0d0302070f02090702060703 65
    0x6124a500803603043e00c4680f49000c0000440c1803400035030f49015801030b954090b00358403029112826a25509a00c0c030403200f0f0301090300140600b40c001e4290400204240541d9021140011384046039400b0a40480c01080d400d18800007074101018910f40c0001001d4400c01240e5041904941ea0512110b000d20143c1e9071507850650448001c00065030550006542c240402e459501550000b100da1401e512001004010300c500302e00941d41160026102d07003904144486e0880740441d0720b088074508904c3c4a1b44031002c18140c4181c00300b440d44070300d98480a001c2018090340c0f812060403088231042c452454242490325154110180415030000c22000190518006204c0d442d01c466058485800a840c0c0010484103032224134000c5805100810012882c0d61400d00078000030f00c55020b90b400d682c2902c40000702900e0030000001c001c0d51050311b4041213048081003001009040f49401a2152014203103520307540c1429802070341000c04c10042c002540d902060f0349101e001540c5007888000702c1c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 688075890 1250 688074640 688074649
    0x50903070b0d0203043008060303070209010602250605030f0702010e07090f1506050717162108061e15070f0b07050c0601090b0310060e010f0608010f050907020307080406030b090105 80
    0x41b1a00106000c02c0408140c001a000d48001030b005030018040302c1c100621540030481101c1c0070f802c40c001503030083c00c9003d4103c03c1507400d2140501d00c02c00c2e403400903140103c00351280c00003400056854a0200004040d84d200350300488008001c001120620380d40c424000006200d500031400c072060402680b03100442c036280346402262100d54038145002c043d0b8035925404042d1880f541c0c005901080030b2040484822040103915014aa14001101002018038455000e85104030b0901500b0410008140c0e105003400c03510405100c08104010040030014500c1e400013200180000d10201d144400d008500d6184160380d803244011040f207840b03005090300c4a000b10032a081c0280d102400502c4071045640001000403005411940b00d48140011141a101da54014100355820700004111091003009000010011414000b04950500c81d542140c202103010300f500403502034001c1101240700b04104d82e02560040303646521182c82d860003c000d003005503c820f119401400000c50b440c940b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 688077140 1250 688075890 688075943
    0x311100311030604020c0709020a050414090610030b030a14030301060908031804020a0c0f123e0a2a060e01020c09070e040906020408010f0e0d050903070b0d020304 72
    0x41807681421a907840742040040d5110480790807035401766840010308000280080d207c0100142c451a0311a03050201300c04500301d040b0012449103000c0418800151070b68502081d4841d07540c94082044e81943d00801c0ca80317411003000820704045035000c0510b00300301202540c182d0b0385990314540b0144e9034028141c0d90340164001c100c0b09248260030200c95141caa4001c00a403515402c0115410405488a500304c80e20301c00185da80721062503006c0e0150b90b00140d411025049400486032503c0700070f180300b0980d904103207030060402d0121051454044e0030801c1010b0258880c1400008295030303510b25465a003944c62090b0003058200000c10007602443d01c0301110364043c0d00500300385058800300103540c040034140030280050419900195102c502514240a0141b800541c2d00c03807610050030308507030a55071203207041b510307003e01c2c8500c014000ca441d40083c0381e03629110342c0303c05650000900700744259005040e00f84002480b2040c482d00c54000e1071150b4000c02520080082c0c1002e040541031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 688078390 1250 688077140 688077161
    0x903071517040302150a0f0b04020a090b0c030c060702070e0f240a0b210f041a0403110a0c03050f0d05160c0e270703020f060306030a060603111003 65
    0x44070a03405a01ca54480e00129900500a10485aa02c0720100588402c6142501c0c1302c1b40031900c0c2e5400d010b2101190190031302040080d1003c500d40319490500401d4481180100046041c00240e0900948010800e4031400d40b00308098441c00d08004502030b5a0b0220752044026003040c83c00068410200ac105140c070034086070070300910a1003c186582c00c8203203010142c903417200301590042160800000507011801180c19258403915440c41c1c1002912001410f804240c03e0090070007000484001031a4000c04802401d62015251860151a9040310044280580c0700c0e014401c3e050042140c90403003102e0181d42983c0b43c1540524280fa21070102480300400f00f40d04025440b8900003000500c1009401011440491615400c074290300c20f1054640e01c2003484c42e03007803140e490303002c02c900c07400103a017107000808010303145a000c1001948110345151103094084001005501c041c0302450310145d11580801401751a880d188100c20104c00b00c640c0611620304580b80710b1402803040c1440c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 688079640 1250 688078390 688078397
    0x801051003090f060506011106041b1e051005070f0501060314150f090a060207050705091e0103021507060c0906021603051203091f0c0e04020a121d0703030509030715 73
    0xf0082500d41030054980a003600381000411201a40300050901110740514410390320070071540c01c030b00c1c051840e0100503003200d07202440c006002c55000340005014000c9982c140c590410203151001d040d10140550b10000c0c0a1819051200b400c00c68198005415248a003011705007240d00184c14941e5411100801d0480240407404a504020201541d41c0c2c440b50f071100f2540c0c0326400ba50b41000f607801004046403c3d50004070300380128031f80141c01952040344008070410b00c010722500c14502460612010f8090310b00f409001e02c0d0500d1607011501d10b140c2010b0140002c5104100080420500340303e040e005006105105014030030000707040d01129040001031083c144210703110489035001620428140c48ac0840311100c10000700d20808000700d644200003402c040c0c5403c003a0070300305c3c40039070248240d01c1005100c1c1e10b1a0455140d0861744290000003d5801b80b14145118080800b2a901c11910901130008101070f8480300914801105a080c1c94246035104031482d1088030203001e15021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 688080890 1250 688079640 688079663
    0x30905030706051c092a030b130c060f02010219050d0b1c0b0a091e0b090a081603020a02190501090b0307143618160f050c030a080105100309 62
    0xc0007005e4003d20541d9014120000903905505241d205813010381d2500780408061120810500c50781041145d40085c40720450f82d1080e00d5555403a6003020f0601502e414070140c4c040380100f2600c00d5051b604141d0640741c500c01c030801c00001c00741241e00594455070300c050410401080034207294521140002c03000300d40003000d40d401e0340d4403071106034024a5448400e40e50903550010520a41000541c84084400c240142d611428041141800141074011603409502020001000501180d4185400312500d0402107190b250881c07c00c0030504c0d011354010200410700c030b01c2d0740c40d0000500441d10241c86000798541e9130600340d1004d010440788000400d44c480629a41c0d8440c190060400000c5211004144010480c5c0512000f403500300d800e002c040001c0f011051810101820360311304060407a8203003189050140740e2828240707144940e08012800c0c0b235030365140d4010f0081d211181c0d0003100303a0f502d075a85500001c0581d2024460203120307600034900d000f900e50003841001c458a801400700200e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 688082140 1250 688080890 688080937
    0x1e0c06310b0a0e0420030103020307090506060405040b0d020405310f02010f110601030501020a0323010b220b0d1506090509060a08010e06060a06021b1201060e0403090503070605 78
    0x20070b0703200401c169810603115182c940314280d44c050288030441100c44a90b4495040d4012b05180c016070b80c100310700c254a40814041c031561030780159000c85004840110341c020403640820f0f200441e070f15000303400904200c140444800c2c000d060f09000c031552075180d04040c81440d40201c41501c9890040c1901108900304405948208400d10782c0d012282040300501900070340461414000740e1065031140d40c00b1540c04090340d4980501c490203501d0000d812121703040e444108071007840602c07412128500014103100743c0c030740016140d601e0350110802007031038964034011513002d0740c4800d001c058624a086050785c4521003162084c0c06903816595600ba00500b4441800742994002d000d00742d00c18001b0000042c410800d00131840300c0501e1401800301410901c0901402d004681c1200c403d640008031006007954140c4081d840b0040c08454101c0c0b89030a00d800513004080d1a0442c41c440a804070400080c980c002c0e804a0440341c0a90440300d4250780c03843d003169603000c2e0100c4034a4900410081c0513 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 688083390 1250 688082140 688082147
    0x14040b09120a0b070906050301050f0d0203280506060d03080106050c0a08040b1e0412060216060c02072c0402011808100e0f070302031e0c06310b0a 65
    0x2208400508140e0030a2100e039801d519054401c44229071000c00d09040002480d40007001c200200145d080850440d4140b900080680c652402e1042c09100c0c110640c1b02507617420400c94000118490006c4203000f010206d48060441001c001d075150302c581408038030542403442c111090740750103a0b80c05403544d00303000044036103900001c0f50b6211441041140b00100384254000c0c00100000c4030815900d00071a4540000d1064052040c4003d003002d20041291403410841e228455502103030050b950b03114885400c03003c3d80c0d41040a00841d00c0d00c807001d840a900000c1e18010f40740c2203010020030042c8240b0b0302486802d603109001c10600c007400854010350050114410b252103003001d607420386031600c0f9900e01d44000a00c0c00c0400545030300401039900300074441042c0e9603942d04050f180907411900482c1c1d844020b405100f4078000040140c20720480305102c424040c3c0320040100c7da039405e505c83c0c1d10b00c0030400c11084a004482070101e40008085c1d40341c0303004c1103030000701c40c55013441b042c0700040d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 688084640 1250 688083390 688083397
    0x80a0804330f0e0a081b0d08030a0221040f022e08011d0906040b130b07020a11010e0a060f0504080319080f13060b040b030607030504030f14040b 64
    0x8580a441d02104107501d0622000c1e208041c00c40c9666108500020320001040790200000180c01440c0c0804d00b030003440d00101e508201c00d0001d04d040c0508400700c0c000308030024100d8101425010002c401d100842645030010b120b4602c1c4800741d004022400b12010640e11410340e8000c01035111400044010704180c400c800c04094440b40d510601040031a41d51260303015004403000160003200103002e2041d1003054403401a0b07480c003449450b80790000016544181c040c1000d4115401003001880e480d00d000c05d5006c100b5400001d5615030b0a0a0384045d55039010f145048545120f0b00341408540d51140344a92064000102900203847c83c007c0255001000300c10316604000080101003540a410001071910007402c0c0b18070744c1441180e4500400036107000e403001d44d1180070381c4180442d0030348122580d5000c0c0d8000c040042c07588042c0000130001d00c0c0c0000199058040da000700701d00d5680588c81503100d68001d45501c01d030841d4559003100c00d641304c80d141d4000712909220510080d2505d8024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 688085890 1250 688084640 688084679
    0xa110402090402030702071502030a0905041d0f010204240f12020405030f0609010606180308180d08090307090b0607031817030711040b010c021012020c0a020a080a0804 74
    0x501d0000d14102040a03640220707904005030303000d158100401c1043d51016082a81c3e544050750624070703c8100241100d01c42d04c02d04c3e10890321000c0010380014091041400c0801e980708440c0000022600070f4040e420500c40c2803103e100c02900041b041238901a03030302115a96503680426040304840a0342d49480d110135000c440d5500f40700109030790f1010000c0c0700180801c03800401f46890304d00c406500b076070802d030010b04c2002845403c821041400c40700c50f5041d01d5014078490749542c080c030a110102c03d0750008a60b48400025415024048600f00809070554290f054508207922001c0c20002d8a1041d40b22a4010004000c0740011a03c200c60038042c00f8001d22407014100ea40d03203600b008070030040719a0010350b0000500442004805000f01041c48000c3c3c4081c800008041c0c0041c01851462602900502d04502c10500091082034103107441c1817214070854071010700a950303954400307002c24102c0c02144401c0001c034044034002201c0300e0b0b89038007080b850b1515082a01460851205030403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 688087140 1250 688085890 688085899
    0x14060f071b0b03090109061109090f04060906060e1602010603030504140f040606080702070807060c24050c1c0203010e01090b010c14060609011221051e030114060c0a11 74
    0x2001c038800182e03400440c083c8080c18004280205c050500000300c80c15a000b5507400a0200302c130f0216a121208420307403040741450101540e90f03640c140000034081d1868010141850300d2004a8111402c036802030248611585000c0315880f420300c168220303452408042d01190313051004110b000540350300502e58080280400a00303100c03c201050035100b003900100086409901000100b650400c2054010104a0002c00c50310349001c4014005a61302c0c40b02411004030583c4140c503001d51807101c128808034040c4204914546521000c0c030907001036141c8a5001102e09041420399840e00a8a058a00041c00080c0ca6443d12440800500caa00d181a050011649130007012403403003480080360204c400c0242405280072010041a00720581182c0d11800340c0c0f140482c04034280c01c070184481c81c03160800c42d020406180041c0c41c0f40c042c0c40790003020302c400030040f4503407598108080d5048881000000e80ea540e01101046098040d41c450400380b6172040303c0d07500c04a6840454024110000350 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 688088390 1250 688087140 688087193
    0x60f01030b03011506111507050a0306050d0309050a0837052a0109060e120106050307080a05010e0a03020a0f02010e040203040f030f1103090d0203030405060406020714060f07 77
    0xc001c00d007940c3c04001d44c0d140d070741c20221042122a81150030450515201006049880454030000341c0705280030340160304201c0701041d4130009601941c8004040d000042c86068040351a103001040c050560246501034a02d004c400519400c002482d140d011114131070402500311002c0c45800c0c2c0c51843d03100f100120140c0071080d00442c8040c08010598800042c1e40d40700da504e5114204418010002c0250400c05519020883c096026011101d2180101d81c03501d00b2001c5824503901400464200035450b000e050800601d411000806c04120b41c0f180380240034a100b0034130655100d10f518400a009600b28803602000540c0d0044032103841c500c1410040c2c80c6c140c102d40424200c0e04112412541c80c80036000c400107154020802e116210600d01e860030402004180ca6078032030041c2c6183c14041d12544204000315502031082e500a4030024000a858540d1081d009598030030130320075102080c0f100900301d001400c002e811202254102002da0340b070000d890359400d2120201100c982c0da46070303154 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 688089640 1250 688088390 688088411
    0x24030308060307031a0718050a05041505120f0f0a0201170c0c0102181e06090f03010e0105100e10050a180209101e030203040c0308071a01030323030906060f0103 71
    0x12070403080350755010783c001461480d01410143c147c0d4910b00710402103010016081015503035030541402038410980380401c40c2905803015900b0701202d604280d5109036000b40249250038009041720001d60160115440c02404041c3e10303448090b01000179000904c48100d01d405007000308032039038100c0e1142280c01e1030400001d0019013240c010000450703010301401480d009a00c1c000c0c10090091440f542001045030302100000c0451241d0070006000d10000d5000d14801e6400b0751102e906664440001d014a1500c6a400004540c6902404050710a070402140806604c6c40d404425100041c008074101401d251203c4460314004040c800402c0d0200f0103114592189046090541c034075880310380711034210700e140312054502d05071a141007520500400c40031030004c0d610441100c1c0c104013295032b1a0713144e0410503a803807082980e80c104d400382d010000040590000c0640d48806203250070740f19100c08206080380d01d00c002c3d500c40e1090341c42400881c0c410310f07011047c1d1101e81c0c01410001000c2c03040d07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 688090890 1250 688089640 688089653
    0x120106030f03030c181404020c1b0a2c180d030608010e21132301031109010e01030b0102031c05060f030d0c0605060409080f07062403030806030703 65
    0x240d0300212140c81144280c4010550180644181d10300c030f508011040c2d41070806a96551110303403003020725403032a146074132410f5225541168084500300080c0d0741c0d01d601e4503120660f8a14008502400744421410014004c42030010602038409200002c0304000000440001401009030000d0034041840d04c00252015082000c132081802c03a850104503546000704003421190100c941c20780f9600001c0642000b41c4d4809620b603801c1c0c050b60320264503803020080d0742c50034641e95000000c0b940502a18505c2c1d48c3d1490f0b0400400c030800342d809000c1c1d400120140031040c0a0110001e02085645083c0b8103990300a400c003c481003030600c1124108030300c000140050340130100c103118205640b0340a022580c00c25101440300140158028000c6540844004190f42c11011b000340c4030320359038004143e03039941d5a0000c88805070403003110b40d1100145503410741070398848102195040c0c0340268400342d40060903106080c100042d5040130310146181c8007503400c13040081c13000e40d040c050700c1004800200c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 688092140 1250 688090890 688090901
    0x20a0b0a03090209100b040b07060b0a030311070501020307150507030f1805013b07081501140a0302030601050d02030307020405090d020d03060b040501031e0507030203060103060906140f1201 84
    0x201940c1c040380300246801072144082020345221100c4148103010301c0703019441401c40e400c9604051440744d903400c503030501600411101c07842603400f0311064400000d06602a800f0f600080049c07050f660039580e07450042e6500d201da0800104001e82248840521025590007594051014200407800d001c4e0403100b1030440c2c0c40301d1001c0528000805084050203001d1052140c84a52402c0501d04001e100050a01000c07030302803c13801500981c820144110390500582000b0704601040f100705944082d01003c1c00701090260407908542284000c2c040d1514002c414101d13a0054090401ea9003010140300b00901c5503401681c061004010400c01a145d500c585480350000401800c0210240c5800900344190808220b00309401c1c00014002126204211401c40c0c1c0242400900c4c0c481050f0949004028140d14420071480d24007080704698050300210320504c0c09913000c100305a210180c41003150802c0c040d14100b40f42100070814070b81030a4030407003500301000704403040c5905e1410307081b400d460 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 688093390 1250 688092140 688092157
    0x180d2109061103100501020102030c09040b0102160303091508070f080c1605030705010501050324130b090c0a0801060e0a050711121804090b040f0c0801060806061c0203030313020a0b 80
    0x1c2c8000b042000380f01026102d803005c1e0409100070b6140d420040c1340c58495014207141c3c280b14079903494100328168020410440d9040100414009069590034081d103444020f101d9101c4c907100328000c04541c28491a02c8510801c607070340b01c5190b00042030200301c0d82c5a5006054012a0904018020040440280c4110794510600c025681d58446103030241c29108180c0c02a0302a50001418100305500d030f01010f40701c0b503043c048881141d51600c1c44e5800a0907899009010b662940040c0304401c04d011a040da841441a14610303e036070740d01d035062800c94110707108024003c01140e01042945406030803041c0c100400c0d2820200d0300d0810440507091070a035807012914000c00143c5c000e4690000031803504040d204135001c010000c1542c840c240f140500410040ca00c4840480000c00c01c9401c05001000c0e01c0744800800100c1d840301c55183d602d200c20b81e10544a841c55240c00e03d401e0000010b0340710405ea000e0081c40c1103032600d803426614100c258404076848000b0320710214550044001400c01d14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 688094640 1250 688093390 688093421
    0x504050f011e0c03050f01030618022101050c0306010f0503090f030a0f0306140a0302040b040f06150801150905060307051c0207021801030b0c0913060e180d210906 72
    0x2e04100d074240c08964100c1c0b040d000741070400c405c000e2a2010b9446040c1140d4111402060a5070507402014566000c21700095100a205001c15440040000030440d0014000000c11250b200ca0301440000d00044420724000390312000410741c154412405907800905450403580d2026515407080d0454000c20f900900041d00c03000080074143d4503010710402080c100700d82c00441c0151102182d0541e403d400082c0c0120740301c0340c08407007581311a40b101c0d41d50410040100b0480f038070307600c02c24610340c041040e00001414900c0007184041c45441035581c8000700d0b8035800f80309403a000a00c07a0a800046c0344c0e800748034040c000484801c2240e41c3d80300000b8002140160385552510421151070698070500365200f60600041c00003074001c040d44d6403c0304041d4405074803400d071840012000142d010010444a040070000a024035540d40c0b83c41c02445041022078041046200746551807401141480c0005c501912540c150b510b01d041020407508060350100d0030745060f8031188140c032007800745110203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 688095890 1250 688094640 688094681
    0xc0302030f0619230621060a1103060303030a1122062718020403021f1e0c0f03111b0a050a18021317100c0c150504050f01 54
    0x6034003c240464510808480041060a0003942c00c01060181144100b2000440c68040b94155541440000b0701e180400d1500c490903080808031a00d854003610203a40d410300700b000340c0c8034010398901903034454034002d4011400e580da003500400180a0807409030814190400c403851011140001c21220001d86200d080d07241445c00038018012008440c400080c0441900c1c010000d003c120441c0342103810480c0d500f00079a030160102c00c0284a180c0c0000c1d40840c0ca4003950140c004048040c0308103091586480780180c12403900468001040081d14001500d032034101e44c00039603c42d40e547e181500a02c0c01d08441140c8814030f40c80c0041162500012045a041d50241d62400107242030145c901070301c0040e0550b00c3c0c491624a000300b91490f402a498000c5840b000003004204120000d01e0609080301d460000d846a00e600c4801c8403075844145c03414524030b9154103005682d441c00c10b46c4d1050701e07110b0664000c1c01d9000100009041100d01e4000c025005c0d100130720034094602255403100e141901d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 688097140 1250 688095890 688095901
    0x132f03060109050d030c170c0f0c090105150a030905151e070302040605040501050c03090603010f030308091609020307023c0105011412030d060b0904050609220c0302030f06 76
    0x8001d05030b44058131541c52001c20034002075010400310329071036000080345070400c0d2005503114207014100d00340419100321500040b492200140c10300c2c003070105981c4004542d8946091020500c1e041e0f0f02061451010403080440a210390310900303c2c01d02030000d41d4000740100080141540081e07907080030110001c40d8180341001460f4a080c0c000103681021490300380381002c0036065020b144101070501c03c000c950002c401c1024002c40d02d4221000b04020307965a114003580c06860384901003a8009840003000410340880041c4030141d1800340c00c000e1a00720700d07013003404002c2d600c000c1c80d180450040504403001301e80341895505c03125002c410403a071150012103190b2610758030224800700c96818907004010f4044030500e0b4440303d500c00e440701c22038802a16040c40c590312401c1c0750346404500e001c4001903080c644101410b00c10f4000c5406015903110142008076a0300d050b50450b9607a40103101c90241c21049084042c0890710078a09038542d00e0703503030300040d003802d01c054040000e0350441ca0400c41e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 688098390 1250 688097140 688097147
    0xa05090f0d0f0c080c010f0507080a021303060b010e03070306020a171014120d080a0606051306032007060509160311060a0314040609060b01020c132f030601 69
    0x105180080100300c8800400c80050160b100303480c03080d00b4440da000c41a003c0c40748220450301e084207810001e20103c1c40409140b80144022220800010948804203a040303034a40200c42d00d81401c89982c02c000741c00c40d201e0368024641500220306001c600000110f0036201800728400450160000503154094544050000355807401545d11050041e81046006129844210241d454101e2244903458548011074024410b000706002c0900c1000c2e0080138142c0e100d500144180d01e005400e024042e6244820364141c0542c00c10704001024548007840395600c26800407642281c80e4400c46a1401c1c0d044031400c00d540b0801c0180c900075200c07010002155010844100008900451392100905c0e540b5071804c0401700c030f40030a21488001454075142c7d4400e401c540794805085444030020300341450108001d0401072000c541050a1200344900c540c008a0100100480035100c5801e40350201c04000041c48200800303002c60081042d000c0390100041c019598440b00132003030a50340e041c07010000d0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 688099640 1250 688098390 688098403
    0xb060f100314182a0d0606060f09080d11010b0a0305011d0705060409020315150715050106021e030d060f030b0604020301030f0b0414030f120c0c0d260a0509 69
    0xf0182d0315901a001c00c8200000244501303442880381c803915010508800203a41c0d652844003031a40301610400358020301003207500902c119001034a0340c510310b0013402c10555110849108101494114106440c07205020304000d01e4910059800090740d40d02c41030020320460025001596160b54651509655440700c030843d82d003100710640286140340c54030340010150311650241000032034020000c6501010041183c400280b00101030b551401045954004143c1021100b40d41480351a00500e12490795449407506842c06580030f04a80f22070fa11104c0040c0020070b0382c0500383e21080185410107001485010301800e1940c11180358945103007002c24121402038161031080d8810001080080e224011511550b903000000d0302c100e03075a5040c01034215014007040407032400300081000117190711100038840c81413952000541c1c0c3c0c0320b07562031034074a024040090b4555400500320110080c05a4440541100c0280000000c809401056242800265043c103809921501030104444060010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 688100890 1250 688099640 688099651
    0xf0a05151e0903071a0f0a0507150501050a1505071e0c0902160b0603030c06180d0e0d0f2402071106130509060d060212041b080a0b060f100314 63
    0x8680c02c0c00001d03400a500c8070064400e0b40d001d0b8124040700c001654188068590700b001c01000c203034448000c508090300c40e82c00b40c24100c584069400a02050b50a00c0c0304035130503070388040c043c43c4400e41403101c1080e80443e40741d41e01040c41424800342d000104ca4002c01d81e41704d07103168240710b001242031402191489054016603103040c014444100c1d0800540d090717154068101382e1841c9292503a8000c00d003103100382d280000041c003400c8100140d01d1111040c00b8408076100c003c4a01e444400b040c21201d07800c0f8203800c0c0e80e002c0700d04282c01000c202100460400306024928802c01880300010b202031881001e0128107103140c010a00d2414400c80307801e101e9103604c081e200b503842c206038034541e00c000f004603000e01e52150076401d0103d4140d807a8142d000d102240d111800319039401450210850002d811102110300300b010348905c0202501e40e00650044034010350040c41403030595500c40381c4404c030003098a0340003010015543e40a55a008054040f058561000030b02603041c1c0c000b07200a100300518 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 688102140 1250 688100890 688100947
    0x30525020f01020c150c190e0a0803131701090b0a2a0e01080f1501030905070f03060b030c040605060a03092904050106090216020d08040e0c030702060106031a0f0a0515 74
    0x410403100710700d4821147e1010440c0303050300100c0328160018203c0e03c4e440c2c00441551001103003c0100d40d103940080c00999210b00704030364401100c180300340d082e2810700c5802003d1444440205442ea140350304140e0305002c5040b222070306003088035955584508070540c241c000030308032100030b039040d6005800300b41c1100c0251402100d070b2500300c0c0c01c2400c4290408006040698a1090b401400402e1022034003408860000220f0141d40b41000e00207040170461042c440d0040c844600001d03e490712a1400321600030782180d091100064058006010003e0165030798000710030720540403d450103d0041400c031060b114050f0341002d0030440e00b1640c181e0440d104052042002c02078001840940720b84081e070403900d442d17a5004901e03010640d40141e41c40609070050702020310001c086294081c40c8a0300d02036003140c15581e611b2208400f80c0d00e1600320084116032200030140c00c0e007820030241c0f218031000b903c00c07804c06940340c1c0866901258801d08120724039020502812024050380b81d840c44d00703110407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 688103390 1250 688102140 688102147
    0x307060f26090d1d1f17190b040e0607120608101410030302030f0a030e01020a050a0f050f07080a0e150904150305060f071407120e01030525020f01020c150c 69
    0x1000b2411000350040e40d0700003091145d05c19445c1c18481ca001030000c861240300d503021810300350003101030000075622596401d814400340e815541080e10401040c490050018881d41d15011010303500e11110070070b40d20060340c0f03501020807007410030080780c1d9204044540c0080d07c080c0920100e00c6501016010500305248500100082603000056410511400352030036594042d030001500180410018054a5400455030510140d08000940f0400c2101c0e01d511036003101c108001c903005c2c814440c290051031001c0c850302c00801c1c8448064058105035081c40110b003044000058a10180c40d560420b00c40000a0040328034245801251117440c00059050344282c00e5a071010303240c0b00001c018442402a65000403071151150211102d503d149d18801c964808003404c25202100a1080c1c090104d070800580c0007a0703506c03a208961240104005c8514945030304a250311003841c1084210342140b24488601404100c2880100304030900070006052824000d4480c03281d5600040c000703001224140f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 688104640 1250 688103390 688103447
    0x50103110a050d2a08150a140112030c0212011a0a120b1303020a231207120f02100e030304050f03030907090b030a06020a0e010e0307060f26090d 64
    0x405002d120042001c0c440b814203a085804d0040110694000a164400ea10030310b001c02052000303050181e201c1e0082400900d03180003880c003c0e29001c1c4180303104d0300500316130a00403c3c0300b1032031003d0242c401841400d8840d1001e040c1e9003503174060503d04074824003004d00f482c49403420f426804c0040c4046035250b68020116100c0407202c81d0020950f4007484580f13002442054070034480790712103035400074981c034580440801e1043c16001c0301c42c0d10983c501c10031f207402c0030003c0300600791083c0c1d07075012011780c0500c3c0d0304480c1200e51300c05160041c07056214880300b10401c05058050b4503155002540115181c0c903023824910725003010078981c1500394101700140100b80c8408248203098501c40c2c000032501c1c29400740841e00d0268002c0e00038001a101081944c696584503203049490f2000741c0e2464ac90858400130103494540620070100421507103002c108006001e2104002e41d000310003c0c0032403959030100070032590b41c821900405107800c90b44138050f50039081589042da10051a290030351b4010103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 688105890 1250 688104640 688104653
    0x5010b0c0d1b06240b033102041a0a120c12110d1a0a050a0509060f0a0b0103180609022110020c010902031b01020705040509101e050103110a050d 64
    0xd505000e007500d138540440920fa140c021040c1405800b191301154061a582d180a0005800689034043c21050090f180409261110180070051241d403038040500c07604d9900300030052140b80c00714058a02c520b042000c01d0f41d81d1440007070090141034124640b000c00c0340b515008a07a07850708286040d5040703000e80808621210840411040c2c16908905e8030034a508248121890703190601c5281200c08003001041081904038500a080c040014091601d83d9120682ca9a4044404000c074408240c0010844e0f9525000f102014606050020305105207064251100f019824240c901c29101c1a0310700460408641c07898904c1105038458401140e0034a0143d1180c04c0c0120704410b040c0c0210f84142003120030360040c1180c66005048500802a09540f0741152004941c1c00740980140c00c000900b904040c080c0d03900c0707000200042c00d44c2c00100300c2d18100400c12849007044151010000000c040c03034a125250185009035a00c8519051000c01c000348030060f9000680550204108170300001c17035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 688107140 1250 688105890 688105937
    0x10050c0c040c0c060203071e0e010e04151e0f0b03010303140d020f0c0f010515010c02100908060f06090601140304121b0308090c030c010f2105010b0c0d 67
    0xc22100864504202c40084404464040340608014400018030000c0c80d040b408116014568084180c6607040b001400e0342d43c0c0c980c5111311404500c0c881c0d4500c0702031407d030740062103224080c0110512607880d1403012104101c0400c0a22040004050178405c2c0104c11107103500605181044a20f99811542c00a1610250000c0702e001c8050204070294004802e4050342e80e55200e000f031007500c540d0070b0704116035151010b441c240c85035441c00e4013181049410000e183c01024040e1240d40b01d903e0a0b60038880410380403c030120800c00c4c1c503038010070f103804103100c609c0c05584180c06040300ca08000742001000d42000e0001c90512044424500c04040032070142c903031081d080251500036082042080d80d0002c048072a581088010002800c105500454050700490340d1400303c1d10b1942d07110090603543d0740d000b40c2c0320f40450a000030141c0301e00d00c101c0308001700000a00002401d00600800e0109544083c4c21422910901041a05401c0801c0101c12030f919901c0c07405003008201241348904070007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 688108390 1250 688107140 688107163
    0x50c040902130e070c0219051c06110f04090606020610034d0406030f02120321010e2401050c0f0616080c03060102030901050702190602030910050c 65
    0x503008601e0442c440a0006188010501e0b051040050301d03003924010540c402244c07040b88a2511608607a625020245040d42540c2c40600051b582c0f207c040719182007044030030070445403541c80d00400101c61500001078649880e000d9500340c0c032242040015010307188181c000c001117500441c100080c0c401514038032000c070303900001a0002c080b1010000049002e441446014908480680e0700303440c040100280c4244524410040104190408010555405100c060905c2500980a4001d031509407030007040c4982200459140c00c0c04400fa030840f800307500c141300820341800001044450759031321045a008001c5407400310fa07a446c0c00881040003000400b039504010010488100148007008584c4030310310907004591052900001514008104030b16010010b84080c1c04242084508070a0341c2c003d1038141c01440c244840039004640e1034000308400da03402010501c1580032000b01200741d0000d04881d9021710780d80c110720424004651b2610088900700328040142c206c04680c0400e540b90040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 688109640 1250 688108390 688108409
    0x10c051605160b0a0e040908120705070c1e050303120403030c140c010c09060c0b040609170307020a021e0306040b06010507120f03060509010b030415020c03070605040501050604050c04 81
    0x185040142c94038080d204150000b4281d004045902001d0078060104681c0755a10b44446110003410710096801003400100629400c4c13104840b050340b074000060b4091581e1a005003058040d40707036625844801e45c018000c40c951903d070441e400c00d04002000c0a003a00f45c0080d8541023040c40c03000c030b04440040010f003c00d0360313550025609a00c600f030840c0005808601040d141c24140070f05a00034400c2d25820700210b522b627000050054050850740e02016004a41c94000d641c50ba1104406441185400c85a4000a4aa0880980894010354081c028582c0200204203080c070611444040015548480300b10040d50040b01d540c0028000791300031350140c00e50445440307071001030303580740540c110040421940d5400c040b412a84032000240c00905690300b4040c807a924024802c1ca21020b0250f1203420000f000020081013200582030340c4800c01d070a005141094200d595429500142c0084418945900a110922100b4014581c00c44e508890404c00380c10588a051150702c254031810342003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 688110890 1250 688109640 688109677
    0xf010e1305010f11040f05031f021612020105190509102403030c051501030c1e0308210f060d02120f060c0a230313020f0a2402010c05 59
    0x10401d0079000702c2c141c44802003090200f14011035440d03055070802e0040c101038207a039000004082c40d0000e122943e02c204808101c0b550400390404601a60007143d000e002460f80e00324800006600000c820124186607000042e01c0c140005042150303d075401c1580304250501d01401a49180030450040210300c085000440401c516105803a481c8810010110103a00810003c107040d000300f4141c03c40380c17142c0f095a00da09641008038550803001c0c040944208e905107011f00460100032024581c0022408031800c000c0c0e943d84d10482d450344080750b1004050031141c140034100343e80550315a0000e82c1c503e440d81403864218040381050b008602c0180c0705e440400d0b100c211625043c00340840a48820080d40c0701460084028611507012411943c0010b100a00c40b400d41402c0b00c0c0c500810350100400b0a00c2c54841c0c420855048003810030036070740104800300e01002c2e83e64030500b00000703042600d25003044104c00701c02c014045111032850000d69041500c0740140e02c4d40b110486130380c0c88030b028400c050f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 688112140 1250 688110890 688110893
    0xa02160614090d2001090611030a0f02030d0f06090c090515090604180605010e0909070e07140d0e0f190605100b072103110d020304032f01050f010e13 66
    0x1281d002c5840984140c0350702d1440603040504c1c400c5130403045401e0b29010a016520001111428600d00c1c00c03850a402c1440391589440c412072035081203440390310407070f414606606019412101c0c09000700c80c025544813420032205000b4083c0d016008940d0520080c850300d01000314541e005581c1c0b00c140c0700e0000048644207951590140c50242c002d108507004640420714410b002401c50740200e81c08200f00001d95034075403805203100b41c8030b91001c0c800381c164140b810701c180c2c5e0501c901401600900c500c5601c845005141140941207606d800c07000494000c110341c10705820305240d400304101c0c03604800040d00c00302180d894100300d00da500c6000011241d45c0e80f8450100121907411103050482d0016405052000c04103403110f048286901801c5010010715041c1c00300d0310100f403445c1440c03000380100011000f007903001d035074018041e04000b80c4101c040c1542130703011a02c0f06641c0142070f05a10902501000920940381d2141d0242003080441d410054900c070041c10081002044c2040b541d038440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 688113390 1250 688112140 688112149
    0x323010b0a090f030302010203060a2709080f070c050f150a050f04050405040f030e0402040521010f050c03011503020405011b14060a0212060a03020603190b03120a0216061409 77
    0x140140f160b10034051100381ca0703140003800307580705a034441d02c24041d1450214560313804071407001510341c500c030302c030b80c0e41040704100030010b0440c4a03000c1d52110018170896002c1d140000c000c041191103044410000c0d801c000421555140302c4000900801c120b5640c801401240801c03103030a1001803d282c0c1d101d5048901c0d190b454411b135003001e500a402c081c02d000800180310078424441303200f61120340c1c0c0580d8050507c0101c3c011449000e82c00405400c40c20f810810488402580c1081c490012483d00d0502d880081600c01c107850020482400000400c400d1031600600e04848a25160940c42e052030080000c7c00c100d0a41814545407a201076003908201c244003000c0000c040c1281501d00302d107031408400d13009401410080d80c18440900c0000c25910304100c101c0d00341c9030f00070300302821911080980780400f40d80b020750b5040e455540c0c10140c400c1c1d03002c01665050a2140307001d203036204140030000b810052914011002d04810000a00ca215044102520b4241d1102d406035200d004200024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 688114640 1250 688113390 688113407
    0x250510110a1218300305060907030b0f010318080f040302091006090605030603210307090504110d0902030304080a0503091e030a1704121a0f250c08030a09030323010b0a 74
    0x4ca03841c4e01002c003814003940c1c040d0001c81c45440e048032107007007613620124254150b69009500c1c96224410071103100c119030007070340080c0c2c030130003403003104600a0229a9040c05a5020081f4010200b6002c1420421864100499503000b060100d00c015050300c0d01901500c1c0d0003584c0070f80028050040b00080c0182c84c20440b000140000d0301e42c1d43c070f04690703075040e00e03119070700076617400c0001040000c0c0401d003810940102c01150204404607460920700701c08a000034007500008a034140001c010020b003040c0300f00402c0720100c1c01007005d180d9940494041141940a100c050155641a1301d8211003507900854452011600903000c0100c0030001d414030302c5540320f6500071040c4c1c103240f210007600388031200d540d00701450748410001e1442c0d1280c110f8420000300032a40c0401e5030441250f0810102140e07020140e0003507150500c000035074020307599008250001c80b8480c03105955610070710b043c590305001c0c09054802107540c1e90360100c2c000394100018001401040a01c8200062a12000d03102d00c005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 688115890 1250 688114640 688114703
    0x30c12031e0c0b06060a090b0307051b0606180c07020d030201060503010908030117120a0309060b06030708040215160201050304170c031e250510110a1218 68
    0x2010340a4600304409404660b954200baa090041d003000104981410002c6690385d02d420344660003405e2510781c802d0000da00050024040001c217028107049503400714184122241070502030601407400034144071802c540c00b2800c0b151499400305209003241c00c042191405501a035503502850b000c1e09081e4090410b641c0015019840c0103e240305002c5200041d5060740c0b03140100d00b0076041d1041000307503034501c8101e03034030003c0f407040007295505030080c1e20441d09240708840c0031904440720000070303080b9081181c1800102d0350b044108004c51a100305c001d1071001200c00b04601380441a01c0034428800c00720750003418080000040780c240142e1081e90483c0c808146510760740e8a103010102074482d040006500c025032151320f103030b4924000c0350b41518502d079224129480c0c07154004954512000c100101030720b880c01b9840b04d40307135000120b005980c0780d400034010b03441e07031419200001405503001c0303020307450844d1174513540314980090003440d001c0743c0750013034109005500e0905d050982e06104290 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 688117140 1250 688115890 688115927
    0x60c020f0d021c05060606042709051f0c030510061b0c0b1b1b210610170c090103080901120509060f2d0c0913060915030c1203 56
    0x1c1c0f640340070800c4039103281c05445041520400d80f6101c080c02142c0c080c601031a988000c0c000f40880c500038951814501d6003810100102d403421071030b12918241600304107460f201c00c04425a090624855000b20000740203240b030100198940110150159030b428082c11040014440d5000f84215150540300b41003900502d0f0400c510796075050400d102d51000404100c0384000800703545490304041201030707060900040c0b0041000303042003045208251002614003500c0d0f281c68042078030504000d05803042a42c12081e506050410495070f52006492096085951083c074008200f80c882c02c62507030450b0b038442c814a454080480050b130750040c091801c805160b00d45400c100b5840400665107002e0038003122000d402c4c0e20780f044e00300d00b448084402054001da0400c4041c60b00f452500415510505050f6101d0800a1440c000b43d1010215140c1002461f2070300c90910200041c1c4c484d082003c00e6000c13101d40e045c0e2030340c0e42d000e0307604425208030103901c289240e5120a050007250903203c100e84964 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 688118390 1250 688117140 688117159
    0x5010932040b0303220b03010b030115090314060a0e010213050d06061203050d200702010f03270b1302150307090509090114012304050c0c0d120c0207060c020f0d02 72
    0x11404003002202580c0444a03d01703208000502c042008201c0c0d0580e60f82600742c0b8950703800c2a450020514455002a0400207614800808600307090014100120881c2c0603140d40e00b040308480003510280b4403605920b03403040081807015260500c40604440051318003640228040c10900b0042240e6806141600c40216450040541c070038014030403800200002c00c044d83d01d003140a4500c01c2058203581001000b00440000f6600071000241113825501d00490f00541100a41c9000f00d4084200c80341c4107010030b5244200320121152a510540d82d20141d000110b00340c000034030400303074500000d10716840000410710b444d00c2410028080c02c0c0141c51078855041c95248a4024030401a1324085681548008900520246214041091940c920811104640381004002c2034090610717074000744100401c03204984c060140805203005a141c0d4080d428642080006451440c0c001c8021500840028800b042e04078043d0b8400c250145c0d01554a805600c01080440c400c815000c0e50211044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 688119640 1250 688118390 688118407
    0x60409060203190c050304020f0f0d05070b0a1d030a0f030201240302010e01140910020f0a030f0f08010602150910090c05011403130b0c07081305010932040b0303 71
    0x250190044000740c94004c02c00b9080121086590740003e5800a502021040d06100145045020071000707600040a003480081d25507500342c1303000d1145c2d00c0b5901d401b90206080200a420040d445040032060b0498460749404100003034484503074040061117105020000c0c0b0a042c0300358400c461610604180d03014015000780c298a40035400d11040380082d8000070909007035445500c070707c44c1500390b254045051592080400400010088000e021032161040c8500d1012041002d070304880d009032a1030401c02914580180640c000c0d910407010f0068140040000da58002a00000032039280180b071144e841d0f03009180c1c10946426000110141010001000d1240c108958802c42e002621044004a240000d50000307000480702442054564101d48011514107046e065121007680016407070710889079610b162541000f0080c0e0f450f0106221b0a01007943c101001c80701401c420710704200b5000c3c8011000449075543c0c15681031414012a03410481d0303c031504074016a000042c00d494031214030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 688120890 1250 688119640 688119661
    0x6110c0619060b131401120f09020906030303070c08070f0f0c06020c0d11190f080304050103140405030a0c05071205031207140406050708040323060f010f0e060409060203 75
    0x40104841d00107160850014031000c24100329560040b02c160040f00761071808416501e08850300b16040d0610804a502c04050740080c440c00f41412500704001030001c0350781c010310100c9040201164042c2c1d004005001030b0a4016105402c542d034030413551581c40741d10349402543d5a4050200900045503218030404004080c107440d0705036003059003215503818030001000b551606246000c0e04405600200e80400d05182100c00e0009901005000350300369140d04003084207003158440c4410740c0020809005540e85401000031111903558001036504054a0f2561603120b40d212030000d0081201c5081c04020052000700300810045011000800a5003845600c0b5071100450001c0b0090100c00201d02c5405204180b6942840220983c10305007001c1084d00d241d40b0804042c1c80120b0213000002c0024861008620480b1160300c031440c90408503a80317a03281840c00340ca01c400e01b0740349000610000c00c1d503015000440c1e007000c0324a00b0b181c641704080f40c000c1c0103216025290760300000030000c0d100c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 688122140 1250 688120890 688120921
    0x6030c09010e031c0507051e2103150d1a0a09050111040807030308090c0a140f0a0305030a4d012a031d010b0a0504140406110c06 57
    0x3a200d81d90b942d88000100354076511800b0300c0d0032020300c4240c2c03031815440c41840074084140c0705104441b0188120601c101c01c8181c1c450b00705000303500c540301400d4091596240d070840401c6519a460941c00c00c03800514031a0340710240c03d0b000b48060104802403024000052080051040d0415010700305071101c1009405c103001c050b1455070800c80c0075030307000c585501264111f40c0c1d0380e030281048a0960b60110345c0b026020300184400e1043c00f201003442d544840402d801040c294840c007885802c2c00060001c81c0213800240c9208850030501040441d8012045901848292820002900c0021044403c4404000460486091408030204400f060028485004080600c0c9a42404c800c48185007038512144100000c454440b4060150204405010107035100340d00b0041078100c9588102a00d0000005c0085103d0391100304891050030100012000381c0b805a80521105068218100e1110800352000306000e583c0c032004000310342d5010580e10511400070641c1e015081050400e0891035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 688123390 1250 688122140 688122157
    0x161e0e220c110708071d0402180c0d0e03160305030901090f080405030124060309020a080f1506190b0306010c0507060302031905012301121508120909010e04080906030c 74
    0x880c0f02030110310b5000000705101210b003a0480105035140c0d00721001449080508201d03004076442c0c0c20301d056032a01d03120b2940300742e10248086441e401040d02c48002d4804100240d12150810084000007200b02c141d00c1d28425050b0074142d540b52200c680c0c440c01000140d4000d802c0100c10300c00141005a4080200100e40c0110001d202c403490841c003c0e065900301140c03c1228000c40c100c100140d0b4000e0f04008880d6000a0021284e140d895032030f5420509160700204254001c00300c1c1d86c04a8049030042a00500c00340e0f42c0400703102002c2c1d00703030395403503c00e001d190b40312180480080c00303580c07082c1000c040b29a80300b001e81d0890340c0e07106c6016001e1340094401142108003c0045c00f0b503030071640b041604882415004001001c00c030a0361840e0540384090707541c101300758280b100b154038806006514541109031a0800300601c1d06051505040f03140e00d40c501d140c00c08200c5118030740c1d10030140d2410340d5038107a02e0190b99140c0d442d018a0520984000a801440202c100641031040d40c01130017000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 688124640 1250 688123390 688123393
    0x516110a081b06040e040f030c0803090d090614041e0503190515040f080304030e0603070e0f190509100503010c082a220e161e0e220c11 60
    0x408542c4208403c80c0118020041254400000207010801002d01428250b01030704005140c02d015460b4030802d94012510000558000c600400100742c1c84401040105200d1400c100c1c0b98040810300b0070b4038482d500c10440c1002241c01041c500070200402c8900074040241124002403202c43c80c0e88540300003480945d454010060000c0d002102c0164441c41141c0c07100491300310881941d030f8104982c1004d003090313081001082c0150f002e07444035001540605156120100c3c1442c05408000080740307518051401503458a500d04240c00c0c006503640e041d0b81007100d009160303940300030148081c20407540c40769515600741405039000c07942010b0711500400d030070421040c109809101a0801c100040120741050134200420242e1091041140d070260031402d40c4101800c0c2e846000202000e826506140380c031111070203242d20a40c201040c0f44964440390f0250700c4860a404020303000c5030744d51601c40d000d00500b85010000d403405800005580c9000c0004000c4141405e030000d00740b120764000c84406 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 688125890 1250 688124640 688124683
    0xa1221020a1509030c140303061c120e0d0602070b18011505010806011715010215100b09062101140316090b0a030f05010902090a050402010516110a08 66
    0x81803000c101c41140e9600103030207181d040140c9000c07500921500e40240c0c100314000d60814005141c041010f115100400d004548905011041010a21199419601880400d0f1403200001c2480e040c61208048500300315150011160203d580710b1001d80000308207510016101d010061381e42a00b0740101d03170070610640315400e04505142295101c10030a056142001c2e004c10040d03100b0301d03429503c08010300d025032602140c880b02005d0001c0c00d0358040e071802c00b102d000510381c4d681045224801244168520300c50b0410051043c41020340e405440c01c050f10008802120343c032040c08031061041040c102a40300c281003005166240b40c03e005542c500c0c10b058841d81c80c18900010b14081e100141f940c4642054984503403040140214444aa005552148004080340789001c000c044e060042c030010903000118410800d80f044c1c0201401c2110f8644000e005c0541d83c41000c0da4007540c100c1c2802c450100c03607400e20a240e411b042c44410340c8600c1e0502d0200d00c3c0e010110702e540440b10100c072140320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 688127140 1250 688125890 688125953
    0x4080a03110c03070c0f06021e0c210c090f04120314130201080f010b040909110613181b1d030d0f110d0212070804030c0b030613050106050d0b0a12 65
    0x14000a030300ca43c1c001a488504244444165508092058040141107840e6009003a020603e41840e075180019076041e07541080300c614132f003441802410a012115507a061070300c1c0071900b080182c050000707421021145808460740d030082c0d010300070108480c891440645010542c1c603081e11802d820890006049030b001c2003600021800240c183c0304500307030311410305081c0b01d03290b8002d100307004040d02d200880745017000c883d4449a0007003c0703801c0032007001a842400d043c04007541d0a010443c0b001000d107400690034600200b480c00a407002c1a03850200d5050a0000d4408405000c40c02803075818018601c110500d9504085e800f004400c180d195010040c001c01000c9442d1091081010007503089200c8100b0440c0100b40141002e900c0380071210b00301a100d498003100414580c121501d64200081445220b150102c040d10016404420610a66040c4a4000d081c1d0250b10210101c190321848080304c1603903100da1880141107100d00940380c44400c0d090480c0701e5034040b5040b01c0e200382c1d03d00c800fa2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 688128390 1250 688127140 688127159
    0x30a053016031b030b01050403080f091e10030903120501080601051201021204020d020d1502031905100b1602040905010b01170129040506031303030c0c030804080a03110c03070c 78
    0x24100c80d02c2e80c0380c2603903d0403030980c01d41c0501165110b05040050410000c000900182c003c1e044d49050007007400e8440413901c0911003400c0c000181c01100b0340d01d14142e441c0603620280c0342c0a1800b01850b011801110614007907030750300c078140440d46c40c0a0a10001045603000058902d04076a4207c55401c40709113003600c100d080380300d40c6541c00380114a460001c2d0160038881d0020b07040c14401340910103440b216445010003152042501c4603400c0c2c0000c2441031001c42080c046502c4c8603c414200300d0b60a0080491070b56000512402c49869000706410210020b60016480708540280061041818034a482d40c000c00c6031b070b08240d0110718143c4a229102249041c1181a1071130310070001580603c014428440d00007412400301c4000c820000402c1d1902d40364003441c080c43c0c1c1c940c400040381a144c0f81c01380564040440c0303903040002460031071011941c48071415400981240e0459550744030035400320060030384000e020b02502800204084a800c0000007014014061040800b250362150100c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 688129496 1106 688128390 688128401
    0xb04030b1f03050c0f1819150e04062304060f0912020307020102101e0b060c07171c0806040513020901120c050a0503030a05301603 58
    0x1301c03d0b00b8120508604440d04803905085540c0e40d540c1e41e04210001450000601240c840e5034201490a0b8002c0c4914180342e1804000c540d181e01c0d80b032001003404d650446030716182c1200e8111000c4821402c920100101c44014059103480d200d44020300307546049101d030140d03180081000181003080e03070550407203541c0141d40c48815030f0001904208030380309515a65810031006102d07030200d014520b000c610030a900003071036420003004619a4000c00501d500b8521a0707507004034600d0504c0c1e070b80042002c5030404680511031909001d8113406803101e441c1c00030802080201c2d5032441e050b0812075002c01d4204050060180540000e90f0494081c0c0c0b0140504580b0b065a8003840561342c21180640001d40c1c2880c00e00d460a00426524421020013108000c0086844922090b499a14011440040601900d00000e402e100f9101001c1a0f90600803010b81e1460450602c5c02400354 = true := by decide +kernel

theorem cover : BRFrame.Cov 687949640 688129496 := by
  have h0 := BRFrame.cov_init 687949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 687949640 ≤ n) (h2 : n < 688129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
