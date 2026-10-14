-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2708
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:30:09.77051+00:00
-- url     : https://prove2.me/submissions/bd914e35-7bdf-4124-a4af-694468cafb6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 486870503 ≤ n < 487050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 486871753 1250 486870503 486870511
    0x40f03140a020906090a1d06010602150f07080711030f091e0a0b0c0a200108130503031302040603060f0b0108010503010902010c17041a070b010f061e11120c06 70
    0xd5214806040040c1d43d01880b060f403182c000d48408401e6140d0350790300c2c0c018040304c0d5100807a4038003103c1c2d8040a80e000082c154105e85840d42110b50380988050703a81203074603041d02c446184500c0c048c00981010f001d8101c59400c45624940356080202c14503000e429500800c0141218210006892000d85000074030107440070502108030100709507440008260303a2162003250040d072004140850700800074040d851178160408071542081c103520b42040480c3c0c00008909011030440d4000c01c032121035100388400c50300d901c01d0086107180c484c800e00062840200408907070140e12814007000050941c0900f5542200380030010800706032000014088480c140c001c80c1c040c1c2c1c5001c41d400d0140c3e130300c040760b251a41e81141010500c504540900003035803081b82c04c42c00e02442e01c081400e246040c03010081c420f160080701d02d004140d07224603080001030100c1c403403040000c50a0f880c2d808aa1a8101d2101e40071241e0300700f82000c480340b1000503080c04000d14200d503c2420100d140b40074001d05205490784 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 486873003 1250 486871753 486871793
    0x60a03050a05071b060c020118060e0105130803070804051e03090a150219060b09070503011a04060f120e010c050912032d040b07060b040f050405100e01060b040f03 72
    0x1d84c43da00c05151502d032103941020f41080c0c0c5070f544c1d042d0818000e500c00c8400703030070b07400c5100c140d81a24100003000d4410074608420946c0f802000401d101c00e5204000b104690101c5628515141c5400071215540090800e6805015115180c02c4d00d02035039052540c1d080b95080999122204042005040021948406003540450800d61150381d80801c003000104502c0c20058040c0300381d42044002002c40c14140b54015000c0c20030b000c1c00b41c0c3c02001841c122103400d006500ba055020882520a001e1440ba10703021070b030b80441c00486203005d01002d00c400318080b0340008602080b04541801d46000d280301d040424000201502241441e24118000c150300c1c5000714034050307515081c04440e64140e240980507807040e26418491070182821540240701031000359071103040d00e040640c018640403080030302c520300c0c01440340840316850140381c1c402d98101018044405541a000b0f0140c1100b91081546541c2c4507004181e20200001610141c0214295489114154500701d828440090710313a0395 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 486874253 1250 486873003 486873017
    0x40b01170c01210209060706020403151107030f0203091f020708070f060c0213110d050a09020d020112090f140d140d021b06040f0510180b060f060a03050a0507 70
    0x1c81c81c0d81114010162500b11108501c420111000403070080c0100800c80c1d83c040c2c000100f80c1c091029a40207002600c0c054904200401e039181350340c0e02119001310003e40b20103000d001401c00311380581c0700b03031a0f25801801941d1070310060000044e206075134038000c2c40a480310001d402000540c10001d000107000800010704829041116000411074144600310406c1000c2c04280110744400039230003c100c000c2c01060066440011080703c0c035400c00854141d01d46d1810300000d62140c0c140c0600800113070068107076004004680c004660038000343d49840b909545404446000498205800342c80c24041e20a118500e40c90070701c980d00700345400407040300f08440c0c0c1450142c83d00a1004880701c0308010754005a41e80180b001c558018590882c0c2540d0700e000c1c4070104020f100c503400c4520000d51180040e0364061606036280000c039800250b0185e88508400c851200007807021480e680c000e00c00500d003103484035082000550070b03030018261200080c2c0720b8062003040009802256002003603420890 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 486875503 1250 486874253 486874273
    0x30b041119020c060a02010c2604171902240402031213030c060201020a09090608070b0903010b030303070f08070311120714130602190f020d080f03040b0117 69
    0x40e0090045007940c07062600c002100600460007040850880e440180c1201d40b0b4419421001c1d009207c0c0802080c085013140030350901d0220280491258603400c948005000d403655268500c004010012072442040104140781d2017007001e0a040e01108450f078001c10341c200036000030350681010000030b95110b02002c028003005903004100e52074151060b80810780c4405207403220090b524440c0d800030b8000500d04034085003103541074008100c9000c043d180c50210966848100e01202d5051241c5150b54011480074441010900020407000b03c000300003003000c502040c00241990300a4801401050030411030a0450b40c0009249500c800b10b810204003081c01e07594525100d102d54618a06d0108a9400003503007140511440c100c804012250240c43c0d480d2688030f01c41e410500d0151001502c9124110500b10124801c0c412129501c601202c0d007000d030a90030701000026001d01100e030003000340a8640082da41c0c1d4007840c0304034003900d40464903515002501501c2c00e420b0f142c0b4911900603550b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 486876753 1250 486875503 486875531
    0x71a010302090c0a0c15050108061608150d02060f04061103030907150c0606030b0612061308090607050607031e0c020c060310030209010e0106030b0603160318021807030b04 76
    0xb19501100040b04196528000c0e2000c6035682114400103103a2151510480207070b000301d81c80f041c140d8103104101c0e01c494803071400a98000c800d00023124005190758000585144100c61515007400d0060f101c600300c050290b0028005820280740c01001d41c40c08141044510750184003615188100c401851540c10548452522000f1600840c0401c04480f00c0c1006254070803003d210300e0a401000070440341d0380703901d00100c01340801d0743c445101d030ba09400141c820107004911b9a010700c101e140c44482d07400260b66030240940102c214664029014007407440442e0051214500c118090369000400ca0300f0170a42046103170359030070320811861a10001520082d00080c2e40484010304481d001e40b0f036900c001d5042441c06c1c450b04025000b00c80301e00005007120301c0ca0584c034141e03901a00c052000e220800d092003120b000807201144115055403040c849907000b54818000c1c0f042a00a041c102c1d402030700441c180c0c20381501300d0f005501c070100c00c01034184c2c1e1501c540342c00010100ca05000c1030819181e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 486878003 1250 486876753 486876769
    0x316180603020702060c06130303110c060f092a010909050f19110705010203040b01090509070603091a15030c0616060f1b022113091805070b071a010302 67
    0x1500c060550002d14101555604ca0036600c90020207000c90345a0300c2d0018031100112000d010403030100c0e0900700f900d40e01400318400d54500c00003001c010b04566a0b06d02100112030005000e070308960040780d0110507403a650881000105600310b18002e12a60400c0004100001560080510310f103040244080b0141010349030b60007190300001040e042c804540500d008000101100100d01d100180d07110810106401440c4194011500b4200680e078503004007083d600704071100561600900b82c24001d40d07002354440c840c0b603030041901c1003103515000b4540c50300300000d41c8c200c01c92050a0003032a01602d020092030601000a407040c50905002415601c1800d010110003890982c03110311f014000342a070b9000d00040c1980c911581c44101c04942d0180d2a40c055209070107807400600c800328000ba1580c021550040c80200ca0100b105140c00c070700400070302d5000f0045e800c0084aa80c54000301c0c00c20031030100500909912255540882d1510f804c0600c6130300f110a012010345170040000da46d440031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 486879253 1250 486878003 486878009
    0x40e160603050f0609040201090807140f030102030906061c02033901020618010f050406061a04030b040303270602130812040317120108070f0806090615060408060c031618 75
    0x505e043e05440e14401681d201c1c8107600b040283c0e100340400025401c000030b08004640400f40e501003125410482072509034401200c1c0d500c290ba10060120340541030040007610540b4100340384160503082030703000905280802907600c0422a880384500041c0c074008201003000c102c80002c0414070101800040e45646009000c0b2101d40480c80c1c0c103010108003074201c05898603250b00100074074035052500f00002c12545c01120303c1102a024050040f02252044400340c0390050307d1640700d03135126507049015214058907140003440d000d5008010612040041c81228402e0001503111541480c20707c001030038560082500398080001148070070071413400c48003684d800549190601c18110342e00e56841c172481e44030301c1c1c2540c00034000280c0c441001c6150f01c00d40741c151001c040181e40d60070507603039207510a40b4009515040400454070f6002c500179802c03207040e0040e200341d080130755528200341845c00484681e00040000000c101540080e80782030310f00450641490701580a52001d441030600f1280 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 486880503 1250 486879253 486879259
    0xf01081602070f09020315010906090e0c091c1e0c090e010b2e0503060612041707150c020f100c0905102c03030a0507060b040e160603050f06 62
    0x1100300188500c00e006481c09019000582d842d0981d48501c860001e61003129040400a0f00b100d1401c5198420115030048501030b503203c01815081280c0707103002c414045d100d040301243c1040004202d850b400f12164004e2411001a41c007070384542481c07010001c010080c180c90400b18501c150001d100e900009084d0b40b2850800207828a01d45400d07401409185c4041c0d40c0038080b20403402d2441480702414001382150851030503040a2100182c41a01040c0c038410b0f4080000c1c00f400440814091629601c41d00501c008400c02c40003113079070b400c2c50703010002c19074800c072016800898400440c0035012101c400c52005024030300c1210b1350b454a4942800b00801c5081e155480c90071260b11072000705006c1d0100a03d110301003040c40d000502030041c403081c07200051a0305401c0c0070388001804440549000050051841e02c484c0304400ca9095100c802d048a070283d481103c070450351074500c03648000c02c4440000740f0300d200c4641d421540248207a800309003014107040800240d04941c01205401000035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 486881753 1250 486880503 486880531
    0xd02100e03070b1f05100f1202070b010e04120201111b15130218010602151b13080c0a03080a0e0607060603060203040b0a0515011d0907081b0f09060f130e010302010e0f0108 76
    0x1d231841c0d8002c0d100e03040014051103051000415100007130b038101801140300c5c422844e5109a072031016400d031003014909a1a0309400d00032000d807281d0210304e1210b2014a602610b95608841c000c1d250440000e65112001d0144028500e0860411002428030320090980c01c1e03040f0761604000950702c0c000304003580c3c1c0c8440b207800400d4009054810f608540f400e0f032032400ea11414202d5a80e1801c070214840c0748514030940340f025410b8240302c1c10300d9040e66000202c031841c11241103000d0b1828259048800d4000780c0c10407000010810a1007010302461148002503900d007818108105101c034080e101c1e000c081c1c81c100a100c5050046070180300c07803207003e0803c05005903000082000c07035415100b1054120388600c0c10401e00e00e601c604214414129040e484c980d8080c0300032048501d00036544580184d038810080c14030245090740c040c290100c8192425440e001410320001307420001641300d45036035000c06005004540c1c02100b0526105c41c2520200441120100006d046d000b000e001500c0ba5a10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 486883003 1250 486881753 486881777
    0x1d060f030109020715020414040c03050609040b07050c0a08040501090e07080a0c05040306020a0917070308070615080a08030a050f0609040312021605070510020d02100e03070b1f05100f 81
    0x241744201703000081d00c2d481c11500c0d603a031861b8005182c1903102606208500e400100c4941074001e1044600030728002e481d0451558a030b50b42c0741985440a000c21050050034031040c0c00020301000400c03410b81c4508580d5487e0361a19001408452094000b0075190060000300000d140d44544080d9020991600200b4046c40080c0182c0b0203210740e400180c5001d0000444022141e00003102d88200d500301000058044180c240d2191201d80600000305801020082840410b1442c0c000b420348000340c001c0c1d404a9991400c440b40740ca01c55420440700a0340120800c14102c2d0140b20301d592040e41001300f4442450480002111031800030002018009510510100502681c0c1514031100c20190070921440070341c1446644c0c0d860303d00c134840c800d0b15404000b885c0c0f03d00c081010100301169400400310300b010881c000c0302402003002c81d6400b5220038400c880c0401c4d0001c7c11103015542c0d41102c41080034075003900c120510159013055000e281c1d00c070001f02242d5800848010203109511f8444065030f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 486884253 1250 486883003 486883013
    0xa0305090f0d08030907170a0602030901140906090d0c11190308031e0c0c07170f060106030204080f010e060112060905061618050d080a030f0c1d060f0301090207 71
    0x40c07a11440d5000302800011008101e52000118052a0244200d42c15aa611610210003450401e90b41c009030700036000c10400514181c01035500a800e150010444282c40071075180315400880d188141903200001748464260207011035503861030745280203044545c450f1188140000000a60390096001050244600c4940009031010f56449404550f0341d0900c45000410710407807090b240f407000d071008040342250890a080b556102e0f80304014020403031601070f1460720740d904044000ea5500a0460718401000f0900800c2d010701120f44005071203a0401405524194540d200d0105580c03500708542c402c4940024020b044445d0040030104070f40d00c0e032400f1809450340d03901c000c146200300c0050085007406480c011304025000d0395242c0ba00e0507103608400141001e032183d01e800089880442c0c02056a010042c0b10985180c03c0128a101c240c4009500b00e40c140004440018483c2c01c10f100200341203920090701c1c4008032101390a0484585240348103100c18411840142c1c0c0c0043c00001304a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 486885503 1250 486884253 486884269
    0x106050a0314090c0f010206040c0b0c0304080303101401020313032301020706060312080f0a0504030c02030607031d01061a0d11040806042306040308040203030904111b0f0a030509 79
    0x4424403982d8801d401c110050564544011000c02c0c4103081c0d40303a10f10015440002e006214540003d40089018949090301c4059400081d9861b1107000400022440d004100019405010020034440703449103040c41780603d03003241801d00e904542041240c560f4840c1603000e800243c07500150041c510f02410b50035950b5800c181605443c4950000c04e0800c14840c0d9680564200d9000e21001280400c0c00c140c1103d0148080744e040e50001138090104022084541c02540d01a00c079040c1200d501070a078000910308102190203600081d2101c00320341c141c06020240209801d40c10000780002030800410744c85008010714015004103012502d0102d0300034a400216a14402c0c94419a4860707c511aa5032a008121001d4403000c3d0150104180e07030261841c20380c402c0346614080e1102e520f40e50340844a100c1b02500a07649403001b407002c4985a034030351040146011788031240c0d82da11510a10820442070301004800003a0b00044000c0d9011000890061041541460b04580d00c002110000f0040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 486886753 1250 486885503 486885521
    0x61b1209080718060609030c0e1e0903070c091a040b0f041b030c1d0103020a1404060c170702090118060819050c0a051c050c030a080702190605030106050a03 69
    0x900c40d0030b0340091099042e141c2142c8201da14041481000e07151041601e001c00e041c48010501c014505c001c226080d00074074940d4001c5201c0d101c14819080300c0c40e800b0450f503016035003258907420001e44130701041242c9c52541d000344100344c810302c509101500b07168860b290a2038094021600d4a181c542203903903e0310442001c01c0d000b0000c020410410048100000694000201181c68030444d80b0406000d19000c0b82c8130001e489445110300d6040004401a404c40e58910b8240007011070310711020443c0b00041c00261460b66181c80d40c1040364102030a24240f400100c018040081140c40d015894280d0b12905503000e169081c0003d48820310184020003481c0c1c041c5600c0d000c1d401c00729080106c80d0f4042c7d12018050403c40d5420380c400d5040103000b003194801c0507403007400c0302280800004842a05490303240240103039020702c2e40c040042824031305070030800c98400000107001c4003180741200700d10044c00c00c2140b02c03100b91400c0c12400381991206010b00c805204012030600c7c01e040c800c1e0012024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 486888003 1250 486886753 486886769
    0x219031e0b0a0314070611030f0a1b0606031b0b0906090f2e170f0a0506010e060f1e0c060103150204080f0f010501090b0f1e0a060513061b1209 63
    0x13250b400003003a15864140141e0001944e08040308011000000681d0404608812082c0c40e2010081c81998680700c200f00e1040d20f078840106000100e8030300d01c1268011030092000b0340543c0211001d00c152000325070007200150100b0311940d01c45440d00000d80b401103006640d0018410013031400500d9104594030703480c181c0780c0600b6070b00f040300e82c0300d4410341c031b8820346900c45a05906144c000256407070341c2100c44040100844c40007075400896a00b01035003118041c1008a184e1100700045075603503100341c000348842c000c001024205d03510300c076104000301804940d0582c20a1100509503407100418440905a21300040a800741070603a80d044400602101d411a0500c02650b08269103c0000c00300240c000c1d480c10000181407400ba001c0e188240c0d00017041c000ea814241400c100c025000c01a910203202a0b002c640400c541702c0009080103488141c0f960780c0c940d14803072100244e1484540081c410011040c04c0d5140e07003200b00c9040103006610030105680c0c00000300781112548100d90109007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 486889253 1250 486888003 486888023
    0x120912030109060503010c1418012c0f060a0203070b07050f1207030c0305270114010b0301080f0a11060d0f05150913030e01050309030405130219031e0b0a03 69
    0x165810290f110b041201e50541c001e00c5183d10321382c010b80d014215a040c050781c481c400c0140502400c810840340364021014140403404a01911015005090070300d1b4089000b509444100c00034030305041c1a5048000c1103440300e24040815400030340780d00403080001d280a00010204090324082c100307403000500c410241a480b417840417140e8454510580c1c015004c40c0c500840c52a40b20f00c01e00817148688041e84007840340a410002403044803451500c0340800355612154a0700b04400c1610307041c0201100110f003601d0b541824805800c0694040035003510b640142c40752400101803810030410110100d6201c0d031201d00248200020305040001e2860951401c804c226401620441c48118001c02791000003607075842139042c0e40049107800010b80814100c1442100c15880f940c0250342c8820341034182ca040665501c04110907990305070030741181d030b50080b403400d080e64200a11105010020f14040c000d1b043c0708580000090342c1440135684060f25803100030b9042e15803242d00001951300a04420b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 486890503 1250 486889253 486889259
    0x9070b0a030c1b05120a0e04090308071209030e010c031215061202041d040f170406141821100f0c050703050a0c06110c0a05211209120301 61
    0x20300400d80302c025400820b041e00503502400810189800e4a540e00c04000c00b000705241080525607088151040200303c2e00095101c0f82e40c03200e02801c001d4902c03a454a0601d800d100783e019101ca05402c0381c0003102880d01202d080031aa0050008030750a801782064841c1d0640e600b021141d003043c1035098204607080052407072941080d6841141268525a07410303107080d91060585081c4d20403803240c640c10700f5034400c042e1501c071501c903503c0f50840d02c1414208801d4251f036030b171656026101e5140c0984c014022900b0001d850b006440b0140c0313041c401c44414684200c07845040325255185130b03500d0103440344200c0c45d6494190300f241012480018000c441e46420b01c0c549039030180c2851103a00004a0030a105c040c0c1081c080d10941c0d141551617141c0d141050f1213240206e40c4495803400c2600d609032299040746001e0282e20042520501d880013a0070052000e0500381c0c0340000708031500e195400903040210082c480030b0190342403d00d00d110303200c0d9031751600e0b11003510308500c40d0403010324550000000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 486891753 1250 486890503 486890507
    0x8030a0906081b070b0709080610090f0e25090e0606030c040c020607030216080f091206060102031608040f0602030d060e04170304030c06020315011107081509070b0a 73
    0x40c801c94040d0b076210b0415a03a10401029146881802050544001c0c46044005000005c0c07242c1c0c4280d15282c503d4140e0754610b880c500d080e4040c3d9420b0500d26510710144034101c0c00b4000c0905149507060184641329001485035990090a034100c55801c42540d5100c0400da22120f0800081040c0c8074140030800050303d0103a25408150703152032103841490404d00490800340150308495189401030302c1955903c0b0b90030b6019501c2010260000e20803d012140002c981001400c9100e00101c20a5298a1180d00340011071281003001001c541c00f8034100110360307074004115050740d05200c099065541c2170346824682c50186800426141412030b00204080382d0000190000218030b52052000c60b554074220b2411100685002d170628000e5003189420385400310007990030500c41c5c03404038009226901c4640c201d801c1a1500401e44201c88072984041d0703400a0a00f245240c0f03100030300803144c0f900c000a90754101c00e000c0d4441c03100079103000500d101c81c1448044010000300c85207a94403070f00c00f03c2c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 486893003 1250 486891753 486891767
    0x30c03030d1505040603050606060f07080406031a0406050303030718030b07081e06150c03130b130b03010b0a181701050a05070806103504022b1b08030a 67
    0xc80412800b20100090307249030502031314003241d4002000c3d1a045d2945420b100095101454000d4141e8042003807000081491005000030181c43e60002500010346066007942580340700d18920035820410140301c551b42c00300031030782c01c1040c2d810682c1d03070300c44000403605907249a0307400608006000820000340d6600700c45050300c9514691042d87c00c44841e5546000700c00001d1310301c80d8105803064005c4800180c2e00000741200d0f04030740b04590038410381030400070521030181c210b210084e1011540c0001b021305402c1c1d280251141482003400c540c1060120500c070b00031081038030300b00200c41d6072100001c0108130360840a000d159140c0c9040b81c032080c08a5001e404282d410707a214528120004003180d20031107006002d0807000b07142102481c0b4400c405c0b540b0885100c00c00003007110020014082d441d00c160708550100b4491401d46c0c0da49403a004101d050030000030385001844000d245007403403d2500c0070040b80c141d480b0950241c100f103140c1e41500c0c1c21304c0d690407100c2507210000f6a10101900601 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 486894253 1250 486893003 486893021
    0x51e06180a0906051017010303051c020d0e1915020304020d020d0501050601021b100f020c0d2001030209130903031d0604020f0609130218030d120506010c0c0311030c03030d 76
    0x60022100c4002c000840700b1b60001401c0080c103454560060000a101e040141440c81250030100d18444500303110204a901c20080301b2195a0342c0ca19082d80c090092089140600690381c0b06d03844e4000503200d08900000005007140019130000001d4115500d684141c607a0f5074000c1d16001300c0003590b207000b0f802818247e46160140c0b00d84030310440304500002020f900e240028120a1810602d440c1c1a10094907030307140a01035024014045006445002005070f52078029800d20126001c410300c02e800c9500d03180d04150400d40100700e1003c0300d0305c400444030401080540d00080d400c20504044006140021240c02d0061700040c0c074047d012400141c00d8040c6008840c0030285c28090810450144070344a40f0503041001c69060320350418540c0d000d41780c0312414846102c800b1510314006401c0c8981500300381d000c00e141c104441d00080b243c1c80303001c0c0c0c00f1a0a00385003c18050f036440340c6400004034800100980c5ca0720080a2060310140507940c2c29010150440b034559444080000181200310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 486895503 1250 486894253 486894259
    0x203010b1b1f0b040608010c0e2b14160303092301020c06070204091202010e0f07080705040209061608030106020d08100e0402031501030b10051e06180a090605 70
    0x541c030003140804640c11000c00c000300c42c2c5004002000c0c500314054105000c0c041e90056541d031000581d000213010305c9140400c1a5503c03c1070030210800c120403240c610464101e51030710760207441900082c0e884000401a0030106452524418807003d51400342104009a0494040d0000004154010104e0001d8511710f10700904600084e055038096600180421401a0700c040c0071102c1c1c9003400d90007000003500192001c41c2d401c0c6540c69004001c0000400c02c03006030754594003c3d07101d0b1024045c031028000c030f21340a40002031502d804941d4400d40b601450384200e50000e0f80000390f5a07900100c94030b90900c10101811518035003401000c0d40c00034071400001d4000c10307690074800b070b210b00a80740c07003008042c04160b003460501ca403400542da4014400c9070907220f0a401d00024040e40100345000354030442c1d80c11805d01e0154415041c1c0640e03a402140101194003080b4000c0409070798401d0516019110300307440b44240341e01100551900c042443c1c00807000c90b00400c14507016000101a07030816 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 486896753 1250 486895503 486895537
    0x12010b1c0f080c1b0405040b01181d1015080606191503090c0b120f040201020123060f0f0117150406140f060c030a080405030d061d0105120d0302070203100203010b 72
    0x1400d00c8251b50301158000d00d0040300320018441d40e005036070b89604003c8100f1001403039251100000d11801c442c166140c20b02c1e40440340b403d0780320b20640a025150640031205101c2240340a0325295a80409818144204420b040c803110340c9000d0510a0010102c030300580c2d085200d1624040e00500a9140650b040328035981d0100f00359888a0803242080c031102803140041e0748540881948000c0a0002c0b4115502c84412080a40c81c002e1a56000501c9030310800302801c2100400440c10050010680190300001d00440d461b078104140c12420290b000e140c01c00b076a07810011201c48400c0011103588135181c6480031850a0301403682441d281c0c0d007524010381a008503030802c403d50144100d48000c1d40d0040240c010220b1003200ca1580052080c41220b007000b42c280300302c0c4d094601e80d07040000515100203078a8032014107070381c51a0060405031083c0c582c445c050b02c3d800e42c580d05444008018560005628011500c0800401120300c1016104648070b503122880f0010a40c00280150020162 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 486898003 1250 486896753 486896803
    0x160507120509031506060706090f0c170d02070605030c0a021f201303120c150b011e020d0309150204031407080102090d0f1a090c12010b1c0f080c 64
    0x1e00307440d50217824010506070174103c40350f031040040c1c405107030101c480718040191800050302801c40180a0721520700c03500c01d84400c00b00103510303041d0107110000440d4851242002130700c0d000b1049039000720144aa003a0760303080c1c0300410f920703140307170440c11038200781c10a244070410b02c00a900240050720035200c7d118076900c40400a410500588800504031204054100300080201c10310010070b12043c2403d98900d015a2101341604035022580021603440310128010380d03a10a4800352645580300345425240c1800e40300a56900301900d280090581d145490002e01c648240c10400f40c0303114240a560f00c9441c1d03e02039250311200300748120703248a4028003290310380e03040c0280d03512170101405e06d4500c14099110361000080d40d24050315809a23001da02281c03005401c8604c3d101c0c0d203d65000f001444140170a0044880303540004407401d03490404c44003810360b901525100e8807406450312402c1074019083c00e4014190595004001410001d035078804503202040d82d502c40c40030366115903000b0307503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 486899253 1250 486898003 486898033
    0x30e010e100509071d060103021b0105012303240a09061e0e0304060f030515040911100302090d0605270d021c0f0f0504090207050601030c05030d0816050712050903 72
    0x85c219a9204803502c030742000400c10f51080d4040c1c483c90110307038072142d070303140d03403034599500710f52081c3c001c003840541e0480003000e122001900c011507071100303400402810b001085042d6070010b9000d0203208c0d855100000c82d11302c1c0110341054803002d4100104000031266180f80c0030000b41c42140328040700b410700d00b214030010004025a01203c40715165003c0c0309002c0f43d41100103003401820608480200101125241c441d4856050498440e03240071941c1c085540802400b108829612020180104910300701d0b43c50b00f890f4804400ea1105001c506030701e131408074240310100140c2d149a1401211000c0c81114000070b01d541c4001100d40030746072500380c80284552040c01030072038000412030f98080e040d03030240701e45c03d80c0c2120207a031b1600f40d003403d48458144099078003403107084d58a81d204800500a0040e007444020003000218004c0c204091703038180141c081d0300c00620180e070b244810015241014001d01c2224803d56200200d5100c2154112002d001038010b0032030280244100400c00d500e2035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 486900503 1250 486899253 486899279
    0x12a034709040f1b03120302030a050604052a070204021201031e02060405010807140a0e010e120a08070c050303040e07022a0d0c03081204052506030e010e10050907 72
    0x2d80c00c200c0e55082030003035448400324041004050051080c03203640000108007903070000c0d526001c459401583d00d061154469050350b41c0034006034480c51a11090259481007039210490084141000021440180e41e0106080c0500d10019411600010707004013000c4c01044028140c0344200200c0c064a10380304e4a2102c130ba10b038203d000f90800fa081100303104642c0074010803644000c0f6454000f81e89011030b03000300c0c0b00b5001030081c1c0b0040350003044500070300d60301b10662054091050b00c0400d00b01150881c42076640b0720807540902144400925001030244030142c1e4006008080c048075034640e61581e4610313071384408850b80001401000d078039011540e80c80180c41400500546482c05a143d03800401880b07a0707240404443d608003130080080054a00b1014000901450582e0a15840c3c5803c0540c10030302e4880364110b0003c0d0f035280c9419060600c440304c400703880032460001007040d00c1c2503c080c014a0002c0c180c4103075102e110410071500600790009032050000781e050341c9940c2d0740d41035000311344 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 486901753 1250 486900503 486900511
    0x40f0603060303050405091302040e061012021f021e070509010b09030601260a110102060f041e02060708130f05040b01021e01090b0906040203012a034709 68
    0x80e104000810141c64031f2030085421032a05c240101011501d50300040c100d42040c440062150009130800c036121004200000052001070350380305804038a07600103458008034a00c0005424581c40103258914404c00c07180c41c0b8528804250a0420070b20304519070380d07025a1282074802c1225030000305000c1c40c2102914540100035000b0f1038164288007c1019541c501140304218044032040e001800008210203620240030b100a4501308507072000090902034028152a22644a0710501c00052a0305600b0f1411804007200061896428800540d42d8418900040c0104601040040e0b9225000d04100c0c1103c0b00140301101703440d40c80c401d110580705100c00030380c0560440c5004004460f09803500003000c003030441c00010310b40b41d10381c2c401d0071034a03098400c01100c2d8000e0b0200f108504003486802c488101c101d48091045100f0f0040700c01d61031400d107906003016140ca81c00c100248102c0d42e0310b2181d184036906820301c504260308184507030905900c408884510ba006004041c1400b41d00340e402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 486903003 1250 486901753 486901757
    0xf0d0c0c0501030905030d27140111130e040201120204090209120c01120207020d060207050a031205040b1501120f0b040b09102706060809011d0303011811040308040f0603060303 78
    0xe04c009040e84200030000000707031507180d00800880c210300d1041445023a4403d4800d20711008405050b50100b4210f40c0e404140d5800140708000784041c00c40c2e2800701c1011180c0c0c2d40300c507440ca90303260310040350b51803641d40d406001d250001c14003140340360752034010b06000c0b0340a6402c0084004151400344e95644010102d5010542c00401903405901540050911a0011780980180c180c5962104100c1e880318500b511070f030704480116003c050b40101c10700041c9280480901c61400c0c6610303461000d0320060180100030405200584869029030150b070608002040b0810407813810403411000303000580280f0344103900d041980b0081d403030041d420034040c4481001c0d0000250800010350703000004940d804510301015803101c0c6101c0418000c02026042507074500816003804202503007914030074070403c410000b125160440b010000429a41140c20760310002554007c0380480400030500045001d0002100103000b03c18450003d008008603003580501c812a966165401c5003141d880b8080100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 486904253 1250 486903003 486903007
    0x100804030f050901020109050f06270c060d1b110f150711150c070c05061206040b0a031b080708060910020d0b06130305070501030c0507020409050f0d0c0c050103090503 74
    0x140718481c0740580b5286a041c00000f80359811a20741d10f243c81c1d0034030440700c400d5111004210303406c45580501c1c85d40001c0d100d550b1291510785409180c84865100d18a4060000843c40034540e02c526001450380140304246c01c00300007210000104440020201030b00e17288140000300c009001c0014440c03500d46426a907860035911443c01c101e40e850101908174040d403041d804914143c150064100380203030440350025031360f85024039240c804600184d22052240405010008518488000342c0e40d00c00b40c21500000c0d29140c180001d02540319541010300340e10700390100c01500030801410401500c942074204c0790125034a4600541e03c4c1e0080b0703104800c0f6048442c40d403902c0000d0f234018000c42d020500004c120b00b9207800c0440c4c650b82041c107507403212454800041003840001c0c421000944800c0c41c00f8480c13040e20322400780180c4110b01000340a256503d0100c800e00c502408401d110700704c00300698040007040c2000418800300903400361902c96510400041a6020703226520202e58014003541c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 486905503 1250 486904253 486904277
    0xb01050f060d0b06120709060905010906051e0d021606110301051e040221070909050c07140106081203160314010302060307180b0c0f0106140603071209030e10080403 73
    0x1402c1d150f000f80b030f000340b01440500b6038903000030481489401c041d5500103030030b403810b840146140740b00c1c1d100304d06208481c00c050000d2a40502150030f034001c2c40c2060401d0741d4146c480c0d2078031445003400c845481413010500040020781c1070300302490507000c0d20051010904142541e80c0e148400e120741c6a206041c81121100368404032510709141200800060408c00315005d541e2036030025282134410324040030304104100b600306200202070442000200001d14202004145074407903031101071310302601c034084050100310940100c00541001416603101040ca402c240c1718a0308281c4080c1c110245401c15400b1881c840c0c45100c99060b00740031840d000c1d03461602403180560002d0880d13010410b42441c6c0002c05042100218001c1141d04880f40d60b624000b0780d45400c100d00502509110b90410b64108814860107200794050001110000d5490329944d1040d24000000c1c800305070240e050101c02001d2681003803500d01c0c45401500c50642900111804450300c0c2400c4800401158080b4440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 486906753 1250 486905503 486905527
    0x5060910030f03030207020d0b01030212070b1e0c0f0c0a0b0a0207050f06130305030301090e010b0f1005040f0e0a0606030c0816020f060109053306340b01050f06 71
    0x242c0b1079a400b0341401450301c005900070a107554402d01082d02c481c4c0d9244010011800c01044202d00d141130080a0f000f0075003000c3c40411284140d104a654030340740901180030000c0c50703800319080708540c0d80c2210114003c0d20207403130329452149080b5110704000305000546000000455042d0a00c5501600a4a080ca420007592508108800e904086c052024602c0c40700900d0408020b180a40d0003940c0340d601d41407500b000c0d612411400310311a410305136250410380b110300d0001204602121a85500c015070003046409000310761141d140c10100b032500085000c0002c3d10300303014003510881403003501c0e00c80c0002e5080d00c0c12600450300140b84c1c4800100d00412141d03d8507041d16081c03054442c6070416003d00c40c9410020303006035054036070f52800e0002d02c1861442c0c10384014200200c1000c900c88070001c4244403102c440110340a4900000e01111056103011b20860806607076480c49030161742c10354891042c41141c03d041740c00103841000421a40b820842645801c6801000d481c9000c05003606 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 486908003 1250 486906753 486906773
    0x8031e0a030902120f100209030c10020a0816061b020a0f02040b030709052502060a051e04060905150c0403060b0406080d0c0611040b03150a080318040506091003 71
    0x1011081503500c168100c016030790140c40800413000c080041c40851a02da0050f030602c810ba043d80000d0900c10440181151000715417a0b6000c4002c4509600701e0140810076420503000c203c00501b91040003c0d1000b1100c29140700c01c0c1f845000f00420030001926070869240e20fa1031046010151344481072400c0041e50b010070541e200da1000d00081a810b100d0750129162103c2904021074494540d410069801c403041d40030803000c9044d012081542a854101030344507030010741495806030b2500005440701050008140448070045194055440d160500c04002d240c0d02c2e100700c440740104241d95040500d40c1c0781c3e44d405991000c00c282d24041c079517554480100110022990802e4882d600001c020005100024400b40181c9402d084203400c0e14081d0100d80301640041e00c910010300c02840304040304401c1d80e90010b00482ca40b40d140407410b00260009402d07030f016104601c000645d800c80c501031b0f80c0c114841c0c6941910305201544855003048002d4000703e82000c141c0d8040f4108101203403003901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 486909253 1250 486908003 486908017
    0x60c14240a2003151201060e0603010903090302100c0b01030f140d08070c141516080f06010507020d05060925210c0b0414281512060314010608031e 65
    0xc9011348204075102003280549651403100c81c59540fa0717010061001e03495401d561100048000700801d800e07680d0040c2c4002c5003400041e0082c8804d51411003840d000c1c01020b000c0c62380004002489607524508081b030803100200c100c0c0d1900716509808a100000680440c14488a441e0301d56255590181100c417407201880980d81420618a2091a0b50051001034a070f2134000b40070b001c00740340100420350401c03526402d61041000e42c0e030030000c24291200003590040780034a071903a5103064500010b000380d12902d07800b800c0c80c06401c062001e540300c009142d0800280a403918600e5403405488000a031207941300b490310000301060000e1240001d9050454218480c10754003450f40e8030340e0420941904250010b041c1c0505100700141c4600e8492038100c03510180c0800c1c0c20000c80d0018180007400350701d02c00c410701108905130f0b07150000e00a0f400c1d00d802403011042009076594074200070f411802140b1040c01d00d54031305440400c0104d000b004845d64001401c10712103504030014a9000d141d80050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 486910503 1250 486909253 486909271
    0x6011707090b040e060f03151b190f020607030c020304050613080601080c0114070f110303090315180327030102040911030609070810060c14240a2003 66
    0x2041c4000d0242c060301c0503180d0301c00c1d1041c440c50680705001103800321161040c800d1307120004040d582c09074214025030105050201c4040c901c80c101d692190340c080d400301a0800007030640c0e04800325601201c074018040b40c0c0d900b20340f003d40b507000083d002c0320040030103400160402c000503c07223400d08400401034110000c003d140016034070021242000002e030410820f64101e03130342c0c1041940e88a0b0850003c10302c803020b000e02d055465612000c014081f00d100400c2d007210468824950784e0140140d0b40d440b440901a00c10000258a450082040c100c861680c1c034000e544040c0d1101c000081038034500030b0100b404410342c860000c4000d10f41110003544070360543d020000400e100c90b040c0110200116100102626401c10780d04010080c0c02c0188490100040070080041d01100d44269000322221410100d502195034140800c100c1200c20242d0110f114959000b204450610303503043d075940c0204206502274449405c080181c0d0300d111520304101b103207031000001e203035421802150426100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 486911753 1250 486910503 486910517
    0x6090c0305010c0c12080106050a0c0303060e0705130b0903120d1808031e041502070305071a01030308150303030105310204060f051204031b06050103210806011707 72
    0x10303a0303580d8250342400501c3c00c0080c0784d8505034010403d1401c1c500c6400d24040c00c0124140d8100a002003050160885000c02c10490307108540c1454041c1d48950058600d404403e1400d02d0015030241803a0301c82000034500001500c0b002440300e47c40c005440118100802038001c41408140034155900604034862890b0f86c0da0b9400301c0484001803025466502c9007000e0742d101d280c01043e04c400c81310b03503600c500c0b00e0742642c00c00c210010b11111074080140308030781c000603201c108a0804450a000c2c8010040c400c179074403508554441d1840440034101c034071a5464a0840e41e6550030942140e2029408540503842840180b0552400ca050036500c0402d800c140c1445003007081c281d04031269142c04101a143d40050140802c6921003110518451b8134209240740c100d0540c06015911001440034040084202e041c0d210072010080e100d071442d4011009001658603410712010180d5512581d018241d1404140d42d0041d0040b50014401d0350140c403606c1007401d0031030075a010584010f00b135400300580 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 486913003 1250 486911753 486911759
    0x40302090619060c120806010906080a0b0d050f070503150402240307080f01050d02031f1506080109050109050c090d020f0a0611070b07050304140f180604050a05010f0306090c 77
    0x1495a0b600000e14507966210078020240c1012184c0c01d0901940208100840d010019640d0700015011704036400d52414a4840d540c2c070f00c490b8000c0034041002503212121003450018450005501d220508110f02600c202c103585070101540e440181d0a180c21145032500001d0140c40c045108414100950150b10b8a4101341d14140c0103d80c0215503110100f440d40083c418018003e85100c7d0140c0307000d44401880c80340c5600000e075075003a441c0d0315956000e0341900462840070320350060701c082c1300d020180124094482e0380281c4107003804d015940000f40b501000240039812800f031940500c884600c0c2c5450187ca4005003c41201c0b9030300180e07000b050303d62440034991a2680560010560340da65403032103052070100389042c0038040e8801180d9241c14405080032078404400ca43c1103842d503180c00520050a035001c90056100c0320500e41d406121440c0c9407500920400010348101000c80d0100030940c0e80121080071074400780588030b0841503412040c400a080c50f406511600d004070001c4a841d55 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 486914253 1250 486913003 486913039
    0xa0e0f1519031410020f07061a060406080403110a0f0b0403020111160201020606030a11010f110106030b2d0c090f0a06030b01080c040e36070501020d03020f0403020906 74
    0x381c0b0380c811038000c604003640140550080c0042c0d07480041003038043d4607080070b049401c00c0c00d00a0010103041c41d55191070b803160031f01082e14882c0d8446c0303000c1e00c5d0326102c0d0380d02c91000d409414121011790104484181c41c40c0180c00c0400c0c8055955449001541800d80c0c50b02c42c0c1d4844040100b00300c0541d0740c2c49004034a0003a00d074018090070b600040d821070030620709100090038254050425070096012072190b0300040c00e024043c040c41e90081c42e014030740c00945141114140c11100380b40c0340d80d5182a01c00700a201155500610070300003a40050f58080a4203070b1035201340801c910395940080c40c000411040300104c001004a500c0081c0030741c928410f001c0000305400907642c01180400c0d80c401d182c50403542c120740c0c0b0a9010040000d00307401d0520b0600c2003100e40e50010000c05844440d02d0700c001c144403500c0c00840c0f840101c01c0221090f0300c0000503150303903a2824051140035110701c4941c02d000c02d10a0088a00c0b2500b445400341c00d05180d0390038411541c1014001651041b000a81c51100d25 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 486915503 1250 486914253 486914299
    0x31401080f0c010806061204230102180d021f03020c030c0f060f09031e071407060e0a061b03090b1606060f0b071202100e060103020a0e0f15 62
    0x824004060107449880003095072602d6040c181d8a818003032944200104c1ea5a6030302558480818002014900d5917607190030500d4541010b510017280120035215094040c05501600000c2001c01042019211079000c221205420410007540070441a190000c0030401c940620078176031243c00c0250074080641c8800303013140c101c17110010942e030112100610210303081240a410a40a0303410705039a0800c81c00da25140c0c883c2040305802e603d16009070030a201c8001d0200c80f0415000f1941640c00c040d5603542da61100c0c090700c84d450006414000000082c40c1c030480060481e4042c1e19640e900744040c3c00311008420310880103500b80000c0b003400113990180040181080305110714a4603c920007440c00c2011513100b50029005170140f11802e120800d0743e43c04031640075800503840102c05d0b204007000c0b0f20b0005884054281c181c00c0030701d61266a1030020b41c4034140c030310071508072034081c1c0c40e040c0100070700004940302c83c0311450310400705e502083e039228034031203181700034001454514214040040d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 486916753 1250 486915503 486915509
    0x912071205031c0203041a0402210604050c01030e0d110304090905100501060212040b034f1109090a08120114040c1d040902300a0206120403031401 65
    0x9410010f101c2104440c0c408182044107100c180860550030035844591042480345055000c00c00c0c80e0003c1015991260420417050034149100d4019950b0401e10703548586060700d040300e892043d0484001c81d580240074030150840c5030002801c0c1600408811074019035001900800d6010030480422698240d001e400d420501400c002c04805400781d00c9081100d40513402001150082518000140180c9080720211650f0380806070b241c0d180c60844691000f03121400d800034030203290b09800c006100c420020040c0106094041d92581d102480564031b081e000401000580e014210920a141c28441a40c1110040e012a0308488880d9100c42581d0700c0715414580107200400108001c40000c000201a4003060b5014403801c3c88501d07006c0c21a03030251002c0c0e0714900c1c1140d070f00300f40c54072aa440302c0300140e00104101d100c42002e800000100154940040d8020704040703466112040c0006c01d080010b5010300580d10b015801e0320400b80090010340201c0c2003686881c85510240c003268001406 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 486918003 1250 486916753 486916763
    0x2a030903090306090312010303050a02010216140c01092603250b011508150f06030a020307200d030b040b0d030e03010606090e0406090303020f04091401050604050609120712 76
    0x25030321141d4101803409000034143c81c00c6074800c11101d8071090007160003504607030b41410099107444107013100f64064082e85101c02a0900914851020300c030300e80443d040c1d200490416a040202944011502000380b80600c42c031100000d01028184210307030303a205001603032100a076810324500322904402c2580c103484407110340c1030280b0060240302c5a1840a40108010310245912081c640340c007411100c030007044a81c440410140c04100703a2aa80c0e062228000c0041c0086d91ba032616070031250080d0415500000012002090102d1484608446072a501d42c50001080c070b03014824001c41c050881d00103055000390f00e4102c400d40c82d86801c1d20011070030748079803102407000c8003210925003110241d92004081100b042c00410440c51030406440d04544c001d04081014042810140c02a10482c80c1035210031400180000b0040090341c014440c1d065130f02c80305182a44d0b81c8040101c240254010301d070340164104106034103458076400500c0d40a84031302c00c0d154400e84d02c0345404024070f189001920 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 486919253 1250 486918003 486918007
    0x1a070c170f0618061302011202041d0c070309090216060603210e0a0e0903040b04061d0f1008041a0901020a0816080105130608100e10142a030903 64
    0x10484040c0a02c0c0d0380403181c0b4043c02c01d030601100368590703924006020151590140002e08042da44581e0b22a880000081401d41d80d80382d441192100320380f1a07002d0301e40f6807445a000304401c500380030221303981560165101401c007420702e1a41c034000e600401c00303810109106414400081c0365405075000235801000c020340005c0340340b005d0540351500103002004104c0000340580b01640e6a84d0301c84141c07103e90030000003540d16030040a00c0c40c85140c0019501e004080b40020740c0320391002821425800136040c2080018410f414004042c24180700b01e9442803070a0100d6958038070039540c8aa2045c002c00405400303081c0c1c0044c2c81c80340b4100b070f111f900c1d00c1d9400080382c03403542d03070840207041d008040c070341002c2c3e1824120f0300002c102c2e15060198074030070701c0c8a961106903018240c00c4140500208000d4803000780103808072070020090b1501c8903005000c0c002d44240b08552a03c5230001603030754521614655900c1e4544607000300ea01c0c000f40030720000b442c4c66020441001c50051072107075081c580115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 486920503 1250 486919253 486919273
    0x3020d0c0f0e1f0e03030702040e010c0f0503010f05010c03020a020a0f17070302031005270d111906020a0c08030406050405150c0d090c1d0a151a070c17 67
    0x811490006251a0040c555800d500303030000c41c80f0110a807445154900569407140c4100000e08511405401950050800b4848095480b041d80a00a000400c0d05c444404501544080e07925000901c94641c1440c1944010403072940a650551a0359101e881951805c0005600081ca920400c1d005490000001ca5041c41152900701c84418075150600003040c2040ca5a0300007960364100030610701c01982c80310f000c00c000c034041450004081800c4800380040701400149281d8907482c0200040004501c580320394120003010624030040d540d040d042030100200313500d90101a5010001030020003144220a00214052001640c0a144100400b043c81c0c20181007851500b1056911541c00c82e00e941c09000f64004104e00b20f8040120404000c110012a42402e8119252a900c01d440c0340b2841c0001450122400320310620a141240e4100411034172000d9030f0300c0d124202d00414030354210707065910510001101c09094002c3c4a1802c0301c0c8565101c480c1444a200100f50030122a4040ca13811 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 486921753 1250 486920503 486920507
    0x3100905070c150b010c0519020f040504110127170706050c060a091e03020f0114101703090301090c061704080f0a0915020c03010e060105031c03020d0c0f 68
    0x41a0401c203545808489141641c980d00c0940001542c01d516060383c0b45401400c90b40100304101b19150481300762840000004810340f80c4a03440d0b02d0892041924107034035980351400d807040d10700440d0800c2c0c01140e00d070f0040c1d0040d207143c404c0440b80006442c034150800a5a0126407031080645160040d4040745034843c001d40386401030740c0d0411414044180031a203402000060040e42c005030803240480c40082a05143d0151a5015080141c10200201d503205141e0005400c181da5905c280081203050105500300300301c100b050f1104103190980da08204940028102d0a280240d034500942c2d20380301c00600001d0854082d0481212006103050b020071105c4c2c0c018040e81d06090628031805550b151680d01c0c88918071a80c40a44400354001c030b801e12042d8410070340603024080346009180d030442c0c0c0710b002940d106c4885002521a40c2020448081020085406030498070094001c207420500000003003540300c0c080c4480703c2050b90a1102685282c03884c05040d003a5071454680201e5101d00c4400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 486923003 1250 486921753 486921761
    0x127020a050406031e080c0a29010f150314040b0609070206010806012102210c040608030306012003041d16140310050a0b041d0708061e06031009 64
    0x100500c9145051000c0000c074078081d41084085005c2c0030700d401100202e02d00f0b01c0c100e0003019142400c500c1341511500420251680f108040090002022010700d510b203450000440240a0000b41104c01c99040000b0072100c0807000003c2d0740390034045031900d820404146044030481c1d096503018600300620182d402c10703c0c6445d4200381644054112981885017803640c804041c0320b10b08800c07a00104c250051094dc1e82488561580108120700d4058149200b281000440d0b0890045000e10000d6000f185004d2060100300d80e602c138091401e50f5504001500c21246466501c80c100384000000c8800400500042018012064141d80d451920004170300c10f66100511004643d25003c01c1005541d40107907906940c01c494070303040c6a480d40e6403013640b04001201d1344071580081c408a00410200e0104000e00155618540c600d03045008802c01e810207090f0503108c00d40412500d0021034203904011444004505c1d480e401040f0b4514800c02040c0705900071100011100c002c3d80c2c05216581507400b07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 486924253 1250 486923003 486923009
    0x1030b011704022103031320010e0402030c0c030418180b040209090c040606020f06090c010801031712071805060f180a0308130815010f06030507020127020a 69
    0x40d24101c0e00d0800c5081c0400500c000c0c1010303220b24210816480d030844141102600411144141d80e202d00f8505a840d000d8042c0180807944a8075400c60418140d82c005444072102d0340c146e6803a240301900c0c0051000035400a003242145030300820080740820400c10040008107009003d00f400303903e40c008140103c4409000406500003004e144002140c00006040e4001e0340465410200c2d40700c0c1c0c00600e190044c0103012580190030503600041030b03034010170003103803494580003a0b0302c0a1703407200829a2105560104da03400706131500c0042c00400c401c490328403080d180b00700480b880c040c807180001c0f9100d0750850b0454001901850800b18011503407580d00300402060350310320309200d0b4117001d281c3c590068805001d80c5080c920150324055490b00c0361000119040081c05640389810480d0b406114550701910609200d40182800e25404064540c2e04031118020020b00d01420a2802c50181002900352011507407564082510f20000442c007544502c1d07c05c0108600c010584144010b039051a8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 486925503 1250 486924253 486924257
    0xe0a05010510050904021c060605042309011e050415090b030f030912150108030a17090d031113140f0f030c0103050414060115030516020d08060a090f05010501030b01 73
    0x304000c04903e80100648030400812500941ca450100e010000700d150140d84600c0c03801d003030181c00182c06404c00d0040c02510180003607400d04004c912484034040c1b20624245800810f0300c0c0c010007042c04444d0081c01c9116a484080c1d000d00d41d075500007410341d22031000780b603903900c441c00d82008442d056204034003600303030103070040e122406000c0c600f04e450780079103204180990380e00000320701c0c0c82e07106015003003100441500320802561030f4041103581e600141030320703404500140034030030000720036000132442035181c2001010060301843c0101d01800803060501c03004101403243c9440c46410344020009003240301c291100341c403e484c04101350410904170b0036010b55144428a24203803004640c4100041003801c0104003901c86150071a06d185401d00b01607818044c00001280551007118024074182ca2135030107018640b150700b5110f0000901c2c0c404500580d0042d02000601405401d1480d44284003c01c1c000c0a15070350b44215040d24001103003200314556074801030107150b0b0148929200c108080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 486926753 1250 486925503 486925519
    0xa080a08100501080601080103081c02043c060507080426070b070f02060703020705090a050a05010b0933040e0a0f060503070905090a02061206030d0224090a050105010e0a050105 78
    0x17040060007400041c0005081c9140c0021301d0401d040c0c0d110303501c880c9041c1d0404210341e500d66176101e481600b9a112515004551b0385402d0625001d481400303864003513089a142e10580e454006d040c0d98903888010b00325580d4400b4000044d11154490b04600c0e001d50002454905015600c5907904240c4242c1100c60444424041070b804140d4403a41e0b0820350398165001c96942d1914202603240c0403041d4400e039800201c520800c9401780c02c60b008075004801001e02817090b0303600c0c2c8100014a00640f0b00e003d8000400115085002c50740310004914040b2136902d070300c02641940560842c1d607200e5086214804841c4007401074584440c826071040c0d00c1540010000d080c14280041d07115411841010800c544910116543d42c4e804d010310003800b44c0c0100351644d2080080e0018802d26001c0300c482c0e01c41c5c001c0103c0300404900100f804400c8444642c40d040d101455203a82200141004d0b2840480388039811070351001030000d12441e400b130412841004480c0ca003061100c1e007901d4050b08214029880 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 486928003 1250 486926753 486926761
    0x909030c1c180e041b290d181b1202090a0902060f0a0206010b04060c0305180415090b190522090605060319020306131a15150711060c0a080a0810050108 67
    0x40c0c54449645070240c803520074900700d111b01c0400c518003070039801401e20341c5010f5039030b4008080e211403072109610a1a00340450101c0c0f8141c080000d1203481038030700030403503c1d00c11401480e0121483c1e030b01071400b4200003544109a00490510381002d81c07030900c46040090f0b0140c840b030b01005400d0044c81200041071615040c558000c00081c81d0220007401d0000104465100307010002ea810b0b4010700c00341003040b00211084d00d00c0000308aa225405280745056503c0b6114106241d48405942c5880d401c1100caa2401c0f00740400a049981d030312203c1540301d006054003002900804c80017a000d0070000c40d04d07003800800c043c1011340001c04100d41d54102003180d0700503100412440e0340f103502040caa4501c0086410148038090000d1342d050342c001c07028000c020400f481d0240034109132005880c14403074801c103030380c00000c0b91007031010103440c642601c064401d1034500300009000303003081c103819643c0e188034036942c402550b085401c000d030108498a00700408501d520680d10b00524091904a04c5424 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 486929253 1250 486928003 486928019
    0x912050309040e0709020705030703110312180f01020d02070b0717270d110d1d09040809130b0f042a02011b0306050909030c1c180e041b 60
    0x10501ca00640190703143c140316006030100340810340043c103507900159550719203490079903180da01180c002c4020500024860440300000000c0c1d070440b5a6040030406c0c0c0d91203c6001007000c0740700d448842018842c1c0f010044050034280080c040750a031800c2c001d6100c0d6558506000b80c140010250000c001c825000407481c05902c00c1c015030041502d202000c80030386440d0071030b2426004541115030612039100c07158885a4051042d940f21602c00054583c5249255821200300041640c07810518005031702840007460551402504a48100c201b00d02d01200500801c0116002d41c0000030055a6601a0441130400c21404000c190003168200800041c2030340c1e0302e025141c4019a5a5017039046d18075141002c0c000d5011400300d510004101c0303581c060848004001d0f00340c40c000d0a024414000c04543c82d0100003040e02ca048007002c018003550485a03520b58480b6132024007440030001090f8005c074403168903000120140031000300200c03091406040801c030300c00803410603180c6811840c6081204c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 486930503 1250 486929253 486929257
    0x402120a020603180a0b1323030d0e0c122a011d012709060f03030c0213090204060b0304031e02061f0f08010506030706020a031202071509030e0109120503 68
    0x40f86036860380b0b915509a03138801303203000f0300b40b00020119000f0341e0501c5229000708003040c1da014410298600c01d410176030300b545004210f26030070b02c0345507206100d19214518103806c14175000411078105e440b030540d4400018640c2c41e2010802c0c2c0d454110280280d011540961103c0d002c10313041816041042880c00020000b421070158a60103000c480d0415550f030b0320403494907845520600511180c000703544084801101140704240100740741c1200080c0030b400c400d440d0000c803034068950598074041c40d0280300d81244a113424516490756004080300513555442074801078800001b000c1d45901d41403802400201441c0e2517000348281c03600d00481c0d40c65000804035440021141900c2e10340310248881c54042035150490f000c0807540060100b456441544200d12503042101101ea459030358450136030300c80100b22400380010b618a03c119003c03490b903400030203c46100d801000081c41180f002601116980d5000314005408118803440715a8040103980180005480305a44a41c150b95001d903a4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 486931753 1250 486930503 486930511
    0x330402060405040929011502060615090102100f0204050a0501051305041a06071217011d040c0308120109150b030f0402010903020d0b0a1a010815190603050402120a020603 75
    0x59500da0341101c0805c0300b04842102256042070b14140310080d444030300041d4060902a104500b4402e96100c01c0341480002c0083c050320001c0c1096481300121a140c50290b0700c204080c0341584904003109010100c20301c21281000071900780181c0303c500340410800c1d42005031388440e040010502002c00020310002c40c0c641154822240061301202511111010b030a085000c503900c81c40118450090141c042404c2021601c2650f40c50240102801b89000d258000c0c0598003554000d008582c190100e8070b0001074105000e0f40801804590384d5450390200c0c3e200c1021000024a20b00041220104900680781f0441c00015140841c0d4205011001c141c00700034041588803004502207420359005d4490103000d1500a00390340202d12080c1460300c00d0b807000356244801030303140c14041083c1211542c00200c910105a444140c0c40d125040c103202280c01c906803044d80301240914000642e40c0c8649000000c150584010525250500400c00c20b00f042c3c0d0442c0d102900400300c01e40050b03507104c00302c0ea0701c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 486933003 1250 486931753 486931759
    0x1021e071e05100e06100504020a0210050c09120c0f0109080c0105071a01230306040b1303021e010b13110901080a1107141c0915020f330402060405 65
    0x340000d9410042c0c07826000509103111286858010f8100d0900402d41c1c51003154560700c402a443d84c7c40052008030300c96007001c080181c00400c050f155481c40c9030880b9400040325407005050400080000c0e0303802600860b152199070044608040342d080c020360906403460309080c003440321441d0920741912154840183d80c1040000941c0303500700b260a906020b803603046041c50150940e1121031342c0451074010f03030304450300c0d840c240c2050b8254580000c03804c0c49207600050b003d0240e00c411040c00600144403008809501411450507207103044c03d880e00b070889014100205250305a0b40600030003051044410741e03201c3c14502d1051031000d0601c102c481041007841d02c4549590341008440040202d60f030b146040b44c9000507007105006206020340320319002d002c141d0f01010990ba14a0414080404240010503030805040281c04444d0001c07000480160041c4d41c18800008005030820041d600340f0301140a4078404c4100c109110100c81c8400c410380c00a0b14082c0c103058001542600651054901c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 486934253 1250 486933003 486933053
    0x1a0c1509101509060602010e101b03020306010507060507020d110609030a0e1201150302040f0b03100b0d0c03051606080c030103020d0c1d1b252301021e07 68
    0x94441c6807450b031000500340d031003042194540b80e080c001e002c1d01404030a00c5071032007201380f800da00d54040c0c0704003401c40381c001030080d001e001c2130704065001e50030013045035060000500c40c000108825005161047c0101d85c094403004110010107021016455204503a40c0d10030b130b0410021359000401c5409004075070070001d07540c40b0004001060b6004074400c02c04654207004a4017880380302c551000342030302e200312814400c0b41c0210102c10202c1e0081c0c03031708591560002011300c0f13040d05554089002e40c80081c1003041d817070441d92501c0e260b1f0101944100d92aa003d80143d0554040a00341d00d00034002e28549600d1506240300000c40f940010f00000e032045948080c80000c0002e1040940c004042c2c000100c800d0002e0110b003c01550000c6505600ca0307110750b2403030f400c505025400c40d03a0512101880c904482e40c071142010b440302070740c0c0044651180d4218115090b4503440c14141c968805800007580d03441c0c1003818052003420242d108a81c819050080c2000a00c450f041501580100740b0904 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 486935503 1250 486934253 486934271
    0x605040206090604150e06180d060b0409030504030b0604061a030a020d05130201110c03070b07050f0f030c010f09030c0b0a0f0c050403211b0c1a0c150910 68
    0x608075101c0c0003031060340702c0d0000a00040d444100744c800f41c078050315601c81801a0b40c0710800d200c2d00d889508610003901c0051403070101c1074030341100c10507401801840001440ca10001c0850b0444d41484c005070040f6402041c01c001b0001c280380070b640d01030300944003072140358603250041c0b05500000c04502c0303039018080005042240140c0c1600c40c00c501840050155091000e20680342c80e0100030140e000460003901411151000941c403c0780d0b0308050014501d49241080c442c0a5400010b01169540210000320940c2d80e420031020109020140c0990365030080b420300c8a084034001411503903c94140890a00841e4101c5514101c04d17810000c8514540d0320400d4241c01014502c00c030100c011329080c15528050760110191003500d201d10984680c10702c0e40040008225140300400d000038450b52060180c8039102ea641508952054489241c1ca548885081d0043d04456228500688010808a50795042041003c403003002d9000440d14a04004d0074007925256030358495545603031180d4001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 486936753 1250 486935503 486935509
    0x1002071506032f0306010f05010e030615040c020c04050f0601120504080f22030b010f0f0e0106050702010908070b0706050105040506010e01030e15090106030303200a2604151d060406050402 83
    0x1440f9000300142030302d40c6580c6070710b26602d040000e8014580040d00007842002d25042c0090154051884c1480da56030400c80d660030480503200c1c5640e07010443c001c900c003d445640380c1b40510345c02081078a00340055460210001054020300312072400f2040e081c0400d0002140d84882120031001c4805010b558481c0500308021140c10800646001c03400f1140000050048e0001458181c8010100e11140c0d03644e0f400c045000700025000742080c44080000410005004500a105091060400704100f42e583d0311418103040722503201428907500003038002d042080c2441387c94003400040ba402c02490a103000024403908500b01d40d141816501c080041d0400e20410a0309400d9890300c07003000062034002c1106010f015107100c114042401e0192440148000b8100c0c1e1841c4848913409604103130030807500300e402c000d0340304140c03c01018401c2a0901148407a000384c0c4101c2c0540c6004009100c0f01c00ba42d42190000c0e043d80700d1104a519081c010202c0200c3d03102c1e0410381045000c40c494440f4000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 486938003 1250 486936753 486936833
    0xb070e150306100e1003090501050901060501090b030402241903020c030306091f0b07020a052202030c120a020c060c04120605040c0503010504050f010e0601150f0e03100207150603 79
    0xd5417040030114200e15035581768215604032031142d0002d004907110080c0a5081e20710301d008403404242c2e004828403591001c1e8003d198842d000034007003c040044c8213030000e0001c1840c0c01920a170400040e80208904030899003012903081458118501180081e001e500ca010141030b00317109d2040c65010850030402008d80c0041502c01c29030f0381c080f80359100441c044544c8405c0c01280150205c031400109031611142e4510080b035004180c0c02c0c0c04c69490000d0000354030080510150345010700c024080c48201c110340e0303441742c800c00d10016520b010201d855464401c00801c1c6120b00d5000b000280141d0740a002980e0080c1d0340300300003140356145d030b1800b8407040700345400181e05903190500700000d004001806080f221003c0f0020000d01d010710f05842d480c0c8200340200f1644170581482c10751120b115130904c03078192081746400b40c9283c00f201c00003828409016210815660003051020511a01c010103001d408080301003003054500d1580c40802d500070340030321829a0f1500601042e841184140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 486939253 1250 486938003 486938027
    0x3020f010515010905060a0f050307030207050a03110f0c0a0510020a080d05010e07020a120c03030b0d0305031e091504050a0c12140c090115050c01090b070e15030610 73
    0xd00892800d02d0003095a92400c1c545140001c00050000405060450884000414580d611004000b9420040e206944054507410425508201c080c000c1241030040c0c2104501c039a45000c410403000301c1c1c851034203070a47c80c280c031250010710031000c25039248940041190020f0f42c1110f6103100580c03050b4140340d441c02005d0091a00044d02591601d145e0f402181078600c2101c2c05242900c1d070080403a0b0714416080000c00c00226410000741982c020310b0204000c80c072030729000c80c4030b90302500030410b10004840110b0100c2d80104c01d1140064404060410003c20108103c40914143c2e0f4031039501d4102207410094032040c0e02c00b19045c403500788110b40d02c09402056140307a1903650b41d035480c7c29002c0400d040d03a0004000c820000d2100700401c3c43c07404010010f0010350740c0d13401c210350140522804074580041c00030402001c1a440307002c0c05064000c43c01203206002c07600e8400030207040749604000203072140f15040d900000300b03450241500d4004400303581c40861102451020350310399500e41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 486940503 1250 486939253 486939283
    0x2b12020f06090c040c0206040b0a020904020409020a1206060c03052d13030b0705040518060301020903100603020906090c0322060e010504050c010503090703200d032003041802070302 80
    0x5410880100400074404900700f0301914100444040d0301c4040f600d6074420b0750000e09820f801000310341c00049a402900c0800f1008000500c0d00c6d66031049030080b83e204a0702c41001c24401c03041d442012916111b07000040802d804c011043c00782d15640106140f01d070303141070144e11500c461300803002036252500e442002c52040c0d10564030603409107520400b075118807049a611300c8240025186e14803c2c400daa080720005003201c1903000a006060034400e600a2801d0303010343d400d019480c01507500308520b0010786202031000540034103600601135528001072205000e201000d042c01294860041180d6019800800304018400c141e104410103815041e1302406042c1803141c4103111000640c485409140316200301e8030400c40050043d07645000489076111150450001000424100280086011242c480c210007003011355000814100e0b070001b013036002842c3c012101110143ca408070392018118403000b90704191038002a054040c0c000c081c044140c039004162041054002c10030a803515540f5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 486941753 1250 486940503 486940513
    0xc070c0b0318120f0903100c0302070b13022101180b0f1303200307080d0207050613020306040204090317040b0a060518060d0c0f03030e2b12020f 64
    0x640c108021a042551488030048030102a80c42141000400004001682c000c69040460704d40c444006034010020741c1d80c00d801400e800c942c50101c0d500c5074001c224110f40700184c0729001c60902001b10308000340b05560141d01020580d0141c1c1e69494012000c61b0144030b00b5001080901d00d240c0500710042d03041c075000146a04400c00c010a0500b41032103102016803166060f0f880c6580000d440071300400281c04074604407008441d030303110309900700c004030480300480345003030700d943c0d1940030307541c404a0203458540c0e000c81d48400f00401440050741098801c08003403030789141c0c2d8000035101c60300504003d106596032400c440c10903002e02c410701407560022210298a2402d03041507510341e0f600700c41801c0c0c1549404800f141c240351007a1803000030591001c06894070f81d500750a1024050b00420180c91a007048a40081c0c0b0240c4083c1c0d60f4055442a034402d4030007030241040c05441c4010ba00c4076061100200800d1400107296011550041e4004034440ba007110b082500340c2c100000b1034078082c013070b01070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 486943003 1250 486941753 486941759
    0x161d0a1503080708270a031b1a220f260604030c0507080a080403060b0609031c02070b090d121b0308040b010b0c06010909060b1003140c040f06080c070c 67
    0x70800291082c040c034151071305c02519001c0302d10150b09244d000c9056003d503040c502400850185007091241c001e0030400903841da601e440300745140c001c0050004020302400940801c0c071141c19110342d2084003030121002d0281c0d00340a0602d083d140c140c026540051910600e081355010b030b40415229911584041d0b803c0c07401c090400070140c509034001510b6a2040d0f440000c2d050900080140c041c82d040b04886080904641e905009040c802190f958803950501449140355030034401042a01070310500c0902c0d81510740806400c2c00140d42c803140640d8414022224a0b8444404c0580060380c440c0da100c024100c00c0b60103940518280c41140700d5100c54250b0a800c1603000b0151a0043c1d010302d141102680c1e03690b840742440d01caa40a04a0b158001170300400403d1140e410030300c000387c400e4901103000040c1034041584003035022007210000e40c1b0b8090142d0355030080d822070f5810210344810185083d0030842d640c05200321a10502040160790000100308195060580d41c13805e40c040418003a25035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 486944253 1250 486943003 486943013
    0x6060b03060a0f1401230f07060b030105010302010903110a090204090c0e0d0816260a03050709080d1407080721020304050d230d02161d0a15030807 65
    0x208880c1107002c2d010444010460080d03010301e0302c046a040d04c1100009801d00c00046905554084640d060558039003e00b21181000d02c0142c01c81402040c0c0860310b90308a820729505803030303644209502a03403403d0012710150340e00c00940303029039801030001c580c10240312000c102c603491650701c5003c0d402c1c80418042090f08540e08651032000c2c0c941d85101c48600b036201007040035101c020005043c4c04040261025019200000c10507450182c2910340c184a55a000b50751070004501800708023800006190304100e4051081940101281c900440514208409195550903c40d0a1424040c40501d0341c405005081c00b101c0b402c2c0e6004100c0e0340c80d0f46481c58030040444590900039045c02c8030b2000300c44800e10001c00e0b1f4044801c010700c00c240c0004280c0742e11064401d4801900c1032030010102c000c410600400910752080d4565009104031b1006064512041485400580c070790f04005100c1d501505858808070340140c2e4500c03002a6150100104031103462441d40010b25070400844c42e07405000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 486945503 1250 486944253 486944257
    0xb0a05190e040b03030421020105041203030203010f06050c1e07081207050111030c0301140d060c09030b01080a0c2c01060306140a0b0712050c070803030a0f0501180902010c06060b 79
    0x40c9081c0c405106101002c01099200d000c3c5000308650f12880302c05611f2504925074113600181e0060501e00c2c5000c0d11859003140c20b107008082580840d8001004020791040075288100901c02071812604040522811544412001c444c038212072101c000d030086900001d10100e0000d0555008840000c40c1e40b010340001900b0008040e1800c1d444d22580711003820401c4100c0b842030303221901c09031640e07090008d4450780009500c500c07078020b8180020750000a8642c4601d400e05c00c1180c50b1244854035603e0141c40c04c000c140c000c04015048040604001001c0061800c00d4034a03c40c0503041c001141000703800352510501c2010041a9844000988a505980500c0650303040c440280c3c1ca40d10a18248035000c0d07214810802100003c01017030000c601c034142c0b0f015014115103842460704001c1c1c0030342c501e4100e4940010700c8942002091008803980e82c881d000c1154089071051029614100041d01000481400c400d43d098032140c1c0710003160b1060440740300844c0c1c041e0007000015200c0070441900d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 486946753 1250 486945503 486945527
    0x20010e070e0f0a020313060c0905300309060d0e0f01062d06090303030f0b030714010210050618040807050601090e010f05270c03120310060f090b0a0519 67
    0x300d04007001044182019000712441400301b01d44800c1800328640e642401082d5581840c400c102201e00c01040c40c1d61881b0140c20012607a40c500c40020003c5000c10004004081200c50650f000300b141034400d842e20301c2030751101c108140300060070328445400765050114070009102154680500490074100303001c0e61802c1402c00780345104036880c404a2101c054600c900a84010403922030302000004d1094008252460907580c0200303008a411010038034150b00c941004c1c40404011105d0040c650341001080c00c015061a010b01041c1800000b2901404042420034030502c1d040c2c2c0020f051042d0f6804540803a50b01101b00e0707215603503c203003180050000c0140c00e0b1040d400c2c85c0480d012011580201801800441410202c1c2000c50703030755243c4c0c90300340907014090f8026042203031071564080c80b510416012203100a1781d24608600c0d03015090344030b60850030910415011560314143c0c465008001d581c440104183e685c5410a0161003d020b400c150340d4a0f20003d05d0f82c91800c56110202e0302c04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 486948003 1250 486946753 486946771
    0x3060c070507060c0317070c020d0c0918080708031b070f0c0b0304030801050f0a03141b031501090504060b031c0f140f09011407110f1020010e070e 65
    0x40c1c071640c08442c0c050345144c000d4002060003042031030075045100070039000700c12400e060580784142d43c0420500c10740010107642020300b40c14200060002400742c0c00040c010803d804864500580e80c80d030387ca000f07488010b001c2c640044006002104545504041c5440e000c130300700d45400240c0360010013240c04504c11260504072082c00103407440d500c02607a0103113905845070170a5a0805040c00840300550048507070000d44034070004041401c060b940b003041c0c44118094080300003102c10301c1c1d500c003001a000d98000ea01104898503034039138001d4440c0c10b43e0070751000418251a6810503002030201042c2c0580d05004800d10502120408003a11100100c55200c0e81c0015060a409943c140520500b0014000040003044081d000c8103000300482d1368141894040f07405096a052825004420100c901d071602c00342c2c2c40305600e03050003640202c03241141c1d41340101303580200c024102c01c440b000510b0508005031a29403412020342200c010f0451401c121a001070340c503491440c50080959000358 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 486949253 1250 486948003 486948013
    0x91109040b060a050d0312330e010f05060403150209060c060402150c070b0309070f08030a020c1909090501060306050a09111008181213061b1e0206040503060c0705 72
    0x9494240307898030445c0305401d5168a08400703041800074000d09140411884400c5820b000a01d42c4c02c0c110301404c582a0001d4001140c290810450b9081404182c10800c040d2410070340c200890740c0d44008580540f0761003000e100059880d007030f11134064002c22150315807100c00456008429040020100d11683c000c03a0b0200c920700542e0f03820a80ac4c4245d01c071100302500b0000b0300340242c4e01c0f070400950300080228200c0c0c0e03080f5a100f4510041142c107400c40c0826810000b665511260304000302c11040350304484100310b02090a110142003100c0d803081c003081c80d444058610602800b03600100c002d50f0409002d01041c5010510307800107011002048402094007e4041e41e075080200080400d1620741d00d8054050302d40c900604009240081201c4a1b4469290744200103d628001b03440c1c8e60460b451055081c80c1131100c080d240390611106464100502845540414403a0748101414000744062150022080c0003103000303880742d41c0141f0703014400c070002e02005207080c0700185040c5011f00141d0b6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 486950503 1250 486949253 486949259
    0x41b1a0a03050f061302091215040525060c02030c1002010f061409010608060d170d113903130e01061103090108102430091109040b060a 60
    0x203d0406810f03514950800c0700c0e2013214088000030741c0203080692000389144014000e0a80d81450f01104461644558142409120802c6810020000e24000d594810200c42c02c03143d05c045898905417180c181007008808401080d5201441407100d030000107070611610440c441c1c0041d002e0400f88100d40c20742d510b42200050101c41c12036260381d140800030300a84940c1d103800c00464100034094034995020380744011140000c0c29620510600568030082903441350314905001044940c0340306000c4001e0410403100e0366010162200089411000c901c24950880744034158605503800c0d200c2c40e005110016030180a6106030321842c00301d5000c0c4000341590ba8a07904200c4000340080c2034503110350300910400c06c0c90760003140305650040c036070210005520b41c3c410300b034541d25500209990482c40c0703005480c00d00aa0041c034225401481c0a611000c1c00c6003180340c01c500401c1d01c0341c002c01084d0b54401b40410443d2818000ea1301c40001080c190007424941030013802d100041d00c046205071000c003000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 486951753 1250 486950503 486950521
    0x60906010c02060706020901050f0703120b09010522020c010c02030d1d15060d0b04030c03090510090504050408040e07180e060f100207260c1206041b1a0a0305 70
    0x185032581d010b0416070400c0034559a0070302a401c64011503061100c01e1140305401000ac80203005898040c2e9940408420003890913800c81d18181081c41c0105680c0c801031149482c0c440c2ca101000141545024101241019100081c051f9201c107548a50901280a202d16400405490005080b4800b0440c501400c0c0b1041500940f000200001303420003110316011508104009030300c010050a032482c0e848480d607a500c52070a04650807004035404507292814143e0000c00c010140c0342c141c500f60342454070348101602360010b030710031180b04544a2000804228000c8280c400502d010386404486040104014009411280300a00b041c04020030008a10080c3c6102e00d0044401814046608000105100c049440f035480c010661095050000b12501c0400d0140081881994a02103000780b01400710b080c40702c0242d0041c425070306100d185080b000e000c03402c070342c00a13884a0031740c58010212896103083c0c3d0b0158000c10941c030080000400741c184c130310010850410941c0c1c0c01c111030741c5c0e0300329a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 486953003 1250 486951753 486951767
    0x30f040f150222092c0f030406032703140a0318030e010216240507050706080108150412050705151603050601020303130b06030c0604030807050607020d1205070504080a0b06090601 79
    0x81004000d01017500d2219454000415105070301200003922014801d80c045c1078176650255002600003955404d0340d5400041503589000da00c6081400c0c0d0107058156200202112390803035041d02101310001d80210030030702940c88012407a0303c140a0982d0f210903030401411320b5141c00744031409400384002c40c0d50a2690103541206032490f01642d00305a00e4401d2600140700e0f4619243d1090107030400400340880c030100070890050080b5500c0c0c058940c14080b205041c0042046a000481c220f0b405010028500741d0400103a11064908540c4a1415040185c42d118001d04c4c40246898000180500907504503940020462161018850b507141c1d80300485ea00c0c802100c2480082902c3c0d5881000100a08882c540204000301250350500c0303c040028501e0744103a0007101c0d4100001144010031406100312540000340380003910038420011800740005140d0000340601e40c1d540e500081d0314600407800d40300a030040c3c0c801c0b0703035442e41c180c5001480e141090710980c1c4600412000500740350b22402c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 486954253 1250 486953003 486953021
    0x20f0a0608070c0309081f1a010203272214011202010c03020c04020d0f0b061c09030318030201020c060c09210c1221030f040f15022209 60
    0x280780c0c4026619a4400c890321603007800d0890170004003450025030b00c0e00800014140c415183c5060140c28090444501151030507229501c0504640000c0102d50303030040180da40c2400640c0c11650b030803546a0010414140080090351301c04c44061b0411601c02c14a9403007040520320340e0f03081200c149000f0541c200400300740b0690030300540d0301c0d01e080019407045004040540c8640104d03141075840c0800a0280c0c0c1000d180e50071080c1d03681845804c0c0d003940d0b0040c1018141c01780c0391289881c400300034000362107803024403120b400d07611000001c00b0503112707501c9401c0c52120708454404240541c90024041c0d8000321038a4244c3c46241c0c0802c52185c4180215007840000912004801b6120f41c00000070403110010041380d4080c19500c7ca00c01c0d2190501e030350480026101034052114a42480c80111008580e1080b10520601c20424101205920540c000f41c10800c00a5000203034a0301000801c00113507011009400030410110300c242481301c060801c1c03210816000082d803525850801c481e0454 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 486955503 1250 486954253 486954257
    0xb0303090f040209010201090b280b0906010f11150109050a0e030a12090503070b0108070f030203030f0c0118260705070302210604080913020a020d050f070b01080703020f0a06 77
    0x148091040b490294020180c1c804103000100e40c103034442d160380c6d06c5d00700c00b10f0b0500d01080307510419050760310314030b0b25046e1440025003042003802102800f10b040c00030001d0000d4180724401035a9035802c0d000e00042c1c6805c2c1e0b401401c85540d140c01c507150000c600020301c2380b00b034854240400301d50f00b08203d018006203d00220300440c10611042d508850700c4440d49140c009181c1c0d10305501010500c144003c00032140a142150700035454070415600c0c049080c0e2180c1c80f01c1004020620042e07030080220341044c0d10b0f4620b50340d21204009081401494440714900850381c00507400300400c0007608104c01c100f42400200701c40300b104c005800480780b080d981c000b010b54115030030600041c60a030303d0348644403101745031504440d40c4583c640703031030800700345c800b9512080040303803e2182d480c040910f06035444003100190f04113a03101f000a55500d072103a00302d20600402051010840f02a20240d400c0713107801032086002d551b9108088d903121102c5000c242d001314000100c0b00c40c82d0034402c150718102d911039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 486956753 1250 486955503 486955519
    0x60e01140c100605060711010810051e0a050108040f0303090809100c020307061b02042007050f071a032806060302090405010906121410052e06090509091216060b030309 74
    0x1f080116081400202031840060071f44902003110b4460b80e03140a150503620306030301e44914041c0200045c6101d03560040d41008441070800000440c0480c24007403a42c1c1c1030030081025281441e001c01c190284910031034100c1c1d40391000462040e0b11585902d541802074040e00c0c040c80c2c81c1c1d1742c11201810341c500383c10b802c034420701c00d20001814298003210702c56810303600141d80040c00c0881086076a00483c42618180d00880e509002d0760b100b40031840c0204a04d9491400c1c1000b1b00c2309d112a103010003800d5500d81e00300c000032403040c00c0404144103110441d4100801c219500c2c0d1070003030001d401504609015525000000c030b03044555106a20960f00c0850030303180d28024a40e6282c02c00f4802d9903010126006045800c04500058080c41e03010311005140301d0340d110034600b82803c1c1c0542e840348000140100b000100b01550f0401c1c200c409491003074900381440d941e00900203140403da01112080f9010005008680c08800f51441c42e89238803841d4144103c08504041507624060035502c26401181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 486958003 1250 486956753 486956783
    0x6080105070509011d09070809010e03070b0408030601111009140c031906200a0e010e0609040c0504080f01021306020102040503030a0c14070602010605030c010810060e01140c1006050607 82
    0x2c01503255481170744410400d441564202150380004103a40310400311340c00d08184249442c00b8044c049050000c0c9000310b0818489031039000e814540900003520502c1c00001107485039114035264082403083c042140d42e0320b07054817201e82c010083c1080c1521300441d402c0384104841c101051409500324001c0050940d03645006c0200320000c2015808c07640c0995442c20680000030f4041400040c2c90056851078482c2141a4050070008842242c14108202400b5081d40f5503942026a0b500700425200001c1c80c10482106a0743d921650700465402d2081003001d034a40c070415002021810080d14101c2d860a40d60071059083c1c3c000e5004a51b4981c000f404110761080c0f03c4c42c1d0800300c544c041c40c00d03503e80300c3e80700c01c40700d04000180c2c10000050351900414091030404015800800b4000e2038981c5003031914403a00d0050b160303d8080e0908000ca1240b6545544e80b0400180c90302c0d01407103811a03034424404da54182da82000810030002c00d03081420003d4240381880540c0c5819401c81640120060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 486959253 1250 486958003 486958007
    0x140903101a130e06063106030b06061303060506010c060207080a02150103050a060c0909230c040f030b060301290a060504061b0309090606080a0605060a02121809070f030608010507050901 82
    0x1b41c0b1503407942c4000329266440e104000c429014000e1524440016905040d07040021031120002d000601903030007000001c40744868400984d013269000000081c0360740751080100c440e6241c541026200c140041921020701450341c008103180c004035001c070380080d5403052103188144000d12001c1d0007a0001400d500210b070b19a08124403d06191810800d015217079100c0c0811102118000d075152000e906c0e2110000d000c560075542c101603040c1030701341010b1800040d04103411190100030720b04c040441c041006a02c094000507059665801d6240c1d1045004401003070081c2001c1e001c1e07100c1e90b403820000407018000d508540c150707803d9560f1080d0b0f01845528090600e403038504124100100054000b64514083c0325000c003034282c1c1e94134100c0605110303c040702661100e40246101e1502084003440994000883d0041042060fa2143d220f01207481d20300004483c004405401400c103000b00404d10360f001d195508095800c0c4c404000c101d4945800608852007242c0000119108005001c4958 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 486960503 1250 486959253 486959269
    0x10602070e040605130b070f083702040b16030305010614040510020f011a0f0a062a02041a01120c09050d050a0507080109120f140903101a130e0606 65
    0x100910400c9907550006686da032020180458102c0000b903651400150036981c40568030b40c11007040c505018802946004565442c130201d114400c02c2d401c40120080341c1105030701039400a0281002031901d5181e001003182210040c40382c200c0009140a0021580e03034001d2507051707624103035000c03040c0c00d00341080188441501404445402d43c4510490701d41091001d01030481103002290085090981e69400e216443c1d0305121030030301c20302a0b20010b0207019840004011508004039110242c02d914060340901c101c082e00d0080d400c03d06100405031404510358502c2000682aa1500b41211445000c08210f4140203511000584030020401580c0340424410091500960075201e000105c0d9556520b400b1056000b0407199455903c854280300c032a007c040c011410b41d040072030000e00d4486004001280d4244c90810004022960000301e490030800c14a108210750410080144000710480001c2c5040c0c030760520602a0840c0c0416441090003500501085100101032503202c54040250403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 486961753 1250 486960503 486960511
    0x206030414120901032a18080d02150105091308031807090c090b070308010b0d0209030d031a03120306090c120c030a0c050c210c0703060e06010602070e040605 70
    0xd240403081c401c091103000c2c4190041e044000500e9079903420414009001e0b9605004c090400c04049115240518418440e100030010140383c6040c10540d0307440e102400e001c0d65002014544031b880d60090105030000369400103080001030b09480781c2e998000b0020317402c00071160f10050a01c400000800100c404000d5501302801d0200e0349801c8502e0354069180c070700d04e60300400c52282c840d805c032210380b9040f00000015100c0074800c0740c50700c3c00944014080382e50600c035007503042d1000505400707604007660584078ad0001c001c00356090310260440013009031a2102e40b07003400c810002050000e030710700024891001e0000b5000607040d959101c00304685480020400f03089010204400c900b10703882c1300541449240882c1165880c1d0038507442e2007049aa80c0e59240050000810a4240011000035000d0601c21201a0100d000102c0e200390b000c2ca01a91030a060f5601c501e12010041203915000303910f90002060490701d642c0e0340d600c03080b0b9039074090b031040c0d641f400a0303400498040b9070141c2219a03c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 486963003 1250 486961753 486961763
    0x30c020102030d09081b0c061209070f03030509010e010201020a0f030f0609050403170a0b01090314070312030b150414060705150103060b041b050405240a20061302060304 75
    0xa0009203d40c96042d01c8202804944200c80003030701c1c0c9410610300c04c1c1c04e0b0741502038400502d062011600810194841d55140c03189260f001e8000881c400703030400c142d80142079524402084143e0f20700d005040743e0407544c0800c4c08182d10440b06c121a500c1482620a6441c03141d07a401c1c1c2e00064406e082d0700404140d000c5120450321440042440310403402200e010b40c1c402e03611540c440300e00502d5085a03003009402d0b00452824070008142903030f401446207050b00d41020003108000c0c0c5402200785040050740c801481c440d0b403d20400040c1c1e405500202c2454010341e06280d1f068030303030082c060003441f950081c400c0c1c004034004e42c1150380c1089400362000600c52002c849070303400392005c00303e58038009030b1003101d2094651b0703101c0340a801c290141a01c581281400c409403451711080c040c0c03213030081c1e000c0c0700d0040351004c0c1c195166160b4101d0f1b11640c40241c0c1c071200d80c5c1b6a10300c3d200803d20240624420303080071105407019101a800101c0c00d101d4170700e002e00e03d0300c0d0810a80c200002c50b4000b80c0280c603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 486964253 1250 486963003 486963007
    0x6062e0203090d0c08250b03091603060518120d05280506040e06090d080702030d110a03051e0103060216021305010f0b1602240c0d030621030c02010203 67
    0x1080d03d030062802a400d0240010700e90061a04100d6460604400303070061040f582403049441d400a1003440c08241c070031009032591030765035085038546003640940c080c3c15070403451a000020700456501c80c50040030202c1045605403202d2040954401c010581100712407010000c0e040c10f0640fa91003d50006a07020308400f0203e08980301c0312942c1240400d1040407913945061149070315081c8a40f5218850400160a076403501f5121251100109260001440403000010f0a1a07100744111a125a5200020002d4100e0003035100c031182c2003000d0b1140801d1600d804288c10b12030410a60100038861040c80d55942c1c2980d542030080d41014084240390200420034100503a200c04209000c2c00000800007150f61605e0540c013507440346907100a8181e00100907406058848400c240b015580545070b0380159a40000c01a91400100640300b00780b200203d1a1000f1070390114194040c0d03c141e60741400100e0700d809201c85480e0412003485d0102c4003801c0a0710001e401030840100352801401564 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 486965503 1250 486964253 486964267
    0x307030506040615140d0b100803040807170106031212090c06050a09060302161112010504050d110c060a030e0106210b0a05040804050d0606031209060206062e0203 72
    0x585815001e4504560490321464130452103111118001d0050403c09080b0440002c460040f58480980c400003074014074040c0005010705504035400e030000e04411046960b603c0d91024495258105405003da0f0503050101d40760714440140500410382e80c02c0440c0030681100c2c8a003e41c0c00d8a1a041c1041189446808031800300f050140c034503009107401c0e1101a0350b14403141c0000c04418041d0040818544180200f0340368018a040d04c154456000340b0010b803a1302d0b0140010843d05400054280541c01d0604100401c40d010425500c1ca481a8680343c00841104086944403007000140c144c02c00301c10300c0740500061007608034a204c081e103000009071082e254001c504411482d01500c11106140e98a00420003403000310b05a44000091400c2025007801d541d054400e00c00d0748074451240c1c0546c0c0e401c00500ca143d03030180c4004e55005150b08100100d110000d0b00f407000520401016025450024556050800303019051222035000d116954100d643d0000c080b084211182e0708500c0244440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 486966753 1250 486965503 486965513
    0x10030e03041409091c2d050a1205130303050c0d090308012c0c0a050d0906090c05100f0f0306030b0a1b0f050d0c1b121b021806030703 59
    0x1c0024007404140803140d01c001800303102030900003400f140480da00610300e0000e05036414034001142101c0d0300d0501c01c000c91180c1302503400b0402c00c0b400442110041c01046029411400421105501da11a204070341d0100c0f02c0c00040310002c9409920b103003117007002040042d100307500c0158001842c0700c0f15400c0c03005260702042150016581140840c44180c01070107581075900401c80b03517140ca400e0710900c0a0414880c080f03100c1024040328000c04c00411601020783c0100242d44841c0c0c82204100074000050038000301a01843c2c20565100b5420400407030035042a012460310803c440d110741c1951005454211a800d507404000b03c20942c1d603040200004012a102902a100e6080080f0f00454000c040c240780d500c1c0c1540d01070900c60009a03510800742c100042d14243c0021070740004000c040200c00727a60754601034120501040709074046030100720b04400441540551591108400301c0c081c11010070350780c04504065030040d04030088031003520f490003003540e001ea00601503884055495642d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 486968003 1250 486966753 486966757
    0x303040b0c0c160306050c161101050712030f0f02030105060a0e030c10020f0f21030709051003090c0906050a0308070203120304050a06140402010906030b01030e030a09030c0b0304080910030e03 85
    0x110f0341041c00700785020018002d140c01815000002250040d143c89120407070707800403000b03005008100c0d50340014040302070303805902941c0c1565041f030a555030b148501900100244049081c9403091484c09000c585554800e20940f8162403002d442c00e860710014440a45908080700222681031040300d059640a0b140d1105a0090f440b10b50002c02c4000e5041704200e0810f044000100a10b5002c128446400201d00300c924000d01070031203003035035240c58000e4100c072050495000aa0050360780c04004d85103950550001d1190380c081c0007101001071719040400b003a60101c1c4a400c0d40041c0c000411700100d00420001d101c4584001c0c100d030341c51103491202e0f80071600120303002c0d91f458000f0140079081c4007190040000b00744900508004901c0e2913030001e4810522402224101940c4484140041e40298002560a001801129241c0c4442203004104c15a83d0108440c141d11814000680d8010b0308140ca001e44c0d0702401c024140790780318041c0500d031607862011000301604d91381e80288007442800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 486969253 1250 486968003 486968023
    0x130c0308130e150901210b0c0a030509070f091a040c080412090506030a050901181209080703150209061b01020702040e0a020d030f0513150305060109080303040b0c0c 73
    0x140442592400004031648500100f80380b100c0380f11901035980381e81c1d4196503181580d50441050b4072000c90034103220400b2081100c02008000b01c0c40c1407041e101c8401c0701070030699040d96801e02080e0341e018003d40d00c85070f2a1003a440500c000c410103015004c510f40220f043c0c0441102031190b01c042844c00101594040e052040c0403c4140d0144002c2c44400b0050180186840c180a031001c1d00c0c02010980610005020030003140e0f5a0000c00c2d092002900050b018010282460b0034260760340c1890384006200740141004600e56503000120844003151100807a9009803143c2059414090000060341c8406d07a0300d0351280c01001000030b0140d400900c0c18042508500058032401244103000c112180d640c01c14410b07900c4242c070710f001642c8070401c00c0c0c500f640c18901101c03202100001525140074001ca85007070120a4500450b040210740c020f101c81100c50b0742d090045845190040d80c02c15424044c00d170045c1c1003040003170040b610110a058010490f03496071403418054181150034003582d50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 486970503 1250 486969253 486969277
    0xa080c03070507181803050307030b0f120d022a060a0203040806010605121e130c05060f030f1302090c090d060e1f0e1b030109051905070603060e130c0308 68
    0x880c0410b0b203280d505c00c03c0c075100300d1a0030407001c541c541d48010300340f4040201030508054075000004640e449504201c0700c010300182c0f542c5c9401101003040f91701c41c10342440c0b400040c840e03000010f01c41124000180e42012100115078610344152040c0319407603001c01c94280c02d45c8010400098540002c0002500a00c1c8554616858401e00c40190080c1240607180066007064520786032038072828135450390b421000020344610945202c0ca05081c1001e1240d11540e800600441e81401d081038032001540b00750380d071103102c1000d541e6803075440b01103691040740a90804039140019000300954402400360120003800740d500c8003895034590342980e100341d0481c3d6860300030101c049003800c0c030603125a0301490402418803410040032400c1e940c076040e0103500d807124400002500100d0f10203501c007101c816041415109500024030111200001e8102c01720340c7c92003800c42c00070360640319101d11030175030361400204001d40e242e100490203034800340c00054a00392681305001001505410041003504550 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 486971753 1250 486970503 486970529
    0xe0106151d0a081c08010b0a030e0111160507120b06010c0302010b0613030323191b0501050615090108060d03020f0607110c06040311040c050d09150507110a080c03070507 75
    0xc211161030b44c464885003182445420380c0180400c1c481c01081c0c90249040349000520043c5c154280c6000d4801040701080380c0c2d00008102d0500907401028151031402601180c403aa0340c5c03440307030701d4540d003000c80007800c0d01d20440082499984103090360651940248004184101e907403000030455400714030701c494904140c4e8401c00415070080641c244140c40700390050304462020858503200c0c4075040c03840c0100d4005000601025000d40580c0200904148180400f02444c0c6003190083c002640c41314071602c2040714014030081c540782182d0142c8010b83d0340340000d4a8840a0000c0751540340421001c4d4051194180e140d04c0003001941d106404699403070107160400ca041c1130900d0710305000180900c0d0200401e10105134041c01180240c44151000201145800c400311094040c02c50400d510310300b40414542807258502e460307c0f980c22500002c00ca240c80d80d510071388032120340f2600e1b40c440d600100b029402007851480904001e1856005491030018103540b01070414000c1d410440840b248 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 486973003 1250 486971753 486971773
    0x70501050c15010810061e03170f030108070609080a0f08030a06080d0f08060f0a0b03061908011a0409051f1503140c060304051203090c090a050a0e0106151d0a08 71
    0x85000326030080844040a448080c5000404030154655000c0a001110001500352740307400c420341124448000e07600096140e50f104e111007a1200c006118240020f1850308011074441004240804d401d98481c464030b41c032600c03a60300c40c582d540009000707203ca5580d0340300001e410742060202000b000100c4d0382c0d0007020100c500014003105000f80c0400c1c060741c08888401c1d19501d600c3c041303c5c00ea4144203a629102e95a000014122001c0307001c8402c6010030200e0006128941500050044286d40984640014405092200b190b060080280031540801406102c50ba410304880390300040f4200c02142c4044403141c1032110b00d250391b0040710002031000707513944010030921100c82034400c200e451350300e582010349a4950701c1024001d0f5880c0840c0000204141c090200111408100081c0c905186468100c8070000100000c40b2400c011900f040d41c40f40c40c3c614180724400548103000210705107200c841c60201c45040019400e68889192280d02c15000e0381c0f184410002440c04800804d00b801e8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 486974253 1250 486973003 486973033
    0x30c070b09060601200f03070c081c050403080d2a030e060c07120210060906080d09060518041808250c030b0c0712031a0d0203070501050c150108 64
    0x3600501080441c0c0044040c4442a030340704600200f8640074200b41a4604440218075003014900c090314030390b51100007642010071035000854002c071000c003019611000d0f80c2281c160b101c2010f00f040c007400079500f0401400081c81c0e41021308506410100e001866184500c5407818052702503840c5a800844110403500a80d4036000d20013414000340003500b114102019001518003550f00d0080c50070711182103030208a4401c03c205c109880d42c0388005c0c080130342c2e144402001002903005401c01401417401c5550014010070640301111002d42d510741c80c0682c54510000036444104542c0e610503168040b840d10705000003d01350202c0d000d035121a40d602c00c07081000009180000040d8030b032120071051407003ca04101c200d8001c40c1e4000c104100703e969540c2034501e01e4072813090000c2450301ea1060f64081258190b110400383c2d8040c0a002c4210082d02003007049208001e00c009506a100c004203001552080004d04468a86041221851030250b00c40702c00305c203400d8000d140d06078407166800349120 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 486975503 1250 486974253 486974273
    0x60903040f050a05060409021c020d290102070303210905030307030b1912080c01020703090528120201140d1505270405070503070315050c09010c120e0402030c07 71
    0xb00c1165080c080914060201d002c501031481804102039020400484865480d8080e00801284540441d6101c2010760004001e00c04481c0ca00030039a801c104241d80d91a4101405180f02e078140c0007040c01629640c5c0441c2e03c1d1004880c0c54101c440010026044507115018909510344100003858407850304040050032210004c4089110380e2140b611040f507291451002419a9a6108081c019001e2801d0100e09031140c005000d20310361001800300207042d0b1000340c040a44400302e87e10480562080203201004502260f110350203203c94000f000480c110541e40303400315106040001d0001880e00f581002c0340c0180fa145100c2d00c0e21115014161035010701403401901d4201c42d41490595000e00800240507030300e90207001d17000f0101c040350500408200b0031006110050444600d41d80380d16205417040c107110188001c1d50b06140129401351a1142a40c7d04032034180e40702c2100148a445942c1e040706224078003000d10004171410201c0f51038a000071880b4042085510360354203503501d804a01c003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 486976753 1250 486975503 486975509
    0x18080102180406031e050a0b150406170d110c0306100810060b0f03130209010b090103050f130b04030903050313080f120d020c070509150910080303040f0311060903040f 74
    0x5614051080c0000f620305d03860001d05100ba81e00c1400c0094551401901c1d00c1010b0b0405841c2c60590410414035115501d030994142c00140c800b40044c0b40d40b0750144803c41070f00040c0303a040d60030a26002ca80c2c10720910054103e000c1690032502040d441da000f107810084241c5400800402c4198140100e03102002000c00034005d0445c1000b0192501c6d030b4503032042c001c01120600c1018008080307144039009000810341c4075002401c407401945e403141a4036072035102150441c00b080c10700001980d460144240244505a0780b0910030381c01c3d03420792b1002c004030340c02041201840500000400418401c00143c032400400481d45c000742ca0401042a02d00340c481d000c174071003640c41440d041d100b00c282c074010f6421450300b140d00541c465400d0301da0f80741022415000160865103520800c649085954541c640e42c0c102900c0d11080c0d91248164400c1c990600d0040300b00c40c2c0e100b0800700340020103407504494040e010785080030a0b1841122040e00300300090303502090f43c1d400410140030381d40150040c4402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 486978003 1250 486976753 486976759
    0x40f1b08010f060f0f1d10030b010f0504050f060c03070f0c031502070c090b0301061205010c030b03150c0306060705011d2503021306030c062f03030a0c1808010218 72
    0x208615410040c0619085e19200082180c0b02c040880803402c0c1c114001040040102484441c400d4480000c3c020180c040c10903002640b07490384408954018012141501ca014002016680c1307002c050003055171099990760000d100800071400841d80000480c07498034803507141d0126543c5103043c44c0d0004103010600074222441013001400082c4112120f00c2202c050140118000d2080d4000a00425150340b001c000c80d6038044000d41000307019800480548a507803004c000068114040c150360f4800800e6803020303089448041610082c2281c050750f0700440081510303145c01c8103956200c0c00e40b03007800c04000144000016412070301b4018041880d00d400d041d010540854100d88451611100511001e07008800c541040c0e20308080070b4001c440695048a40c81c00001d580390350051490842c1d203841589203400b0070011a0806070900c51a4404010100450554543c124014010010326020b1000d00407070311640c1300920908600007004041c000001a100c40820000b0700203003507003482c2d17248 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 486979253 1250 486978003 486978017
    0x6030c04062616091706161103160c0f171e070e04061b05190e0d02010e0f04110c100b010c0311070e0a0603020f031209040f1b08010f06 60
    0x70031188100310158000c1c1ca0101542400b80828000d4811314925001105015001152501090400244280181071140c046444c07240e13902411600007201d0480e1802d5900100250b0a9000141410414482c0035480408050365124524219002a98011020102d400105040e4402c0900c1a8800c4200049100b0103102030060390948800c868000c045045011b1f80100d01480041d511120b45c41001201503441c05000b0b80019120f50409655030000020540c241d21910784034003452681040b025140c1e1105041c5c0e5401500c00c0e42e600100c00b40c000b80c1d4134660352030a0755180910410400b4240c03400d0f0b82d1300c4120a005c0c1c04d0005039504000b15070b040071545011030740c0c040c10392001142c06250440d41a40c1c20b040c46c2d810b0003000d61103c034200130707820107115592849a00c48400c60307100300e486041c0b110b640801c2c5501d81c045135011054082051082d2038071810142c01c0300c4000c3d2150786000540c1c2d500300d14a059800c0c0d000d26041c0006414000600001820611402c083e0003e410854 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 486980503 1250 486979253 486979307
    0xb2d1902010b0117060111030705030a09030b100303170402010302070b0a05100b12070509010504080601080c1f1d040f09210207082802060a0210060632070206030c0406 74
    0x131220500503200384d040042c4021200041a814819626440d50020661707a4460b010180280307000300710700041c2c0d9668900300100d03145e00184400c0302c0889506481e801c048101c0040301442108004205a0615408020795070006550142c60b5201e00c0f103000c3d0014139402c0260740100301e08101c0d0003580078014100000071501d00d102c1e0043ea4022450b143c000d40d11174500d0012140d80c00b880c2d01c0b400c4d1900c940d00020841c0c10006c1980503e101e02030301e0303601001c190038403113401d10101c03070784038034049207040800f40110b4020f104a41203800005d080070501d903000c0d001090450700f8403201901c9402480d1600841c40100305113041c40301020f44001c0107070341d0820b0100c0e40c989400c83c0b10610386800c5011407510350816400b583c0110f5030000c0145483d40c1c1c0c0c00b0806915105018485c10015103072040206000380141044140d0350010b010781d200c1c00c424811040c04ca03034001c16409442c0c0c90240070b0b541c0140d44240007984240e10301d4541646031403500e80041c00402e1601103005815080d11907135 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 486981753 1250 486980503 486980537
    0x1110020c0307020913051902040c0f230408150604240e040510020703020c01170c0a0503250c0506073905010e0c09100b2d1902010b01 59
    0x10b200c40070f070100c400740c84589035143d211082e40a0410020718902030383d10b031805a1010b2500f003078001802542e090041549140040720f88120446582000c286040304101400010301e091055040c0b02120b007d241c10744907811145014101303d00708100140c5032040003900d00701401a04a1030b13041440882028514126510610415010788800d8865002c00030301880002c00041a480d0b41003a0304640da04a2400c1c02034940ca04a105130f40842c900f20248070395400b007060179a1013403a041131214107040e840e038401c950707e6001400400048c161680c0c1040308a02002d55080d80c1d4241da214440f0300c0d289440d00e281805001800d010501080743c0b81015500d0817590500c100729540b01c442c85107801c10002c165498400550080c209629020b00b181601070001030310100900b0496000401365103400300201002c40e18015030070701c0d180034000c61402d40d260600322051207600c4014401c81c08080809941a90400305900701c8000820030188c50f010380a1098504d0740c0030030310b49410031055110304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 486983003 1250 486981753 486981757
    0x50f0607080a080403020102130608011410081302032a0a09060501080109090f0b01090f1401030f030806031c0f03050604150303120b0901180509030a09060e0d0803071110020c03 78
    0x2c00034040148005820117200398121000282040740d4403064680312070004268000900404641d5004031400895030300d410300b041210502c1c02c0c1d84407101d1b540d0f42143d846c1280c00d4000100e8040c803541002c1c090a2007000da05100d2414500c0c99203120f220600c1c00c20491103042e500c00c5086a24044060050781d034494449030555110580100c0c08950500c1c1c00c02c0c2401e1304103009000e0284003c00072684a186421800c81042c05c0042030109800c80701c404d4011320300c2071000a0003d0b40c200a03840c0000c0c0079010340c5a01040003070681c1c019042d8103103401c1d1040340ca1424540051303140c0c100e04c46d8035501882041d82010081d1404c100c1006c044805000001c41400080d080c0140340c0f429540c004030716004903504440160038035020f96594a101c1400354842c486c1c843c0314904207400110b222070000b003075400503001e036926125513070300e865403d13144014221501d58000180085000c041100c4500070b42c0100c0d0180e485040c2000030720003080c20000d0328000d80d030050740104240f074030f020b00c0082 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 486984253 1250 486983003 486983017
    0xc0506070c02060f0c010504060623091305060408120a1a0103051f0314061b07110303041d07020105010b0903030a0513170607030c03050f130f02031006050f060708 72
    0x2445141801d4900000d803450059a1840915803000a500950024190841030085104a906220381c1d900e44800c00040ca88030b01d407050300140b10402c5603105142143c2e0721a00002e0b80b611034210700e45151125030078007030103c1d010b840e901d000149000510502d480010351000a108081107074543c0b00b4182807001d139000000d141010380b200042001c50941406507110054018058002c01da07481c034000020701c1c8070001480440c050303940000c12002c90010712801c0900c25240c41d501c0e0459990b0b81c25420740f00f00f080b41c1d805210a101c0826180c40c00b2102407051800110300035410f02c2c1c101002406c1d01c0050300810760341d96091085511545000042d50004980c0381010750711090041c40f03d428415465002003c60300443d00c4d0a12210307004030389640520324598050044100c00340b400e9003034a10580e2110a0403070320000003245030090b0882128101d21901015030a60004c0d00042c1c0341107a00704000101c943c1c1d1b071700b08116600c0d01ca00103080301c0300203031480c03070402e11183c0341c550850040e8a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 486985503 1250 486984253 486984257
    0x8070c05030c0901060324060c060f021207050d020c070e150f030d030f180c080601080a020d03030504030201180c23090a0929010603050c120403051b0609010207020f010c050607 78
    0x3045840f008801000d46100c1400c40e0b2440910a5640703230010310b070514403001946c0f0329261030307841b890108560080706c001801100500c5903d85540350100c0b42a03000a114a2010f9802d2215203010041403000340d0080c0000c00400016003440c00d40542c034290b080301d145100d00c21805800c8190344000c1070138140d6010506001a10f0021022110080c0c100b0740c03140b450703102d041440030341000104c07407010f000d0701c43c110202c500b03a80c3c0f10720f010340e541c258200c806544000c900741c00700c1c00284030750001640716219100104e01460001d0804001c001100ca085600314030104040c418a40319180081d6400f83d00d20700f600000c184800443c40d10340d00075040e02601c549580e1040c0904c110444050020302040d0084c44c070700b404683e601100000d00307000e5903000030b0a1501003404100310b24203031410219252028811038a40d5070302036032541d00060900c640551150129100700006004040c840c1d1980000582da5883c5481000812014018000e0502c950840340d000400c0000803903941c80320040c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 486986753 1250 486985503 486985511
    0x8012c030909010e181002180306100510050405041d1623030a08030405060714034b0a050a0504050d030b0d150e0706090b0f070f0f08070c05030c09010603 68
    0x7078403940b401405d0f02d40c8160014410b500b07241188500640c010300b141d1141c00326140010310b92404140c0ca451003070b202c0c040340710400c4205200614103061640b0000d0b2640c18101c0c603040d69000400c05442c002d04160044070191700c0070a80950b8140032403110354402c01c510840035810f1114a10184000d07902d443e0400c60f4103d444400d5880130801c100100383c102030b04076207919042c6445950384208450410018080344102d6070005801d109581c081d01e860074051103800400f101452000d20812400f1054861071803012502e60080c182130704400c4d58611500c56103107031201404043e1103000c1c00b006070551500d400c20001c10783c00305401c010102c207403034045029200c5400080c48900c40400c007410b2200c00040f414007404090b400064414404010b4030541a42d0389010345980340e84e0700c1501000c450410000e402d140c0001d004245092044d41d0071120794031240c65020000c1c001440403a076404000410900b07124079071008a0050600302c1c001d1408048680210f0395001e0103104036400d140d19 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 486988003 1250 486986753 486986761
    0xf0803040b0c07051914010302030606180a05060c0703030311040b040605030a060b031329060d020d080c06190e07091802040c020309010311070c03080a0908012c030909010e 76
    0x81445040010080105503000054005e171016104024603c142c0c40f110084e450003070001d5009000b501d10a100040405041030b0a007826203580025101c000d60703124403096004106942c0d620060700702c804a0701c1c01090030600b140307805811510402446010100d0038401002000640011207081d150180340007030b16601d03246070b09406451300b41c100d00d8007003c000c02000324004801c3c0d0900056400b408071034550f00c00102511710441019034001c601c00010700000b6005007403041005001d244081c1c000c0701100055100d5041c580c000d07c0403082e030b9801c10710500148004c04c52040c8000240076070100030344a40d081680d0fa8031103e40c4903c40000d40c60340d103403905100c0801d080030352442d005401402400d9520100a449500040425000c2440c0c500400d064045440c15101802e40c0580001c41c03060454032078240380d03084085c140d420020002400b1a00c3c0d0420f024002c2841c5204416240e2043c141d0901545240800403e21242c3c4c028000d44d503140e070782c0b2030303038241150100b6680e12210f8403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 486989253 1250 486988003 486988027
    0xb040b01020a08031f17031809070903060e07031b0518090d03050c0702031c0f0e0a090218030a0f1703161d04060f0f050a0501080a020a1803030c0308010f0803040b 72
    0x4961b01207600181000140c0c103181c40044018060700720612468054125140d040060006059a0341c10000700140414000503020b50300c4120107041450840d4245540c965450307014080700d40010741c3d0307050b00400410881c107101c180c0440e003003c501187c0d401d91038441589a9514140079030f07641015200c00106a8000c501c10880d0706160700a801e6807040600480440c0519080791256000540c0c3c1903c1e0107801e6100759a400c00000b80108080d07070b020726200c11500650003800840901c01c1d040e2009004075070303040114020107882030008c500c109041c1d0800401c510343da1a203111841c9000c0081082e800300b65040c0b00c003200301c5424040f555400f44030324501c0540740a00100d400c1480d21901013a0480d5102d03118089034101602d5084032074642e010b000d00f00c0e1051185901203252070011a6103120150040e09000040389419110390b107500e4020180c103146e691095022504044400c1d0915600c40745442c05890100e09011181d0300d00700c446645c0e40b06034803502101e600082940061b001e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 486990503 1250 486989253 486989311
    0x6040b090406021201050303090d0f15061701061505031f0e010f050906060702060306220207060207021309030212070201091701020301210203071214100b040b01020a0803 75
    0x80141205806240c903151060003135000e94480c02c0145028000041d4600e000012540300510182000304507152a5481c3c0310791106000e82220780d41086003c041240d4a14400e100061000c00c02c005034a114010055003101c0c9640c01c480300d01e0000e0002c00d102039400201f00c0380c00401c1014056141c0c601682c22844041e159080191002c6201c000003a02100d00b4880906496085480351400d8449600f040b040348901e250003504503605000081d000e04d41000b80e03460680402114085583c1c040c04104100d0f80100b500312074144e404202c00c015070500150304100032516003001c1088401da9103000c0d5031690004d1940681c1c1c130002407800d085910541180c4001c10803030900070f135060030300120302c1c0c040d4209010344090103500040c181c0600340f0440c0044a02038018004e04049414981d5000c1d10440c03080003502d0b541e04404400c04410b0080012403e03a82c01c044d07001800c10b4660003000140c03244441008d0440d80622a00404181b0b1a812a0b4224010410b007209080d902499a0040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 486991753 1250 486990503 486990521
    0x30a03180e01230325090c0203040f0e060a0f350709051504060e2e061815020105010303120c080c0c0f070303020f0d030e031b0c0a060302131203170604 67
    0x1500d10540385e60300708019000b181c041d10000d41c814049480700c520101c0c0d0340c1c016407203801078103c40c200e0100511500300b410950042400342c209849103403a01d811114110450340070300000e05910404402c00031140c14003000001050301000406032000b44c94507035035a0075010300c0e42e1103030b0f840020507012242c15032049140c0d04050402e21107d03507070340d80a1001190494900802a4680c22209814000012030071017424042c040540b040f428882c0885800f1a10302400c2c03c81e410344100070030301c40140c14419240181a90000c00e0a6045113002071500b900c00c807055041501b018880b1901e660480900c691206041e02c0c0b0584502c02881c031549400807044c046002c5000d40c0c003000c8107140d40401e1060007d4842022500c0c01e903041d20084089481244c03084134a078100344000c3d40741c12110398002e00c980705c0020440300499080000114400340d10f0b400f02c3c02081d0700041018243c0455498072004040111000b00300002c80c3c4c8018141e03000948404244a0940c40001d613280e0351540318444c030f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 486993003 1250 486991753 486991783
    0x201080a18050f072408040302030702040f0c0f0e0307090911090124232b0c02010608060714031e070c06290111010209030a03180e012303 61
    0x3420105052042e180c42003902c91038214002c0c03030b00c04201481610912482d1a00c0500081800d203041030b4206d5400710040c000314210f000401601015980e07500640e034413180c10a4001400344d0640c440500f124002d503516009200a0443da1400d568020408004880b90322902060034281c600c0d0000700350300c2c290580307548410140004911501038220303044400401c4c004840f05043c1c4c140d016103018080b0b0743c031903206a190342b03400c5507011202030250401d00d644141c440c5100b0050351b940c0d4640c8c059080f402a0455680944648080c0c0c24000c01c0c0c01000480060207603420030700320081c8040050741406039840e0001001c10084082e800e1f00760303a80100d0285030045820980d20041408482c16002da0310542440704000c481004c0d11100c08112250107030441360405901700548506130b80a10300f100711355081c0145115603c0503c4580103552003540c41115625000303a484040744041e401040640c21000014014000002d03502410480c107080d020b5458031800c00007920304540c2d81d4414038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 486994253 1250 486993003 486993041
    0xf140d020f0406200303011403010b0d05060601021509070e040c03050109050327010e010807090e011d0c0a023d1512110d1a18120702010c0201080a 65
    0x450040c000c007500a4035550b0b82c4550200c03414580b08901384415003070101c0c0343c0e00104010401c6640c0501e25003070b00c080c080c0011521652110005d404040d404c20141e41a4000c0c1c41003103485d41c1e041c00154080600700c207081c0174506000180d01c3d5501491301a4150340a020404141407100080300800256486802405807002500c0c4c016243d4020442c510100e001590741742584441580070500320301c03011380d076248142c01c4001c0110f41030348000e0f0900c4140b000d210310215246c03906600c200d002e071030340401241c8051201c0300f454180200c020541006004140050070040b40c0c086195529428070404245148510002c1301e20f14003101801d1414902c00740e41070422407035442d080100c04e661160102d0a50542e1030120806840001030001e00c0080b6000c0c1c60382e45460f03c462a65061406000322409005c00c590790000c3e01c020950380c91f003030210402d070b0b0344420110810040300010f040140c42400c0104950002c2d00c0500c6d0306c0d400078184842c1e2000030f8504600d075804905d14541440c0c1c625 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 486995503 1250 486994253 486994267
    0xd030c080a0504060e0d0f110112090303051f081e071d04050c06030112031112040608041104200c0f1002090306151c0c0e040309051903030f140d02 65
    0xc2d045030f009201d107502041c2c0201100300c5a241003406c25030460742013003020700e00000300c1c0e4660b0124080c80c00f0355414000340e500c041d52484064807074460b200344251000181800c10051808079103e0042c0504241c10210300706110f041404076074004c1d240035061440c1080c1c8800c204003401d000640e008880035000750000d0300e5429883d034a9440c01b5030300400a4501281800e0140001c81c80240510f0820941401562000901c1a0201c40b4100118000d0b00e04a44a000f8981d00340e5000d40d00140001d0604010300c8148040304039240201981250308014071034111447c003e6410f030040f0484d00c80040410300c1c2413907a80c10b0005100a5aa000a440450102d2401c0d1002504504c013514001d11900340041e049110311126004a098010182100e0807400c080e070580000c527400e0101e9290b049101c00081d2400c14a26440c0154465113a840400d8100020300c41c1428010018a00600800c48100040b030f03001040100b10002d14641079880799203880442e1801c2c811032090004040c80040c0b05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 486996753 1250 486995503 486995507
    0x80d050709030b090a053f040f1d070503060102150c2113060903180608011401030507080c4b07030e0603280621110d030c080a 56
    0x90740559200718a914402d0302ca0b940c0540d0780e4000c91a00a0099100c904030416056101c011110700d800f0704884501c410f8060541c503800300c040c09042d40540640400c090011007860200c110180003200c80b4001170039511080b03115801400751561041c01400008034150380d00c24403001c0600d40d41014004580d0501c9075880e0207552101c00c07140c44a0289404a0105401d81c0e425140180754458140500c000729403200310040900250413020700910001144110040c200c40a004000e240c032008815071416482c05106140c0c100e10034101881e003802c2141c0c031030304841c800740c000c001c00790b04030780320990504200040d41d0151303000b05032002960001c0740758070b818013401000752920300810104809540780195950080d075900801044401d0301c19003003410008051030703000305200c1c68900071030400c42140c9115141e11104450003510341c0d506111040304650030100780c2d0f801c455240c00c000304070789500d00322006080c503103841058401c441c20103041c4102c5251f9112500414450b0341c1d10403100700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 486998003 1250 486996753 486996767
    0x20c010c0806030d111513050f030405010f030b03060f060a0b0403230d02150a060510030902041a0a050d0501060b0f030106020c0306190b121204030b10140d080d0507 73
    0x982c0340700788520b014000c981445008845180c185180c014003143d00705050940c0064402030801100c00034501042000c0f0ba81000300801c104441c5000e9a555820000010841d0303040c022254103050a101d03001400f6100011307010740c0240034a00c104142d071200c0000608904803540070141c1500c010501000303200044208500103c06107901000605a04e02ca40303445d1469007035143c02603040030090b03c1c2d102c2d040354491584401c02141c0051580d4413800081e401c55041c010180000b80e40e4030824086040078880d410040318940f202c80c682640e948005103402c030b4070b8000c690042540c280580100082500701801034600041881d440381108442485260424420f50005102d00b5251444906001ca1454090040d0907108850840c04e0149103014103484249641c0084110020f1000000c00340190350b00d03c44001d80d901e0352146941494030805401411242c540c00c1114020020703442e40e2120312440d44826605d02241b044203051041c3c2d00d014072451964a60b04100401283c60381c0121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 486999253 1250 486998003 486998011
    0x10605010306080607020d1209050a0308040b1005091b07330203010605090f0f030a080301060f0302250c1e0e07020309030a0b090a06090b0603190c1404020c010c08 72
    0x40d0420105a6031403207540c2c4d514083d00c00d5400360700810301440e01907108400243c401c002c074503030210310074030b01d6a126031408418005c00c1e0002408403040c00200300c0400300b0160800f10303640c0d4100c609820100021900c02010f17200006045440604c000d42030b010000741c0e40350540100d40000410285c6c0000300e5010622240a2889803155105440084440c4240e9050f03034602d0342c4040c1044d501c00c05000b80f040c2c9121000e540b004003084004083c0d6400c020b0000b10620034008035440b54504400503040144400d081d03c1814014062240c0400e0070000c0c0084014000107281d442030280c0c10140ca11642d550046c0d100c09120b0005210301c011004e0b0b0403411180c400d40c520f04244c1d07400c00c0480e143d000c0c0811151313158000c1c441100102d1140c0702100e401c480c1d4401038031441503403a81ca21085403520f1104030b4568400b40308110781440d0521190980d03610925448d2031141c416520440f00c1c607018050101841e04088040455031200d5040c3d5585c0d14242000b080b0081d03520502070300d451f004403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 487000503 1250 486999253 486999257
    0x101a04140a03050703030c020609060c0a0b150310051e04030e012a0b060102011107050a170f07080f13061110020f0708090d06060e0414160e0907080d0201060501 71
    0x100904034200394580d1402c480d004000b03000032500710354044850f080380340000d90344180248102d400903620ba40c01040c10b00f010800410100d0214545104400c00c010240035040190306940300e82901c010030707001d02e02e54403408000381540c0d0780450842d140d00403039001c81d81144050208001c250b0455502e40c1300e002c3c240c1b103480801082c0610307159a06201d0908100c1c000c50425144000b030b09078000e06422010500010804650000702d030134294204600950f500e0380503044070020b21011180510001c510348038407510303204540c08800400d204d11540140803600018400d910200504162101070b40007104030b01004e076480000a0114050400300700340c50040d170a0070200000d9900c01c9806283d007000d1007500340070180e101c01101d90080c1e4546038004030b0701e180d0b040000d12244245c5001d0902e11034a000e0a0401e0709286040101c1030054481e90344c403d000d201e01154524000350300f1240c3c1c11280d1a42680d0700c05030a0308003440b03980404901e00c1880007480b5107980640141042da4020f03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 487001753 1250 487000503 487000529
    0xe0303070207080d050a0c050a051b0405010f14010f23030906070e010e060a0207032a08010c0c171b07080c03010204050a05090c0c1c03050903070302060609101a04 72
    0xa0fa80e0540c94050302c07403030388000c00c80800111040c0c030f000300100b00c1558000d00c00d0f10004107654a445080c80158294010703d0b40360750f14503003e41c0c03078248101805820b1a040c00d02d041c41c1800020001c007001000c00c513050000d004828680244250b1000540d204100d04649044501c5d5200100c80d41041c0c40000e0580214400101c986200e01801c60145005959801048025000b03111543d1b10106001c1c08500400c0004408144843c42e42c4c1940ca10509002c0511114180100c4011189410184c0580d040240c06a01380d584640e1b04207105800c000d803008001c1c002150200140b0641700e4079401c62500070b200282c210804210315080300d40c1141030b5171040034480e0405081707209900600f980030701c100354284100d081041d103c0740e02080c0040c46900d08510542403600d00300b00c0b240e01c02800c0c5003908541036207d500d030142c19002000c0400950400010fa80c0107034840070010301c81806045401d00244014250401403401044210728440142043ca01040c0c0c09906c0750140c59841108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 487003003 1250 487001753 487001759
    0xa051b0103051f0902130b04031a060a030b0a0c120f05060301063c080304140f09010308340b150a030b18030d050a0c0909110d02090a090e0303070207 66
    0x80c0d99280e8003a0310340700041c03d0b605007400c880b42c0081d00302903000c0059211280d00030503444c1404c0020005140285480c1d040501c210445052042004084500502d401e103800c02c00501d5100c0301c19000003000c203004c5418031425104030b48480001684443d00c40c105002c15404c0304e000d51040f0b0203100141c0092041ca6149c0d145580c110700002003102c14080f04a010340a54502e4817041c295001c1c000c1ca61a629036038a1840e20326580098002e482c00c01c001d5811190b25107020101c800f900d4105545a0710f40b0342c91600d03004401e01404410086d041802c11514551203074608030840e094620301d0316034a0441c0d02d07003001ca1900c50b00329005010031800240c0c541e528507011825100701c0e40d219619440565840f142c40d180c1c81c00592a5200c1480f080c02100a4417096015241c416108868009410242030200070320800c115481000b01501c1c0492030f9921701c40e08002c07292803c1d520300c030150f034400c2c4001c0411201405a4005d1940500d411000c82da5000040019802103a40b58211450551 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 487004253 1250 487003003 487003021
    0x111009170412300c02040b0603010b04060306051c0201230c07090509030c0a1410050a0c03050a0605030709021e13060f110613020d1b320409050a051b010305 69
    0x181c12010000705031070444910f0b90039442088200c2c0464070140c40460021180c00204482c0d0f042a00070450b00c02003c5800c4c040d00d540741c858100109412500004030842200c003403100c2100d280b0019041000c12055600c105090508104100340400100d5555100340409651100140e0203140c0c510741c209000308400401c00415070381b40c80e241c40003605580400d0307a500c0c6007282803528011224003034103114420943c0140f041a108400086002c5254044020000d00302d4100502a0112030b107450401e0182c1d8400280e2482a94003c030b50040c0c1d207005649002280f0800382d060401110030011b03250284044849101c022074105844284030f9206044050390011807920000c00a41c2c07100000510300040c3c2c0042c8000d40c0c0c00903100011a90141e102e1080c03804070a8000b07000041400d030100561030192240c02078132952441c009901c0e03844c1d20060b403e80342e01c00d11940d2041d911401c103481440300c1840198a0542c0c03080845511130f41140900020a008803580b1740801c0c5001e000400400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 487005503 1250 487004253 487004303
    0x803091201140a05180604030203070b071b12020a05030403110f0121050c0d0e010c02100c0801150e030714090c09090a0c092310111009170412 63
    0x81c2c10b680c1c414469a48011040340100801002075030040c40081115408404c01e00c021409140039a000e141e03030304414201148000d01c041c000301c1c10001030000303181c8075241184002d00741560060140c82a2a146da41c104e1400c07900c464060141d00000400104211082003008100270064581c02540640b4034019103103802004800b620b18191400b246601c20015880a0b5002d01d004010740e003080b003461900c1742151041c03035590106a64414800d907880e0b070104041070240324000d40511140070001c02c01480c8100600c100b0608100500011440500038101a81444c00c040c044648040d528080f8008502c1d240452900401c40e403000f1450400080c402c0b1404590043c0441c000ca031140041d403c001c0c102d42d0200010001310000200d0100c1b80c2d14588160101101a8400c4600541c4100074032401152055010301c032118008604980b00466260014401c001c40000c0896890074404007020295190b01d440e10000500440c003650a00d20740340704640180c0343c00c8c1000c0304003020303031000c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 487006753 1250 487005503 487005521
    0x1c0b0103150e04051f020c010e0c0d061a15040905010f032001110601060306090e03090d150e01150303020d0212090f06070203070603090302061f0303270803091201 72
    0xc07607041e840c24400c40d4219406107410600c940201c1e40d1524901c80f400c1c0c8003c0074840c2d825041a0000ba480040007024010305254030140000390071240c40d40ca00052100380140b80c0140600e8842803e100d2180f400c800c100c591200c05000b190001c1d08120303281c4810f034030900443d0800c901d4000040385980b440004441078a51210700140d01d0040100c0a170212840e40360300394104000e21b5100441900b040c04800e008140c19200415118101910f000a44141c956040c8141d8414403d03583d25036500582251640d4100200503003d110600082001d40b100022010341507003010076590104000d0404682180e000350b0943d03000d011a0311b01240c55024480500840c0001440300c0c2d40c581c81d0100300b5110490000b45040d28141d5581c0c0880d00f0b00307031158425000f10b603483c2d11f10418940c043c00b10950204050503404080b04101200c108510018000901000400007801d6995003140d59514051410030840b0003d01d6504d08082e5542d600503440325000340c074071301a505c0300d0b001e05000f09105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 487008003 1250 487006753 487006781
    0x14040602060f09010213060914090408070b09162907120e130510030303180b040609080d0e0a14030c0304090f06030b0703060e011a070b0601030e031c0b0103 69
    0x351661074000b21004005403140525560070007040c01ca1403070110940700100030340d440b2220b0140c94a112000d0045c0d4052109005032809400c120000d00341000b140d4400c1c1d803004100d00d060b101e500100e864540701c9c1c141c003080010150b034045030381500c000590100d8041548042c4000240010b01d00f0745001e9803400030141c0c00000f403c109402c0c080d54440030055400391004078010f07118400c10054030010744601100040c0030605105159041c00348050020650f403d10200e40c409a403005c40c1d851000304040d00f6559102000400c01070100102c8042c0b003407101091010b400c3c240766032600d541418000300c602407800550308011100100654115a220a024504240ca0100500090f0084942c2210413990700c1d180840042c0300000402d0191000d5903000494a041410350106503a068014088441c02d1140f44107821040c102100c2a07980e01244031055525060010303405030503590b00300030b0140400700e5811040e0544181501e0603000031001030148151820040d002ca4103a00700c0145 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 487009253 1250 487008003 487008013
    0x30c0607120e0f041401081002040303020a0b0a180614071d1216060203030435070f080a0e030114010302030a0b100902040902090f011d15070f05010c14040602 70
    0x1501c0c018100382d003580002404850102c2d94800000b401ca03404103480395500383d500c50060110001c104854442d82c901d0840441c5882d0454070060364500803520014115030000e00001d1344e04a041d0440e50200e2012200a40e41c03074820319080002c1c04041e1031100b0900110000030360f07001d02c691342904002d1864075920780184002004e04c03540840f1038031842c1780384c4030b0fa500400c0400c3c241c07461403004180340d5002d140c50b0308181c584200c85505403101c081101c03015940c8484007515958480c02e00020b1800d005a03508105c3c03610300705071032a080b006803060358042030b2103203400e41201c040000807004070000c01804040000003c1d501d1020302010350198402c24414000450303c1150b1500b1491041c05503100c682d072000e1410a030380c400c1d0482064950040341c184540d040800c08903090f014242000c110740d0041242407101c14041000c480d00c00c01c160f91400c1194400c0004840401d50001411705a5601508095003c1c1090119000004003a85c0002e400c40780c1040684081c1c0300d50b980541 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 487010503 1250 487009253 487009283
    0x126120c2b0e03030705030406110f0109050d030507020f0a080301090f091707140708071d0f060103020f160c030506130803060f010306170105010e0a15050d0f0c0306050402030c0607 80
    0x4074420b0001c0c0700543c1520040089801064042020744000d10a0380d844800c0d0305070902c022810410702050f0300b511a81081c00420019070701060b11880c1e007403a882c1c000707069950403034100c1c0352000480e0b882c0b10340d0140d003008405010240e0b0085040e154041010b025102c6001c0703020044405d0080050300070380c144080d5901c290907034401032040600528812800005000c070850508174107510080d0258800d40b02005100b400d00a05603502c5026855603951386080740b458040c0f08030003001103040540c00a00c030710026107094155a42d50f0f03441e000141001c07032a413a12a01580c0d103030005841c18882da4002075091180c4030b0401e00ca00398014441400d5850360403e00c034204004000b40360606440f00d80106810f031801500c9810712100000100b00c03545400c02e0710040f5000500318152035800c0600c41804c0d14008204d98048030016240300104120604103003807002c8588000070540641c0800c000144501c640149004900840948074107028420030032841d03205c0e0f207000030a540c588a40030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 487011753 1250 487010503 487010507
    0x3050304051003060e191425050c16090e070b0d200705030910030c050a051c0c0908060a0204030b0406201b06060312030126120c2b 58
    0x102c820704514280401c034651103a03ca1100c2c285c00320340e941c460300001c4500100403415409a0168581c0c506290b8407541880343e491100c076280600407000305a8020041d102e100e00c500210751507442440c055407001306046ca49803038040360520408400900f44259010400c20100e610021901100c8070a480c0c540528450005007501180f107607138604540da03000320000c0d060b01c0100700d818840c0c0041e580d035020010421484804c01400182058607041c20302e0707249504101141e0502900d41031240e02d03950011045c0c0c410560381100c0c0340015040048204040da0090070140640751080f00b0381c4c0490380c50300c490f10f0890180d4880a800500c10201290100d50340d6841860041500d0400c0d80f849107100c2405801c640c003884082c1e00c1e40d141c420304080c0016082c00340907000a0f04401400600b440c1152040842c001802410f002c00100d100300f01c0329500b5400000350f0207a607071003500c039450051040d0049035004045107603110f0081d0600048030069020440c00300d100c0d0000181080c405100c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 487013003 1250 487011753 487011769
    0x7020705011b0b011202090a0506030607110313030f020a06030e07030816231504050a0308090f0607091d060d030e0f15030703060b0c070608070e040207061508070305030405 76
    0x1001041076074141400d000c21501c01e1910f0203004034207111000741c05d180c410703c0000080280030301e05207843c1006010850341c01140f2a074000103540303040a0005905c10600e4254481d20a00c0b031107a083c002000410059440e801d29002402210460541541c500050341596407030411001c0b01c1e000300c041400020320080103080b900300080007480c007041080d0380700024a280c51042d0072584030210b20038981484100000f05d041c2246584695881c1000c0d03903190394540182200405100304800000e8840500300601c442003d0b001040f90100d0074105c03030140510700c0501540000b5008020415220030140c41003a0040d24081c1c9155000f110b591400c82d1410323044010558404002c0102601d0795803017096481400d52003001d10b0740d40b420507030405802c484130355010072070804080c450b18003032140104604003215100e08084001c0d42d50303103030100c0315403d030311089942c01440400c0100030311102e94404080c0c1241e06000c41d07606038403841116655041e5200c02030240d0f100704424046803c140d05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 487014253 1250 487013003 487013027
    0x71a0f040c0e04030c0b090c030f030a0c1103010b0607060515010804020916030b060a1e0309080d05040218160e0a052101090606030308040b010e010b07061a040204060e03070506030702070501 84
    0x900307805c000400345d8071b01c54460019144005654490312842000d89028464007a1f81e050b10f030000e510348011135a01421251000d000030301003026012034100c0b0380d00d081d000030b940408020318050744c0b1519490601c00904040d202042140300c0c5c0300900300a940124841409150020711070442991020100c1102034105c00220040580f80c0342d0364142d0380c0300c86028011038402c0761242603080c04048901840b07505801c69460400d03003010400030204010313a08071801e15850303441c0864165128004144482c00580303110140301070392403c0048409070103038040c1595000d95240c4031f50746030010030015015000d002d580d0b40300030001c8a00703121a5180c038100740a04110b800200d8900481c1c1c459008503045503000b9400300b03264608001c00c0003541d0414031302400c2c40c603220410750750500804014074010b8a00081c00665501603403840380407942c46040a0301030040055640720303203d2000800c08240d610b6024040e20a8000c046420300d8920700b56403086030160b004040b00c42c6000700448614034401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 487015503 1250 487014253 487014257
    0x809030109060509030a110d140a05090616060b01030b060306040e0703020306040b160503131509170418052401180816052706060f071a0f040c0e0403 66
    0x41c1c6104002641405150703c0703040014040c54507510034440c094a001c0e00e0900c101c071140c0241810101c0c85401080e10110086e106200b2900c58880c0c2c4410b44042c4030f20781c025940b000d4045595002a40010b6924040500c5000f0034001411161b0054065600140030158821014000030b140fa040540c02425020380e80707400c032071700f0f180c0d48d4010030700303002c801d440c1a2048032003507040040c003030030032100011003e1003483d006180d481e100e00342c031000d040d1080c00140070204a615054200c03c2030b400940542c0d4000c0007120744d51040c015011020350040c410b0821210203042040c40400181c46040e1196800c0c82c070100315440401c040752510400c143c1d08605022a405054040400400741d41028048800041c00000c3c40c801003610281d070144c0c0030911031103000b05414407248410092111603c41c580103250241c4540c40000c4807070007900503044140d64049403105c1404400100c14400008101e40300d025611070401000741c0038002c0303d0150903c90b000104214020720541c0043d40f050180c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 487016753 1250 487015503 487015511
    0xf0213030501050f07080c03160512100e062b05030712050306040612051c091a190c080313021c030309050c190509060a050907200607050708090301 65
    0x41422001404003a00107403896035590f4104403400301c07410555500041141404500c0d86000a851182d510000741204041e0907480101c415080c020421b03680784841d840c420308920315115401e004c2061039803145841240c4000080750107030602035804003112804c0480c145001c002e0740e1689204602641040320700303200c00c1120b500800c40d039810456507402e8664560740c0e01d0424404102c103892481d000b4100405101d81030310f000410008050401e05020446030301107503040c1c0c5095656041d00e502100142c03118a4000c1c1c04003502c03800070a11092128060391021072a101c040301c0c00301c0d00c100700901e000800c20106286a00000480800510040c200000f0943c80340d940120030403003230f0045022a40750a024810088140880541c08400380c03808400c59090580d1580c0c066074511410b802086048040341d020b469028070f0401800c0701a011b408142442d450040c6048402c84042d000c046401d809160708420125581c1c0c0210111b544103410680a0740303a0301c010781d001403030599042d960303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 487018003 1250 487016753 487016767
    0x1404062a20061003050d0203090d0f170c010606033e04050d0c0e090c0108010611070e01030b0f0703090f20030607020f0f060603060705030414011e0f090b06040f02 72
    0x304001451081200292107100c441c0b031850414508050300003140155003027030142c592a601d40d80070507415507402001c4211900302c070303040c0114400c1d12500c0d00006c06d10009005002c0d0780054000e2401c48a403680c0411a201042030201000d03d000726601c0507000d0102c20b9041c4001d0803d41741f00030003c010141c10700d860340d80c0f800901e80c0440c280040ba01e0140c890400c005202c01290402d41c4001803a000d05400fa4407040000c0804d40d05001c3c0b4024000c81080034049035004106420140261540d868002d50f1a820141400e0404a802c900c0c664008800200c40511900802110650100040c00c0607000c5a56442001d0b1900001d0b150803410201c0510316642d0070014103000d00b0032600034000e25141485080d0034000450405103030343d0310041c2806815140051541c0c0c1c05001403800c0390700d0b07803220b18001401c1c640d410480c100c0c0790700f048980050341014620702c1015000200080020003450100130f4203a980707002e0094215a420700c005110303402d164000300030030242d0507401850080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 487019253 1250 487018003 487018067
    0x30109230702010f061401140a031d0c04060b07051c03091a01050f0d05030906070615030c0806060a03050d1101061d0f0906130f03121404062a 63
    0x3504a5420005030f460f000d52103c01e83c4148268000f0740740520394800003601503000a451203210442d800ca11b4200020305140b00c0d4400c0e442164481301499014001c4410754402956440310941c50340d104910b05400000c10883c1c0104581d1000da0010140c03151204440c025012600d46500c000d081c5500d413642980003400c07203809001e141e0050b03580009994100428080c00c840403a40381d07402600081c1039500401c400000391425000112441561507250b403404e80003a01500103041c0e4041c5010340040108050440300d0000d80349000c0869040342d0b00d907020021600d003144000f800c0354101c2d5030041c424a110340300d06840300980d2400403d11950340c00307196055500808001501e80c03e06410f002c850114040e0003604001c5040c014101d504000605030080768000000401450494424008042c0500120010084680c0c0b0401a201c000d00354001c1e14001140d0450b251440c001c00352565480e40044620040c0080d00001b6a941071190182e07128890404000122030b0140d0416282003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 487020503 1250 487019253 487019321
    0x40501201903020604050f0601050a0506070206040f151205071b110a080d1e021504060603080f0705101b12061701062903040201051606240e0408030109 67
    0x1034803d9004103082e142074142607080c45010548202e03d42c0000c00100b15170ba980c03401810944208465039036440e425440041c289110325840b1254070610b25000259100b240e5200c4580510941ca030b61b0100e40c440c2e6406021164200d5410740410080c481000d000d005040c060910a8818034050511300b180d0b0b0002504941240d2004000d80e0080101940702d50344081e0003445100048040d2154004009019407239000414640030710701c800070002002d024552b00102c006503000b28200c0c4d500d440198440c0041d03804260281d0785842100c3c45040001305922422041c50754072000c0000c85040000c2c120350400c1444480e0b85901e40324040402d498a803000d0302000c10754004000136403079203040c01109502d485414542c1c40c44030aa00c94400c85011b030411668025424a05284d40350640f03880b240c2c0c5d2a80016002d0891850400c500d50040012a100da062030140400890034580d201710300707800000100d400810341e00f002c2c0010001001070340c014a0302c900c8051090420010800c04202c001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 487021753 1250 487020503 487020553
    0xc04090b0f2101060e1311010203070f05061501050c1f0905010501120506011a0409050406020f13140301090c030b1015051c0e0318040b030706050403020a0b04050120 73
    0x1078524002e070790384000802d115403402800c07400325055103864030061460100c00d0307550016022200c1820030f0003550f803081c8200d4402c59408203a5843c1c801542c200146c1e074480403034902015401c80a01d294440d80581c0c269041000004010490142d01140903034000c50b000d1508401c070f0b5214012000002c0082c05050302800d502c5000300c41c0300390303941015887e040c81a0301c01c601b0030941c03280c942901e81c1000201c8056a130000340100b445c0d00c0d68a0048028400c05004c1c00c000c80c0d001c40c01614103101c4c1240407044403201d01280d00b6010845040608131a80240001c007503c00103542000041d02d03d41c03905920403102091449500d56a4101c1c0200c01c480f000e070700e00000e500007184100c01d00d149d071003001811b00c9500c08118000898014550701e200b0105680c4100a00e40d5424200d940d45070000384004401034285c80c03a6580e2004058031035000f900040b80f091003241c0d00402c4a0b03140500303a03400c58005944d008810710950300c0d400c5000030318165069081c000e4903018003855500884440c0e030703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 487023003 1250 487021753 487021789
    0x62d0a021309060b09331908060303030429040834021e030106080607020d0903110f0d1e020109080f070e04110901060f12091203110d051e070302030c04090b0f 70
    0x6a408482451f5481404420841c0705100406041c85403d49001056a500c55801150b04030b610800b0310f5020350015009464808440042e0100000c115442c1c0160000f05180c042c0890301040c03115605080031002043c0014081455455030050315150510110700c4254001030f0079604214400703c0d080d42c42a402c09481c0d42e1002c03050142503a81040061185621883c0482289040d03030385280e00c807082c0269180c40b452966031000344035581e280043c8142603100f641e0041c109000c0b0603d2450b882c00c180d099000c1549000002200403010a1401001795a0000b4000c101c2c1403ca400702410300140051390741070021500080070b07840300e504050180521340c655200740002010020115503042040300240c60a01070b4550008007010481c0c03401403210b04004c1050003800020014034010520a60360039401c11040c080000c40100f01d0301c407040a80703140701c5200d540c0c03020103170181c0c4815521850040c01c10402040300c0c4007030382c1c8010400c440050154401c94201800a6041d06040c500341903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 487024253 1250 487023003 487023007
    0x501201b01030b060f04030203150f07030504051006030b0712090804061103041802030105040506061602360a15180908040b07030827062d0a021309060b0933 69
    0x170a510303040122b10030004842119000c03514101f4035201c2c0418003e0003007010306451b10040b03800c00c44180311190111041200c108110396503400c0c5080c0c0c0d250140c407804042094180010701444040c0944401940c010b64031600d000d01d044001c481794200c1c3c48013030044d80400d0101107000020380800c035072f140d14011000358481d41008100002c50f540942001c0c4251020018410403140c02d20580c4640b80d0101c4038000356411082c2003a4209100700304000c0d0b00030705601041d507422a27021901f4064042c40074100400348040307142001940803801408c200320300c1400d003806404040c0e0030201a652259074614107080e50344580709442e4108400440200d00381d541000b0b0818105005030b011040e28102490440d1f0740b14141a40b0750101905591009407040c0d4071a2203029940160501a112003001201344c0c0f4001c1d4409000390801c0005020004005000013507140c424020481603a5030203143c10301c2c0800c904100001400001ca419050388a41c3c1a50701c040c068003100c1103100540907000135 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 487025503 1250 487024253 487024259
    0x17040c090c05070b06010c02062a010f0501121e08161103010209060f0d02040806070c03020f0c01080115110d2604170a020a0b100501201b01030b060f04 67
    0xe09484110781c280040190601c00d000c04210095030182e0800000e0034910000700c1903002159061144480410b102881c08031031800c80c40340b070802410444002402007050041c0b4040c04000d171002841807290b030301c0303034070941e500850011304094011002154680341312a84981d01c44085030407010140020181884060007030011a800c03410348034404070001c40c584105030300020268040d00d03000050040000c22075840e6481c6a82c100c0303001d0060740341221610700d012400284008000780c4114018040c00c4c941a00b00300c400100341450742016140c1c18140d80c2000c0c0305481d07001d940c07a0790104100405221034800c100c14814841d10500c3c0c0c0e1345006c0d1018030084100d24400110341c5108440c00781383c00f00310100d001154440608120b50020954842d4020b00c124130f0310300801000b61070620800c0922620801280141c01240c2081e00d507035044282d6683d400740c0c1d225410b80da5009982080d0000302554143c40650307130310a2014140004c0145861000c0754868002e0041e07040101c400250134 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 487026753 1250 487025503 487025519
    0xb04050f070303051e0409020c06011a0301030b01050108090c091501090b2a0f25091a060a0306080708030703020c030f100207032601030b0108030702030604021017040c 74
    0x1004524032114000d1015034070b1903500030903610074480e8040c082d202401c5008960b8195104076001005414015500c0c1d0750030380c12458441c04d0a00c60141d150000c40085490020010140c90480b900821101c92503841c00b001900c40d400b0091240140e4012855074403190b03500e403800036014403501030120812030740c00710001d0007070303000b40e049076102100c00d0203003450441140962144100c08000500c1c0405441526a03280000205e0502014014200980100c081c5a00005190b81d0084a5090510b0f035601c1201c003140c201580d02c01e144a443c0c01480b2840c100703200245203c0407107181c0000c9207541d031032005052503440e40105030541c00020741c0905060b03042080d0901c40004802900c503000c60001196958820341d440b4440e62900499054141406100c103800a44203581c088a2800c04a141440852000f400304561203c100c200114507030f01c0010031f0710a8241d0103001800a0f072900c0c0c08000b50007c5d141021000c0114005e4210000c411050381c2e81c0c005c611074088484201c0c2041700d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 487028003 1250 487026753 487026763
    0x1c03030f0b060c120702010201021201091505011d2e030914010b0a180f09030c0b0705041a03060307030212070602011410031b03121101150b0f0c1006030b0405 70
    0x4201d202c0e203000d00800400e1000030400c420022100d01c14030360b852141d0b10040c0c0c0a030064111310313095000100000030704c408040d04070700070b040c000d0010320340003a0319a0015a248509815202c0381c00c43c0d50302034107800e810304540102400920740d00c8000a51040308150a0544520130310ba00020f8031402c1120402402e0314800c060004918000d1002c002e105011030f005640c1407080001f4000c0852080d50000342580c0032500311400b81d1400d0140002c0c1d4100a1f011106288040b00d0b100c62134400107444901c29000d4074103486c1c50741401001002c0420410300140c05c0070b068582d040c0100580080180d492010a80404004002904071103142200227421262000c5c04144100c03c440700f00240c0001303590340402665030011008840c40700d1840c54220b9030000c0d80000708178240c5420310150b900c0d004004412541f01c40e8000340072014005d24109180c0f07016120b842150b20003808288102c0178601e020301014190081250f42064025904200351080d550054514100320300030711080c03050500c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 487029253 1250 487028003 487028021
    0x606120c0e010608040314210601110106060503060f040f0501061e0807020a020904330b03070f0308030705070c09021803060f0a0509070e0a0501060f1d0603061c03030f 74
    0x1a00358460340c901000030300070001c0108010100000581c00444442c9084162307800c400d000a115200d903102d41c4010034680d9400d4914a01185080e404e28816610500400e4151042c0395a520709540700e61003440212080c240069901644840181d00c4a001600c90640200b02d03d54400d00d04100380c840401107200010200c000b00101481002403040d000204514943d5050321001c5250f559428089900054241d4608170a1180d41c03111a42401e1440c00140200300c9040801c9412490801c0550b6511248901072200d241c144041001c17919400c0590382c01425820081c0c5403040da5951410340358150317004200d10581c00f2a0210a2855004400741185d20680040c465401c0c9086600102100200075001d46512000081d000b00c0080c80f11600820460160784602d0400c105e103c1c1c0600700034010340c4c0014014000700c200c0c80e8815210a03400c00c0844104844d410f4020f406d022040c1e1000b40b48503040500444540407540c0b1540c0225581d80c0281d800103002c0d10520305040940704516 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 487030503 1250 487029253 487029269
    0x31e070302250b0c25120206031b0706090c15080c1b0f01140c0901081810090303021b0a020607030f140703030504050105010911090d11030a0f030f032a0c0606120c 72
    0x20700034001c01c80c011b168000b2042c1c04aa52688a94400d90844800050340c116400d00c03c2c00424408200245034004001e1207104206400c55142c41d1401031802103580300032040040c1960012811040002c0001c00898801c81a8600605200c00301d80d860b140040c90b214603241c0d95103000c82c10108004500c0c58000703d04245181c41c2c801d582000802c0c440c1e02406a14000c0c0350500c05000028040010400100c4103100074086806681030113002904155a43d0a03e051901c1212100f03140100300008a07650050000b0705120064030120b9039000c101d03409a05000c44200501d01a04004000d000c08610035a40403860f0f2410303107401420345006070b0041d50424140400c400b44107002d20181d41003014159448418000303182031018680901001803501170250390b0b145c1080c4841003100c0c4a44a000c1c0d150342c4444410780c5011401c80303080c0b00c0149604040700b000d00d01000506452402e05400d640f9000020010070744480d070442d074403580000c40800081200600700010000350400400c110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 487031753 1250 487030503 487030573
    0x1e03051f0614060f18041d06090a03050a085b090f0b040204030503040501110607080a09021215011e140105030403090314031e070302250b0c 62
    0x3150114140d4041c50768122004540452030444c408000075480e100b05c40e0040050026540c4e161004c0c10940314401d080c1c809004040000b00030314030004800c088181c0c10b544042c5040403030b62040368820006400c061031511b20500390035800080f844007110030107022402c042e0642504c040058205071100900c02680c02c07000418030762003401c000e030208581d81c1d030780e010560a1102e214500145011400143c1c01480840e0100500000102410950f032082c6ca410815210340c1c0f03122545c2d0402169201d00242e0900e0002d001030505800c038100707407480a4407080e8032004c1821007509001c140c0480711b41d5182c0380401040101b60300c000100c10100e04d501d920300010300704014a91440c105210701c90511500002050400d440740d0080c0f0000c1d50000704c840e011004c2c0d4000703d07490341e001c44045a904505035003c3d8100340600404c8645150b8180c00400d85401d00c0260382040810115030b003030910b0301c0414001402c2d511100141840344032040a003000d4964080310030f0a401c507008452182d0216 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 487033003 1250 487031753 487031789
    0xf070f0b0709050904050d20030c0715170402040f0e061614070b010b1b1002042306070f150e012c030f0915040605070312020a091e03051f06 62
    0x4500c2c081034070482e00d0f00e140507964050800600700c1d0744230100304c1917100009a240d10300c10041076030015501c07441d00c0d80d221440b0340034088500382c20549001003001045c2b8013160052526602040440c075000002144802c520b0f802207050600c2250001c0c3c084000b48401e00219a000c5414000c1f00b68501560307040100390b881c3e180c1170060500840090050008411298160140d0f0701c201c418801e80032221054503a54103c0007a42181c8602d501c403204d0004003100307080074030000c2620008045c19860a10519807200f0400461002054039050b0a0b6899056406814081c806100445800218410030350a46603001800d40c000480c0440340e00600e0020741850110468801c08902510700e601c400350b103030000e035040d10088003200c91030303400040002c1c2240c0c00501508041d4082d44540b940080600c41d4107003684a54050100041c54000091280740102e00d0302d01214110408071440c0141ca0707581703162505034004218080080403102034103031590350380210806091501e202c0c4841c146 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 487034253 1250 487033003 487033013
    0x61602070e360a20210105010503011a130618090510090803010302191e0e100302030709110d0228030905070506070219170c06040b040b0f070f0b0709050904 69
    0xa40c0003c01440809040c0c0102d0003c00c0030746614608104c02001801241d082021380c02820001c0f03502001c1e0b82d400c040000503285410300c80e6541e8a4500c0c0600241641d40e42c082040307021005001e0b40c6101e550ba20085091a4040d00344030100000c0c400004201c0b2450901501d00030140240f0f1480c1030034448000c2c0042c0c9041c0a580c1102c1e41075130040504900d038070f0f1410090384180c01119180c02c512000700d0282402d00c0504040714460001d0080342d40b00c2c5150481460350f207010103501640555801c2240d2079940d4403100480b00700c102024202010f400f84807042e64858043c2030304e80316920030b00155580202c0906248140c8500b0200203016041d81e545032100041d2240e20721543c40403c110082d500e0322101c140000282c441d001203d0358907241c3d203d0008000407e140000d204038036040200d400d0442c1141d00b41c3e40c0c1c2051203400c20f4542070000000e90b11000515421200c14800540003400c50031510403900d01c102c03048101e610f000790008200303000d00c0d8003541c0701d062040c0600000c51 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 487035503 1250 487034253 487034263
    0xb040b2e020a0b04060c030c0f0f0e0f1e01091e0b2107020607090609060e060705190506060f040b010e120c03160f0603050108061602070e36 62
    0x44241082200e004020581c14905403010203040603081c24200010010164004903e2603410f4034108005042e0792811a01d10f2071020000700401d40207010050054014490b59440310401844003007100300c040d01103011034141c403480c0b2071041080c801040081da005661140980380c440810380c4c1540e6190449a04131850f0b200300c0080724000106450b5002c41c100411108908480321b001e80ca0800c40402543c82008031044400218089008600f103885846407000702c0711a5a5408e90304030485042081640c000e6900320f85600c541040f002500c03038100360318880745014602502c550718140081c400420310030344405225034904000091982e812000ba00d800c510240c810003508a211040ca61920b0900310b00380b54035118006a40f4614000c0c00b5103001640e000840e00a0362981d84c3c46c0541c1230321420f00820b0f95039041100000d5003000c5c800c0c1135400c402030034811220f809a883c02189200f0a050b64040e4084000c86115241e601041d08484101e2010103070a0a4030000403c01c00d85032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 487036753 1250 487035503 487035559
    0x2090d060f0b0607080307030b060c0c0418020306090f010c0509101b0204060f030629221401080c0111030405010c0501021207030902030d09030f08030720010b040b 72
    0x6180c0c1c480444500302007540c409507404602601c1a03980300c0070303400c200c141600115072100006e0b04010304000c181c14000161030510030808000c3c0b1000c0d03a61020040035140c5080d03008841c2c441e004400d80940d80401c002130107840b005002d0f0207266921a002429100c402411206000b020444e10748281c0380e6581c09140c00c1d4807031802511003921510f6503082ca0851200281d809414020081003500c0d8603021002180c0c4500c41c204105858041c02c0040345000914101d42018000049400c504041403075240400b02200c1c06414042c3c020311032402c5981c01c0d480504040300c08001130001c039504010785107100b8000d003803008000e06010b810750307a01d01c5580591410010b00385001c2080240035016620500c510401103034071490204001401411000401ea200b440342001250465000b510301006503a007040c44c45050400ca9256107141342d00103840300f010840640d165103505404680040304408500c0d00100c0c01c08000f50801040e42e80c0c68082d1441207407202083e5080c1114a0501a04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 487038003 1250 487036753 487036763
    0x50301090b0111010f020a0f0c0206040918140105040210020a0b0604020c010207050708010c1e02030409020f07050f0a020411040608160c0c090506180705070f06060b1b060a02090d 79
    0x1080e0141c00403100c0c3d019001c043c1036690700f0041c4402140c4215009000c0c0020680d40d032030f10103419902c0c116400c070349010001e17400010422062068040b15000060140158880c0785000c00445d644c3c428034092000c08120303d65958003c4c0421464100302101404d0068070080c01c4c180a603458002048078083c100e44e224070341c00a0000c25103002034051b201400c2d088400da5114a5813052094041d2001103601000a0061421000c984101c13208401d0002c0b030b554015418981030010300c1001750320821190742c680ba014049140082c804200341000b0445c03a0001e01114221841408251906101e00c001e05074404d01c02030102c541e015007084da0010b114003410f100828481816035100c0354401b000740500740a5000401e400300c030764014a018000c2134400c1c0352036907414401c84103844016104c0300b00080c805c12080703000ca01b040800c0d882c1a80500390020b80e10b650b43c45100c40640c80000c155400650b01c5400b12140349060110541c86104100151300e403e1090000841c1e5040e03128005003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 487039253 1250 487038003 487038011
    0xd050c090603062209151b020322150c0213020a0e01080c0409060f0f08060c070818030318040608070f12050f030304060209031b061902100207030e0a080a0305030109 73
    0xb50000d9008511410100e0b00c42c8200705040c45811b09400003003110a88100003400d1489452030f070350501036481e10f0343c41d60b9400744d42050f0307441101a101e01c0c42c01900707880307185011202003030210850034500c149440c00d880380c020380036091050100341d40c0c4962807414003034414015101c14540003e10102c15203402d181101c42c0d42d41c0d059100c2640d02071608515002c51510802180c01c50095805030250b450340f040d075415031641d50120aa903868119240c0807407410500c0500009100c000c09020100b44046c2e610705000240c601003031a41d00001e02c080d0452000d001010224101840764402405a181c05042c04509024550b2040302041c4507810f01c0400490030042408400c0c400c0380a5a064181560394038100b07400d200c00039411107400c4034443d0191070b001a154450415070302402d108040c2c00d0f1410510001c0803401032842d020400740641c000c144500e149280c4600c010208079200380c41d02c001240703500b000d206110000b40c0040040703074080190a40441d400c5400d4a04484007480701103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 487040503 1250 487039253 487039279
    0x100302060318011b0c0308010b04270e01112a0316030210050f01053c0415090f050603060112110a0503190b150604030f05190501020d050c09060306 65
    0x42c0107040b01c400e141300314003510504103d02d030b6000140b040790303034001d0f0740d4800703141d0f02d440ca00c04030783c815032141c2c80c00c0ea00c2c08241810b041e1601c41c0d2150000d0381006002681311050508542900d03112030071042d45982c00034030340c040b001b22890f05101e58100740800d0340e94104002c40710390b503d21400605602c0c10314070300020802c00d4800c00a80308480900f00d414000c900341450204c20240e0280281d51180303000d41014000310a0703d4020321814210104c1640002400403c2c10207050784004400c0c0d00070761251103651604c80c0c44840040180303800c83c400074086042220b08802c60314044c200301d110b90841d2004011035030406501001031500140f03c40700a40315100003070081300d91a8080d0b50103020304042d030891014800d808020960040f94619404d40c2d6030380080e08010b20105260b6440082440f040c004106181d0520145070b02c5402194010841200f112104040340c1c141220f11343c1d000250302094020344c1c01050b8222400003582410100e004000490b9400300800c0302c2d000740184a152 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 487041753 1250 487040503 487040551
    0x30e2b0209100506040803090102010c030903020607202b0e010f210c03050711164b090501120b090c12101a1f020f0318091003020603 59
    0x310002d10b0b00401c40d90745c469a441500740c07a5000404500c2c099440c04002150960090060100c0c040d4960f0280042da5903004040d9035600010703011443c01e21030081c45101480741040100c41c45400c0c042e0100c0b407454000180c0c0400d281520000003003092002d01002a0b98006150300f4071480c0904040101800344074141ba04001d03082c50709500719040941c4542d0403501a84514010700c01540c4801c650310111002990315101130709240040000c01c0c000701b10a10150040040d01d407102210b006107038004003029150040c80c0740d020180c10025170b9003c0c05150300641500700814030040305100c50b41c508170351143c005407849400703082080b44c180010304485051003194404500148205841c90104080c26520030b01c190441ca0850301e400c40c0d02010b90600c07a00510482d5000308480b402c4040c1d00b07001015408160660810b5101e0900c50a4568400f0300c00740c80c8560202d00242114042413040260503000540741c90340ea07001c0c1c5c000c02e002503142e00c0c2c12644d100100c4003812481aa01e0851 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 487043003 1250 487041753 487041781
    0x203061317191b08030c0702010e040b0303161a0403021e060c18030309180a0b0105090306060103270f0b010605070f0314280206250f05090d030e2b0209 67
    0x51504e280007042041440c0d15038054a0168000c1e40c0e1800b00c00700700c1c4e00f40070880c0e800d20021039142d0700500038010b08009600604480a20a4456044003030b04c8149044d1503400a450850161b0080184031080c80c1e580314100c401401c4a0700205603504150035a41100c0c030643c215000041c0381c1300140011520b08104440c0030710f40240c801c81c4401648041c0b000c00c10b8090fa030300c090050600e0f030942100e621820694049020080c09002903440326401907004161808605d41224501c4900d4030315801150080c000c418010384928038a02c1c100e1906041501c01600b04109000e0705105000100355210320724212143d05040000c180441c44201c250980a0600404002200d0b8070302e9040f580702048140b16408034980031104161240c229440c2c03061402102128605468004c50340d038284a01c1151600d204d5504021b440c100f103400110b100c81803046c2040e0042960760794140d6441c1001304681c0c03840008007a0b4500320914091f040c000040c203484000e44200c24010104041da5001c0c0a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 487044253 1250 487043003 487043057
    0xc15040b06060a0306360b030618011803030516080906040b0414010c0c060e060415020f1b0d0f140a050d0f090f0c050609060405040903020109020306131719 69
    0x120241c1c101b40c03010b44682411840c2840c054004443d642c4050b40d20f08a4060300b6120070004018100355511b10f6000d40407400310909481301c56490300130404440d24107a0307442803218044d40e070101d010318200c040b4610007900903128104001e1560f003040840b110100343e494000394000f242c2840c80e00c9605040d4402400d015003210103501e4441c0010209420a02c28852103200d030300140090300641c00340d182c0351503040b00c3c040c10006203800301d010304e514280d00a1032403412103280141001640d13100c05c042001e01e20844041507010712511102260003500204003d400f0f458000301d00b40d030100801c0c849005003103500e41480300c0030414061080356904040f0b41d60030391640400000c80a0f0410b202d6980d0900070556038040720100c08101c1d8100700085850403d00076140e2840d06103008184402010304400c01c1d000c5548c0c0315243d000584d414400503004610164290004100c24240b0004802c041e04481c21020700800c182c402090441c500615469000c0c10442a81080349008209480c01c0030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 487045503 1250 487044253 487044269
    0xc0918050f0f10112b09060906050a0614061b060c04170a0c0311040f05160f05070c0306180605010b1b0a0f06050a1107080c15040b06060a0306 63
    0x112801d03424000029103604a080500c01c80b665001c41c00d4a8030120b0b04001c5901840f00c070304020000902d00c03002c0e0040029071150a40d61100904290702c202203621400c0708903207050300da548030f1050101a006040d04500088801c0201901c2c2000c00f01b0f00b42e4101c890b0a00648002c00c5210424440c0e1b6914148003501105842c480d242460344480164007034014054518039102c07241e841c07054000b4038030f2119540300001d642200e04644030740003076a20f1000d140e948940c860140105d0f200c0301c1c0c000c850252851a500005001003803c0140052205020007030402000380410000b00c0c00f540c42d0002282c0e0050400034131402c04032040c5400c04980c2001070300361810708000107040c4020000a00002c021000c610820489540340e1540752002c4034000b80c2403030000e1140001141c0940c0c4000d80040c03407050002100d11002d40300040d5500701e80d600341c8510700040f4030050826014840802c040c0b02c6060720b10a50720f45035460508140c00984864060b0101041d00c40c13055000381c0c015006441c5507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 487046753 1250 487045503 487045513
    0x1c1125030b090d02060f10091508030d06210b0a05040c0b0a0c050c01171b090d060e011109060f090103021213141606030b060d02040f06080c03040c091805 68
    0x840b0800d0740e9801000a007400620420001405c2481d181203824007410001e00d010b1849444d1070160005010703040510240312000308000101c3c41c0e0100b00521202c0d0031070001085451604245451101c040703c03001c0c0c0c801880c04e000c10f00007180415070a0b1700050300400010f06488508001e0f4444c0055040380090010000d0b10307211442d000607a000403d80b0070030848001843c40300045510400113506130804111203800b0880030b2790700e41907044424450b00c644909214600000403c008164030041c0c039585ea50700090003108600780078140c010301e200134043d0326104014000c101c2c83d00c1448110851040b0100e03540c01e640e0b120307030111080c440c4050000e05c00e50500c01c02d0003000e0310700300504485810f80188140003101c40801c0380e4011580e8118240b0109140900c207801600c000008a0f5004404101c8003c00307c2176032014002030032007440d414580c2da00302800541100400380084030301c0c000038410400042c110701140c20030b40764a81c00c0030600c3c02511030080b07810108820002c3c0700340a9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 487048003 1250 487046753 487046761
    0xe070504050106091509060509090411060d022a0304030308070309060504110f011d0f010e060a03020c121201090c0302070b04050d02010b0405061c0c03080c1c1125030b 74
    0x112004c1101600c840b4001103880441442003a120364402d8070800d0302190080c401c18859281a04071740b03a010707008190340004080c891001804030b5002c9460040019404a0b141e01448088600141000e680f42c01443c81c00c1101103d040e13480c00f403407000600300003c4800003000c15200c1d40010500c00d030f20070000c0c44582070524004d19444000c08002d8011440303480510003641c451804034221290012410100319014002c1c0b001101005004905014441e1043c04c030300d03202c441c02080102d100340d40050701e5480081032141070a483c91000e000220040c031004c004029405070140c111210400c00103410100000180e010303024006004c1c0284100008000038043d002c1100d001c0005c059008000c4482c0ea0806c00c270449c3c0069820382e4002c44885440070560280764812010f050107690780c444455941c4d65284c00a502c0405254035a81201d10518202c4820500c24411070705031342445540c20440d400807a81d5a030b02541c02c60500d8000c0ca6281c1d100082d04081c0c0d20245030044051142450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 487049253 1250 487048003 487048007
    0x30504080a030c020108130b27190309050d240603050d120b0a030b01170c0d060b010e04060e0a0911120a0c1a070b09030d050f07020607030b060d0e070504050106 71
    0x3e10307502c01e0b8081080c03100041c3c0d14100440d8552074440e44094210115200ca00485401c85038607841c0780403250020b00b144040100030822000da90414140311407021003c2c2c50010001d41c0725034850f80c06500008542400500514814140c0045599010b10b204142c680600060001580060072602412140200443d030110006502509103602441101c00c1c2209008003954140320142c0b40d90900d10040c004045003050f92903482083d2412100c3c1c11241c540090202c1380d241030103d0b1516030380d0030200d802e960013091040b0380401c1242e04021407444c01044c840043d40041ca225034a5507501d0b41c01c0200006500b08054000c0e010700f500240b48e0010242658404901d501600d826921803030001c1d44503008203107040c0064251003a64100112a40e9059801390060202c840710300043c03184040300b010b5845910300c00e0078070780310314025030030150801303410411301801400c00c040c1000081d200d203031510422a03c0300c540c04135000074194002d4036420705001c1035402c1980e0040c1840c0000881503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 487050359 1106 487049253 487049267
    0x6020409060f08241620010b03060c0c0304060f11010218090604050f221a010611010e0c01050913051603060801060f12030504080a03 59
    0xa034a840c1604141c80080d0400c1c41c00482e41c110400089004000c040d86540c00304004506480388007020960048005140201e8a00a058081d140c98824004070204009601ca00d4214044246400340a0610610400d01c40d104940129508400500c1200d82041500000f0361500b03141042c03d842c0800306d09014401e01c43e0314030002d42c80c5082030004090481160884502c5d5100c0c003420004061005400503014515010030040e85484115500303800c54205a0300d15168800e081164400d0440e2400040c02c16142e890010002c49001e494203040e60000d8070340b00089102c0e503512600700c8681d42d1341c01d20300da80b03c6192002107502460080c80c4c042d00c040c25800303405404101c100140d81080d41c0d03000b5108020803024210913818452240034100c07050080c0070003460f100c00130040340041d0042d20b142404000c1d0107001c160040c001c840044c448401562952022800c0150040e = true := by decide +kernel

theorem cover : BRFrame.Cov 486870503 487050359 := by
  have h0 := BRFrame.cov_init 486870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 486870503 ≤ n) (h2 : n < 487050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
