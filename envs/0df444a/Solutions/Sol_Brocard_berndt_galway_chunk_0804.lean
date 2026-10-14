-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0804
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:53:37.45632+00:00
-- url     : https://prove2.me/submissions/e4e62e68-58e1-43d0-a3c0-26db2bc1a840

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 144424460 ≤ n < 144604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 144425710 1250 144424460 144424477
    0xd0c0e03070e06060a0509130e0309010e12120304050a05010903091403031c0c030b1e040b0910060305151f021e0a1b12110a0f0b03040318080304080106030c05030105060102070308 79
    0x10070032041c108c2d0b42205218007450340d4114400780da10350540a0014002441e034011103405400300c004141c0c0d1000c030108120880000c0c4140090301c036212410020720300b60803558014081e610349032008090540200d150700803500e144040c0e1400240364002e260300c0307000702d04044600c0010100300001203607654004c46070400c1c0c14500020325516220006100c550758801210010005444030420f504050290344240710f0305984403040c5090006d85440151000e10405d030401d079444012070b1458284400c14030a08000070011f8001554032090b01c5802c400c904910000352041411510855044503076811001d45400050249040591a01064080c2402e110b030799550400ca008108110010782001c202e50284441c0c0c01d2500c1200c0904c9814a40380c0c008159480c10b4082c104030307030028981100da11a90500d010358000b6060780c0c4040300402e80f5004120140008038011844250550004003200d010303600c0300904e241c1d50814582201e1042c0d51035801a0031140302440801c900320010319480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 144426960 1250 144425710 144425719
    0x120c0a03031e14010905060109080a06022b020309010b100903030c05070e090708010e1603060b0d120f1205011a0f0c030412050f120d0b04020d0c0e03070e06060a0509 73
    0x820301c0c00c2e00b01048541155104441e40c801d003006001d444458400c03194002000e00740f0100c01c2c0c2c01c03c901180e032803000c890003d100035000203030403d04a14840320220780090203000c401703122410300540c1f00690000c5400c1d44003981380030341d03280c490300c0d050302c01b2040c030f0340303140c07070320380354142151822605441103420a440900ca10440016140e6040003228840da800070060a00c0e20b0504c0480c900791114031032100c00c4c0c0c0d0b203c11010780c001643c01c120b804c01c80c0e900000000394400c01d0b02c0454100f40d07690720043c0c102c3c2500064914010b801110100c0c03401d5440c0c0d00c1e80d0f444444440306804850080c001c042c655000c0c5e80c045007150010700003c00031200300440e05410803e810401601d0f42d800b54004101d140c00301420b02d000c103e010000ca91040e107c60010b41f81d1501d0601c2d00701124001c0004080c0c80940780c1403003c540ba1140d904940c0c1180145101b0300100b5000c80c0e0180217520b0a124942c0248604480000c00c10b03400c0240318000d41d0700030003442c40c000c0580781c00c83e0b80c1d4101001c8545d02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 144428210 1250 144426960 144427001
    0x5030105100e10050d1d0f24060f0f0405010e1009050c030705031305120a08010905240f03010204140306010501021504020f01110604050a060f020403020f100203120c0c120c0a0303 79
    0x151b00401c00100740108424002c02c0c42c03443c0d40b080d2030708100703880100300d500c803218051460642c0e882c800032a41c0144280c070100c03424018000018940e080982e0582e400a29140001c506e080b060802d9901c90150048070300003880c1d40f8100c210407580121b80142064400f0310220701e10380e11502c02150090031020004926440f961034207800e14000005141d0310010018103100156040070310240105070440e170400680c03415501e64000155484100c907018800c04102d1466079480003480311000c01c0c00340c0210744460700e82ba000c00c3c5372840c40e203001e0700c0b9101d60b1000040030340c8006401202c2400d00d40000746583c513540c3c01d1000b0761608015450601c509450382007902c4904004042c0310340c0c098402440c1603142400e110003203804c0e510b03031000341c580100030502c00742e141c3c400803a424800c16a510041e40080c0c0328202d00310300800380703140143e164400a0101150280c1f01406680001c0f0003614070034030780b81c199030180f0b1180d00070305c2107240c00980000c400b013806a0300040300f580110540560 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 144429460 1250 144428210 144428231
    0x20708030709090c0801260313090b0f060901140f0702060a05030711010606140c030d060f09050105030102130b1804050c0409180506010b030c071205030105100e10050d 74
    0x500d0300221400c40008444103010008000c080c000c400150107107003041040c55040000d840e04103040726101d91040368402c11341d0310403c10200220340c1085040640f901303141e902e0310404805410b81c14441c03807045d08005c4a0304014504001103c2808905071100e00d445c0b400c80c84000c605400c03070412849150014008840581c0ba074074020550038100c1e542e025a01c0c90440b00103860f20f907040c85c0c6855603a150071002d221480e040400f03044600180c0c0c100301d85a4aa04461a2651041614210b8414207121000860103080c1c1940760644030003042c1884940c1c2c1780e109242c02c0740166590b50304250351812080005401c0300c8018189901045040c04a5094640108064440c1550b2030480240c0029007040040200e02c80c0182084074041d050042d0195034480d950b4507503043c0600d00369047c0000c042452540b0840407100d0690740409207190100580b00d01920a410903c140343c000c031b03910b49049003690311440c0c45103d4540010b0070b4040800030b10038104d0f41c50301302942e4240034070b03680c05410300b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 144430710 1250 144429460 144429473
    0x902090103080901030f050c18060717030f011401020307060c052a010b0301020c030a031d06040b010603060605071703090a0f0809040606050a0206070e0f1201060515090f0d060207 79
    0x1030185000c0e00e14196030741a5140018100e846000c0410308803440d080c10f2003001c0032060101e49085054040e07452a2798140e000060b180d115000d801044001c400106981c1201408007443c401d51844141c5011a030b40c0d4108050204015442d250043e0010806480000ca980d0710200c5466164a070103400c040b0a400c07040900068490444040410900403010b0710400f40504020188250029424141c0e8500855641d0003004406c1052645400720111b105c440b41042d0309002c040c150031205039003060705040c010312200b8021600003904104000c11010b01500854041c644d0102e01540381385a000b0920f03159130000f030641c00e850302480c0081008103881c0d20100c5001401150f54a580e50714410401007103810b1680203009000f070170300c0a121032a401080c0b0640c1320007542440e240c450070340c500051601c0d6000c011154003104204e14150b01800540c0541700f030750415070f00a0700e00c225511001d1130074000e40788083c6d80144032503040c1039141003034400400254441c800150a014139580c580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 144431960 1250 144430710 144430729
    0x30f030703020607052b0f06050103090f1e080a1d0a0303080403030e161403010c1404090b040209120102130b0f0418090203030408060a050708150d030e0402040602010614030615090702010902 84
    0x41d4506e074a84485441e105824403c800080c0406d0034200001d00540c1e94045008004001c0076000d03030810300350383c44800c02d8080300c4010103901c4074020307030b40380307005800a4201408a02c010004401100303019650f4101241d24070152501502c800c525907499a030110041d103050000c9420328020701e01080001c074002c03402080600a940d82044020b1406030a26084401c0c0703007840420001400f01841191040c41e04840c2548c2103514049034808094002c0b40c06445240381c060307042003c0409941e040b65041d409004402c440300c98200d440303030381d0394114141406101c0042c1480c4d58208020403500c0d10b0f80d402d80c048895014030114444125400107404e54200b07a00c80e00d65604848200500800e482c443c6036444452030901b41002e04140b1031000030f400680b403410340544010700c094001d00d070040214a420f550001c1c0290b50741d03515840024044e01d035512990300c5c0c83c0d402112844541c6000b1a05c288070740c41d030b4003440c1980c0c42804d04100e503000c400740400056540c0d40155030302607140d0a401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 144433210 1250 144431960 144432037
    0xd020c011e0533040e24090c0d0f03090f03080304060b010e01050a030e07080304031b080a03140a02010f06030c080705031b010807050c0321011d04030e130f0902030f03070302060705 80
    0x1c500c0030f0903005007110301c1640c0042060f02548c00070a2000240d603240c843e0504400d40204c104500c481107844e09403420007075130700800e100250469001040141c2e644c021846180b03e8074040c468802070100564040e211080b209000c91014030015040d180300c1e038060403040481c581190513035550780315118199031080d001036500e00c0160044d1103d104804088074001d00c0c8a500420240109890082541103045006003418000141426030305100f5003107812005d085101c2000380c3e59a81c500301c40b032400c01e0310800289024400c0000707901d00d00407440016003001403080050030b125003001100c09000003001d000034482c041c018503080744410006810141c40b900d844880d103401061a041000d10168010340c45415144002a074165020052640055050425080b0210701c0d0340001c900082038520b0102280c03602210451800c1c0c3c0c0d402c0008130701d000b90305544901e219103e60b944c49208140c0d020b0090f9001e034001c50390051003080101400b01c03030000303400749652416200444c42140b0540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 144434460 1250 144433210 144433243
    0x12052115060c1006150210050c09060c070611071d0705221e080d0f0504210c09050906070e040f09030305060a0501091a0d020c011e0533040e 62
    0x3c1c8407041c0c0380706200d00d90140403030002c45070904210039030003566050341035488400c0301c0d291004503840003460b1040c0d98410900034052a02c6100e4044981d41c1e81c8201d00c90300c2d001558280d07404050480c0440c0316425900240c3e10b10183c4803c0e03410074450b182c0094000400c011041001842c0850343c1d060f40040d00c00609002d0507010f20300003c4140d98000707195180361085542004022858000641d401001e40d941056407150078505400d0390180a907601c405809080c5500444240384114204102d07036119800c0415143d4448107000f00f21207080b15401110f900c0040440d5409010712a031021600b0020804220720048071005403d07500d501c90f003200444d8031801880414038142503010301901d804e19103410090b14280040100400c0e0846a4100c02c0c030004220a200c520350b01240c42030480714000b4000e01d0014035513042501c54030900031403120b1074000070402564041c4c07107107a500c2c1c80c80c0080943ca85149940000f2500700d00150342d501c0307035540001d968000f00074001420410341800c13 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 144435710 1250 144434460 144434473
    0x1209050a0b0f041b050d1b031209210201020a0323040e070e0108071b0f0b0c1306030605090109050723090102010e0c0d08070c09020c010912052115060c 67
    0x30300700800c41c0130160340301203140720081c1c14040341d110b841003100308541000710f0ba44031040143c14030889520640002c0c2c100500311f2007016000307412200b200c048807030030b02c12603140300390410002c07034108020400203005800c008070890129100390403680c00e83c0c0c43c5c800c804091104c80f0041d03402d80d034400e600c0300201000e144100080d00342c002c48502000b50081c28040d009240c90b40005149d01c0b503c11040da1042418180803007400782074100d9032240c035800518001c15007403a000646054101001c0f01c0c10303c004503070010607298424000c400131113001a095102a0f400c1803400c2c405400000e211108000d0301494814484550800c0e451092806220080e580e00d5114002400d4801416840c2d131660700024196540382c50b80448110704982189400742c079a026880c1c88401000c0361360140d14003d002182c0a40300309010b6004440d02d510444541c0509824281d098415019036485404550703002d54402c1040c0c0001006260b01c10218451840031f00b1500002450b950081c0007180003950029 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 144436960 1250 144435710 144435713
    0x60a181d010905060a03120c0503070c0f08030a020601140103020c0a060903030b041104090c030e0a11030712050c0f03030f0f03010f270e1e10060b0a1209050a0b0f04 73
    0xc686441c0980040314007803000e80f4092002c00c8800c0d01500c00200060801c200c0f48001600c00c01440d05426400405e8968a4000f81440306c1c554515000d0305034218008000091400340000460b10b2203e019006028982c0c038003500010180c5501c04480d052507001c100c01c0c40ea0110520050700c209205440c0020380140d24240241282e100e400c0280c0074520301400e980415440300184c4084039102540491032120030607080b40500700600d00d40e0001c4c030908407a80c003002000e90419845440c15003c0300c2d00d00780c0d00d802c040e6010710b4038200900340350400d44650200303003800c0b80545500d40025048034504426503003501d10036070142d42d680308844804001404401c5508040e40d0080140f002c2e9080d1400490102c1d40e00c45500c8140f00005a80d25811040482e20a0111141021580c3c001007400c41990302034988942c10900d00441c42460001c01180c01c2821070141c07003e05802e55100c0041c82d0089030044014501308005072114440e151a410009045c4400345208070044ca90b0700d105400d26 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 144438210 1250 144436960 144437009
    0x160f140307030e1b01050f1309060305070312021b042a0e04060b0c030a050a0309020402030f01060f0c0c050d020a08010203091c020a02090a051909111e0f060a18 71
    0x40440d00140451400c03031a13003507a03003d41a9040000904d02d45c2d503952804031140c0e404440d990740310541260900c0800804d0140128030710080700d02072290405500c2d1490400c03a121180d450203098417503440c08090425003001d82c885420884c045500c48410b02019108099080c8100e04820006103200c000010340c3c1400d004e5180140040d01d01c540c01c0c420502c114640320701a51080d041042404138441c4640c41c80783e00410b14040e009001150740c0c5c2000c0384100340c0c80c03000740140008941d213800d652418a20a01c650290a60010f02c540c0006041c10100a84013500010a991101c180800880d40281c2840111300030001c0030000c04035032440b540d118054020fa1400b030000c0d50448807050026841d002284d99001a030014001890b079180300216124507464000a4005890308406c8400c2106c07446104500c2d007012210350010304080254041c21040c0010450f030440c10613035900449040080190000c03442a0900c40b0004411021703060411000f980412800c6500b0985051501c04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 144439460 1250 144438210 144438223
    0x120102040f0e0606090d290907090c1b030302030103060b010c02030c120309060c0105040308011706070302130305191103070302031002090102010b12070509010905010b030402010f020c13050603100203160f140307030e 95
    0x1010400c00b00e40c5400340300315271512503600c200310300c85403210f00e1407040d244114140110855980e6452100754a1810018001d4100340800c444040c5002511101503001c2d48014181d648d00400030301618100c0c00c240800014008445403d0348006e00c21507529030b84483c080d00c040e108090001400786400c2c24010065441a0310000301c0269035a40c800c0707403a07004500340c0c1e4401100e0030301590718105802c40301d8815803103901c042e0990081506041c0a80040e0828464a5003c2c80d01c04031141c0c403910030141c41e040d640c400294594014888110b8803002500036062004050000080c1410b100002c02d008011702030604e00c84d50030500040c00f03a0301d80071000324090003c024041185605221000f811840054400703814032826a00034002d5078402c0091414601c1d0141981d450002b143c0f10003005401c044d602e00d4070034007400d0800c0d81001054800d5a12418507401d0180c0c0180d01e0000a4949110a82d884010440f0841050090741841001540251071030703600000e800c8130041501d0304018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 144440710 1250 144439460 144439523
    0x2130e01050405150415090302030d0c0e010201051503030403060510030f0c17030909040201051303050718111801050309030c060708041a0423030903060a0902120102040f0e0606090d 80
    0x1250f40103200100703003403000ea40c009900d1441d00142a1301f00d42026491400755031000450f9a0410b50120004c81e405801c21032402c8003a00284465201e0658524684130031004a513050741c82400200041803180d040f294000115561070000c464403500d0f102145400880d06985244680301e0401c001d0380007540c0760340a465460302550a0035241303000100c1034500540068104000841e105042c02c0086036124000d5030f200c0201c81c0c605985002d215510280103104d24031181c076148200a4807812841100e02c1400803440c20b0380c003003075000c0056915030000b6001d031110784002c1c000f0005c03c00c020001c080c042c900980700c0300d10900e00761400d050443d4825110b020040790020500000a501120548020300c40440c0284100a207062488ca54002c030805560f1510400c002d001305460380b80e014010f0f06000b40e5281441c0c001103900b140c2030748034034401c0402c1e00f0f20a590070011144260055500004000c0c0b910349005070308400104da5482058050356000c101005c041c07891812301200c0c00070f50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 144441960 1250 144440710 144440743
    0xd0f0207050106171e0303010303120f0504051b0111070e040c030807080d0b19090e0a0c0b04051f020c0f04020d0207060b0a080c090a09060b1c03030b0103050412030902130e01050405 80
    0x845c80c1828030340702c1c0410311008052240145542083e15a107130041c0c0703240c0070b03402c800304020318050a0940d518101110010000ba608d4603405940794410f480d04842c2039142002401a10b1520007910541500100f040c0c8a55500c0000800000d0b1000010489603000b022990380f9114840003070390807100e80c10720304c0e8030400e01804c00610f0402d401c00c0e0361084a00340c0e000050043d807035010700c9040100c0104020400c58800001190012140000d0000e0711300646841301000381c00107400981112050462002d80e00c0302c0d4442d811b61420795040810088042c0001d4240386030b17032252a00fa07030009002100c4003501c61042e4011400e22a19680c02402e60000420711500c942000c81c4106c1c60292124441607103a0544d5014410160070141c44032801425030f0001c4017401c0e07490404e08200620850000e814205210355a44c880e004450149030461305511150405800540043c490f00c2e10481e0025241c0315075800040d21171081c1340c21218144004660f502e01071030800d0400304240c0001040c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 144443210 1250 144441960 144442003
    0x309061f05011e050f04030501020c0d0201060f03080313060e031c05060d060f0b0907080403122307020106080d0309021201060f0e0c0c0d0c05060f010501050d0f020705010617 77
    0x140e070340000303c108560301c0c44a082d0000d4030b2841003182d00b4400d00e401d4041681c000a800410800154014581a8a40c0d002d54149103d0004101e0136103100d1300c103a1a00c5118548144041440c0f900255003100001d8503040c0e0040c1c06a0307030141034a1240e4002d00c481d070004074140c8050304445004d040100f003680c0e03040080703140c00710010728014031103840503082aa5455024141d0701c00ca5000c040c4900d00103103a000c1d01c0c0740820b80140303500c50483c0c0841c0069420340b051040c0198900480041d040350f1940c18095402904881840d080010050b4085640b00d510006403c0c400744214414100d807030381c020450309070600500c004000f0005c00d2000c0c03a0714021040205062010741a400e0300c0703560100b0400d5480340c0030402e2140c0940c1040d02e02500400c02100e00340d5401c4000028024490f02c181e070fa9581e142241000140402d108041c0811410070041c10481050362000c40c01c490001c9005007810b645849540c21108607400035810030508055124481604001e58031642078042c400100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 144444460 1250 144443210 144443219
    0xc03050a03180203010509162c0402010203070c14151903091407140a08061b0a020a150501140303030403050405060d0f020c011d0c010207030b060d02060309061f 71
    0x1038440c101210041642d034000744014521800c1c40040e010740c004000740618241201d44035210903662201c2000000742d0040024209141e85022150841400344c1e4015485900144180000010b002b00d046010400022000816000d204406012000300d2128845c84050500c42215058100d040100300140300c5031420100c100e18807040e03c969450003040c0d40d039440c5007a03200c081e90081100c1e103500400801080340d40c0c644100c542440804c035011648550f840c0c070400c2c2c440e40309550750b103544036001144800400820780244010203881c030440d4502c00154407143c01090541c0820100c55448000401c000c600b099200a40c00c207045028528600306581c000d0300d94070891183e2400303114041004003101c10304d680f0400c0000750321b881c2951b0b144408500f05000300070b020415214105007030980078400600040a085821041e00101503480c1107440c2c0e511500f00c001c01032a804084611034800585640d005180103e25110041000f8200700d0341c1c182400041940202040c0200d000401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 144445710 1250 144444460 144444467
    0x6091b140d0311120901120203241c14070503010c05070b07140c030903100507090504090507151d0105070b150102070b1c0b04110415120f050114010c03 67
    0xc06001222444400c030705515003561851102860034040380584c818045410300d480b0010b10002c4401da841440300e0125200080c102d02041c0c50100c4244d5007410201840068000c0c1000c04038030044c205012018080f00034540b01141c0131084401c3c43c596400c10f5801c280412405002c0c3c4821402440800c0302200024514000c2220180800e12084003080006000304144458856200c80d000e58606410300015965804114080e00a1041da51115003d40ca0317482a0f50084030507036030f0708000c1d503d0310b000c10015290001056a080c02841000a00a03181c1c03a0450144075143d15000403101c80e14114051603094030881034180b0034200070380000070341c0c08107a244c3d220119417001c0c0744480782c802c0100d1030050786401c100c009220008940c0c2400b44d3740c0000340f04801102c5028008441800c0c1400151064404624115501031209010940c641c5a1008030003095203400400708040075400800c3d00d03055410a09041c7d550801800341e08890070040819a10a080034403110183d036030000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 144446960 1250 144445710 144445739
    0x270501140906130e16030b090105070f030e01060f1d011d04030503360d1e05090324060405090a1104110c0a0503030115020d02030304030c0602040302060706091b 71
    0x2442980038901c0b809a030310840d0b20000c0c401e100402101c0c082445100c110303003001c5c0c05001c02c2e04c010071780d4000154485c0d4140621440390746640d64404a4801c100c2d420360103131180d24844a42ca5403540c0c00440c1071211900d42d0001480c080102400ea42429088041104010380281c1c14120090368012850410f610803070740c2141c1d00d41b0701540e0720382d581c0807030703054062845000031103048054045021541e2401440c80c80104c10405840c1c070401205810354031026641380240c491a141c11801c03041600a20203071400c20000f80a8500c0c81d940c0d45180c1d144006062506d00e4076009a506011031b905091041d1580006084014907c84000f9110010341d05038903030310103200359142c070010603840f0502400e03207070340320504030444201c441245801a00ea42090040040703460f0801000034003148001080d1007007030800e8010b035285440c1d9481c11601032403411001d440d003d4007000000f0058aa0000425555004a80004042180c0d01e8403540703508580e043c0104072081c140003480190b5402c1e404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 144448210 1250 144446960 144446971
    0x111b15060d080f03090d08090708100507110d0f020c040216140f0307050102070b06030c010f05030c1b100b01080606040e06030a06090309030308010522152705011409 73
    0x1030300003101880ca00500c5621404440043da08004024080002030004042c808014075032540c401503a284103802d41c1d514920720902042e940080c0303811042c801c0c80d40c405a0400300c0303442d10340112000c9105452a01202c4250103000900e01c01206045c036a0600c01054504000c403010b51610603c002407040300041d04c034001d0413225004000c41c0401004006040f04c80191354141c1341c54903200e0408034003d4100328815940000f2800007e21f4515021442c8128000141c480103400a80008211500e410080ca003a10802d010031000c3d4194007020b401d545619000f00060031008851040d002c190f81207007103010b052005000c140b202039541c0c0300a5405542e1400d404440580c0d174400080d10382010040e014003000d14284d500341c01e15910240c8281aa0701a4a41c01c03c03c0e641d0700c043c004c1840c01c885d81c0d01d049440a603002d4a00e500190840c01d0031191042da203040b12502c1e12401c0e190a104040d0204042c407908000008055143c018140180100c002c81640c010410010550443c0700419 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 144449460 1250 144448210 144448219
    0x60e0607080a030e01051503010b06030106390b0a0c1d1311040306020703170606190e0901060206090111070203060705070305040f08070501031404260c01111b1506 72
    0x850300c542c24402d83c003415680414000911140c14180c24010b00800640c808a000e5401d00d1500c1c200d078144503048034120b410a50314907002c1d020f46c4160041c1c2d0700c05110010420b1034094800100800b100c83c0c40301d40103000f22203054050030290403100c102c0307481020340070521202008444c0ba11100110f44580a00b044c2c82001d4140207030b089801c001c0400440d0300b0000751020401000303000259000d41100b42c032949075840c455100c3c14801d43d85074030407900e6070380c03080040187e04c44400a51850821501282c10043d013004980c500044903c28243c01500060f803000c0c0400c450301c003090156600c403c0200035403510782000ba40200380c64050003050001840000114501010701c15000c85008000e22103038810003588900c003c2e502c0d02614401c007170010307007402005c0c1c41030070002c0002d600460340410990580b0b800791030040041104007085c41c503100000d00016040500a0080506060500c0c03143c80c1e03140e407100c20340c0842200c0390080204075408400480e501c1074003508030301c2c0c00160884 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 144450710 1250 144449460 144449467
    0x10c030c022701090b0306060109030f0210050903030304151803141303020307030303060302030d03050108060f040201050c0a0b040b100b030112020a050a1401120c050a030e010f09030c030207060e060708 89
    0x142c00e151030101c080d803100c2c0e5107280c0c0d40005100300581d03010030354580f01101602c28545404004450455090001030311050038600341d40c0041c80c02d40113880c840d0307000b030070014200142200020308540085806482105014140c80191085807056010048000e041c0107880181ea8030001c110707501c2c02809440e4182d0018a400c1c0c100303004801080150b03401001c45001c0782c2c4914000b0007502c00e6100880c0070384240250305a403d406405010b0580701400c0051000d40e0b07a445100310304090107802a8144042040000c180e19018001c0c0c1c40243c0c024040600513007810b15110001c440018a65042c1500c3d84e80140708400292046038119840300619100740741c00ca000080c08492254170030f0794407001003440025407414060a038640b20800341c880e2212809a0806c2e80103030f98840030560000354041103003001c0503000707a010b4075081c00360304000a0f10780c103419180d40468880e0303030080d00403808404081082550401440014100524100b003070b8000850100d02e00340201d00700103040e0708022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 144451960 1250 144450710 144450739
    0x30e270106030c3603050d0801150507031206050909070612020702010215090c090a0b03160803091c06020d060509160915030e070609080d0c080304060203060a0f0605090f010c030c02 80
    0x2014000204c0c1140700f501d01241e070340c1d03d080c1c0da41d4a172060310313134021a6a000c000510040c480d400f24035018000d88901c0d24000311527400300da084004075840c0100542d078140104994507500c900ca440b40590f6401025003900346000640600042c001d4500054010081c490060341e01280403a504c00d82c0381c44043c0941c0390313100001e0420b0481841c45070041003800810200109580110306210425000d85195942865a00e44030341ca05008400381c0d648100030251480c201001c1080c055112800b0070100c14142d5520081640d201c2c0e061a0880c3e0384802d0184005c1c07900c0d89809402c41c0aa400a11200705041c0000c1c0402c92248100004400040a01c00d062806a00a2400d4010034400d0313420242d1108805030903e03003103018401d6544280e03440000395034050040c5d003a4090308414034900b1640c442d03941c2d01c0030354001010b25800910203000050402d4000311400068203181c1c1710039449503941000e00036000000da8a45042000841500d00170a422581544203a501603032100d80d0301417207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 144453210 1250 144451960 144452027
    0x4020307020f030a0302031608070903110d021504050f010c050712080d0c020f2103010b130f181a090412050c0a050f0714030303070c030e270106030c 66
    0x82c242d402c40c0b80400107060107540e9140d801144508440c0c41e2190200703900c03a004407000041181c00303401082400b4000c0c4040340142440d4031a0301c0e40200404008201540842c00e60342000e040d15130550400b040501140c5003a15101a07441020300e007240589030320761201503444a452003091b40140d0505c06640510280c9000c4030104183c6510502c1b4100300700d03000941c3d44080c117020813041e00602d070013990400400d14406c000c6d48400d05031542540d00f000103281003030340503200301c4a400c140301500194840c00901460010711300a4090b48c1c12060000401d03013615500040f9600380c0410a0100d02555100c2c90816005070b04419980840a5030341010f031454400c0d904494040d1150031041d0b0100480001d0300c044840c100003d4034a010b80d915244941407a14000c1603515070028000146042e12800701041e00350302a151030360703628200c070004c0342c10224034550550b9440c2800e89a5507c4520754540d103801000c052404000c1c40d00c200200520607200080b1100d101071481d40440b4a0240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 144454460 1250 144453210 144453223
    0x120503041a070506070810031419030809010e030a1202030402010c0c0807091401030215031003120f030b030f1b0a030510020910090b0301030b0a140c0a0306140f0402030702 76
    0x544415000368024803a2450721034100380b41c11605481014005080b417841400194000c000b5400c2901d01c450071035948501c0f40800e0001000304d4401e03c40464485c96140000030401e901940f10900541881d50300d107805d503072410f000c4000720351041001c00e0344950f02850340c00c4610000c54005849403242e100417035100115150182c209107443c42d001c18000b03c0440c0030341c102e49400c4030400080d0240e6000042d0000244000395000104102500e000400c0e44020343c0c0c0014107109280c0c03400c4d141d0b0703076041c0c482d101c0c000b0f80d1000820f50711000300c0e1980c141c421042c2024003100101106840d85400654650144500c9a80c08604240d03c00d0940c03074041c0c024000d0341c1d03c5010f4540740180d000d001d00c000e40182c0b5966124502906d0082c1c80d45019000030002c0e240000d101f54910380c00c540364042d5261001d8015010700e55030748145c040b4640003415980c003400e070b802d400c2c0f03035903100b004802002d0307440c960050100180050003446960341d41b2824144086c00540c1c000da201d07503450000768200407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 144455710 1250 144454460 144454469
    0xa0f0e0a0e090a060e1f0b24070b010f050f031c0e03030d0519050606030f07200d08160504080712020406080d030b2707030509070b1210050306040c12050304 69
    0x1070170011502203118002c200036034505a610008030342203800340380150649002c9402d01d5001141080090200c140e1491090b01119074040d01502d48842c80d0340342540c4120991044002001c108024081803800c40c0d04070240b140c0032402400750314220032260540b41c0c41000080103014441d1120768450300d041c02940da1450300030004101920b00048840181e40d900314000502c01d1030580010300c14980358055a000300b078006810885561004015100001c2c0f59603019260b0b4101003201c514444108154081c3c90182da45035000750a003411103050801c400b04a00d0280300c0300b41300610200d60009004001c4803001000c8900701d0072113002081c02042c1d00c0d00808114010400201c0005806402401c1024010340307c0700b0415522100d0002100020a1035040340036041004c03a400760300c640c0245802c04514000d80b4611507480c01c1c0403250b64011300718800e0720640001041034074160399100030001c101c03d4014048500d081e076141e000a07900c0b8010700041e5584564680b041c00020000d403000b82 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 144456960 1250 144455710 144455723
    0x60f0907030b032a030c0301090305121f0b0c0f0d140706020c01060b04140d0b040803060f1f1704050a200603010b07061a0109092703050a0f0e0a0e090a 67
    0x110b480344c0c06840200c6140c400280288030f01c0744170340c0035802c05102c0e0321002c1d50961340ea00d05000401d43c403000c07519809003100c0c85107040c0750030315004a0349004081009000744990700350f0760314071094058142061a4403890540e0011039440c2180303900b0210782244541000311071550f4030518076025000f4000c200f00c4c050b0a44c80c01d0408500583d00348001c0003a40c070400d40f400c0300f00c0c20040800a1180070040002c181c036110201050000308540007035604000003c2109541e00d82c008041888401e001e0011501003070b0030103907003141c0c68002c200e104411840202d6100c8918198549076618840804010201c000c5200c0349030030302c40440340042c140380b4020041d0780e8035651100079004076045440c05440716807400b1824040c240c00c410388880e89100607110000130a140c240d8420060140e805c2c41442c10421900c00031100195461245915103c0d44a4540b1040365803001080d07032129149000901c0760141802d80150340c4c00900500b1941d858095103000d603180701000d410b01d0003946004211 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 144458210 1250 144456960 144457003
    0x105130b1f020718050c04060c020f100503011406030105060a050702030f0a0b060a06020303070c02013002040e010506030c03060402340611250c051509030105060f0907030b03 77
    0x401e0307400300300c40c1e088411420b0a61000d41a060362041254415901c0c00c25241c030800c820000340c2e000300000e071032140c0001c2420908100840100e0107403105415030a00007140000103104840c1e0180e0f254651580c1600e08070b00303540c1030001140d2607105400101e000d101c00412410211341d010081d501da46120a001e07034100c094540f03046d6589c800d00b51041d030b120300740003030000c104030348000140ea11550103941c94201120f440c1c5c005580c0389021002840c91300e42813110785c40c075070407461050a101d40e54200707005995519081c10034102c00010b801c8980b04e0013040090000502c01403003030b242c010004807030040ea035401e040c1c1c032400e0040c828101489402148444030440e07500c1010b402c9030944c00b41c0c2e01403100c030840d50b4185016104d00e6900140f07c0c4e0103145c1110807031400b00074048800344101c000c1e020140e29000020a01d41030f1405c1501b04600c0080c00d481c40d801c0a00a16070000713070070b450030180c0101f00c2c000592803050007081001010742e40c00c3d403d115a90304000703191941c040340d44004034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 144459460 1250 144458210 144458269
    0x30d020c130b010807200714100804030804060e030403210305010806010503100911060301080a050c150702040c0c080a050703020606090c03010b0a020c0613030203150105130b 77
    0x40364820581a20710482000c4000142503440e40595070364440c05944101490b602c41c0401c0e900310400c4070710903141c40c5180d12210100c20b005c00441003e00700ca103140e04200d104510070482021040d01a1700d01300f000798800e2100181c1c0140320150013030350080c0003141680041c3c032018a540610f5001411010303841629007000036444400c01d585103140d80d014405681c951400340e81d80c49003031042e207400d64400420a500484641d11050105105100c01340741c030070090340011096002a04511a107412038440901004000c01441019a506480009810304200c06000050180c404007134040d90b100d0543d591154469604800240d902c10181502c610852000805c20b80000c1c1e0220050301c1a2800702c1c1c0c02d85001d0400318400c0000b4107001e45540c0c01c008100c2c4907a0844a031040075441404002ca0042c0c0d00c29005e42001c441100c01001001e2031030041610344a491094240b629000d40c00502058681c194840c81e540c400500c00f00b41e081245000c5030112210380310815840d02408039001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 144460710 1250 144459460 144459463
    0x110907031d15012304050f0105030f150105040f0e0109060e070807180c0212071a070f120b010912060e0f0d1704020f060a0f0906020106050105040506030a0209030d02 73
    0x55400050030078a482003958900c680d40708054107982c01c411020030010010108030301540400c40c00e48450325401103600401190640e442503d90002c010718520050000303080c10803920303581c111500d0081000d0000780c09003481001060151034056900c1c0c8050000e070011035000410342d421000d00030041c02020b41403101c02844604c0302c88080b40911754000617000700000b8044159030b980d5003014400024060000020402c000c21b003020360007038201103000c512404018004070380c040d01550182c0d200300c14041000c500c001b082d86080c800e42210b050b84843e0b01a900042a101c2008001501c0c003503e401652100700c036500050130001000090f6081018942200340580040c000b01c0d0401c40c3c01d10ba145850b60748091141c0c00185080030741603880360380c8104407500140050001c00400090601040301503002d002d1082c04110b1001031641011b0b0720603940001041284000c000e00b50500c00001c1040c881d038401c1030710410000c40418040c81c186d41c12585400401804ca48030751030303a040080e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 144461960 1250 144460710 144460721
    0x40f0b04081c0c0f020304270e030a11010c08071e1101020a030b040f020a1b170304050615090105030703140f07080f070b040e01060804060e03270d0b011211090703 72
    0x207000240591303407141000f900000c20784040d14050349446a44118891040c040e1014041c0c5c03100e401e548800303000482d42410301c0100301d102c5055503202d0b03903040000001070139030701c1c03405800041005038410080043d9000036607804100d101c403001c5001b9400c22008640541040503078450a510000e0f0032882590540c0c810311506500392014481000b051100b5012805050414400306e40c090142000c5c910141d265803003d14417642d0540b10389004031809040b0b5800c1106d040f25030764084000d08c9480e17810b040c1d0300300004400310381c0a00c866040074007098880119120040c8400c14240c00d0100915080c00a161984081000c84444941c2d0350009960781904480154003800342c0c000104542c03081100b19000d8030400060250507901e412411107840c10010001c1d600d4560780c40117600030080900040a00440e001451070780154140c0312014041154015640b08001419036400003480c40025141110728031040074a0800250401280d880740d00c6c1c444d664031000e81c07810050b0054155011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 144463210 1250 144461960 144461981
    0x201020a02150a080c03090c100c050a0c0305151b070c0312052101120201080603031308070603060503010e191401060602100c05211009090501061d040f0b04081c 71
    0x5100c082d495003c41c5c1e00e00344c40151441c4105421250102c1c0850a1624603100c440e03080740741c0905800c503d84c0f181820f00c08140c3c0220f0f0403500c210350070414841c0401065010b0501f0388981d80c6142050f4100e10b40501d4410ba8005601038040341140510405603207040c003c541141d5000807801d80501e00420030b034007502d80101000300c5400401c50001041c01c03071a0603100040319801c3c0c0300b0081c0d00152040c5200900c42503047c8820030101106220501c1a540100400e4005144950408501070140c1d00329405c100c1c02a85425500c42d02e41d50009042043c00103401141c072800300887c1055010648040d41c40314040d0f081050019a1590004090540c014420010444020b10400442d100c1c452800100000f415025030282d41c0d9043d01c0a40c0c1c0c01080100c0720985071750781c501420042d2841200155180e943d238290408c1041c0384500b00d0542c030300101c100b400017890243e4130a075400885d041c018003120f8003080043e00f004030f00d4080342e81c00303000405200c3d0148140401c0300d0152051806 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 144464460 1250 144463210 144463217
    0x102030405011404050307172a06090a022101230403021c0f120f061d0a090c060e03010f020301090b0a0b0c030405010e030106050a0f0603051e040209040201020a02150a 74
    0x40383c001080402c942d02d8000d0f54040081e514201482e2100d25404400c05507010300c1d010100406417018803440c0840c16420080448804580d18801c84903040250061028241b40c00a500380c2c0c0050b9201900c0132000c002000103104c0312105503d0450040c0305040c01c0c039903540c080070301441d6158051400b55105034402d6003200d4511441090041607944030051040106145011460b51203005014101d55600d0712100004c240c5603080c1500142c504961120198440e000d25502000d5503000445500c015101c41c140900c40040d510801405180e20030103040003104090052566000c0d00300c0c0c02001d2141a0a54517561107002c030000a00703541c0910751045c810414009004a181e4051f0307443c490050000c0d504041c903150043d03c0104071108601d925560b0741401059583d15124500c01401d003000303080e40118102807001c0c04803180079181074095040c452101122900c01007181e0f5019038141da2840d40b0342c5507440103070310301121020000d40c0000300000081100311860064245030020b80e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 144465710 1250 144464460 144464471
    0xe0102040803070f0c140603070815031006031a10060c05030f031602010b030c0102031b070801020a050c060709081c0e090705090f06040503070e0403020312010605033301181205010203040501 84
    0x80c50429904201c506c400d8020030148006040300d8010001c0c02d9104c0b80f580243e15100a41e0800a402c001c0758010740d090003544c0d100c0034000e02c5080724801c0c5514105c001400c51600f42105d0f810b41d0211544610401c004d100352502007000b50600907620301c4040194025102d0810f45400c801d032001c1205060015032030400035141516002030351102c000010780140d0300d09450321070ba40c100424100c0b80000944240000001c0ca43d1342440241200341d81030b51030741d458000610320542401ca01811407400c0100882083c440d00030081a4040d00807203010145580a404d05c00c2076503c0c4030314403901540301580100700720345a07400030001c10a0410849804d8100c180050800185001340d0040310f0705603201080501c5585d51303d051494000380640100d0b0f0610568403000328588009030030032400100007100f402000e42100c0980380002102c0d401d40d400c409161030780790703152044480100341000340041c99582c9525008071104042c081c00a0840c0c51103501d810b0580c081c2d4410f4030100c40c00d61a04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 144466960 1250 144465710 144465719
    0x20c10020c0906130e060f0403090e040503251e050d170c030705070c030c0f05010305070f08060a080a11090a0b060d0b0609090f04030305070e060d0e0102040803070f0c 74
    0xc6980c8401e14030050a0801c0760301c0f10b005008061403203100003680c0075507451225407040010003085106e0018070040b90a40d2500b49001840b881e407030340c400403d98811030207000c0080c0b80407040d914003035403074000300c0040c41a50b0001400414031407009483c8161580710072030101294413101d41031030301440c00c8501c4e100885808403140261b00c03948100640254020618881100d0002d40c0c102140b881d080f424240d040d140d8001240280d4021a44004094002c00028103407000020061a09007010031081c6000138002d0024a0940e0581c0204000708000030348c59640c8803503217805404980e0469100440c03501d415a81c0424124040e0311400e00f1100040424900c0c2c0102d090005014203440d080c0038601c2c040b603028280c90984964000020701804c04252240074990740314032405103083d001824682400303022902d014010030b00700314201200c203180340c407000100c400000724228006511071070403180c0d07030082c0a5500320340038a000c00180d072403d101000c01d81440d641d014540b8281201d60f40d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 144468210 1250 144466960 144466963
    0x41701150f090f0609110c0c15090907090e15031c09180f0203040c17010e0c060904020f03090a030906020604020a05010c050a05060108160911030406050c040f06020c1002 75
    0x2034030880c120221501d40a104030400c82e080550500c5507404082401c1c0e4850682e2025645c4590911105040100d15142502010018009031003000d9822400400d403121040c0c1030362094814450081d11420041401d0f1842603547c040102202c1080070f5041c00c091045914407180502c0c10384c0f180c07180ca41142e01c848010790716001000c1e019158201002e150006c021b0040700340d00e52964a00f0366131204130b21f07010198002503124510038016814258245091410250300505107010389a150544034007202d0307000032304c9101d60320040f40c0d01500d58140100140107445914900c3e41c08803408024042900c400180740034205100c0d40f24181e02035110301e8120703030350041150003941c45020751008003c0c65004002341764155009500381c0311205540e031581d40c81c0c42001c2c1e00a0b41250702101c8803401c1030215641150180c000b03101b0511480340c41d03489601c4117000281019160380d03a030b103001c079041400010850f00208480b000118009a88036800ba4444141c85070482c0100002c8291242e401e20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 144469460 1250 144468210 144468251
    0x20447060408100c2d03050f091b0f061b060105030303090d2d0e040f020a120507020c030717070b0f0d0b06040f0b040329070305060f06041701 63
    0x140840200044016121110003900c1803132550b03418014500f0001001e8a40d40c0a10081c40807002c1c1010f100f9010103200030304544005108104424039241400890400440c0906d01e648010b50503117501041c1c4c8000400000803051202e40c02880000c0241d507003001940050600700301070044d9203144c0e0f81d810034143c0301e1104555030a02074016402c040744541c02120304402078014042080741c10500e0300140318400081c8407a070400b160004861400501c0c05010752012586000415401d10034980c6014107031445a041c0b207840720b600c880025998610802c40188101c50043c00c0f18901e036034610009014051b207115202140c01030100200713864620070700f00c840d03c00010640910b00040c501016000f0309121740e04543c0310b40104030004104007103a040d00040c0c5041200b4035030700d921f54902501050200c088502d20901c85000c40d00c0c00442211240d5446012070034003080ba661001d000585255490740c90300c0e07201d817001c100410002000c500d00441c020001b8000c00040703050b55000c004825 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 144470710 1250 144469460 144469469
    0x8042706090b060a140405130b0301051012030806040b0919050c16021309060606091809030e060304110d150e150604090312050a09030f14070204470604 67
    0x82d013000800035040c41120800001200d09a250b403c20741c4910025442e0070900c4100c0b51000d45400c0120f8041c642032164580154043c182109081c0c41c00c0c0c60a4100c2c0600e00c405400e00c0b1030200014032a4440303421100c18288010100c0d07a440c41c0c004c4070041040320b4100440b41236890880012a1290b200d405c40b08418038454040941000950801480700c030307181c3c052220076860720171002c00100c2d20b02640b4041c2c402c0b03450b50701085003818000d0041181c0c0d080b100c0f1441b81048c09140110303401440c0d0030b070552016522207689039501e0601300d04242c02c104203d50089108624401445a9040601010300000000384101c900f030040702c5907036440610007031600c2c0d494400403a140b07207000c0d8801180d951103801c00c0035840c134564940100320340040302c0c0c0da601140c881ca041020560300c0b902c6803854454600f4040e00c40f58400c00c0e40700c420702401000900407030391070115100c9100a000040b0340c42101190b1400400107548400364040c00c201d850030f2001d001d004e8800c041e4540301d02030740d0980c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 144471960 1250 144470710 144470719
    0x30c0e10031a06031603113102130b0f0a08090f0706030b030a020406080705150309031c0b06070c030b16020a02040f090503030106080709120503090d08042706090b 72
    0x124044000284082c00641102d41c144184241c1c514070360282c0011000640c00785001118000c4410240701203011a038580300c240e100305486811940f22052070b48800d1422100005031502b80400802000310240d40003d41c0500002c07820b01031205402c0b0041a40c0c085036950348180f6100c140760075960301c000f544080c0258000000500c8020300c41e6000100151004040b2050628a9004641203400359045031a4681103103501380084d040503000c0360440c520481c802481c1d440c00d4540580c8901954402e10b1500841c100406640b0b03169810080c003925000b01165643d000914058800c0c031a1848103c84111161300041c10181881e01034405050186d0060300c9580300c1a402c000c000d150315000c00c070005079240740c0039003c00d504101441c003810b0705881c0e08184d414002d4010303001d210313a80d000210522082e28000000f07000881500d20400701074903005118102d500c0c3c00d401030300482e001040078800311a010251124011249144440710520030808192204030400035030308201d8030113811 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 144473210 1250 144471960 144471983
    0x30b01031406040b04020904020a03051f0806010e0601020a120804020f03010612080f1e221a13080d0201060905010b03060603010b07081c02030105030f07050a060e1207030c0e1003 79
    0x2e070a050308007443d0400c00410051619040c040000c040340c1141e2180700000c2d5603502003082d1900010b0900d80740c0c000a169008031540f41c00e200c40e50390301c01405034409048041000c150300f030b4002c000d2841c0040d84840592480c3c00c003010021303c0c1c4102240c043c0e03c0760304005000e00340d03810180700d220103856030420005055105a20b40100650090420120f928001c1080c21034619500001001c00030b141c2d6000c56542081040d0035a4440007250700031051480714174100605154145200d881440e14003905440d440841c091160036541607001e807860703004011007110025811752124080d01c2406408004c10390b210001c1041902003241c07a90342081d0108018848c101c040c01c054891584503480c1c5130f1502d580800c46581d2443c1a008610005401200510191030188011200710704040b0060a401c2c2c40c040c00030700354030924810740c2e003440210030b42c420312501c2d4410741402000c0458100c90a195a925000011048900c10398600303158290100321003000d04a20141241d41000390b0005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 144474460 1250 144473210 144473221
    0xb0610030e07151202220f0b04030b09100e061605092b05030d020d0b09061e0d02030304230102030408120d060909050601030506060607150507050c070305030307030b010314 76
    0x800c040303580903005008021500340a02c910038001403100c0481000040030ba003003500000000e1b00f40d16004042d003a124420709021000f0000c00b0780d01141d42100215178607844042c002420305030000d2510180c98204502c40c0110381d000109140207603000542c01205150b0040111240d02400c529298440c50b02402032100c00d007007010403004a1034094240e0501142035031000d02e03603030102150750f000e550040f562101d182210303c108250104140c45040140c5000000514184540c0100516120101c220fa101d151141511a003009a015080701e941d141c4414800400341101e1502410035184035800c20000d51000c0141e50440c0e00200090400c030817100054151a0040700292044507640e603030000e9100e8150240c0e24001d8000c1001d02519411810001e08003500100a9800b55404000c88000a0482c01c105441d607511070b5000140d41d00c480d40e04980710300c502c100b500884c0c45820808402e02c603001c030003140500b1940e1400c110b80c17003c0740d0056056501000365080740c540000c0c00110b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 144475710 1250 144474460 144474479
    0x20609010c0e28060804020a050603010302010219060e010c020114091f051b04030f020907180918120203190c021e0d0204061205010f060e04080c0102070c030b0610030e07 75
    0x200c4010440c542ca450620b240909000c1022144d0120000806010500c01941031020900020b8041079921914660450b00040c0d6101407080e10030840084600c3c4000a101550340041c5244003c94001d014222207090001d01070b01d25070381414264400b0300c012494407500058a00c4c81c1c80c844041c10614900940d01075001030500412132a40a580052902032615200d4001c01c00b46200740b0344c1c2c058500311801071141050700100f24506000c0c80140c6603410082c070f081640111100f021000c40c480c03c28214803490441c200200070282c1051822881c00681c012000c0c0c900281c4000340f200030540d00c0c20045488000c9890080c6d003104668840512000c01907028848071040900119184940ca41c081022208990301035a091203400401c1c0d000c00900b0f02521070541b01e15982400103c0c24a00c100c040340344c0c0030f031009150460001d0600000b85082d0144d410040e000f807404c61b511640c9003401e00c0d160008407281441400d0903c1501d001070302030f1003000c900501401c0140744d040c7c01c5c40c114030b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 144476960 1250 144475710 144475729
    0xa12121b0203060f041203110f0f040801020a0306080609010b1f02010e06040302030d18020303192c0a08030a0804060b220e01050c0a0206060402030a0216030c0201020609010c0e 78
    0x1244400614510030025031400c0146900800c02111041000e2030f01d410004258086901000205401c054016030030f41050415607040300d00c0395400c0c079628140c260344020a40715031351100203a035001217000e00311590543d0082d012617000760140c90140c0c0d0b4a4804500700d4081d10720701079006140fa05144050800d00303550030700f240c0860000240d154110303804075140c41c03002c4400f100141d000041155448210b070141e000c0320062100348402100e010b50010343c403801510b40401c4401c2d8000522103c6501c1014210006004251504420600d00e5600054440034401c41402142c01c00000961140008215544c9460175a108116500c8540c0c80340003616507000160350102d01074015503103c4441c2031104900010700c1100003103100341519000e081d20f0000306404020741c403d000c024581070300850600e074002c03c115001a925a501d0316031134000d009801282d0f17159880c1c0e0009a0801d900421101100c500076002c0312015030325816601c0c00c0c0c2ea14100214000b496840001080d4146600390 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 144478210 1250 144476960 144476987
    0x9030305120c0d09050d0e010e01080103020d2d0c0f0b1b070b0c071a0c06070e03010f02120415020f09151b06011809111e0301020c07050a1212 63
    0x1618900505500e00d0f4064824242040e2190741200010580042d0059841d0480301028202a001529a140003a00c4c2000522011780555004e16544041155414640d11440c0000480003440c10540c0b0726180005565801150414402c01011820200c000001001c841ca401d4007145880490400050503400108401e80188a40307040400c031034610501500c001420740e0020a031003442d0410500c103c034108a0002611041009261701c22314000c00c049a012003242407031351070300d01150003080c0144980c40078003030b401c1c0c030118101c80c0300e4260440b5107024038002c1c0300e90001560101400401c80c131a4001503104500100019092802d142c081114400700408005007010000001069988124022440030360000380040c001c440d20020041050541d1420400010b00690741d02c00e4072400e100c10f114400c20342c4a940080038140302d103100c0320b040000f800940d15018107104459403100b45005240c03040e81c8000d00414211800c5500044d03450704898001000502640c060310a030f24031244 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 144479460 1250 144478210 144478231
    0x10605090d021309050717120901020309010807020c0d03050a0e01020c22090213052e0603050402060903010f0606090602240402060d05090a060e010c0207060503060d170304050d0903030512 83
    0x20703c0c40442e50070f000500040450700390b0b01f00345411495440341051080030004c00f201c4c80074018032509903400401c1c0c541c2c4078804e081030a070944074a001030f0300d0000012251036110420a075448200359021010f0000180f071900c40c19450b501000c01a0b0b212044003c2e150382211414100c806e008079410001d00140442200c0022030007001c1d004a68852102e400c1c500f04a40c0307030310500c4010011111000042401e1500c01009404001e085101c0d00c00107205146c2055103d2001c58203540e5110100d880d80000100200a000c4520031480064621481544082242d03400e000901078004182021343c1007070f110408009100010004032402006007050741c00160910603481f16075003c0c4200c0c2d000c0c00d281d038028080111a40360040544443e92003440f038990515101c00e20054000030400c0c01d981c501d06080b5101d03904c0368089065011030302c01c0034240c3c0020288140140140c40015401540038200740c3c1c040f0610000700f0313036204020b071000400060713007040a01414090400041d401046820 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 144480710 1250 144479460 144479471
    0x70e010e030c090726040c080c0d0305030408070204062c01080d022109060c030d0f060e0f06010516140d050403081902030712030c080f011512140717010605090d0213 73
    0x1120481741d020111000c072100c8003c04810b20800c4410001c40c0a41e25040f92500c594556640c0e0003402400040c100074000c49000c40e80764111364540d006000130706003240b207500511103058603d03081405203c00624240a4140c004184030001043c241001e41c11a0010b0440c0f12000105208000d12040c42002940050100000c140d031a04010401c0003108801562103104c0e1070494001c4403560403050011070b140c5101004103100d00c85109a0090341c882d402009542e078840160b035203208050010140840c48602c4400304650015400045080c00c81119526001c020003610303603204501020b0005035060260b05015210140850407121485c81580d050450a0740c465080c2c80801006601094903098000581d60380616440c0d0b0100c400395951040b54503010842900c2c896806c0c840d02080204200c4510b1318299420210111080444a072100d161214000300006d88105c1107a800c90801400021114440c800342e540014004003904600282c9a003044038181a280407883d18a4444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 144481960 1250 144480710 144480767
    0x106020c09060f09070f09050a030c03030f0909020d02040815060d020d1401050a240612020904090803040c081005010f12030c0c0602010e010c02030403050604230303070e010e030c0907 81
    0x2c09240d000b400f80d034461a101b4150480007600e443c076640c101d43d000d00100041080414a17540304030046a400d41421051104082d44c2103580c41c89030f800012045000241d03000c0d121410b90300070001c0314800c2c4107413000e00d950000c138030b12801c0083c3c80d001d40c0081d10f008080c001d45000b0148038030492013161114414000790b1040d60a5030422a8250041c0b99200e100c00f605555882d99561000d0034901030013207c07820120060050b40400b1100c1a00d41d901068544181d02c483d031007100800c4c1c1200016450346458500702e22aa4824020521503010740e108444011146014490503509d80c1c11503900340f00e0034600d21301c0c8510301d0800183d0070403100000c00c101045c040003413500688403c3c1d00101d0324030005641c460958030302c15541c408540c01000200082800030551640050b44a200e000b01d00c09901c02c00301006030f10100c60300860000200344a1402d4000030410b40032a801c0e2629020441c010382010303110001c404513039400170f00c6400021107007072040c10000e0490a40301aa012a200708 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 144483210 1250 144481960 144481969
    0x103030210060617360607030c05090a2102030709020a030c0c0f0b1504020307030b0f10021c05070b0a150506030c070210050c010c020705090a0203070c17160b06180106020c09060f 79
    0x4885e03456080e08104180403c10307500d406503c03007800150806600d0492140046114032600e4445e0344400221001c40701584080c01e4032040300c0d00c1d001412554415210100c0034002c4d800000c0450202c0d141180a0310350034054210b041503150099045900f035000c603250402001001060b80003020324400d84840c5a40d254405540034015582e4000f036001c203520248598610901002c46c490155980c2e689003440d400113060102e482c4440c4002012803101e02c09642a01907044010122541982048020215039010110b0310903020148607105030303960180003442c8000e49004101e00740401802015041c0242541d2044030a07250203450807000800301400c5035200842800144c102400c2002940382018110740c200103130500c21859800c090a0107007032104941402458030350802d01c4070712401e58210036200682001788000b801d4034840c0c505042c003a80300315046482100000c4103680c282c981c45034514103030340b440d80003005503200d02004c00003001401421329601c441d80350308101c00c50301c030b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 144484460 1250 144483210 144483301
    0x20d060504140702010e0102030c0405011d0604061110060308030a051f0b04171c120f050a0f0c0e0a1211030102070809011106090d12140103030210060617 68
    0x94128403280d83c140f8034002425074102da0400d54042c2c0c0144103012070707154060101c0b411500c01b400d000307418440c03049181200705540b1001030380c40440403900040300c9800955452001c1a041b003a1034074601004015402c54445003c0600614800c0c80051490495680590703003040001c0510038690002da215140c40c0303c610b410041c510000410304020920240301c171840c0000804029101f0428044c951011040c0032100c8070040020385120010342946070b81c8400901c054980040c030551612400300c102501c1780c0c03040c420b4418949542d8000083c400d90748010381c080024001c5520510303003080d0b05201d4052201c1540c4840f42c404508003e65000d10003090f859100d9401141c442102000140122141401c1c130612030f046041042404040858039014503120f03420505130449005103c10f0061540824000400c100d101c0048181a0002104400040010014000d603521010b044556004034501e078070030341d9002000f0825441e03064041480c100624001004800394007401c250103840c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 144485710 1250 144484460 144484481
    0x14070c03060e0c060c030d1e0203090a020a09140c0d02040b120f060a12020603040309170708010f0b0906040209030a0506040303150f0b03150a0807030b090106080619020d060504 78
    0x280c0d12070280d201a10180031002003424221074440c05c200e40004031945912542c03000c0391901d961050402c0c8000c1452004a4000492520854503890130000c2c4540c0e039442d988050b441b510404c07000051406c043d018004800240052440d6191180d42850305140c1000e22210840b94081c400461145490f00151010019420590380103080c681c424084000c80640114020071190405014083e1210070106072182d05039001d03603403540d460504407600e20203134001c0306030600c3c140d2607246180000100d41043d5201000200302d00b003401d001104c101c8886010046c0c100b82d1100000b000c83c40d0079405480c1e084400340581d034103010360f95605410305a048a044020036a5104041c44011092000102816002e0508503a20707040503032200b01030000400c410b003d2140d0320031b4400ca80e103841d51500004c0022000305d50702d00d9220b2800401c94002200d40a01561a0a02c009089100014100d00075602e01d50b40100010b071001100020358083c241900d121b6071a0800003170692a5407003070a2110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 144486960 1250 144485710 144485723
    0x30712050c0f15060a0e0c07060219020d0305180a030e04060b030f07021507090e0907080706030f0e0a0f080a02030f07151b200a020316030c0b0f030714070c03 70
    0xc065401c5101041c2c180030788031174002e05004a00344207004440c1c03002900180c02201c0303a62102c010785402c0740a4480c0f6504030111400c080241c2071000d4001440400d2103120380c0781849550744110082d00b00c202400304e03041c80c0f03070b000801c1031010a014500c40c44c40d5040c050310204140391204241c02841d401681d1140740e5030035600400207060f9041c00b000d4440e0840c124805035a0501c0a001030a8040e05e0003081c40002d003940c0800e003840020080380c4005c040000070380380120b90f01c107809002442c2502440c410302d0305003c06d00001d094007007004030740b103680440000e40c50b41c1c01e82c0b030703614080d08810401c03c19072104204c4c6681c0011918090b100692103000b104405003c18602c02c000d0b500c500340c450601100d618203090b00260030034203100c1d0b011249180341c01015004c1c04141d1801c13483c0b5002a4250081034a0080300608401c00c40703003503a010301c184601007551040c1040a134421780c89002082981440401c503001c1c03240c1e40c511649038004203154140080d6407214841104641d1040700d98 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 144488210 1250 144486960 144486973
    0xc180405011e060306060e06030604150305011d01060305060703090f21031116080a020109020d080304020906060304030804060b040e060a0f061a04090c0221030f18030712050c0f 78
    0x820029400000103040350b4a405d2203000e25200000d4401a004001d40d40304000200c000f0b84203455070b6000105074000540e0f803041181d80c07030030b000b03000306801c072582c19840c565001034281a1703805000300b8040740e40c008d0090015580305075040340102400c100441b21040d40c003211001054200f40c1e0a40030a036100d10103541c540b5001000380484103010181b503044042408104007900d0310251000743d40e03402c00f030a10b6a83c424464201d00400102e00001c1d407010009559409010407100590b00c101d01c03e564803291031700c9000c01c1040d54003040320300400150440b400034002070929003042c10500030282c0042171500400341d0007414005c0442c1d49003509981c034118031400010b54001c0344000c02c4030302c49880c81040c001840c54114401c50050f0f95400b41c556105951161080144a5900c454110482d540002002c219101588280c84a14101e4604004a0820b0703070780d194078050000c0107500445c41c203882a600d004c94100d0003007400d014002c0038440400c50305420700074140e03034070a130102078180d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 144489460 1250 144488210 144488249
    0x20f060a020304210b07080402120106080a02030c01030504020303041206021e0d0f20130801020310180b0d0b07020f060c04080712020d032a03082406030c18040501 72
    0x2041441305070042c000868a61070040784040700c0c070b00c0d04401d0b545071524540c0c0e11400442c207460481ca00340640c5621b80b0b400040c200c43c0100e20380d40c0c0e040c403c0302174580c4141030400440588806680103981034008002c03c0041241188014086510400f800b609100c00380021604040c907020b0701041807403000440e180d80d0f000d1442030002c400612001000f108100c444a801d0381007c04451250074140007800c0078000e200c1015940060038101c000350340d01d00e0030b0043c810514101d442004a000350580320114a03c0d05801001d2184c00b01800c84001c400868561041e844800b400d27000550080310000d101c822810300c040e0340704220200c00c007a91180384c04041071a0094030361048824400c40016a801655040001401d480c0c042c034044140440d082d610441041014000b8800a45420042810150072110741d0b8070451050100c0c88610b403207094508041c072171840042d80c2c0b150040000804130007035034000e00301140800c0c410b04144140315001c0b030201c0b04280c11008261200c1d806108 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 144490710 1250 144489460 144489479
    0x7050714010e03030a020c0a140715021c0c0227011409150402131503090b0a05040510050c2b0b2e0c060c030f0b040b0a030807020f060a020304 63
    0x141400003000800a04000506140e00c9020141804900c11340000781c14041150420040311855040252444039034004943c00d5524200781c8542c198500ea410103030501140089131050300c0c120040d070801c041d40314900c000c503164803d00b10200c0c0c3c0704070079400070441c03283c055240c85110102020341c00c00a5060135001a600c04810340c000d8402c404c0081040390f0032041c4c003041e0307131b24000c1036401685484450040c281088000e810801414200442c110461a4184c11000341940203e0440e41d007601d50511441c1641d1089a002e0b00a5024a440885208450740f180e5485894101c24504040e203125005000f0581c8a03900c1240c0d940310503400003851820f2241c4c203402081214808103032100040810582041000b03401040e0ac47d0080a201080c024044d0458042c0d11880801a8100b5020054001d12a5642d151074451412000c800d042c28284500c200c0700c4c600424003a03149107141d07208841c983c040b9008a0b0460050340c0303880c5981d02d4210161481c808160003960319541401c1502 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 144491960 1250 144490710 144490733
    0x60102070b0c070e040501180501020a091409060d0305040f0902090315010621020906070503070611090303120a09020a0308030411010503060a031e020303220e09030405220203070507 80
    0x84812860800802c4541c900000c0c5400c111118000440e40741e9540e0f040290060203521410080c01f038514055008002e410341c014503440402d03032a0b450b038443c2c4540d00c104100221014040e0072501c175802041d294a000d10192488910030300c1d02a01c6c060300d901c100c0c0c020120f26440b07101c2850300816415038604d07051048240b00c0c500048400c02540c906280103000d21003145009103010228a1141403945864049461164001d4200b030390780c4045180103a500d6008045c00d031800c903c0c214224294034040303070841e012908024021400c03e010384140c0281c640016014019540e41d40d8010001078555403240001140aa00d4817a16881c041c00d000e4008000e044800d81045020270030041e26035550512441603d0308070b800c0c442030409100e41d4503d21040c0c0340f0044d50502c0b01240041ca0221500400d4032011040059156015596002004180ca0640740101950010301c02072040d0b0034601e11100340d031825500301130741c10b4100100c403000705e0b031054900d6400110005054800d114034010326 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 144493210 1250 144491960 144491969
    0xf090109140d2606100e100518040903020606121f0203010602060f010b04060e06070213020405040e0a05030d0b011803050705090105010e0a090c050706020d0207170403030c0809150d0506010207 85
    0x84110b410904061450400f40107240c24485d078040301c15407114a1080542c0700d00c401c009042c425440250703aa014000d42c100202101c10320500c0c00315240e20b81001d014008449a144d0000c2450307407100020043d1140d03654511404074032841d0700e016030743d203c80481d8100800d00c19800507560b5051460003410071900502003001001c20030010003501e04038004840c00c460942c40d100010051810000e8113034410f00303102941c0b107031000b004040340d40c4860340108103d6904403800c0081e0303d0020344142d243e1b40350b1342000d40590001e100004480c489504184c045840500d0081c111501c4107500103035110349a08280c5003607004420510050034401c1c0954003400f001d0034100c205107202e01c00251040c2c881e010b016807143e1200324070b0740f1141c042c50541c0c49041c1d101c8819522203894001d40c60080d08810001d54000d5030207001c01140541641c225400c0c0c80e05aa40d21081c0850390700c5600c010307403140c91015000b80c2c041c0c0070019620701207805845480b4201d080800d00b402d103140028070703003115a000f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 144494460 1250 144493210 144493247
    0x706050c1b060f060d030909020c010e0601080a080f0f09060d0902010f050405031b0103110406170c120f1504050f070906050c030d2307051e030403080f090109140d 72
    0x60045003e1074840c5654003800403030310300080150620301110010b916034040b50100380040750500116006401c040200010101107610b285e9840920307d580e5480c0120240000c032042000301100c40707080d00102064070302d10403520700d84410384020500644c0800e036000c50890f1f680d8891021982d04c8014200700c0300807441c000781000e040c80002138840091001e0b5490700c90701c0e10f10400f900e134000d03040b115410f2035120555072210707603d21015102020908441c45001038034030000e18409502c0c5c040e05c010009808294245584e04005201100030283c10311075800c2c8803010301c5046640d50301400b44036004c102d81c08a20784c00c2c810b8000d002494aa000041030190900070305510442c0001034601c4002c007040c010444044e0700e481a0981096a85105180070b101410000c9840c0c016000f00111060124403814190742c20f142d00031a40400c0d02c00030001190080800c28a100006840350400c000e1030002400e03500b103030f558040c480003404403501b16410000c43c0ca140a81c0100c11101e14403030307188 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 144495710 1250 144494460 144494473
    0x7060c05090f0103090c030b0108030c060c040807050105030a09060513060c17061c06050a0518070503030904020a1e0801080d02010509060402062a070302041a0918030706050c1b 78
    0x400040e14a2060060b1904150360380070300c842486400000e20380215007200750f400c0203584514019031658440715031301540e88105008204018000c100300c0b01107410a40c0a41005801c003001120789a01c05403035881d02c50385801480c0301040861280c54000c2c41000380200c40c4140030324110301a02e9444c024441881959070f0038800d1802200150bd0384541c049a94140d00c48280c01c0702c1e0702007121044084c10a07032810b010418107068a502581c042e01c8400c2919a06446000322259644500d000d1140c05404c14000d202203410a5009450354403000c1c180525107501504d81000414903001d8a0400150000d004211b8600c2c24084080c01325114030013403102e840c00c584c0b00c0f9a5014090b0000303001c3c440c000b881c0500302003010041c0000ca00c0075582c814450903600032040d96003000d804140e02c514640314590003d00106d060f440410b00d00070700340d41c2840d03544003100103c9401d401c20482250004002c10000900d20340304e030fa440395404014072a00ca2041c1410b1111501104020003115480075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 144496960 1250 144495710 144495727
    0x10b09011d01031107150b030d05070615090905010c1407050a11030c090114030d0c0308190216052d12030606070b090a0212010c12021b0601060507060c05 68
    0x300d6110081840a00919920888180120300401800f0b1080e04c0603000840c0803000c21600a031485400c50100c3c4043c0a080c1c0480205516480051003c00100e4010804000007481d160486050142a841c08180e400d617551441800e8542070300c02103482c0d0f5942c030380c0d8400d00360300405203070300302100c2030f540504251140c1e4555230780b200c0b1494040d0613000c503401000245c0e034023081288118080582400310559481d0100c40d85d45a0007183d45220b4010020030210040c455526026402d4159076000040d8450704004881c0c0c1c140300102d10310042d0200100d0b00031402c240003410340c0500c240700a21255480004141c3c1c60500140e0746901045403020010520100059103c22400e20340c880a5883d01ca4800040b424800c002c4000c000e64503442c1007060030040824002040c0e4000d540d041c1c01700c8410654642250501c500d601d022550501240000703003901e6028120258807905035000107406110021701d05003003607010740c001600024203070003000301e24050060380426a003050350074003460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 144498210 1250 144496960 144496967
    0xc170706022713201b010b0d021c03022e0e031602060a030e010c050d0f05010f1e1d07021c05030703051306061e08060103021c05161805010b0901 64
    0x550f03001060264441e03100785045010025640191004038030450395900c8944104141c58120481030b250325441d000d0b070341c0110700b0a407180d000008c0d40240441c00d520003110750760407070102a9100f0380031803140390b810070514800300140094862049464001403542c3c0c410713960a84003060740b20840c5d50000d12503000c01d81e804041030800183d04a807015112101004114000c0c504612002100d6080450004401c7c0d00b004c01400040140c040034401500511410b5040da0300c03c2c41001982c0500305c1040043c8100058001c60301d5001c00c0043c805143d0ba82d41c182d4060143c58441503080329800244101c041d01082101180000342a08008941c0c01020251050000074500d00c141500c03035002820542140b2070118059034440c500700030240c0c41d0701810a40c001d005845240ea150324800201d046600001c0181c101ca50003041e400c80400c59507010b0144040c10202207072244902013550141d01101803500c3c003d04402820307c03980c05040c486200980d80113900c444c0714403c08002d040ca0a992 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 144499460 1250 144498210 144498229
    0xa08032706011a07060606170606070c05040c11010204090c110703050d0c0303140403030c0e040e060c0f0403050d020a0c0f050102061305330601050301060c030c1707060227 76
    0x800e090f8015044000c551100e2081e20f0000b030001c1d1134410007258858121000440c1c001d20004407011940e40d04091000324842e11501a086401201c400c00076840c050704040201201c03440e102d01d0344580300e8012403e98000360040d000d896100c16480450a0303111481078151901080204425851034643c030351580e440e51441001c0140c203101d4203003418025004440450a00ca60f0380500d498941401001003200c030000400041403400e4001d2180303424043d80d403010008801504464440c22400c106503400103a000c104d00310180000004142c00f8003003102e01142c242c01600011070a8076210038041c2c0311380c226481e1400510018880303030345e000600543c0403944064181400c85181003152911400c2081503c045034919000142d41107005118908160300100e280a580c0f5403000645207804240503a1000a104209100120b48180104d1041e40d000d011503600ca03850036011003089500c011003d6840d00c0e00001c0030304000d0134802c0e0005000300030034178840111419100103080b5a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 144500710 1250 144499460 144499469
    0xb070305041511040f091a220209041103041202060f13020105070c1e0504060f0b0702091807030609030206060406030308061905040606030c080702070513021b0a0803270601 76
    0x5903100751a08501c18910115030150600940900b1000e548412010243c400c061380b03c7c3e074420fa1a80410034a040c0f41500c03004021414118a800304c102c901598003e400a10140d0351007500c1c1e0280c4c2c10041c0d01d400c02503004902401a511940c400d440e8085e1070090050010102c00950700204940b82011180c122a511350900c0d145660782a6410000244010740c3c2020008140c0d0f00c4004c2548010400380c80101c440980f4103210245e5580080c003220107451081c0b0707d02c0141080010014034002d890a5400510b80c02d100503070200c00000c43c1e140031101d410443d045075940a1500c245901001040d03408101280d081c41401c2c01c5036001819401c5c083d10841c0500001c601d252103a040e00b04103d0090b04014104000362595501c0040c081c01d03d041040011030502e1f0041810a40b010900300165040604044562009010103d00a41c00700121500508800c2c0b0940a00c1f6010f1145c030040740d00582c021500c0b420040c641208220081e0000d042a046070750050020001c082881d50445 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 144501960 1250 144500710 144500753
    0x21918050601050d05010f1a13050f0307080d091802031510030902030109110126041b0902210106050a0c080307020c0a06020d0801060e01020c0f04110409090b07030504 74
    0x9807510401656540540c1032114403460030000042003a03014220b00c0c03812030705001008007007140b0300d103d42d454074413500388145182c0b110020180880e017070030111602600e0001c0d00301c030b0000e5990f80025051603c2811060002102c80804001c0d102c88054484903105081c0811480c41c06d00c10340c3c0b95511003d080c011070240c0101c541c140000e034001d612902c0f2a07a0054000d02c66840c151800c1d44002041c2d102c0c45003c1081d04203035040401c0914007900e14440c1004000c0c4017600d454503000200c0f04a0ba41c4c0400105000c08041601880e500181501412400b00881c4c05400c0300340e002200c84050700070600b0802e0900c14452026400603035040c601d0f812102781c503903e0326042d60807410b1404461202e0380068090100184840d0f0000e050b600c00b04041e0740c1d040d100c0e42c80d0241155440600035005005034401d03001400c0c9442c00c111b9480480c40014000185503940149003d81d507041644140071883d078400c542800d000054100030340c4420701d490b0402682c5441d0f07481152010700001840d429 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 144503210 1250 144501960 144501971
    0x5121b0d140a140c010f02071a0709030f1b080c030c24030402041b08161d010f1206060c0501050105090f1306141014010c12051c0903020a021918 64
    0x40520f5201101c825114143c000e000d4024000e030400069840618201c0315000034011000c061800403c5d0180a80680d40d5004440c5145841d102505803c0315815505ca200b1544c03034218039000314000a0040c0301250150224900c0c1d20201401c01c40c800d46814001c8603903503180342c2c0060111044c4407130340080201003a201d4503940040307802040e1142024000045602c0d1071643c1580094103e842124411042414162018012140c0703080110580d40f02820040c0c1c070150079800381d01c086c100009c00d481d1501c04900860104400d942107640800041000614400306012003805518050f26003540d0000250600030b204c4c0c0c00d080c10060001c1481512590404100710558110804d0383c0c038070060141c0d1606004240c449020840d10070580140200862500c03103500840c00ca980d81c2e50008211107e400d80740109590382d80c010748150046900040706410620414861425480e00903802484d0100c800d00c1448802c440514210585440042d020400823045071107810a000c00c18002051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 144504460 1250 144503210 144503237
    0xe04090519110405040303052a0702040b0105090405070e03070e010806040305220e180a0b06010f18030803040507060503100302220e1c0309050304030f05121b0d140a 73
    0x105030440d000c07102e0f84241440140b1080c10340c07541000b40200110455400c0b15210700e0b4281006010b00c000201d02c0d65802c1c4242c8000d403030668064810100103040c1140b030401c160b40018100d810440b1040702081030ba400c0300e003d03800c040040b24041e18071041460b8495062400e001d5443d10000d2009003003050015451002c529803052964421080711005858a40c480c5010140303580101c41e181c10b001c05220840c40c0c4031200080c000c03140c0350450309c200066110800116601c810021852003807113405e114211200200140c101c00850041219036240d04251a00c40d09040031a8420001c020041c0300b4080f00111482d000400c4030b0f8125601501c80350590007202d501c1d4541001c0c034925034076004420151040106400302c525004100321640151035480540c112240c5d40b0024006600c103001c04d00028105a41344410b00f40540100d6005405050b43c034109a400564030902c4602d005101d00343c1240100105180180d080c20308000003004900884854010f0441d42020031031000d1502e41c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 144505710 1250 144504460 144504473
    0x403020304080303010b0915030c0a200f01051603060b0301181407050712080c09040510031b060801050a05220b0303040909030206010b040b0403141203070f0e04090519 74
    0x9006280300b03000d880d103039a507075001028550481c14003240280c0c4d030b800d81e00f10340300c5004c4103d0b407040c59104141d40c1000480e20341281c01c1d410303034517403450341c0121040c076492400c40410002d00c005074000000300b045d2800300c520904c0140a96461424182007600a020074161241a2415500303170030704020843c8014035145016003050407141060000304028001c1e5654400300400c25540104038034804002030b8641146d00b5101158401009030045c0030440091402c0d0708060303000701603240488500394aa48524000c0c0c7d00c0030045c944101c6040340c0c1081410b80085100303004180459801184030f10704004250012850840004a08030050a481844074a9807011448800141c220b0340c03030381d89880b5801c004041c1000181e0152151000020340403840104480948a80c0c08506e03003421715680e244087c0c1c40c030700c16802c901d5028011926050a04401c0035500c5108195a0407c60044c1d8210203881400503911a5014908110905002c81c2d40051901310341c5110342c0e84840d00007410700b4141c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 144506960 1250 144505710 144505717
    0x1031112010204120305030108010e15010612020d02041409070c1a0a090c08010501180527071205012007021e0109080f010f0b0a030317060a0b1216020c1804030203 72
    0x410840e220f400c0040c050546c0700c006141030b11000002041070b80c0c010400d482e9201e045030481c0302c52144520050040f87d201c0c41403003007a2554510091f040003490354601d0143d0f0031a0300100011030090003c500c051510a25040e0042d0950500c1e04008075251035120701580042e4603036441008800104510b58169800017003669008410203444907102d01f4214060720003841491035500220046440d501600e104003401044040c0980403600044140301148000d1203200807000d00502100048100c074160444c0e0704d261107540000f6041c06142900c4001d1020300d03208540c003800600c1447c00507159451441d050411550024400d14400b030300480700c1800d9a0041100d0303001d442c0d40c0201c405070540100e010b00f010801d0600c03400c4013134018003041041c1131002900141600e0311819034012104031031604180c018140d0154146c07140c070703030051f1940044814070107582c42e00200308202001c1c440f107240c05401031020b400001034010014100d4130480801c5019a0b050f040424109402003048 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 144508210 1250 144506960 144506969
    0x304060b1815240904090311060103080a0f0e0f040e0304150201020712020c0a140102010f0e03090a0e010f0302060f07060c0f020f0304030c0905070e0a090603060f0501031112010204 80
    0x250346152400c46042054041c45803807071409403036940700150780300d028024401007405034002240e08244c1284108070240c00800d2040d418040280c12070088004248025400f0314002d142d9250348910403100107122201c150040c0d001c20104841e03030100ca90b11152a1141c0100c200c9000c80e1071034035103260701d007144140c2d07028401c1035054020f101070b42901900904a018001e815442452034650350580e216140c54440c554055520041405904d0304500c14007211041880000303072440010a04404443c0f04440a810036440410b490300345c0d18009803030300098010b946a0750119450460001b84c1400117020082c4251404510740d4110072008007900c1c1e41c260003c60512a003210304d07002400c0300d10410f0740321005016a00c0c0c0c000c040c00d0b0010407101200c0e84001e501d401d2034617242d0b81c44000d2201070100001c0040e241140729440d550a07038100b016042241e400203101e49940780880403503800700e481c2c00c00507003000010030121b4504215410840000c0d2119181c40c003401052074024412a0071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 144509460 1250 144508210 144508249
    0x10614060d0b040f090c0b03070f1b1e11010212090d0827010801060f0c0212030c01050f01080f0a021f12051314010b0d170f03090a0309051002030304060b 68
    0x3410380304d500c203030304203480c807602441c40300f4569a11200241003902c001c4520134040348071545410b00b564402d201406030f141c0c070b0311240340500010340d4070100d0380d500c0c0c40c90b2091540c091986000900190b9000d02000b59000d0000748412011011000c01390300900e1643d5200301c140011210510682c20201c0d08102003403111031140034121800e03400e80008800e1298001000000042a0039004400c482c03406c01301c58032910441c0703680b81d0800054150303c11212007107000c20310408003202c409004503409120680030760085903051001292800c000500300070250703407046010350056150403050801c940d024801900b0b0008000d00240e40036856110303030801c4180b400081142203070180f5800d48070144100321250072099802d00380740c05d0f5500166095449440c0c04900340000d000c1035803200000d1007408006050034a141c2c400e4065400c100c40c91105604030f00c140750200f5500480d07400142000303c40c0f4003500f52010340025500e0200500041400c1d5441c2c8482c001640c40c100e6060301c1020703115 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 144510710 1250 144509460 144509471
    0x30405040516020609121804110315040e0a1a0903071b03051501230f0607050106080d030e07090216080d0c03110c030f03060a0807030f14010614060d0b04 68
    0x25400d0031081054140d60050141c1da0210310001004114540001e0b1b82080705803c01009448080c1c80100e94a009540103996800b89000780d106100614441d040100c910200c1108a00900064440c02c1c3c00c0e10420342c00000390840003501c0b040e5000411201100301c8400c59551450007403842c0b2661002400d404984800c0b48148664400f1040a4a101d14242c44882550303100f00031101c0400c2c02445218a6201e100b61081441540809420040101102e48440e54000400c2d0941c0c0080d40070b07103160351168018010100c081204110040d40c0780380411101031040304a941b2054a401040310700d9800140c41c4580d00d51040c01c088051b40c10604a40c0d0780c1c0d000c0340d1301c440180204001000841c0c240321000c03a544403040c3c15110000d140304041c40c50800764400c14000c6a0004060700e038410940000852680010405440590b11990304102100c07040c0c1400110781035901440b0341d880e0b05100082c40070368451102c886c203513030098840ca42c450300242e00035000390981050031034100e0b184c80c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 144511960 1250 144510710 144510721
    0x6061c1d030705070618090902010e120c03010509030f0304020114070c0e1603060305030406120e070b07210c0b0403113403021005070f0c0311040f090b04030807020304050405 77
    0x100080003640c0c03041081341c41543e41d6041c1a2100e60200c0e0210461171801c1004010881180c1c11000c0440d2051404c9000c0300c00b20b200040310380076140c0315982c1c141c0c00300704075071802c1c2000d1145d00c0d00441c440c1c00650030b0580025000390703140b00081009040000305100040c00f03100c85015141c01c0c990002c00301901c5500c56404103c544800c42d1a00c0c00c1c3c028100d5200c000c14000e2107440256070b003106c081c501d001e08001d01640e19504800400721580c0d078903107824510f0031090060310090203000c0c1c50699503115904081070944200138030a400c10401c1c100940070b41c6c0e0400c1107402d41c40e0f40800504c00c140e8070340c1400c1d42c4107014011403401038014003441c040c50b6110313004800d20110b2429210711701c2c0300007941f10013030318401800000d401c0300c1212800a0154014005007080c03a01c00d01e98504c24018540e2000314142142e401104d9a180d07010040903145494010315000c440203e80070800510700703484014010a010f4409024030203017002003003500d8400e2040f80e0107413401030418400c1d810403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 144513210 1250 144511960 144511963
    0x41a13030602271206040b07090302130506030d080907260d090303090602030a05121302030a060f0f2d06051206040501060608100303030b0402090d060506040c0806061c1d 75
    0x40f8100700c0c00b00c1805081d0391207240f900b0304400c1e80c0e08008800408540d552642d034948a00400380010060003448480040107990f02400b03a00c5494401c0c07000b0555041c20000e052500c500b410f06001400401005c1000d81c40c4001811001c85245800380da81680c02c503846071146150b841a6108280038030102400603d4000d800c0300120381c0f00fa5111100566501da0490701c1c2d0040507038080000c2e0040007004044e68503481d8054100e400c02400500280e04c5e6400a403400410701000c42c0e903070303071180c2821082c08901d2159075501c080050081c080d00328039030100800c0449100410b040000d161103800f0b44182d150788101c0140001810f106904205a03032416552081114212440c0d8202040422074901c602112401158070901100985041d1b80e03040d070241c030a10604035045507090251009039900c40b1340e4507003040d024940c0010303a8240f103018802560f2403282c80c0c0c41481030074410301550f0b0b150713a004c81d08514089240c2020034480c100440c3e0250510a0541c3c65458080312a99001700c0e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 144514460 1250 144513210 144513247
    0x9021c050313091505090c040503011e0e01110d0f090b0106030906050c0a09051002030f0a030c0e0108160509040b04060b280504030204021812010e0111041a13030602 73
    0x60541d510900c2c999203518400035500c0d00f050b00c03032120844040402846c00c01c0016160000440040ca5040c10345503400b09007141e80c414840541c0d00c0545046400d841141d11a4102e40300500300203000c40440c40c41190a5403007034045005000340e07a008030040e035030320a40c012200f603580014030020399651020000e01805040e0026100245001c000c502e8505402048401c2e20b005601c0716111a0300e48010001c074032402035442d5041d030104014800305d02081d0f070014012a440c0707407000030780c9002c840802000a012003e00380c4c10301a80700e0a000030071406101454503566145005651020054003141c064002c50b00c48581160501001050001d0f664000e08090708607555138205038030106036045100c1000400200200304200814805802d041c1c00a14511000c1d244c00c104a14605010651448200b5045425030b55101c0c0081070155080c01484803404818030454101810080c107408985440444510100d030000394100a603030745c01c2ca11030002c1d80c114000315200c8a12400c1c01c0600b90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 144515710 1250 144514460 144514477
    0xa050a0b060f1c080a0c0803070306030b060102031317070b030411010806060304081204020418030804020a06030b0109090207262101080a020d020102120f120603010b0d0609021c0503 80
    0x542200700d07042c0c10304201d081502075006039850040c0c1e0456503282d109844d880424050200422060720201003016030300254055500742c2e60004a880c69420180c48a03000584480c0c1150810030000340034103841052301041d82c0d6008407562845040e05100c5250255030b50108002040100400092040007052601c0014003030301e4a0880342e03107c20812040b44800c07200100f000b041441901200c0180310201d40e8844d102a0001481901d0605081c0c20510b82040860000d9840010801107003803182e00c02004095038141803114115074030020706122070724041c1000c000d50206502c010305c8450540c1ca4620309400410680744610b9020641040e030081000201220400607071510100b803a84c0d4640c12141c2000140c800e1071003540c02c00c041000c49102c01e90443c0310704014210322502600041106251120141da50b0b03034550300c0c0c1c03051003840040c581807003645003001c4a407058940c80b09000d8000da0040000803009981d100040d9201554110b0761400800c07070a90008000000005041070b2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 144516960 1250 144515710 144515719
    0x31c0e040e030405041a151309020301030809150406090b090a09051320100309050c09070c0606150c080a05041806181505040e0304030602030906040308070507021f020a050a0b06 78
    0x1241941140c00c400d01d0707160700316041100344011461121003107000d40902010340c490340c0a00c0b49c3c1da1400c031003603800c20303081520b414100044a4017030b4501415240c01c0c5c148404800360405c0d00d400001f5240104922032010030003000650404a43d6549110902404440d94108410304101c4054051490404400c4445d080d540000101141980c030702d440d40c14000401c52042c0c5075004600302d01405c200c402c102c407039108098170340515680302c0011500c43c45150b5103014900f0040d003032176400e50b45a513005440801c20108007903160340d8440001c214494014110a60300d0b41c02031811596481294044400080c600c031008914503050f4100604a800b101100d41040345e400c900d9004941b00c02000a08600807100c0421103130809402907000f00544c00256410596a82c403581d00744c1c1c1c130480f9008665005802000708254104907003503000300107442d001d07052034003d50101d02525804142165035800c45444d04001e00e108000d03c0802e958401c099030312200700e518084060312410b8800c180328 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 144518210 1250 144516960 144516971
    0x203060a0203160509010c050d022103040b010308070813030503030406050702060709051507020901091d0708030d05060d1b0303020c04270201090f0305030306090c09031c0e040e03040504 82
    0x990304580281d0f800b62500402c01c110641a078035095039035502c55609281030104101251010620600c21240c8542840d0040c02d145002c1c08015903201045503d020041c440900600000c00c62000c0900d0540394000c8a0741c0c0e8440c01420514070601854a010510825030300001c42040340110255001d00c0c4540000c0c0041d4440344000c1c0c1e11030108032800740000f15005010025854600300b10002142500c821074a40085070700480c00c560700981100400946506125400c000e40c40c003a5291000c084000d0710070503081c6001d9645911500900684161321000411041e51341d15038030844451340710041c1c040f2441c0c802d24885001c2c0592201368054092522002c035107040c54041e11300d0001240304c042000003810042001d03e80303000403050341009038090020038058031164046000e10b00a0b0011920b0345082d80800400c22b13070060401114403018058001c094400103001c0965501089040342c410a404000700c1c0c0c41540c40000c1a030050070714190700c40308140880144251403003664103020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 144519460 1250 144518210 144518221
    0x21010f08060a050105030a150e030a200102120a0b03010b04020301030302010b04050106020d050a0c080f0c072c160c05120c06090c010c0308070905041401060e0d0506070e030a060f09020306 83
    0xf241c42c2442215003540081c01c942000404024810301d200c00ea01394006100e03401c454440b03245d501b103c9280300204024141042d1004e50030300c104940c0079207003002589090070101c030111502c0d8010b0181e8411948a0240c142941e42c00c0d00280c800032409841103440f0340e03590400a0217000b041e08440c0c060b83c0341c1070002c1011880414044c25104258640601d8070380240c030112a4141c55030700c1070320003040034408110880c900e24001d00313419030b0800090002e03c0c1030241441b0901c4840340c0c00c0b20806414442e14801c081600c1200c0ea115640c1e0064100c1c1083c1d5500c1520040f41412008000340207800701c40d00d20607110b00203400e00d184080100c4103140d580e00d0380c4070b075211482045c2e00d000c507500401b1030340040d20489001e94040d407540740444c04240d59202050136242c10180c50303000c845100380180310143c0d111500c00c1101c101194080790040841d103c60340c03150805019a000c1000b42c011500380f40d2400c11019606e540d002404008010b0140b000d01c0041901c90000c0b803103800785401062 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 144520710 1250 144519460 144519481
    0x7022a1903170703090f03050d120b10051b060406050a06122012030c0307030f0206042105041a0307090501020a0b070305040f02031c03050a02040b090621010f0806 72
    0x40a8a600401d0495902c959500c41c46103900b00c494110100701c510741e000f0030029800d1000400940c440d500030012200f00c040d020706074450a400b01d191491138100090040c2c1d440101d02c2c4594942c90905540c1d0340020201d507000350903150041300c00d03031203000144000c00c0b4080c0d2101d4860000084204003090712040b05000c41c2c01070305d0000d08020f08000c3d1a012044040946085441000b00102c980c080369420300e0b8196042440f0394601c0d0f80021840c3e9091580010388a5440340c01403000d00b8442c80e19945a02d401c0c24120441281010080038642410340624120790150040703078204000340c000382103011a503600c1151210000ba107849800119540001109d03a8482c1e8408048083c0d565450011801014018015910b800100340701c41c000d43c5045c08450310303480f981840800c64190003040901900d801904c03200e000341c0304000070400303030390540705841c4551400c40d82aa030301d1a0500f83c1c046103000404443c0d03642c5803030f00300002d0f001070303075241440c1119801f6090313a001c1e5a9084004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 144521960 1250 144520710 144520759
    0x18062502160302060c01020c0d05032a0a0c150608071502070b030f07090518070e0108010609090e0a080a08010312090b12060316090c0806030105011d07022a 69
    0x64070451107140500040c0b801c400640b0b442c5042000050400340011603c2e40341402e41c0c07200f200440d0000080c8030203403415442d400d001910105220b405c0080c081c000103110310450041d03004000740894028100700040c3c10385501c030460008144000c0c1e4071503e41d207840780100d104d0059260b03502609455514000b247c942c04980402048a0560381e5002d501c103400785008003420304000401c01c0105042e500e8107503280b00b02e44580c0511400346403041c0044c003414031031603041c0e040c00101001000717410f80c00318008054442e0060049422103840c07100610700a84960001c05103000442c604507515803190f1914104e03805803030301104038084600c00703450080352401a8942e04000f006903c0034484604000c580240000c1d04a82c1c2210032080b19040c0707405203400400c9115146d0f01d2403c200d070f81c81540e40e44c220704100c00030485545098046108500d81031036040d2015580301c0000c0300d45000b0311446948006102c54030440d1948540c640f10100b8885014500c1804a00140602518640c441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 144523210 1250 144521960 144521983
    0x50c0912060f040221030406200705100f0c0506040501020a02060a0207050c0103090503091203090103140c0a08060303070c09060614161509080f070203010c0206091518062502 77
    0x240e502d1500c07540c0034044c91484090f010444504d82100000441c1d1040008000030302d066550002151000c80c2c0f4075046100929000c80d41d54442d15061141e92b0710703030803a0000000c4600f000c00b41000e10000503200003a4000300a080c1c3d02a01d01004180201034005199080d401d9081d56156510403c43c0c208078014a0405851540b080c14510890b5000341e11201c4c005028004503820941700d040000c0102c85c0c00d01d01741c00d090b00046140c0c6401d50b00340c000c40c82d0311518900079420034a4041da034043c2d24080c415003d000c006081c80415076a89050040360f20b60341e003101c2d00c1140c030313a01e84000f040035043c030340b00d00070000361013140c0d81346031810300f00a4624a280d00503036244078022036143c03101c0c1c030303480800302890041c1d131102440000313101e2070b00800460140c1d10425446004a004050846403c0781d8500e0035500170714108400d107000401c1e00721840100c40e44a060a07142d01c4100c400b50070071102a0040ea228460074412415554080711002c04d040501200310b207100c036035080303840c5d6400700d24 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 144524460 1250 144523210 144523231
    0x10608070302070606090f060503010c0f120b1c0506010510081e09010e0312041112150a02070b07081503010213060507050c09010b070b0f011d0901060504050c091206 73
    0x8a1112803082e0014641c1c41e02465001c100c094480d0010b60031641c403602040c09041d6694810809418280070366050903006013800c0c0c85041c10310602602100700e00009440d811740c0c1d44207610540c0d440e414096030189808508000c1480985003596032800280910b51280040425102103144902001072142482030091120304c0c000c079103100b4070039002805c1c2910315502e0340c0d01c6c412600c00c20000f8100b00c0e45158100c0d400d50400c5d05207002107410126100d801000d698100442105002406404158402c41e001e03600e80d071003003d000001d0141070002000011040103210f50150f02c0746070741b40100b0748510305c0940084404201400c03481039040085045440031020091310f07024401400d40c1b0390083e415105c074480b6038000101b04c88030907000104c00700c40100300e040c28407080c986c0159100b000a100200300f075041611513148401140c9100024100000004018042c00c0d0040001404060010f10013402e0280d0101d1281e004494100e01454140d482d0b040340c03210015007240034607000c16 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 144525710 1250 144524460 144524477
    0x5060f06070311010e03131e06140d140406050a0b090402130b030a0804030c060206011e1a07050f01020a0e0105030103020904030c08040308030c030402010909202a030306090f0106 79
    0x58050b0f8114900464404940d5078402c03440c00718038001d0004000f00031175582e40342c0b43c00303081072104482d03407843c950070001c3c407254501e085c42203c1d08100629505110810300545038014042020044c00088651030b8140070713000240010071465030003ca0207100c507a20244030803140c400034003603d00b10454001e580201c03854800b0800c046990f10440f00c504000e011b403050018143c80303803906135000794412074030180d5011003002200e41c14483c4d036000d4180340d202180300101d5241c202001c159180140e8000207180c050820700f002408040f5807c1980c04000e8451071140c0e80080d600035000f9180500204c5c90700780700785113158071a45c12a41a241e00405c240c1c40b648450b1000c860356500c0c140111303911030301088048042110300d0081c520401c10603d085540e0b191520004040c0090f652000d100c090406069115001e84182c0341e080c58403844040a4464042c10744e41080c00c580b403072550708980200c01842210300c0004c0015841004292074100e40750300d5403213007605444000d00c1408001002c15 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 144526960 1250 144525710 144525713
    0x7140d170714030f060a06080405070b0f071406010905060d0b1503190c05010210020403080306090a060b04080c1206091f0204030c0e0603010e0105070c0201050913090305070605060f0607 82
    0x5541d00408a4905824100c1e0003400c00d102c540e105076007034080c0811603410001d580c5000190000900140d28200c181801c29507a526918861401a501a2030010640c62180300600d401c0e50903054003c10200d80710800002020b840e90070070b00501c44142d0811000039003e04054108d510b090b81c0c0144540c40a40c1c0300081545a01985040c00b9890b0081049035200c039040c9100003442940941444007050307203007030006440c20404d00b2040806600600080010851400130340780d01c01c0c816244c02c80c8a50b1146840001409660008c2d201c090002c04c02150b07401000415108070a402d49000503859007a480580c2e813000222045902a4400c0024410314100180c455034143d1101502504007620390f50740895002e00c6030409200c21a48101300a6189024000c01d03100f900a20000c010500340400c0c02004204000c001070b052080000300d020240c0c41e20b282c43c8809000341502080035039240e28004002c0d43c407030742040c4d90060030030700440c0c0725144c421002d8521010060034a0725245a5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 144528210 1250 144526960 144526997
    0x609030809190611070f080301080601120201092603041d1302090112060608010c030b041404120f0c050714120f0601031113060825290d06030807140d 66
    0x554110810482d01400010009840411250340c040c0c490401fa41e03da60404101070328001d0141c0c8004032084111613600090b1760003030132010690f00e900313641040c880c0c0c14020001010311200d01d40d0529200000380001c43c18850341502e90302c0581c40040b1162a00d605501c10000c00304194040d601512400040198410389145180c1c40e503c903d0300441c83d166501c03038080c21070310315004880c040303500c680b41d050840c50705100b880c2002c180141550030b9400d0903101c6034141200c0154401c144190800040c5d041070054512900d0207910004131131415480b02c404a451140184140d8090340313034030f001044900d201041050103a11050020640c582c40c580329480d180d41c9a60410750040d45414400c0040c80003070207918040d1402c0002004580e010410f00c2c50f8107941c4802e02c0004203608079090104103003111030014131111002d140d500806000c2800356041c4500880c40c0d040603c1e0000000c00c100e4803001411001d401462440b40034802e8000f490f4480c00940d0000b00040d49848160042984 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 144529460 1250 144528210 144528221
    0x51504050106090c111e101e050601032009060c010216020a051012050a0b1305010f090605210f0a03090312210c18030609021309050a08090f0d06090308091906 70
    0x6110045941c1c000b001068101100c0141c103410b0303511281da108d41c26880c0c4090251a411100030310f8104500018200d11485104030090003400d044800240d440c10351781ea090603600031520442c0215601c44501040f40d900148550b8100d0083d108440d0019140ca49104001f10184981c0c441f0012034148044075801040d0051000c141d05590b034002c00529294000900601c0401c513100080355411304002c00c080140c1035008005481c03c0c0041031040c1d8444c004000518184020110800e02d10f81e641c980c100002061920100c0c40f450710410149680b0200032400c890003198403800b00b182c5009c0480e92416a0212545800341e440c4130320400346495803250710400c225241110900901d880c1581e22010154819079030136842d041410154a8400c8038504030845680e800c0110340c00c07c0c2e8405460f80030341c1c000507120700000700e030681131034035446080071080d0300c0100410411016890020010113000409400184503c0300280f204040000c1c0602400002104a1413882a9684402c00b401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 144530710 1250 144529460 144529513
    0xe040510020a080702071a090906040207301706010c031206081b1e091005030a030c1b08030d0c020102120106090320011b051504050106090c11 63
    0x416000c0888000340d561000d484014103d66a228203801d06440092800b0402c2e080b0885109441034030104c4014041d0440d04c8030003003a150701e04035689003000038000b40564940504402c041c0c090380e180344084540c007901404e00c0c01e4040b40c0c0390102c00004448140511451403410300d00900420659170051001510861107441c065403107515080e4908103846403680f00000c03940c004074141e40040c10350100e0f01d892041c03e9411040e14415449840b004d07010030900a070044c44241c020810710b60540322820b002d040702400319900c00d981d9140040c90380d81103180c00c0c4c5821402c0c00b1101000007100d107101e0104c505c0c51004604101e8070003c2d103001800001120015990308010b0f081c08406c003401d6007402095240c0300c407680b0300d00d10b0400001603403102402d0240941000720400c43d6a80208240240301803c0f00611100d80d12450f01c14502b0f03c8031a010760302080c000c0200b00800205421080607118000010700c03035440e806c60140ea06082440c0d0180a0784c006508245100303422444005902 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 144531960 1250 144530710 144530713
    0x12010e04020f0d0c08071205060105040c0903050a0b1012020d020108060301020c1e070e0c03070507020a0b0d0b03070f05010c0b1b03160801050609010c060906060f0b031803030606040e0405 83
    0x409100000f07802107152202c102d07048800c00c0d1013001740307410074044000140381402812611441d01c2d624a62908014041c1c24400c1c0e5540c051007004501c01d5191b0300c060756115013154a946418100100a0302c002c44082a0a0004030740115240f42d52140e0a007400b07502a210f180d0700300d4580c0c010750303403031130010525a0152740c02d20510403091001c2007020041c42c041c203801c0503081a8500b070b490920104d5040101d20910590a001d00e86503403208895001c0001e180c40f546070662480042e40e0119242e005451064012a44501e01e2480380e1004035107490480480b290540d0b14001100240307000c1c030580e408519100c82150100d0000d182281d40b22803102605000041640174400090b00b042d198050303e042004400a10940c100d42041d02600e81210950300300b8281c0d00008003103001041c03004040f1511840814204201d03600100050b00f9110006035120362100903080c9075803c101d03810b000c0c1c41103502040e4034145010044a0150030050b240d14a40fa061041da40712036603001c0c0044546 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 144533210 1250 144531960 144531979
    0x4170c0307030806040b0102010c1407020103060f06050307030e0d021906060b03010b0a030605011e0c110307060f0305150108060d080d0c0926032b06060306150512010e0402 76
    0x20106000515030036100c1d442c0ca01c55814500b040c40300715540b0410480c10348e8505846071842503002000040c2e1003501030003607680c8010a2004038060725250b0304c40384082007014000300d1500d03004409140708030003555040240024010425640d4420401d280380542c01c0407440001c81c4494510000c00c4a010f0540400c019070f603612150388960090784902c04c0c107400401e41e9001e481d4140641c3c8014403003403819040c0294500580d160ad2a1004840c0052101c1400d80d1010400848084a4044e0000b02521142c41d6100805800d0420004500f00041d1a2a000414401d15401120701c9c2040694551002d6503a600501480100501055400031414011000d8101450007140c485401540c0c0c0e100800c0e02d044400c0410000310703c11150740342401425284003207000020f841d12080443e440d11010145000c0d1050802c001c1c45041500e1800c059001c6084c58164000108540340c00ca404182040b120b041203a007170180300c455081d003c3c1e5140041200100c0360700d2681c0c0080c0010001401b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 144534460 1250 144533210 144533227
    0xb1602010306120b04021810151106010e0604060902190f0203070b130b07050a08041b0503060109020c0609030a090302040510050904060912020102090604030609030207182009090417 80
    0xf0040b0b022007219044a46001c00046003403010711a01c1507201107074080c0c02030400140ca14100345c00c034010500804142640c1010346481a46282d10340301c4080107035840d558480e6400780c0014000c0b02d0081c0103600703000c0c2c0001c0400343c920072240030341c1103540601e0800d42c104000f02e81d016090787d903041c1148814061480070402e070304411801400070802a91300100a0300e0019140400184050207011042c441c0340300940c0c2000b0403d40c019800400001d80840c04c00050441d031220b0b8005039090300c01c08002140c109560b0740140080245802190410364900c11a103030350348900d950020000e500c2560403c01800d041e0000746c0c00c650220a1204c0882d21480840c8964400310fa0540b0201c2e04c0358104014800303951019240c202c9644020b515102c00c20000c269039105620000307203504d540740c40e2041807500c24440c4401514a0144158824207040700381c001a20501d1211700d0041a4842c03a5010390360b20700f0880c0c0c28000040d20f10002c40d5510745600b003040f00600740100740300c1c80c100700405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 144535710 1250 144534460 144534479
    0x301150807050f18280c080a0e1c020a020a050a1d0a1d0d090e0606070f0503071202030d060501080f0109150305120a090b0405090c0307020a05030d1d01060b1602010306 74
    0x24400e188050a611071703060508803000420821891008a00d0b180c10b2441c59a242d01c20030007a030002c5145004034030404800f2895141c085c1c0901034810045d500c0d03004251156000c101c1e002d080e4022901600500d4a035010060949031600c2011451081411365040903240c420900f54800d081190014401e00781640d44c1141020200c030210350354010349901801d44ad0004005000b40c0401c841394070381e500c0c01d50081200b81c80f507400060a000480e82d140b80c1000360401c200e60340325501036021402d56000d4040a96650821f400d07261300d03d414200702241c1540700e2900103124501c0200c1c80811039180c10001d80080100350720044143c0c903606000b0020038010809441c501c3c0e806405a0341c3e8040007940141001c40030780041003110401c001c00c12650b9244030910760004603814500307507240c65003282070b4507103800628000c08502006c100b100c0d46110341e50251200041d42c83c400c0010628481c0060300f00d42040c005c007410350a09110705504d01c00310811513400c0d94418140010450740343e03401603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 144536960 1250 144535710 144535759
    0x70c0c14010f02070806240d0c030209070201140f06010c12110c04050903091009090e0601030309050f010c030f1818061d0105010507060209040e0c0301150807050f 72
    0x160000c11000d200c1940301e5030300107504000c070001440070309003442c00e084030107449244c080d01001e40c0d00d0104207205101e0401034545c2d22030400050501c0e0601d416454034882d00312461205074460100c0300300003100d0034011700072003c4034110b6250000d07640e503d608802d6511031010349014104001c051034100011084000301d1510000c90f01c0349103440080c0b4240c0c03490400020302e550f014509100a004440038008291500d006003220016442100e084080311802c00340d030f02c000c000500342001d0140408010403068184c034000d40c0d464030307001e45480500c4407000c0121102030005001142200100344140c1c040215041c0c24a00b08180f240011048629400e094220413400400b0744142601c0d1231052085000070483e004020503407240100c050610361005200c0c40b41840350020729003003003020941c122107003084002e0082043c848032005007a40c0d508042c105a029618081d02d072081c11320f000350a00100c03040301e001423001d00e0900f814866503c48400441d078000b00450341041101c081100003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 144538210 1250 144536960 144536969
    0x160209070804060c020703030210020f160c0302010201140606090d0c0815090c0307030203031206010302070206270108060d230303070c120c080a08090a06020315190b12070c0c 77
    0x1580290b0510b0b04103141101c42502c801c40541d0301c4800104006500401c0d001c0c004420400016222420380c585024a4070608900c410050360001240341088040c014050540e0f000fa80200502c41e20400e00ca0043d840a03a02c9540c010003d008510952a0840507400414487e00343d00e04810740d16007441d80380000c840755143c2402d030a1010400f80721130401890722a14400c03001080014510340200c1e1300ea1085103a50010034401100107101a400303501210012a030203401d4075625031201c03508220403040c90f9000b242c0c599028414484540c030071609180614401880c102e0501402d68642034500c0600c1d40003803007003d08003124607803000140b01848c825090350710380b55030500c514501a43d0519081c4000b4051002e6400c4060203e00c0c0841610480c41481c24103400688415054502d443c00800e402003800d03000008221040420024801038200d0681c0d040c4400d01890103002d40d03668036401500040c4070309010141070100743c2d9048a40000050424460042c0c05440b0780d04c68803c544c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 144539460 1250 144538210 144538217
    0x14010315061e0503101103070507050a0f08040602010b040501030309090b0d2010021615020a0507060302090a0609150503100317030f070c020f0105030c0d1401061b0807030516020907 80
    0xb01041079040c180300310071102c100070408002040f001c44000d00c650001510309810000c0100f640020880d082145a6071260060282d105064443c03501c40710710760007406036400550901d03103014080e0826004090589505031104000c083c10a08200b009002030110281c2c4044800c100402185c181040c1c6112008002602d0b001c8990700820b02142ca02041c104000310740c00301010100300030819400e40140c036a004d50f0000304603501c010403450f01051120203089400b4401c80090241c0e050381c018440e500041d220312070b001e95075801c143da1070303041c41c8100f14088048100c0e0b49111407044000790390003885c0c1c00d6402d82c07660302d075218050000c2959298201400c1d00100f4850100c12111015030310101525010080f100140e000c00d074000b80030b1031070030306000d07010020480c0078189406032a141b101344070b010810040d03801c13403020ba80e83e002e20803034011032400026040e100f80280030140d0000d40042c602c40c82e2001d1903504542a0744404106600c81090707c03180b4006030b540c0301810340a15003d59 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 144540710 1250 144539460 144539519
    0x609020304060603060c0c0f0b06060d020a020109050606190b0a0915020f100b0d02130e01090b0f0a0207051905010b060c10060503070501120b0616241401031506 71
    0x160080484605986c00d400f409000503034140002c0c0c0d03000c02d81e14160f9004890780081d03140c50000c2041402a40e5007480740034004a10ac0c0b6030b4a50560155203102d002e481210041c1c1c60b072000344852002141360000d00768490f101c01b480402c000b08020a003458491400a100540d074a20144a05003081542070041e08a02c1e206c89403c1c90405c11505404000c0c0740c02c01080441000240c0d0a0034101c90090088410382201110114682d104040d03008408000380068009031602c1e001e0002c00300c80e4664034900c48030100d80004200c1c800d890025601100402d180c0700d1503054000e0105000d00c007103451359207d00c0030640d00d0b140d000241c004c03003a40c0001041100d50311140f10701035138003540000f4080d82c4406002c1003642e0348604651041200c5070000610011000c000c60518030411042814014000c0c50a07030801600f0f000300700b02d0740071080140d44c1c40c0e4202c0440e00e0a0f40c022b40c1d011580100050014008180d000c424140800381507000091220b44e6560220200c0f15030b1201d01c1842c1590f003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 144541960 1250 144540710 144540713
    0x12290a05010b0343090905070e0a180b090c070614152b0804150e0102060106030c030b03120a02060a0b090408030901090501050f01140a0f1a1e1c05090c090a0609020304060603 77
    0x18051f02d500800d007402c001c05440f0406c3c0220f90016002e118800440402c86030b00d00307100099500011004002500650b02403908104150782580807e0b01100c046152112039071461145507100c9008803a030342c540e07a011380c000380c08028461001c90106800244021aa5500d4054080c0801741d550311070081103489500c0c020305801d43c04040c0000600303114109601c1a0144c0e03001c16000c1c1560b00b07504000030480001038084000b0055410241d41510a460a1180d011000c038003a01c1c09031090360072503c06541e0f05030f0304401d54181515030b0f5040011500420b0001e1031800103554480d0205000244400003512703020700303462090350f0118a414440c03005201d0b100c15600d5609030054162401e281a0749401d2900400e0b49491081d24003080c0e59003411074075819801c084500180524180c0e080101c1c82c1c428015159003c80720303407088130200754030300c481e03480c628059107211f407010202030a5182003404c140301e559400200301c141c01d2903a801d4003041d030038094400b450041d4002c00700040e4843c00c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 144543210 1250 144541960 144541979
    0xd170f031e2214010e0304090609150803030601030c0e09040b0f06010203250c0308040602010b010e0a270609090305040e100803030112290a05010b034309 68
    0x1401d0400520515201d458403454240309402e000e40c2e00c820240b40701041c0c60f00b03150050510340c22078074980c0800240014680340f00d40105055920000081004c04441292407441704818032415205400600026a196020394000c003108446d0b41401003d0380d140c0000111004402c46045403a04410300c1400b8584440120082c2c0c00340e002c3c0001e520b0700d01d015203580e0106009120317000d48405c0c0700008108001000c0c3c03054000310741c0810401d4443e6111940079010f4141d5030001800515028482030f800d1034900d0b40c0700101c0d064510b0300c000f07018006188031203a07d602d1070008802c54a40c100002c05101a120b280010342c0a651b441d0f88480c10a10a03460403100900030201c40708100206000055022007128111910b011807946d8038422890b00c041c0c0b00986031001c205080801813114406183c215580e407041c03150700001c0140c3c0c1e80703c80d84040240401d9a030070701400b510701282c3c0c200651461703100796030400c0c0741c0f44111002070b114000c44102850303134002400100c2d550000c1000001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 144544460 1250 144543210 144543271
    0x5040317031b0c0c1521090606031b090a06030c0b040603140106020706050307090807091a040908040603020f0c0601090b0a0806040f12030b03070906150903020d170f03 74
    0x1400044900d00500703000e05540c2c4141c03900c03034180708000380005c41c00c000f0100802c032504035080000c030066404c520034030300c10300034000c8a00c1c2c8079900030380d0000b41a5203801b00d41c40c9164040c10f4110003244800c0030074440e5044008150102480c0da410021002c034210000c1c0c503000305444140030b80d80347d041a10080903144005c3d24400e407d40c401d00140043c40d000f095400c269121890040c1d10380e540d410302103818007036550011215028800e00401e4103111500b204117110b180c960859221000001030004030760304080e0180410700180024000907100e80c00401d030400342801c20702d0515441e42c10142c182002a44001c0c003040c0d44940460290521001c0d0030000c0c41480050043c901c3d00d51103400310b80e000307144001e0100040780410201c0034040d52107201d116401070704580f6026240c00c00c8100924040c042d20141018413014120554030419151059aa01030050107203002d4542d942caa48004041154503112814801959805134040255115a080880c070f100020409d0400c4400b050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 144545710 1250 144544460 144544501
    0x50706060f09060b0909010504051b0304060c1707080712090b091b060c0703020f18090705031c0210020a02010605151c0e0a020118080712060e030406090b0a0504031703 74
    0x8028400c5c240d00d99160180641128402c0e1404111135840c0754100700078003031f0445c0c40001c901c0040144010f1021550100c81807450688075205180054018842540c0d8115403900001e030780300300080d803980e100300c00c00601044135060200e2030921a84e914146c1c420220365a1140f6484000c1805d1612405009092510001d854070741c6461242c05250362552010700000c1d0107020101400e1403191905c6445005020a007500814030307040c200121915640d4500c60075119214408600c1c19030234014420111170f0300650004c207005080035035003c01a410000000f402c0d55030b10000081d00f51260b1411f1481505401ca50700d648900781ca103211100b56400707161304c240300e151a85840102c440090000d0b0040d4090809894131307080e9600103451261940c01c091424000d201c000a421545411000c04107031080c0030a01180d443e607480d04d5680e0103988902800200c01c0ca00c10000c03891000000c1a00385060b00d00301d40f4003616902d07070050300c0c0c2a009005907428400020480e45070a404110745004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 144546960 1250 144545710 144545729
    0xc0312151804060c0e0a030b060111030315090907031407090e06150405040507053105100303050f13031a070c0320010603060c090e09120706020a050706060f0906 71
    0x1d0605034a4004140104010401c0790f80d502d00c0301d0301d980544115001440e006207203895242e2245803000741e0b0041500c40703d0224540340c2d174950015002106880c8905120186200381800a000300031002c40068030804240c018440c1c040702051045181c050921810030007801891701d0001010f046818803480520590881400c0c00f0814060b4182d40184110072200030038a5111780c20081c0c1017107001da000550010039016400070000c03140c09005988242c0b480750bd039081d10240400f005031201220302c0007031114540e5003400064010300c054083c0b01c4c90b0811050030441d031f450000c2200100d070740060742d450b43e1618100a4000c481480154081291315104114400c2c641d406800c8003403201c803014000e10b01e000ca02062400c254002001150482005d10041408220180c54403826001c0d01309888080e2001824003a0005500209090415140c61802e5804d48030007000b50070030355485040010410046010843d640100340113070801300681000186003040b100102c5045912140d60b0307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 144548210 1250 144546960 144546979
    0xa050402130e0304060c0311010606030c0908010902090402010c0816111215010501320c06090d0f05030703230f0603010c0512060a030f110109120503071202030c031215 74
    0x2400c022044d00c0803100107080c181c02002c0c0a00c0d05468249102c880701001e58a0070300002440c0d94150440e0001007d140ca85000386511004c03040c0c00e07030f186004043c0d04101054041030040d4811f2084c0b01c0418080c90f121400c0c06028400e01c0c04221a2507816210084440300300d41e0303030307180801041540800e5040248418103944105100c0d40c041403244606101e203035038141c01010740318195a1401d41034036078074203a0300e43c4030309042600760400c001c181550b1080d400058160300b40040c000c00808074a40b41d41124030411481291076078002003183e0b0400d5141c0361200700700380550403105039500100001d014186441ea00c2c90a800c40000c111900c0b070780c1000c01200b0b109800c5400c5136035100746180203803529640d40700410703401006076100a100e07500301c00c048401d2100400840880e120243c0e900400195901e010f0030303880271640b40c00f501c1074004014610010303490140c80c0c10340a640c2d0050300d040400c4109200e0458011910710b08824a0070780130052085003482950407a80821070782c0300340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 144549460 1250 144548210 144548231
    0x201021c0813020103060b12150607081b0a06020f0a021005010b040b0705012a0206060303090a0e06011e0504050f030304030308071d03070f0303080f15010c15050a05040213 76
    0x249a010b050351091440c28007640056900c81d41104d0040d00015112965807544c5041d11044800200d0b840105880760702165a0185841c90440e000b95420210b85400d000c0084e88801e500d0600724411402c0c0d12604c8007050016909001400e40c02880103120f075140c004402c4040d0500c11040e21328800c240c5080014002c00e0f23007200c00d4800761102e607002d20b0f88400203450117034010001c45000103440008428407003c0305201c180c412500d850f166083c0c1e5603d8460000b890b80e0307401020030082e8040410b0005210140c10000403950140e01450080380c2400711206140c00030181d821030030005000000c05100c3c2d418403c1003142c1c02d107001e030021440c0c1403441d00c0c001d0a544c00076000408000780c161100e080301c15050f410706030000c2c0040507106119034406c2007102d04111031108034086540840002c41a140b940501c80c4a10b4544104169032030303070303400110b800102c910400c4520304007458550b1003850b1140b1410744501360b0214001250306050040004060061032510130350303428401e0300d00c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 144550710 1250 144549460 144549467
    0x4050402030d0c1a010806010302030d111908120f060f0901030f0308040c03050706020703152a090e0a0603030e0904080d05190912080114090402060d020f0f070201021c 74
    0x40d04034034518140841c0d0f03000d840c0550b40700069900c00001c2c988800004150b044011403124100e0380f01310102c0c0c03005540e00d0810764041915040040c2c01d030b0003645049004507000c40d84807040328880d0b55030307a00d0084031100240704040c0503030f202c0c504e0814880400c407050a0696a60007a41402c440d80700b055855039554540b69680c54800904000d4050082400c00034203440500256900800b034450117610b4540080d602d000178881a281c5900d140c100f0060700d4402e10502035525420003021107070b0104860210000c809071050381040081c04140003400030441c80d0380034014621502d01061003851803c0007030003241100070991007070f01c400c0140000901507000f20760001c15a000041115682c800d210596a4152881c0c0b403003960500c40700314200b00d03100c03c810b03e4030620364a42c04104e0b40c0301d001c2586029070040c00e10381c022003584003081c05460f26201900c80b01c0d0008402510f0120707003510045242d00000180c0000c1c00c0c001c14848210343c1c0610004003d0b00c422041d24980780d05285008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 144551960 1250 144550710 144550723
    0x706020705030c0f03031e0d05070c031e021c0c0b06010906120903030b120607170c0406030f020d1d01050f060d060b030a023307080405120313090504030e0405040203 73
    0x1c2d44107214055054180e074809005440d440c1c185041220355512001f0000309031a48402000310303002c1d00c0d0000040342180500000c590441e00740c1d07241d241c420400001c0d00b05c0c03544c0c1d46018005511440080d0a5522004641d86a80c0c201a031f441e032803e0100344c0352031005c01101421a41c140500d628086c003181e5809010164000940c40380442c070b01c001802d00b1b4001304020320344182c00545d04003882d40c40080006406000e081c056807280c903400f80c030b4084aa98100151138020554404020820481e4405d401c0361089280f43c1c3d50040c580400c840441003168080c6581c40038040a14031810f441c2e000070300ca40381d405812001044814944031380010183d4414840013004140da500c981c0c181500e0400c091203030158041d150b00d047d620107072a25001205401082c00030f20306803100d0754890b10207080984213050b038045030b510f08050404d000c100e00b80d040240b490010f44800e0040040603055510810003c0402040c001401e04207070900501001001800601540c142810f200060f03d0010b403c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 144553210 1250 144551960 144551983
    0x1050a020427060306090c14150313020114120118020702030a0b1f140418080a0c03021c0302090a050409020a1e080a0b06010f020f06010e070c050f0c03070602070503 73
    0x203418001c0d260540c0b00100308940016021626002d065410803440c9100801610841180c1e180d2801102c1d0800006040c8284003201d00b50013071001c00c480300000038600c20114814140040c202069a02c4040c454025034061541c2070100030042100c0852001030b50207a07074078a58103502e40318584c0c0120760b03070b16481e00005101d0f1700d10f640001c8403203100d8a00c06180075040101410b0440d40c0d0070201c50340d80f440c16000d03031003103281c502d40d051b1230f00302c4071030060006a100a8041c104500f44a041e01c6404800c0c02c29404e40c0900020b1034010741c4005181103600613503131401a1a41242002d000c400120307900b115024a00e80000b60740940d441c401c541007203070b9505000d02500300124030000c0b10072042d40d000c891648500c1c07420008100a006160b449110283d0b05c00c2010944981c0490f580c0c80045102c9945422200041c040081c6102c4655032049440c10081a405401c0d5142490720401080300d0f203e03908081c5918480e4501801084c0041001d0710041c0102814100007070740300c0518148 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 144554460 1250 144553210 144553259
    0x307080a120203040c080613030c0809012001020408010b010503012301050c010603030e09060904080307030b010516120215070f08041e050618030a050307030519051801050a0204 78
    0x24544409407140200c408070760121102035403282014500b082c03050007a0b000b052800e0051000068400302190a0072081d903425564240500c9001d840340c00455000c603551a040100c4108041d81310524100b8400c0798048a5000694843c6403108aa08490110900c3c80c100007080004010780c000d00641c02c9080c082c1040d1703400500407070500680d611300c80d11010403034039424070400105054100c04120f07110002515050031517501e00041002141e400c49004008200038008240294400d40c042c2e0f6243c401030418525001300c92443d000e452611260440320540c004880521031075062056101c14541c4920b500c0b01801c1c28040a0b1050100070440c0d8200414000005c00b41310400800c81400000b004070b0b4403502840c0d05150340c83d60304c100d54461040001007085803046000004035201d410007039440300e0464070344032021400340101801c00c0740329601c60203290091200c135104450003024500f50000750140410201381c2510341c0100b84100315481400108000c0707560300301a02c10100340c01c2c5c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 144555710 1250 144554460 144554467
    0x50901050c0c1c030201050c0307051b10020f1c09020f04150f080d020723091503100203010528051908030c0109060f0216030516290f0405030708 64
    0x14414604600a0441c0342c0c0000100007050358908030801c1e4050003030117a4020700c015903032824040118801a6100000600c0402901501c030207000402185500007c00f9110001401a0000c0a9030002007034603102103000107500034001c2190600040039880c40c8028440382169030002000e9200384841a40515201e400c04091900021080800b802d050f402e020002e640b00c245403651303903508980c0c0b0005032080010110701e1103038861480d070220300c3d0030f95410484143c11050058044e8058002404540c2540b514030307069405200520040610301e100588944c5054204900c0101c0040341592065100300b0300604040c40840341c07010b5900c03e8684081780c0d0078101e8046000c1c007484c1d100d1a103d01000c07995042108064000e448000e0003644180102800c01505000324801c80a4564000c00030000400010b8000c10160141403e1a81079400028035615011880c003a45807140fa0717114421080048440c14500d8185d40040c1072909080081c030b8503542e900e030f40740b01d9100041c0c030910012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 144556960 1250 144555710 144555727
    0x1501081906031b050102160e010b09011110050919082a0610050a170d030f0b0402040f09110c03070803190608030c070b18040b04020f04230109050105090105 69
    0x503085600155407004245092200c143c144aa04086501446005025403622242c03440902403030502540c5d440300360341b512070b40703000c81c0e141c034a5000840d11410b202d41d508142244000900440d500f28141080201e145e141c40810141000b8050110034a05542c17003038088042026501038030003140742400340c11b21486204865484442280c810180b00340f0170b100420a25104c5281082d085500a584601e0000d0315180340c00042c10044040100b19400848001030003403081d002070804080780800000c44040d05004a4280d0388181c00c003081443e800c1404002e030307030064810b20100483c1e800c41c040c10003100f440c42c40e4586c440c00d14007030103139403001c004034600d0300815030040d03446d20750300d802001407569500015489400c604903940060082400009101400800b10380e007511107095950750101d20007003040000c14445201301d80059007070001c000c01404480082001c1c2c40381030b03840c88481346055101000c045075080810304011400400304403990700308095403c44802400c2c001d840e1300b50b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 144558210 1250 144556960 144557011
    0x510060507030503040f0209040f050c03010203060f1c020405100e090c06070b0414030304060c18140d080712080105030f01020f04030308040f051509012007020402360108150108 78
    0x35100c088e5029540c0d405010400c9404100218a02d2140042d90042c2541000300350803400f045890580141c006841460075182000c00d800e840307288000035158058107500440c080358000c0302c1c107242c858170000c1e0900802921024241c0d01c4140940240800998080826254001c1810041400000f140070508101000c0d45d032841581000c2d040b00e40301e18041c1001000743c413aa9815802082c40c034001c0d03000c00b54009a008083da50094044000c40c03200000384562040081c200f555000d8040c0f003484005441e0700c034540101500c03aa80c040065040004040c201024820000e080340e10401c810180070030650141c3d811280c040c2048503c40da501d00b400e9030f000c48455001070090199103210301000f41030140c02805502c510000304030001d002211000c50f40c0c1e645404800c0e401c0240b02c0d4100602c2c0540013000303407050725070000011901841588081e90404c2d107140148100c100f00b90411075034081045a40303c2c94012204910b41e80d0540041c080040150070201c040c80d5502145101509 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 144559460 1250 144558210 144558233
    0x604090b0a2d090504112202070f021801150f03020904050a1d0c0312070302010605091e0f0f04060e0309060a03020301080c030a020306150d1212051006050703050304 73
    0x407070003070245100c0340c035030702c0a41d03401d440c080c00c0c4019010800c0c0100c2c04002902c00d44d07104550040c8031035a28800c5a00b08072042a040005103524003055004080c420381c03a00182c200030740320f0300c0d1808100860b8810001490080c1d0317103440280580d0401042407a9800c81c0d0302404c003000e030a04061265019808a019105491066070498104800e003c694a4640d0095070300513881d100c030602207256151800d44030003c404545505038845060412090035000040522510030300001400568600c041402c0d81000c6400c034400003001c084c030404001c1c4e680440303131303000307542042c550315601c0c0100a0b0000e00d00043d002400341507807000c00c4400101d00700708580101c3d5000b042c0a03140d10303601500070302a5000f4042e80405004007a4240a40d040018403000c2455004002e88070342d81d10454905504e202010141e94040590b2800f0008154100c040c0300d600c514569422428802d001b040e4020350b500680300d0301c0c1044022000700001c952080545582030f926140c51962500e0b01d00f40811143c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 144560710 1250 144559460 144559469
    0x309030c180e030a050a05031e07080f0901060303080411030f030408010605010e040e0705130908071110080603060a020d0b0301060801020405010f0e010503010b031909050115050904020604090b0a 86
    0x60004000728a04403408118124480391000501078a48000c025a40368021110044040340051000c14020350003103001d5580b1465207107903040c1c0e10281c405500e400000685e124030100e4184000d00504401441d1003690080114000b0301040380b031580c1c0202a410024400b4107400d12a100c142c2060780c003806810b01c56020380c02126111512440c3c842d0081149105890100d4545007001c1c00b071f414280202e54081300c00394058021940360100b84005030b0140d000d2000c0b281d075203910b4540091400c0d005031510502841c03034903400e001090305020354010f60044031400d0003c00400c00406a03000104c4641c48640c0d9880580c44030010403144015040003020a6459424084045540070055018000f10b1b2803d07660240302e00a60481030300d10740c5080b100140003840c01c000502c852040c079802142c0003101c0040c031020070078030a20080200c0d203280c542182d40d40d4444440012405c2c072803907818050309048510040c45d0825500047da2441188114824540c41c0e0309580b4040d5a02d040010042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 144561960 1250 144560710 144560723
    0xb0d18060504050c1206011a070206311e090b130612020102151302102c04110c15090f030a020a06140c0d0510051305010f060807020a030309030903 65
    0x9003072903d480c0e030300e814004052034022282048401210040000c0c03e030304a884c1c590002d05003e0000d0001c07403003680318583c16078001208205204190f902440d10f090031503180d01001103090580390400194018684c040c1c181e040600c0805e0402400400c1c41104690302c0b450b002512170301c0c0c0303000701d007001940c141c21060803413411034001a0b2403184030007422507500c00d90035250b03500f42c060a00380400c40140c420011000030b283c000702c01810444040c001c3c40241e81000050300300c2180410078103144d000c24041503007404a09001e102e0610b0b000b07412600300c040100504015800003455035a82001040c8110180c2000c00b003030701d01809220240a02010b2010b030382d602c809924010307503641040402101c1e111300d8508400e43c8500040600b03405a400b9031000c0349030003072400d0010068070000e40340115280e4100e000107020342d5603074042e05031507203d480c020032198500314400c4c40ca4200c0b03610000c01c0c000c0500401101980c04101c0040c0c19526040014450703000341400c9411000740c0e08020711700c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 144563210 1250 144561960 144561971
    0x903030e0118051002150601020a050a15140703151a0d1104050a03030c1104110708071a09010b0a0f06080c0a020a02060f2a030a1b0203011518060b0d1806 68
    0x2280da01040d112008401c510507250103880c0e1034012030750ac1c4503142c0060002d801c0343c0c41c018002510039040c0100f03100c0e00400810b1018100c00d5207a20490280d540d80003296540518060305442e8608074401800c80401c00240800319442d0b0000314480da60911000a546a0407200b0040006003900c0c041c00011b030042c0c00c040d40343d1402410112240606403000009508006070504e01400307102607009000313070031a05051150342e481c400394005540445141e1103010191440a510360a144e10a0107080004640683d150b401c0c003182011079042440440b4403a03805200d0306801041403034000c8400e010309503817140d4000080b420b003c2078000003940845d000814189080d1114040c01103100b241c614580302c040900506215400a42d071140025041405064181405101111158405003818809011095001900311585000b0fa0201740c580c00c0c100344420112003c0e0101c052265840405c0000c0c1842410503040c0900c082c01d4020319120107540c9001500d180500007080c0e44942c05200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 144564460 1250 144563210 144563239
    0x302070512070b070818030702010f0e0312193f050c0d050a0b030a0210030e0609060423101509050a050a0b010315030f0807080705010b0108070903030e011805 70
    0x1120b0400b941c0b64130009101e800031544880c82d404078660503e00400081d4079100b2a680103640c0c0e801541c0e4000140200380c0610f281c9510180241110303840080c9181b90384200703091204030340081c0c02611400f0444841e141001200c08040310f048036040203032444281b5004941084000703000f80020702c481e2030a090a0000015405002d03200c4020000c0b4240480d0381c400800300126a551481503602d03601600420380582440c5400c0302c42d513805880e021450355010700780d851800000b510116090f81c8070104100510510065040e4145080b41c0d11529204154100700c0c0c4c0c6100c42582c8100c45c9640d2420303e0041851000c8450050400540902c540d1500d003102c403000300300441d440c6411904010f10f002d181c1d0b11034480c1c0c00520f011407080780a031500b540c549065032013000380210f030134040401084001c40c13480405002a548100004680102c000380010142e1501805003800d01802d00010700000c1d401c0092028916001c0c80d010303011a03842d091304609a0420303441550884043c0c402620f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 144565710 1250 144564460 144564473
    0x30201320f071a09100915060314011d0601182d0f0b0a030b09030c032d030103030c08031b040b0901031802090105100e0402040f050906030a080a030207051207 70
    0x7880328003d800c0d14500701c08010181c0c08581046408604035005070301c08500f126070592262030903d002d601c4c4481800030381600c010031a50547c0042c0d541810315008508200000d000d20440b40d03602d185e0010100b075202045642d22072040c000c40015814031400130560f03294942c000051044c0203030640113900c40b000a48060340c000d010002483c9824800402a12042400b0741e0176501e030080c284080349483c54407004400e0901030813186940c001004200c020b1031041001c3e1482c4642030005504a1860710020f0911038a0000540131801050004001103900100e550740301d103400c40741c126521399a18146482200389007914034009800845c01103049500d0501414110500780c0b000c011100d020700d213442000c20a424020b41c8045100010300180c00d090407604410300913030624190313002070350b0700203016600290406400015900403c020500e024544a50051010b0703010b401d070f111440d00c0364000c9100706400740c4141a00080c03030fa000c0200801c250309d0141c00c08504541c0300e40e864035041c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 144566960 1250 144565710 144565717
    0x16180b120f0108030a110a0c1e061115040311150a0606090b0d180611030a0c030903021b03031215041b020706030f0605040f0f15030201320f 62
    0xc80003001550004540011441115050f80e0f124401035041c1254150126000100468031103a01c0c0107103480c0b180062070701c0c207094010f058202d60341e480c10f90a582440010003400c1c1c1c00101004195585038140300700c08140c40c03c1c51391058140c0300d6240d80d20f090075115918084039066403449120700b03c14201032a03032130f001d02234103030404c00b0300c03620350740740d1040710a880390740a100c04030a02084a00c105554542c0185501d001c001000308a40700f55031544070468828104002500100000700255010300d0b01ca0600300b5440d80c10200300007566234500941d211021001020b00c41c843c5c03501e10040ea50208240d4500310399014810f0418038007103400c0c4034040c48000790a4022803d040ca0120114a103111602c4c01d500c25600a060a82c075122088018000105603102003070b5451401003419280d0b4082c5c048210404600411400503411510045680031224003142d841c8000c004c0c00141c2e48101d01960300d0b100940b1075042c0e25007800c000141d44c010b41c0084040d054001560440111012026 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 144568210 1250 144566960 144566977
    0xf030702010f06123c0501020a170408090f01020712060609050c1c050a060302100e0a050118030b1806090f0f1f091a0a02041e0b0316180b 61
    0x24401940e507200e158000c8859201d00401c02c85120003140d0340c07030130800d040101ca240d48880710358905030001117030228412100d00a41d070356500090700d05941a000f008600c40a00381100140341c0b86010748696500380280c0000c188188624110104e540e84200142006491403108001c1c1f10802864a000244290b104180c101400c20000030601124203055a22540044101e005444103070b21000004000003040040065a00d07000400940c03144194844070401036112943d800282e0002c01c0b80980300f99001c1410001d00880e10401c82400075581804c1360b50022009440f5112035142c080300d803100c10708400d075510070901003095507400002c03240801a440400d031681c0c803a8405003030740c4480e0000f4286502c8100d0f521910881106944038006842c040ca603810b855454840d8045030078034007503507000251500480c05000c00e08030364856000752160a0345520404c0d01e070084140031070000070808152048032241b030540755070040f1900c6c1aa10700040007107071060345440c5840c909811060a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 144569460 1250 144568210 144568241
    0x110a080307110705040606020309092503020307080f01080706050c03070f11130c0512070507020d05011b052712011e0507020c0a1401141201080c0d030c02060706020f03070201 77
    0x14000b4450400e1b110310000d84426601461400c2070311414407807001c40180c44d441c0c0172000084045c80c040039001901000c1ea03500e030340241c0d60341010b6000410400000c0c001c820340f82c400e8001080105000a040c03070413034102e402c100e070b1101a100101811402540340160030840e40c001401e040114070b204100804004864081d0313060802c0080b003040700d10080741d0202140040261080d94460007000d01c1d880034051030400c2c078241d00f950215409240c281d904407000d0303440360042e1481e0504960040c021000900e0014140b501022011440c1d072607145d802c48890060040310700036a181d1401c003003602030f000740080c0480022140b81c80e0044c494143c1d201505813030030300480d440303510200303201c0a14080180030924071400e085001c0020b4030995001414005c62400000506810902401e021000217000301c0c001e6240941c084c2c1444070400400d44120009086000000e401051460446405072002d0752501c002c0e250440c000d10a00d805280c407240d0110800102641c1500402294104400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 144570710 1250 144569460 144569473
    0x2040b160c0608010e04110409051f0501062c011b0305120703020c030304020f010e280603020a0504090213030b04050604060e1b040b03070512030d141501110a08030711 74
    0x64111003c480a0150369900011500400c01040d26022040740b913050045c000240710301c15541d420710302200301c0c08520303a961020b00741110262442c46074a0040006040040c5c4200d12541000d80400c2103581036060309c03205001c00ca449034070400940d0062040500b561000b140c01d4240907140b5000106594a1100ca5800268802d4402d009075014152004015411038580d41d081100e01c8040300d41081c100541c40d07103208220365586000c81a00f80c842425118007002c144941144a070301c41e003000c02814010868220140da00804660444540f2280140c0322040c2952440a0f0007041e400a800c03040110305010610401060340fa0083d032107050100400c140c00f0071401e40f144003608042c1a10f03014500c889200d805c01d60000080c000c402401c0c4c94803903840c0d90004071014044034003202641c3c8049030610912810b031203a0f42d21682410303d1100c040c03522614030602100b4a441c0d003070410bc2144105041342104000c0016401d0b0301070841501c901e848a001461000c400204103600d21826 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 144571960 1250 144570710 144570719
    0x1205060a050705190f18090915020f0a080c041802030925050f01050705010f05010302130e060402010c020607120f021e0309011112030a090c0603050f0403080a02040b160c 75
    0x120200e0304a8004c2da104012507802c0040d05503a0660b4121006040c00b80f881c10000c4000500000344001c1c00c11644002501842d5040c0206185403040c0c54402c030a104111000c00e0300c0d8840b0030b035030b455651450841042d94a100c0b0b240da171409160b2040d0705106062880d0796900005802951003146d20100301d90301c243c0801c40c140340c0810040741c141502c00c0c414a050003142460301c3c41861801040c10300501e0520700781c4e0384a085a29002e0201c0707490b0b503550010310852402010407844002c0300ee0b018400481203c110319150000640000e06104c850310240e411904e6002c1690341e1150409101c28500b40c0409002d05150945078480c2d00501503000d890301ca0303244003000d6081d01013020000714101802c010054681c22491a00043c0d54441c1e041e10b107000303500550055219200c0f216001c00c0d80c02d00c03031406810001e541e8000c0c5083c18280b00c200144003440c1514140d001d1340600e8034010301c0d2114227149000340b041c0d4022080d45d910000307201c000341a002800420381031003450304814a5654 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 144573210 1250 144571960 144571967
    0x12120d020315090709030311030c070803040602061333020706060509010f0e0a0506010c02100914040e030a0f20070503100212070518040606120c08070210151205060a0507 75
    0xc980b05401718005c00c00520109102e0707910fa0004100320011285003000d10110f9524056855025098039800020284405507051107401c0d0402d2000c2c1842d42c041c180f60340d400b018042c48016022019091041c076200c1d8051030740c90f0b00e2654829000c21560b44076030303003407080142049005c3c040c0150320f580300004480c40c14450200c115403510b90301007010780740c10745e0540140c500500954100b100f484603401c00340e9290301c8c42c00282601034440409a61400400c08003101141580d140700c2d51901404034030449000c012100004850b00d0080880a441030341034030f080d01500d0210015071801d885014800d0000150741c800c0e244118101c0d884044009244000c0e03101d10b01c4c1490301225604040381015001c0c4000d01034540311400504000030794603001c0313421255280e00130f40008822340c00643c80112548142561180c4c0b078903112885140040c0c02075601d8035102540c140302a900c01c26540343c1a403048a500c0a01024650107200c60a5410107640d1601c0c00d0f0f0302d05040500d000c020509181c007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 144574460 1250 144573210 144573229
    0xb090607060203011d0615180f040204061701050117040308060a08030408070503060a0e0c060d09050d0806010e01080105030325080a02010e0f06010302010f050304031106010f08010606030204120212120d020315 92
    0x1603e0320350301d148c42a0700540104000c81c0410090b00005c1c131101c1070403c0c0e9541e0001d0b10117000159581c640030300e548000c180c02180113a000074107000403030008058080c418001a5805501420801400d07200c89010401982c2d159209034183d001c00b003130120303c0c0705001c140700f41190003c80403549161500300546c8100c0b03030848084201070f8000c8410508508090001d451884607a000002d002c1d0255220b8508101e00300c0c40510000702c4000400c882c1e03603081494258004402e291415480d810503022130b84d00e201c0d02d844008100884036070502400600800c581a0303e0b0700000860b2a09140c07003002c2c1c003030200c0030100c0310203004140c0f100040540008105048a030141e60f801e0298001d808c055900d0307030010b04142c0820445807602c065088040003ea4001c1100900d140c45443ca0840e00e42c1c211046078005404040c0100010451115040c142000c0d2640403111520445407034220580b601c0540c2407810444100451400480c00f03540c1d01039889a4034181c0608400000703802004104d50703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 144575710 1250 144574460 144574489
    0x501020115050a0e04080c0607030b0109081b0f0d1a04110d0b010302130609180b0115120b010e09150405060d03080703200403050609070506130b090607060203011d06 73
    0x2c08a0f0000c00000a4000301150844e0217038210303610340302d41c0d0b0115500b403010440b00c950209031514160601c959008079080f00030801040602903041c071484014000c0d042d108120b0388108440c004a080d25030756103080f000e815901010f2900c2000b03c2800001d0070b080121402d5448821200d800c4280b130805002505080341d010f400907065a0950f42086010140001c20307010342c543c0c803040424103141070b02c10001a02c085150640c0415864607240b1a404c0c016005800ba00a411f22100390598115440002c0062626000b14240e500300004a420004013704180c0c8104c1c4c81d401d2090401c4071a10714098000c090302c051209540d000c040c0709120030f6001005000584040000c0e500621030350210540107440001c9080040f02410300c5000d41e045500700b60340b1500088244107040d13100b0490140101010b868540c1886c0040352101061f54030f61080011440c40011860200e9403074108031501158040d104540720350311580c039004401902844041c3c80c54010010803450316103544140c000e032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 144576960 1250 144575710 144575719
    0x3031112120c0307030b12150604060503190503070804060f0e010504030804030609021302031f0509010b0403020607140307060b01020d022b03020c030c010507090e270c0301090804050102011505 85
    0x103031503441050000c3da200800060030190389509960503903840c994501840e1031079100030041c002c036881c604122090301030300040c4100d1a1000400041c2c9000c43c0784845a46802603c0104010303d040c04c5040d4808d0750801031071101300180120f1070315000700008044402540e070ba810044550001520702d03200e60302024044620a01c01040001c0b243e4100f10501d0b88054409030f0b031a0170b0042c0c4201641c105851180a402da00c030b03d00c2c0c054088444441c0c0080c50204c480ba0001d524002110816225a000203070040b000050078000348002c014400703404403c00c0017201c1d6101400c1c1041d900070726140308500c3c010300440c0050520300d4400900c020f09483d4250004800c0e8802c803000a10500b000f00422052540900030b4800d010028406010b00f54038481c008101d40c80d16110007400ca00c000e804c00e24400c01c00000780b04110003201d070a440003076444038890281303500b42c1320307010300d4201c01080c01e40d859030801501804009080000c0d100311903083c0c0080c80540c0707000d2002003004444e8001d2a800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 144578210 1250 144576960 144576997
    0x90b0703020717011e05011409101505121306050a140c0c01090807060f06060c11240712020c01020309030a060902041806050402010e090c12040305040f03031112 71
    0x800d8120000f400c3c6a20300000291142800b04c550f43d0b00411220840b90140e654401040308400780b01502c2c5120504a400b0811440c1c2000000c030b118400d40106c0c3c00c2090b6030704201c44241e000c2d8045801c4002107940c24006480c2441502900d03134540c0303504442807070504012440304510f500402080c0e0074008011003040c1d0780c801d0103603020f81084030319201542d225041e28000c54429001410124080c843c08264000781c1c100e084283d4406502440c2042022410640070600c8000b4030b40100c5c0b001c070b902c0e071450103107031844924000c503000e140c80c100701e030006001c410440c510300303202d407000c0c00c80d000d44a5021041005907200d0141c0640c46805420031120309002910079840f40241c903100801c0041e412008a0003404540c1005004440783d964480501045d5a040108180038260460307005905251400101e81c8601039903009078003200d54180400d08050083c2d007942c0c05052449881049a60390741402400a1000c0c42905541e0103502c0c1621440e04d012011a242e650300002c8a081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 144579460 1250 144578210 144578219
    0x1703040201080f090102040b0a03091b0302150c07051012050601020f0705010804150c02070e1f03080703020703150b090609040c03140c040c03020c060f010806071211070c0303090b07030207 83
    0x3d000030004d2401d03001d954204000301d01c518241c0b02400714405540d40003e1050a28501410314503401d50300002c014516000400040e038400c041124000200085542c0310000800043d15203846600800c0d800161440d401d9403140c0d109070948244403280c0000d009a480c0e01d001039072140240b400382d400682101f04107000a5000d51350441d00035205415940702d291204a1803030031142164803420050b0400a800c00c6074100d07070b41d4001d8000e04215100c0e4404190452076680e85c280c18070000341940008502d42040c54001d211042c000d507009601340c2c100f803051890000090070b40c196240d00c1010341001103240303818203c07003185c4a10b03130002c130b030100050443c1c440040840e1080507070700f0340384540300d4842c4041c0c03111700a0111000850300e001d41c44000e4411501d0801e000185030036038218895004000c80800000c1c0940c000f044d5040c480d0400300c4860711000604070040010540c070900154520400800308040300c1182c2c02079454908840e01c820452605115811000e001603100e03880500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 144580710 1250 144579460 144579481
    0xc08070302070c050a1415190f051227010e03030c131a0706060602010902030a030311090619080106050f120c070506090d080601030b060f0a050702030a050a170304020108 75
    0x1001d980a081c2d4030f08269540c400142e03a02c00d03242c0101c1542d60301c1105504a6040559030b001c2c0510381005000d041c82c1601802841c001c504800715420444a080149680c07400303541101c408203100204035900e407500c1c0030030319003001200311030001071030703130241031040102062081d4400b02144401541c51070300d4241100090f0b40044090440030b001e10400003c441c040c203070225008803500c2042a13120100d5041980440303d46038450386c20b59042804c4500160b5021500c00821a4103003400540811007442100b801d029a4148c650007490016280e0170080700d9910030401c0f41c0d00b0703680701e14250fa02c0d001c048401d40205108860351141c1402607968101d0400d6a06500c0301070b0300d00c87c4d810f1142540724985410b41c2a00c8500709600400569040c05500401c00c07a0303c040c0a080c00d1000e105110082403140c4038410080710040b46c0401c2c1000950310600c11119011780041c00c80f08140c425080c05501d0700343c817080459160503040c00551003a100740d42600d11441d0142c5a001c100c2d51450f1101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 144581960 1250 144580710 144580717
    0xc0a050f0405101701050402031009030c030f02010f02040b0705060106020a02010c060f02070803040f06060608060a030b09010f020f03010e10030809061c020a020c0306010506070804120305040f03240c08070302 92
    0x80d50103c0d003808003282c90f408111038008010541c03c00810281060b00606041c084847c03841c00190b800d000400001c00e802140ca0604164141f8252200003e409800c07401050000320a402e1980001000035158a041014210143c004c600703480d035136640c1d004180e0ba640c2c003100000380032420307011045001c00c036594441180c48181039400b5181007183c1c1d690000561003107034211450100c4420030f100344400751007010090070302400c01001c0350503c00b0001d00d200c8080e21005080a100c2c100140828100b07400030034030b0340744048055403684242140681190403d02403018401515800140d03c43c0a944800f41101d4011002504d40f0b164201480b01c254802d4141e1540314080a10081440c241d51000701406002035000d4103402c0004010507060007010b034800c6119140901514011901580441d0103c8a1648128146621500d410703100750049502084801602e0b54000041c03286403c031464100c110120805140030407959010100d440c030509440008117140c00042c0010f0090303005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 144583210 1250 144581960 144581971
    0xe090f091908040b0417010f0b130c020a02090705220f0b21040b07030b19060f0c060507030203060418150c050f0403080d0e19080901110d080402030c0a050f0405 71
    0x141c0f40380c0394807412100340543c0140d002602c140d9025040e00001c410a119000d8180c80c080c006018880a520015064a01800c0c00f840c0160b40c9032194402c0e40d0003040014500ba901038040300c42807401200c06886601700207180e43e00140303c041c1b041c00e41851103c092050301e104100300300a250070044140300c10b030072020001c0225106150000c508014074035403c0d21648c4110525046450039400003403e40b00b80b0020175000c1d1105040e80286481e0900e1a04103440e0303103180c0f0400302d1001c84000c81d4244010780c005000546010203001c801070b0705400031486500c00341c4080c400c01c01c00d000000040c00803180080c1003030043c4804580042040e401494040c542441c11034104540d101c218900340d4050f90044400d803800140540e900c2c01d050150000441303440c80502a81d985100201100303451100000b80b802900152046481e03005800381c0d059030203240c04440714031049460180c0b40742402ea509900c24420b20700e0401c5c3c0c03846d04403055000d848000d84056450541181400094800a041d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 144584460 1250 144583210 144583223
    0xb0c0711060d06030c05040908040b0c15090c01030c0806010203031512070807030605010e010312450b1809060301020d050c0307030f060e0619050306070e090f0919 72
    0x4440105680d00d002400900c02d040d080003800702c1c40d51510400c01030a50780140d0180d4140401c40c808960180b06940848410880090380c0d4488800d030fa600b00b104e00601407190510b9801804001200011041d1110a080c0c0f070400980c8448502654480000c5070401d0040c0c1c001c00c009502c05508021003031440202500507503482d0910450780c1d0820380742d070700040c1256020b64010418003d4a00a5a004103403403080e00e50107504503101c0b9041c402941d01004180400114400032240c510318140000c006900c66080184991904412100c0084031b11060300140c0c1440109049e100c5008841b101d00300800e0016443c8414018840b5900000b40f0269040d5400e0010148421150203001d1051228940156aa00e00001d0280031116070000d00c000d018500002484400e0300341203103540049048034510a01e070b4a0681005114525401c0703503401d0701401e014030030a180c005030480307001101100d40341020341e1244025100c0d81c2d8111a25038450b4400b92031061020702500e18005020301905 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 144585710 1250 144584460 144584483
    0x20d02030a0506010803120f0103110603040804050402030406091101020c09010510020f030a090608070c0203060402010e040f060305031806030609010512030f1222030f1b240e06040b0c07 82
    0x1210a0b0900b0b000364842c0b1096000000c259918040740a881c2c8c0d4400321860860088c0d50440d2641d800e01d444a013019402860000041070500c00b00e00c2c00c0e80c000b4400100255683d1a0928188014009229080340c00d03501c0c0c1c6101544a41c0041010030000d00302600000e2181e10702800c020a81f190000d41c042540920071060f052203a0034401810400c500c1c0d180d1050440c60400c00800e06d4000424507002c000c1c0b507202501c0145c0c0c1c0803a0094000c0d0302417030419400500700c070008000344500d02c08071029602e00b072000000c001001c00030340300c14003280c4400042c0032888024480c141c1b008554a0764844002c40c010f100610345007002030035059901d0f0440317040282e032075045900c42d8050340321412030200c0c1c103081041d6511f02500b417510041d195900c5c80c845021030380e0003800c04e200b910b02000901030120020700000c15061800c100183d04440c603810510440004040b403d00d030030b8a8041c0541c10940b04d84110707100002c2942c015940868401c0303256842c0741441403190460103003240c83d1030740300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 144586960 1250 144585710 144585713
    0x504030c1202220216211106010905180d02100606140301030b0a0e030a09080d0903050d080615070c030b0c03070f0e030a021203220501090501030e12161505010b07020d02030a 77
    0x10400000300328804c0304c107031102e225094000d882d0b284031008901c00304000b15602887c4d50402180070b0741183c59400010420b0b44440030304000c5502c4008440500b48100e05844140c958000b074980785490300e8800070005240c441c502154150510005401e001504000420000f81d00300354440d4006601d401c00641c285180280c2c6055038801c2d880c10740021030041092240c0001804804882e03003190805040c0b462039540c4a0791100c1c6090140014404a40005030342d64481c0305102000400140000d0741c1c0741040d207828004061030b4042556150004000155070039007102c1101d0042c107154440401160301c0345011a51201d0446045030580036a941c404010380305c0c058150400180580610703118034640f072400e4403c2d01181407468003003c101c1420880c6981001140d0b050358002e190105000071013058003440c1403641940400542c10000c1c14095245507002004412441a14100d11010b00d81c00c4400c1940c0c02802a19048401001548014500064150070003440681174032800b40380c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 144588210 1250 144586960 144586987
    0x131d1b060d15150806040b0a030f032007091a03120307051608040612060e060607060914010c12020414061602042409140105010c050f030304030504030c12022202 71
    0x1607103d03203110044401c0031200300c2e4000c540c0940c0305400780da00300200c90b2048001031171900309201c0a400c0340445081b035401d05205114404444860428045a82c008940b00981e60324487c40340340b100c0c501d00303003034481c484405214402c0c1901d4018010040b0303480d0802d12440300d40c4003070440c00074828108808100b4449400c0c0f21460640180303c907580301d601d00903001c0c00e81503010032038810b103070314140043c0f002283d411440c075004401a01c080c0d880304482c3c0f5240d401040c005801074a0401025422041c4581c1500305134540b2000e41e481c00707080b444803664801607004900683c490011464070050780e5091084c058002c1c44480b080c0d00d41c0071a0703142c0225044415000d6143c1c0c0c0d031301054000010036010485000c000f031290f0300c0100f1000712120764084071100c041c014076040202644052060040070840701d95a107102400342c942d41d080918001d40340364410301c42201c6002c10746c0400603604401566085242d9005010400115808820311081c5c07101302064107101c80e4240f0450590040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 144589460 1250 144588210 144588251
    0xa0b0105160c0302010f03021e0918161803080a03050c041e030c05030a020303030a05070207081b010216080a02010c03050c01060303050c0606040509150403020705131d1b060d 77
    0x142d50910803090860000406140040c04800c05142c0100075413030303501540ca80b00d81002c81075007240030740f00c052600c0041c0514400d062643c3d80380807110188081c1418104611058000e1354580c00d41490307180c25285500c003210b10010b4030240050000740080317400303504143d5201d021201003500d095100c90501058800a000c1c030081188010740520401800002c0300006e040201c0040c18070040380e6001940ea0700c4028501c401060f103c001050109001b0030909000d84008400e940b42c0d40c54000744000c4c07a013041900b050052007414461040210214440c0040c3d5580c800940007028440c0c006403403800c8040811000c024081103400d41ca42000e1291002640c804d0b640c0955984401c58402e2404a02400ba40d108529003c02d11408801c00580002231a02c40c06032009155601d0034141c0c200702d50303540000d40201d43d51a012100c03581d6076200c2d0800c22040d041c5203c0201c0500e0210b652000c03000f0f1607083e0304403c0541d400003441c240c00500780302a46007002040000c180400184c1008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 144590710 1250 144589460 144589463
    0x30f090c10050309010c021b040902180c07110a05100e2b02040b060a0c0312020d051e0a0e0706050f090a06030c02060f060f041121090f0c090a0b010516 67
    0xc20203c24451a0381d0280604044486103100801680c003240c0c80300708201181500d194801e60745d0b008110115103d00e0450001041c20300801245490101c0c2d444200da0300c4480704a0700e403100c004d0542c90030702e0035004400a5403000740c111380c410743c2e80b044180e0b440f03101c24480ca503202e0b804108000340903a019a510781c0b43e94000e2404458041e10b48140410355450744641442404180030049505901c009150722450b054035140b1004c95009540800900c101c005103520315040c5002c0000071543da0b00544072030442c0d40e48110050b0380b40914001100c50301501132031150003440301000280d10070000343c000c03940030b2680070b4a41841d110014100c0606e5038440c00201b61944215000b4076018011213038450412030340079005140c281c0004a10340300c7c2440f05449641e4800004101422610964104480404103100d44015600555600c0030302101c0505191184001c115152940420342421012000c2c102e0f00007a21840d0b0703160302411188001038100300081c805ea5120b175800d07282208000303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 144591960 1250 144590710 144590717
    0x3160221010606021203150108040309080f060402090c0702031203070e031b041103010605030a0c05070501090b04051b0d082209020d0606050a020a020d0204020d0609020415020a0503030f090c10 85
    0x3900e42507004c0d041c403216a0b41c030018150144100050b60700340003e0400350034000d103070800c280d650301e00d000d035035004598000440900c11801b41161381a40003849601850084420340c0d00c9036105180308500d841242e5000390107401490104507070300070780e9028640101c03841c103080720002d400c000420f03e000c00c0b074031808100c1c450354403071640ae6003054414185800c0d5504080d03807641d07040c0039000d8480c0c440130f800040b90fa42e85094032500300344640159071001ba0b02400034400c200c118200780b0780c105d4066406440314000d52029502d6030604c04411303a02074401038000f101c0400c02e81c8440c08190005500450350035180803544001410f1140131101604845c04010786494030603d4240c221400d40d0484024000304100003007901f0b400084000748217038102e921001c10001840800c0181c06851900c3c0d1205090440200300510340b43c011b070040c1c0c0c1d440d09110080d0040c1d5070703080380e445040c024082d010303800400c0462011040100026404050352003111003c951490100b10000d008050b42e8002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 144593210 1250 144591960 144591971
    0x110109030c0b060405040b0412030f110c07060207080c0909030403050a05030c060708040c0b0c150112110f01050f1303120e011d130209030c030114010e07110316022101 74
    0x1000281540140c00c0201914104017502c2d1598502c0b0521101404c09003c0080c03c106801c02c0c1d61198101010044c808402440401c10000d0f2110254124400122503406144400726101e4800940b400844640707034002e0160b4458041401000c2001503d010300c2c40c00100700c0400418820020a020f143c0308500540d502c2140f10307055410408050030080401c1444020300c400f140009030020182c550361705030070380c0e1010b00e40c0303140c2d10b8034092035800c458401d9103030300006900740c0103d16000b1203405240340a0320300000c0c0c000c00c52820343c0040301601140052204c568541c40010142c03001c004410340206115403640c581a001c1404031000e080004c4810b4800c69007544c3c4000303180b0300845411068014880100001181c03d0701151056103019408601c0c0c001940c1d041002144010780034000300034260700c0c1d1186600034042402019201c036203207408030304868411200c06a036030b12406c0c095400c0c08041204550340e0300d4520011307680140702140c3d081c1450400c00303541f6200031601000241 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 144594460 1250 144593210 144593213
    0xc02180f010611010e0303060f042910020105011a1308010204030f020f04020a0f0e0d0804090608010c02061506030c0906130303090b0a0c0204150b030406050603070f050f040507110109030c 83
    0x1405054065406079042c01e030305e41c480d40000400c0ea44c20110417a0350105000840c00480c0c024407081c60032092000171900c2c40c801c2154024401a08000107913081c000c01000440300340e007078500c00c1c40b40b8890103c0608444004201500141c10340c0142140b0700c00b03060740d8400040d42680c0094009440c004050035810003140340c1410f901c86580e030306072425800c04004170405408412541000814000d00303100d074201c241e41b1031aa01051650003640917840c1d1342c840b031001c0000c2043e8000c000d881d40c03920010914441c000034400d0310440008880310f009002031018042e41c0d82000e401c500c020041413021508594801000d04449808080d00b60080c900d50300b0000c01e00e0350340307074005e841c01c0604019044142ea40224010229a01a100452110b401c100503c0600045030b22000720b209020050208102e4030360840c42c01030100300c080b94801603e0340d03031100e07900256224242e070040c419020710303005003055004940d2140c80c0742001160400b45105c00c9003900d0190710f04900042000103641c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 144595710 1250 144594460 144594467
    0x1f0204090c09140f03012c07060804020d0f05010f02040305010c0e010302040f051903020303070305040303020708060c1b0a0602040627030816110a0e010509070c0c060c02180f0106 79
    0x2407880d101c9150281d681460403281c203900e0403140700110b02828003a0900201c98800b5004422017a9103403105205880c004207012029446004100d080c601420500280d030318868602e06004980040000c2c6000c1c40302d0359007029820a1040071609552103170729800d1006024806800154010400811002daa40000500a844120710141410302c140030601210b0741d24114030080d9102500c010b001994580302607800c400c0b02c0e41c0000c0d41448006981010980c1c02406002101c0c420b80071640040c2c1c81c0c41c00651100c0301103507611109101401500c3c000028100e80c0203400d10203030b041d600c6c940d80307903181c150590303100f17070809070200310956075034903419030f60391401a401800e43c2140022242035545141030381c440c07442c4064450031522610402d2160035100000031000c0200f650050f41d40c1c80b0740d000d01007542441440d115241050010300d500340110b0440303c1c402e070310109068440703041032400c2d10071a0142d6000c1e60000d8001d1440300b00e02454038611030044405103a010140d615040004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 144596960 1250 144595710 144595721
    0xf0909050106080f0f190f0b06040914010f140d2a060e0102060c040b0f251a0906041b0e090610050607030203030a1d0d090e150a0b07051f020409 64
    0x5030b24501179002c100881030144c0c83c29521200800e00445c182000c220007401038817606040c0b503806800050001600006540715a21003034040e03001a87c26a40c64483c0d961040caa88107003101d034619400601c00307a00e40044c0e04115103200b002042101594404403401c400c00140d1541250155a103050054642014900140313a1092004181515140441e21540d0245200b08c00d038490010a00000821044054624014644148503061303010071010030050701501710151150945201100e003601050700750140b08141100041489881d243d0b070f00d0403006680d05014114032188500460417400d91650a070142000b43c0c020038150826a050b006122080d41c07290b441036030100f040a0000350048182c0b0340c0b00b0f008140005842c4030b20465043c0c0910503107000c80c1240200841c2d150150780000140e015a150441828025615180400d084582402e80a503102070310941c02c1100091039030003400300c0c511901c1a503030008600d01580d013001e6000c0c080c902096802041c20b004d501e1051140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 144598210 1250 144596960 144596971
    0x2091b16060509190212031c060f0f1215020409140a0c09030c15030204050a0803070309050105040f030f0624082b03090303061509030606050f03030a0f0909050106080f 74
    0xd44103048408131010641212008002d01410103c00c1c01c0c2d000038021b00985903100d24002450841501c0300c24064003c003403e025403d5810342020000c00e49002a2820000747e41c41e06a64070541f058036250100380380d0988600c0303c2700c2a003c00011440103214020000380003030400011901c2e040007800c0d0001c1c0d4433440180405c02c040d902081021881c400250340407640d100e400c9a041d503540505c200c2c040d00c1560007040e04940c03041400115090000002e01c1854080d41d0b50001142d00c2d01c0c01190700e0b104501c280c4040f952036001c1400802c520080007240503108400004091000e403030074080c040c0d181045c40e1040140e40004011014041c403a0380719500d4000d42d8100000d00042150324845245800c4030b081699603d1748600300f5000b54005009404038441100e1400b0b88050000c011001a0004848150609c080051141400c131204105203c0c0107028504040c17200c50100e4021501c0c40398001041a40b501c0040d001c0120300c61030380684625507034100c0c54174000c00c03074240b4808080d09 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 144599460 1250 144598210 144598213
    0x20d0f2c010b010503130309050303040608040b0630100603050102090a0b0a021e0a0215030601090609030c051005040e13030314310b01140f010c0302060402091b16060509 75
    0x4108003240c0c0c4c00411664081d0012030f00c018030f0300b06810b04075001d004581042e50544400180407429a401c030340c1d0305218030b10035411440c203131380c2d400c040c040d4240c1c000d1041c0307501010007100904403210705ca000e20403005000c801c482c00100c11070500019554568410340b03103658006101030550134000c1945001e840241d100900e00301502800075030764060f40c1d0354100312442d05036000712034000602a46035101d0b002001c0074030440004040b009168404e66089012504100c1c00045850046241000b240c0d0070001302e40610b403500702400110800401c0007010824100030100c0e034600307081680c03400f460961141d910b131940f0a28000c4d00312040c3c0103620720601350100400c1084201c180c407960507030581185d00c191040e10700c1602c0000310407003c0300511600b506800031945001581d889000140c003107400c8030308207184000640f0f142c9050400900103810681c001001750502c40c44241d005102080590b1144000c101d01409035007004050040d564801140c90040c0469800f0f0035420078030910 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 144600710 1250 144599460 144599471
    0x501080610090b090a08030304030f0206101212050723060a020412060b040216060b030c04020f0a051c06030809090a060b07030e0325030b0c0a05040504020d0f2c01 72
    0x190081c050044510a003008500b0000e41c01c2032503200c580c1701c600103003045000c80741c5034189441d0180034987c0028201d0300501c03407940050b061441400302d01d4203c030002c18150601030081c0d108c44400780d0016a0240a100c02080403100082091403800c0c01e00c0d0454140303c4c1d544944100882c1488000381000b041980180310500a0b007180d142d04e04045903128a00080c0304001e100818003901034003411070071032070321611408280b041c01d4208078901c1008509407402c10314240108403c030b01482c0d40784009480c017402400540e90080c80182a41d0b00740448030070f5110560043c4005564041d08126504400814028410300b86101e403150801a00841800b4080c20120b08400718045c0f080c02504010600082c0e120340d07182800083c0c2000310011b1116034051071880c201ea402801d1388011070720b04542c280014020600c1038181c680719010342e40d4152400e860041008083c1d0840c4840c00040703552200c4c201001c0d0403030310842243d08100062208501201005140c4c1c2c141e8208100c807460341002d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 144601960 1250 144600710 144600739
    0x10b01081e0a1d010603030e0312090d03170a0c020f1c0f0311070302010506100e0904080a020f0609010f0b0105030603060c0c1e1506010c05060f0a0b1905010806 71
    0x1004444425010104140916036a480c0e201c2c000d40501d103040307182c0e058040440281c40c9010742190003560300035150044800c0307121f410316a580070440b2802c40b803c1070610070541c451818241c4c0e20031990203483c08005c1c60300c001d8010a50000161041030000f5a6040c4c0f50301041c0d0144209100343c4141000740c0088190b00a40c8400c50ba11b4000f24400c1051a010321681140607511103901c0c008002030803074550007181f0f8007038024078003543c080b4800c00074505041c06491103019071080da0309014044101e070b921a075550f50115001411001c083d40500340002d1110801084110312030b4162500204094038034441080440300002c40d070300d040240801c100711450300c1c0021681e80240c45d11004a660340c0c03401f8101400c0a10603030101540c1c02070b0b2200c08000305000650306402c0f540c26078280c0350a840320001035a101713841541c001d1640c1c0280000407290340d02a0742a40c0c0c00002107502040701004040000c20652254000010310f0390203420600c81541e00c0a4410740c040e6080d07814550302c21a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 144603210 1250 144601960 144601981
    0xb070f020a030e030304090905033f06210a1203020403170307020c031c090b03060d0b040201020715020a05010501060e010518060702060f03040510061d10030507030311010b0108 78
    0x3500c00142c2801290030744294541c404104507401402c69010400580e0420700e8155229403101110220f482c00074400c2000700c0406141040100354511115128000000010341d80c1602c01000564001c11080010541c46100880070410f804000c001d021006035138035041322005400308881d01010300c1404240000f40c42001c40f180040012441140ca82da2070fa10100c1c0790002d441c2030b803034050050721280140c07156424400254403500d51148003110391074919000d03181c08120382c0540d016440681070804205a010b0b100d4020740103105075650f00f9164812000190703100881c240c0183e200c40d5041c3c2c14064280710b42130140c0018030b0400d1011205000087c02400303000e490707400703a007030440c400c51480c0d1b101e40460310780c0382d4064450f540301d0400142c00105a00300b00c500b40e55600031401c003050320045906c188016030b2030003040c078840f0031145442100c640300018450ba1400384100310200c08a0f80402116000b503102c1c1d61843c2c03021404001003420354101d60801c40c18010041c0c00d10000c03000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 144604316 1106 144603210 144603223
    0x914030f040807080307020109150905150702180f0c21010f0326041202030304080a0b060109081615052b0c140301050d021f03090b070f02 61
    0x342d9242c13842d02e910806030000e00007010044148982c000460303a04045c031001e0f28040d200d0980340c00100b4020001ca1002c2c2c0c246103c00f10301c050440c0740002d16884c500a030340c440d4001904101c0b90b840d015441c06010466114400700d5411825001414401c440d865140460b1405503502c115408240455004c150340003031070106c52448401c400442500600b0f00c4916451510380b030303d150ba900c401d01080080360705020811002901e000104110060a4042d040016260805031b002400d00040c0d54400f0040b908840800880c06209000c84e03070450381d54445142e4060440e000454280c82100d02102d030340480f440c0786410a0300000c0c545c2450182c0b00f40e0400c48005066800d40b005900c041e949a940c0718100018000d40c00c200107031281c42d5102820000b800d07071006544031481c1000300e0110380040ea0f6400c0324428482d002200e250010694180380d0070300c40c1c14040083d151721 = true := by decide +kernel

theorem cover : BRFrame.Cov 144424460 144604316 := by
  have h0 := BRFrame.cov_init 144424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 144424460 ≤ n) (h2 : n < 144604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
